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
lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg(){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0);
return v___x_159_;
}
}
LEAN_EXPORT void l_Std_Time_instInhabitedGenericFormat_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_160_;
v_res_160_ = l_Std_Time_instInhabitedGenericFormat_default___redArg();
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg___boxed(lean_object* v___dummy_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_Time_instInhabitedGenericFormat_default___redArg();
return v_res_162_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0(void){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_Time_instInhabitedGenericFormat_default___redArg();
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default(lean_object* v_awareness_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___boxed(lean_object* v_awareness_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Time_instInhabitedGenericFormat_default(v_awareness_166_);
lean_dec(v_awareness_166_);
return v_res_167_;
}
}
lean_object* l_Std_Time_instInhabitedGenericFormat___redArg(){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_169_;
}
}
LEAN_EXPORT void l_Std_Time_instInhabitedGenericFormat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_170_;
v_res_170_ = l_Std_Time_instInhabitedGenericFormat___redArg();
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___redArg___boxed(lean_object* v___dummy_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_Time_instInhabitedGenericFormat___redArg();
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat(lean_object* v_a_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___boxed(lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_Time_instInhabitedGenericFormat(v_a_175_);
lean_dec(v_a_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(lean_object* v_a_177_, lean_object* v_f_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_apply_1(v_a_177_, v___y_179_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_pos_181_; lean_object* v_res_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
v_pos_181_ = lean_ctor_get(v___x_180_, 0);
v_res_182_ = lean_ctor_get(v___x_180_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_190_ == 0)
{
v___x_184_ = v___x_180_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_res_182_);
lean_inc(v_pos_181_);
lean_dec(v___x_180_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_apply_1(v_f_178_, v_res_182_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v___x_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_pos_181_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
lean_object* v_pos_191_; lean_object* v_err_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec(v_f_178_);
v_pos_191_ = lean_ctor_get(v___x_180_, 0);
v_err_192_ = lean_ctor_get(v___x_180_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_180_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_err_192_);
lean_inc(v_pos_191_);
lean_dec(v___x_180_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_pos_191_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_err_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1(lean_object* v_00_u03b1_200_, lean_object* v_00_u03b2_201_, lean_object* v_a_202_, lean_object* v_f_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v_a_202_, v_f_203_, v___y_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0(lean_object* v_acc_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_fst_211_; lean_object* v_snd_212_; lean_object* v_pos_214_; lean_object* v_snd_215_; lean_object* v_err_216_; lean_object* v___x_220_; uint8_t v_decide_221_; 
v_fst_211_ = lean_ctor_get(v_a_210_, 0);
v_snd_212_ = lean_ctor_get(v_a_210_, 1);
lean_inc(v_snd_212_);
v___x_220_ = lean_string_utf8_byte_size(v_fst_211_);
v_decide_221_ = lean_nat_dec_eq(v_snd_212_, v___x_220_);
if (v_decide_221_ == 0)
{
uint32_t v___x_222_; uint32_t v_c_223_; uint8_t v___x_224_; 
v___x_222_ = 34;
v_c_223_ = lean_string_utf8_get_fast(v_fst_211_, v_snd_212_);
v___x_224_ = lean_uint32_dec_eq(v_c_223_, v___x_222_);
if (v___x_224_ == 0)
{
lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_234_; 
lean_inc(v_fst_211_);
v_isSharedCheck_234_ = !lean_is_exclusive(v_a_210_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; lean_object* v_unused_236_; 
v_unused_235_ = lean_ctor_get(v_a_210_, 1);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_a_210_, 0);
lean_dec(v_unused_236_);
v___x_226_ = v_a_210_;
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
else
{
lean_dec(v_a_210_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v_it_x27_230_; 
v___x_228_ = lean_string_utf8_next_fast(v_fst_211_, v_snd_212_);
lean_dec(v_snd_212_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_228_);
v_it_x27_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_fst_211_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___x_228_);
v_it_x27_230_ = v_reuseFailAlloc_233_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_string_push(v_acc_209_, v_c_223_);
v_acc_209_ = v___x_231_;
v_a_210_ = v_it_x27_230_;
goto _start;
}
}
}
else
{
lean_object* v___x_237_; 
v___x_237_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_212_);
v_pos_214_ = v_a_210_;
v_snd_215_ = v_snd_212_;
v_err_216_ = v___x_237_;
goto v___jp_213_;
}
}
else
{
lean_object* v___x_238_; 
v___x_238_ = lean_box(0);
lean_inc(v_snd_212_);
v_pos_214_ = v_a_210_;
v_snd_215_ = v_snd_212_;
v_err_216_ = v___x_238_;
goto v___jp_213_;
}
v___jp_213_:
{
uint8_t v_decide_217_; 
v_decide_217_ = lean_nat_dec_eq(v_snd_212_, v_snd_215_);
lean_dec(v_snd_215_);
lean_dec(v_snd_212_);
if (v_decide_217_ == 0)
{
lean_object* v___x_218_; 
lean_dec_ref(v_acc_209_);
lean_inc(v_err_216_);
v___x_218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_218_, 0, v_pos_214_);
lean_ctor_set(v___x_218_, 1, v_err_216_);
return v___x_218_;
}
else
{
lean_object* v___x_219_; 
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_pos_214_);
lean_ctor_set(v___x_219_, 1, v_acc_209_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(lean_object* v_acc_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_fst_241_; lean_object* v_snd_242_; lean_object* v_pos_244_; lean_object* v_snd_245_; lean_object* v_err_246_; lean_object* v___x_250_; uint8_t v_decide_251_; 
v_fst_241_ = lean_ctor_get(v_a_240_, 0);
v_snd_242_ = lean_ctor_get(v_a_240_, 1);
lean_inc(v_snd_242_);
v___x_250_ = lean_string_utf8_byte_size(v_fst_241_);
v_decide_251_ = lean_nat_dec_eq(v_snd_242_, v___x_250_);
if (v_decide_251_ == 0)
{
uint32_t v___x_252_; uint32_t v_c_253_; uint8_t v___x_254_; 
v___x_252_ = 34;
v_c_253_ = lean_string_utf8_get_fast(v_fst_241_, v_snd_242_);
v___x_254_ = lean_uint32_dec_eq(v_c_253_, v___x_252_);
if (v___x_254_ == 0)
{
lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_264_; 
lean_inc(v_fst_241_);
v_isSharedCheck_264_ = !lean_is_exclusive(v_a_240_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; lean_object* v_unused_266_; 
v_unused_265_ = lean_ctor_get(v_a_240_, 1);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_a_240_, 0);
lean_dec(v_unused_266_);
v___x_256_ = v_a_240_;
v_isShared_257_ = v_isSharedCheck_264_;
goto v_resetjp_255_;
}
else
{
lean_dec(v_a_240_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_264_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v_it_x27_260_; 
v___x_258_ = lean_string_utf8_next_fast(v_fst_241_, v_snd_242_);
lean_dec(v_snd_242_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_258_);
v_it_x27_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_fst_241_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_258_);
v_it_x27_260_ = v_reuseFailAlloc_263_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_string_push(v_acc_239_, v_c_253_);
v___x_262_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0(v___x_261_, v_it_x27_260_);
return v___x_262_;
}
}
}
else
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_242_);
v_pos_244_ = v_a_240_;
v_snd_245_ = v_snd_242_;
v_err_246_ = v___x_267_;
goto v___jp_243_;
}
}
else
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
lean_inc(v_snd_242_);
v_pos_244_ = v_a_240_;
v_snd_245_ = v_snd_242_;
v_err_246_ = v___x_268_;
goto v___jp_243_;
}
v___jp_243_:
{
uint8_t v_decide_247_; 
v_decide_247_ = lean_nat_dec_eq(v_snd_242_, v_snd_245_);
lean_dec(v_snd_245_);
lean_dec(v_snd_242_);
if (v_decide_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec_ref(v_acc_239_);
lean_inc(v_err_246_);
v___x_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_248_, 0, v_pos_244_);
lean_ctor_set(v___x_248_, 1, v_err_246_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_pos_244_);
lean_ctor_set(v___x_249_, 1, v_acc_239_);
return v___x_249_;
}
}
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint8_t v_decide_273_, uint32_t v___x_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_fst_279_; lean_object* v_snd_280_; lean_object* v___x_281_; uint8_t v_decide_282_; 
v_fst_279_ = lean_ctor_get(v___y_275_, 0);
v_snd_280_ = lean_ctor_get(v___y_275_, 1);
v___x_281_ = lean_string_utf8_byte_size(v_fst_279_);
v_decide_282_ = lean_nat_dec_eq(v_snd_280_, v___x_281_);
if (v_decide_282_ == 0)
{
if (v_decide_273_ == 0)
{
goto v___jp_276_;
}
else
{
uint32_t v_c_283_; uint8_t v___x_284_; 
v_c_283_ = lean_string_utf8_get_fast(v_fst_279_, v_snd_280_);
v___x_284_ = lean_uint32_dec_eq(v_c_283_, v___x_274_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_286_, 0, v___y_275_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
return v___x_286_;
}
else
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_340_; 
lean_inc(v_snd_280_);
lean_inc(v_fst_279_);
v_isSharedCheck_340_ = !lean_is_exclusive(v___y_275_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; lean_object* v_unused_342_; 
v_unused_341_ = lean_ctor_get(v___y_275_, 1);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v___y_275_, 0);
lean_dec(v_unused_342_);
v___x_288_ = v___y_275_;
v_isShared_289_ = v_isSharedCheck_340_;
goto v_resetjp_287_;
}
else
{
lean_dec(v___y_275_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_340_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v_it_x27_292_; 
v___x_290_ = lean_string_utf8_next_fast(v_fst_279_, v_snd_280_);
lean_dec(v_snd_280_);
lean_inc(v_fst_279_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_290_);
v_it_x27_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_fst_279_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_290_);
v_it_x27_292_ = v_reuseFailAlloc_339_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
uint8_t v_decide_296_; 
v_decide_296_ = lean_nat_dec_eq(v___x_290_, v___x_281_);
if (v_decide_296_ == 0)
{
if (v___x_284_ == 0)
{
lean_dec(v_fst_279_);
goto v___jp_293_;
}
else
{
uint32_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_string_utf8_get_fast(v_fst_279_, v___x_290_);
v___x_298_ = lean_uint32_dec_eq(v___x_297_, v___x_274_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref(v_it_x27_292_);
v___x_299_ = lean_string_utf8_next_fast(v_fst_279_, v___x_290_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v_fst_279_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_302_ = lean_string_push(v___x_301_, v___x_297_);
v___x_303_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(v___x_302_, v___x_300_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_pos_304_; lean_object* v_res_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_336_; 
v_pos_304_ = lean_ctor_get(v___x_303_, 0);
v_res_305_ = lean_ctor_get(v___x_303_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_336_ == 0)
{
v___x_307_ = v___x_303_;
v_isShared_308_ = v_isSharedCheck_336_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_res_305_);
lean_inc(v_pos_304_);
lean_dec(v___x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_336_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v___x_311_; uint8_t v_decide_312_; 
v_fst_309_ = lean_ctor_get(v_pos_304_, 0);
v_snd_310_ = lean_ctor_get(v_pos_304_, 1);
v___x_311_ = lean_string_utf8_byte_size(v_fst_309_);
v_decide_312_ = lean_nat_dec_eq(v_snd_310_, v___x_311_);
if (v_decide_312_ == 0)
{
uint32_t v_c_313_; uint8_t v___x_314_; 
v_c_313_ = lean_string_utf8_get_fast(v_fst_309_, v_snd_310_);
v___x_314_ = lean_uint32_dec_eq(v_c_313_, v___x_274_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_317_; 
lean_dec(v_res_305_);
v___x_315_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 1);
lean_ctor_set(v___x_307_, 1, v___x_315_);
v___x_317_ = v___x_307_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_pos_304_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_329_; 
lean_inc(v_snd_310_);
lean_inc(v_fst_309_);
v_isSharedCheck_329_ = !lean_is_exclusive(v_pos_304_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; lean_object* v_unused_331_; 
v_unused_330_ = lean_ctor_get(v_pos_304_, 1);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_pos_304_, 0);
lean_dec(v_unused_331_);
v___x_320_ = v_pos_304_;
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
else
{
lean_dec(v_pos_304_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v_it_x27_324_; 
v___x_322_ = lean_string_utf8_next_fast(v_fst_309_, v_snd_310_);
lean_dec(v_snd_310_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_322_);
v_it_x27_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_fst_309_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_322_);
v_it_x27_324_ = v_reuseFailAlloc_328_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_326_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v_it_x27_324_);
v___x_326_ = v___x_307_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_it_x27_324_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_res_305_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
else
{
lean_object* v___x_332_; lean_object* v___x_334_; 
lean_dec(v_res_305_);
v___x_332_ = lean_box(0);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 1);
lean_ctor_set(v___x_307_, 1, v___x_332_);
v___x_334_ = v___x_307_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_pos_304_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
return v___x_303_;
}
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_fst_279_);
v___x_337_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v_it_x27_292_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
return v___x_338_;
}
}
}
else
{
lean_dec(v_fst_279_);
goto v___jp_293_;
}
v___jp_293_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(0);
v___x_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_295_, 0, v_it_x27_292_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
}
}
}
}
}
else
{
goto v___jp_276_;
}
v___jp_276_:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v___y_275_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_decide_273_ = stack[0].m_num;
uint32_t v___x_274_ = stack[1].m_num;
lean_object* v___y_275_ = stack[2].m_obj;
lean_object* v_res_343_;
v_res_343_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(v_decide_273_, v___x_274_, v___y_275_);
stack->m_obj
 = v_res_343_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object* v_decide_344_, lean_object* v___x_345_, lean_object* v___y_346_){
_start:
{
uint8_t v_decide_11365__boxed_347_; uint32_t v___x_11366__boxed_348_; lean_object* v_res_349_; 
v_decide_11365__boxed_347_ = lean_unbox(v_decide_344_);
v___x_11366__boxed_348_ = lean_unbox_uint32(v___x_345_);
lean_dec(v___x_345_);
v_res_349_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(v_decide_11365__boxed_347_, v___x_11366__boxed_348_, v___y_346_);
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
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(uint8_t v_decide_413_, uint32_t v___x_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_fst_419_; lean_object* v_snd_420_; lean_object* v___x_421_; uint8_t v_decide_422_; 
v_fst_419_ = lean_ctor_get(v___y_415_, 0);
v_snd_420_ = lean_ctor_get(v___y_415_, 1);
v___x_421_ = lean_string_utf8_byte_size(v_fst_419_);
v_decide_422_ = lean_nat_dec_eq(v_snd_420_, v___x_421_);
if (v_decide_422_ == 0)
{
if (v_decide_413_ == 0)
{
goto v___jp_416_;
}
else
{
uint32_t v_c_423_; uint8_t v___x_424_; 
v_c_423_ = lean_string_utf8_get_fast(v_fst_419_, v_snd_420_);
v___x_424_ = lean_uint32_dec_eq(v_c_423_, v___x_414_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1));
v___x_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_426_, 0, v___y_415_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
return v___x_426_;
}
else
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_480_; 
lean_inc(v_snd_420_);
lean_inc(v_fst_419_);
v_isSharedCheck_480_ = !lean_is_exclusive(v___y_415_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; lean_object* v_unused_482_; 
v_unused_481_ = lean_ctor_get(v___y_415_, 1);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v___y_415_, 0);
lean_dec(v_unused_482_);
v___x_428_ = v___y_415_;
v_isShared_429_ = v_isSharedCheck_480_;
goto v_resetjp_427_;
}
else
{
lean_dec(v___y_415_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_480_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v_it_x27_432_; 
v___x_430_ = lean_string_utf8_next_fast(v_fst_419_, v_snd_420_);
lean_dec(v_snd_420_);
lean_inc(v_fst_419_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_430_);
v_it_x27_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_fst_419_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_430_);
v_it_x27_432_ = v_reuseFailAlloc_479_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
uint8_t v_decide_436_; 
v_decide_436_ = lean_nat_dec_eq(v___x_430_, v___x_421_);
if (v_decide_436_ == 0)
{
if (v___x_424_ == 0)
{
lean_dec(v_fst_419_);
goto v___jp_433_;
}
else
{
uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_string_utf8_get_fast(v_fst_419_, v___x_430_);
v___x_438_ = lean_uint32_dec_eq(v___x_437_, v___x_414_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec_ref(v_it_x27_432_);
v___x_439_ = lean_string_utf8_next_fast(v_fst_419_, v___x_430_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_fst_419_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_442_ = lean_string_push(v___x_441_, v___x_437_);
v___x_443_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(v___x_442_, v___x_440_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_pos_444_; lean_object* v_res_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_476_; 
v_pos_444_ = lean_ctor_get(v___x_443_, 0);
v_res_445_ = lean_ctor_get(v___x_443_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_476_ == 0)
{
v___x_447_ = v___x_443_;
v_isShared_448_ = v_isSharedCheck_476_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_res_445_);
lean_inc(v_pos_444_);
lean_dec(v___x_443_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_476_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v___x_451_; uint8_t v_decide_452_; 
v_fst_449_ = lean_ctor_get(v_pos_444_, 0);
v_snd_450_ = lean_ctor_get(v_pos_444_, 1);
v___x_451_ = lean_string_utf8_byte_size(v_fst_449_);
v_decide_452_ = lean_nat_dec_eq(v_snd_450_, v___x_451_);
if (v_decide_452_ == 0)
{
uint32_t v_c_453_; uint8_t v___x_454_; 
v_c_453_ = lean_string_utf8_get_fast(v_fst_449_, v_snd_450_);
v___x_454_ = lean_uint32_dec_eq(v_c_453_, v___x_414_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_457_; 
lean_dec(v_res_445_);
v___x_455_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1));
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 1);
lean_ctor_set(v___x_447_, 1, v___x_455_);
v___x_457_ = v___x_447_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_pos_444_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
else
{
lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_469_; 
lean_inc(v_snd_450_);
lean_inc(v_fst_449_);
v_isSharedCheck_469_ = !lean_is_exclusive(v_pos_444_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; 
v_unused_470_ = lean_ctor_get(v_pos_444_, 1);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_pos_444_, 0);
lean_dec(v_unused_471_);
v___x_460_ = v_pos_444_;
v_isShared_461_ = v_isSharedCheck_469_;
goto v_resetjp_459_;
}
else
{
lean_dec(v_pos_444_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_469_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v_it_x27_464_; 
v___x_462_ = lean_string_utf8_next_fast(v_fst_449_, v_snd_450_);
lean_dec(v_snd_450_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v___x_462_);
v_it_x27_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_fst_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_462_);
v_it_x27_464_ = v_reuseFailAlloc_468_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_466_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v_it_x27_464_);
v___x_466_ = v___x_447_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_it_x27_464_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_res_445_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec(v_res_445_);
v___x_472_ = lean_box(0);
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 1);
lean_ctor_set(v___x_447_, 1, v___x_472_);
v___x_474_ = v___x_447_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_pos_444_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
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
else
{
return v___x_443_;
}
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_fst_419_);
v___x_477_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v_it_x27_432_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
}
}
else
{
lean_dec(v_fst_419_);
goto v___jp_433_;
}
v___jp_433_:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_box(0);
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v_it_x27_432_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
return v___x_435_;
}
}
}
}
}
}
else
{
goto v___jp_416_;
}
v___jp_416_:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_box(0);
v___x_418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_418_, 0, v___y_415_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_decide_413_ = stack[0].m_num;
uint32_t v___x_414_ = stack[1].m_num;
lean_object* v___y_415_ = stack[2].m_obj;
lean_object* v_res_483_;
v_res_483_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(v_decide_413_, v___x_414_, v___y_415_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object* v_decide_484_, lean_object* v___x_485_, lean_object* v___y_486_){
_start:
{
uint8_t v_decide_11732__boxed_487_; uint32_t v___x_11733__boxed_488_; lean_object* v_res_489_; 
v_decide_11732__boxed_487_ = lean_unbox(v_decide_484_);
v___x_11733__boxed_488_ = lean_unbox_uint32(v___x_485_);
lean_dec(v___x_485_);
v_res_489_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(v_decide_11732__boxed_487_, v___x_11733__boxed_488_, v___y_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object* v_acc_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_fst_492_; lean_object* v_snd_493_; lean_object* v_pos_495_; lean_object* v_snd_496_; lean_object* v_err_497_; lean_object* v___x_503_; uint8_t v_decide_504_; 
v_fst_492_ = lean_ctor_get(v_a_491_, 0);
v_snd_493_ = lean_ctor_get(v_a_491_, 1);
lean_inc(v_snd_493_);
v___x_503_ = lean_string_utf8_byte_size(v_fst_492_);
v_decide_504_ = lean_nat_dec_eq(v_snd_493_, v___x_503_);
if (v_decide_504_ == 0)
{
uint32_t v___x_505_; uint32_t v___x_506_; uint32_t v_c_507_; lean_object* v___x_508_; lean_object* v_it_x27_509_; uint8_t v___y_511_; uint32_t v___x_521_; uint8_t v___x_522_; 
v___x_505_ = 39;
v___x_506_ = 34;
v_c_507_ = lean_string_utf8_get_fast(v_fst_492_, v_snd_493_);
v___x_508_ = lean_string_utf8_next_fast(v_fst_492_, v_snd_493_);
lean_inc(v_fst_492_);
v_it_x27_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_509_, 0, v_fst_492_);
lean_ctor_set(v_it_x27_509_, 1, v___x_508_);
v___x_521_ = 65;
v___x_522_ = lean_uint32_dec_le(v___x_521_, v_c_507_);
if (v___x_522_ == 0)
{
goto v___jp_516_;
}
else
{
uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = 90;
v___x_524_ = lean_uint32_dec_le(v_c_507_, v___x_523_);
if (v___x_524_ == 0)
{
goto v___jp_516_;
}
else
{
v___y_511_ = v___x_524_;
goto v___jp_510_;
}
}
v___jp_510_:
{
if (v___y_511_ == 0)
{
uint8_t v___x_512_; 
v___x_512_ = lean_uint32_dec_eq(v_c_507_, v___x_505_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; 
v___x_513_ = lean_uint32_dec_eq(v_c_507_, v___x_506_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_dec(v_snd_493_);
lean_dec_ref(v_a_491_);
v___x_514_ = lean_string_push(v_acc_490_, v_c_507_);
v_acc_490_ = v___x_514_;
v_a_491_ = v_it_x27_509_;
goto _start;
}
else
{
lean_dec_ref_known(v_it_x27_509_, 2);
goto v___jp_501_;
}
}
else
{
lean_dec_ref_known(v_it_x27_509_, 2);
goto v___jp_501_;
}
}
else
{
lean_dec_ref_known(v_it_x27_509_, 2);
goto v___jp_501_;
}
}
v___jp_516_:
{
uint32_t v___x_517_; uint8_t v___x_518_; 
v___x_517_ = 97;
v___x_518_ = lean_uint32_dec_le(v___x_517_, v_c_507_);
if (v___x_518_ == 0)
{
v___y_511_ = v___x_518_;
goto v___jp_510_;
}
else
{
uint32_t v___x_519_; uint8_t v___x_520_; 
v___x_519_ = 122;
v___x_520_ = lean_uint32_dec_le(v_c_507_, v___x_519_);
v___y_511_ = v___x_520_;
goto v___jp_510_;
}
}
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_box(0);
lean_inc(v_snd_493_);
v_pos_495_ = v_a_491_;
v_snd_496_ = v_snd_493_;
v_err_497_ = v___x_525_;
goto v___jp_494_;
}
v___jp_494_:
{
uint8_t v_decide_498_; 
v_decide_498_ = lean_nat_dec_eq(v_snd_493_, v_snd_496_);
lean_dec(v_snd_496_);
lean_dec(v_snd_493_);
if (v_decide_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec_ref(v_acc_490_);
lean_inc(v_err_497_);
v___x_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_499_, 0, v_pos_495_);
lean_ctor_set(v___x_499_, 1, v_err_497_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_pos_495_);
lean_ctor_set(v___x_500_, 1, v_acc_490_);
return v___x_500_;
}
}
v___jp_501_:
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_493_);
v_pos_495_ = v_a_491_;
v_snd_496_ = v_snd_493_;
v_err_497_ = v___x_502_;
goto v___jp_494_;
}
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint8_t v_decide_526_, uint32_t v___x_527_, uint32_t v___x_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_538_; uint8_t v_decide_539_; 
v_fst_536_ = lean_ctor_get(v___y_529_, 0);
v_snd_537_ = lean_ctor_get(v___y_529_, 1);
v___x_538_ = lean_string_utf8_byte_size(v_fst_536_);
v_decide_539_ = lean_nat_dec_eq(v_snd_537_, v___x_538_);
if (v_decide_539_ == 0)
{
if (v_decide_526_ == 0)
{
goto v___jp_530_;
}
else
{
uint32_t v_c_540_; lean_object* v___x_541_; lean_object* v_it_x27_542_; uint8_t v___y_544_; uint32_t v___x_555_; uint8_t v___x_556_; 
v_c_540_ = lean_string_utf8_get_fast(v_fst_536_, v_snd_537_);
v___x_541_ = lean_string_utf8_next_fast(v_fst_536_, v_snd_537_);
lean_inc(v_fst_536_);
v_it_x27_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_542_, 0, v_fst_536_);
lean_ctor_set(v_it_x27_542_, 1, v___x_541_);
v___x_555_ = 65;
v___x_556_ = lean_uint32_dec_le(v___x_555_, v_c_540_);
if (v___x_556_ == 0)
{
goto v___jp_550_;
}
else
{
uint32_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = 90;
v___x_558_ = lean_uint32_dec_le(v_c_540_, v___x_557_);
if (v___x_558_ == 0)
{
goto v___jp_550_;
}
else
{
v___y_544_ = v___x_558_;
goto v___jp_543_;
}
}
v___jp_543_:
{
if (v___y_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = lean_uint32_dec_eq(v_c_540_, v___x_527_);
if (v___x_545_ == 0)
{
uint8_t v___x_546_; 
v___x_546_ = lean_uint32_dec_eq(v_c_540_, v___x_528_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref(v___y_529_);
v___x_547_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_548_ = lean_string_push(v___x_547_, v_c_540_);
v___x_549_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(v___x_548_, v_it_x27_542_);
return v___x_549_;
}
else
{
lean_dec_ref_known(v_it_x27_542_, 2);
goto v___jp_533_;
}
}
else
{
lean_dec_ref_known(v_it_x27_542_, 2);
goto v___jp_533_;
}
}
else
{
lean_dec_ref_known(v_it_x27_542_, 2);
goto v___jp_533_;
}
}
v___jp_550_:
{
uint32_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = 97;
v___x_552_ = lean_uint32_dec_le(v___x_551_, v_c_540_);
if (v___x_552_ == 0)
{
v___y_544_ = v___x_552_;
goto v___jp_543_;
}
else
{
uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 122;
v___x_554_ = lean_uint32_dec_le(v_c_540_, v___x_553_);
v___y_544_ = v___x_554_;
goto v___jp_543_;
}
}
}
}
else
{
goto v___jp_530_;
}
v___jp_530_:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_box(0);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___y_529_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
return v___x_532_;
}
v___jp_533_:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_535_, 0, v___y_529_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
return v___x_535_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_decide_526_ = stack[0].m_num;
uint32_t v___x_527_ = stack[1].m_num;
uint32_t v___x_528_ = stack[2].m_num;
lean_object* v___y_529_ = stack[3].m_obj;
lean_object* v_res_559_;
v_res_559_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(v_decide_526_, v___x_527_, v___x_528_, v___y_529_);
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object* v_decide_560_, lean_object* v___x_561_, lean_object* v___x_562_, lean_object* v___y_563_){
_start:
{
uint8_t v_decide_12030__boxed_564_; uint32_t v___x_12031__boxed_565_; uint32_t v___x_12032__boxed_566_; lean_object* v_res_567_; 
v_decide_12030__boxed_564_ = lean_unbox(v_decide_560_);
v___x_12031__boxed_565_ = lean_unbox_uint32(v___x_561_);
lean_dec(v___x_561_);
v___x_12032__boxed_566_ = lean_unbox_uint32(v___x_562_);
lean_dec(v___x_562_);
v_res_567_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(v_decide_12030__boxed_564_, v___x_12031__boxed_565_, v___x_12032__boxed_566_, v___y_563_);
return v_res_567_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t v___y_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_570_ = lean_string_push(v___x_569_, v___y_568_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3_0interp(lean_interpreter_value* stack)
{
uint32_t v___y_568_ = stack[0].m_num;
lean_object* v_res_572_;
v_res_572_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(v___y_568_);
stack->m_obj
 = v_res_572_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object* v___y_573_){
_start:
{
uint32_t v___y_12127__boxed_574_; lean_object* v_res_575_; 
v___y_12127__boxed_574_ = lean_unbox_uint32(v___y_573_);
lean_dec(v___y_573_);
v_res_575_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(v___y_12127__boxed_574_);
return v_res_575_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(uint8_t v___x_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___x_583_; uint8_t v_decide_584_; 
v_fst_581_ = lean_ctor_get(v___y_577_, 0);
v_snd_582_ = lean_ctor_get(v___y_577_, 1);
v___x_583_ = lean_string_utf8_byte_size(v_fst_581_);
v_decide_584_ = lean_nat_dec_eq(v_snd_582_, v___x_583_);
if (v_decide_584_ == 0)
{
if (v___x_576_ == 0)
{
goto v___jp_578_;
}
else
{
lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_595_; 
lean_inc(v_snd_582_);
lean_inc(v_fst_581_);
v_isSharedCheck_595_ = !lean_is_exclusive(v___y_577_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; lean_object* v_unused_597_; 
v_unused_596_ = lean_ctor_get(v___y_577_, 1);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v___y_577_, 0);
lean_dec(v_unused_597_);
v___x_586_ = v___y_577_;
v_isShared_587_ = v_isSharedCheck_595_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___y_577_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_595_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
uint32_t v_c_588_; lean_object* v___x_589_; lean_object* v_it_x27_591_; 
v_c_588_ = lean_string_utf8_get_fast(v_fst_581_, v_snd_582_);
v___x_589_ = lean_string_utf8_next_fast(v_fst_581_, v_snd_582_);
lean_dec(v_snd_582_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v___x_589_);
v_it_x27_591_ = v___x_586_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_fst_581_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_589_);
v_it_x27_591_ = v_reuseFailAlloc_594_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_box_uint32(v_c_588_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_it_x27_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
return v___x_593_;
}
}
}
}
else
{
goto v___jp_578_;
}
v___jp_578_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_box(0);
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v___y_577_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_576_ = stack[0].m_num;
lean_object* v___y_577_ = stack[1].m_obj;
lean_object* v_res_598_;
v_res_598_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(v___x_576_, v___y_577_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed(lean_object* v___x_599_, lean_object* v___y_600_){
_start:
{
uint8_t v___x_12141__boxed_601_; lean_object* v_res_602_; 
v___x_12141__boxed_601_ = lean_unbox(v___x_599_);
v_res_602_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(v___x_12141__boxed_601_, v___y_600_);
return v_res_602_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1(void){
_start:
{
uint32_t v___x_607_; lean_object* v___x_608_; 
v___x_607_ = 39;
v___x_608_ = lean_box_uint32(v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2(void){
_start:
{
uint32_t v___x_609_; lean_object* v___x_610_; 
v___x_609_ = 34;
v___x_610_ = lean_box_uint32(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(lean_object* v_a_611_){
_start:
{
lean_object* v___x_612_; 
lean_inc_ref(v_a_611_);
v___x_612_ = l_Std_Time_parseModifier(v_a_611_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_pos_613_; lean_object* v_res_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v_a_611_);
v_pos_613_ = lean_ctor_get(v___x_612_, 0);
v_res_614_ = lean_ctor_get(v___x_612_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_622_ == 0)
{
v___x_616_ = v___x_612_;
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_res_614_);
lean_inc(v_pos_613_);
lean_dec(v___x_612_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v_res_614_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___x_618_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_pos_613_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v_pos_623_; lean_object* v_err_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_695_; 
v_pos_623_ = lean_ctor_get(v___x_612_, 0);
v_err_624_ = lean_ctor_get(v___x_612_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_695_ == 0)
{
v___x_626_ = v___x_612_;
v_isShared_627_ = v_isSharedCheck_695_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_err_624_);
lean_inc(v_pos_623_);
lean_dec(v___x_612_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_695_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_snd_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_693_; 
v_snd_628_ = lean_ctor_get(v_a_611_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_a_611_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v_a_611_, 0);
lean_dec(v_unused_694_);
v___x_630_ = v_a_611_;
v_isShared_631_ = v_isSharedCheck_693_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_snd_628_);
lean_dec(v_a_611_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_693_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_fst_632_; lean_object* v_snd_633_; uint8_t v_decide_634_; 
v_fst_632_ = lean_ctor_get(v_pos_623_, 0);
v_snd_633_ = lean_ctor_get(v_pos_623_, 1);
v_decide_634_ = lean_nat_dec_eq(v_snd_628_, v_snd_633_);
lean_dec(v_snd_628_);
if (v_decide_634_ == 0)
{
lean_object* v___x_636_; 
lean_del_object(v___x_630_);
if (v_isShared_627_ == 0)
{
v___x_636_ = v___x_626_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_pos_623_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_err_624_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___f_638_; lean_object* v___y_640_; lean_object* v_pos_641_; lean_object* v_snd_642_; lean_object* v___x_668_; uint8_t v_decide_669_; 
lean_inc(v_snd_633_);
lean_dec(v_err_624_);
v___f_638_ = ((lean_object*)(l_Std_Time_instCoeStringFormatPart___closed__0));
v___x_668_ = lean_string_utf8_byte_size(v_fst_632_);
v_decide_669_ = lean_nat_dec_eq(v_snd_633_, v___x_668_);
if (v_decide_669_ == 0)
{
if (v_decide_634_ == 0)
{
lean_del_object(v___x_630_);
goto v___jp_663_;
}
else
{
uint32_t v___x_670_; uint32_t v_c_671_; uint8_t v___x_672_; 
lean_del_object(v___x_626_);
v___x_670_ = 92;
v_c_671_ = lean_string_utf8_get_fast(v_fst_632_, v_snd_633_);
v___x_672_ = lean_uint32_dec_eq(v_c_671_, v___x_670_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1));
lean_inc(v_pos_623_);
if (v_isShared_631_ == 0)
{
lean_ctor_set_tag(v___x_630_, 1);
lean_ctor_set(v___x_630_, 1, v___x_673_);
lean_ctor_set(v___x_630_, 0, v_pos_623_);
v___x_675_ = v___x_630_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_pos_623_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_inc(v_snd_633_);
v___y_640_ = v___x_675_;
v_pos_641_ = v_pos_623_;
v_snd_642_ = v_snd_633_;
goto v___jp_639_;
}
}
else
{
lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_690_; 
lean_inc(v_fst_632_);
lean_del_object(v___x_630_);
v_isSharedCheck_690_ = !lean_is_exclusive(v_pos_623_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; lean_object* v_unused_692_; 
v_unused_691_ = lean_ctor_get(v_pos_623_, 1);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v_pos_623_, 0);
lean_dec(v_unused_692_);
v___x_678_ = v_pos_623_;
v_isShared_679_ = v_isSharedCheck_690_;
goto v_resetjp_677_;
}
else
{
lean_dec(v_pos_623_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_690_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___f_680_; lean_object* v___x_681_; lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v_it_x27_685_; 
v___f_680_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2));
v___x_681_ = lean_box(v___x_672_);
v___f_682_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed), 2, 1);
lean_closure_set(v___f_682_, 0, v___x_681_);
v___x_683_ = lean_string_utf8_next_fast(v_fst_632_, v_snd_633_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_683_);
v_it_x27_685_ = v___x_678_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_fst_632_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_683_);
v_it_x27_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; 
v___x_686_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_682_, v___f_680_, v_it_x27_685_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_dec(v_snd_633_);
return v___x_686_;
}
else
{
lean_object* v_pos_687_; lean_object* v_snd_688_; 
v_pos_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_pos_687_);
v_snd_688_ = lean_ctor_get(v_pos_687_, 1);
lean_inc(v_snd_688_);
v___y_640_ = v___x_686_;
v_pos_641_ = v_pos_687_;
v_snd_642_ = v_snd_688_;
goto v___jp_639_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_630_);
goto v___jp_663_;
}
v___jp_639_:
{
uint8_t v_decide_643_; 
v_decide_643_ = lean_nat_dec_eq(v_snd_633_, v_snd_642_);
lean_dec(v_snd_633_);
if (v_decide_643_ == 0)
{
lean_dec(v_snd_642_);
lean_dec_ref(v_pos_641_);
return v___y_640_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___f_646_; lean_object* v___x_647_; 
lean_dec_ref(v___y_640_);
v___x_644_ = lean_box(v_decide_643_);
v___x_645_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_646_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed), 3, 2);
lean_closure_set(v___f_646_, 0, v___x_644_);
lean_closure_set(v___f_646_, 1, v___x_645_);
v___x_647_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_646_, v___f_638_, v_pos_641_);
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
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___f_653_; lean_object* v___x_654_; 
lean_inc(v_snd_649_);
lean_inc(v_pos_648_);
lean_dec_ref_known(v___x_647_, 2);
v___x_651_ = lean_box(v_decide_650_);
v___x_652_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___f_653_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed), 3, 2);
lean_closure_set(v___f_653_, 0, v___x_651_);
lean_closure_set(v___f_653_, 1, v___x_652_);
v___x_654_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_653_, v___f_638_, v_pos_648_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_dec(v_snd_649_);
return v___x_654_;
}
else
{
lean_object* v_pos_655_; lean_object* v_snd_656_; uint8_t v_decide_657_; 
v_pos_655_ = lean_ctor_get(v___x_654_, 0);
v_snd_656_ = lean_ctor_get(v_pos_655_, 1);
v_decide_657_ = lean_nat_dec_eq(v_snd_649_, v_snd_656_);
lean_dec(v_snd_649_);
if (v_decide_657_ == 0)
{
return v___x_654_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___f_661_; lean_object* v___x_662_; 
lean_inc(v_pos_655_);
lean_dec_ref_known(v___x_654_, 2);
v___x_658_ = lean_box(v_decide_657_);
v___x_659_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___x_660_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_661_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed), 4, 3);
lean_closure_set(v___f_661_, 0, v___x_658_);
lean_closure_set(v___f_661_, 1, v___x_659_);
lean_closure_set(v___f_661_, 2, v___x_660_);
v___x_662_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_661_, v___f_638_, v_pos_655_);
return v___x_662_;
}
}
}
}
}
}
v___jp_663_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = lean_box(0);
lean_inc(v_pos_623_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_664_);
v___x_666_ = v___x_626_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_pos_623_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_inc(v_snd_633_);
v___y_640_ = v___x_666_;
v_pos_641_ = v_pos_623_;
v_snd_642_ = v_snd_633_;
goto v___jp_639_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(lean_object* v_acc_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_698_; 
lean_inc_ref(v_a_697_);
v___x_698_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(v_a_697_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_pos_699_; lean_object* v_res_700_; lean_object* v___x_701_; 
lean_dec_ref(v_a_697_);
v_pos_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_pos_699_);
v_res_700_ = lean_ctor_get(v___x_698_, 1);
lean_inc(v_res_700_);
lean_dec_ref_known(v___x_698_, 2);
v___x_701_ = lean_array_push(v_acc_696_, v_res_700_);
v_acc_696_ = v___x_701_;
v_a_697_ = v_pos_699_;
goto _start;
}
else
{
lean_object* v_pos_703_; lean_object* v_err_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_717_; 
v_pos_703_ = lean_ctor_get(v___x_698_, 0);
v_err_704_ = lean_ctor_get(v___x_698_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_717_ == 0)
{
v___x_706_ = v___x_698_;
v_isShared_707_ = v_isSharedCheck_717_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_err_704_);
lean_inc(v_pos_703_);
lean_dec(v___x_698_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_717_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_snd_708_; lean_object* v_snd_709_; uint8_t v_decide_710_; 
v_snd_708_ = lean_ctor_get(v_a_697_, 1);
lean_inc(v_snd_708_);
lean_dec_ref(v_a_697_);
v_snd_709_ = lean_ctor_get(v_pos_703_, 1);
v_decide_710_ = lean_nat_dec_eq(v_snd_708_, v_snd_709_);
lean_dec(v_snd_708_);
if (v_decide_710_ == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v_acc_696_);
if (v_isShared_707_ == 0)
{
v___x_712_ = v___x_706_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_pos_703_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_err_704_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
else
{
lean_object* v___x_715_; 
lean_dec(v_err_704_);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 0);
lean_ctor_set(v___x_706_, 1, v_acc_696_);
v___x_715_ = v___x_706_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_pos_703_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_acc_696_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser(lean_object* v_a_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0));
v___x_725_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(v___x_724_, v_a_723_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_pos_726_; lean_object* v_res_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_743_; 
v_pos_726_ = lean_ctor_get(v___x_725_, 0);
v_res_727_ = lean_ctor_get(v___x_725_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_743_ == 0)
{
v___x_729_ = v___x_725_;
v_isShared_730_ = v_isSharedCheck_743_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_res_727_);
lean_inc(v_pos_726_);
lean_dec(v___x_725_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_743_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v_fst_731_; lean_object* v_snd_732_; lean_object* v___x_733_; uint8_t v_decide_734_; 
v_fst_731_ = lean_ctor_get(v_pos_726_, 0);
v_snd_732_ = lean_ctor_get(v_pos_726_, 1);
v___x_733_ = lean_string_utf8_byte_size(v_fst_731_);
v_decide_734_ = lean_nat_dec_eq(v_snd_732_, v___x_733_);
if (v_decide_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_dec(v_res_727_);
v___x_735_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 1, v___x_735_);
v___x_737_ = v___x_729_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_pos_726_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_array_to_list(v_res_727_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_739_);
v___x_741_ = v___x_729_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_pos_726_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v_pos_744_; lean_object* v_err_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
v_pos_744_ = lean_ctor_get(v___x_725_, 0);
v_err_745_ = lean_ctor_get(v___x_725_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_725_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_err_745_);
lean_inc(v_pos_744_);
lean_dec(v___x_725_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_pos_744_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_err_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParse(lean_object* v_s_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_755_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_754_, v_s_753_);
return v___x_755_;
}
}
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(uint32_t v_a_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
lean_object* v_zero_759_; uint8_t v_isZero_760_; 
v_zero_759_ = lean_unsigned_to_nat(0u);
v_isZero_760_ = lean_nat_dec_eq(v_x_757_, v_zero_759_);
if (v_isZero_760_ == 1)
{
lean_dec(v_x_757_);
return v_x_758_;
}
else
{
lean_object* v_one_761_; lean_object* v_n_762_; lean_object* v___x_763_; 
v_one_761_ = lean_unsigned_to_nat(1u);
v_n_762_ = lean_nat_sub(v_x_757_, v_one_761_);
lean_dec(v_x_757_);
v___x_763_ = lean_string_push(v_x_758_, v_a_756_);
v_x_757_ = v_n_762_;
v_x_758_ = v___x_763_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_756_ = stack[0].m_num;
lean_object* v_x_757_ = stack[1].m_obj;
lean_object* v_x_758_ = stack[2].m_obj;
lean_object* v_res_765_;
v_res_765_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_756_, v_x_757_, v_x_758_);
stack->m_obj
 = v_res_765_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1___boxed(lean_object* v_a_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
uint32_t v_a_boxed_769_; lean_object* v_res_770_; 
v_a_boxed_769_ = lean_unbox_uint32(v_a_766_);
lean_dec(v_a_766_);
v_res_770_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_boxed_769_, v_x_767_, v_x_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(lean_object* v___x_771_, lean_object* v_s_772_, lean_object* v_a_773_, lean_object* v_b_774_){
_start:
{
uint8_t v_decide_775_; 
v_decide_775_ = lean_nat_dec_eq(v_a_773_, v___x_771_);
if (v_decide_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_string_utf8_next_fast(v_s_772_, v_a_773_);
lean_dec(v_a_773_);
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = lean_nat_add(v_b_774_, v___x_777_);
lean_dec(v_b_774_);
v_a_773_ = v___x_776_;
v_b_774_ = v___x_778_;
goto _start;
}
else
{
lean_dec(v_a_773_);
return v_b_774_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg___boxed(lean_object* v___x_780_, lean_object* v_s_781_, lean_object* v_a_782_, lean_object* v_b_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_780_, v_s_781_, v_a_782_, v_b_783_);
lean_dec_ref(v_s_781_);
lean_dec(v___x_780_);
return v_res_784_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(lean_object* v_n_785_, uint32_t v_a_786_, lean_object* v_s_787_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_788_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = lean_string_utf8_byte_size(v_s_787_);
v___x_791_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_790_, v_s_787_, v___x_789_, v___x_789_);
v___x_792_ = lean_nat_sub(v_n_785_, v___x_791_);
lean_dec(v___x_791_);
v___x_793_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_786_, v___x_792_, v___x_788_);
v___x_794_ = lean_string_append(v___x_793_, v_s_787_);
return v___x_794_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_785_ = stack[0].m_obj;
uint32_t v_a_786_ = stack[1].m_num;
lean_object* v_s_787_ = stack[2].m_obj;
lean_object* v_res_795_;
v_res_795_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_n_785_, v_a_786_, v_s_787_);
stack->m_obj
 = v_res_795_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii___boxed(lean_object* v_n_796_, lean_object* v_a_797_, lean_object* v_s_798_){
_start:
{
uint32_t v_a_boxed_799_; lean_object* v_res_800_; 
v_a_boxed_799_ = lean_unbox_uint32(v_a_797_);
lean_dec(v_a_797_);
v_res_800_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_n_796_, v_a_boxed_799_, v_s_798_);
lean_dec_ref(v_s_798_);
lean_dec(v_n_796_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(lean_object* v___x_801_, lean_object* v___x_802_, lean_object* v_s_803_, lean_object* v_inst_804_, lean_object* v_R_805_, lean_object* v_a_806_, lean_object* v_b_807_, lean_object* v_c_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_801_, v_s_803_, v_a_806_, v_b_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___boxed(lean_object* v___x_810_, lean_object* v___x_811_, lean_object* v_s_812_, lean_object* v_inst_813_, lean_object* v_R_814_, lean_object* v_a_815_, lean_object* v_b_816_, lean_object* v_c_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(v___x_810_, v___x_811_, v_s_812_, v_inst_813_, v_R_814_, v_a_815_, v_b_816_, v_c_817_);
lean_dec_ref(v_s_812_);
lean_dec_ref(v___x_811_);
lean_dec(v___x_810_);
return v_res_818_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(lean_object* v_n_819_, uint32_t v_a_820_, lean_object* v_s_821_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_822_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_string_utf8_byte_size(v_s_821_);
v___x_825_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_824_, v_s_821_, v___x_823_, v___x_823_);
v___x_826_ = lean_nat_sub(v_n_819_, v___x_825_);
lean_dec(v___x_825_);
v___x_827_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_820_, v___x_826_, v___x_822_);
v___x_828_ = lean_string_append(v_s_821_, v___x_827_);
lean_dec_ref(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_819_ = stack[0].m_obj;
uint32_t v_a_820_ = stack[1].m_num;
lean_object* v_s_821_ = stack[2].m_obj;
lean_object* v_res_829_;
v_res_829_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_n_819_, v_a_820_, v_s_821_);
stack->m_obj
 = v_res_829_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii___boxed(lean_object* v_n_830_, lean_object* v_a_831_, lean_object* v_s_832_){
_start:
{
uint32_t v_a_boxed_833_; lean_object* v_res_834_; 
v_a_boxed_833_ = lean_unbox_uint32(v_a_831_);
lean_dec(v_a_831_);
v_res_834_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_n_830_, v_a_boxed_833_, v_s_832_);
lean_dec(v_n_830_);
return v_res_834_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_nat_to_int(v___x_835_);
return v___x_836_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad(lean_object* v_size_838_, lean_object* v_n_839_, uint8_t v_cut_840_){
_start:
{
lean_object* v_fst_842_; lean_object* v_snd_843_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_858_ = lean_int_dec_lt(v_n_839_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
v___x_859_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v_fst_842_ = v___x_859_;
v_snd_843_ = v_n_839_;
goto v___jp_841_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_861_ = lean_int_neg(v_n_839_);
lean_dec(v_n_839_);
v_fst_842_ = v___x_860_;
v_snd_843_ = v___x_861_;
goto v___jp_841_;
}
v___jp_841_:
{
lean_object* v_numStr_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_numStr_844_ = l_Int_repr(v_snd_843_);
lean_dec(v_snd_843_);
v___x_845_ = lean_string_utf8_byte_size(v_numStr_844_);
v___x_846_ = lean_nat_dec_lt(v_size_838_, v___x_845_);
if (v___x_846_ == 0)
{
uint32_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = 48;
v___x_848_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_size_838_, v___x_847_, v_numStr_844_);
lean_dec_ref(v_numStr_844_);
lean_inc_ref(v_fst_842_);
v___x_849_ = lean_string_append(v_fst_842_, v___x_848_);
lean_dec_ref(v___x_848_);
return v___x_849_;
}
else
{
if (v_cut_840_ == 0)
{
lean_object* v___x_850_; 
lean_inc_ref(v_fst_842_);
v___x_850_ = lean_string_append(v_fst_842_, v_numStr_844_);
lean_dec_ref(v_numStr_844_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_851_ = lean_nat_sub(v___x_845_, v_size_838_);
v___x_852_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_numStr_844_);
v___x_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_853_, 0, v_numStr_844_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
lean_ctor_set(v___x_853_, 2, v___x_845_);
v___x_854_ = l_String_Slice_Pos_nextn(v___x_853_, v___x_852_, v___x_851_);
lean_dec_ref_known(v___x_853_, 3);
v___x_855_ = lean_string_utf8_extract_fast(v_numStr_844_, v___x_854_, v___x_845_);
lean_dec(v___x_854_);
lean_dec_ref(v_numStr_844_);
lean_inc_ref(v_fst_842_);
v___x_856_ = lean_string_append(v_fst_842_, v___x_855_);
lean_dec_ref(v___x_855_);
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_pad_0interp(lean_interpreter_value* stack)
{
lean_object* v_size_838_ = stack[0].m_obj;
lean_object* v_n_839_ = stack[1].m_obj;
uint8_t v_cut_840_ = stack[2].m_num;
lean_object* v_res_862_;
v_res_862_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_size_838_, v_n_839_, v_cut_840_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___boxed(lean_object* v_size_863_, lean_object* v_n_864_, lean_object* v_cut_865_){
_start:
{
uint8_t v_cut_boxed_866_; lean_object* v_res_867_; 
v_cut_boxed_866_ = lean_unbox(v_cut_865_);
v_res_867_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_size_863_, v_n_864_, v_cut_boxed_866_);
lean_dec(v_size_863_);
return v_res_867_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(lean_object* v_size_868_, lean_object* v_n_869_, uint8_t v_cut_870_){
_start:
{
lean_object* v_fst_872_; lean_object* v_snd_873_; lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_887_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_888_ = lean_int_dec_lt(v_n_869_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
v___x_889_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v_fst_872_ = v___x_889_;
v_snd_873_ = v_n_869_;
goto v___jp_871_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_891_ = lean_int_neg(v_n_869_);
lean_dec(v_n_869_);
v_fst_872_ = v___x_890_;
v_snd_873_ = v___x_891_;
goto v___jp_871_;
}
v___jp_871_:
{
lean_object* v_numStr_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v_numStr_874_ = l_Int_repr(v_snd_873_);
lean_dec(v_snd_873_);
v___x_875_ = lean_string_length(v_numStr_874_);
v___x_876_ = lean_nat_dec_lt(v_size_868_, v___x_875_);
if (v___x_876_ == 0)
{
uint32_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = 48;
v___x_878_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_size_868_, v___x_877_, v_numStr_874_);
lean_dec(v_size_868_);
lean_inc_ref(v_fst_872_);
v___x_879_ = lean_string_append(v_fst_872_, v___x_878_);
lean_dec_ref(v___x_878_);
return v___x_879_;
}
else
{
if (v_cut_870_ == 0)
{
lean_object* v___x_880_; 
lean_dec(v_size_868_);
lean_inc_ref(v_fst_872_);
v___x_880_ = lean_string_append(v_fst_872_, v_numStr_874_);
lean_dec_ref(v_numStr_874_);
return v___x_880_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_string_utf8_byte_size(v_numStr_874_);
lean_inc_ref(v_numStr_874_);
v___x_883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_883_, 0, v_numStr_874_);
lean_ctor_set(v___x_883_, 1, v___x_881_);
lean_ctor_set(v___x_883_, 2, v___x_882_);
v___x_884_ = l_String_Slice_Pos_nextn(v___x_883_, v___x_881_, v_size_868_);
lean_dec_ref_known(v___x_883_, 3);
v___x_885_ = lean_string_utf8_extract_fast(v_numStr_874_, v___x_881_, v___x_884_);
lean_dec(v___x_884_);
lean_dec_ref(v_numStr_874_);
lean_inc_ref(v_fst_872_);
v___x_886_ = lean_string_append(v_fst_872_, v___x_885_);
lean_dec_ref(v___x_885_);
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_size_868_ = stack[0].m_obj;
lean_object* v_n_869_ = stack[1].m_obj;
uint8_t v_cut_870_ = stack[2].m_num;
lean_object* v_res_892_;
v_res_892_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(v_size_868_, v_n_869_, v_cut_870_);
stack->m_obj
 = v_res_892_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate___boxed(lean_object* v_size_893_, lean_object* v_n_894_, lean_object* v_cut_895_){
_start:
{
uint8_t v_cut_boxed_896_; lean_object* v_res_897_; 
v_cut_boxed_896_ = lean_unbox(v_cut_895_);
v_res_897_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(v_size_893_, v_n_894_, v_cut_boxed_896_);
return v_res_897_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(uint8_t v_x_898_){
_start:
{
if (v_x_898_ == 0)
{
lean_object* v___x_899_; 
v___x_899_ = lean_unsigned_to_nat(0u);
return v___x_899_;
}
else
{
lean_object* v___x_900_; 
v___x_900_ = lean_unsigned_to_nat(1u);
return v___x_900_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_898_ = stack[0].m_num;
lean_object* v_res_901_;
v_res_901_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_x_898_);
stack->m_obj
 = v_res_901_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___boxed(lean_object* v_x_902_){
_start:
{
uint8_t v_x_40__boxed_903_; lean_object* v_res_904_; 
v_x_40__boxed_903_ = lean_unbox(v_x_902_);
v_res_904_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_x_40__boxed_903_);
return v_res_904_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_906_ = lean_int_neg(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(lean_object* v_symbols_907_, lean_object* v_month_908_){
_start:
{
lean_object* v_monthLong_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_monthLong_909_ = lean_ctor_get(v_symbols_907_, 0);
v___x_910_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_911_ = lean_int_add(v_month_908_, v___x_910_);
v___x_912_ = l_Int_toNat(v___x_911_);
lean_dec(v___x_911_);
v___x_913_ = lean_array_fget_borrowed(v_monthLong_909_, v___x_912_);
lean_dec(v___x_912_);
lean_inc(v___x_913_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___boxed(lean_object* v_symbols_914_, lean_object* v_month_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_914_, v_month_915_);
lean_dec(v_month_915_);
lean_dec_ref(v_symbols_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(lean_object* v_symbols_917_, lean_object* v_month_918_){
_start:
{
lean_object* v_monthShort_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_monthShort_919_ = lean_ctor_get(v_symbols_917_, 1);
v___x_920_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_921_ = lean_int_add(v_month_918_, v___x_920_);
v___x_922_ = l_Int_toNat(v___x_921_);
lean_dec(v___x_921_);
v___x_923_ = lean_array_fget_borrowed(v_monthShort_919_, v___x_922_);
lean_dec(v___x_922_);
lean_inc(v___x_923_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort___boxed(lean_object* v_symbols_924_, lean_object* v_month_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_924_, v_month_925_);
lean_dec(v_month_925_);
lean_dec_ref(v_symbols_924_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(lean_object* v_symbols_927_, lean_object* v_month_928_){
_start:
{
lean_object* v_monthNarrow_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_monthNarrow_929_ = lean_ctor_get(v_symbols_927_, 2);
v___x_930_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_931_ = lean_int_add(v_month_928_, v___x_930_);
v___x_932_ = l_Int_toNat(v___x_931_);
lean_dec(v___x_931_);
v___x_933_ = lean_array_fget_borrowed(v_monthNarrow_929_, v___x_932_);
lean_dec(v___x_932_);
lean_inc(v___x_933_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow___boxed(lean_object* v_symbols_934_, lean_object* v_month_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_934_, v_month_935_);
lean_dec(v_month_935_);
lean_dec_ref(v_symbols_934_);
return v_res_936_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(lean_object* v_symbols_937_, uint8_t v_wd_938_){
_start:
{
lean_object* v_weekdayLong_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_weekdayLong_939_ = lean_ctor_get(v_symbols_937_, 3);
v___x_940_ = l_Std_Time_Weekday_toOrdinal(v_wd_938_);
v___x_941_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_942_ = lean_int_add(v___x_940_, v___x_941_);
lean_dec(v___x_940_);
v___x_943_ = l_Int_toNat(v___x_942_);
lean_dec(v___x_942_);
v___x_944_ = lean_array_fget_borrowed(v_weekdayLong_939_, v___x_943_);
lean_dec(v___x_943_);
lean_inc(v___x_944_);
return v___x_944_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong_0interp(lean_interpreter_value* stack)
{
lean_object* v_symbols_937_ = stack[0].m_obj;
uint8_t v_wd_938_ = stack[1].m_num;
lean_object* v_res_945_;
v_res_945_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_937_, v_wd_938_);
stack->m_obj
 = v_res_945_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong___boxed(lean_object* v_symbols_946_, lean_object* v_wd_947_){
_start:
{
uint8_t v_wd_boxed_948_; lean_object* v_res_949_; 
v_wd_boxed_948_ = lean_unbox(v_wd_947_);
v_res_949_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_946_, v_wd_boxed_948_);
lean_dec_ref(v_symbols_946_);
return v_res_949_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(lean_object* v_symbols_950_, uint8_t v_wd_951_){
_start:
{
lean_object* v_weekdayShort_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_weekdayShort_952_ = lean_ctor_get(v_symbols_950_, 4);
v___x_953_ = l_Std_Time_Weekday_toOrdinal(v_wd_951_);
v___x_954_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_955_ = lean_int_add(v___x_953_, v___x_954_);
lean_dec(v___x_953_);
v___x_956_ = l_Int_toNat(v___x_955_);
lean_dec(v___x_955_);
v___x_957_ = lean_array_fget_borrowed(v_weekdayShort_952_, v___x_956_);
lean_dec(v___x_956_);
lean_inc(v___x_957_);
return v___x_957_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort_0interp(lean_interpreter_value* stack)
{
lean_object* v_symbols_950_ = stack[0].m_obj;
uint8_t v_wd_951_ = stack[1].m_num;
lean_object* v_res_958_;
v_res_958_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_950_, v_wd_951_);
stack->m_obj
 = v_res_958_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort___boxed(lean_object* v_symbols_959_, lean_object* v_wd_960_){
_start:
{
uint8_t v_wd_boxed_961_; lean_object* v_res_962_; 
v_wd_boxed_961_ = lean_unbox(v_wd_960_);
v_res_962_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_959_, v_wd_boxed_961_);
lean_dec_ref(v_symbols_959_);
return v_res_962_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(lean_object* v_symbols_963_, uint8_t v_wd_964_){
_start:
{
lean_object* v_weekdayNarrow_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_weekdayNarrow_965_ = lean_ctor_get(v_symbols_963_, 5);
v___x_966_ = l_Std_Time_Weekday_toOrdinal(v_wd_964_);
v___x_967_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_968_ = lean_int_add(v___x_966_, v___x_967_);
lean_dec(v___x_966_);
v___x_969_ = l_Int_toNat(v___x_968_);
lean_dec(v___x_968_);
v___x_970_ = lean_array_fget_borrowed(v_weekdayNarrow_965_, v___x_969_);
lean_dec(v___x_969_);
lean_inc(v___x_970_);
return v___x_970_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow_0interp(lean_interpreter_value* stack)
{
lean_object* v_symbols_963_ = stack[0].m_obj;
uint8_t v_wd_964_ = stack[1].m_num;
lean_object* v_res_971_;
v_res_971_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_963_, v_wd_964_);
stack->m_obj
 = v_res_971_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow___boxed(lean_object* v_symbols_972_, lean_object* v_wd_973_){
_start:
{
uint8_t v_wd_boxed_974_; lean_object* v_res_975_; 
v_wd_boxed_974_ = lean_unbox(v_wd_973_);
v_res_975_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_972_, v_wd_boxed_974_);
lean_dec_ref(v_symbols_972_);
return v_res_975_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(lean_object* v_symbols_976_, uint8_t v_wd_977_){
_start:
{
lean_object* v_weekdayTwoLetter_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_weekdayTwoLetter_978_ = lean_ctor_get(v_symbols_976_, 6);
v___x_979_ = l_Std_Time_Weekday_toOrdinal(v_wd_977_);
v___x_980_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_981_ = lean_int_add(v___x_979_, v___x_980_);
lean_dec(v___x_979_);
v___x_982_ = l_Int_toNat(v___x_981_);
lean_dec(v___x_981_);
v___x_983_ = lean_array_fget_borrowed(v_weekdayTwoLetter_978_, v___x_982_);
lean_dec(v___x_982_);
lean_inc(v___x_983_);
return v___x_983_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter_0interp(lean_interpreter_value* stack)
{
lean_object* v_symbols_976_ = stack[0].m_obj;
uint8_t v_wd_977_ = stack[1].m_num;
lean_object* v_res_984_;
v_res_984_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_976_, v_wd_977_);
stack->m_obj
 = v_res_984_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter___boxed(lean_object* v_symbols_985_, lean_object* v_wd_986_){
_start:
{
uint8_t v_wd_boxed_987_; lean_object* v_res_988_; 
v_wd_boxed_987_ = lean_unbox(v_wd_986_);
v_res_988_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_985_, v_wd_boxed_987_);
lean_dec_ref(v_symbols_985_);
return v_res_988_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(lean_object* v_symbols_989_, uint8_t v_era_990_){
_start:
{
lean_object* v_eraShort_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_eraShort_991_ = lean_ctor_get(v_symbols_989_, 7);
v___x_992_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_990_);
v___x_993_ = lean_array_fget_borrowed(v_eraShort_991_, v___x_992_);
lean_dec(v___x_992_);
lean_inc(v___x_993_);
return v___x_993_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort_0interp(lean_interpreter_value* stack)
{
lean_object* v_symbols_989_ = stack[0].m_obj;
uint8_t v_era_990_ = stack[1].m_num;
lean_object* v_res_994_;
v_res_994_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_989_, v_era_990_);
stack->m_obj
 = v_res_994_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort___boxed(lean_object* v_symbols_995_, lean_object* v_era_996_){
_start:
{
uint8_t v_era_boxed_997_; lean_object* v_res_998_; 
v_era_boxed_997_ = lean_unbox(v_era_996_);
v_res_998_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_995_, v_era_boxed_997_);
lean_dec_ref(v_symbols_995_);
return v_res_998_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(lean_object* v_symbols_999_, uint8_t v_era_1000_){
_start:
{
lean_object* v_eraLong_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_eraLong_1001_ = lean_ctor_get(v_symbols_999_, 8);
v___x_1002_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1000_);
v___x_1003_ = lean_array_fget_borrowed(v_eraLong_1001_, v___x_1002_);
lean_dec(v___x_1002_);
lean_inc(v___x_1003_);
return v___x_1003_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong_0interp(lean_interpreter_value* stack)
{
lean_object* v_symbols_999_ = stack[0].m_obj;
uint8_t v_era_1000_ = stack[1].m_num;
lean_object* v_res_1004_;
v_res_1004_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_999_, v_era_1000_);
stack->m_obj
 = v_res_1004_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong___boxed(lean_object* v_symbols_1005_, lean_object* v_era_1006_){
_start:
{
uint8_t v_era_boxed_1007_; lean_object* v_res_1008_; 
v_era_boxed_1007_ = lean_unbox(v_era_1006_);
v_res_1008_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1005_, v_era_boxed_1007_);
lean_dec_ref(v_symbols_1005_);
return v_res_1008_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(lean_object* v_symbols_1009_, uint8_t v_era_1010_){
_start:
{
lean_object* v_eraNarrow_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_eraNarrow_1011_ = lean_ctor_get(v_symbols_1009_, 9);
v___x_1012_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1010_);
v___x_1013_ = lean_array_fget_borrowed(v_eraNarrow_1011_, v___x_1012_);
lean_dec(v___x_1012_);
lean_inc(v___x_1013_);
return v___x_1013_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow_0interp(lean_interpreter_value* stack)
{
lean_object* v_symbols_1009_ = stack[0].m_obj;
uint8_t v_era_1010_ = stack[1].m_num;
lean_object* v_res_1014_;
v_res_1014_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1009_, v_era_1010_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow___boxed(lean_object* v_symbols_1015_, lean_object* v_era_1016_){
_start:
{
uint8_t v_era_boxed_1017_; lean_object* v_res_1018_; 
v_era_boxed_1017_ = lean_unbox(v_era_1016_);
v_res_1018_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1015_, v_era_boxed_1017_);
lean_dec_ref(v_symbols_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(lean_object* v_x_1023_){
_start:
{
lean_object* v_natZero_1024_; lean_object* v_intZero_1025_; uint8_t v_isNeg_1026_; lean_object* v_a_1027_; uint8_t v_isZero_1028_; lean_object* v_one_1029_; lean_object* v_n_1030_; uint8_t v_isZero_1031_; 
v_natZero_1024_ = lean_unsigned_to_nat(0u);
v_intZero_1025_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v_isNeg_1026_ = lean_int_dec_lt(v_x_1023_, v_intZero_1025_);
v_a_1027_ = lean_nat_abs(v_x_1023_);
v_isZero_1028_ = lean_nat_dec_eq(v_a_1027_, v_natZero_1024_);
v_one_1029_ = lean_unsigned_to_nat(1u);
v_n_1030_ = lean_nat_sub(v_a_1027_, v_one_1029_);
lean_dec(v_a_1027_);
v_isZero_1031_ = lean_nat_dec_eq(v_n_1030_, v_natZero_1024_);
if (v_isZero_1031_ == 1)
{
lean_object* v___x_1032_; 
lean_dec(v_n_1030_);
v___x_1032_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
return v___x_1032_;
}
else
{
lean_object* v_n_1033_; uint8_t v_isZero_1034_; 
v_n_1033_ = lean_nat_sub(v_n_1030_, v_one_1029_);
lean_dec(v_n_1030_);
v_isZero_1034_ = lean_nat_dec_eq(v_n_1033_, v_natZero_1024_);
if (v_isZero_1034_ == 1)
{
lean_object* v___x_1035_; 
lean_dec(v_n_1033_);
v___x_1035_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
return v___x_1035_;
}
else
{
lean_object* v_n_1036_; uint8_t v_isZero_1037_; 
v_n_1036_ = lean_nat_sub(v_n_1033_, v_one_1029_);
lean_dec(v_n_1033_);
v_isZero_1037_ = lean_nat_dec_eq(v_n_1036_, v_natZero_1024_);
if (v_isZero_1037_ == 1)
{
lean_object* v___x_1038_; 
lean_dec(v_n_1036_);
v___x_1038_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
return v___x_1038_;
}
else
{
lean_object* v_n_1039_; uint8_t v_isZero_1040_; lean_object* v___x_1041_; 
v_n_1039_ = lean_nat_sub(v_n_1036_, v_one_1029_);
lean_dec(v_n_1036_);
v_isZero_1040_ = lean_nat_dec_eq(v_n_1039_, v_natZero_1024_);
lean_dec(v_n_1039_);
v___x_1041_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___boxed(lean_object* v_x_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_x_1042_);
lean_dec(v_x_1042_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(lean_object* v_symbols_1044_, lean_object* v_q_1045_){
_start:
{
lean_object* v_quarterShort_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_quarterShort_1046_ = lean_ctor_get(v_symbols_1044_, 10);
v___x_1047_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1048_ = lean_int_add(v_q_1045_, v___x_1047_);
v___x_1049_ = l_Int_toNat(v___x_1048_);
lean_dec(v___x_1048_);
v___x_1050_ = lean_array_fget_borrowed(v_quarterShort_1046_, v___x_1049_);
lean_dec(v___x_1049_);
lean_inc(v___x_1050_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort___boxed(lean_object* v_symbols_1051_, lean_object* v_q_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1051_, v_q_1052_);
lean_dec(v_q_1052_);
lean_dec_ref(v_symbols_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(lean_object* v_symbols_1054_, lean_object* v_q_1055_){
_start:
{
lean_object* v_quarterLong_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_quarterLong_1056_ = lean_ctor_get(v_symbols_1054_, 11);
v___x_1057_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1058_ = lean_int_add(v_q_1055_, v___x_1057_);
v___x_1059_ = l_Int_toNat(v___x_1058_);
lean_dec(v___x_1058_);
v___x_1060_ = lean_array_fget_borrowed(v_quarterLong_1056_, v___x_1059_);
lean_dec(v___x_1059_);
lean_inc(v___x_1060_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong___boxed(lean_object* v_symbols_1061_, lean_object* v_q_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1061_, v_q_1062_);
lean_dec(v_q_1062_);
lean_dec_ref(v_symbols_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(lean_object* v_symbols_1064_, lean_object* v_q_1065_){
_start:
{
lean_object* v_quarterNarrow_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_quarterNarrow_1066_ = lean_ctor_get(v_symbols_1064_, 12);
v___x_1067_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1068_ = lean_int_add(v_q_1065_, v___x_1067_);
v___x_1069_ = l_Int_toNat(v___x_1068_);
lean_dec(v___x_1068_);
v___x_1070_ = lean_array_fget_borrowed(v_quarterNarrow_1066_, v___x_1069_);
lean_dec(v___x_1069_);
lean_inc(v___x_1070_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow___boxed(lean_object* v_symbols_1071_, lean_object* v_q_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1071_, v_q_1072_);
lean_dec(v_q_1072_);
lean_dec_ref(v_symbols_1071_);
return v_res_1073_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(lean_object* v_symbols_1074_, uint8_t v_marker_1075_){
_start:
{
if (v_marker_1075_ == 0)
{
lean_object* v_amShort_1076_; 
v_amShort_1076_ = lean_ctor_get(v_symbols_1074_, 13);
lean_inc_ref(v_amShort_1076_);
return v_amShort_1076_;
}
else
{
lean_object* v_pmShort_1077_; 
v_pmShort_1077_ = lean_ctor_get(v_symbols_1074_, 14);
lean_inc_ref(v_pmShort_1077_);
return v_pmShort_1077_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort_0interp(lean_interpreter_value* stack)
{
lean_object* v_symbols_1074_ = stack[0].m_obj;
uint8_t v_marker_1075_ = stack[1].m_num;
lean_object* v_res_1078_;
v_res_1078_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1074_, v_marker_1075_);
stack->m_obj
 = v_res_1078_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort___boxed(lean_object* v_symbols_1079_, lean_object* v_marker_1080_){
_start:
{
uint8_t v_marker_boxed_1081_; lean_object* v_res_1082_; 
v_marker_boxed_1081_ = lean_unbox(v_marker_1080_);
v_res_1082_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1079_, v_marker_boxed_1081_);
lean_dec_ref(v_symbols_1079_);
return v_res_1082_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(lean_object* v_symbols_1083_, uint8_t v_marker_1084_){
_start:
{
if (v_marker_1084_ == 0)
{
lean_object* v_amLong_1085_; 
v_amLong_1085_ = lean_ctor_get(v_symbols_1083_, 15);
lean_inc_ref(v_amLong_1085_);
return v_amLong_1085_;
}
else
{
lean_object* v_pmLong_1086_; 
v_pmLong_1086_ = lean_ctor_get(v_symbols_1083_, 16);
lean_inc_ref(v_pmLong_1086_);
return v_pmLong_1086_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong_0interp(lean_interpreter_value* stack)
{
lean_object* v_symbols_1083_ = stack[0].m_obj;
uint8_t v_marker_1084_ = stack[1].m_num;
lean_object* v_res_1087_;
v_res_1087_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(v_symbols_1083_, v_marker_1084_);
stack->m_obj
 = v_res_1087_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong___boxed(lean_object* v_symbols_1088_, lean_object* v_marker_1089_){
_start:
{
uint8_t v_marker_boxed_1090_; lean_object* v_res_1091_; 
v_marker_boxed_1090_ = lean_unbox(v_marker_1089_);
v_res_1091_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(v_symbols_1088_, v_marker_boxed_1090_);
lean_dec_ref(v_symbols_1088_);
return v_res_1091_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(lean_object* v_symbols_1092_, uint8_t v_marker_1093_){
_start:
{
if (v_marker_1093_ == 0)
{
lean_object* v_amNarrow_1094_; 
v_amNarrow_1094_ = lean_ctor_get(v_symbols_1092_, 17);
lean_inc_ref(v_amNarrow_1094_);
return v_amNarrow_1094_;
}
else
{
lean_object* v_pmNarrow_1095_; 
v_pmNarrow_1095_ = lean_ctor_get(v_symbols_1092_, 18);
lean_inc_ref(v_pmNarrow_1095_);
return v_pmNarrow_1095_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow_0interp(lean_interpreter_value* stack)
{
lean_object* v_symbols_1092_ = stack[0].m_obj;
uint8_t v_marker_1093_ = stack[1].m_num;
lean_object* v_res_1096_;
v_res_1096_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1092_, v_marker_1093_);
stack->m_obj
 = v_res_1096_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow___boxed(lean_object* v_symbols_1097_, lean_object* v_marker_1098_){
_start:
{
uint8_t v_marker_boxed_1099_; lean_object* v_res_1100_; 
v_marker_boxed_1099_ = lean_unbox(v_marker_1098_);
v_res_1100_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1097_, v_marker_boxed_1099_);
lean_dec_ref(v_symbols_1097_);
return v_res_1100_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(lean_object* v_dp_1101_, uint8_t v_period_1102_){
_start:
{
switch(v_period_1102_)
{
case 0:
{
lean_object* v_am_1103_; 
v_am_1103_ = lean_ctor_get(v_dp_1101_, 0);
lean_inc_ref(v_am_1103_);
return v_am_1103_;
}
case 1:
{
lean_object* v_pm_1104_; 
v_pm_1104_ = lean_ctor_get(v_dp_1101_, 1);
lean_inc_ref(v_pm_1104_);
return v_pm_1104_;
}
case 2:
{
lean_object* v_noon_1105_; 
v_noon_1105_ = lean_ctor_get(v_dp_1101_, 2);
lean_inc_ref(v_noon_1105_);
return v_noon_1105_;
}
default: 
{
lean_object* v_midnight_1106_; 
v_midnight_1106_ = lean_ctor_get(v_dp_1101_, 3);
lean_inc_ref(v_midnight_1106_);
return v_midnight_1106_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod_0interp(lean_interpreter_value* stack)
{
lean_object* v_dp_1101_ = stack[0].m_obj;
uint8_t v_period_1102_ = stack[1].m_num;
lean_object* v_res_1107_;
v_res_1107_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dp_1101_, v_period_1102_);
stack->m_obj
 = v_res_1107_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod___boxed(lean_object* v_dp_1108_, lean_object* v_period_1109_){
_start:
{
uint8_t v_period_boxed_1110_; lean_object* v_res_1111_; 
v_period_boxed_1110_ = lean_unbox(v_period_1109_);
v_res_1111_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dp_1108_, v_period_boxed_1110_);
lean_dec_ref(v_dp_1108_);
return v_res_1111_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t v_x_1112_){
_start:
{
switch(v_x_1112_)
{
case 0:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
return v___x_1113_;
}
case 1:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
return v___x_1114_;
}
case 2:
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_unsigned_to_nat(2u);
return v___x_1115_;
}
case 3:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_unsigned_to_nat(3u);
return v___x_1116_;
}
case 4:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_unsigned_to_nat(4u);
return v___x_1117_;
}
default: 
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_unsigned_to_nat(5u);
return v___x_1118_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1112_ = stack[0].m_num;
lean_object* v_res_1119_;
v_res_1119_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_x_1112_);
stack->m_obj
 = v_res_1119_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object* v_x_1120_){
_start:
{
uint8_t v_x_112__boxed_1121_; lean_object* v_res_1122_; 
v_x_112__boxed_1121_ = lean_unbox(v_x_1120_);
v_res_1122_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_x_112__boxed_1121_);
return v_res_1122_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(lean_object* v_arr_1123_, uint8_t v_period_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_period_1124_);
v___x_1126_ = lean_array_fget_borrowed(v_arr_1123_, v___x_1125_);
lean_dec(v___x_1125_);
lean_inc(v___x_1126_);
return v___x_1126_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod_0interp(lean_interpreter_value* stack)
{
lean_object* v_arr_1123_ = stack[0].m_obj;
uint8_t v_period_1124_ = stack[1].m_num;
lean_object* v_res_1127_;
v_res_1127_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_arr_1123_, v_period_1124_);
stack->m_obj
 = v_res_1127_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod___boxed(lean_object* v_arr_1128_, lean_object* v_period_1129_){
_start:
{
uint8_t v_period_boxed_1130_; lean_object* v_res_1131_; 
v_period_boxed_1130_ = lean_unbox(v_period_1129_);
v_res_1131_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_arr_1128_, v_period_boxed_1130_);
lean_dec_ref(v_arr_1128_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(lean_object* v_data_1133_){
_start:
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1135_ = lean_int_dec_lt(v_data_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1137_ = l_Int_repr(v_data_1133_);
v___x_1138_ = lean_string_append(v___x_1136_, v___x_1137_);
lean_dec_ref(v___x_1137_);
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Int_repr(v_data_1133_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___boxed(lean_object* v_data_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(v_data_1140_);
lean_dec(v_data_1140_);
return v_res_1141_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl(uint8_t v_x_1142_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_box(v_x_1142_);
v___x_1144_ = lean_obj_tag_nat(v___x_1143_);
lean_dec(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1142_ = stack[0].m_num;
lean_object* v_res_1145_;
v_res_1145_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl(v_x_1142_);
stack->m_obj
 = v_res_1145_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl___boxed(lean_object* v_x_1146_){
_start:
{
uint8_t v_x_4__boxed_1147_; lean_object* v_res_1148_; 
v_x_4__boxed_1147_ = lean_unbox(v_x_1146_);
v_res_1148_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl(v_x_4__boxed_1147_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(lean_object* v_k_1149_){
_start:
{
lean_inc(v_k_1149_);
return v_k_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg___boxed(lean_object* v_k_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(v_k_1150_);
lean_dec(v_k_1150_);
return v_res_1151_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_object* v_motive_1152_, lean_object* v_ctorIdx_1153_, uint8_t v_t_1154_, lean_object* v_h_1155_, lean_object* v_k_1156_){
_start:
{
lean_inc(v_k_1156_);
return v_k_1156_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_1153_ = stack[1].m_obj;
uint8_t v_t_1154_ = stack[2].m_num;
lean_object* v_k_1156_ = stack[4].m_obj;
lean_object* v_res_1157_;
v_res_1157_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_box(0), v_ctorIdx_1153_, v_t_1154_, lean_box(0), v_k_1156_);
stack->m_obj
 = v_res_1157_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___boxed(lean_object* v_motive_1158_, lean_object* v_ctorIdx_1159_, lean_object* v_t_1160_, lean_object* v_h_1161_, lean_object* v_k_1162_){
_start:
{
uint8_t v_t_boxed_1163_; lean_object* v_res_1164_; 
v_t_boxed_1163_ = lean_unbox(v_t_1160_);
v_res_1164_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(v_motive_1158_, v_ctorIdx_1159_, v_t_boxed_1163_, v_h_1161_, v_k_1162_);
lean_dec(v_k_1162_);
lean_dec(v_ctorIdx_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(lean_object* v_yes_1165_){
_start:
{
lean_inc(v_yes_1165_);
return v_yes_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg___boxed(lean_object* v_yes_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(v_yes_1166_);
lean_dec(v_yes_1166_);
return v_res_1167_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_object* v_motive_1168_, uint8_t v_t_1169_, lean_object* v_h_1170_, lean_object* v_yes_1171_){
_start:
{
lean_inc(v_yes_1171_);
return v_yes_1171_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1169_ = stack[1].m_num;
lean_object* v_yes_1171_ = stack[3].m_obj;
lean_object* v_res_1172_;
v_res_1172_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_box(0), v_t_1169_, lean_box(0), v_yes_1171_);
stack->m_obj
 = v_res_1172_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___boxed(lean_object* v_motive_1173_, lean_object* v_t_1174_, lean_object* v_h_1175_, lean_object* v_yes_1176_){
_start:
{
uint8_t v_t_boxed_1177_; lean_object* v_res_1178_; 
v_t_boxed_1177_ = lean_unbox(v_t_1174_);
v_res_1178_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(v_motive_1173_, v_t_boxed_1177_, v_h_1175_, v_yes_1176_);
lean_dec(v_yes_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(lean_object* v_no_1179_){
_start:
{
lean_inc(v_no_1179_);
return v_no_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg___boxed(lean_object* v_no_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(v_no_1180_);
lean_dec(v_no_1180_);
return v_res_1181_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_object* v_motive_1182_, uint8_t v_t_1183_, lean_object* v_h_1184_, lean_object* v_no_1185_){
_start:
{
lean_inc(v_no_1185_);
return v_no_1185_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1183_ = stack[1].m_num;
lean_object* v_no_1185_ = stack[3].m_obj;
lean_object* v_res_1186_;
v_res_1186_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_box(0), v_t_1183_, lean_box(0), v_no_1185_);
stack->m_obj
 = v_res_1186_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___boxed(lean_object* v_motive_1187_, lean_object* v_t_1188_, lean_object* v_h_1189_, lean_object* v_no_1190_){
_start:
{
uint8_t v_t_boxed_1191_; lean_object* v_res_1192_; 
v_t_boxed_1191_ = lean_unbox(v_t_1188_);
v_res_1192_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(v_motive_1187_, v_t_boxed_1191_, v_h_1189_, v_no_1190_);
lean_dec(v_no_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(lean_object* v_optional_1193_){
_start:
{
lean_inc(v_optional_1193_);
return v_optional_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg___boxed(lean_object* v_optional_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(v_optional_1194_);
lean_dec(v_optional_1194_);
return v_res_1195_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_object* v_motive_1196_, uint8_t v_t_1197_, lean_object* v_h_1198_, lean_object* v_optional_1199_){
_start:
{
lean_inc(v_optional_1199_);
return v_optional_1199_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1197_ = stack[1].m_num;
lean_object* v_optional_1199_ = stack[3].m_obj;
lean_object* v_res_1200_;
v_res_1200_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_box(0), v_t_1197_, lean_box(0), v_optional_1199_);
stack->m_obj
 = v_res_1200_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___boxed(lean_object* v_motive_1201_, lean_object* v_t_1202_, lean_object* v_h_1203_, lean_object* v_optional_1204_){
_start:
{
uint8_t v_t_boxed_1205_; lean_object* v_res_1206_; 
v_t_boxed_1205_ = lean_unbox(v_t_1202_);
v_res_1206_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(v_motive_1201_, v_t_boxed_1205_, v_h_1203_, v_optional_1204_);
lean_dec(v_optional_1204_);
return v_res_1206_;
}
}
uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(uint8_t v_x_1207_, uint8_t v_y_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1209_ = lean_box(v_x_1207_);
v___x_1210_ = lean_obj_tag_nat(v___x_1209_);
lean_dec(v___x_1209_);
v___x_1211_ = lean_box(v_y_1208_);
v___x_1212_ = lean_obj_tag_nat(v___x_1211_);
lean_dec(v___x_1211_);
v___x_1213_ = lean_nat_dec_eq(v___x_1210_, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1207_ = stack[0].m_num;
uint8_t v_y_1208_ = stack[1].m_num;
uint8_t v_res_1214_;
v_res_1214_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_x_1207_, v_y_1208_);
stack->m_num = v_res_1214_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq___boxed(lean_object* v_x_1215_, lean_object* v_y_1216_){
_start:
{
uint8_t v_x_24__boxed_1217_; uint8_t v_y_25__boxed_1218_; uint8_t v_res_1219_; lean_object* v_r_1220_; 
v_x_24__boxed_1217_ = lean_unbox(v_x_1215_);
v_y_25__boxed_1218_ = lean_unbox(v_y_1216_);
v_res_1219_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_x_24__boxed_1217_, v_y_25__boxed_1218_);
v_r_1220_ = lean_box(v_res_1219_);
return v_r_1220_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__1(lean_object* v_a_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Rat_ofInt(v_a_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_unsigned_to_nat(1000000000u);
v___x_1227_ = lean_nat_to_int(v___x_1226_);
return v___x_1227_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(lean_object* v_offset_1228_, uint8_t v_withMinutes_1229_, uint8_t v_withSeconds_1230_, uint8_t v_colon_1231_, uint8_t v_padHour_1232_){
_start:
{
lean_object* v___y_1234_; lean_object* v___y_1235_; uint32_t v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1245_; lean_object* v___y_1246_; uint32_t v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1252_; lean_object* v___y_1253_; uint32_t v___y_1254_; lean_object* v___y_1255_; uint8_t v___y_1256_; lean_object* v___y_1258_; uint8_t v___y_1259_; uint32_t v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1270_; lean_object* v___y_1271_; uint8_t v___y_1272_; uint32_t v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1282_; lean_object* v___y_1283_; uint8_t v___y_1284_; uint32_t v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1290_; lean_object* v___y_1291_; uint8_t v___y_1292_; uint32_t v___y_1293_; lean_object* v___y_1294_; uint8_t v___y_1295_; lean_object* v___y_1297_; lean_object* v___y_1298_; uint32_t v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v_fst_1311_; lean_object* v_snd_1312_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1324_ = lean_int_dec_le(v___x_1323_, v_offset_1228_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1326_ = lean_int_neg(v_offset_1228_);
lean_dec(v_offset_1228_);
v_fst_1311_ = v___x_1325_;
v_snd_1312_ = v___x_1326_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1327_; 
v___x_1327_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1311_ = v___x_1327_;
v_snd_1312_ = v_offset_1228_;
goto v___jp_1310_;
}
v___jp_1233_:
{
lean_object* v_second_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_second_1239_ = lean_ctor_get(v___y_1234_, 2);
lean_inc(v_second_1239_);
lean_dec_ref(v___y_1234_);
v___x_1240_ = lean_string_append(v___y_1235_, v___y_1238_);
v___x_1241_ = l_Int_repr(v_second_1239_);
lean_dec(v_second_1239_);
v___x_1242_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1237_, v___y_1236_, v___x_1241_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = lean_string_append(v___x_1240_, v___x_1242_);
lean_dec_ref(v___x_1242_);
return v___x_1243_;
}
v___jp_1244_:
{
if (v_colon_1231_ == 0)
{
lean_object* v___x_1249_; 
v___x_1249_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___y_1234_ = v___y_1245_;
v___y_1235_ = v___y_1246_;
v___y_1236_ = v___y_1247_;
v___y_1237_ = v___y_1248_;
v___y_1238_ = v___x_1249_;
goto v___jp_1233_;
}
else
{
lean_object* v___x_1250_; 
v___x_1250_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1234_ = v___y_1245_;
v___y_1235_ = v___y_1246_;
v___y_1236_ = v___y_1247_;
v___y_1237_ = v___y_1248_;
v___y_1238_ = v___x_1250_;
goto v___jp_1233_;
}
}
v___jp_1251_:
{
if (v___y_1256_ == 0)
{
lean_dec_ref(v___y_1252_);
return v___y_1253_;
}
else
{
v___y_1245_ = v___y_1252_;
v___y_1246_ = v___y_1253_;
v___y_1247_ = v___y_1254_;
v___y_1248_ = v___y_1255_;
goto v___jp_1244_;
}
}
v___jp_1257_:
{
uint8_t v___x_1263_; 
v___x_1263_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1230_, v___y_1259_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = 2;
v___x_1265_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1230_, v___x_1264_);
if (v___x_1265_ == 0)
{
v___y_1252_ = v___y_1258_;
v___y_1253_ = v___y_1262_;
v___y_1254_ = v___y_1260_;
v___y_1255_ = v___y_1261_;
v___y_1256_ = v___x_1265_;
goto v___jp_1251_;
}
else
{
lean_object* v_second_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_second_1266_ = lean_ctor_get(v___y_1258_, 2);
v___x_1267_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1268_ = lean_int_dec_eq(v_second_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
v___y_1252_ = v___y_1258_;
v___y_1253_ = v___y_1262_;
v___y_1254_ = v___y_1260_;
v___y_1255_ = v___y_1261_;
v___y_1256_ = v___x_1265_;
goto v___jp_1251_;
}
else
{
v___y_1252_ = v___y_1258_;
v___y_1253_ = v___y_1262_;
v___y_1254_ = v___y_1260_;
v___y_1255_ = v___y_1261_;
v___y_1256_ = v___x_1263_;
goto v___jp_1251_;
}
}
}
else
{
v___y_1245_ = v___y_1258_;
v___y_1246_ = v___y_1262_;
v___y_1247_ = v___y_1260_;
v___y_1248_ = v___y_1261_;
goto v___jp_1244_;
}
}
v___jp_1269_:
{
lean_object* v_minute_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_minute_1276_ = lean_ctor_get(v___y_1270_, 1);
v___x_1277_ = lean_string_append(v___y_1271_, v___y_1275_);
v___x_1278_ = l_Int_repr(v_minute_1276_);
v___x_1279_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1274_, v___y_1273_, v___x_1278_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = lean_string_append(v___x_1277_, v___x_1279_);
lean_dec_ref(v___x_1279_);
v___y_1258_ = v___y_1270_;
v___y_1259_ = v___y_1272_;
v___y_1260_ = v___y_1273_;
v___y_1261_ = v___y_1274_;
v___y_1262_ = v___x_1280_;
goto v___jp_1257_;
}
v___jp_1281_:
{
if (v_colon_1231_ == 0)
{
lean_object* v___x_1287_; 
v___x_1287_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___y_1270_ = v___y_1283_;
v___y_1271_ = v___y_1282_;
v___y_1272_ = v___y_1284_;
v___y_1273_ = v___y_1285_;
v___y_1274_ = v___y_1286_;
v___y_1275_ = v___x_1287_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1288_; 
v___x_1288_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1270_ = v___y_1283_;
v___y_1271_ = v___y_1282_;
v___y_1272_ = v___y_1284_;
v___y_1273_ = v___y_1285_;
v___y_1274_ = v___y_1286_;
v___y_1275_ = v___x_1288_;
goto v___jp_1269_;
}
}
v___jp_1289_:
{
if (v___y_1295_ == 0)
{
v___y_1258_ = v___y_1290_;
v___y_1259_ = v___y_1292_;
v___y_1260_ = v___y_1293_;
v___y_1261_ = v___y_1294_;
v___y_1262_ = v___y_1291_;
goto v___jp_1257_;
}
else
{
v___y_1282_ = v___y_1291_;
v___y_1283_ = v___y_1290_;
v___y_1284_ = v___y_1292_;
v___y_1285_ = v___y_1293_;
v___y_1286_ = v___y_1294_;
goto v___jp_1281_;
}
}
v___jp_1296_:
{
lean_object* v_data_1302_; uint8_t v___x_1303_; uint8_t v___x_1304_; 
lean_inc_ref(v___y_1297_);
v_data_1302_ = lean_string_append(v___y_1297_, v___y_1301_);
lean_dec_ref(v___y_1301_);
v___x_1303_ = 0;
v___x_1304_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1229_, v___x_1303_);
if (v___x_1304_ == 0)
{
uint8_t v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = 2;
v___x_1306_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1229_, v___x_1305_);
if (v___x_1306_ == 0)
{
v___y_1290_ = v___y_1298_;
v___y_1291_ = v_data_1302_;
v___y_1292_ = v___x_1303_;
v___y_1293_ = v___y_1299_;
v___y_1294_ = v___y_1300_;
v___y_1295_ = v___x_1306_;
goto v___jp_1289_;
}
else
{
lean_object* v_minute_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_minute_1307_ = lean_ctor_get(v___y_1298_, 1);
v___x_1308_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1309_ = lean_int_dec_eq(v_minute_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
v___y_1290_ = v___y_1298_;
v___y_1291_ = v_data_1302_;
v___y_1292_ = v___x_1303_;
v___y_1293_ = v___y_1299_;
v___y_1294_ = v___y_1300_;
v___y_1295_ = v___x_1306_;
goto v___jp_1289_;
}
else
{
v___y_1290_ = v___y_1298_;
v___y_1291_ = v_data_1302_;
v___y_1292_ = v___x_1303_;
v___y_1293_ = v___y_1299_;
v___y_1294_ = v___y_1300_;
v___y_1295_ = v___x_1304_;
goto v___jp_1289_;
}
}
}
else
{
v___y_1282_ = v_data_1302_;
v___y_1283_ = v___y_1298_;
v___y_1284_ = v___x_1303_;
v___y_1285_ = v___y_1299_;
v___y_1286_ = v___y_1300_;
goto v___jp_1281_;
}
}
v___jp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_time_1315_; lean_object* v___x_1316_; uint32_t v___x_1317_; 
v___x_1313_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1314_ = lean_int_mul(v_snd_1312_, v___x_1313_);
lean_dec(v_snd_1312_);
v_time_1315_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1314_);
lean_dec(v___x_1314_);
v___x_1316_ = lean_unsigned_to_nat(2u);
v___x_1317_ = 48;
if (v_padHour_1232_ == 0)
{
lean_object* v_hour_1318_; lean_object* v___x_1319_; 
v_hour_1318_ = lean_ctor_get(v_time_1315_, 0);
v___x_1319_ = l_Int_repr(v_hour_1318_);
v___y_1297_ = v_fst_1311_;
v___y_1298_ = v_time_1315_;
v___y_1299_ = v___x_1317_;
v___y_1300_ = v___x_1316_;
v___y_1301_ = v___x_1319_;
goto v___jp_1296_;
}
else
{
lean_object* v_hour_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v_hour_1320_ = lean_ctor_get(v_time_1315_, 0);
v___x_1321_ = l_Int_repr(v_hour_1320_);
v___x_1322_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1316_, v___x_1317_, v___x_1321_);
lean_dec_ref(v___x_1321_);
v___y_1297_ = v_fst_1311_;
v___y_1298_ = v_time_1315_;
v___y_1299_ = v___x_1317_;
v___y_1300_ = v___x_1316_;
v___y_1301_ = v___x_1322_;
goto v___jp_1296_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString_0interp(lean_interpreter_value* stack)
{
lean_object* v_offset_1228_ = stack[0].m_obj;
uint8_t v_withMinutes_1229_ = stack[1].m_num;
uint8_t v_withSeconds_1230_ = stack[2].m_num;
uint8_t v_colon_1231_ = stack[3].m_num;
uint8_t v_padHour_1232_ = stack[4].m_num;
lean_object* v_res_1328_;
v_res_1328_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1228_, v_withMinutes_1229_, v_withSeconds_1230_, v_colon_1231_, v_padHour_1232_);
stack->m_obj
 = v_res_1328_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___boxed(lean_object* v_offset_1329_, lean_object* v_withMinutes_1330_, lean_object* v_withSeconds_1331_, lean_object* v_colon_1332_, lean_object* v_padHour_1333_){
_start:
{
uint8_t v_withMinutes_boxed_1334_; uint8_t v_withSeconds_boxed_1335_; uint8_t v_colon_boxed_1336_; uint8_t v_padHour_boxed_1337_; lean_object* v_res_1338_; 
v_withMinutes_boxed_1334_ = lean_unbox(v_withMinutes_1330_);
v_withSeconds_boxed_1335_ = lean_unbox(v_withSeconds_1331_);
v_colon_boxed_1336_ = lean_unbox(v_colon_1332_);
v_padHour_boxed_1337_ = lean_unbox(v_padHour_1333_);
v_res_1338_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1329_, v_withMinutes_boxed_1334_, v_withSeconds_boxed_1335_, v_colon_boxed_1336_, v_padHour_boxed_1337_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0_spec__0(lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_nat_to_int(v_a_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(lean_object* v_a_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_nat_to_int(v_a_1341_);
v___x_1343_ = l_Rat_ofInt(v___x_1342_);
return v___x_1343_;
}
}
uint8_t l_Std_Time_classifyDayPeriod___lam__0(lean_object* v_minute_1344_, lean_object* v_second_1345_, lean_object* v_00___1346_){
_start:
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1348_ = lean_int_dec_eq(v_minute_1344_, v___x_1347_);
if (v___x_1348_ == 0)
{
return v___x_1348_;
}
else
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_int_dec_eq(v_second_1345_, v___x_1347_);
return v___x_1349_;
}
}
}
LEAN_EXPORT void l_Std_Time_classifyDayPeriod___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_minute_1344_ = stack[0].m_obj;
lean_object* v_second_1345_ = stack[1].m_obj;
lean_object* v_00___1346_ = stack[2].m_obj;
uint8_t v_res_1350_;
v_res_1350_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1344_, v_second_1345_, v_00___1346_);
stack->m_num = v_res_1350_;
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___lam__0___boxed(lean_object* v_minute_1351_, lean_object* v_second_1352_, lean_object* v_00___1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1351_, v_second_1352_, v_00___1353_);
lean_dec(v_second_1352_);
lean_dec(v_minute_1351_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
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
uint8_t l_Std_Time_classifyDayPeriod(lean_object* v_hour_1358_, lean_object* v_minute_1359_, lean_object* v_second_1360_){
_start:
{
lean_object* v___y_1362_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1373_ = lean_int_dec_eq(v_hour_1358_, v___x_1372_);
if (v___x_1373_ == 0)
{
goto v___jp_1366_;
}
else
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1359_, v_second_1360_, v___x_1374_);
if (v___x_1375_ == 0)
{
goto v___jp_1366_;
}
else
{
uint8_t v___x_1376_; 
v___x_1376_ = 3;
return v___x_1376_;
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
v___jp_1366_:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1368_ = lean_int_dec_eq(v_hour_1358_, v___x_1367_);
if (v___x_1368_ == 0)
{
v___y_1362_ = v___x_1367_;
goto v___jp_1361_;
}
else
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_box(0);
v___x_1370_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1359_, v_second_1360_, v___x_1369_);
if (v___x_1370_ == 0)
{
v___y_1362_ = v___x_1367_;
goto v___jp_1361_;
}
else
{
uint8_t v___x_1371_; 
v___x_1371_ = 2;
return v___x_1371_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_classifyDayPeriod_0interp(lean_interpreter_value* stack)
{
lean_object* v_hour_1358_ = stack[0].m_obj;
lean_object* v_minute_1359_ = stack[1].m_obj;
lean_object* v_second_1360_ = stack[2].m_obj;
uint8_t v_res_1377_;
v_res_1377_ = l_Std_Time_classifyDayPeriod(v_hour_1358_, v_minute_1359_, v_second_1360_);
stack->m_num = v_res_1377_;
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___boxed(lean_object* v_hour_1378_, lean_object* v_minute_1379_, lean_object* v_second_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l_Std_Time_classifyDayPeriod(v_hour_1378_, v_minute_1379_, v_second_1380_);
lean_dec(v_second_1380_);
lean_dec(v_minute_1379_);
lean_dec(v_hour_1378_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_unsigned_to_nat(6u);
v___x_1384_ = lean_nat_to_int(v___x_1383_);
return v___x_1384_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__1(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_unsigned_to_nat(18u);
v___x_1386_ = lean_nat_to_int(v___x_1385_);
return v___x_1386_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__2(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_unsigned_to_nat(21u);
v___x_1388_ = lean_nat_to_int(v___x_1387_);
return v___x_1388_;
}
}
uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object* v_hour_1389_, lean_object* v_minute_1390_, lean_object* v_second_1391_){
_start:
{
lean_object* v___y_1393_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1413_ = lean_int_dec_eq(v_hour_1389_, v___x_1412_);
if (v___x_1413_ == 0)
{
goto v___jp_1406_;
}
else
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1390_, v_second_1391_, v___x_1414_);
if (v___x_1415_ == 0)
{
goto v___jp_1406_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = 0;
return v___x_1416_;
}
}
v___jp_1392_:
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_1395_ = lean_int_dec_lt(v_hour_1389_, v___x_1394_);
if (v___x_1395_ == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = lean_int_dec_lt(v_hour_1389_, v___y_1393_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__1, &l_Std_Time_classifyExtendedDayPeriod___closed__1_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__1);
v___x_1398_ = lean_int_dec_lt(v_hour_1389_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__2, &l_Std_Time_classifyExtendedDayPeriod___closed__2_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__2);
v___x_1400_ = lean_int_dec_lt(v_hour_1389_, v___x_1399_);
if (v___x_1400_ == 0)
{
uint8_t v___x_1401_; 
v___x_1401_ = 1;
return v___x_1401_;
}
else
{
uint8_t v___x_1402_; 
v___x_1402_ = 5;
return v___x_1402_;
}
}
else
{
uint8_t v___x_1403_; 
v___x_1403_ = 4;
return v___x_1403_;
}
}
else
{
uint8_t v___x_1404_; 
v___x_1404_ = 2;
return v___x_1404_;
}
}
else
{
uint8_t v___x_1405_; 
v___x_1405_ = 1;
return v___x_1405_;
}
}
v___jp_1406_:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1407_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1408_ = lean_int_dec_eq(v_hour_1389_, v___x_1407_);
if (v___x_1408_ == 0)
{
v___y_1393_ = v___x_1407_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_box(0);
v___x_1410_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1390_, v_second_1391_, v___x_1409_);
if (v___x_1410_ == 0)
{
v___y_1393_ = v___x_1407_;
goto v___jp_1392_;
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
LEAN_EXPORT void l_Std_Time_classifyExtendedDayPeriod_0interp(lean_interpreter_value* stack)
{
lean_object* v_hour_1389_ = stack[0].m_obj;
lean_object* v_minute_1390_ = stack[1].m_obj;
lean_object* v_second_1391_ = stack[2].m_obj;
uint8_t v_res_1417_;
v_res_1417_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1389_, v_minute_1390_, v_second_1391_);
stack->m_num = v_res_1417_;
}
LEAN_EXPORT lean_object* l_Std_Time_classifyExtendedDayPeriod___boxed(lean_object* v_hour_1418_, lean_object* v_minute_1419_, lean_object* v_second_1420_){
_start:
{
uint8_t v_res_1421_; lean_object* v_r_1422_; 
v_res_1421_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1418_, v_minute_1419_, v_second_1420_);
lean_dec(v_second_1420_);
lean_dec(v_minute_1419_);
lean_dec(v_hour_1418_);
v_r_1422_ = lean_box(v_res_1421_);
return v_r_1422_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_unsigned_to_nat(100u);
v___x_1424_ = lean_nat_to_int(v___x_1423_);
return v___x_1424_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_unsigned_to_nat(7u);
v___x_1426_ = lean_nat_to_int(v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object* v_dateformat_1430_, lean_object* v_modifier_1431_, lean_object* v_data_1432_){
_start:
{
switch(lean_obj_tag(v_modifier_1431_))
{
case 0:
{
uint8_t v_presentation_1433_; 
v_presentation_1433_ = lean_ctor_get_uint8(v_modifier_1431_, 0);
lean_dec_ref_known(v_modifier_1431_, 0);
switch(v_presentation_1433_)
{
case 1:
{
lean_object* v_symbols_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; 
v_symbols_1434_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1435_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1436_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1434_, v___x_1435_);
return v___x_1436_;
}
case 2:
{
lean_object* v_symbols_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; 
v_symbols_1437_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1438_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1439_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1437_, v___x_1438_);
return v___x_1439_;
}
default: 
{
lean_object* v_symbols_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; 
v_symbols_1440_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1441_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1442_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1440_, v___x_1441_);
return v___x_1442_;
}
}
}
case 1:
{
lean_object* v_presentation_1443_; 
v_presentation_1443_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1443_);
lean_dec_ref_known(v_modifier_1431_, 1);
switch(lean_obj_tag(v_presentation_1443_))
{
case 0:
{
lean_object* v___x_1444_; uint8_t v___x_1445_; lean_object* v___x_1446_; 
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = 0;
v___x_1446_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1444_, v_data_1432_, v___x_1445_);
return v___x_1446_;
}
case 1:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; 
v___x_1447_ = lean_unsigned_to_nat(2u);
v___x_1448_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1449_ = lean_int_emod(v_data_1432_, v___x_1448_);
lean_dec(v_data_1432_);
v___x_1450_ = 0;
v___x_1451_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1447_, v___x_1449_, v___x_1450_);
return v___x_1451_;
}
case 2:
{
lean_object* v___x_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = lean_unsigned_to_nat(4u);
v___x_1453_ = 0;
v___x_1454_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1452_, v_data_1432_, v___x_1453_);
return v___x_1454_;
}
default: 
{
lean_object* v_num_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; 
v_num_1455_ = lean_ctor_get(v_presentation_1443_, 0);
lean_inc(v_num_1455_);
lean_dec_ref_known(v_presentation_1443_, 1);
v___x_1456_ = 0;
v___x_1457_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1455_, v_data_1432_, v___x_1456_);
lean_dec(v_num_1455_);
return v___x_1457_;
}
}
}
case 2:
{
lean_object* v_presentation_1458_; lean_object* v___x_1459_; lean_object* v___y_1461_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v_presentation_1458_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1458_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1476_ = lean_int_dec_le(v_data_1432_, v___x_1475_);
if (v___x_1476_ == 0)
{
v___y_1461_ = v_data_1432_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = lean_int_neg(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1478_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1479_ = lean_int_add(v___x_1477_, v___x_1478_);
lean_dec(v___x_1477_);
v___y_1461_ = v___x_1479_;
goto v___jp_1460_;
}
v___jp_1460_:
{
switch(lean_obj_tag(v_presentation_1458_))
{
case 0:
{
uint8_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = 0;
v___x_1463_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1459_, v___y_1461_, v___x_1462_);
return v___x_1463_;
}
case 1:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; 
v___x_1464_ = lean_unsigned_to_nat(2u);
v___x_1465_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1466_ = lean_int_emod(v___y_1461_, v___x_1465_);
lean_dec(v___y_1461_);
v___x_1467_ = 0;
v___x_1468_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1464_, v___x_1466_, v___x_1467_);
return v___x_1468_;
}
case 2:
{
lean_object* v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_unsigned_to_nat(4u);
v___x_1470_ = 0;
v___x_1471_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1469_, v___y_1461_, v___x_1470_);
return v___x_1471_;
}
default: 
{
lean_object* v_num_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; 
v_num_1472_ = lean_ctor_get(v_presentation_1458_, 0);
lean_inc(v_num_1472_);
lean_dec_ref_known(v_presentation_1458_, 1);
v___x_1473_ = 0;
v___x_1474_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1472_, v___y_1461_, v___x_1473_);
lean_dec(v_num_1472_);
return v___x_1474_;
}
}
}
}
case 3:
{
lean_object* v_presentation_1480_; lean_object* v_snd_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; 
v_presentation_1480_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1480_);
lean_dec_ref_known(v_modifier_1431_, 1);
v_snd_1481_ = lean_ctor_get(v_data_1432_, 1);
lean_inc(v_snd_1481_);
lean_dec(v_data_1432_);
v___x_1482_ = 0;
v___x_1483_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1480_, v_snd_1481_, v___x_1482_);
lean_dec(v_presentation_1480_);
return v___x_1483_;
}
case 4:
{
lean_object* v_presentation_1484_; 
v_presentation_1484_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc_ref(v_presentation_1484_);
lean_dec_ref_known(v_modifier_1431_, 1);
if (lean_obj_tag(v_presentation_1484_) == 0)
{
lean_object* v_val_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; 
v_val_1485_ = lean_ctor_get(v_presentation_1484_, 0);
lean_inc(v_val_1485_);
lean_dec_ref_known(v_presentation_1484_, 1);
v___x_1486_ = 0;
v___x_1487_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1485_, v_data_1432_, v___x_1486_);
lean_dec(v_val_1485_);
return v___x_1487_;
}
else
{
lean_object* v_val_1488_; uint8_t v___x_1489_; 
v_val_1488_ = lean_ctor_get(v_presentation_1484_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v_presentation_1484_, 1);
v___x_1489_ = lean_unbox(v_val_1488_);
lean_dec(v_val_1488_);
switch(v___x_1489_)
{
case 1:
{
lean_object* v_symbols_1490_; lean_object* v___x_1491_; 
v_symbols_1490_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1491_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1490_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1491_;
}
case 2:
{
lean_object* v_symbols_1492_; lean_object* v___x_1493_; 
v_symbols_1492_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1493_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1492_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1493_;
}
default: 
{
lean_object* v_symbols_1494_; lean_object* v___x_1495_; 
v_symbols_1494_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1495_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1494_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1495_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1496_; 
v_presentation_1496_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc_ref(v_presentation_1496_);
lean_dec_ref_known(v_modifier_1431_, 1);
if (lean_obj_tag(v_presentation_1496_) == 0)
{
lean_object* v_val_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; 
v_val_1497_ = lean_ctor_get(v_presentation_1496_, 0);
lean_inc(v_val_1497_);
lean_dec_ref_known(v_presentation_1496_, 1);
v___x_1498_ = 0;
v___x_1499_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1497_, v_data_1432_, v___x_1498_);
lean_dec(v_val_1497_);
return v___x_1499_;
}
else
{
lean_object* v_val_1500_; uint8_t v___x_1501_; 
v_val_1500_ = lean_ctor_get(v_presentation_1496_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v_presentation_1496_, 1);
v___x_1501_ = lean_unbox(v_val_1500_);
lean_dec(v_val_1500_);
switch(v___x_1501_)
{
case 1:
{
lean_object* v_symbols_1502_; lean_object* v___x_1503_; 
v_symbols_1502_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1503_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1502_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1503_;
}
case 2:
{
lean_object* v_symbols_1504_; lean_object* v___x_1505_; 
v_symbols_1504_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1505_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1504_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1505_;
}
default: 
{
lean_object* v_symbols_1506_; lean_object* v___x_1507_; 
v_symbols_1506_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1507_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1506_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1507_;
}
}
}
}
case 6:
{
lean_object* v_presentation_1508_; uint8_t v___x_1509_; lean_object* v___x_1510_; 
v_presentation_1508_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1508_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1509_ = 0;
v___x_1510_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1508_, v_data_1432_, v___x_1509_);
lean_dec(v_presentation_1508_);
return v___x_1510_;
}
case 7:
{
lean_object* v_presentation_1511_; 
v_presentation_1511_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc_ref(v_presentation_1511_);
lean_dec_ref_known(v_modifier_1431_, 1);
if (lean_obj_tag(v_presentation_1511_) == 0)
{
lean_object* v_val_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; 
v_val_1512_ = lean_ctor_get(v_presentation_1511_, 0);
lean_inc(v_val_1512_);
lean_dec_ref_known(v_presentation_1511_, 1);
v___x_1513_ = 0;
v___x_1514_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1512_, v_data_1432_, v___x_1513_);
lean_dec(v_val_1512_);
return v___x_1514_;
}
else
{
lean_object* v_val_1515_; uint8_t v___x_1516_; 
v_val_1515_ = lean_ctor_get(v_presentation_1511_, 0);
lean_inc(v_val_1515_);
lean_dec_ref_known(v_presentation_1511_, 1);
v___x_1516_ = lean_unbox(v_val_1515_);
lean_dec(v_val_1515_);
switch(v___x_1516_)
{
case 0:
{
lean_object* v_symbols_1517_; lean_object* v___x_1518_; 
v_symbols_1517_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1518_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1517_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1518_;
}
case 1:
{
lean_object* v_symbols_1519_; lean_object* v___x_1520_; 
v_symbols_1519_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1520_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1519_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1520_;
}
case 2:
{
lean_object* v_symbols_1521_; lean_object* v___x_1522_; 
v_symbols_1521_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1522_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1521_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1522_;
}
default: 
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1523_;
}
}
}
}
case 8:
{
lean_object* v_presentation_1524_; 
v_presentation_1524_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc_ref(v_presentation_1524_);
lean_dec_ref_known(v_modifier_1431_, 1);
if (lean_obj_tag(v_presentation_1524_) == 0)
{
lean_object* v_val_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; 
v_val_1525_ = lean_ctor_get(v_presentation_1524_, 0);
lean_inc(v_val_1525_);
lean_dec_ref_known(v_presentation_1524_, 1);
v___x_1526_ = 0;
v___x_1527_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1525_, v_data_1432_, v___x_1526_);
lean_dec(v_val_1525_);
return v___x_1527_;
}
else
{
lean_object* v_val_1528_; uint8_t v___x_1529_; 
v_val_1528_ = lean_ctor_get(v_presentation_1524_, 0);
lean_inc(v_val_1528_);
lean_dec_ref_known(v_presentation_1524_, 1);
v___x_1529_ = lean_unbox(v_val_1528_);
lean_dec(v_val_1528_);
switch(v___x_1529_)
{
case 0:
{
lean_object* v_symbols_1530_; lean_object* v___x_1531_; 
v_symbols_1530_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1531_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1530_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1531_;
}
case 1:
{
lean_object* v_symbols_1532_; lean_object* v___x_1533_; 
v_symbols_1532_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1533_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1532_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1533_;
}
case 2:
{
lean_object* v_symbols_1534_; lean_object* v___x_1535_; 
v_symbols_1534_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1535_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1534_, v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1535_;
}
default: 
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1432_);
lean_dec(v_data_1432_);
return v___x_1536_;
}
}
}
}
case 9:
{
lean_object* v_presentation_1537_; lean_object* v___x_1538_; lean_object* v___y_1540_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v_presentation_1537_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1537_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1555_ = lean_int_dec_le(v_data_1432_, v___x_1554_);
if (v___x_1555_ == 0)
{
v___y_1540_ = v_data_1432_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_int_neg(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1557_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1558_ = lean_int_add(v___x_1556_, v___x_1557_);
lean_dec(v___x_1556_);
v___y_1540_ = v___x_1558_;
goto v___jp_1539_;
}
v___jp_1539_:
{
switch(lean_obj_tag(v_presentation_1537_))
{
case 0:
{
uint8_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = 0;
v___x_1542_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1538_, v___y_1540_, v___x_1541_);
return v___x_1542_;
}
case 1:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1543_ = lean_unsigned_to_nat(2u);
v___x_1544_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1545_ = lean_int_emod(v___y_1540_, v___x_1544_);
lean_dec(v___y_1540_);
v___x_1546_ = 0;
v___x_1547_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1543_, v___x_1545_, v___x_1546_);
return v___x_1547_;
}
case 2:
{
lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_unsigned_to_nat(4u);
v___x_1549_ = 0;
v___x_1550_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1548_, v___y_1540_, v___x_1549_);
return v___x_1550_;
}
default: 
{
lean_object* v_num_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; 
v_num_1551_ = lean_ctor_get(v_presentation_1537_, 0);
lean_inc(v_num_1551_);
lean_dec_ref_known(v_presentation_1537_, 1);
v___x_1552_ = 0;
v___x_1553_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1551_, v___y_1540_, v___x_1552_);
lean_dec(v_num_1551_);
return v___x_1553_;
}
}
}
}
case 10:
{
lean_object* v_presentation_1559_; uint8_t v___x_1560_; lean_object* v___x_1561_; 
v_presentation_1559_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1559_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1560_ = 0;
v___x_1561_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1559_, v_data_1432_, v___x_1560_);
lean_dec(v_presentation_1559_);
return v___x_1561_;
}
case 11:
{
lean_object* v_presentation_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; 
v_presentation_1562_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1562_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1563_ = 0;
v___x_1564_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1562_, v_data_1432_, v___x_1563_);
lean_dec(v_presentation_1562_);
return v___x_1564_;
}
case 12:
{
uint8_t v_presentation_1565_; 
v_presentation_1565_ = lean_ctor_get_uint8(v_modifier_1431_, 0);
lean_dec_ref_known(v_modifier_1431_, 0);
switch(v_presentation_1565_)
{
case 0:
{
lean_object* v_symbols_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; 
v_symbols_1566_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1567_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1568_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1566_, v___x_1567_);
return v___x_1568_;
}
case 1:
{
lean_object* v_symbols_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; 
v_symbols_1569_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1570_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1571_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1569_, v___x_1570_);
return v___x_1571_;
}
case 2:
{
lean_object* v_symbols_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; 
v_symbols_1572_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1573_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1574_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1572_, v___x_1573_);
return v___x_1574_;
}
default: 
{
lean_object* v_symbols_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; 
v_symbols_1575_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1576_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1577_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1575_, v___x_1576_);
return v___x_1577_;
}
}
}
case 13:
{
lean_object* v_presentation_1578_; 
v_presentation_1578_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc_ref(v_presentation_1578_);
lean_dec_ref_known(v_modifier_1431_, 1);
if (lean_obj_tag(v_presentation_1578_) == 0)
{
lean_object* v_val_1579_; uint8_t v_firstDayOfWeek_1580_; lean_object* v_firstOrd_1581_; uint8_t v___x_1582_; lean_object* v_dayOrd_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; 
v_val_1579_ = lean_ctor_get(v_presentation_1578_, 0);
lean_inc(v_val_1579_);
lean_dec_ref_known(v_presentation_1578_, 1);
v_firstDayOfWeek_1580_ = lean_ctor_get_uint8(v_dateformat_1430_, sizeof(void*)*2);
v_firstOrd_1581_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1580_);
v___x_1582_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v_dayOrd_1583_ = l_Std_Time_Weekday_toOrdinal(v___x_1582_);
v___x_1584_ = lean_int_sub(v_dayOrd_1583_, v_firstOrd_1581_);
lean_dec(v_firstOrd_1581_);
lean_dec(v_dayOrd_1583_);
v___x_1585_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1586_ = lean_int_add(v___x_1584_, v___x_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_int_emod(v___x_1586_, v___x_1585_);
lean_dec(v___x_1586_);
v___x_1588_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1589_ = lean_int_add(v___x_1587_, v___x_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = 0;
v___x_1591_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1579_, v___x_1589_, v___x_1590_);
lean_dec(v_val_1579_);
return v___x_1591_;
}
else
{
lean_object* v_val_1592_; uint8_t v___x_1593_; 
v_val_1592_ = lean_ctor_get(v_presentation_1578_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v_presentation_1578_, 1);
v___x_1593_ = lean_unbox(v_val_1592_);
lean_dec(v_val_1592_);
switch(v___x_1593_)
{
case 0:
{
lean_object* v_symbols_1594_; uint8_t v___x_1595_; lean_object* v___x_1596_; 
v_symbols_1594_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1595_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1596_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1594_, v___x_1595_);
return v___x_1596_;
}
case 1:
{
lean_object* v_symbols_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; 
v_symbols_1597_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1598_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1599_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1597_, v___x_1598_);
return v___x_1599_;
}
case 2:
{
lean_object* v_symbols_1600_; uint8_t v___x_1601_; lean_object* v___x_1602_; 
v_symbols_1600_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1601_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1602_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1600_, v___x_1601_);
return v___x_1602_;
}
default: 
{
lean_object* v_symbols_1603_; uint8_t v___x_1604_; lean_object* v___x_1605_; 
v_symbols_1603_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1604_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1605_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1603_, v___x_1604_);
return v___x_1605_;
}
}
}
}
case 14:
{
lean_object* v_presentation_1606_; 
v_presentation_1606_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc_ref(v_presentation_1606_);
lean_dec_ref_known(v_modifier_1431_, 1);
if (lean_obj_tag(v_presentation_1606_) == 0)
{
lean_object* v_val_1607_; uint8_t v_firstDayOfWeek_1608_; lean_object* v_firstOrd_1609_; uint8_t v___x_1610_; lean_object* v_dayOrd_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; 
v_val_1607_ = lean_ctor_get(v_presentation_1606_, 0);
lean_inc(v_val_1607_);
lean_dec_ref_known(v_presentation_1606_, 1);
v_firstDayOfWeek_1608_ = lean_ctor_get_uint8(v_dateformat_1430_, sizeof(void*)*2);
v_firstOrd_1609_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1608_);
v___x_1610_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v_dayOrd_1611_ = l_Std_Time_Weekday_toOrdinal(v___x_1610_);
v___x_1612_ = lean_int_sub(v_dayOrd_1611_, v_firstOrd_1609_);
lean_dec(v_firstOrd_1609_);
lean_dec(v_dayOrd_1611_);
v___x_1613_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1614_ = lean_int_add(v___x_1612_, v___x_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_int_emod(v___x_1614_, v___x_1613_);
lean_dec(v___x_1614_);
v___x_1616_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1617_ = lean_int_add(v___x_1615_, v___x_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = 0;
v___x_1619_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1607_, v___x_1617_, v___x_1618_);
lean_dec(v_val_1607_);
return v___x_1619_;
}
else
{
lean_object* v_val_1620_; uint8_t v___x_1621_; 
v_val_1620_ = lean_ctor_get(v_presentation_1606_, 0);
lean_inc(v_val_1620_);
lean_dec_ref_known(v_presentation_1606_, 1);
v___x_1621_ = lean_unbox(v_val_1620_);
lean_dec(v_val_1620_);
switch(v___x_1621_)
{
case 0:
{
lean_object* v_symbols_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; 
v_symbols_1622_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1623_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1624_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1622_, v___x_1623_);
return v___x_1624_;
}
case 1:
{
lean_object* v_symbols_1625_; uint8_t v___x_1626_; lean_object* v___x_1627_; 
v_symbols_1625_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1626_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1627_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1625_, v___x_1626_);
return v___x_1627_;
}
case 2:
{
lean_object* v_symbols_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; 
v_symbols_1628_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1629_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1630_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1628_, v___x_1629_);
return v___x_1630_;
}
default: 
{
lean_object* v_symbols_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; 
v_symbols_1631_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1632_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1633_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1631_, v___x_1632_);
return v___x_1633_;
}
}
}
}
case 15:
{
lean_object* v_presentation_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; 
v_presentation_1634_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1634_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1635_ = 0;
v___x_1636_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1634_, v_data_1432_, v___x_1635_);
lean_dec(v_presentation_1634_);
return v___x_1636_;
}
case 16:
{
uint8_t v_presentation_1637_; 
v_presentation_1637_ = lean_ctor_get_uint8(v_modifier_1431_, 0);
lean_dec_ref_known(v_modifier_1431_, 0);
if (v_presentation_1637_ == 2)
{
lean_object* v_symbols_1638_; uint8_t v___x_1639_; lean_object* v___x_1640_; 
v_symbols_1638_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1639_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1640_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1638_, v___x_1639_);
return v___x_1640_;
}
else
{
lean_object* v_symbols_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; 
v_symbols_1641_ = lean_ctor_get(v_dateformat_1430_, 1);
v___x_1642_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1643_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1641_, v___x_1642_);
return v___x_1643_;
}
}
case 17:
{
uint8_t v_presentation_1644_; 
v_presentation_1644_ = lean_ctor_get_uint8(v_modifier_1431_, 0);
lean_dec_ref_known(v_modifier_1431_, 0);
switch(v_presentation_1644_)
{
case 1:
{
lean_object* v_symbols_1645_; lean_object* v_dayPeriodLong_1646_; uint8_t v___x_1647_; lean_object* v___x_1648_; 
v_symbols_1645_ = lean_ctor_get(v_dateformat_1430_, 1);
v_dayPeriodLong_1646_ = lean_ctor_get(v_symbols_1645_, 20);
v___x_1647_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1648_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodLong_1646_, v___x_1647_);
return v___x_1648_;
}
case 2:
{
lean_object* v_symbols_1649_; lean_object* v_dayPeriodNarrow_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; 
v_symbols_1649_ = lean_ctor_get(v_dateformat_1430_, 1);
v_dayPeriodNarrow_1650_ = lean_ctor_get(v_symbols_1649_, 21);
v___x_1651_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1652_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodNarrow_1650_, v___x_1651_);
return v___x_1652_;
}
default: 
{
lean_object* v_symbols_1653_; lean_object* v_dayPeriodShort_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; 
v_symbols_1653_ = lean_ctor_get(v_dateformat_1430_, 1);
v_dayPeriodShort_1654_ = lean_ctor_get(v_symbols_1653_, 19);
v___x_1655_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1656_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodShort_1654_, v___x_1655_);
return v___x_1656_;
}
}
}
case 18:
{
uint8_t v_presentation_1657_; 
v_presentation_1657_ = lean_ctor_get_uint8(v_modifier_1431_, 0);
lean_dec_ref_known(v_modifier_1431_, 0);
switch(v_presentation_1657_)
{
case 1:
{
lean_object* v_symbols_1658_; lean_object* v_extendedDayPeriodLong_1659_; uint8_t v___x_1660_; lean_object* v___x_1661_; 
v_symbols_1658_ = lean_ctor_get(v_dateformat_1430_, 1);
v_extendedDayPeriodLong_1659_ = lean_ctor_get(v_symbols_1658_, 23);
v___x_1660_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1661_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodLong_1659_, v___x_1660_);
return v___x_1661_;
}
case 2:
{
lean_object* v_symbols_1662_; lean_object* v_extendedDayPeriodNarrow_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; 
v_symbols_1662_ = lean_ctor_get(v_dateformat_1430_, 1);
v_extendedDayPeriodNarrow_1663_ = lean_ctor_get(v_symbols_1662_, 24);
v___x_1664_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1665_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodNarrow_1663_, v___x_1664_);
return v___x_1665_;
}
default: 
{
lean_object* v_symbols_1666_; lean_object* v_extendedDayPeriodShort_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; 
v_symbols_1666_ = lean_ctor_get(v_dateformat_1430_, 1);
v_extendedDayPeriodShort_1667_ = lean_ctor_get(v_symbols_1666_, 22);
v___x_1668_ = lean_unbox(v_data_1432_);
lean_dec(v_data_1432_);
v___x_1669_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodShort_1667_, v___x_1668_);
return v___x_1669_;
}
}
}
case 19:
{
lean_object* v_presentation_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; 
v_presentation_1670_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1670_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1671_ = 0;
v___x_1672_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1670_, v_data_1432_, v___x_1671_);
lean_dec(v_presentation_1670_);
return v___x_1672_;
}
case 20:
{
lean_object* v_presentation_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; 
v_presentation_1673_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1673_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1674_ = 0;
v___x_1675_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1673_, v_data_1432_, v___x_1674_);
lean_dec(v_presentation_1673_);
return v___x_1675_;
}
case 21:
{
lean_object* v_presentation_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; 
v_presentation_1676_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1676_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1677_ = 0;
v___x_1678_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1676_, v_data_1432_, v___x_1677_);
lean_dec(v_presentation_1676_);
return v___x_1678_;
}
case 22:
{
lean_object* v_presentation_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; 
v_presentation_1679_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1679_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1680_ = 0;
v___x_1681_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1679_, v_data_1432_, v___x_1680_);
lean_dec(v_presentation_1679_);
return v___x_1681_;
}
case 23:
{
lean_object* v_presentation_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; 
v_presentation_1682_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1682_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1683_ = 0;
v___x_1684_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1682_, v_data_1432_, v___x_1683_);
lean_dec(v_presentation_1682_);
return v___x_1684_;
}
case 24:
{
lean_object* v_presentation_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; 
v_presentation_1685_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1685_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1686_ = 0;
v___x_1687_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1685_, v_data_1432_, v___x_1686_);
lean_dec(v_presentation_1685_);
return v___x_1687_;
}
case 25:
{
lean_object* v_presentation_1688_; 
v_presentation_1688_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1688_);
lean_dec_ref_known(v_modifier_1431_, 1);
if (lean_obj_tag(v_presentation_1688_) == 0)
{
lean_object* v___x_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_unsigned_to_nat(9u);
v___x_1690_ = 0;
v___x_1691_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1689_, v_data_1432_, v___x_1690_);
return v___x_1691_;
}
else
{
lean_object* v_digits_1692_; lean_object* v___x_1693_; uint32_t v___x_1694_; lean_object* v___x_1695_; lean_object* v_s_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_digits_1692_ = lean_ctor_get(v_presentation_1688_, 0);
lean_inc(v_digits_1692_);
lean_dec_ref_known(v_presentation_1688_, 1);
v___x_1693_ = lean_unsigned_to_nat(9u);
v___x_1694_ = 48;
v___x_1695_ = l_Int_repr(v_data_1432_);
lean_dec(v_data_1432_);
v_s_1696_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1693_, v___x_1694_, v___x_1695_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = lean_string_utf8_byte_size(v_s_1696_);
lean_inc_ref(v_s_1696_);
v___x_1699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1699_, 0, v_s_1696_);
lean_ctor_set(v___x_1699_, 1, v___x_1697_);
lean_ctor_set(v___x_1699_, 2, v___x_1698_);
v___x_1700_ = l_String_Slice_Pos_nextn(v___x_1699_, v___x_1697_, v_digits_1692_);
lean_dec_ref_known(v___x_1699_, 3);
v___x_1701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1701_, 0, v_s_1696_);
lean_ctor_set(v___x_1701_, 1, v___x_1697_);
lean_ctor_set(v___x_1701_, 2, v___x_1700_);
v___x_1702_ = l_String_Slice_toString(v___x_1701_);
lean_dec_ref_known(v___x_1701_, 3);
return v___x_1702_;
}
}
case 26:
{
lean_object* v_presentation_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; 
v_presentation_1703_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1703_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1704_ = 0;
v___x_1705_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1703_, v_data_1432_, v___x_1704_);
lean_dec(v_presentation_1703_);
return v___x_1705_;
}
case 27:
{
lean_object* v_presentation_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; 
v_presentation_1706_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1706_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1707_ = 0;
v___x_1708_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1706_, v_data_1432_, v___x_1707_);
lean_dec(v_presentation_1706_);
return v___x_1708_;
}
case 28:
{
lean_object* v_presentation_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; 
v_presentation_1709_ = lean_ctor_get(v_modifier_1431_, 0);
lean_inc(v_presentation_1709_);
lean_dec_ref_known(v_modifier_1431_, 1);
v___x_1710_ = 0;
v___x_1711_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1709_, v_data_1432_, v___x_1710_);
lean_dec(v_presentation_1709_);
return v___x_1711_;
}
case 29:
{
uint8_t v_presentation_1712_; 
v_presentation_1712_ = lean_ctor_get_uint8(v_modifier_1431_, 0);
lean_dec_ref_known(v_modifier_1431_, 0);
if (v_presentation_1712_ == 0)
{
lean_object* v___x_1713_; 
lean_dec(v_data_1432_);
v___x_1713_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1713_;
}
else
{
return v_data_1432_;
}
}
case 32:
{
uint8_t v_presentation_1714_; 
v_presentation_1714_ = lean_ctor_get_uint8(v_modifier_1431_, 0);
lean_dec_ref_known(v_modifier_1431_, 0);
if (v_presentation_1714_ == 0)
{
lean_object* v_fst_1716_; lean_object* v_snd_1717_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1741_ = lean_int_dec_eq(v_data_1432_, v___x_1740_);
if (v___x_1741_ == 0)
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_int_dec_le(v___x_1740_, v_data_1432_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1744_ = lean_int_neg(v_data_1432_);
lean_dec(v_data_1432_);
v_fst_1716_ = v___x_1743_;
v_snd_1717_ = v___x_1744_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1745_; 
v___x_1745_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1716_ = v___x_1745_;
v_snd_1717_ = v_data_1432_;
goto v___jp_1715_;
}
}
else
{
lean_object* v___x_1746_; 
lean_dec(v_data_1432_);
v___x_1746_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1746_;
}
v___jp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v_t_1720_; lean_object* v_hour_1721_; lean_object* v_minute_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1718_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1719_ = lean_int_mul(v_snd_1717_, v___x_1718_);
lean_dec(v_snd_1717_);
v_t_1720_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1719_);
lean_dec(v___x_1719_);
v_hour_1721_ = lean_ctor_get(v_t_1720_, 0);
lean_inc(v_hour_1721_);
v_minute_1722_ = lean_ctor_get(v_t_1720_, 1);
lean_inc(v_minute_1722_);
lean_dec_ref(v_t_1720_);
v___x_1723_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1724_ = lean_int_dec_eq(v_minute_1722_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; uint32_t v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1725_ = lean_unsigned_to_nat(2u);
v___x_1726_ = 48;
v___x_1727_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1728_ = lean_string_append(v___x_1727_, v_fst_1716_);
v___x_1729_ = l_Int_repr(v_hour_1721_);
lean_dec(v_hour_1721_);
v___x_1730_ = lean_string_append(v___x_1728_, v___x_1729_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___x_1732_ = lean_string_append(v___x_1730_, v___x_1731_);
v___x_1733_ = l_Int_repr(v_minute_1722_);
lean_dec(v_minute_1722_);
v___x_1734_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1725_, v___x_1726_, v___x_1733_);
lean_dec_ref(v___x_1733_);
v___x_1735_ = lean_string_append(v___x_1732_, v___x_1734_);
lean_dec_ref(v___x_1734_);
return v___x_1735_;
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v_minute_1722_);
v___x_1736_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1737_ = lean_string_append(v___x_1736_, v_fst_1716_);
v___x_1738_ = l_Int_repr(v_hour_1721_);
lean_dec(v_hour_1721_);
v___x_1739_ = lean_string_append(v___x_1737_, v___x_1738_);
lean_dec_ref(v___x_1738_);
return v___x_1739_;
}
}
}
else
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1748_ = lean_int_dec_eq(v_data_1432_, v___x_1747_);
if (v___x_1748_ == 0)
{
uint8_t v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1749_ = 1;
v___x_1750_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1751_ = 0;
v___x_1752_ = 1;
v___x_1753_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1751_, v___x_1752_, v___x_1749_, v___x_1749_);
v___x_1754_ = lean_string_append(v___x_1750_, v___x_1753_);
lean_dec_ref(v___x_1753_);
return v___x_1754_;
}
else
{
lean_object* v___x_1755_; 
lean_dec(v_data_1432_);
v___x_1755_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1755_;
}
}
}
case 33:
{
uint8_t v_presentation_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_presentation_1756_ = lean_ctor_get_uint8(v_modifier_1431_, 0);
lean_dec_ref_known(v_modifier_1431_, 0);
v___x_1757_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1758_ = lean_int_dec_eq(v_data_1432_, v___x_1757_);
if (v___x_1758_ == 0)
{
uint8_t v___x_1759_; 
v___x_1759_ = 1;
switch(v_presentation_1756_)
{
case 0:
{
uint8_t v___x_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = 2;
v___x_1761_ = 1;
v___x_1762_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1760_, v___x_1761_, v___x_1758_, v___x_1759_);
return v___x_1762_;
}
case 1:
{
uint8_t v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = 0;
v___x_1764_ = 1;
v___x_1765_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1763_, v___x_1764_, v___x_1758_, v___x_1759_);
return v___x_1765_;
}
case 2:
{
uint8_t v___x_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = 0;
v___x_1767_ = 1;
v___x_1768_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1766_, v___x_1767_, v___x_1759_, v___x_1759_);
return v___x_1768_;
}
case 3:
{
uint8_t v___x_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = 0;
v___x_1770_ = 2;
v___x_1771_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1769_, v___x_1770_, v___x_1758_, v___x_1759_);
return v___x_1771_;
}
default: 
{
uint8_t v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = 0;
v___x_1773_ = 2;
v___x_1774_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1772_, v___x_1773_, v___x_1759_, v___x_1759_);
return v___x_1774_;
}
}
}
else
{
lean_object* v___x_1775_; 
lean_dec(v_data_1432_);
v___x_1775_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1775_;
}
}
case 34:
{
uint8_t v_presentation_1776_; 
v_presentation_1776_ = lean_ctor_get_uint8(v_modifier_1431_, 0);
lean_dec_ref_known(v_modifier_1431_, 0);
switch(v_presentation_1776_)
{
case 0:
{
uint8_t v___x_1777_; uint8_t v___x_1778_; uint8_t v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; 
v___x_1777_ = 2;
v___x_1778_ = 1;
v___x_1779_ = 0;
v___x_1780_ = 1;
v___x_1781_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1777_, v___x_1778_, v___x_1779_, v___x_1780_);
return v___x_1781_;
}
case 1:
{
uint8_t v___x_1782_; uint8_t v___x_1783_; uint8_t v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; 
v___x_1782_ = 0;
v___x_1783_ = 1;
v___x_1784_ = 0;
v___x_1785_ = 1;
v___x_1786_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1782_, v___x_1783_, v___x_1784_, v___x_1785_);
return v___x_1786_;
}
case 2:
{
uint8_t v___x_1787_; uint8_t v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; 
v___x_1787_ = 0;
v___x_1788_ = 1;
v___x_1789_ = 1;
v___x_1790_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1787_, v___x_1788_, v___x_1789_, v___x_1789_);
return v___x_1790_;
}
case 3:
{
uint8_t v___x_1791_; uint8_t v___x_1792_; uint8_t v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1791_ = 0;
v___x_1792_ = 2;
v___x_1793_ = 0;
v___x_1794_ = 1;
v___x_1795_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1791_, v___x_1792_, v___x_1793_, v___x_1794_);
return v___x_1795_;
}
default: 
{
uint8_t v___x_1796_; uint8_t v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; 
v___x_1796_ = 0;
v___x_1797_ = 2;
v___x_1798_ = 1;
v___x_1799_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1796_, v___x_1797_, v___x_1798_, v___x_1798_);
return v___x_1799_;
}
}
}
case 35:
{
uint8_t v_presentation_1800_; 
v_presentation_1800_ = lean_ctor_get_uint8(v_modifier_1431_, 0);
lean_dec_ref_known(v_modifier_1431_, 0);
switch(v_presentation_1800_)
{
case 0:
{
uint8_t v___x_1801_; uint8_t v___x_1802_; uint8_t v___x_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; 
v___x_1801_ = 0;
v___x_1802_ = 2;
v___x_1803_ = 0;
v___x_1804_ = 1;
v___x_1805_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1801_, v___x_1802_, v___x_1803_, v___x_1804_);
return v___x_1805_;
}
case 1:
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1807_ = lean_int_dec_eq(v_data_1432_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; uint8_t v___x_1809_; uint8_t v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1808_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1809_ = 0;
v___x_1810_ = 1;
v___x_1811_ = 1;
v___x_1812_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1809_, v___x_1810_, v___x_1811_, v___x_1811_);
v___x_1813_ = lean_string_append(v___x_1808_, v___x_1812_);
lean_dec_ref(v___x_1812_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; 
lean_dec(v_data_1432_);
v___x_1814_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1814_;
}
}
default: 
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1816_ = lean_int_dec_eq(v_data_1432_, v___x_1815_);
if (v___x_1816_ == 0)
{
uint8_t v___x_1817_; uint8_t v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; 
v___x_1817_ = 1;
v___x_1818_ = 0;
v___x_1819_ = 2;
v___x_1820_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1432_, v___x_1818_, v___x_1819_, v___x_1817_, v___x_1817_);
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; 
lean_dec(v_data_1432_);
v___x_1821_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1821_;
}
}
}
}
default: 
{
lean_dec_ref(v_modifier_1431_);
return v_data_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___boxed(lean_object* v_dateformat_1822_, lean_object* v_modifier_1823_, lean_object* v_data_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_1822_, v_modifier_1823_, v_data_1824_);
lean_dec_ref(v_dateformat_1822_);
return v_res_1825_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_unsigned_to_nat(400u);
v___x_1827_ = lean_nat_to_int(v___x_1826_);
return v___x_1827_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_unsigned_to_nat(4u);
v___x_1829_ = lean_nat_to_int(v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(lean_object* v_modifier_1830_, lean_object* v_dateformat_1831_, lean_object* v_date_1832_){
_start:
{
uint8_t v___y_1834_; lean_object* v_month_1835_; lean_object* v_day_1836_; uint8_t v___y_1837_; uint8_t v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v_month_1846_; lean_object* v_day_1847_; uint8_t v_firstDayOfWeek_1851_; lean_object* v_minimalDaysInFirstWeek_1852_; lean_object* v_date_1853_; lean_object* v_timezone_1854_; uint8_t v___y_1873_; 
v_firstDayOfWeek_1851_ = lean_ctor_get_uint8(v_dateformat_1831_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1852_ = lean_ctor_get(v_dateformat_1831_, 0);
v_date_1853_ = lean_ctor_get(v_date_1832_, 0);
v_timezone_1854_ = lean_ctor_get(v_date_1832_, 3);
switch(lean_obj_tag(v_modifier_1830_))
{
case 0:
{
lean_object* v___x_1886_; lean_object* v_date_1887_; lean_object* v_year_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1886_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc_ref(v_date_1887_);
lean_dec(v___x_1886_);
v_year_1888_ = lean_ctor_get(v_date_1887_, 0);
lean_inc(v_year_1888_);
lean_dec_ref(v_date_1887_);
v___x_1889_ = l_Std_Time_Year_Offset_era(v_year_1888_);
lean_dec(v_year_1888_);
v___x_1890_ = lean_box(v___x_1889_);
return v___x_1890_;
}
case 1:
{
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
goto v___jp_1868_;
}
case 2:
{
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
goto v___jp_1868_;
}
case 3:
{
lean_object* v___x_1891_; lean_object* v_date_1892_; lean_object* v_year_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1901_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1891_ = lean_thunk_get_own(v_date_1853_);
v_date_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc_ref(v_date_1892_);
lean_dec(v___x_1891_);
v_year_1893_ = lean_ctor_get(v_date_1892_, 0);
lean_inc(v_year_1893_);
lean_dec_ref(v_date_1892_);
v___x_1894_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1895_ = lean_int_mod(v_year_1893_, v___x_1894_);
v___x_1896_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1901_ = lean_int_dec_eq(v___x_1895_, v___x_1896_);
lean_dec(v___x_1895_);
if (v___x_1901_ == 0)
{
lean_dec(v_year_1893_);
v___y_1873_ = v___x_1901_;
goto v___jp_1872_;
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1902_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1903_ = lean_int_mod(v_year_1893_, v___x_1902_);
v___x_1904_ = lean_int_dec_eq(v___x_1903_, v___x_1896_);
lean_dec(v___x_1903_);
if (v___x_1904_ == 0)
{
if (v___x_1901_ == 0)
{
goto v___jp_1897_;
}
else
{
lean_dec(v_year_1893_);
v___y_1873_ = v___x_1901_;
goto v___jp_1872_;
}
}
else
{
goto v___jp_1897_;
}
}
v___jp_1897_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1898_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1899_ = lean_int_mod(v_year_1893_, v___x_1898_);
lean_dec(v_year_1893_);
v___x_1900_ = lean_int_dec_eq(v___x_1899_, v___x_1896_);
lean_dec(v___x_1899_);
v___y_1873_ = v___x_1900_;
goto v___jp_1872_;
}
}
case 4:
{
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
goto v___jp_1864_;
}
case 5:
{
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
goto v___jp_1864_;
}
case 6:
{
lean_object* v___x_1905_; lean_object* v_date_1906_; lean_object* v_day_1907_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1905_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc_ref(v_date_1906_);
lean_dec(v___x_1905_);
v_day_1907_ = lean_ctor_get(v_date_1906_, 2);
lean_inc(v_day_1907_);
lean_dec_ref(v_date_1906_);
return v_day_1907_;
}
case 7:
{
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
goto v___jp_1860_;
}
case 8:
{
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
goto v___jp_1860_;
}
case 9:
{
lean_object* v___x_1908_; lean_object* v_date_1909_; lean_object* v___x_1910_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1908_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc_ref(v_date_1909_);
lean_dec(v___x_1908_);
v___x_1910_ = l_Std_Time_PlainDate_weekYear(v_date_1909_, v_firstDayOfWeek_1851_, v_minimalDaysInFirstWeek_1852_);
return v___x_1910_;
}
case 10:
{
lean_object* v___x_1911_; lean_object* v_date_1912_; lean_object* v___x_1913_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1911_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc_ref(v_date_1912_);
lean_dec(v___x_1911_);
v___x_1913_ = l_Std_Time_PlainDate_weekOfYear(v_date_1912_, v_firstDayOfWeek_1851_, v_minimalDaysInFirstWeek_1852_);
return v___x_1913_;
}
case 11:
{
lean_object* v___x_1914_; lean_object* v_date_1915_; lean_object* v___x_1916_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1914_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc_ref(v_date_1915_);
lean_dec(v___x_1914_);
v___x_1916_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1915_, v_firstDayOfWeek_1851_);
return v___x_1916_;
}
case 12:
{
lean_object* v___x_1917_; lean_object* v_date_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1917_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc_ref(v_date_1918_);
lean_dec(v___x_1917_);
v___x_1919_ = l_Std_Time_PlainDate_weekday(v_date_1918_);
v___x_1920_ = lean_box(v___x_1919_);
return v___x_1920_;
}
case 13:
{
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
goto v___jp_1855_;
}
case 14:
{
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
goto v___jp_1855_;
}
case 15:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_1832_);
lean_dec_ref(v_date_1832_);
return v___x_1921_;
}
case 16:
{
lean_object* v___x_1922_; lean_object* v_time_1923_; lean_object* v_hour_1924_; uint8_t v___x_1925_; lean_object* v___x_1926_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1922_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1923_ = lean_ctor_get(v___x_1922_, 1);
lean_inc_ref(v_time_1923_);
lean_dec(v___x_1922_);
v_hour_1924_ = lean_ctor_get(v_time_1923_, 0);
lean_inc(v_hour_1924_);
lean_dec_ref(v_time_1923_);
v___x_1925_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1924_);
lean_dec(v_hour_1924_);
v___x_1926_ = lean_box(v___x_1925_);
return v___x_1926_;
}
case 17:
{
lean_object* v___x_1927_; lean_object* v_time_1928_; lean_object* v_hour_1929_; lean_object* v_minute_1930_; lean_object* v_second_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1927_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1928_ = lean_ctor_get(v___x_1927_, 1);
lean_inc_ref(v_time_1928_);
lean_dec(v___x_1927_);
v_hour_1929_ = lean_ctor_get(v_time_1928_, 0);
lean_inc(v_hour_1929_);
v_minute_1930_ = lean_ctor_get(v_time_1928_, 1);
lean_inc(v_minute_1930_);
v_second_1931_ = lean_ctor_get(v_time_1928_, 2);
lean_inc(v_second_1931_);
lean_dec_ref(v_time_1928_);
v___x_1932_ = l_Std_Time_classifyDayPeriod(v_hour_1929_, v_minute_1930_, v_second_1931_);
lean_dec(v_second_1931_);
lean_dec(v_minute_1930_);
lean_dec(v_hour_1929_);
v___x_1933_ = lean_box(v___x_1932_);
return v___x_1933_;
}
case 18:
{
lean_object* v___x_1934_; lean_object* v_time_1935_; lean_object* v_hour_1936_; lean_object* v_minute_1937_; lean_object* v_second_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1934_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1935_ = lean_ctor_get(v___x_1934_, 1);
lean_inc_ref(v_time_1935_);
lean_dec(v___x_1934_);
v_hour_1936_ = lean_ctor_get(v_time_1935_, 0);
lean_inc(v_hour_1936_);
v_minute_1937_ = lean_ctor_get(v_time_1935_, 1);
lean_inc(v_minute_1937_);
v_second_1938_ = lean_ctor_get(v_time_1935_, 2);
lean_inc(v_second_1938_);
lean_dec_ref(v_time_1935_);
v___x_1939_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1936_, v_minute_1937_, v_second_1938_);
lean_dec(v_second_1938_);
lean_dec(v_minute_1937_);
lean_dec(v_hour_1936_);
v___x_1940_ = lean_box(v___x_1939_);
return v___x_1940_;
}
case 19:
{
lean_object* v___x_1941_; lean_object* v_time_1942_; lean_object* v_hour_1943_; lean_object* v___x_1944_; lean_object* v_fst_1945_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1941_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1942_ = lean_ctor_get(v___x_1941_, 1);
lean_inc_ref(v_time_1942_);
lean_dec(v___x_1941_);
v_hour_1943_ = lean_ctor_get(v_time_1942_, 0);
lean_inc(v_hour_1943_);
lean_dec_ref(v_time_1942_);
v___x_1944_ = l_Std_Time_HourMarker_toRelative(v_hour_1943_);
v_fst_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_fst_1945_);
lean_dec_ref(v___x_1944_);
return v_fst_1945_;
}
case 20:
{
lean_object* v___x_1946_; lean_object* v_time_1947_; lean_object* v_hour_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1946_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1947_ = lean_ctor_get(v___x_1946_, 1);
lean_inc_ref(v_time_1947_);
lean_dec(v___x_1946_);
v_hour_1948_ = lean_ctor_get(v_time_1947_, 0);
lean_inc(v_hour_1948_);
lean_dec_ref(v_time_1947_);
v___x_1949_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1950_ = lean_int_emod(v_hour_1948_, v___x_1949_);
lean_dec(v_hour_1948_);
return v___x_1950_;
}
case 21:
{
lean_object* v___x_1951_; lean_object* v_time_1952_; lean_object* v_hour_1953_; lean_object* v___x_1954_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1951_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1952_ = lean_ctor_get(v___x_1951_, 1);
lean_inc_ref(v_time_1952_);
lean_dec(v___x_1951_);
v_hour_1953_ = lean_ctor_get(v_time_1952_, 0);
lean_inc(v_hour_1953_);
lean_dec_ref(v_time_1952_);
v___x_1954_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1953_);
lean_dec(v_hour_1953_);
return v___x_1954_;
}
case 22:
{
lean_object* v___x_1955_; lean_object* v_time_1956_; lean_object* v_hour_1957_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1955_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1956_ = lean_ctor_get(v___x_1955_, 1);
lean_inc_ref(v_time_1956_);
lean_dec(v___x_1955_);
v_hour_1957_ = lean_ctor_get(v_time_1956_, 0);
lean_inc(v_hour_1957_);
lean_dec_ref(v_time_1956_);
return v_hour_1957_;
}
case 23:
{
lean_object* v___x_1958_; lean_object* v_time_1959_; lean_object* v_minute_1960_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1958_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1959_ = lean_ctor_get(v___x_1958_, 1);
lean_inc_ref(v_time_1959_);
lean_dec(v___x_1958_);
v_minute_1960_ = lean_ctor_get(v_time_1959_, 1);
lean_inc(v_minute_1960_);
lean_dec_ref(v_time_1959_);
return v_minute_1960_;
}
case 24:
{
lean_object* v___x_1961_; lean_object* v_time_1962_; lean_object* v_second_1963_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1961_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1962_ = lean_ctor_get(v___x_1961_, 1);
lean_inc_ref(v_time_1962_);
lean_dec(v___x_1961_);
v_second_1963_ = lean_ctor_get(v_time_1962_, 2);
lean_inc(v_second_1963_);
lean_dec_ref(v_time_1962_);
return v_second_1963_;
}
case 25:
{
lean_object* v___x_1964_; lean_object* v_time_1965_; lean_object* v_nanosecond_1966_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1964_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1965_ = lean_ctor_get(v___x_1964_, 1);
lean_inc_ref(v_time_1965_);
lean_dec(v___x_1964_);
v_nanosecond_1966_ = lean_ctor_get(v_time_1965_, 3);
lean_inc(v_nanosecond_1966_);
lean_dec_ref(v_time_1965_);
return v_nanosecond_1966_;
}
case 26:
{
lean_object* v___x_1967_; lean_object* v_time_1968_; lean_object* v___x_1969_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1967_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1968_ = lean_ctor_get(v___x_1967_, 1);
lean_inc_ref(v_time_1968_);
lean_dec(v___x_1967_);
v___x_1969_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1968_);
lean_dec_ref(v_time_1968_);
return v___x_1969_;
}
case 27:
{
lean_object* v___x_1970_; lean_object* v_time_1971_; lean_object* v_nanosecond_1972_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1970_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1971_ = lean_ctor_get(v___x_1970_, 1);
lean_inc_ref(v_time_1971_);
lean_dec(v___x_1970_);
v_nanosecond_1972_ = lean_ctor_get(v_time_1971_, 3);
lean_inc(v_nanosecond_1972_);
lean_dec_ref(v_time_1971_);
return v_nanosecond_1972_;
}
case 28:
{
lean_object* v___x_1973_; lean_object* v_time_1974_; lean_object* v___x_1975_; 
lean_inc_ref(v_date_1853_);
lean_dec_ref(v_date_1832_);
v___x_1973_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_time_1974_ = lean_ctor_get(v___x_1973_, 1);
lean_inc_ref(v_time_1974_);
lean_dec(v___x_1973_);
v___x_1975_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1974_);
lean_dec_ref(v_time_1974_);
return v___x_1975_;
}
case 29:
{
uint8_t v_presentation_1976_; 
lean_inc_ref(v_timezone_1854_);
lean_dec_ref(v_date_1832_);
v_presentation_1976_ = lean_ctor_get_uint8(v_modifier_1830_, 0);
if (v_presentation_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_dec_ref(v_timezone_1854_);
v___x_1977_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1977_;
}
else
{
lean_object* v_offset_1978_; lean_object* v_name_1979_; lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_offset_1978_ = lean_ctor_get(v_timezone_1854_, 0);
lean_inc(v_offset_1978_);
v_name_1979_ = lean_ctor_get(v_timezone_1854_, 1);
lean_inc_ref(v_name_1979_);
lean_dec_ref(v_timezone_1854_);
v___x_1994_ = lean_string_utf8_byte_size(v_name_1979_);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_nat_dec_le(v___x_1995_, v___x_1994_);
if (v___x_1996_ == 0)
{
goto v___jp_1987_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1998_ = lean_unsigned_to_nat(0u);
v___x_1999_ = lean_string_memcmp(v_name_1979_, v___x_1997_, v___x_1998_, v___x_1998_, v___x_1995_);
if (v___x_1999_ == 0)
{
goto v___jp_1987_;
}
else
{
lean_dec_ref(v_name_1979_);
goto v___jp_1980_;
}
}
v___jp_1980_:
{
uint8_t v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1981_ = 1;
v___x_1982_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1983_ = 0;
v___x_1984_ = 1;
v___x_1985_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1978_, v___x_1983_, v___x_1984_, v___x_1981_, v___x_1981_);
v___x_1986_ = lean_string_append(v___x_1982_, v___x_1985_);
lean_dec_ref(v___x_1985_);
return v___x_1986_;
}
v___jp_1987_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1988_ = lean_string_utf8_byte_size(v_name_1979_);
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = lean_nat_dec_le(v___x_1989_, v___x_1988_);
if (v___x_1990_ == 0)
{
lean_dec(v_offset_1978_);
return v_name_1979_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1991_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1992_ = lean_unsigned_to_nat(0u);
v___x_1993_ = lean_string_memcmp(v_name_1979_, v___x_1991_, v___x_1992_, v___x_1992_, v___x_1989_);
if (v___x_1993_ == 0)
{
lean_dec(v_offset_1978_);
return v_name_1979_;
}
else
{
lean_dec_ref(v_name_1979_);
goto v___jp_1980_;
}
}
}
}
}
case 30:
{
uint8_t v_presentation_2000_; 
lean_inc_ref(v_timezone_1854_);
lean_dec_ref(v_date_1832_);
v_presentation_2000_ = lean_ctor_get_uint8(v_modifier_1830_, 0);
if (v_presentation_2000_ == 0)
{
lean_object* v_offset_2001_; lean_object* v_abbreviation_2002_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_offset_2001_ = lean_ctor_get(v_timezone_1854_, 0);
lean_inc(v_offset_2001_);
v_abbreviation_2002_ = lean_ctor_get(v_timezone_1854_, 2);
lean_inc_ref(v_abbreviation_2002_);
lean_dec_ref(v_timezone_1854_);
v___x_2017_ = lean_string_utf8_byte_size(v_abbreviation_2002_);
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_dec_le(v___x_2018_, v___x_2017_);
if (v___x_2019_ == 0)
{
goto v___jp_2010_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2020_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2021_ = lean_unsigned_to_nat(0u);
v___x_2022_ = lean_string_memcmp(v_abbreviation_2002_, v___x_2020_, v___x_2021_, v___x_2021_, v___x_2018_);
if (v___x_2022_ == 0)
{
goto v___jp_2010_;
}
else
{
lean_dec_ref(v_abbreviation_2002_);
goto v___jp_2003_;
}
}
v___jp_2003_:
{
uint8_t v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2004_ = 1;
v___x_2005_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2006_ = 0;
v___x_2007_ = 1;
v___x_2008_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2001_, v___x_2006_, v___x_2007_, v___x_2004_, v___x_2004_);
v___x_2009_ = lean_string_append(v___x_2005_, v___x_2008_);
lean_dec_ref(v___x_2008_);
return v___x_2009_;
}
v___jp_2010_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2011_ = lean_string_utf8_byte_size(v_abbreviation_2002_);
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = lean_nat_dec_le(v___x_2012_, v___x_2011_);
if (v___x_2013_ == 0)
{
lean_dec(v_offset_2001_);
return v_abbreviation_2002_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2014_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2015_ = lean_unsigned_to_nat(0u);
v___x_2016_ = lean_string_memcmp(v_abbreviation_2002_, v___x_2014_, v___x_2015_, v___x_2015_, v___x_2012_);
if (v___x_2016_ == 0)
{
lean_dec(v_offset_2001_);
return v_abbreviation_2002_;
}
else
{
lean_dec_ref(v_abbreviation_2002_);
goto v___jp_2003_;
}
}
}
}
else
{
lean_object* v_offset_2023_; lean_object* v_name_2024_; lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v_offset_2023_ = lean_ctor_get(v_timezone_1854_, 0);
lean_inc(v_offset_2023_);
v_name_2024_ = lean_ctor_get(v_timezone_1854_, 1);
lean_inc_ref(v_name_2024_);
lean_dec_ref(v_timezone_1854_);
v___x_2039_ = lean_string_utf8_byte_size(v_name_2024_);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_dec_le(v___x_2040_, v___x_2039_);
if (v___x_2041_ == 0)
{
goto v___jp_2032_;
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2042_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2043_ = lean_unsigned_to_nat(0u);
v___x_2044_ = lean_string_memcmp(v_name_2024_, v___x_2042_, v___x_2043_, v___x_2043_, v___x_2040_);
if (v___x_2044_ == 0)
{
goto v___jp_2032_;
}
else
{
lean_dec_ref(v_name_2024_);
goto v___jp_2025_;
}
}
v___jp_2025_:
{
uint8_t v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; uint8_t v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2026_ = 1;
v___x_2027_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2028_ = 0;
v___x_2029_ = 1;
v___x_2030_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2023_, v___x_2028_, v___x_2029_, v___x_2026_, v___x_2026_);
v___x_2031_ = lean_string_append(v___x_2027_, v___x_2030_);
lean_dec_ref(v___x_2030_);
return v___x_2031_;
}
v___jp_2032_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = lean_string_utf8_byte_size(v_name_2024_);
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_dec_le(v___x_2034_, v___x_2033_);
if (v___x_2035_ == 0)
{
lean_dec(v_offset_2023_);
return v_name_2024_;
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2036_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2037_ = lean_unsigned_to_nat(0u);
v___x_2038_ = lean_string_memcmp(v_name_2024_, v___x_2036_, v___x_2037_, v___x_2037_, v___x_2034_);
if (v___x_2038_ == 0)
{
lean_dec(v_offset_2023_);
return v_name_2024_;
}
else
{
lean_dec_ref(v_name_2024_);
goto v___jp_2025_;
}
}
}
}
}
case 31:
{
uint8_t v_presentation_2045_; 
lean_inc_ref(v_timezone_1854_);
lean_dec_ref(v_date_1832_);
v_presentation_2045_ = lean_ctor_get_uint8(v_modifier_1830_, 0);
if (v_presentation_2045_ == 0)
{
lean_object* v_offset_2046_; lean_object* v_abbreviation_2047_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_offset_2046_ = lean_ctor_get(v_timezone_1854_, 0);
lean_inc(v_offset_2046_);
v_abbreviation_2047_ = lean_ctor_get(v_timezone_1854_, 2);
lean_inc_ref(v_abbreviation_2047_);
lean_dec_ref(v_timezone_1854_);
v___x_2062_ = lean_string_utf8_byte_size(v_abbreviation_2047_);
v___x_2063_ = lean_unsigned_to_nat(1u);
v___x_2064_ = lean_nat_dec_le(v___x_2063_, v___x_2062_);
if (v___x_2064_ == 0)
{
goto v___jp_2055_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2065_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2066_ = lean_unsigned_to_nat(0u);
v___x_2067_ = lean_string_memcmp(v_abbreviation_2047_, v___x_2065_, v___x_2066_, v___x_2066_, v___x_2063_);
if (v___x_2067_ == 0)
{
goto v___jp_2055_;
}
else
{
lean_dec_ref(v_abbreviation_2047_);
goto v___jp_2048_;
}
}
v___jp_2048_:
{
uint8_t v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2049_ = 1;
v___x_2050_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2051_ = 0;
v___x_2052_ = 1;
v___x_2053_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2046_, v___x_2051_, v___x_2052_, v___x_2049_, v___x_2049_);
v___x_2054_ = lean_string_append(v___x_2050_, v___x_2053_);
lean_dec_ref(v___x_2053_);
return v___x_2054_;
}
v___jp_2055_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2056_ = lean_string_utf8_byte_size(v_abbreviation_2047_);
v___x_2057_ = lean_unsigned_to_nat(1u);
v___x_2058_ = lean_nat_dec_le(v___x_2057_, v___x_2056_);
if (v___x_2058_ == 0)
{
lean_dec(v_offset_2046_);
return v_abbreviation_2047_;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2059_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = lean_string_memcmp(v_abbreviation_2047_, v___x_2059_, v___x_2060_, v___x_2060_, v___x_2057_);
if (v___x_2061_ == 0)
{
lean_dec(v_offset_2046_);
return v_abbreviation_2047_;
}
else
{
lean_dec_ref(v_abbreviation_2047_);
goto v___jp_2048_;
}
}
}
}
else
{
lean_object* v_offset_2068_; lean_object* v_name_2069_; lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v_offset_2068_ = lean_ctor_get(v_timezone_1854_, 0);
lean_inc(v_offset_2068_);
v_name_2069_ = lean_ctor_get(v_timezone_1854_, 1);
lean_inc_ref(v_name_2069_);
lean_dec_ref(v_timezone_1854_);
v___x_2084_ = lean_string_utf8_byte_size(v_name_2069_);
v___x_2085_ = lean_unsigned_to_nat(1u);
v___x_2086_ = lean_nat_dec_le(v___x_2085_, v___x_2084_);
if (v___x_2086_ == 0)
{
goto v___jp_2077_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2087_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = lean_string_memcmp(v_name_2069_, v___x_2087_, v___x_2088_, v___x_2088_, v___x_2085_);
if (v___x_2089_ == 0)
{
goto v___jp_2077_;
}
else
{
lean_dec_ref(v_name_2069_);
goto v___jp_2070_;
}
}
v___jp_2070_:
{
uint8_t v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2071_ = 1;
v___x_2072_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2073_ = 0;
v___x_2074_ = 1;
v___x_2075_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2068_, v___x_2073_, v___x_2074_, v___x_2071_, v___x_2071_);
v___x_2076_ = lean_string_append(v___x_2072_, v___x_2075_);
lean_dec_ref(v___x_2075_);
return v___x_2076_;
}
v___jp_2077_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2078_ = lean_string_utf8_byte_size(v_name_2069_);
v___x_2079_ = lean_unsigned_to_nat(1u);
v___x_2080_ = lean_nat_dec_le(v___x_2079_, v___x_2078_);
if (v___x_2080_ == 0)
{
lean_dec(v_offset_2068_);
return v_name_2069_;
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2081_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = lean_string_memcmp(v_name_2069_, v___x_2081_, v___x_2082_, v___x_2082_, v___x_2079_);
if (v___x_2083_ == 0)
{
lean_dec(v_offset_2068_);
return v_name_2069_;
}
else
{
lean_dec_ref(v_name_2069_);
goto v___jp_2070_;
}
}
}
}
}
default: 
{
lean_object* v_offset_2090_; 
lean_inc_ref(v_timezone_1854_);
lean_dec_ref(v_date_1832_);
v_offset_2090_ = lean_ctor_get(v_timezone_1854_, 0);
lean_inc(v_offset_2090_);
lean_dec_ref(v_timezone_1854_);
return v_offset_2090_;
}
}
v___jp_1833_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_month_1835_);
lean_ctor_set(v___x_1838_, 1, v_day_1836_);
v___x_1839_ = l_Std_Time_ValidDate_dayOfYear(v___y_1837_, v___x_1838_);
lean_dec_ref_known(v___x_1838_, 2);
v___x_1840_ = lean_box(v___y_1834_);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___x_1839_);
return v___x_1841_;
}
v___jp_1842_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1848_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1849_ = lean_int_mod(v___y_1845_, v___x_1848_);
lean_dec(v___y_1845_);
v___x_1850_ = lean_int_dec_eq(v___x_1849_, v___y_1844_);
lean_dec(v___x_1849_);
v___y_1834_ = v___y_1843_;
v_month_1835_ = v_month_1846_;
v_day_1836_ = v_day_1847_;
v___y_1837_ = v___x_1850_;
goto v___jp_1833_;
}
v___jp_1855_:
{
lean_object* v___x_1856_; lean_object* v_date_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1856_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc_ref(v_date_1857_);
lean_dec(v___x_1856_);
v___x_1858_ = l_Std_Time_PlainDate_weekday(v_date_1857_);
v___x_1859_ = lean_box(v___x_1858_);
return v___x_1859_;
}
v___jp_1860_:
{
lean_object* v___x_1861_; lean_object* v_date_1862_; lean_object* v___x_1863_; 
v___x_1861_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc_ref(v_date_1862_);
lean_dec(v___x_1861_);
v___x_1863_ = l_Std_Time_PlainDate_quarter(v_date_1862_);
lean_dec_ref(v_date_1862_);
return v___x_1863_;
}
v___jp_1864_:
{
lean_object* v___x_1865_; lean_object* v_date_1866_; lean_object* v_month_1867_; 
v___x_1865_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc_ref(v_date_1866_);
lean_dec(v___x_1865_);
v_month_1867_ = lean_ctor_get(v_date_1866_, 1);
lean_inc(v_month_1867_);
lean_dec_ref(v_date_1866_);
return v_month_1867_;
}
v___jp_1868_:
{
lean_object* v___x_1869_; lean_object* v_date_1870_; lean_object* v_year_1871_; 
v___x_1869_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc_ref(v_date_1870_);
lean_dec(v___x_1869_);
v_year_1871_ = lean_ctor_get(v_date_1870_, 0);
lean_inc(v_year_1871_);
lean_dec_ref(v_date_1870_);
return v_year_1871_;
}
v___jp_1872_:
{
lean_object* v___x_1874_; lean_object* v_date_1875_; lean_object* v_year_1876_; lean_object* v_month_1877_; lean_object* v_day_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___x_1874_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
v_date_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc_ref(v_date_1875_);
lean_dec(v___x_1874_);
v_year_1876_ = lean_ctor_get(v_date_1875_, 0);
lean_inc(v_year_1876_);
v_month_1877_ = lean_ctor_get(v_date_1875_, 1);
lean_inc(v_month_1877_);
v_day_1878_ = lean_ctor_get(v_date_1875_, 2);
lean_inc(v_day_1878_);
lean_dec_ref(v_date_1875_);
v___x_1879_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1880_ = lean_int_mod(v_year_1876_, v___x_1879_);
v___x_1881_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1882_ = lean_int_dec_eq(v___x_1880_, v___x_1881_);
lean_dec(v___x_1880_);
if (v___x_1882_ == 0)
{
lean_dec(v_year_1876_);
v___y_1834_ = v___y_1873_;
v_month_1835_ = v_month_1877_;
v_day_1836_ = v_day_1878_;
v___y_1837_ = v___x_1882_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v___x_1883_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1884_ = lean_int_mod(v_year_1876_, v___x_1883_);
v___x_1885_ = lean_int_dec_eq(v___x_1884_, v___x_1881_);
lean_dec(v___x_1884_);
if (v___x_1885_ == 0)
{
if (v___x_1882_ == 0)
{
v___y_1843_ = v___y_1873_;
v___y_1844_ = v___x_1881_;
v___y_1845_ = v_year_1876_;
v_month_1846_ = v_month_1877_;
v_day_1847_ = v_day_1878_;
goto v___jp_1842_;
}
else
{
lean_dec(v_year_1876_);
v___y_1834_ = v___y_1873_;
v_month_1835_ = v_month_1877_;
v_day_1836_ = v_day_1878_;
v___y_1837_ = v___x_1882_;
goto v___jp_1833_;
}
}
else
{
v___y_1843_ = v___y_1873_;
v___y_1844_ = v___x_1881_;
v___y_1845_ = v_year_1876_;
v_month_1846_ = v_month_1877_;
v_day_1847_ = v_day_1878_;
goto v___jp_1842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___boxed(lean_object* v_modifier_2091_, lean_object* v_dateformat_2092_, lean_object* v_date_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_2091_, v_dateformat_2092_, v_date_2093_);
lean_dec_ref(v_dateformat_2092_);
lean_dec_ref(v_modifier_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0(lean_object* v___x_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
v___x_2098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___y_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0(lean_object* v___x_2099_, lean_object* v_b_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_fst_2102_; lean_object* v_snd_2103_; lean_object* v___x_2104_; 
v_fst_2102_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_fst_2102_);
v_snd_2103_ = lean_ctor_get(v___x_2099_, 1);
lean_inc(v_snd_2103_);
lean_dec_ref(v___x_2099_);
lean_inc_ref(v___y_2101_);
v___x_2104_ = lean_apply_1(v_b_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_dec(v_snd_2103_);
lean_dec(v_fst_2102_);
lean_dec_ref(v___y_2101_);
return v___x_2104_;
}
else
{
lean_object* v_pos_2105_; lean_object* v_snd_2106_; lean_object* v_snd_2107_; uint8_t v_decide_2108_; 
v_pos_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_pos_2105_);
v_snd_2106_ = lean_ctor_get(v___y_2101_, 1);
lean_inc(v_snd_2106_);
lean_dec_ref(v___y_2101_);
v_snd_2107_ = lean_ctor_get(v_pos_2105_, 1);
v_decide_2108_ = lean_nat_dec_eq(v_snd_2106_, v_snd_2107_);
lean_dec(v_snd_2106_);
if (v_decide_2108_ == 0)
{
lean_dec(v_pos_2105_);
lean_dec(v_snd_2103_);
lean_dec(v_fst_2102_);
return v___x_2104_;
}
else
{
lean_object* v___x_2109_; 
lean_dec_ref_known(v___x_2104_, 2);
v___x_2109_ = l_Std_Internal_Parsec_String_pstring(v_fst_2102_, v_pos_2105_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_pos_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
v_pos_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v___x_2109_, 1);
lean_dec(v_unused_2118_);
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_pos_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v_snd_2103_);
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_pos_2110_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_snd_2103_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
else
{
lean_object* v_pos_2119_; lean_object* v_err_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_snd_2103_);
v_pos_2119_ = lean_ctor_get(v___x_2109_, 0);
v_err_2120_ = lean_ctor_get(v___x_2109_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2109_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_err_2120_);
lean_inc(v_pos_2119_);
lean_dec(v___x_2109_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_pos_2119_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_err_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(lean_object* v_as_2128_, size_t v_i_2129_, size_t v_stop_2130_, lean_object* v_b_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_usize_dec_eq(v_i_2129_, v_stop_2130_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; lean_object* v___f_2135_; size_t v___x_2136_; size_t v___x_2137_; 
v___x_2134_ = lean_array_uget_borrowed(v_as_2128_, v_i_2129_);
lean_inc(v___x_2134_);
v___f_2135_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2135_, 0, v___x_2134_);
lean_closure_set(v___f_2135_, 1, v_b_2131_);
v___x_2136_ = ((size_t)1ULL);
v___x_2137_ = lean_usize_add(v_i_2129_, v___x_2136_);
v_i_2129_ = v___x_2137_;
v_b_2131_ = v___f_2135_;
goto _start;
}
else
{
lean_object* v___x_2139_; 
v___x_2139_ = lean_apply_1(v_b_2131_, v___y_2132_);
return v___x_2139_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2128_ = stack[0].m_obj;
size_t v_i_2129_ = stack[1].m_num;
size_t v_stop_2130_ = stack[2].m_num;
lean_object* v_b_2131_ = stack[3].m_obj;
lean_object* v___y_2132_ = stack[4].m_obj;
lean_object* v_res_2140_;
v_res_2140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2128_, v_i_2129_, v_stop_2130_, v_b_2131_, v___y_2132_);
stack->m_obj
 = v_res_2140_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___boxed(lean_object* v_as_2141_, lean_object* v_i_2142_, lean_object* v_stop_2143_, lean_object* v_b_2144_, lean_object* v___y_2145_){
_start:
{
size_t v_i_boxed_2146_; size_t v_stop_boxed_2147_; lean_object* v_res_2148_; 
v_i_boxed_2146_ = lean_unbox_usize(v_i_2142_);
lean_dec(v_i_2142_);
v_stop_boxed_2147_ = lean_unbox_usize(v_stop_2143_);
lean_dec(v_stop_2143_);
v_res_2148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2141_, v_i_boxed_2146_, v_stop_boxed_2147_, v_b_2144_, v___y_2145_);
lean_dec_ref(v_as_2141_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(lean_object* v_pairs_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = lean_array_get_size(v_pairs_2154_);
v___x_2158_ = lean_nat_dec_lt(v___x_2156_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2160_, 0, v_a_2155_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
return v___x_2160_;
}
else
{
lean_object* v___f_2161_; uint8_t v___x_2162_; 
v___f_2161_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2));
v___x_2162_ = lean_nat_dec_le(v___x_2157_, v___x_2157_);
if (v___x_2162_ == 0)
{
if (v___x_2158_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_a_2155_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
return v___x_2164_;
}
else
{
size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = lean_usize_of_nat(v___x_2157_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2154_, v___x_2165_, v___x_2166_, v___f_2161_, v_a_2155_);
return v___x_2167_;
}
}
else
{
size_t v___x_2168_; size_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = ((size_t)0ULL);
v___x_2169_ = lean_usize_of_nat(v___x_2157_);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2154_, v___x_2168_, v___x_2169_, v___f_2161_, v_a_2155_);
return v___x_2170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___boxed(lean_object* v_pairs_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2171_, v_a_2172_);
lean_dec_ref(v_pairs_2171_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(lean_object* v_00_u03b1_2174_, lean_object* v_pairs_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2175_, v_a_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___boxed(lean_object* v_00_u03b1_2178_, lean_object* v_pairs_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(v_00_u03b1_2178_, v_pairs_2179_, v_a_2180_);
lean_dec_ref(v_pairs_2179_);
return v_res_2181_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_object* v_00_u03b1_2182_, lean_object* v_as_2183_, size_t v_i_2184_, size_t v_stop_2185_, lean_object* v_b_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2183_, v_i_2184_, v_stop_2185_, v_b_2186_, v___y_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2183_ = stack[1].m_obj;
size_t v_i_2184_ = stack[2].m_num;
size_t v_stop_2185_ = stack[3].m_num;
lean_object* v_b_2186_ = stack[4].m_obj;
lean_object* v___y_2187_ = stack[5].m_obj;
lean_object* v_res_2189_;
v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_box(0), v_as_2183_, v_i_2184_, v_stop_2185_, v_b_2186_, v___y_2187_);
stack->m_obj
 = v_res_2189_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(size_t v_sz_2199_, size_t v_i_2200_, lean_object* v_bs_2201_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2199_ = stack[0].m_num;
size_t v_i_2200_ = stack[1].m_num;
lean_object* v_bs_2201_ = stack[2].m_obj;
lean_object* v_res_2215_;
v_res_2215_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2199_, v_i_2200_, v_bs_2201_);
stack->m_obj
 = v_res_2215_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2216_, lean_object* v_i_2217_, lean_object* v_bs_2218_){
_start:
{
size_t v_sz_boxed_2219_; size_t v_i_boxed_2220_; lean_object* v_res_2221_; 
v_sz_boxed_2219_ = lean_unbox_usize(v_sz_2216_);
lean_dec(v_sz_2216_);
v_i_boxed_2220_ = lean_unbox_usize(v_i_2217_);
lean_dec(v_i_2217_);
v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_boxed_2219_, v_i_boxed_2220_, v_bs_2218_);
return v_res_2221_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(lean_object* v_as_2222_, size_t v_sz_2223_, size_t v_i_2224_, lean_object* v_bs_2225_){
_start:
{
uint8_t v___x_2226_; 
v___x_2226_ = lean_usize_dec_lt(v_i_2224_, v_sz_2223_);
if (v___x_2226_ == 0)
{
return v_bs_2225_;
}
else
{
lean_object* v_v_2227_; lean_object* v___x_2228_; lean_object* v_bs_x27_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v_v_2227_ = lean_array_uget(v_bs_2225_, v_i_2224_);
v___x_2228_ = lean_unsigned_to_nat(0u);
v_bs_x27_2229_ = lean_array_uset(v_bs_2225_, v_i_2224_, v___x_2228_);
v___x_2230_ = lean_usize_to_nat(v_i_2224_);
v___x_2231_ = lean_nat_to_int(v___x_2230_);
v___x_2232_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2233_ = lean_int_add(v___x_2231_, v___x_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_v_2227_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = ((size_t)1ULL);
v___x_2236_ = lean_usize_add(v_i_2224_, v___x_2235_);
v___x_2237_ = lean_array_uset(v_bs_x27_2229_, v_i_2224_, v___x_2234_);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2223_, v___x_2236_, v___x_2237_);
return v___x_2238_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2222_ = stack[0].m_obj;
size_t v_sz_2223_ = stack[1].m_num;
size_t v_i_2224_ = stack[2].m_num;
lean_object* v_bs_2225_ = stack[3].m_obj;
lean_object* v_res_2239_;
v_res_2239_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_as_2222_, v_sz_2223_, v_i_2224_, v_bs_2225_);
stack->m_obj
 = v_res_2239_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0___boxed(lean_object* v_as_2240_, lean_object* v_sz_2241_, lean_object* v_i_2242_, lean_object* v_bs_2243_){
_start:
{
size_t v_sz_boxed_2244_; size_t v_i_boxed_2245_; lean_object* v_res_2246_; 
v_sz_boxed_2244_ = lean_unbox_usize(v_sz_2241_);
lean_dec(v_sz_2241_);
v_i_boxed_2245_ = lean_unbox_usize(v_i_2242_);
lean_dec(v_i_2242_);
v_res_2246_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_as_2240_, v_sz_boxed_2244_, v_i_boxed_2245_, v_bs_2243_);
lean_dec_ref(v_as_2240_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(lean_object* v_arr_2247_){
_start:
{
size_t v_sz_2248_; size_t v___x_2249_; lean_object* v___x_2250_; 
v_sz_2248_ = lean_array_size(v_arr_2247_);
v___x_2249_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2247_);
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2247_, v_sz_2248_, v___x_2249_, v_arr_2247_);
lean_dec_ref(v_arr_2247_);
return v___x_2250_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(lean_object* v_as_2251_, size_t v_sz_2252_, size_t v_i_2253_, lean_object* v_bs_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2252_, v_i_2253_, v_bs_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2251_ = stack[0].m_obj;
size_t v_sz_2252_ = stack[1].m_num;
size_t v_i_2253_ = stack[2].m_num;
lean_object* v_bs_2254_ = stack[3].m_obj;
lean_object* v_res_2256_;
v_res_2256_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(v_as_2251_, v_sz_2252_, v_i_2253_, v_bs_2254_);
stack->m_obj
 = v_res_2256_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___boxed(lean_object* v_as_2257_, lean_object* v_sz_2258_, lean_object* v_i_2259_, lean_object* v_bs_2260_){
_start:
{
size_t v_sz_boxed_2261_; size_t v_i_boxed_2262_; lean_object* v_res_2263_; 
v_sz_boxed_2261_ = lean_unbox_usize(v_sz_2258_);
lean_dec(v_sz_2258_);
v_i_boxed_2262_ = lean_unbox_usize(v_i_2259_);
lean_dec(v_i_2259_);
v_res_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(v_as_2257_, v_sz_boxed_2261_, v_i_boxed_2262_, v_bs_2260_);
lean_dec_ref(v_as_2257_);
return v_res_2263_;
}
}
uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object* v_x_2264_){
_start:
{
lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = lean_unsigned_to_nat(0u);
v___x_2266_ = lean_nat_dec_eq(v_x_2264_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = lean_nat_dec_eq(v_x_2264_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = lean_unsigned_to_nat(2u);
v___x_2270_ = lean_nat_dec_eq(v_x_2264_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = lean_unsigned_to_nat(3u);
v___x_2272_ = lean_nat_dec_eq(v_x_2264_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(4u);
v___x_2274_ = lean_nat_dec_eq(v_x_2264_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = lean_unsigned_to_nat(5u);
v___x_2276_ = lean_nat_dec_eq(v_x_2264_, v___x_2275_);
if (v___x_2276_ == 0)
{
uint8_t v___x_2277_; 
v___x_2277_ = 5;
return v___x_2277_;
}
else
{
uint8_t v___x_2278_; 
v___x_2278_ = 4;
return v___x_2278_;
}
}
else
{
uint8_t v___x_2279_; 
v___x_2279_ = 3;
return v___x_2279_;
}
}
else
{
uint8_t v___x_2280_; 
v___x_2280_ = 2;
return v___x_2280_;
}
}
else
{
uint8_t v___x_2281_; 
v___x_2281_ = 1;
return v___x_2281_;
}
}
else
{
uint8_t v___x_2282_; 
v___x_2282_ = 0;
return v___x_2282_;
}
}
else
{
uint8_t v___x_2283_; 
v___x_2283_ = 6;
return v___x_2283_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2264_ = stack[0].m_obj;
uint8_t v_res_2284_;
v_res_2284_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_x_2264_);
stack->m_num = v_res_2284_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object* v_x_2285_){
_start:
{
uint8_t v_res_2286_; lean_object* v_r_2287_; 
v_res_2286_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_x_2285_);
lean_dec(v_x_2285_);
v_r_2287_ = lean_box(v_res_2286_);
return v_r_2287_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(size_t v_sz_2288_, size_t v_i_2289_, lean_object* v_bs_2290_){
_start:
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_usize_dec_lt(v_i_2289_, v_sz_2288_);
if (v___x_2291_ == 0)
{
return v_bs_2290_;
}
else
{
lean_object* v_v_2292_; lean_object* v___x_2293_; lean_object* v_bs_x27_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; size_t v___x_2302_; size_t v___x_2303_; lean_object* v___x_2304_; 
v_v_2292_ = lean_array_uget(v_bs_2290_, v_i_2289_);
v___x_2293_ = lean_unsigned_to_nat(0u);
v_bs_x27_2294_ = lean_array_uset(v_bs_2290_, v_i_2289_, v___x_2293_);
v___x_2295_ = lean_usize_to_nat(v_i_2289_);
v___x_2296_ = lean_nat_to_int(v___x_2295_);
v___x_2297_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2298_ = lean_int_add(v___x_2296_, v___x_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = l_Std_Time_Weekday_ofOrdinal(v___x_2298_);
lean_dec(v___x_2298_);
v___x_2300_ = lean_box(v___x_2299_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v_v_2292_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = ((size_t)1ULL);
v___x_2303_ = lean_usize_add(v_i_2289_, v___x_2302_);
v___x_2304_ = lean_array_uset(v_bs_x27_2294_, v_i_2289_, v___x_2301_);
v_i_2289_ = v___x_2303_;
v_bs_2290_ = v___x_2304_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2288_ = stack[0].m_num;
size_t v_i_2289_ = stack[1].m_num;
lean_object* v_bs_2290_ = stack[2].m_obj;
lean_object* v_res_2306_;
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2288_, v_i_2289_, v_bs_2290_);
stack->m_obj
 = v_res_2306_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2307_, lean_object* v_i_2308_, lean_object* v_bs_2309_){
_start:
{
size_t v_sz_boxed_2310_; size_t v_i_boxed_2311_; lean_object* v_res_2312_; 
v_sz_boxed_2310_ = lean_unbox_usize(v_sz_2307_);
lean_dec(v_sz_2307_);
v_i_boxed_2311_ = lean_unbox_usize(v_i_2308_);
lean_dec(v_i_2308_);
v_res_2312_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_boxed_2310_, v_i_boxed_2311_, v_bs_2309_);
return v_res_2312_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(lean_object* v_as_2313_, size_t v_sz_2314_, size_t v_i_2315_, lean_object* v_bs_2316_){
_start:
{
uint8_t v___x_2317_; 
v___x_2317_ = lean_usize_dec_lt(v_i_2315_, v_sz_2314_);
if (v___x_2317_ == 0)
{
return v_bs_2316_;
}
else
{
lean_object* v_v_2318_; lean_object* v___x_2319_; lean_object* v_bs_x27_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_v_2318_ = lean_array_uget(v_bs_2316_, v_i_2315_);
v___x_2319_ = lean_unsigned_to_nat(0u);
v_bs_x27_2320_ = lean_array_uset(v_bs_2316_, v_i_2315_, v___x_2319_);
v___x_2321_ = lean_usize_to_nat(v_i_2315_);
v___x_2322_ = lean_nat_to_int(v___x_2321_);
v___x_2323_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2324_ = lean_int_add(v___x_2322_, v___x_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = l_Std_Time_Weekday_ofOrdinal(v___x_2324_);
lean_dec(v___x_2324_);
v___x_2326_ = lean_box(v___x_2325_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_v_2318_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_add(v_i_2315_, v___x_2328_);
v___x_2330_ = lean_array_uset(v_bs_x27_2320_, v_i_2315_, v___x_2327_);
v___x_2331_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2314_, v___x_2329_, v___x_2330_);
return v___x_2331_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2313_ = stack[0].m_obj;
size_t v_sz_2314_ = stack[1].m_num;
size_t v_i_2315_ = stack[2].m_num;
lean_object* v_bs_2316_ = stack[3].m_obj;
lean_object* v_res_2332_;
v_res_2332_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_as_2313_, v_sz_2314_, v_i_2315_, v_bs_2316_);
stack->m_obj
 = v_res_2332_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0___boxed(lean_object* v_as_2333_, lean_object* v_sz_2334_, lean_object* v_i_2335_, lean_object* v_bs_2336_){
_start:
{
size_t v_sz_boxed_2337_; size_t v_i_boxed_2338_; lean_object* v_res_2339_; 
v_sz_boxed_2337_ = lean_unbox_usize(v_sz_2334_);
lean_dec(v_sz_2334_);
v_i_boxed_2338_ = lean_unbox_usize(v_i_2335_);
lean_dec(v_i_2335_);
v_res_2339_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_as_2333_, v_sz_boxed_2337_, v_i_boxed_2338_, v_bs_2336_);
lean_dec_ref(v_as_2333_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(lean_object* v_arr_2340_){
_start:
{
size_t v_sz_2341_; size_t v___x_2342_; lean_object* v___x_2343_; 
v_sz_2341_ = lean_array_size(v_arr_2340_);
v___x_2342_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2340_);
v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_arr_2340_, v_sz_2341_, v___x_2342_, v_arr_2340_);
lean_dec_ref(v_arr_2340_);
return v___x_2343_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(lean_object* v_as_2344_, size_t v_sz_2345_, size_t v_i_2346_, lean_object* v_bs_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2345_, v_i_2346_, v_bs_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2344_ = stack[0].m_obj;
size_t v_sz_2345_ = stack[1].m_num;
size_t v_i_2346_ = stack[2].m_num;
lean_object* v_bs_2347_ = stack[3].m_obj;
lean_object* v_res_2349_;
v_res_2349_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(v_as_2344_, v_sz_2345_, v_i_2346_, v_bs_2347_);
stack->m_obj
 = v_res_2349_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___boxed(lean_object* v_as_2350_, lean_object* v_sz_2351_, lean_object* v_i_2352_, lean_object* v_bs_2353_){
_start:
{
size_t v_sz_boxed_2354_; size_t v_i_boxed_2355_; lean_object* v_res_2356_; 
v_sz_boxed_2354_ = lean_unbox_usize(v_sz_2351_);
lean_dec(v_sz_2351_);
v_i_boxed_2355_ = lean_unbox_usize(v_i_2352_);
lean_dec(v_i_2352_);
v_res_2356_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(v_as_2350_, v_sz_boxed_2354_, v_i_boxed_2355_, v_bs_2353_);
lean_dec_ref(v_as_2350_);
return v_res_2356_;
}
}
uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object* v_x_2357_){
_start:
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = lean_unsigned_to_nat(0u);
v___x_2359_ = lean_nat_dec_eq(v_x_2357_, v___x_2358_);
if (v___x_2359_ == 0)
{
uint8_t v___x_2360_; 
v___x_2360_ = 1;
return v___x_2360_;
}
else
{
uint8_t v___x_2361_; 
v___x_2361_ = 0;
return v___x_2361_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2357_ = stack[0].m_obj;
uint8_t v_res_2362_;
v_res_2362_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_x_2357_);
stack->m_num = v_res_2362_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object* v_x_2363_){
_start:
{
uint8_t v_res_2364_; lean_object* v_r_2365_; 
v_res_2364_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_x_2363_);
lean_dec(v_x_2363_);
v_r_2365_ = lean_box(v_res_2364_);
return v_r_2365_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(size_t v_sz_2366_, size_t v_i_2367_, lean_object* v_bs_2368_){
_start:
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_usize_dec_lt(v_i_2367_, v_sz_2366_);
if (v___x_2369_ == 0)
{
return v_bs_2368_;
}
else
{
lean_object* v_v_2370_; lean_object* v___x_2371_; lean_object* v_bs_x27_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; size_t v___x_2377_; size_t v___x_2378_; lean_object* v___x_2379_; 
v_v_2370_ = lean_array_uget(v_bs_2368_, v_i_2367_);
v___x_2371_ = lean_unsigned_to_nat(0u);
v_bs_x27_2372_ = lean_array_uset(v_bs_2368_, v_i_2367_, v___x_2371_);
v___x_2373_ = lean_usize_to_nat(v_i_2367_);
v___x_2374_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v___x_2373_);
lean_dec(v___x_2373_);
v___x_2375_ = lean_box(v___x_2374_);
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_v_2370_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = ((size_t)1ULL);
v___x_2378_ = lean_usize_add(v_i_2367_, v___x_2377_);
v___x_2379_ = lean_array_uset(v_bs_x27_2372_, v_i_2367_, v___x_2376_);
v_i_2367_ = v___x_2378_;
v_bs_2368_ = v___x_2379_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2366_ = stack[0].m_num;
size_t v_i_2367_ = stack[1].m_num;
lean_object* v_bs_2368_ = stack[2].m_obj;
lean_object* v_res_2381_;
v_res_2381_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2366_, v_i_2367_, v_bs_2368_);
stack->m_obj
 = v_res_2381_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg___boxed(lean_object* v_sz_2382_, lean_object* v_i_2383_, lean_object* v_bs_2384_){
_start:
{
size_t v_sz_boxed_2385_; size_t v_i_boxed_2386_; lean_object* v_res_2387_; 
v_sz_boxed_2385_ = lean_unbox_usize(v_sz_2382_);
lean_dec(v_sz_2382_);
v_i_boxed_2386_ = lean_unbox_usize(v_i_2383_);
lean_dec(v_i_2383_);
v_res_2387_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_boxed_2385_, v_i_boxed_2386_, v_bs_2384_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(lean_object* v_arr_2388_){
_start:
{
size_t v_sz_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
v_sz_2389_ = lean_array_size(v_arr_2388_);
v___x_2390_ = ((size_t)0ULL);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2389_, v___x_2390_, v_arr_2388_);
return v___x_2391_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(lean_object* v_as_2392_, size_t v_sz_2393_, size_t v_i_2394_, lean_object* v_bs_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2393_, v_i_2394_, v_bs_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2392_ = stack[0].m_obj;
size_t v_sz_2393_ = stack[1].m_num;
size_t v_i_2394_ = stack[2].m_num;
lean_object* v_bs_2395_ = stack[3].m_obj;
lean_object* v_res_2397_;
v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(v_as_2392_, v_sz_2393_, v_i_2394_, v_bs_2395_);
stack->m_obj
 = v_res_2397_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___boxed(lean_object* v_as_2398_, lean_object* v_sz_2399_, lean_object* v_i_2400_, lean_object* v_bs_2401_){
_start:
{
size_t v_sz_boxed_2402_; size_t v_i_boxed_2403_; lean_object* v_res_2404_; 
v_sz_boxed_2402_ = lean_unbox_usize(v_sz_2399_);
lean_dec(v_sz_2399_);
v_i_boxed_2403_ = lean_unbox_usize(v_i_2400_);
lean_dec(v_i_2400_);
v_res_2404_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(v_as_2398_, v_sz_boxed_2402_, v_i_boxed_2403_, v_bs_2401_);
lean_dec_ref(v_as_2398_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(lean_object* v_arr_2405_){
_start:
{
size_t v_sz_2406_; size_t v___x_2407_; lean_object* v___x_2408_; 
v_sz_2406_ = lean_array_size(v_arr_2405_);
v___x_2407_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2405_);
v___x_2408_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2405_, v_sz_2406_, v___x_2407_, v_arr_2405_);
lean_dec_ref(v_arr_2405_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(lean_object* v_symbols_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_monthLong_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_monthLong_2411_ = lean_ctor_get(v_symbols_2409_, 0);
lean_inc_ref(v_monthLong_2411_);
lean_dec_ref(v_symbols_2409_);
v___x_2412_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthLong_2411_);
v___x_2413_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2412_, v_a_2410_);
lean_dec_ref(v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object* v_symbols_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_monthShort_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_monthShort_2416_ = lean_ctor_get(v_symbols_2414_, 1);
lean_inc_ref(v_monthShort_2416_);
lean_dec_ref(v_symbols_2414_);
v___x_2417_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthShort_2416_);
v___x_2418_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2417_, v_a_2415_);
lean_dec_ref(v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(lean_object* v_symbols_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_monthNarrow_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_monthNarrow_2421_ = lean_ctor_get(v_symbols_2419_, 2);
lean_inc_ref(v_monthNarrow_2421_);
lean_dec_ref(v_symbols_2419_);
v___x_2422_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthNarrow_2421_);
v___x_2423_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2422_, v_a_2420_);
lean_dec_ref(v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(lean_object* v_symbols_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_weekdayLong_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_weekdayLong_2426_ = lean_ctor_get(v_symbols_2424_, 3);
lean_inc_ref(v_weekdayLong_2426_);
lean_dec_ref(v_symbols_2424_);
v___x_2427_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayLong_2426_);
v___x_2428_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2427_, v_a_2425_);
lean_dec_ref(v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(lean_object* v_symbols_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_weekdayShort_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_weekdayShort_2431_ = lean_ctor_get(v_symbols_2429_, 4);
lean_inc_ref(v_weekdayShort_2431_);
lean_dec_ref(v_symbols_2429_);
v___x_2432_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayShort_2431_);
v___x_2433_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2432_, v_a_2430_);
lean_dec_ref(v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(lean_object* v_symbols_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_weekdayNarrow_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_weekdayNarrow_2436_ = lean_ctor_get(v_symbols_2434_, 5);
lean_inc_ref(v_weekdayNarrow_2436_);
lean_dec_ref(v_symbols_2434_);
v___x_2437_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayNarrow_2436_);
v___x_2438_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2437_, v_a_2435_);
lean_dec_ref(v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(lean_object* v_symbols_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_weekdayTwoLetter_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_weekdayTwoLetter_2441_ = lean_ctor_get(v_symbols_2439_, 6);
lean_inc_ref(v_weekdayTwoLetter_2441_);
lean_dec_ref(v_symbols_2439_);
v___x_2442_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayTwoLetter_2441_);
v___x_2443_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2442_, v_a_2440_);
lean_dec_ref(v___x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(lean_object* v_symbols_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_eraShort_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_eraShort_2446_ = lean_ctor_get(v_symbols_2444_, 7);
lean_inc_ref(v_eraShort_2446_);
lean_dec_ref(v_symbols_2444_);
v___x_2447_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraShort_2446_);
v___x_2448_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2447_, v_a_2445_);
lean_dec_ref(v___x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(lean_object* v_symbols_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v_eraLong_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_eraLong_2451_ = lean_ctor_get(v_symbols_2449_, 8);
lean_inc_ref(v_eraLong_2451_);
lean_dec_ref(v_symbols_2449_);
v___x_2452_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraLong_2451_);
v___x_2453_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2452_, v_a_2450_);
lean_dec_ref(v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(lean_object* v_symbols_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_eraNarrow_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_eraNarrow_2456_ = lean_ctor_get(v_symbols_2454_, 9);
lean_inc_ref(v_eraNarrow_2456_);
lean_dec_ref(v_symbols_2454_);
v___x_2457_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraNarrow_2456_);
v___x_2458_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2457_, v_a_2455_);
lean_dec_ref(v___x_2457_);
return v___x_2458_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_unsigned_to_nat(3u);
v___x_2460_ = lean_nat_to_int(v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber(lean_object* v_a_2461_){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
lean_inc_ref(v_a_2461_);
v___x_2463_ = l_Std_Internal_Parsec_String_pstring(v___x_2462_, v_a_2461_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_pos_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v_a_2461_);
v_pos_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; 
v_unused_2473_ = lean_ctor_get(v___x_2463_, 1);
lean_dec(v_unused_2473_);
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2472_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_pos_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2472_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2468_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v___x_2468_);
v___x_2470_ = v___x_2466_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_pos_2464_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
else
{
lean_object* v_pos_2474_; lean_object* v_err_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2552_; 
v_pos_2474_ = lean_ctor_get(v___x_2463_, 0);
v_err_2475_ = lean_ctor_get(v___x_2463_, 1);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2477_ = v___x_2463_;
v_isShared_2478_ = v_isSharedCheck_2552_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_err_2475_);
lean_inc(v_pos_2474_);
lean_dec(v___x_2463_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2552_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_snd_2479_; lean_object* v_snd_2480_; uint8_t v_decide_2481_; 
v_snd_2479_ = lean_ctor_get(v_a_2461_, 1);
lean_inc(v_snd_2479_);
lean_dec_ref(v_a_2461_);
v_snd_2480_ = lean_ctor_get(v_pos_2474_, 1);
v_decide_2481_ = lean_nat_dec_eq(v_snd_2479_, v_snd_2480_);
lean_dec(v_snd_2479_);
if (v_decide_2481_ == 0)
{
lean_object* v___x_2483_; 
if (v_isShared_2478_ == 0)
{
v___x_2483_ = v___x_2477_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_pos_2474_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_err_2475_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_inc(v_snd_2480_);
lean_del_object(v___x_2477_);
lean_dec(v_err_2475_);
v___x_2485_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
v___x_2486_ = l_Std_Internal_Parsec_String_pstring(v___x_2485_, v_pos_2474_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_pos_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_snd_2480_);
v_pos_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v___x_2486_, 1);
lean_dec(v_unused_2496_);
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2495_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_pos_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2495_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2491_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 1, v___x_2491_);
v___x_2493_ = v___x_2489_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_pos_2487_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
else
{
lean_object* v_pos_2497_; lean_object* v_err_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2551_; 
v_pos_2497_ = lean_ctor_get(v___x_2486_, 0);
v_err_2498_ = lean_ctor_get(v___x_2486_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2500_ = v___x_2486_;
v_isShared_2501_ = v_isSharedCheck_2551_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_err_2498_);
lean_inc(v_pos_2497_);
lean_dec(v___x_2486_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2551_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_snd_2502_; uint8_t v_decide_2503_; 
v_snd_2502_ = lean_ctor_get(v_pos_2497_, 1);
v_decide_2503_ = lean_nat_dec_eq(v_snd_2480_, v_snd_2502_);
lean_dec(v_snd_2480_);
if (v_decide_2503_ == 0)
{
lean_object* v___x_2505_; 
if (v_isShared_2501_ == 0)
{
v___x_2505_ = v___x_2500_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_pos_2497_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_err_2498_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_inc(v_snd_2502_);
lean_del_object(v___x_2500_);
lean_dec(v_err_2498_);
v___x_2507_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
v___x_2508_ = l_Std_Internal_Parsec_String_pstring(v___x_2507_, v_pos_2497_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_pos_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2517_; 
lean_dec(v_snd_2502_);
v_pos_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; 
v_unused_2518_ = lean_ctor_get(v___x_2508_, 1);
lean_dec(v_unused_2518_);
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2517_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_pos_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2517_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2513_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 1, v___x_2513_);
v___x_2515_ = v___x_2511_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_pos_2509_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
else
{
lean_object* v_pos_2519_; lean_object* v_err_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2550_; 
v_pos_2519_ = lean_ctor_get(v___x_2508_, 0);
v_err_2520_ = lean_ctor_get(v___x_2508_, 1);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2522_ = v___x_2508_;
v_isShared_2523_ = v_isSharedCheck_2550_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_err_2520_);
lean_inc(v_pos_2519_);
lean_dec(v___x_2508_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2550_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v_snd_2524_; uint8_t v_decide_2525_; 
v_snd_2524_ = lean_ctor_get(v_pos_2519_, 1);
v_decide_2525_ = lean_nat_dec_eq(v_snd_2502_, v_snd_2524_);
lean_dec(v_snd_2502_);
if (v_decide_2525_ == 0)
{
lean_object* v___x_2527_; 
if (v_isShared_2523_ == 0)
{
v___x_2527_ = v___x_2522_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_pos_2519_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_err_2520_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_del_object(v___x_2522_);
lean_dec(v_err_2520_);
v___x_2529_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
v___x_2530_ = l_Std_Internal_Parsec_String_pstring(v___x_2529_, v_pos_2519_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_pos_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2539_; 
v_pos_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; 
v_unused_2540_ = lean_ctor_get(v___x_2530_, 1);
lean_dec(v_unused_2540_);
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_pos_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v___x_2535_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_pos_2531_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
else
{
lean_object* v_pos_2541_; lean_object* v_err_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v_pos_2541_ = lean_ctor_get(v___x_2530_, 0);
v_err_2542_ = lean_ctor_get(v___x_2530_, 1);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2530_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_err_2542_);
lean_inc(v_pos_2541_);
lean_dec(v___x_2530_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_pos_2541_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_err_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(lean_object* v_symbols_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_quarterLong_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_quarterLong_2555_ = lean_ctor_get(v_symbols_2553_, 11);
lean_inc_ref(v_quarterLong_2555_);
lean_dec_ref(v_symbols_2553_);
v___x_2556_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterLong_2555_);
v___x_2557_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2556_, v_a_2554_);
lean_dec_ref(v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(lean_object* v_symbols_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_quarterShort_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_quarterShort_2560_ = lean_ctor_get(v_symbols_2558_, 10);
lean_inc_ref(v_quarterShort_2560_);
lean_dec_ref(v_symbols_2558_);
v___x_2561_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterShort_2560_);
v___x_2562_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2561_, v_a_2559_);
lean_dec_ref(v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(lean_object* v_symbols_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_quarterNarrow_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_quarterNarrow_2565_ = lean_ctor_get(v_symbols_2563_, 12);
lean_inc_ref(v_quarterNarrow_2565_);
lean_dec_ref(v_symbols_2563_);
v___x_2566_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterNarrow_2565_);
v___x_2567_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2566_, v_a_2564_);
lean_dec_ref(v___x_2566_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(lean_object* v_symbols_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_amShort_2570_; lean_object* v_pmShort_2571_; lean_object* v___x_2572_; 
v_amShort_2570_ = lean_ctor_get(v_symbols_2568_, 13);
lean_inc_ref(v_amShort_2570_);
v_pmShort_2571_ = lean_ctor_get(v_symbols_2568_, 14);
lean_inc_ref(v_pmShort_2571_);
lean_dec_ref(v_symbols_2568_);
lean_inc_ref(v_a_2569_);
v___x_2572_ = l_Std_Internal_Parsec_String_pstring(v_amShort_2570_, v_a_2569_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_pos_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2582_; 
lean_dec_ref(v_pmShort_2571_);
lean_dec_ref(v_a_2569_);
v_pos_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; 
v_unused_2583_ = lean_ctor_get(v___x_2572_, 1);
lean_dec(v_unused_2583_);
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2582_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_pos_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2582_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
uint8_t v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2577_ = 0;
v___x_2578_ = lean_box(v___x_2577_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 1, v___x_2578_);
v___x_2580_ = v___x_2575_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_pos_2573_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
else
{
lean_object* v_pos_2584_; lean_object* v_err_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2616_; 
v_pos_2584_ = lean_ctor_get(v___x_2572_, 0);
v_err_2585_ = lean_ctor_get(v___x_2572_, 1);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2587_ = v___x_2572_;
v_isShared_2588_ = v_isSharedCheck_2616_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_err_2585_);
lean_inc(v_pos_2584_);
lean_dec(v___x_2572_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2616_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v_snd_2589_; lean_object* v_snd_2590_; uint8_t v_decide_2591_; 
v_snd_2589_ = lean_ctor_get(v_a_2569_, 1);
lean_inc(v_snd_2589_);
lean_dec_ref(v_a_2569_);
v_snd_2590_ = lean_ctor_get(v_pos_2584_, 1);
v_decide_2591_ = lean_nat_dec_eq(v_snd_2589_, v_snd_2590_);
lean_dec(v_snd_2589_);
if (v_decide_2591_ == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref(v_pmShort_2571_);
if (v_isShared_2588_ == 0)
{
v___x_2593_ = v___x_2587_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_pos_2584_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_err_2585_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
else
{
lean_object* v___x_2595_; 
lean_del_object(v___x_2587_);
lean_dec(v_err_2585_);
v___x_2595_ = l_Std_Internal_Parsec_String_pstring(v_pmShort_2571_, v_pos_2584_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_pos_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2605_; 
v_pos_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v___x_2595_, 1);
lean_dec(v_unused_2606_);
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_pos_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
uint8_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2600_ = 1;
v___x_2601_ = lean_box(v___x_2600_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 1, v___x_2601_);
v___x_2603_ = v___x_2598_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_pos_2596_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
lean_object* v_pos_2607_; lean_object* v_err_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
v_pos_2607_ = lean_ctor_get(v___x_2595_, 0);
v_err_2608_ = lean_ctor_get(v___x_2595_, 1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2595_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_err_2608_);
lean_inc(v_pos_2607_);
lean_dec(v___x_2595_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_pos_2607_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_err_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(lean_object* v_symbols_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_amLong_2619_; lean_object* v_pmLong_2620_; lean_object* v___x_2621_; 
v_amLong_2619_ = lean_ctor_get(v_symbols_2617_, 15);
lean_inc_ref(v_amLong_2619_);
v_pmLong_2620_ = lean_ctor_get(v_symbols_2617_, 16);
lean_inc_ref(v_pmLong_2620_);
lean_dec_ref(v_symbols_2617_);
lean_inc_ref(v_a_2618_);
v___x_2621_ = l_Std_Internal_Parsec_String_pstring(v_amLong_2619_, v_a_2618_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_pos_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v_pmLong_2620_);
lean_dec_ref(v_a_2618_);
v_pos_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; 
v_unused_2632_ = lean_ctor_get(v___x_2621_, 1);
lean_dec(v_unused_2632_);
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2631_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_pos_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2631_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2626_ = 0;
v___x_2627_ = lean_box(v___x_2626_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 1, v___x_2627_);
v___x_2629_ = v___x_2624_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_pos_2622_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
else
{
lean_object* v_pos_2633_; lean_object* v_err_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2665_; 
v_pos_2633_ = lean_ctor_get(v___x_2621_, 0);
v_err_2634_ = lean_ctor_get(v___x_2621_, 1);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2636_ = v___x_2621_;
v_isShared_2637_ = v_isSharedCheck_2665_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_err_2634_);
lean_inc(v_pos_2633_);
lean_dec(v___x_2621_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2665_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v_snd_2638_; lean_object* v_snd_2639_; uint8_t v_decide_2640_; 
v_snd_2638_ = lean_ctor_get(v_a_2618_, 1);
lean_inc(v_snd_2638_);
lean_dec_ref(v_a_2618_);
v_snd_2639_ = lean_ctor_get(v_pos_2633_, 1);
v_decide_2640_ = lean_nat_dec_eq(v_snd_2638_, v_snd_2639_);
lean_dec(v_snd_2638_);
if (v_decide_2640_ == 0)
{
lean_object* v___x_2642_; 
lean_dec_ref(v_pmLong_2620_);
if (v_isShared_2637_ == 0)
{
v___x_2642_ = v___x_2636_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_pos_2633_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_err_2634_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
else
{
lean_object* v___x_2644_; 
lean_del_object(v___x_2636_);
lean_dec(v_err_2634_);
v___x_2644_ = l_Std_Internal_Parsec_String_pstring(v_pmLong_2620_, v_pos_2633_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_pos_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2654_; 
v_pos_2645_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v___x_2644_, 1);
lean_dec(v_unused_2655_);
v___x_2647_ = v___x_2644_;
v_isShared_2648_ = v_isSharedCheck_2654_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_pos_2645_);
lean_dec(v___x_2644_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2654_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
uint8_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2649_ = 1;
v___x_2650_ = lean_box(v___x_2649_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2650_);
v___x_2652_ = v___x_2647_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_pos_2645_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
else
{
lean_object* v_pos_2656_; lean_object* v_err_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
v_pos_2656_ = lean_ctor_get(v___x_2644_, 0);
v_err_2657_ = lean_ctor_get(v___x_2644_, 1);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2644_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_err_2657_);
lean_inc(v_pos_2656_);
lean_dec(v___x_2644_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_pos_2656_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_err_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(lean_object* v_symbols_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v_amNarrow_2668_; lean_object* v_pmNarrow_2669_; lean_object* v___x_2670_; 
v_amNarrow_2668_ = lean_ctor_get(v_symbols_2666_, 17);
lean_inc_ref(v_amNarrow_2668_);
v_pmNarrow_2669_ = lean_ctor_get(v_symbols_2666_, 18);
lean_inc_ref(v_pmNarrow_2669_);
lean_dec_ref(v_symbols_2666_);
lean_inc_ref(v_a_2667_);
v___x_2670_ = l_Std_Internal_Parsec_String_pstring(v_amNarrow_2668_, v_a_2667_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_pos_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref(v_pmNarrow_2669_);
lean_dec_ref(v_a_2667_);
v_pos_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; 
v_unused_2681_ = lean_ctor_get(v___x_2670_, 1);
lean_dec(v_unused_2681_);
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2680_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_pos_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2680_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2675_ = 0;
v___x_2676_ = lean_box(v___x_2675_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 1, v___x_2676_);
v___x_2678_ = v___x_2673_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_pos_2671_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
else
{
lean_object* v_pos_2682_; lean_object* v_err_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2714_; 
v_pos_2682_ = lean_ctor_get(v___x_2670_, 0);
v_err_2683_ = lean_ctor_get(v___x_2670_, 1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2685_ = v___x_2670_;
v_isShared_2686_ = v_isSharedCheck_2714_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_err_2683_);
lean_inc(v_pos_2682_);
lean_dec(v___x_2670_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2714_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_snd_2687_; lean_object* v_snd_2688_; uint8_t v_decide_2689_; 
v_snd_2687_ = lean_ctor_get(v_a_2667_, 1);
lean_inc(v_snd_2687_);
lean_dec_ref(v_a_2667_);
v_snd_2688_ = lean_ctor_get(v_pos_2682_, 1);
v_decide_2689_ = lean_nat_dec_eq(v_snd_2687_, v_snd_2688_);
lean_dec(v_snd_2687_);
if (v_decide_2689_ == 0)
{
lean_object* v___x_2691_; 
lean_dec_ref(v_pmNarrow_2669_);
if (v_isShared_2686_ == 0)
{
v___x_2691_ = v___x_2685_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_pos_2682_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_err_2683_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
else
{
lean_object* v___x_2693_; 
lean_del_object(v___x_2685_);
lean_dec(v_err_2683_);
v___x_2693_ = l_Std_Internal_Parsec_String_pstring(v_pmNarrow_2669_, v_pos_2682_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_pos_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2703_; 
v_pos_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2703_ == 0)
{
lean_object* v_unused_2704_; 
v_unused_2704_ = lean_ctor_get(v___x_2693_, 1);
lean_dec(v_unused_2704_);
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2703_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_pos_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2703_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2698_ = 1;
v___x_2699_ = lean_box(v___x_2698_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v___x_2699_);
v___x_2701_ = v___x_2696_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_pos_2694_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
else
{
lean_object* v_pos_2705_; lean_object* v_err_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
v_pos_2705_ = lean_ctor_get(v___x_2693_, 0);
v_err_2706_ = lean_ctor_get(v___x_2693_, 1);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2693_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_err_2706_);
lean_inc(v_pos_2705_);
lean_dec(v___x_2693_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_pos_2705_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_err_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(lean_object* v_dp_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_am_2717_; lean_object* v_pm_2718_; lean_object* v_noon_2719_; lean_object* v_midnight_2720_; lean_object* v___x_2721_; 
v_am_2717_ = lean_ctor_get(v_dp_2715_, 0);
lean_inc_ref(v_am_2717_);
v_pm_2718_ = lean_ctor_get(v_dp_2715_, 1);
lean_inc_ref(v_pm_2718_);
v_noon_2719_ = lean_ctor_get(v_dp_2715_, 2);
lean_inc_ref(v_noon_2719_);
v_midnight_2720_ = lean_ctor_get(v_dp_2715_, 3);
lean_inc_ref(v_midnight_2720_);
lean_dec_ref(v_dp_2715_);
lean_inc_ref(v_a_2716_);
v___x_2721_ = l_Std_Internal_Parsec_String_pstring(v_midnight_2720_, v_a_2716_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_pos_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2731_; 
lean_dec_ref(v_noon_2719_);
lean_dec_ref(v_pm_2718_);
lean_dec_ref(v_am_2717_);
lean_dec_ref(v_a_2716_);
v_pos_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; 
v_unused_2732_ = lean_ctor_get(v___x_2721_, 1);
lean_dec(v_unused_2732_);
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2731_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_pos_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2731_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2726_ = 3;
v___x_2727_ = lean_box(v___x_2726_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 1, v___x_2727_);
v___x_2729_ = v___x_2724_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_pos_2722_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
else
{
lean_object* v_pos_2733_; lean_object* v_err_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2811_; 
v_pos_2733_ = lean_ctor_get(v___x_2721_, 0);
v_err_2734_ = lean_ctor_get(v___x_2721_, 1);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2736_ = v___x_2721_;
v_isShared_2737_ = v_isSharedCheck_2811_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_err_2734_);
lean_inc(v_pos_2733_);
lean_dec(v___x_2721_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2811_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v_snd_2738_; lean_object* v_snd_2739_; uint8_t v_decide_2740_; 
v_snd_2738_ = lean_ctor_get(v_a_2716_, 1);
lean_inc(v_snd_2738_);
lean_dec_ref(v_a_2716_);
v_snd_2739_ = lean_ctor_get(v_pos_2733_, 1);
v_decide_2740_ = lean_nat_dec_eq(v_snd_2738_, v_snd_2739_);
lean_dec(v_snd_2738_);
if (v_decide_2740_ == 0)
{
lean_object* v___x_2742_; 
lean_dec_ref(v_noon_2719_);
lean_dec_ref(v_pm_2718_);
lean_dec_ref(v_am_2717_);
if (v_isShared_2737_ == 0)
{
v___x_2742_ = v___x_2736_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_pos_2733_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_err_2734_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
else
{
lean_object* v___x_2744_; 
lean_inc(v_snd_2739_);
lean_del_object(v___x_2736_);
lean_dec(v_err_2734_);
v___x_2744_ = l_Std_Internal_Parsec_String_pstring(v_noon_2719_, v_pos_2733_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_pos_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_snd_2739_);
lean_dec_ref(v_pm_2718_);
lean_dec_ref(v_am_2717_);
v_pos_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v___x_2744_, 1);
lean_dec(v_unused_2755_);
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2754_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_pos_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2754_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2749_ = 2;
v___x_2750_ = lean_box(v___x_2749_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 1, v___x_2750_);
v___x_2752_ = v___x_2747_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_pos_2745_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_pos_2756_; lean_object* v_err_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2810_; 
v_pos_2756_ = lean_ctor_get(v___x_2744_, 0);
v_err_2757_ = lean_ctor_get(v___x_2744_, 1);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2759_ = v___x_2744_;
v_isShared_2760_ = v_isSharedCheck_2810_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_err_2757_);
lean_inc(v_pos_2756_);
lean_dec(v___x_2744_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2810_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v_snd_2761_; uint8_t v_decide_2762_; 
v_snd_2761_ = lean_ctor_get(v_pos_2756_, 1);
v_decide_2762_ = lean_nat_dec_eq(v_snd_2739_, v_snd_2761_);
lean_dec(v_snd_2739_);
if (v_decide_2762_ == 0)
{
lean_object* v___x_2764_; 
lean_dec_ref(v_pm_2718_);
lean_dec_ref(v_am_2717_);
if (v_isShared_2760_ == 0)
{
v___x_2764_ = v___x_2759_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_pos_2756_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_err_2757_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
else
{
lean_object* v___x_2766_; 
lean_inc(v_snd_2761_);
lean_del_object(v___x_2759_);
lean_dec(v_err_2757_);
v___x_2766_ = l_Std_Internal_Parsec_String_pstring(v_am_2717_, v_pos_2756_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_pos_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_snd_2761_);
lean_dec_ref(v_pm_2718_);
v_pos_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; 
v_unused_2777_ = lean_ctor_get(v___x_2766_, 1);
lean_dec(v_unused_2777_);
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2776_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_pos_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2776_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2771_ = 0;
v___x_2772_ = lean_box(v___x_2771_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2772_);
v___x_2774_ = v___x_2769_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_pos_2767_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
else
{
lean_object* v_pos_2778_; lean_object* v_err_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2809_; 
v_pos_2778_ = lean_ctor_get(v___x_2766_, 0);
v_err_2779_ = lean_ctor_get(v___x_2766_, 1);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2781_ = v___x_2766_;
v_isShared_2782_ = v_isSharedCheck_2809_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_err_2779_);
lean_inc(v_pos_2778_);
lean_dec(v___x_2766_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2809_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_snd_2783_; uint8_t v_decide_2784_; 
v_snd_2783_ = lean_ctor_get(v_pos_2778_, 1);
v_decide_2784_ = lean_nat_dec_eq(v_snd_2761_, v_snd_2783_);
lean_dec(v_snd_2761_);
if (v_decide_2784_ == 0)
{
lean_object* v___x_2786_; 
lean_dec_ref(v_pm_2718_);
if (v_isShared_2782_ == 0)
{
v___x_2786_ = v___x_2781_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_pos_2778_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_err_2779_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
else
{
lean_object* v___x_2788_; 
lean_del_object(v___x_2781_);
lean_dec(v_err_2779_);
v___x_2788_ = l_Std_Internal_Parsec_String_pstring(v_pm_2718_, v_pos_2778_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_pos_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2798_; 
v_pos_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; 
v_unused_2799_ = lean_ctor_get(v___x_2788_, 1);
lean_dec(v_unused_2799_);
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2798_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_pos_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2798_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = 1;
v___x_2794_ = lean_box(v___x_2793_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 1, v___x_2794_);
v___x_2796_ = v___x_2791_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_pos_2789_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
else
{
lean_object* v_pos_2800_; lean_object* v_err_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v_pos_2800_ = lean_ctor_get(v___x_2788_, 0);
v_err_2801_ = lean_ctor_get(v___x_2788_, 1);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2788_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_err_2801_);
lean_inc(v_pos_2800_);
lean_dec(v___x_2788_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_pos_2800_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_err_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(lean_object* v_arr_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v_pairs_2851_; lean_object* v___x_2852_; 
v___x_2814_ = lean_unsigned_to_nat(6u);
v___x_2815_ = lean_unsigned_to_nat(0u);
v___x_2816_ = lean_array_fget_borrowed(v_arr_2812_, v___x_2815_);
v___x_2817_ = 0;
v___x_2818_ = lean_box(v___x_2817_);
lean_inc(v___x_2816_);
v___x_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2816_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = lean_unsigned_to_nat(1u);
v___x_2821_ = lean_array_fget_borrowed(v_arr_2812_, v___x_2820_);
v___x_2822_ = 1;
v___x_2823_ = lean_box(v___x_2822_);
lean_inc(v___x_2821_);
v___x_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2821_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_unsigned_to_nat(2u);
v___x_2826_ = lean_array_fget_borrowed(v_arr_2812_, v___x_2825_);
v___x_2827_ = 2;
v___x_2828_ = lean_box(v___x_2827_);
lean_inc(v___x_2826_);
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2826_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_unsigned_to_nat(3u);
v___x_2831_ = lean_array_fget_borrowed(v_arr_2812_, v___x_2830_);
v___x_2832_ = 3;
v___x_2833_ = lean_box(v___x_2832_);
lean_inc(v___x_2831_);
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2831_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = lean_unsigned_to_nat(4u);
v___x_2836_ = lean_array_fget_borrowed(v_arr_2812_, v___x_2835_);
v___x_2837_ = 4;
v___x_2838_ = lean_box(v___x_2837_);
lean_inc(v___x_2836_);
v___x_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2836_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_unsigned_to_nat(5u);
v___x_2841_ = lean_array_fget_borrowed(v_arr_2812_, v___x_2840_);
v___x_2842_ = 5;
v___x_2843_ = lean_box(v___x_2842_);
lean_inc(v___x_2841_);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2841_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = lean_mk_empty_array_with_capacity(v___x_2814_);
v___x_2846_ = lean_array_push(v___x_2845_, v___x_2819_);
v___x_2847_ = lean_array_push(v___x_2846_, v___x_2824_);
v___x_2848_ = lean_array_push(v___x_2847_, v___x_2829_);
v___x_2849_ = lean_array_push(v___x_2848_, v___x_2834_);
v___x_2850_ = lean_array_push(v___x_2849_, v___x_2839_);
v_pairs_2851_ = lean_array_push(v___x_2850_, v___x_2844_);
v___x_2852_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2851_, v_a_2813_);
lean_dec_ref(v_pairs_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom___boxed(lean_object* v_arr_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_arr_2853_, v_a_2854_);
lean_dec_ref(v_arr_2853_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(lean_object* v_parse_2856_, lean_object* v_size_2857_, lean_object* v_acc_2858_, lean_object* v_count_2859_, lean_object* v_a_2860_){
_start:
{
uint8_t v___x_2861_; 
v___x_2861_ = lean_nat_dec_le(v_size_2857_, v_count_2859_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_inc_ref(v_parse_2856_);
v___x_2862_ = lean_apply_1(v_parse_2856_, v_a_2860_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_pos_2863_; lean_object* v_res_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_pos_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_pos_2863_);
v_res_2864_ = lean_ctor_get(v___x_2862_, 1);
lean_inc(v_res_2864_);
lean_dec_ref_known(v___x_2862_, 2);
v___x_2865_ = lean_array_push(v_acc_2858_, v_res_2864_);
v___x_2866_ = lean_unsigned_to_nat(1u);
v___x_2867_ = lean_nat_add(v_count_2859_, v___x_2866_);
lean_dec(v_count_2859_);
v_acc_2858_ = v___x_2865_;
v_count_2859_ = v___x_2867_;
v_a_2860_ = v_pos_2863_;
goto _start;
}
else
{
lean_object* v_pos_2869_; lean_object* v_err_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_count_2859_);
lean_dec_ref(v_acc_2858_);
lean_dec_ref(v_parse_2856_);
v_pos_2869_ = lean_ctor_get(v___x_2862_, 0);
v_err_2870_ = lean_ctor_get(v___x_2862_, 1);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2862_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_err_2870_);
lean_inc(v_pos_2869_);
lean_dec(v___x_2862_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_pos_2869_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_err_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_object* v___x_2878_; 
lean_dec(v_count_2859_);
lean_dec_ref(v_parse_2856_);
v___x_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2878_, 0, v_a_2860_);
lean_ctor_set(v___x_2878_, 1, v_acc_2858_);
return v___x_2878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg___boxed(lean_object* v_parse_2879_, lean_object* v_size_2880_, lean_object* v_acc_2881_, lean_object* v_count_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2879_, v_size_2880_, v_acc_2881_, v_count_2882_, v_a_2883_);
lean_dec(v_size_2880_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(lean_object* v_00_u03b1_2885_, lean_object* v_parse_2886_, lean_object* v_size_2887_, lean_object* v_acc_2888_, lean_object* v_count_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2886_, v_size_2887_, v_acc_2888_, v_count_2889_, v_a_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___boxed(lean_object* v_00_u03b1_2892_, lean_object* v_parse_2893_, lean_object* v_size_2894_, lean_object* v_acc_2895_, lean_object* v_count_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(v_00_u03b1_2892_, v_parse_2893_, v_size_2894_, v_acc_2895_, v_count_2896_, v_a_2897_);
lean_dec(v_size_2894_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(lean_object* v_parse_2901_, lean_object* v_size_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2904_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0));
v___x_2905_ = lean_unsigned_to_nat(12u);
v___x_2906_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2901_, v_size_2902_, v___x_2904_, v___x_2905_, v_a_2903_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___boxed(lean_object* v_parse_2907_, lean_object* v_size_2908_, lean_object* v_a_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2907_, v_size_2908_, v_a_2909_);
lean_dec(v_size_2908_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly(lean_object* v_00_u03b1_2911_, lean_object* v_parse_2912_, lean_object* v_size_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2912_, v_size_2913_, v_a_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___boxed(lean_object* v_00_u03b1_2916_, lean_object* v_parse_2917_, lean_object* v_size_2918_, lean_object* v_a_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly(v_00_u03b1_2916_, v_parse_2917_, v_size_2918_, v_a_2919_);
lean_dec(v_size_2918_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object* v_parse_2921_, lean_object* v_size_2922_, lean_object* v_acc_2923_, lean_object* v_count_2924_, lean_object* v_a_2925_){
_start:
{
uint8_t v___x_2926_; 
v___x_2926_ = lean_nat_dec_le(v_size_2922_, v_count_2924_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; 
lean_inc_ref(v_parse_2921_);
v___x_2927_ = lean_apply_1(v_parse_2921_, v_a_2925_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_pos_2928_; lean_object* v_res_2929_; uint32_t v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_pos_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_pos_2928_);
v_res_2929_ = lean_ctor_get(v___x_2927_, 1);
lean_inc(v_res_2929_);
lean_dec_ref_known(v___x_2927_, 2);
v___x_2930_ = lean_unbox_uint32(v_res_2929_);
lean_dec(v_res_2929_);
v___x_2931_ = lean_string_push(v_acc_2923_, v___x_2930_);
v___x_2932_ = lean_unsigned_to_nat(1u);
v___x_2933_ = lean_nat_add(v_count_2924_, v___x_2932_);
lean_dec(v_count_2924_);
v_acc_2923_ = v___x_2931_;
v_count_2924_ = v___x_2933_;
v_a_2925_ = v_pos_2928_;
goto _start;
}
else
{
lean_object* v_pos_2935_; lean_object* v_err_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v_count_2924_);
lean_dec_ref(v_acc_2923_);
lean_dec_ref(v_parse_2921_);
v_pos_2935_ = lean_ctor_get(v___x_2927_, 0);
v_err_2936_ = lean_ctor_get(v___x_2927_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2927_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_err_2936_);
lean_inc(v_pos_2935_);
lean_dec(v___x_2927_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_pos_2935_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_err_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
else
{
lean_object* v___x_2944_; 
lean_dec(v_count_2924_);
lean_dec_ref(v_parse_2921_);
v___x_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2944_, 0, v_a_2925_);
lean_ctor_set(v___x_2944_, 1, v_acc_2923_);
return v___x_2944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object* v_parse_2945_, lean_object* v_size_2946_, lean_object* v_acc_2947_, lean_object* v_count_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2945_, v_size_2946_, v_acc_2947_, v_count_2948_, v_a_2949_);
lean_dec(v_size_2946_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object* v_parse_2951_, lean_object* v_size_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_2955_ = lean_unsigned_to_nat(0u);
v___x_2956_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2951_, v_size_2952_, v___x_2954_, v___x_2955_, v_a_2953_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object* v_parse_2957_, lean_object* v_size_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v_parse_2957_, v_size_2958_, v_a_2959_);
lean_dec(v_size_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object* v_parser_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v_pos_2964_; lean_object* v_res_2965_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
lean_inc_ref(v_a_2962_);
v___x_2998_ = l_Std_Internal_Parsec_String_pstring(v___x_2997_, v_a_2962_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_pos_2999_; lean_object* v_res_3000_; lean_object* v___x_3001_; 
lean_dec_ref(v_a_2962_);
v_pos_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_pos_2999_);
v_res_3000_ = lean_ctor_get(v___x_2998_, 1);
lean_inc(v_res_3000_);
lean_dec_ref_known(v___x_2998_, 2);
v___x_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_res_3000_);
v_pos_2964_ = v_pos_2999_;
v_res_2965_ = v___x_3001_;
goto v___jp_2963_;
}
else
{
lean_object* v_pos_3002_; lean_object* v_err_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3014_; 
v_pos_3002_ = lean_ctor_get(v___x_2998_, 0);
v_err_3003_ = lean_ctor_get(v___x_2998_, 1);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3005_ = v___x_2998_;
v_isShared_3006_ = v_isSharedCheck_3014_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_err_3003_);
lean_inc(v_pos_3002_);
lean_dec(v___x_2998_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3014_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v_snd_3007_; lean_object* v_snd_3008_; uint8_t v_decide_3009_; 
v_snd_3007_ = lean_ctor_get(v_a_2962_, 1);
lean_inc(v_snd_3007_);
lean_dec_ref(v_a_2962_);
v_snd_3008_ = lean_ctor_get(v_pos_3002_, 1);
v_decide_3009_ = lean_nat_dec_eq(v_snd_3007_, v_snd_3008_);
lean_dec(v_snd_3007_);
if (v_decide_3009_ == 0)
{
lean_object* v___x_3011_; 
lean_dec_ref(v_parser_2961_);
if (v_isShared_3006_ == 0)
{
v___x_3011_ = v___x_3005_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_pos_3002_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_err_3003_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
else
{
lean_object* v___x_3013_; 
lean_del_object(v___x_3005_);
lean_dec(v_err_3003_);
v___x_3013_ = lean_box(0);
v_pos_2964_ = v_pos_3002_;
v_res_2965_ = v___x_3013_;
goto v___jp_2963_;
}
}
}
v___jp_2963_:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_apply_1(v_parser_2961_, v_pos_2964_);
if (lean_obj_tag(v___x_2966_) == 0)
{
if (lean_obj_tag(v_res_2965_) == 0)
{
lean_object* v_pos_2967_; lean_object* v_res_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2976_; 
v_pos_2967_ = lean_ctor_get(v___x_2966_, 0);
v_res_2968_ = lean_ctor_get(v___x_2966_, 1);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2970_ = v___x_2966_;
v_isShared_2971_ = v_isSharedCheck_2976_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_res_2968_);
lean_inc(v_pos_2967_);
lean_dec(v___x_2966_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2976_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2972_ = lean_nat_to_int(v_res_2968_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 1, v___x_2972_);
v___x_2974_ = v___x_2970_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_pos_2967_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
else
{
lean_object* v_pos_2977_; lean_object* v_res_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2987_; 
lean_dec_ref_known(v_res_2965_, 1);
v_pos_2977_ = lean_ctor_get(v___x_2966_, 0);
v_res_2978_ = lean_ctor_get(v___x_2966_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2980_ = v___x_2966_;
v_isShared_2981_ = v_isSharedCheck_2987_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_res_2978_);
lean_inc(v_pos_2977_);
lean_dec(v___x_2966_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2987_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2982_ = lean_nat_to_int(v_res_2978_);
v___x_2983_ = lean_int_neg(v___x_2982_);
lean_dec(v___x_2982_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 1, v___x_2983_);
v___x_2985_ = v___x_2980_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_pos_2977_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
else
{
lean_object* v_pos_2988_; lean_object* v_err_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec(v_res_2965_);
v_pos_2988_ = lean_ctor_get(v___x_2966_, 0);
v_err_2989_ = lean_ctor_get(v___x_2966_, 1);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2966_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_err_2989_);
lean_inc(v_pos_2988_);
lean_dec(v___x_2966_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_pos_2988_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_err_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___lam__0(lean_object* v___y_3015_){
_start:
{
lean_object* v_fst_3019_; lean_object* v_snd_3020_; lean_object* v___x_3021_; uint8_t v_decide_3022_; 
v_fst_3019_ = lean_ctor_get(v___y_3015_, 0);
v_snd_3020_ = lean_ctor_get(v___y_3015_, 1);
v___x_3021_ = lean_string_utf8_byte_size(v_fst_3019_);
v_decide_3022_ = lean_nat_dec_eq(v_snd_3020_, v___x_3021_);
if (v_decide_3022_ == 0)
{
uint32_t v_c_3023_; lean_object* v___x_3024_; lean_object* v_it_x27_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; uint32_t v___x_3028_; uint8_t v___x_3029_; 
v_c_3023_ = lean_string_utf8_get_fast(v_fst_3019_, v_snd_3020_);
v___x_3024_ = lean_string_utf8_next_fast(v_fst_3019_, v_snd_3020_);
lean_inc(v_fst_3019_);
v_it_x27_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3025_, 0, v_fst_3019_);
lean_ctor_set(v_it_x27_3025_, 1, v___x_3024_);
v___x_3026_ = lean_box_uint32(v_c_3023_);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v_it_x27_3025_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = 48;
v___x_3029_ = lean_uint32_dec_le(v___x_3028_, v_c_3023_);
if (v___x_3029_ == 0)
{
lean_dec_ref_known(v___x_3027_, 2);
goto v___jp_3016_;
}
else
{
uint32_t v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = 57;
v___x_3031_ = lean_uint32_dec_le(v_c_3023_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_dec_ref_known(v___x_3027_, 2);
goto v___jp_3016_;
}
else
{
lean_dec_ref(v___y_3015_);
return v___x_3027_;
}
}
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_box(0);
v___x_3033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___y_3015_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
return v___x_3033_;
}
v___jp_3016_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___y_3015_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
return v___x_3018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object* v_size_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v___f_3037_; lean_object* v___x_3038_; 
v___f_3037_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3038_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3037_, v_size_3035_, v_a_3036_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_pos_3039_; lean_object* v_res_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3051_; 
v_pos_3039_ = lean_ctor_get(v___x_3038_, 0);
v_res_3040_ = lean_ctor_get(v___x_3038_, 1);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3042_ = v___x_3038_;
v_isShared_3043_ = v_isSharedCheck_3051_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_res_3040_);
lean_inc(v_pos_3039_);
lean_dec(v___x_3038_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3051_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3044_ = lean_unsigned_to_nat(0u);
v___x_3045_ = lean_string_utf8_byte_size(v_res_3040_);
v___x_3046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3046_, 0, v_res_3040_);
lean_ctor_set(v___x_3046_, 1, v___x_3044_);
lean_ctor_set(v___x_3046_, 2, v___x_3045_);
v___x_3047_ = l_String_Slice_toNat_x21(v___x_3046_);
lean_dec_ref_known(v___x_3046_, 3);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 1, v___x_3047_);
v___x_3049_ = v___x_3042_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_pos_3039_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_object* v_pos_3052_; lean_object* v_err_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v_pos_3052_ = lean_ctor_get(v___x_3038_, 0);
v_err_3053_ = lean_ctor_get(v___x_3038_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3038_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_err_3053_);
lean_inc(v_pos_3052_);
lean_dec(v___x_3038_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_pos_3052_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_err_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed(lean_object* v_size_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3061_, v_a_3062_);
lean_dec(v_size_3061_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object* v_acc_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_fst_3066_; lean_object* v_snd_3067_; lean_object* v_pos_3069_; lean_object* v_snd_3070_; lean_object* v_err_3071_; lean_object* v___x_3077_; uint8_t v_decide_3078_; 
v_fst_3066_ = lean_ctor_get(v_a_3065_, 0);
v_snd_3067_ = lean_ctor_get(v_a_3065_, 1);
lean_inc(v_snd_3067_);
v___x_3077_ = lean_string_utf8_byte_size(v_fst_3066_);
v_decide_3078_ = lean_nat_dec_eq(v_snd_3067_, v___x_3077_);
if (v_decide_3078_ == 0)
{
uint32_t v_c_3079_; uint32_t v___x_3080_; uint8_t v___x_3081_; 
v_c_3079_ = lean_string_utf8_get_fast(v_fst_3066_, v_snd_3067_);
v___x_3080_ = 48;
v___x_3081_ = lean_uint32_dec_le(v___x_3080_, v_c_3079_);
if (v___x_3081_ == 0)
{
goto v___jp_3075_;
}
else
{
uint32_t v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = 57;
v___x_3083_ = lean_uint32_dec_le(v_c_3079_, v___x_3082_);
if (v___x_3083_ == 0)
{
goto v___jp_3075_;
}
else
{
lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3093_; 
lean_inc(v_fst_3066_);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_a_3065_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; lean_object* v_unused_3095_; 
v_unused_3094_ = lean_ctor_get(v_a_3065_, 1);
lean_dec(v_unused_3094_);
v_unused_3095_ = lean_ctor_get(v_a_3065_, 0);
lean_dec(v_unused_3095_);
v___x_3085_ = v_a_3065_;
v_isShared_3086_ = v_isSharedCheck_3093_;
goto v_resetjp_3084_;
}
else
{
lean_dec(v_a_3065_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3093_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v_it_x27_3089_; 
v___x_3087_ = lean_string_utf8_next_fast(v_fst_3066_, v_snd_3067_);
lean_dec(v_snd_3067_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 1, v___x_3087_);
v_it_x27_3089_ = v___x_3085_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_fst_3066_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3087_);
v_it_x27_3089_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_string_push(v_acc_3064_, v_c_3079_);
v_acc_3064_ = v___x_3090_;
v_a_3065_ = v_it_x27_3089_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_box(0);
lean_inc(v_snd_3067_);
v_pos_3069_ = v_a_3065_;
v_snd_3070_ = v_snd_3067_;
v_err_3071_ = v___x_3096_;
goto v___jp_3068_;
}
v___jp_3068_:
{
uint8_t v_decide_3072_; 
v_decide_3072_ = lean_nat_dec_eq(v_snd_3067_, v_snd_3070_);
lean_dec(v_snd_3070_);
lean_dec(v_snd_3067_);
if (v_decide_3072_ == 0)
{
lean_object* v___x_3073_; 
lean_dec_ref(v_acc_3064_);
lean_inc(v_err_3071_);
v___x_3073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3073_, 0, v_pos_3069_);
lean_ctor_set(v___x_3073_, 1, v_err_3071_);
return v___x_3073_;
}
else
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_pos_3069_);
lean_ctor_set(v___x_3074_, 1, v_acc_3064_);
return v___x_3074_;
}
}
v___jp_3075_:
{
lean_object* v___x_3076_; 
v___x_3076_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3067_);
v_pos_3069_ = v_a_3065_;
v_snd_3070_ = v_snd_3067_;
v_err_3071_ = v___x_3076_;
goto v___jp_3068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object* v_size_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v_pos_3100_; lean_object* v_res_3101_; lean_object* v___y_3108_; lean_object* v___f_3120_; lean_object* v___x_3121_; 
v___f_3120_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3121_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3120_, v_size_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_pos_3122_; lean_object* v_res_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_pos_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_pos_3122_);
v_res_3123_ = lean_ctor_get(v___x_3121_, 1);
lean_inc(v_res_3123_);
lean_dec_ref_known(v___x_3121_, 2);
v___x_3124_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3125_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(v___x_3124_, v_pos_3122_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_pos_3126_; lean_object* v_res_3127_; lean_object* v___x_3128_; 
v_pos_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_pos_3126_);
v_res_3127_ = lean_ctor_get(v___x_3125_, 1);
lean_inc(v_res_3127_);
lean_dec_ref_known(v___x_3125_, 2);
v___x_3128_ = lean_string_append(v_res_3123_, v_res_3127_);
lean_dec(v_res_3127_);
v_pos_3100_ = v_pos_3126_;
v_res_3101_ = v___x_3128_;
goto v___jp_3099_;
}
else
{
lean_dec(v_res_3123_);
v___y_3108_ = v___x_3125_;
goto v___jp_3107_;
}
}
else
{
v___y_3108_ = v___x_3121_;
goto v___jp_3107_;
}
v___jp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = lean_string_utf8_byte_size(v_res_3101_);
v___x_3104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3104_, 0, v_res_3101_);
lean_ctor_set(v___x_3104_, 1, v___x_3102_);
lean_ctor_set(v___x_3104_, 2, v___x_3103_);
v___x_3105_ = l_String_Slice_toNat_x21(v___x_3104_);
lean_dec_ref_known(v___x_3104_, 3);
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v_pos_3100_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
return v___x_3106_;
}
v___jp_3107_:
{
if (lean_obj_tag(v___y_3108_) == 0)
{
lean_object* v_pos_3109_; lean_object* v_res_3110_; 
v_pos_3109_ = lean_ctor_get(v___y_3108_, 0);
lean_inc(v_pos_3109_);
v_res_3110_ = lean_ctor_get(v___y_3108_, 1);
lean_inc(v_res_3110_);
lean_dec_ref_known(v___y_3108_, 2);
v_pos_3100_ = v_pos_3109_;
v_res_3101_ = v_res_3110_;
goto v___jp_3099_;
}
else
{
lean_object* v_pos_3111_; lean_object* v_err_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
v_pos_3111_ = lean_ctor_get(v___y_3108_, 0);
v_err_3112_ = lean_ctor_get(v___y_3108_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___y_3108_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___y_3108_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_err_3112_);
lean_inc(v_pos_3111_);
lean_dec(v___y_3108_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_pos_3111_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_err_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object* v_size_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v_size_3129_, v_a_3130_);
lean_dec(v_size_3129_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object* v_size_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v___x_3134_; uint8_t v___x_3135_; 
v___x_3134_ = lean_unsigned_to_nat(1u);
v___x_3135_ = lean_nat_dec_eq(v_size_3132_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
v___x_3136_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3132_, v_a_3133_);
return v___x_3136_;
}
else
{
lean_object* v___x_3137_; 
v___x_3137_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3134_, v_a_3133_);
return v___x_3137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed(lean_object* v_size_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_size_3138_, v_a_3139_);
lean_dec(v_size_3138_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object* v_size_3141_, lean_object* v_pad_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v_pos_3145_; lean_object* v_res_3146_; lean_object* v___f_3152_; lean_object* v___x_3153_; 
v___f_3152_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3153_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3152_, v_size_3141_, v_a_3143_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_pos_3154_; lean_object* v_res_3155_; uint32_t v___x_3156_; lean_object* v___x_3157_; 
v_pos_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_pos_3154_);
v_res_3155_ = lean_ctor_get(v___x_3153_, 1);
lean_inc(v_res_3155_);
lean_dec_ref_known(v___x_3153_, 2);
v___x_3156_ = 48;
v___x_3157_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_pad_3142_, v___x_3156_, v_res_3155_);
v_pos_3145_ = v_pos_3154_;
v_res_3146_ = v___x_3157_;
goto v___jp_3144_;
}
else
{
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_pos_3158_; lean_object* v_res_3159_; 
v_pos_3158_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_pos_3158_);
v_res_3159_ = lean_ctor_get(v___x_3153_, 1);
lean_inc(v_res_3159_);
lean_dec_ref_known(v___x_3153_, 2);
v_pos_3145_ = v_pos_3158_;
v_res_3146_ = v_res_3159_;
goto v___jp_3144_;
}
else
{
lean_object* v_pos_3160_; lean_object* v_err_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
v_pos_3160_ = lean_ctor_get(v___x_3153_, 0);
v_err_3161_ = lean_ctor_get(v___x_3153_, 1);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3153_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_err_3161_);
lean_inc(v_pos_3160_);
lean_dec(v___x_3153_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_pos_3160_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v_err_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
v___jp_3144_:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3147_ = lean_unsigned_to_nat(0u);
v___x_3148_ = lean_string_utf8_byte_size(v_res_3146_);
v___x_3149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3149_, 0, v_res_3146_);
lean_ctor_set(v___x_3149_, 1, v___x_3147_);
lean_ctor_set(v___x_3149_, 2, v___x_3148_);
v___x_3150_ = l_String_Slice_toNat_x21(v___x_3149_);
lean_dec_ref_known(v___x_3149_, 3);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v_pos_3145_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object* v_size_3169_, lean_object* v_pad_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(v_size_3169_, v_pad_3170_, v_a_3171_);
lean_dec(v_pad_3170_);
lean_dec(v_size_3169_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object* v_acc_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v_pos_3176_; uint32_t v_res_3177_; lean_object* v_fst_3180_; lean_object* v_snd_3181_; lean_object* v_pos_3183_; lean_object* v_snd_3184_; lean_object* v_err_3185_; lean_object* v___x_3189_; uint8_t v_decide_3190_; 
v_fst_3180_ = lean_ctor_get(v_a_3174_, 0);
v_snd_3181_ = lean_ctor_get(v_a_3174_, 1);
lean_inc(v_snd_3181_);
v___x_3189_ = lean_string_utf8_byte_size(v_fst_3180_);
v_decide_3190_ = lean_nat_dec_eq(v_snd_3181_, v___x_3189_);
if (v_decide_3190_ == 0)
{
uint32_t v_c_3191_; lean_object* v___x_3192_; lean_object* v_it_x27_3193_; uint32_t v___x_3212_; uint8_t v___x_3213_; 
v_c_3191_ = lean_string_utf8_get_fast(v_fst_3180_, v_snd_3181_);
v___x_3192_ = lean_string_utf8_next_fast(v_fst_3180_, v_snd_3181_);
lean_inc(v_fst_3180_);
v_it_x27_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3193_, 0, v_fst_3180_);
lean_ctor_set(v_it_x27_3193_, 1, v___x_3192_);
v___x_3212_ = 65;
v___x_3213_ = lean_uint32_dec_le(v___x_3212_, v_c_3191_);
if (v___x_3213_ == 0)
{
goto v___jp_3207_;
}
else
{
uint32_t v___x_3214_; uint8_t v___x_3215_; 
v___x_3214_ = 90;
v___x_3215_ = lean_uint32_dec_le(v_c_3191_, v___x_3214_);
if (v___x_3215_ == 0)
{
goto v___jp_3207_;
}
else
{
lean_dec(v_snd_3181_);
lean_dec_ref(v_a_3174_);
v_pos_3176_ = v_it_x27_3193_;
v_res_3177_ = v_c_3191_;
goto v___jp_3175_;
}
}
v___jp_3194_:
{
uint32_t v___x_3195_; uint8_t v___x_3196_; 
v___x_3195_ = 95;
v___x_3196_ = lean_uint32_dec_eq(v_c_3191_, v___x_3195_);
if (v___x_3196_ == 0)
{
uint32_t v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = 45;
v___x_3198_ = lean_uint32_dec_eq(v_c_3191_, v___x_3197_);
if (v___x_3198_ == 0)
{
uint32_t v___x_3199_; uint8_t v___x_3200_; 
v___x_3199_ = 47;
v___x_3200_ = lean_uint32_dec_eq(v_c_3191_, v___x_3199_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; 
lean_dec_ref_known(v_it_x27_3193_, 2);
v___x_3201_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3181_);
v_pos_3183_ = v_a_3174_;
v_snd_3184_ = v_snd_3181_;
v_err_3185_ = v___x_3201_;
goto v___jp_3182_;
}
else
{
lean_dec(v_snd_3181_);
lean_dec_ref(v_a_3174_);
v_pos_3176_ = v_it_x27_3193_;
v_res_3177_ = v_c_3191_;
goto v___jp_3175_;
}
}
else
{
lean_dec(v_snd_3181_);
lean_dec_ref(v_a_3174_);
v_pos_3176_ = v_it_x27_3193_;
v_res_3177_ = v_c_3191_;
goto v___jp_3175_;
}
}
else
{
lean_dec(v_snd_3181_);
lean_dec_ref(v_a_3174_);
v_pos_3176_ = v_it_x27_3193_;
v_res_3177_ = v_c_3191_;
goto v___jp_3175_;
}
}
v___jp_3202_:
{
uint32_t v___x_3203_; uint8_t v___x_3204_; 
v___x_3203_ = 48;
v___x_3204_ = lean_uint32_dec_le(v___x_3203_, v_c_3191_);
if (v___x_3204_ == 0)
{
goto v___jp_3194_;
}
else
{
uint32_t v___x_3205_; uint8_t v___x_3206_; 
v___x_3205_ = 57;
v___x_3206_ = lean_uint32_dec_le(v_c_3191_, v___x_3205_);
if (v___x_3206_ == 0)
{
goto v___jp_3194_;
}
else
{
lean_dec(v_snd_3181_);
lean_dec_ref(v_a_3174_);
v_pos_3176_ = v_it_x27_3193_;
v_res_3177_ = v_c_3191_;
goto v___jp_3175_;
}
}
}
v___jp_3207_:
{
uint32_t v___x_3208_; uint8_t v___x_3209_; 
v___x_3208_ = 97;
v___x_3209_ = lean_uint32_dec_le(v___x_3208_, v_c_3191_);
if (v___x_3209_ == 0)
{
goto v___jp_3202_;
}
else
{
uint32_t v___x_3210_; uint8_t v___x_3211_; 
v___x_3210_ = 122;
v___x_3211_ = lean_uint32_dec_le(v_c_3191_, v___x_3210_);
if (v___x_3211_ == 0)
{
goto v___jp_3202_;
}
else
{
lean_dec(v_snd_3181_);
lean_dec_ref(v_a_3174_);
v_pos_3176_ = v_it_x27_3193_;
v_res_3177_ = v_c_3191_;
goto v___jp_3175_;
}
}
}
}
else
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_box(0);
lean_inc(v_snd_3181_);
v_pos_3183_ = v_a_3174_;
v_snd_3184_ = v_snd_3181_;
v_err_3185_ = v___x_3216_;
goto v___jp_3182_;
}
v___jp_3175_:
{
lean_object* v___x_3178_; 
v___x_3178_ = lean_string_push(v_acc_3173_, v_res_3177_);
v_acc_3173_ = v___x_3178_;
v_a_3174_ = v_pos_3176_;
goto _start;
}
v___jp_3182_:
{
uint8_t v_decide_3186_; 
v_decide_3186_ = lean_nat_dec_eq(v_snd_3181_, v_snd_3184_);
lean_dec(v_snd_3184_);
lean_dec(v_snd_3181_);
if (v_decide_3186_ == 0)
{
lean_object* v___x_3187_; 
lean_dec_ref(v_acc_3173_);
lean_inc(v_err_3185_);
v___x_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3187_, 0, v_pos_3183_);
lean_ctor_set(v___x_3187_, 1, v_err_3185_);
return v___x_3187_;
}
else
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_pos_3183_);
lean_ctor_set(v___x_3188_, 1, v_acc_3173_);
return v___x_3188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object* v_acc_3217_, lean_object* v_a_3218_){
_start:
{
lean_object* v_pos_3220_; uint32_t v_res_3221_; lean_object* v_fst_3224_; lean_object* v_snd_3225_; lean_object* v_pos_3227_; lean_object* v_snd_3228_; lean_object* v_err_3229_; lean_object* v___x_3233_; uint8_t v_decide_3234_; 
v_fst_3224_ = lean_ctor_get(v_a_3218_, 0);
v_snd_3225_ = lean_ctor_get(v_a_3218_, 1);
lean_inc(v_snd_3225_);
v___x_3233_ = lean_string_utf8_byte_size(v_fst_3224_);
v_decide_3234_ = lean_nat_dec_eq(v_snd_3225_, v___x_3233_);
if (v_decide_3234_ == 0)
{
uint32_t v_c_3235_; lean_object* v___x_3236_; lean_object* v_it_x27_3237_; uint32_t v___x_3256_; uint8_t v___x_3257_; 
v_c_3235_ = lean_string_utf8_get_fast(v_fst_3224_, v_snd_3225_);
v___x_3236_ = lean_string_utf8_next_fast(v_fst_3224_, v_snd_3225_);
lean_inc(v_fst_3224_);
v_it_x27_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3237_, 0, v_fst_3224_);
lean_ctor_set(v_it_x27_3237_, 1, v___x_3236_);
v___x_3256_ = 65;
v___x_3257_ = lean_uint32_dec_le(v___x_3256_, v_c_3235_);
if (v___x_3257_ == 0)
{
goto v___jp_3251_;
}
else
{
uint32_t v___x_3258_; uint8_t v___x_3259_; 
v___x_3258_ = 90;
v___x_3259_ = lean_uint32_dec_le(v_c_3235_, v___x_3258_);
if (v___x_3259_ == 0)
{
goto v___jp_3251_;
}
else
{
lean_dec(v_snd_3225_);
lean_dec_ref(v_a_3218_);
v_pos_3220_ = v_it_x27_3237_;
v_res_3221_ = v_c_3235_;
goto v___jp_3219_;
}
}
v___jp_3238_:
{
uint32_t v___x_3239_; uint8_t v___x_3240_; 
v___x_3239_ = 95;
v___x_3240_ = lean_uint32_dec_eq(v_c_3235_, v___x_3239_);
if (v___x_3240_ == 0)
{
uint32_t v___x_3241_; uint8_t v___x_3242_; 
v___x_3241_ = 45;
v___x_3242_ = lean_uint32_dec_eq(v_c_3235_, v___x_3241_);
if (v___x_3242_ == 0)
{
uint32_t v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = 47;
v___x_3244_ = lean_uint32_dec_eq(v_c_3235_, v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
lean_dec_ref_known(v_it_x27_3237_, 2);
v___x_3245_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3225_);
v_pos_3227_ = v_a_3218_;
v_snd_3228_ = v_snd_3225_;
v_err_3229_ = v___x_3245_;
goto v___jp_3226_;
}
else
{
lean_dec(v_snd_3225_);
lean_dec_ref(v_a_3218_);
v_pos_3220_ = v_it_x27_3237_;
v_res_3221_ = v_c_3235_;
goto v___jp_3219_;
}
}
else
{
lean_dec(v_snd_3225_);
lean_dec_ref(v_a_3218_);
v_pos_3220_ = v_it_x27_3237_;
v_res_3221_ = v_c_3235_;
goto v___jp_3219_;
}
}
else
{
lean_dec(v_snd_3225_);
lean_dec_ref(v_a_3218_);
v_pos_3220_ = v_it_x27_3237_;
v_res_3221_ = v_c_3235_;
goto v___jp_3219_;
}
}
v___jp_3246_:
{
uint32_t v___x_3247_; uint8_t v___x_3248_; 
v___x_3247_ = 48;
v___x_3248_ = lean_uint32_dec_le(v___x_3247_, v_c_3235_);
if (v___x_3248_ == 0)
{
goto v___jp_3238_;
}
else
{
uint32_t v___x_3249_; uint8_t v___x_3250_; 
v___x_3249_ = 57;
v___x_3250_ = lean_uint32_dec_le(v_c_3235_, v___x_3249_);
if (v___x_3250_ == 0)
{
goto v___jp_3238_;
}
else
{
lean_dec(v_snd_3225_);
lean_dec_ref(v_a_3218_);
v_pos_3220_ = v_it_x27_3237_;
v_res_3221_ = v_c_3235_;
goto v___jp_3219_;
}
}
}
v___jp_3251_:
{
uint32_t v___x_3252_; uint8_t v___x_3253_; 
v___x_3252_ = 97;
v___x_3253_ = lean_uint32_dec_le(v___x_3252_, v_c_3235_);
if (v___x_3253_ == 0)
{
goto v___jp_3246_;
}
else
{
uint32_t v___x_3254_; uint8_t v___x_3255_; 
v___x_3254_ = 122;
v___x_3255_ = lean_uint32_dec_le(v_c_3235_, v___x_3254_);
if (v___x_3255_ == 0)
{
goto v___jp_3246_;
}
else
{
lean_dec(v_snd_3225_);
lean_dec_ref(v_a_3218_);
v_pos_3220_ = v_it_x27_3237_;
v_res_3221_ = v_c_3235_;
goto v___jp_3219_;
}
}
}
}
else
{
lean_object* v___x_3260_; 
v___x_3260_ = lean_box(0);
lean_inc(v_snd_3225_);
v_pos_3227_ = v_a_3218_;
v_snd_3228_ = v_snd_3225_;
v_err_3229_ = v___x_3260_;
goto v___jp_3226_;
}
v___jp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_string_push(v_acc_3217_, v_res_3221_);
v___x_3223_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(v___x_3222_, v_pos_3220_);
return v___x_3223_;
}
v___jp_3226_:
{
uint8_t v_decide_3230_; 
v_decide_3230_ = lean_nat_dec_eq(v_snd_3225_, v_snd_3228_);
lean_dec(v_snd_3228_);
lean_dec(v_snd_3225_);
if (v_decide_3230_ == 0)
{
lean_object* v___x_3231_; 
lean_dec_ref(v_acc_3217_);
lean_inc(v_err_3229_);
v___x_3231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3231_, 0, v_pos_3227_);
lean_ctor_set(v___x_3231_, 1, v_err_3229_);
return v___x_3231_;
}
else
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v_pos_3227_);
lean_ctor_set(v___x_3232_, 1, v_acc_3217_);
return v___x_3232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object* v_a_3261_){
_start:
{
lean_object* v_fst_3262_; lean_object* v_snd_3263_; lean_object* v___x_3264_; uint8_t v_decide_3265_; 
v_fst_3262_ = lean_ctor_get(v_a_3261_, 0);
v_snd_3263_ = lean_ctor_get(v_a_3261_, 1);
v___x_3264_ = lean_string_utf8_byte_size(v_fst_3262_);
v_decide_3265_ = lean_nat_dec_eq(v_snd_3263_, v___x_3264_);
if (v_decide_3265_ == 0)
{
uint32_t v_c_3266_; lean_object* v___x_3267_; uint32_t v___x_3292_; uint8_t v___x_3293_; 
v_c_3266_ = lean_string_utf8_get_fast(v_fst_3262_, v_snd_3263_);
v___x_3267_ = lean_string_utf8_next_fast(v_fst_3262_, v_snd_3263_);
v___x_3292_ = 65;
v___x_3293_ = lean_uint32_dec_le(v___x_3292_, v_c_3266_);
if (v___x_3293_ == 0)
{
goto v___jp_3287_;
}
else
{
uint32_t v___x_3294_; uint8_t v___x_3295_; 
v___x_3294_ = 90;
v___x_3295_ = lean_uint32_dec_le(v_c_3266_, v___x_3294_);
if (v___x_3295_ == 0)
{
goto v___jp_3287_;
}
else
{
lean_inc(v_fst_3262_);
lean_dec_ref(v_a_3261_);
goto v___jp_3268_;
}
}
v___jp_3268_:
{
lean_object* v_it_x27_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_it_x27_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3269_, 0, v_fst_3262_);
lean_ctor_set(v_it_x27_3269_, 1, v___x_3267_);
v___x_3270_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3271_ = lean_string_push(v___x_3270_, v_c_3266_);
v___x_3272_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(v___x_3271_, v_it_x27_3269_);
return v___x_3272_;
}
v___jp_3273_:
{
uint32_t v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = 95;
v___x_3275_ = lean_uint32_dec_eq(v_c_3266_, v___x_3274_);
if (v___x_3275_ == 0)
{
uint32_t v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = 45;
v___x_3277_ = lean_uint32_dec_eq(v_c_3266_, v___x_3276_);
if (v___x_3277_ == 0)
{
uint32_t v___x_3278_; uint8_t v___x_3279_; 
v___x_3278_ = 47;
v___x_3279_ = lean_uint32_dec_eq(v_c_3266_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3281_, 0, v_a_3261_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
return v___x_3281_;
}
else
{
lean_inc(v_fst_3262_);
lean_dec_ref(v_a_3261_);
goto v___jp_3268_;
}
}
else
{
lean_inc(v_fst_3262_);
lean_dec_ref(v_a_3261_);
goto v___jp_3268_;
}
}
else
{
lean_inc(v_fst_3262_);
lean_dec_ref(v_a_3261_);
goto v___jp_3268_;
}
}
v___jp_3282_:
{
uint32_t v___x_3283_; uint8_t v___x_3284_; 
v___x_3283_ = 48;
v___x_3284_ = lean_uint32_dec_le(v___x_3283_, v_c_3266_);
if (v___x_3284_ == 0)
{
goto v___jp_3273_;
}
else
{
uint32_t v___x_3285_; uint8_t v___x_3286_; 
v___x_3285_ = 57;
v___x_3286_ = lean_uint32_dec_le(v_c_3266_, v___x_3285_);
if (v___x_3286_ == 0)
{
goto v___jp_3273_;
}
else
{
lean_inc(v_fst_3262_);
lean_dec_ref(v_a_3261_);
goto v___jp_3268_;
}
}
}
v___jp_3287_:
{
uint32_t v___x_3288_; uint8_t v___x_3289_; 
v___x_3288_ = 97;
v___x_3289_ = lean_uint32_dec_le(v___x_3288_, v_c_3266_);
if (v___x_3289_ == 0)
{
goto v___jp_3282_;
}
else
{
uint32_t v___x_3290_; uint8_t v___x_3291_; 
v___x_3290_ = 122;
v___x_3291_ = lean_uint32_dec_le(v_c_3266_, v___x_3290_);
if (v___x_3291_ == 0)
{
goto v___jp_3282_;
}
else
{
lean_inc(v_fst_3262_);
lean_dec_ref(v_a_3261_);
goto v___jp_3268_;
}
}
}
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3297_, 0, v_a_3261_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object* v_n_3300_, lean_object* v_m_3301_, lean_object* v_parser_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_apply_1(v_parser_3302_, v_a_3303_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_pos_3305_; lean_object* v_res_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3326_; 
v_pos_3305_ = lean_ctor_get(v___x_3304_, 0);
v_res_3306_ = lean_ctor_get(v___x_3304_, 1);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3308_ = v___x_3304_;
v_isShared_3309_ = v_isSharedCheck_3326_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_res_3306_);
lean_inc(v_pos_3305_);
lean_dec(v___x_3304_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3326_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
uint8_t v___x_3322_; 
v___x_3322_ = lean_nat_dec_le(v_n_3300_, v_res_3306_);
if (v___x_3322_ == 0)
{
lean_dec(v_res_3306_);
goto v___jp_3310_;
}
else
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_nat_dec_le(v_res_3306_, v_m_3301_);
if (v___x_3323_ == 0)
{
lean_dec(v_res_3306_);
goto v___jp_3310_;
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_del_object(v___x_3308_);
lean_dec(v_m_3301_);
lean_dec(v_n_3300_);
v___x_3324_ = lean_nat_to_int(v_res_3306_);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v_pos_3305_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
return v___x_3325_;
}
}
v___jp_3310_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3311_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0));
v___x_3312_ = l_Nat_reprFast(v_n_3300_);
v___x_3313_ = lean_string_append(v___x_3311_, v___x_3312_);
lean_dec_ref(v___x_3312_);
v___x_3314_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1));
v___x_3315_ = lean_string_append(v___x_3313_, v___x_3314_);
v___x_3316_ = l_Nat_reprFast(v_m_3301_);
v___x_3317_ = lean_string_append(v___x_3315_, v___x_3316_);
lean_dec_ref(v___x_3316_);
v___x_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set_tag(v___x_3308_, 1);
lean_ctor_set(v___x_3308_, 1, v___x_3318_);
v___x_3320_ = v___x_3308_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_pos_3305_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
else
{
lean_object* v_pos_3327_; lean_object* v_err_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec(v_m_3301_);
lean_dec(v_n_3300_);
v_pos_3327_ = lean_ctor_get(v___x_3304_, 0);
v_err_3328_ = lean_ctor_get(v___x_3304_, 1);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3304_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_err_3328_);
lean_inc(v_pos_3327_);
lean_dec(v___x_3304_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_pos_3327_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_err_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object* v_a_3336_){
_start:
{
lean_object* v_fst_3340_; lean_object* v_snd_3341_; lean_object* v___x_3342_; uint8_t v_decide_3343_; 
v_fst_3340_ = lean_ctor_get(v_a_3336_, 0);
v_snd_3341_ = lean_ctor_get(v_a_3336_, 1);
v___x_3342_ = lean_string_utf8_byte_size(v_fst_3340_);
v_decide_3343_ = lean_nat_dec_eq(v_snd_3341_, v___x_3342_);
if (v_decide_3343_ == 0)
{
uint32_t v_c_3344_; uint32_t v___x_3345_; uint8_t v___x_3346_; 
v_c_3344_ = lean_string_utf8_get_fast(v_fst_3340_, v_snd_3341_);
v___x_3345_ = 48;
v___x_3346_ = lean_uint32_dec_le(v___x_3345_, v_c_3344_);
if (v___x_3346_ == 0)
{
goto v___jp_3337_;
}
else
{
uint32_t v___x_3347_; uint8_t v___x_3348_; 
v___x_3347_ = 57;
v___x_3348_ = lean_uint32_dec_le(v_c_3344_, v___x_3347_);
if (v___x_3348_ == 0)
{
goto v___jp_3337_;
}
else
{
lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3385_; 
lean_inc(v_snd_3341_);
lean_inc(v_fst_3340_);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_a_3336_);
if (v_isSharedCheck_3385_ == 0)
{
lean_object* v_unused_3386_; lean_object* v_unused_3387_; 
v_unused_3386_ = lean_ctor_get(v_a_3336_, 1);
lean_dec(v_unused_3386_);
v_unused_3387_ = lean_ctor_get(v_a_3336_, 0);
lean_dec(v_unused_3387_);
v___x_3350_ = v_a_3336_;
v_isShared_3351_ = v_isSharedCheck_3385_;
goto v_resetjp_3349_;
}
else
{
lean_dec(v_a_3336_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3385_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v_pos_3354_; lean_object* v_snd_3355_; lean_object* v_err_3356_; lean_object* v_it_x27_3364_; 
v___x_3352_ = lean_string_utf8_next_fast(v_fst_3340_, v_snd_3341_);
lean_dec(v_snd_3341_);
lean_inc(v_fst_3340_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 1, v___x_3352_);
v_it_x27_3364_ = v___x_3350_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_fst_3340_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v___x_3352_);
v_it_x27_3364_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3363_;
}
v___jp_3353_:
{
uint8_t v_decide_3357_; 
v_decide_3357_ = lean_nat_dec_eq(v___x_3352_, v_snd_3355_);
lean_dec(v_snd_3355_);
if (v_decide_3357_ == 0)
{
lean_object* v___x_3358_; 
lean_inc(v_err_3356_);
v___x_3358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3358_, 0, v_pos_3354_);
lean_ctor_set(v___x_3358_, 1, v_err_3356_);
return v___x_3358_;
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3359_ = lean_uint32_to_nat(v_c_3344_);
v___x_3360_ = lean_unsigned_to_nat(48u);
v___x_3361_ = lean_nat_sub(v___x_3359_, v___x_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3362_, 0, v_pos_3354_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
return v___x_3362_;
}
}
v_reusejp_3363_:
{
uint8_t v_decide_3369_; 
v_decide_3369_ = lean_nat_dec_eq(v___x_3352_, v___x_3342_);
if (v_decide_3369_ == 0)
{
if (v___x_3348_ == 0)
{
lean_dec(v_fst_3340_);
goto v___jp_3367_;
}
else
{
uint32_t v___x_3370_; uint8_t v___x_3371_; 
v___x_3370_ = lean_string_utf8_get_fast(v_fst_3340_, v___x_3352_);
v___x_3371_ = lean_uint32_dec_le(v___x_3345_, v___x_3370_);
if (v___x_3371_ == 0)
{
lean_dec(v_fst_3340_);
goto v___jp_3365_;
}
else
{
uint8_t v___x_3372_; 
v___x_3372_ = lean_uint32_dec_le(v___x_3370_, v___x_3347_);
if (v___x_3372_ == 0)
{
lean_dec(v_fst_3340_);
goto v___jp_3365_;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
lean_dec_ref(v_it_x27_3364_);
v___x_3373_ = lean_unsigned_to_nat(48u);
v___x_3374_ = lean_string_utf8_next_fast(v_fst_3340_, v___x_3352_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v_fst_3340_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = lean_uint32_to_nat(v_c_3344_);
v___x_3377_ = lean_nat_sub(v___x_3376_, v___x_3373_);
lean_dec(v___x_3376_);
v___x_3378_ = lean_unsigned_to_nat(10u);
v___x_3379_ = lean_nat_mul(v___x_3377_, v___x_3378_);
lean_dec(v___x_3377_);
v___x_3380_ = lean_uint32_to_nat(v___x_3370_);
v___x_3381_ = lean_nat_sub(v___x_3380_, v___x_3373_);
lean_dec(v___x_3380_);
v___x_3382_ = lean_nat_add(v___x_3379_, v___x_3381_);
lean_dec(v___x_3381_);
lean_dec(v___x_3379_);
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3375_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
return v___x_3383_;
}
}
}
}
else
{
lean_dec(v_fst_3340_);
goto v___jp_3367_;
}
v___jp_3365_:
{
lean_object* v___x_3366_; 
v___x_3366_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v_pos_3354_ = v_it_x27_3364_;
v_snd_3355_ = v___x_3352_;
v_err_3356_ = v___x_3366_;
goto v___jp_3353_;
}
v___jp_3367_:
{
lean_object* v___x_3368_; 
v___x_3368_ = lean_box(0);
v_pos_3354_ = v_it_x27_3364_;
v_snd_3355_ = v___x_3352_;
v_err_3356_ = v___x_3368_;
goto v___jp_3353_;
}
}
}
}
}
}
else
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3388_ = lean_box(0);
v___x_3389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3389_, 0, v_a_3336_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
return v___x_3389_;
}
v___jp_3337_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3339_, 0, v_a_3336_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
return v___x_3339_;
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1(void){
_start:
{
uint32_t v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = 58;
v___x_3394_ = lean_box_uint32(v___x_3393_);
return v___x_3394_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(uint8_t v_withColon_3395_, lean_object* v___y_3396_){
_start:
{
if (v_withColon_3395_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___y_3396_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
return v___x_3398_;
}
else
{
lean_object* v_fst_3399_; lean_object* v_snd_3400_; lean_object* v___x_3401_; uint8_t v_decide_3402_; 
v_fst_3399_ = lean_ctor_get(v___y_3396_, 0);
v_snd_3400_ = lean_ctor_get(v___y_3396_, 1);
v___x_3401_ = lean_string_utf8_byte_size(v_fst_3399_);
v_decide_3402_ = lean_nat_dec_eq(v_snd_3400_, v___x_3401_);
if (v_decide_3402_ == 0)
{
uint32_t v___x_3403_; uint32_t v_c_3404_; uint8_t v___x_3405_; 
v___x_3403_ = 58;
v_c_3404_ = lean_string_utf8_get_fast(v_fst_3399_, v_snd_3400_);
v___x_3405_ = lean_uint32_dec_eq(v_c_3404_, v___x_3403_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1));
v___x_3407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___y_3396_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
return v___x_3407_;
}
else
{
lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3417_; 
lean_inc(v_snd_3400_);
lean_inc(v_fst_3399_);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___y_3396_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; lean_object* v_unused_3419_; 
v_unused_3418_ = lean_ctor_get(v___y_3396_, 1);
lean_dec(v_unused_3418_);
v_unused_3419_ = lean_ctor_get(v___y_3396_, 0);
lean_dec(v_unused_3419_);
v___x_3409_ = v___y_3396_;
v_isShared_3410_ = v_isSharedCheck_3417_;
goto v_resetjp_3408_;
}
else
{
lean_dec(v___y_3396_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3417_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v_it_x27_3413_; 
v___x_3411_ = lean_string_utf8_next_fast(v_fst_3399_, v_snd_3400_);
lean_dec(v_snd_3400_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 1, v___x_3411_);
v_it_x27_3413_ = v___x_3409_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_fst_3399_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v___x_3411_);
v_it_x27_3413_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v_it_x27_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
return v___x_3415_;
}
}
}
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_box(0);
v___x_3421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___y_3396_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
return v___x_3421_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_withColon_3395_ = stack[0].m_num;
lean_object* v___y_3396_ = stack[1].m_obj;
lean_object* v_res_3422_;
v_res_3422_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(v_withColon_3395_, v___y_3396_);
stack->m_obj
 = v_res_3422_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed(lean_object* v_withColon_3423_, lean_object* v___y_3424_){
_start:
{
uint8_t v_withColon_boxed_3425_; lean_object* v_res_3426_; 
v_withColon_boxed_3425_ = lean_unbox(v_withColon_3423_);
v_res_3426_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(v_withColon_boxed_3425_, v___y_3424_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(lean_object* v_a_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = lean_nat_to_int(v_a_3427_);
v___x_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___y_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
return v___x_3430_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object* v___y_3431_, lean_object* v___f_3432_, lean_object* v_n_3433_, uint8_t v_reason_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_pos_3437_; lean_object* v_err_3438_; 
switch(v_reason_3434_)
{
case 0:
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_apply_1(v___y_3431_, v___y_3435_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_pos_3455_; lean_object* v___x_3456_; 
v_pos_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_pos_3455_);
lean_dec_ref_known(v___x_3454_, 2);
v___x_3456_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3455_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_pos_3457_; lean_object* v_res_3458_; lean_object* v___x_3459_; 
v_pos_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_pos_3457_);
v_res_3458_ = lean_ctor_get(v___x_3456_, 1);
lean_inc(v_res_3458_);
lean_dec_ref_known(v___x_3456_, 2);
v___x_3459_ = lean_apply_2(v___f_3432_, v_res_3458_, v_pos_3457_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_pos_3460_; lean_object* v_res_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3469_; 
v_pos_3460_ = lean_ctor_get(v___x_3459_, 0);
v_res_3461_ = lean_ctor_get(v___x_3459_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3463_ = v___x_3459_;
v_isShared_3464_ = v_isSharedCheck_3469_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_res_3461_);
lean_inc(v_pos_3460_);
lean_dec(v___x_3459_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3469_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3465_, 0, v_res_3461_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v___x_3465_);
v___x_3467_ = v___x_3463_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_pos_3460_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
else
{
lean_object* v_pos_3470_; lean_object* v_err_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
v_pos_3470_ = lean_ctor_get(v___x_3459_, 0);
v_err_3471_ = lean_ctor_get(v___x_3459_, 1);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3459_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_err_3471_);
lean_inc(v_pos_3470_);
lean_dec(v___x_3459_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_pos_3470_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_err_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_object* v_pos_3479_; lean_object* v_err_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec_ref(v___f_3432_);
v_pos_3479_ = lean_ctor_get(v___x_3456_, 0);
v_err_3480_ = lean_ctor_get(v___x_3456_, 1);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3456_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_err_3480_);
lean_inc(v_pos_3479_);
lean_dec(v___x_3456_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_pos_3479_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_err_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v_pos_3488_; lean_object* v_err_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec_ref(v___f_3432_);
v_pos_3488_ = lean_ctor_get(v___x_3454_, 0);
v_err_3489_ = lean_ctor_get(v___x_3454_, 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3454_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_err_3489_);
lean_inc(v_pos_3488_);
lean_dec(v___x_3454_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_pos_3488_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_err_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
case 1:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
lean_dec_ref(v___f_3432_);
lean_dec_ref(v___y_3431_);
v___x_3497_ = lean_box(0);
v___x_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___y_3435_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
return v___x_3498_;
}
default: 
{
lean_object* v___x_3499_; 
lean_inc_ref(v___y_3435_);
v___x_3499_ = lean_apply_1(v___y_3431_, v___y_3435_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_pos_3500_; lean_object* v___x_3501_; 
v_pos_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_pos_3500_);
lean_dec_ref_known(v___x_3499_, 2);
v___x_3501_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3500_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_pos_3502_; lean_object* v_res_3503_; lean_object* v___x_3504_; 
v_pos_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_pos_3502_);
v_res_3503_ = lean_ctor_get(v___x_3501_, 1);
lean_inc(v_res_3503_);
lean_dec_ref_known(v___x_3501_, 2);
v___x_3504_ = lean_apply_2(v___f_3432_, v_res_3503_, v_pos_3502_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_pos_3505_; lean_object* v_res_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref(v___y_3435_);
v_pos_3505_ = lean_ctor_get(v___x_3504_, 0);
v_res_3506_ = lean_ctor_get(v___x_3504_, 1);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3508_ = v___x_3504_;
v_isShared_3509_ = v_isSharedCheck_3514_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_res_3506_);
lean_inc(v_pos_3505_);
lean_dec(v___x_3504_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3514_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3512_; 
v___x_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3510_, 0, v_res_3506_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v___x_3510_);
v___x_3512_ = v___x_3508_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_pos_3505_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
else
{
lean_object* v_pos_3515_; lean_object* v_err_3516_; 
v_pos_3515_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_pos_3515_);
v_err_3516_ = lean_ctor_get(v___x_3504_, 1);
lean_inc(v_err_3516_);
lean_dec_ref_known(v___x_3504_, 2);
v_pos_3437_ = v_pos_3515_;
v_err_3438_ = v_err_3516_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_pos_3517_; lean_object* v_err_3518_; 
lean_dec_ref(v___f_3432_);
v_pos_3517_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_pos_3517_);
v_err_3518_ = lean_ctor_get(v___x_3501_, 1);
lean_inc(v_err_3518_);
lean_dec_ref_known(v___x_3501_, 2);
v_pos_3437_ = v_pos_3517_;
v_err_3438_ = v_err_3518_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_pos_3519_; lean_object* v_err_3520_; 
lean_dec_ref(v___f_3432_);
v_pos_3519_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_pos_3519_);
v_err_3520_ = lean_ctor_get(v___x_3499_, 1);
lean_inc(v_err_3520_);
lean_dec_ref_known(v___x_3499_, 2);
v_pos_3437_ = v_pos_3519_;
v_err_3438_ = v_err_3520_;
goto v___jp_3436_;
}
}
}
v___jp_3436_:
{
lean_object* v_snd_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3452_; 
v_snd_3439_ = lean_ctor_get(v___y_3435_, 1);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___y_3435_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; 
v_unused_3453_ = lean_ctor_get(v___y_3435_, 0);
lean_dec(v_unused_3453_);
v___x_3441_ = v___y_3435_;
v_isShared_3442_ = v_isSharedCheck_3452_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_snd_3439_);
lean_dec(v___y_3435_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3452_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v_snd_3443_; uint8_t v_decide_3444_; 
v_snd_3443_ = lean_ctor_get(v_pos_3437_, 1);
v_decide_3444_ = lean_nat_dec_eq(v_snd_3439_, v_snd_3443_);
lean_dec(v_snd_3439_);
if (v_decide_3444_ == 0)
{
lean_object* v___x_3446_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set_tag(v___x_3441_, 1);
lean_ctor_set(v___x_3441_, 1, v_err_3438_);
lean_ctor_set(v___x_3441_, 0, v_pos_3437_);
v___x_3446_ = v___x_3441_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_pos_3437_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_err_3438_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
lean_dec(v_err_3438_);
v___x_3448_ = lean_box(0);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 1, v___x_3448_);
lean_ctor_set(v___x_3441_, 0, v_pos_3437_);
v___x_3450_ = v___x_3441_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_pos_3437_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3431_ = stack[0].m_obj;
lean_object* v___f_3432_ = stack[1].m_obj;
lean_object* v_n_3433_ = stack[2].m_obj;
uint8_t v_reason_3434_ = stack[3].m_num;
lean_object* v___y_3435_ = stack[4].m_obj;
lean_object* v_res_3521_;
v_res_3521_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3431_, v___f_3432_, v_n_3433_, v_reason_3434_, v___y_3435_);
stack->m_obj
 = v_res_3521_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object* v___y_3522_, lean_object* v___f_3523_, lean_object* v_n_3524_, lean_object* v_reason_3525_, lean_object* v___y_3526_){
_start:
{
uint8_t v_reason_boxed_3527_; lean_object* v_res_3528_; 
v_reason_boxed_3527_ = lean_unbox(v_reason_3525_);
v_res_3528_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3522_, v___f_3523_, v_n_3524_, v_reason_boxed_3527_, v___y_3526_);
lean_dec_ref(v_n_3524_);
return v_res_3528_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = lean_unsigned_to_nat(3600u);
v___x_3532_ = lean_nat_to_int(v___x_3531_);
return v___x_3532_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4(void){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = lean_unsigned_to_nat(1u);
v___x_3535_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3534_);
return v___x_3535_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = lean_unsigned_to_nat(59u);
v___x_3537_ = lean_nat_to_int(v___x_3536_);
return v___x_3537_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = lean_unsigned_to_nat(23u);
v___x_3541_ = lean_nat_to_int(v___x_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_unsigned_to_nat(60u);
v___x_3543_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3542_);
return v___x_3543_;
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t v_withMinutes_3551_, uint8_t v_withSeconds_3552_, uint8_t v_withColon_3553_, lean_object* v_a_3554_){
_start:
{
lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3597_; lean_object* v_fst_3600_; lean_object* v_snd_3601_; lean_object* v___x_3602_; lean_object* v___y_3603_; lean_object* v___f_3604_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v_pos_3651_; lean_object* v_res_3652_; lean_object* v_pos_3710_; lean_object* v_fst_3711_; lean_object* v_snd_3712_; lean_object* v_err_3713_; lean_object* v___x_3726_; uint8_t v_decide_3727_; 
v_fst_3600_ = lean_ctor_get(v_a_3554_, 0);
lean_inc(v_fst_3600_);
v_snd_3601_ = lean_ctor_get(v_a_3554_, 1);
lean_inc(v_snd_3601_);
v___x_3602_ = lean_box(v_withColon_3553_);
v___y_3603_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed), 2, 1);
lean_closure_set(v___y_3603_, 0, v___x_3602_);
v___f_3604_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3));
v___x_3726_ = lean_string_utf8_byte_size(v_fst_3600_);
v_decide_3727_ = lean_nat_dec_eq(v_snd_3601_, v___x_3726_);
if (v_decide_3727_ == 0)
{
uint32_t v___x_3728_; uint32_t v_c_3729_; uint8_t v___x_3730_; 
v___x_3728_ = 43;
v_c_3729_ = lean_string_utf8_get_fast(v_fst_3600_, v_snd_3601_);
v___x_3730_ = lean_uint32_dec_eq(v_c_3729_, v___x_3728_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; 
v___x_3731_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14));
lean_inc(v_snd_3601_);
v_pos_3710_ = v_a_3554_;
v_fst_3711_ = v_fst_3600_;
v_snd_3712_ = v_snd_3601_;
v_err_3713_ = v___x_3731_;
goto v___jp_3709_;
}
else
{
lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3740_; 
v_isSharedCheck_3740_ = !lean_is_exclusive(v_a_3554_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; lean_object* v_unused_3742_; 
v_unused_3741_ = lean_ctor_get(v_a_3554_, 1);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_a_3554_, 0);
lean_dec(v_unused_3742_);
v___x_3733_ = v_a_3554_;
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
else
{
lean_dec(v_a_3554_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; lean_object* v_it_x27_3737_; 
v___x_3735_ = lean_string_utf8_next_fast(v_fst_3600_, v_snd_3601_);
lean_dec(v_snd_3601_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 1, v___x_3735_);
v_it_x27_3737_ = v___x_3733_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_fst_3600_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v___x_3735_);
v_it_x27_3737_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v_pos_3651_ = v_it_x27_3737_;
v_res_3652_ = v___x_3738_;
goto v___jp_3650_;
}
}
}
}
else
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_box(0);
lean_inc(v_snd_3601_);
v_pos_3710_ = v_a_3554_;
v_fst_3711_ = v_fst_3600_;
v_snd_3712_ = v_snd_3601_;
v_err_3713_ = v___x_3743_;
goto v___jp_3709_;
}
v___jp_3555_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3558_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0));
v___x_3559_ = l_Int_repr(v___y_3557_);
lean_dec(v___y_3557_);
v___x_3560_ = lean_string_append(v___x_3558_, v___x_3559_);
lean_dec_ref(v___x_3559_);
v___x_3561_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1));
v___x_3562_ = lean_string_append(v___x_3560_, v___x_3561_);
v___x_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
v___x_3564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___y_3556_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
return v___x_3564_;
}
v___jp_3565_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = lean_int_add(v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec(v___y_3568_);
v___x_3571_ = lean_int_mul(v___x_3570_, v___y_3567_);
lean_dec(v___x_3570_);
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___y_3566_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
return v___x_3572_;
}
v___jp_3573_:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3581_ = lean_nat_to_int(v___y_3578_);
v___x_3582_ = lean_int_mul(v___y_3580_, v___x_3581_);
lean_dec(v___x_3581_);
lean_dec(v___y_3580_);
v___x_3583_ = lean_int_add(v___y_3579_, v___x_3582_);
lean_dec(v___x_3582_);
lean_dec(v___y_3579_);
if (lean_obj_tag(v___y_3577_) == 0)
{
lean_inc(v___y_3574_);
v___y_3566_ = v___y_3575_;
v___y_3567_ = v___y_3576_;
v___y_3568_ = v___x_3583_;
v___y_3569_ = v___y_3574_;
goto v___jp_3565_;
}
else
{
lean_object* v_val_3584_; 
v_val_3584_ = lean_ctor_get(v___y_3577_, 0);
lean_inc(v_val_3584_);
lean_dec_ref_known(v___y_3577_, 1);
v___y_3566_ = v___y_3575_;
v___y_3567_ = v___y_3576_;
v___y_3568_ = v___x_3583_;
v___y_3569_ = v_val_3584_;
goto v___jp_3565_;
}
}
v___jp_3585_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2);
v___x_3594_ = lean_int_mul(v___y_3591_, v___x_3593_);
lean_dec(v___y_3591_);
if (lean_obj_tag(v___y_3587_) == 0)
{
lean_inc(v___y_3586_);
v___y_3574_ = v___y_3586_;
v___y_3575_ = v___y_3592_;
v___y_3576_ = v___y_3588_;
v___y_3577_ = v___y_3589_;
v___y_3578_ = v___y_3590_;
v___y_3579_ = v___x_3594_;
v___y_3580_ = v___y_3586_;
goto v___jp_3573_;
}
else
{
lean_object* v_val_3595_; 
v_val_3595_ = lean_ctor_get(v___y_3587_, 0);
lean_inc(v_val_3595_);
lean_dec_ref_known(v___y_3587_, 1);
v___y_3574_ = v___y_3586_;
v___y_3575_ = v___y_3592_;
v___y_3576_ = v___y_3588_;
v___y_3577_ = v___y_3589_;
v___y_3578_ = v___y_3590_;
v___y_3579_ = v___x_3594_;
v___y_3580_ = v_val_3595_;
goto v___jp_3573_;
}
}
v___jp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = lean_box(0);
v___x_3599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___y_3597_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
return v___x_3599_;
}
v___jp_3605_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4);
v___x_3613_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3603_, v___f_3604_, v___x_3612_, v_withSeconds_3552_, v___y_3611_);
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
v___y_3586_ = v___y_3606_;
v___y_3587_ = v___y_3607_;
v___y_3588_ = v___y_3608_;
v___y_3589_ = v_res_3614_;
v___y_3590_ = v___y_3610_;
v___y_3591_ = v___y_3609_;
v___y_3592_ = v_pos_3615_;
goto v___jp_3585_;
}
else
{
lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3636_; 
lean_inc(v_val_3619_);
lean_dec(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec(v___y_3607_);
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
v___x_3625_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6));
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
v___y_3586_ = v___y_3606_;
v___y_3587_ = v___y_3607_;
v___y_3588_ = v___y_3608_;
v___y_3589_ = v_res_3614_;
v___y_3590_ = v___y_3610_;
v___y_3591_ = v___y_3609_;
v___y_3592_ = v_pos_3640_;
goto v___jp_3585_;
}
}
else
{
lean_object* v_pos_3641_; lean_object* v_err_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec(v___y_3607_);
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
v___jp_3650_:
{
lean_object* v___x_3653_; 
v___x_3653_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3651_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_pos_3654_; lean_object* v_res_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; uint8_t v___x_3658_; 
v_pos_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_pos_3654_);
v_res_3655_ = lean_ctor_get(v___x_3653_, 1);
lean_inc(v_res_3655_);
lean_dec_ref_known(v___x_3653_, 2);
v___x_3656_ = lean_nat_to_int(v_res_3655_);
v___x_3657_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_3658_ = lean_int_dec_lt(v___x_3656_, v___x_3657_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; uint8_t v___x_3660_; 
v___x_3659_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8);
v___x_3660_ = lean_int_dec_lt(v___x_3659_, v___x_3656_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = lean_unsigned_to_nat(60u);
v___x_3662_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9);
lean_inc_ref(v___y_3603_);
v___x_3663_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3603_, v___f_3604_, v___x_3662_, v_withMinutes_3551_, v_pos_3654_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_res_3664_; 
v_res_3664_ = lean_ctor_get(v___x_3663_, 1);
lean_inc(v_res_3664_);
if (lean_obj_tag(v_res_3664_) == 1)
{
lean_object* v_pos_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3688_; 
v_pos_3665_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; 
v_unused_3689_ = lean_ctor_get(v___x_3663_, 1);
lean_dec(v_unused_3689_);
v___x_3667_ = v___x_3663_;
v_isShared_3668_ = v_isSharedCheck_3688_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_pos_3665_);
lean_dec(v___x_3663_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3688_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_val_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v_val_3669_ = lean_ctor_get(v_res_3664_, 0);
v___x_3670_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_3671_ = lean_int_dec_lt(v___x_3670_, v_val_3669_);
if (v___x_3671_ == 0)
{
lean_del_object(v___x_3667_);
v___y_3606_ = v___x_3657_;
v___y_3607_ = v_res_3664_;
v___y_3608_ = v_res_3652_;
v___y_3609_ = v___x_3656_;
v___y_3610_ = v___x_3661_;
v___y_3611_ = v_pos_3665_;
goto v___jp_3605_;
}
else
{
lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3686_; 
lean_inc(v_val_3669_);
lean_dec(v___x_3656_);
lean_dec_ref(v___y_3603_);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_res_3664_);
if (v_isSharedCheck_3686_ == 0)
{
lean_object* v_unused_3687_; 
v_unused_3687_ = lean_ctor_get(v_res_3664_, 0);
lean_dec(v_unused_3687_);
v___x_3673_ = v_res_3664_;
v_isShared_3674_ = v_isSharedCheck_3686_;
goto v_resetjp_3672_;
}
else
{
lean_dec(v_res_3664_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3686_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3675_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10));
v___x_3676_ = l_Int_repr(v_val_3669_);
lean_dec(v_val_3669_);
v___x_3677_ = lean_string_append(v___x_3675_, v___x_3676_);
lean_dec_ref(v___x_3676_);
v___x_3678_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3679_ = lean_string_append(v___x_3677_, v___x_3678_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3679_);
v___x_3681_ = v___x_3673_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3679_);
v___x_3681_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3683_; 
if (v_isShared_3668_ == 0)
{
lean_ctor_set_tag(v___x_3667_, 1);
lean_ctor_set(v___x_3667_, 1, v___x_3681_);
v___x_3683_ = v___x_3667_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_pos_3665_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3690_; 
v_pos_3690_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_pos_3690_);
lean_dec_ref_known(v___x_3663_, 2);
v___y_3606_ = v___x_3657_;
v___y_3607_ = v_res_3664_;
v___y_3608_ = v_res_3652_;
v___y_3609_ = v___x_3656_;
v___y_3610_ = v___x_3661_;
v___y_3611_ = v_pos_3690_;
goto v___jp_3605_;
}
}
else
{
lean_object* v_pos_3691_; lean_object* v_err_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v___x_3656_);
lean_dec_ref(v___y_3603_);
v_pos_3691_ = lean_ctor_get(v___x_3663_, 0);
v_err_3692_ = lean_ctor_get(v___x_3663_, 1);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3663_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_err_3692_);
lean_inc(v_pos_3691_);
lean_dec(v___x_3663_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_pos_3691_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_err_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
else
{
lean_dec_ref(v___y_3603_);
v___y_3556_ = v_pos_3654_;
v___y_3557_ = v___x_3656_;
goto v___jp_3555_;
}
}
else
{
lean_dec_ref(v___y_3603_);
v___y_3556_ = v_pos_3654_;
v___y_3557_ = v___x_3656_;
goto v___jp_3555_;
}
}
else
{
lean_object* v_pos_3700_; lean_object* v_err_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec_ref(v___y_3603_);
v_pos_3700_ = lean_ctor_get(v___x_3653_, 0);
v_err_3701_ = lean_ctor_get(v___x_3653_, 1);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3653_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_err_3701_);
lean_inc(v_pos_3700_);
lean_dec(v___x_3653_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_pos_3700_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_err_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
v___jp_3709_:
{
uint8_t v_decide_3714_; 
v_decide_3714_ = lean_nat_dec_eq(v_snd_3601_, v_snd_3712_);
lean_dec(v_snd_3601_);
if (v_decide_3714_ == 0)
{
lean_object* v___x_3715_; 
lean_dec(v_snd_3712_);
lean_dec(v_fst_3711_);
lean_dec_ref(v___y_3603_);
lean_inc(v_err_3713_);
v___x_3715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3715_, 0, v_pos_3710_);
lean_ctor_set(v___x_3715_, 1, v_err_3713_);
return v___x_3715_;
}
else
{
lean_object* v___x_3716_; uint8_t v_decide_3717_; 
v___x_3716_ = lean_string_utf8_byte_size(v_fst_3711_);
v_decide_3717_ = lean_nat_dec_eq(v_snd_3712_, v___x_3716_);
if (v_decide_3717_ == 0)
{
if (v_decide_3714_ == 0)
{
lean_dec(v_snd_3712_);
lean_dec(v_fst_3711_);
lean_dec_ref(v___y_3603_);
v___y_3597_ = v_pos_3710_;
goto v___jp_3596_;
}
else
{
uint32_t v___x_3718_; uint32_t v_c_3719_; uint8_t v___x_3720_; 
v___x_3718_ = 45;
v_c_3719_ = lean_string_utf8_get_fast(v_fst_3711_, v_snd_3712_);
v___x_3720_ = lean_uint32_dec_eq(v_c_3719_, v___x_3718_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
lean_dec(v_snd_3712_);
lean_dec(v_fst_3711_);
lean_dec_ref(v___y_3603_);
v___x_3721_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12));
v___x_3722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3722_, 0, v_pos_3710_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
return v___x_3722_;
}
else
{
lean_object* v___x_3723_; lean_object* v_it_x27_3724_; lean_object* v___x_3725_; 
lean_dec_ref(v_pos_3710_);
v___x_3723_ = lean_string_utf8_next_fast(v_fst_3711_, v_snd_3712_);
lean_dec(v_snd_3712_);
v_it_x27_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3724_, 0, v_fst_3711_);
lean_ctor_set(v_it_x27_3724_, 1, v___x_3723_);
v___x_3725_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v_pos_3651_ = v_it_x27_3724_;
v_res_3652_ = v___x_3725_;
goto v___jp_3650_;
}
}
}
else
{
lean_dec(v_snd_3712_);
lean_dec(v_fst_3711_);
lean_dec_ref(v___y_3603_);
v___y_3597_ = v_pos_3710_;
goto v___jp_3596_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset_0interp(lean_interpreter_value* stack)
{
uint8_t v_withMinutes_3551_ = stack[0].m_num;
uint8_t v_withSeconds_3552_ = stack[1].m_num;
uint8_t v_withColon_3553_ = stack[2].m_num;
lean_object* v_a_3554_ = stack[3].m_obj;
lean_object* v_res_3744_;
v_res_3744_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_withMinutes_3551_, v_withSeconds_3552_, v_withColon_3553_, v_a_3554_);
stack->m_obj
 = v_res_3744_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object* v_withMinutes_3745_, lean_object* v_withSeconds_3746_, lean_object* v_withColon_3747_, lean_object* v_a_3748_){
_start:
{
uint8_t v_withMinutes_boxed_3749_; uint8_t v_withSeconds_boxed_3750_; uint8_t v_withColon_boxed_3751_; lean_object* v_res_3752_; 
v_withMinutes_boxed_3749_ = lean_unbox(v_withMinutes_3745_);
v_withSeconds_boxed_3750_ = lean_unbox(v_withSeconds_3746_);
v_withColon_boxed_3751_ = lean_unbox(v_withColon_3747_);
v_res_3752_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_withMinutes_boxed_3749_, v_withSeconds_boxed_3750_, v_withColon_boxed_3751_, v_a_3748_);
return v_res_3752_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1(void){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3755_ = lean_unsigned_to_nat(2000u);
v___x_3756_ = lean_nat_to_int(v___x_3755_);
return v___x_3756_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3762_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3763_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3764_ = lean_int_sub(v___x_3763_, v___x_3762_);
return v___x_3764_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v_range_3767_; 
v___x_3765_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3766_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5);
v_range_3767_ = lean_int_add(v___x_3766_, v___x_3765_);
return v_range_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object* v_config_3770_, lean_object* v_x_3771_, lean_object* v_a_3772_){
_start:
{
lean_object* v___y_3774_; lean_object* v___y_3779_; lean_object* v___y_3784_; 
switch(lean_obj_tag(v_x_3771_))
{
case 0:
{
uint8_t v_presentation_3810_; 
v_presentation_3810_ = lean_ctor_get_uint8(v_x_3771_, 0);
lean_dec_ref_known(v_x_3771_, 0);
switch(v_presentation_3810_)
{
case 1:
{
lean_object* v_dateformat_3811_; lean_object* v_symbols_3812_; lean_object* v___x_3813_; 
v_dateformat_3811_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3811_);
lean_dec_ref(v_config_3770_);
v_symbols_3812_ = lean_ctor_get(v_dateformat_3811_, 1);
lean_inc_ref(v_symbols_3812_);
lean_dec_ref(v_dateformat_3811_);
v___x_3813_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(v_symbols_3812_, v_a_3772_);
return v___x_3813_;
}
case 2:
{
lean_object* v_dateformat_3814_; lean_object* v_symbols_3815_; lean_object* v___x_3816_; 
v_dateformat_3814_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3814_);
lean_dec_ref(v_config_3770_);
v_symbols_3815_ = lean_ctor_get(v_dateformat_3814_, 1);
lean_inc_ref(v_symbols_3815_);
lean_dec_ref(v_dateformat_3814_);
v___x_3816_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(v_symbols_3815_, v_a_3772_);
return v___x_3816_;
}
default: 
{
lean_object* v_dateformat_3817_; lean_object* v_symbols_3818_; lean_object* v___x_3819_; 
v_dateformat_3817_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3817_);
lean_dec_ref(v_config_3770_);
v_symbols_3818_ = lean_ctor_get(v_dateformat_3817_, 1);
lean_inc_ref(v_symbols_3818_);
lean_dec_ref(v_dateformat_3817_);
v___x_3819_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(v_symbols_3818_, v_a_3772_);
return v___x_3819_;
}
}
}
case 1:
{
lean_object* v_presentation_3820_; 
lean_dec_ref(v_config_3770_);
v_presentation_3820_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_3820_);
lean_dec_ref_known(v_x_3771_, 1);
switch(lean_obj_tag(v_presentation_3820_))
{
case 0:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_3822_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3821_, v_a_3772_);
return v___x_3822_;
}
case 1:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = lean_unsigned_to_nat(2u);
v___x_3824_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3823_, v_a_3772_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_pos_3825_; lean_object* v_res_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3836_; 
v_pos_3825_ = lean_ctor_get(v___x_3824_, 0);
v_res_3826_ = lean_ctor_get(v___x_3824_, 1);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3828_ = v___x_3824_;
v_isShared_3829_ = v_isSharedCheck_3836_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_res_3826_);
lean_inc(v_pos_3825_);
lean_dec(v___x_3824_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3836_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3830_ = lean_nat_to_int(v_res_3826_);
v___x_3831_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3832_ = lean_int_add(v___x_3831_, v___x_3830_);
lean_dec(v___x_3830_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 1, v___x_3832_);
v___x_3834_ = v___x_3828_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_pos_3825_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
else
{
lean_object* v_pos_3837_; lean_object* v_err_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
v_pos_3837_ = lean_ctor_get(v___x_3824_, 0);
v_err_3838_ = lean_ctor_get(v___x_3824_, 1);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3824_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_err_3838_);
lean_inc(v_pos_3837_);
lean_dec(v___x_3824_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_pos_3837_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v_err_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
case 2:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_3847_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3846_, v_a_3772_);
return v___x_3847_;
}
default: 
{
lean_object* v_num_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v_num_3848_ = lean_ctor_get(v_presentation_3820_, 0);
lean_inc(v_num_3848_);
lean_dec_ref_known(v_presentation_3820_, 1);
v___x_3849_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_3849_, 0, v_num_3848_);
v___x_3850_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3849_, v_a_3772_);
return v___x_3850_;
}
}
}
case 2:
{
lean_object* v_presentation_3851_; 
lean_dec_ref(v_config_3770_);
v_presentation_3851_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_3851_);
lean_dec_ref_known(v_x_3771_, 1);
switch(lean_obj_tag(v_presentation_3851_))
{
case 0:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_unsigned_to_nat(1u);
v___x_3853_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3852_, v_a_3772_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_pos_3854_; lean_object* v_res_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3863_; 
v_pos_3854_ = lean_ctor_get(v___x_3853_, 0);
v_res_3855_ = lean_ctor_get(v___x_3853_, 1);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3857_ = v___x_3853_;
v_isShared_3858_ = v_isSharedCheck_3863_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_res_3855_);
lean_inc(v_pos_3854_);
lean_dec(v___x_3853_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3863_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3859_ = lean_nat_to_int(v_res_3855_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 1, v___x_3859_);
v___x_3861_ = v___x_3857_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_pos_3854_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
else
{
lean_object* v_pos_3864_; lean_object* v_err_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
v_pos_3864_ = lean_ctor_get(v___x_3853_, 0);
v_err_3865_ = lean_ctor_get(v___x_3853_, 1);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3853_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_err_3865_);
lean_inc(v_pos_3864_);
lean_dec(v___x_3853_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_pos_3864_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_err_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
case 1:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = lean_unsigned_to_nat(2u);
v___x_3874_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3873_, v_a_3772_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_pos_3875_; lean_object* v_res_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3886_; 
v_pos_3875_ = lean_ctor_get(v___x_3874_, 0);
v_res_3876_ = lean_ctor_get(v___x_3874_, 1);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3878_ = v___x_3874_;
v_isShared_3879_ = v_isSharedCheck_3886_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_res_3876_);
lean_inc(v_pos_3875_);
lean_dec(v___x_3874_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3886_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3880_ = lean_nat_to_int(v_res_3876_);
v___x_3881_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3882_ = lean_int_add(v___x_3881_, v___x_3880_);
lean_dec(v___x_3880_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 1, v___x_3882_);
v___x_3884_ = v___x_3878_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_pos_3875_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
else
{
lean_object* v_pos_3887_; lean_object* v_err_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
v_pos_3887_ = lean_ctor_get(v___x_3874_, 0);
v_err_3888_ = lean_ctor_get(v___x_3874_, 1);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3874_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_err_3888_);
lean_inc(v_pos_3887_);
lean_dec(v___x_3874_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_pos_3887_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_err_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
case 2:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = lean_unsigned_to_nat(4u);
v___x_3897_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3896_, v_a_3772_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_pos_3898_; lean_object* v_res_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3907_; 
v_pos_3898_ = lean_ctor_get(v___x_3897_, 0);
v_res_3899_ = lean_ctor_get(v___x_3897_, 1);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3901_ = v___x_3897_;
v_isShared_3902_ = v_isSharedCheck_3907_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_res_3899_);
lean_inc(v_pos_3898_);
lean_dec(v___x_3897_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3907_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = lean_nat_to_int(v_res_3899_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 1, v___x_3903_);
v___x_3905_ = v___x_3901_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_pos_3898_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
else
{
lean_object* v_pos_3908_; lean_object* v_err_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
v_pos_3908_ = lean_ctor_get(v___x_3897_, 0);
v_err_3909_ = lean_ctor_get(v___x_3897_, 1);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3897_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_err_3909_);
lean_inc(v_pos_3908_);
lean_dec(v___x_3897_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_pos_3908_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_err_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
default: 
{
lean_object* v_num_3917_; lean_object* v___x_3918_; 
v_num_3917_ = lean_ctor_get(v_presentation_3851_, 0);
lean_inc(v_num_3917_);
lean_dec_ref_known(v_presentation_3851_, 1);
v___x_3918_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_num_3917_, v_a_3772_);
lean_dec(v_num_3917_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_pos_3919_; lean_object* v_res_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3928_; 
v_pos_3919_ = lean_ctor_get(v___x_3918_, 0);
v_res_3920_ = lean_ctor_get(v___x_3918_, 1);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3922_ = v___x_3918_;
v_isShared_3923_ = v_isSharedCheck_3928_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_res_3920_);
lean_inc(v_pos_3919_);
lean_dec(v___x_3918_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3928_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3924_; lean_object* v___x_3926_; 
v___x_3924_ = lean_nat_to_int(v_res_3920_);
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 1, v___x_3924_);
v___x_3926_ = v___x_3922_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_pos_3919_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v___x_3924_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
else
{
lean_object* v_pos_3929_; lean_object* v_err_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
v_pos_3929_ = lean_ctor_get(v___x_3918_, 0);
v_err_3930_ = lean_ctor_get(v___x_3918_, 1);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3918_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_err_3930_);
lean_inc(v_pos_3929_);
lean_dec(v___x_3918_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_pos_3929_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_err_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
}
}
case 3:
{
lean_object* v_presentation_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
lean_dec_ref(v_config_3770_);
v_presentation_3938_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_3938_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_3939_ = lean_unsigned_to_nat(1u);
v___x_3940_ = lean_unsigned_to_nat(366u);
v___x_3941_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3941_, 0, v_presentation_3938_);
v___x_3942_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3939_, v___x_3940_, v___x_3941_, v_a_3772_);
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
uint8_t v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3952_; 
v___x_3948_ = 1;
v___x_3949_ = lean_box(v___x_3948_);
v___x_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
lean_ctor_set(v___x_3950_, 1, v_res_3944_);
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
case 4:
{
lean_object* v_presentation_3964_; 
v_presentation_3964_ = lean_ctor_get(v_x_3771_, 0);
lean_inc_ref(v_presentation_3964_);
lean_dec_ref_known(v_x_3771_, 1);
if (lean_obj_tag(v_presentation_3964_) == 0)
{
lean_object* v_val_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_dec_ref(v_config_3770_);
v_val_3965_ = lean_ctor_get(v_presentation_3964_, 0);
lean_inc(v_val_3965_);
lean_dec_ref_known(v_presentation_3964_, 1);
v___x_3966_ = lean_unsigned_to_nat(1u);
v___x_3967_ = lean_unsigned_to_nat(12u);
v___x_3968_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3968_, 0, v_val_3965_);
v___x_3969_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3966_, v___x_3967_, v___x_3968_, v_a_3772_);
return v___x_3969_;
}
else
{
lean_object* v_val_3970_; uint8_t v___x_3971_; 
v_val_3970_ = lean_ctor_get(v_presentation_3964_, 0);
lean_inc(v_val_3970_);
lean_dec_ref_known(v_presentation_3964_, 1);
v___x_3971_ = lean_unbox(v_val_3970_);
lean_dec(v_val_3970_);
switch(v___x_3971_)
{
case 1:
{
lean_object* v_dateformat_3972_; lean_object* v_symbols_3973_; lean_object* v___x_3974_; 
v_dateformat_3972_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3972_);
lean_dec_ref(v_config_3770_);
v_symbols_3973_ = lean_ctor_get(v_dateformat_3972_, 1);
lean_inc_ref(v_symbols_3973_);
lean_dec_ref(v_dateformat_3972_);
v___x_3974_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_3973_, v_a_3772_);
return v___x_3974_;
}
case 2:
{
lean_object* v_dateformat_3975_; lean_object* v_symbols_3976_; lean_object* v___x_3977_; 
v_dateformat_3975_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3975_);
lean_dec_ref(v_config_3770_);
v_symbols_3976_ = lean_ctor_get(v_dateformat_3975_, 1);
lean_inc_ref(v_symbols_3976_);
lean_dec_ref(v_dateformat_3975_);
v___x_3977_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_3976_, v_a_3772_);
return v___x_3977_;
}
default: 
{
lean_object* v_dateformat_3978_; lean_object* v_symbols_3979_; lean_object* v___x_3980_; 
v_dateformat_3978_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3978_);
lean_dec_ref(v_config_3770_);
v_symbols_3979_ = lean_ctor_get(v_dateformat_3978_, 1);
lean_inc_ref(v_symbols_3979_);
lean_dec_ref(v_dateformat_3978_);
v___x_3980_ = l_Std_Time_parseMonthShort(v_symbols_3979_, v_a_3772_);
return v___x_3980_;
}
}
}
}
case 5:
{
lean_object* v_presentation_3981_; 
v_presentation_3981_ = lean_ctor_get(v_x_3771_, 0);
lean_inc_ref(v_presentation_3981_);
lean_dec_ref_known(v_x_3771_, 1);
if (lean_obj_tag(v_presentation_3981_) == 0)
{
lean_object* v_val_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
lean_dec_ref(v_config_3770_);
v_val_3982_ = lean_ctor_get(v_presentation_3981_, 0);
lean_inc(v_val_3982_);
lean_dec_ref_known(v_presentation_3981_, 1);
v___x_3983_ = lean_unsigned_to_nat(1u);
v___x_3984_ = lean_unsigned_to_nat(12u);
v___x_3985_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3985_, 0, v_val_3982_);
v___x_3986_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3983_, v___x_3984_, v___x_3985_, v_a_3772_);
return v___x_3986_;
}
else
{
lean_object* v_val_3987_; uint8_t v___x_3988_; 
v_val_3987_ = lean_ctor_get(v_presentation_3981_, 0);
lean_inc(v_val_3987_);
lean_dec_ref_known(v_presentation_3981_, 1);
v___x_3988_ = lean_unbox(v_val_3987_);
lean_dec(v_val_3987_);
switch(v___x_3988_)
{
case 1:
{
lean_object* v_dateformat_3989_; lean_object* v_symbols_3990_; lean_object* v___x_3991_; 
v_dateformat_3989_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3989_);
lean_dec_ref(v_config_3770_);
v_symbols_3990_ = lean_ctor_get(v_dateformat_3989_, 1);
lean_inc_ref(v_symbols_3990_);
lean_dec_ref(v_dateformat_3989_);
v___x_3991_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_3990_, v_a_3772_);
return v___x_3991_;
}
case 2:
{
lean_object* v_dateformat_3992_; lean_object* v_symbols_3993_; lean_object* v___x_3994_; 
v_dateformat_3992_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3992_);
lean_dec_ref(v_config_3770_);
v_symbols_3993_ = lean_ctor_get(v_dateformat_3992_, 1);
lean_inc_ref(v_symbols_3993_);
lean_dec_ref(v_dateformat_3992_);
v___x_3994_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_3993_, v_a_3772_);
return v___x_3994_;
}
default: 
{
lean_object* v_dateformat_3995_; lean_object* v_symbols_3996_; lean_object* v___x_3997_; 
v_dateformat_3995_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3995_);
lean_dec_ref(v_config_3770_);
v_symbols_3996_ = lean_ctor_get(v_dateformat_3995_, 1);
lean_inc_ref(v_symbols_3996_);
lean_dec_ref(v_dateformat_3995_);
v___x_3997_ = l_Std_Time_parseMonthShort(v_symbols_3996_, v_a_3772_);
return v___x_3997_;
}
}
}
}
case 6:
{
lean_object* v_presentation_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
lean_dec_ref(v_config_3770_);
v_presentation_3998_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_3998_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_3999_ = lean_unsigned_to_nat(1u);
v___x_4000_ = lean_unsigned_to_nat(31u);
v___x_4001_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4001_, 0, v_presentation_3998_);
v___x_4002_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3999_, v___x_4000_, v___x_4001_, v_a_3772_);
return v___x_4002_;
}
case 7:
{
lean_object* v_presentation_4003_; 
v_presentation_4003_ = lean_ctor_get(v_x_3771_, 0);
lean_inc_ref(v_presentation_4003_);
lean_dec_ref_known(v_x_3771_, 1);
if (lean_obj_tag(v_presentation_4003_) == 0)
{
lean_object* v_val_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
lean_dec_ref(v_config_3770_);
v_val_4004_ = lean_ctor_get(v_presentation_4003_, 0);
lean_inc(v_val_4004_);
lean_dec_ref_known(v_presentation_4003_, 1);
v___x_4005_ = lean_unsigned_to_nat(1u);
v___x_4006_ = lean_unsigned_to_nat(4u);
v___x_4007_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4007_, 0, v_val_4004_);
v___x_4008_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4005_, v___x_4006_, v___x_4007_, v_a_3772_);
return v___x_4008_;
}
else
{
lean_object* v_val_4009_; uint8_t v___x_4010_; 
v_val_4009_ = lean_ctor_get(v_presentation_4003_, 0);
lean_inc(v_val_4009_);
lean_dec_ref_known(v_presentation_4003_, 1);
v___x_4010_ = lean_unbox(v_val_4009_);
lean_dec(v_val_4009_);
switch(v___x_4010_)
{
case 0:
{
lean_object* v_dateformat_4011_; lean_object* v_symbols_4012_; lean_object* v___x_4013_; 
v_dateformat_4011_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4011_);
lean_dec_ref(v_config_3770_);
v_symbols_4012_ = lean_ctor_get(v_dateformat_4011_, 1);
lean_inc_ref(v_symbols_4012_);
lean_dec_ref(v_dateformat_4011_);
v___x_4013_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4012_, v_a_3772_);
return v___x_4013_;
}
case 1:
{
lean_object* v_dateformat_4014_; lean_object* v_symbols_4015_; lean_object* v___x_4016_; 
v_dateformat_4014_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4014_);
lean_dec_ref(v_config_3770_);
v_symbols_4015_ = lean_ctor_get(v_dateformat_4014_, 1);
lean_inc_ref(v_symbols_4015_);
lean_dec_ref(v_dateformat_4014_);
v___x_4016_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4015_, v_a_3772_);
return v___x_4016_;
}
default: 
{
v___y_3774_ = v_a_3772_;
goto v___jp_3773_;
}
}
}
}
case 8:
{
lean_object* v_presentation_4017_; 
v_presentation_4017_ = lean_ctor_get(v_x_3771_, 0);
lean_inc_ref(v_presentation_4017_);
lean_dec_ref_known(v_x_3771_, 1);
if (lean_obj_tag(v_presentation_4017_) == 0)
{
lean_object* v_val_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
lean_dec_ref(v_config_3770_);
v_val_4018_ = lean_ctor_get(v_presentation_4017_, 0);
lean_inc(v_val_4018_);
lean_dec_ref_known(v_presentation_4017_, 1);
v___x_4019_ = lean_unsigned_to_nat(1u);
v___x_4020_ = lean_unsigned_to_nat(4u);
v___x_4021_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4021_, 0, v_val_4018_);
v___x_4022_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4019_, v___x_4020_, v___x_4021_, v_a_3772_);
return v___x_4022_;
}
else
{
lean_object* v_val_4023_; uint8_t v___x_4024_; 
v_val_4023_ = lean_ctor_get(v_presentation_4017_, 0);
lean_inc(v_val_4023_);
lean_dec_ref_known(v_presentation_4017_, 1);
v___x_4024_ = lean_unbox(v_val_4023_);
lean_dec(v_val_4023_);
switch(v___x_4024_)
{
case 0:
{
lean_object* v_dateformat_4025_; lean_object* v_symbols_4026_; lean_object* v___x_4027_; 
v_dateformat_4025_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4025_);
lean_dec_ref(v_config_3770_);
v_symbols_4026_ = lean_ctor_get(v_dateformat_4025_, 1);
lean_inc_ref(v_symbols_4026_);
lean_dec_ref(v_dateformat_4025_);
v___x_4027_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4026_, v_a_3772_);
return v___x_4027_;
}
case 1:
{
lean_object* v_dateformat_4028_; lean_object* v_symbols_4029_; lean_object* v___x_4030_; 
v_dateformat_4028_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4028_);
lean_dec_ref(v_config_3770_);
v_symbols_4029_ = lean_ctor_get(v_dateformat_4028_, 1);
lean_inc_ref(v_symbols_4029_);
lean_dec_ref(v_dateformat_4028_);
v___x_4030_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4029_, v_a_3772_);
return v___x_4030_;
}
default: 
{
v___y_3779_ = v_a_3772_;
goto v___jp_3778_;
}
}
}
}
case 9:
{
lean_object* v_presentation_4031_; 
lean_dec_ref(v_config_3770_);
v_presentation_4031_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4031_);
lean_dec_ref_known(v_x_3771_, 1);
switch(lean_obj_tag(v_presentation_4031_))
{
case 0:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_4033_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4032_, v_a_3772_);
return v___x_4033_;
}
case 1:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_unsigned_to_nat(2u);
v___x_4035_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_4034_, v_a_3772_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_pos_4036_; lean_object* v_res_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4047_; 
v_pos_4036_ = lean_ctor_get(v___x_4035_, 0);
v_res_4037_ = lean_ctor_get(v___x_4035_, 1);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4039_ = v___x_4035_;
v_isShared_4040_ = v_isSharedCheck_4047_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_res_4037_);
lean_inc(v_pos_4036_);
lean_dec(v___x_4035_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4047_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4045_; 
v___x_4041_ = lean_nat_to_int(v_res_4037_);
v___x_4042_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_4043_ = lean_int_add(v___x_4042_, v___x_4041_);
lean_dec(v___x_4041_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 1, v___x_4043_);
v___x_4045_ = v___x_4039_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_pos_4036_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v___x_4043_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
else
{
lean_object* v_pos_4048_; lean_object* v_err_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
v_pos_4048_ = lean_ctor_get(v___x_4035_, 0);
v_err_4049_ = lean_ctor_get(v___x_4035_, 1);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4035_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_err_4049_);
lean_inc(v_pos_4048_);
lean_dec(v___x_4035_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_pos_4048_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_err_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
case 2:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_4058_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4057_, v_a_3772_);
return v___x_4058_;
}
default: 
{
lean_object* v_num_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v_num_4059_ = lean_ctor_get(v_presentation_4031_, 0);
lean_inc(v_num_4059_);
lean_dec_ref_known(v_presentation_4031_, 1);
v___x_4060_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_4060_, 0, v_num_4059_);
v___x_4061_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4060_, v_a_3772_);
return v___x_4061_;
}
}
}
case 10:
{
lean_object* v_presentation_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
lean_dec_ref(v_config_3770_);
v_presentation_4062_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4062_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4063_ = lean_unsigned_to_nat(1u);
v___x_4064_ = lean_unsigned_to_nat(53u);
v___x_4065_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4065_, 0, v_presentation_4062_);
v___x_4066_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4063_, v___x_4064_, v___x_4065_, v_a_3772_);
return v___x_4066_;
}
case 11:
{
lean_object* v_presentation_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_dec_ref(v_config_3770_);
v_presentation_4067_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4067_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4068_ = lean_unsigned_to_nat(1u);
v___x_4069_ = lean_unsigned_to_nat(6u);
v___x_4070_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4070_, 0, v_presentation_4067_);
v___x_4071_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4068_, v___x_4069_, v___x_4070_, v_a_3772_);
return v___x_4071_;
}
case 12:
{
uint8_t v_presentation_4072_; 
v_presentation_4072_ = lean_ctor_get_uint8(v_x_3771_, 0);
lean_dec_ref_known(v_x_3771_, 0);
switch(v_presentation_4072_)
{
case 1:
{
lean_object* v_dateformat_4073_; lean_object* v_symbols_4074_; lean_object* v___x_4075_; 
v_dateformat_4073_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4073_);
lean_dec_ref(v_config_3770_);
v_symbols_4074_ = lean_ctor_get(v_dateformat_4073_, 1);
lean_inc_ref(v_symbols_4074_);
lean_dec_ref(v_dateformat_4073_);
v___x_4075_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4074_, v_a_3772_);
return v___x_4075_;
}
case 2:
{
lean_object* v_dateformat_4076_; lean_object* v_symbols_4077_; lean_object* v___x_4078_; 
v_dateformat_4076_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4076_);
lean_dec_ref(v_config_3770_);
v_symbols_4077_ = lean_ctor_get(v_dateformat_4076_, 1);
lean_inc_ref(v_symbols_4077_);
lean_dec_ref(v_dateformat_4076_);
v___x_4078_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4077_, v_a_3772_);
return v___x_4078_;
}
default: 
{
lean_object* v_dateformat_4079_; lean_object* v_symbols_4080_; lean_object* v___x_4081_; 
v_dateformat_4079_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4079_);
lean_dec_ref(v_config_3770_);
v_symbols_4080_ = lean_ctor_get(v_dateformat_4079_, 1);
lean_inc_ref(v_symbols_4080_);
lean_dec_ref(v_dateformat_4079_);
v___x_4081_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4080_, v_a_3772_);
return v___x_4081_;
}
}
}
case 13:
{
lean_object* v_presentation_4082_; 
v_presentation_4082_ = lean_ctor_get(v_x_3771_, 0);
lean_inc_ref(v_presentation_4082_);
lean_dec_ref_known(v_x_3771_, 1);
if (lean_obj_tag(v_presentation_4082_) == 0)
{
lean_object* v_val_4083_; lean_object* v___x_4084_; 
v_val_4083_ = lean_ctor_get(v_presentation_4082_, 0);
lean_inc(v_val_4083_);
lean_dec_ref_known(v_presentation_4082_, 1);
v___x_4084_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4083_, v_a_3772_);
lean_dec(v_val_4083_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_pos_4085_; lean_object* v_res_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4122_; 
v_pos_4085_ = lean_ctor_get(v___x_4084_, 0);
v_res_4086_ = lean_ctor_get(v___x_4084_, 1);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4088_ = v___x_4084_;
v_isShared_4089_ = v_isSharedCheck_4122_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_res_4086_);
lean_inc(v_pos_4085_);
lean_dec(v___x_4084_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4122_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
uint8_t v___y_4091_; lean_object* v___x_4118_; uint8_t v___x_4119_; 
v___x_4118_ = lean_unsigned_to_nat(1u);
v___x_4119_ = lean_nat_dec_le(v___x_4118_, v_res_4086_);
if (v___x_4119_ == 0)
{
v___y_4091_ = v___x_4119_;
goto v___jp_4090_;
}
else
{
lean_object* v___x_4120_; uint8_t v___x_4121_; 
v___x_4120_ = lean_unsigned_to_nat(7u);
v___x_4121_ = lean_nat_dec_le(v_res_4086_, v___x_4120_);
v___y_4091_ = v___x_4121_;
goto v___jp_4090_;
}
v___jp_4090_:
{
if (v___y_4091_ == 0)
{
lean_object* v___x_4092_; lean_object* v___x_4094_; 
lean_dec(v_res_4086_);
lean_dec_ref(v_config_3770_);
v___x_4092_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4089_ == 0)
{
lean_ctor_set_tag(v___x_4088_, 1);
lean_ctor_set(v___x_4088_, 1, v___x_4092_);
v___x_4094_ = v___x_4088_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_pos_4085_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4092_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
else
{
lean_object* v_dateformat_4096_; uint8_t v_firstDayOfWeek_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v_range_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4116_; 
v_dateformat_4096_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4096_);
lean_dec_ref(v_config_3770_);
v_firstDayOfWeek_4097_ = lean_ctor_get_uint8(v_dateformat_4096_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4096_);
v___x_4098_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4097_);
v___x_4099_ = lean_nat_to_int(v_res_4086_);
v___x_4100_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4101_ = lean_int_sub(v___x_4099_, v___x_4100_);
lean_dec(v___x_4099_);
v___x_4102_ = lean_int_add(v___x_4101_, v___x_4098_);
lean_dec(v___x_4098_);
lean_dec(v___x_4101_);
v___x_4103_ = lean_int_sub(v___x_4102_, v___x_4100_);
lean_dec(v___x_4102_);
v___x_4104_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4105_ = lean_int_emod(v___x_4103_, v___x_4104_);
lean_dec(v___x_4103_);
v___x_4106_ = lean_int_add(v___x_4105_, v___x_4100_);
lean_dec(v___x_4105_);
v_range_4107_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4108_ = lean_int_sub(v___x_4106_, v___x_4100_);
lean_dec(v___x_4106_);
v___x_4109_ = lean_int_emod(v___x_4108_, v_range_4107_);
lean_dec(v___x_4108_);
v___x_4110_ = lean_int_add(v___x_4109_, v_range_4107_);
lean_dec(v___x_4109_);
v___x_4111_ = lean_int_emod(v___x_4110_, v_range_4107_);
lean_dec(v___x_4110_);
v___x_4112_ = lean_int_add(v___x_4111_, v___x_4100_);
lean_dec(v___x_4111_);
v___x_4113_ = l_Std_Time_Weekday_ofOrdinal(v___x_4112_);
lean_dec(v___x_4112_);
v___x_4114_ = lean_box(v___x_4113_);
if (v_isShared_4089_ == 0)
{
lean_ctor_set(v___x_4088_, 1, v___x_4114_);
v___x_4116_ = v___x_4088_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_pos_4085_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v___x_4114_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
else
{
lean_object* v_pos_4123_; lean_object* v_err_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec_ref(v_config_3770_);
v_pos_4123_ = lean_ctor_get(v___x_4084_, 0);
v_err_4124_ = lean_ctor_get(v___x_4084_, 1);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4084_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_err_4124_);
lean_inc(v_pos_4123_);
lean_dec(v___x_4084_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_pos_4123_);
lean_ctor_set(v_reuseFailAlloc_4130_, 1, v_err_4124_);
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
else
{
lean_object* v_val_4132_; uint8_t v___x_4133_; 
v_val_4132_ = lean_ctor_get(v_presentation_4082_, 0);
lean_inc(v_val_4132_);
lean_dec_ref_known(v_presentation_4082_, 1);
v___x_4133_ = lean_unbox(v_val_4132_);
lean_dec(v_val_4132_);
switch(v___x_4133_)
{
case 0:
{
lean_object* v_dateformat_4134_; lean_object* v_symbols_4135_; lean_object* v___x_4136_; 
v_dateformat_4134_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4134_);
lean_dec_ref(v_config_3770_);
v_symbols_4135_ = lean_ctor_get(v_dateformat_4134_, 1);
lean_inc_ref(v_symbols_4135_);
lean_dec_ref(v_dateformat_4134_);
v___x_4136_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4135_, v_a_3772_);
return v___x_4136_;
}
case 1:
{
lean_object* v_dateformat_4137_; lean_object* v_symbols_4138_; lean_object* v___x_4139_; 
v_dateformat_4137_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4137_);
lean_dec_ref(v_config_3770_);
v_symbols_4138_ = lean_ctor_get(v_dateformat_4137_, 1);
lean_inc_ref(v_symbols_4138_);
lean_dec_ref(v_dateformat_4137_);
v___x_4139_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4138_, v_a_3772_);
return v___x_4139_;
}
case 2:
{
lean_object* v_dateformat_4140_; lean_object* v_symbols_4141_; lean_object* v___x_4142_; 
v_dateformat_4140_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4140_);
lean_dec_ref(v_config_3770_);
v_symbols_4141_ = lean_ctor_get(v_dateformat_4140_, 1);
lean_inc_ref(v_symbols_4141_);
lean_dec_ref(v_dateformat_4140_);
v___x_4142_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4141_, v_a_3772_);
return v___x_4142_;
}
default: 
{
lean_object* v_dateformat_4143_; lean_object* v_symbols_4144_; lean_object* v___x_4145_; 
v_dateformat_4143_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4143_);
lean_dec_ref(v_config_3770_);
v_symbols_4144_ = lean_ctor_get(v_dateformat_4143_, 1);
lean_inc_ref(v_symbols_4144_);
lean_dec_ref(v_dateformat_4143_);
v___x_4145_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4144_, v_a_3772_);
return v___x_4145_;
}
}
}
}
case 14:
{
lean_object* v_presentation_4146_; 
v_presentation_4146_ = lean_ctor_get(v_x_3771_, 0);
lean_inc_ref(v_presentation_4146_);
lean_dec_ref_known(v_x_3771_, 1);
if (lean_obj_tag(v_presentation_4146_) == 0)
{
lean_object* v_val_4147_; lean_object* v___x_4148_; 
v_val_4147_ = lean_ctor_get(v_presentation_4146_, 0);
lean_inc(v_val_4147_);
lean_dec_ref_known(v_presentation_4146_, 1);
v___x_4148_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4147_, v_a_3772_);
lean_dec(v_val_4147_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_pos_4149_; lean_object* v_res_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4186_; 
v_pos_4149_ = lean_ctor_get(v___x_4148_, 0);
v_res_4150_ = lean_ctor_get(v___x_4148_, 1);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4152_ = v___x_4148_;
v_isShared_4153_ = v_isSharedCheck_4186_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_res_4150_);
lean_inc(v_pos_4149_);
lean_dec(v___x_4148_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4186_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
uint8_t v___y_4155_; lean_object* v___x_4182_; uint8_t v___x_4183_; 
v___x_4182_ = lean_unsigned_to_nat(1u);
v___x_4183_ = lean_nat_dec_le(v___x_4182_, v_res_4150_);
if (v___x_4183_ == 0)
{
v___y_4155_ = v___x_4183_;
goto v___jp_4154_;
}
else
{
lean_object* v___x_4184_; uint8_t v___x_4185_; 
v___x_4184_ = lean_unsigned_to_nat(7u);
v___x_4185_ = lean_nat_dec_le(v_res_4150_, v___x_4184_);
v___y_4155_ = v___x_4185_;
goto v___jp_4154_;
}
v___jp_4154_:
{
if (v___y_4155_ == 0)
{
lean_object* v___x_4156_; lean_object* v___x_4158_; 
lean_dec(v_res_4150_);
lean_dec_ref(v_config_3770_);
v___x_4156_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4153_ == 0)
{
lean_ctor_set_tag(v___x_4152_, 1);
lean_ctor_set(v___x_4152_, 1, v___x_4156_);
v___x_4158_ = v___x_4152_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_pos_4149_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v___x_4156_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
else
{
lean_object* v_dateformat_4160_; uint8_t v_firstDayOfWeek_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v_range_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; uint8_t v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4180_; 
v_dateformat_4160_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4160_);
lean_dec_ref(v_config_3770_);
v_firstDayOfWeek_4161_ = lean_ctor_get_uint8(v_dateformat_4160_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4160_);
v___x_4162_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4161_);
v___x_4163_ = lean_nat_to_int(v_res_4150_);
v___x_4164_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4165_ = lean_int_sub(v___x_4163_, v___x_4164_);
lean_dec(v___x_4163_);
v___x_4166_ = lean_int_add(v___x_4165_, v___x_4162_);
lean_dec(v___x_4162_);
lean_dec(v___x_4165_);
v___x_4167_ = lean_int_sub(v___x_4166_, v___x_4164_);
lean_dec(v___x_4166_);
v___x_4168_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4169_ = lean_int_emod(v___x_4167_, v___x_4168_);
lean_dec(v___x_4167_);
v___x_4170_ = lean_int_add(v___x_4169_, v___x_4164_);
lean_dec(v___x_4169_);
v_range_4171_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4172_ = lean_int_sub(v___x_4170_, v___x_4164_);
lean_dec(v___x_4170_);
v___x_4173_ = lean_int_emod(v___x_4172_, v_range_4171_);
lean_dec(v___x_4172_);
v___x_4174_ = lean_int_add(v___x_4173_, v_range_4171_);
lean_dec(v___x_4173_);
v___x_4175_ = lean_int_emod(v___x_4174_, v_range_4171_);
lean_dec(v___x_4174_);
v___x_4176_ = lean_int_add(v___x_4175_, v___x_4164_);
lean_dec(v___x_4175_);
v___x_4177_ = l_Std_Time_Weekday_ofOrdinal(v___x_4176_);
lean_dec(v___x_4176_);
v___x_4178_ = lean_box(v___x_4177_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 1, v___x_4178_);
v___x_4180_ = v___x_4152_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_pos_4149_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v___x_4178_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
}
else
{
lean_object* v_pos_4187_; lean_object* v_err_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
lean_dec_ref(v_config_3770_);
v_pos_4187_ = lean_ctor_get(v___x_4148_, 0);
v_err_4188_ = lean_ctor_get(v___x_4148_, 1);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4148_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_err_4188_);
lean_inc(v_pos_4187_);
lean_dec(v___x_4148_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_pos_4187_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_err_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
else
{
lean_object* v_val_4196_; uint8_t v___x_4197_; 
v_val_4196_ = lean_ctor_get(v_presentation_4146_, 0);
lean_inc(v_val_4196_);
lean_dec_ref_known(v_presentation_4146_, 1);
v___x_4197_ = lean_unbox(v_val_4196_);
lean_dec(v_val_4196_);
switch(v___x_4197_)
{
case 0:
{
lean_object* v_dateformat_4198_; lean_object* v_symbols_4199_; lean_object* v___x_4200_; 
v_dateformat_4198_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4198_);
lean_dec_ref(v_config_3770_);
v_symbols_4199_ = lean_ctor_get(v_dateformat_4198_, 1);
lean_inc_ref(v_symbols_4199_);
lean_dec_ref(v_dateformat_4198_);
v___x_4200_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4199_, v_a_3772_);
return v___x_4200_;
}
case 1:
{
lean_object* v_dateformat_4201_; lean_object* v_symbols_4202_; lean_object* v___x_4203_; 
v_dateformat_4201_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4201_);
lean_dec_ref(v_config_3770_);
v_symbols_4202_ = lean_ctor_get(v_dateformat_4201_, 1);
lean_inc_ref(v_symbols_4202_);
lean_dec_ref(v_dateformat_4201_);
v___x_4203_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4202_, v_a_3772_);
return v___x_4203_;
}
case 2:
{
lean_object* v_dateformat_4204_; lean_object* v_symbols_4205_; lean_object* v___x_4206_; 
v_dateformat_4204_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4204_);
lean_dec_ref(v_config_3770_);
v_symbols_4205_ = lean_ctor_get(v_dateformat_4204_, 1);
lean_inc_ref(v_symbols_4205_);
lean_dec_ref(v_dateformat_4204_);
v___x_4206_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4205_, v_a_3772_);
return v___x_4206_;
}
default: 
{
lean_object* v_dateformat_4207_; lean_object* v_symbols_4208_; lean_object* v___x_4209_; 
v_dateformat_4207_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4207_);
lean_dec_ref(v_config_3770_);
v_symbols_4208_ = lean_ctor_get(v_dateformat_4207_, 1);
lean_inc_ref(v_symbols_4208_);
lean_dec_ref(v_dateformat_4207_);
v___x_4209_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4208_, v_a_3772_);
return v___x_4209_;
}
}
}
}
case 15:
{
lean_object* v_presentation_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
lean_dec_ref(v_config_3770_);
v_presentation_4210_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4210_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4211_ = lean_unsigned_to_nat(1u);
v___x_4212_ = lean_unsigned_to_nat(5u);
v___x_4213_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4213_, 0, v_presentation_4210_);
v___x_4214_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4211_, v___x_4212_, v___x_4213_, v_a_3772_);
return v___x_4214_;
}
case 16:
{
uint8_t v_presentation_4215_; 
v_presentation_4215_ = lean_ctor_get_uint8(v_x_3771_, 0);
lean_dec_ref_known(v_x_3771_, 0);
switch(v_presentation_4215_)
{
case 1:
{
lean_object* v_dateformat_4216_; lean_object* v_symbols_4217_; lean_object* v___x_4218_; 
v_dateformat_4216_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4216_);
lean_dec_ref(v_config_3770_);
v_symbols_4217_ = lean_ctor_get(v_dateformat_4216_, 1);
lean_inc_ref(v_symbols_4217_);
lean_dec_ref(v_dateformat_4216_);
v___x_4218_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(v_symbols_4217_, v_a_3772_);
return v___x_4218_;
}
case 2:
{
lean_object* v_dateformat_4219_; lean_object* v_symbols_4220_; lean_object* v___x_4221_; 
v_dateformat_4219_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4219_);
lean_dec_ref(v_config_3770_);
v_symbols_4220_ = lean_ctor_get(v_dateformat_4219_, 1);
lean_inc_ref(v_symbols_4220_);
lean_dec_ref(v_dateformat_4219_);
v___x_4221_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(v_symbols_4220_, v_a_3772_);
return v___x_4221_;
}
default: 
{
lean_object* v_dateformat_4222_; lean_object* v_symbols_4223_; lean_object* v___x_4224_; 
v_dateformat_4222_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4222_);
lean_dec_ref(v_config_3770_);
v_symbols_4223_ = lean_ctor_get(v_dateformat_4222_, 1);
lean_inc_ref(v_symbols_4223_);
lean_dec_ref(v_dateformat_4222_);
v___x_4224_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(v_symbols_4223_, v_a_3772_);
return v___x_4224_;
}
}
}
case 17:
{
uint8_t v_presentation_4225_; 
v_presentation_4225_ = lean_ctor_get_uint8(v_x_3771_, 0);
lean_dec_ref_known(v_x_3771_, 0);
switch(v_presentation_4225_)
{
case 1:
{
lean_object* v_dateformat_4226_; lean_object* v_symbols_4227_; lean_object* v_dayPeriodLong_4228_; lean_object* v___x_4229_; 
v_dateformat_4226_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4226_);
lean_dec_ref(v_config_3770_);
v_symbols_4227_ = lean_ctor_get(v_dateformat_4226_, 1);
lean_inc_ref(v_symbols_4227_);
lean_dec_ref(v_dateformat_4226_);
v_dayPeriodLong_4228_ = lean_ctor_get(v_symbols_4227_, 20);
lean_inc_ref(v_dayPeriodLong_4228_);
lean_dec_ref(v_symbols_4227_);
v___x_4229_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodLong_4228_, v_a_3772_);
return v___x_4229_;
}
case 2:
{
lean_object* v_dateformat_4230_; lean_object* v_symbols_4231_; lean_object* v_dayPeriodNarrow_4232_; lean_object* v___x_4233_; 
v_dateformat_4230_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4230_);
lean_dec_ref(v_config_3770_);
v_symbols_4231_ = lean_ctor_get(v_dateformat_4230_, 1);
lean_inc_ref(v_symbols_4231_);
lean_dec_ref(v_dateformat_4230_);
v_dayPeriodNarrow_4232_ = lean_ctor_get(v_symbols_4231_, 21);
lean_inc_ref(v_dayPeriodNarrow_4232_);
lean_dec_ref(v_symbols_4231_);
v___x_4233_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodNarrow_4232_, v_a_3772_);
return v___x_4233_;
}
default: 
{
lean_object* v_dateformat_4234_; lean_object* v_symbols_4235_; lean_object* v_dayPeriodShort_4236_; lean_object* v___x_4237_; 
v_dateformat_4234_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4234_);
lean_dec_ref(v_config_3770_);
v_symbols_4235_ = lean_ctor_get(v_dateformat_4234_, 1);
lean_inc_ref(v_symbols_4235_);
lean_dec_ref(v_dateformat_4234_);
v_dayPeriodShort_4236_ = lean_ctor_get(v_symbols_4235_, 19);
lean_inc_ref(v_dayPeriodShort_4236_);
lean_dec_ref(v_symbols_4235_);
v___x_4237_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodShort_4236_, v_a_3772_);
return v___x_4237_;
}
}
}
case 18:
{
uint8_t v_presentation_4238_; 
v_presentation_4238_ = lean_ctor_get_uint8(v_x_3771_, 0);
lean_dec_ref_known(v_x_3771_, 0);
switch(v_presentation_4238_)
{
case 1:
{
lean_object* v_dateformat_4239_; lean_object* v_symbols_4240_; lean_object* v_extendedDayPeriodLong_4241_; lean_object* v___x_4242_; 
v_dateformat_4239_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4239_);
lean_dec_ref(v_config_3770_);
v_symbols_4240_ = lean_ctor_get(v_dateformat_4239_, 1);
lean_inc_ref(v_symbols_4240_);
lean_dec_ref(v_dateformat_4239_);
v_extendedDayPeriodLong_4241_ = lean_ctor_get(v_symbols_4240_, 23);
lean_inc_ref(v_extendedDayPeriodLong_4241_);
lean_dec_ref(v_symbols_4240_);
v___x_4242_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodLong_4241_, v_a_3772_);
lean_dec_ref(v_extendedDayPeriodLong_4241_);
return v___x_4242_;
}
case 2:
{
lean_object* v_dateformat_4243_; lean_object* v_symbols_4244_; lean_object* v_extendedDayPeriodNarrow_4245_; lean_object* v___x_4246_; 
v_dateformat_4243_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4243_);
lean_dec_ref(v_config_3770_);
v_symbols_4244_ = lean_ctor_get(v_dateformat_4243_, 1);
lean_inc_ref(v_symbols_4244_);
lean_dec_ref(v_dateformat_4243_);
v_extendedDayPeriodNarrow_4245_ = lean_ctor_get(v_symbols_4244_, 24);
lean_inc_ref(v_extendedDayPeriodNarrow_4245_);
lean_dec_ref(v_symbols_4244_);
v___x_4246_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodNarrow_4245_, v_a_3772_);
lean_dec_ref(v_extendedDayPeriodNarrow_4245_);
return v___x_4246_;
}
default: 
{
lean_object* v_dateformat_4247_; lean_object* v_symbols_4248_; lean_object* v_extendedDayPeriodShort_4249_; lean_object* v___x_4250_; 
v_dateformat_4247_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_4247_);
lean_dec_ref(v_config_3770_);
v_symbols_4248_ = lean_ctor_get(v_dateformat_4247_, 1);
lean_inc_ref(v_symbols_4248_);
lean_dec_ref(v_dateformat_4247_);
v_extendedDayPeriodShort_4249_ = lean_ctor_get(v_symbols_4248_, 22);
lean_inc_ref(v_extendedDayPeriodShort_4249_);
lean_dec_ref(v_symbols_4248_);
v___x_4250_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodShort_4249_, v_a_3772_);
lean_dec_ref(v_extendedDayPeriodShort_4249_);
return v___x_4250_;
}
}
}
case 19:
{
lean_object* v_presentation_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
lean_dec_ref(v_config_3770_);
v_presentation_4251_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4251_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4252_ = lean_unsigned_to_nat(1u);
v___x_4253_ = lean_unsigned_to_nat(12u);
v___x_4254_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4254_, 0, v_presentation_4251_);
v___x_4255_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4252_, v___x_4253_, v___x_4254_, v_a_3772_);
return v___x_4255_;
}
case 20:
{
lean_object* v_presentation_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
lean_dec_ref(v_config_3770_);
v_presentation_4256_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4256_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4257_ = lean_unsigned_to_nat(0u);
v___x_4258_ = lean_unsigned_to_nat(11u);
v___x_4259_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4259_, 0, v_presentation_4256_);
v___x_4260_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4257_, v___x_4258_, v___x_4259_, v_a_3772_);
return v___x_4260_;
}
case 21:
{
lean_object* v_presentation_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
lean_dec_ref(v_config_3770_);
v_presentation_4261_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4261_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4262_ = lean_unsigned_to_nat(1u);
v___x_4263_ = lean_unsigned_to_nat(24u);
v___x_4264_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4264_, 0, v_presentation_4261_);
v___x_4265_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4262_, v___x_4263_, v___x_4264_, v_a_3772_);
return v___x_4265_;
}
case 22:
{
lean_object* v_presentation_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
lean_dec_ref(v_config_3770_);
v_presentation_4266_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4266_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4267_ = lean_unsigned_to_nat(0u);
v___x_4268_ = lean_unsigned_to_nat(23u);
v___x_4269_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4269_, 0, v_presentation_4266_);
v___x_4270_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4267_, v___x_4268_, v___x_4269_, v_a_3772_);
return v___x_4270_;
}
case 23:
{
lean_object* v_presentation_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
lean_dec_ref(v_config_3770_);
v_presentation_4271_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4271_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4272_ = lean_unsigned_to_nat(0u);
v___x_4273_ = lean_unsigned_to_nat(59u);
v___x_4274_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4274_, 0, v_presentation_4271_);
v___x_4275_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4272_, v___x_4273_, v___x_4274_, v_a_3772_);
return v___x_4275_;
}
case 24:
{
uint8_t v_allowLeapSeconds_4276_; 
v_allowLeapSeconds_4276_ = lean_ctor_get_uint8(v_config_3770_, sizeof(void*)*1);
lean_dec_ref(v_config_3770_);
if (v_allowLeapSeconds_4276_ == 0)
{
lean_object* v_presentation_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v_presentation_4277_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4277_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4278_ = lean_unsigned_to_nat(0u);
v___x_4279_ = lean_unsigned_to_nat(59u);
v___x_4280_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4280_, 0, v_presentation_4277_);
v___x_4281_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4278_, v___x_4279_, v___x_4280_, v_a_3772_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_pos_4282_; lean_object* v_res_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
v_pos_4282_ = lean_ctor_get(v___x_4281_, 0);
v_res_4283_ = lean_ctor_get(v___x_4281_, 1);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4281_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_res_4283_);
lean_inc(v_pos_4282_);
lean_dec(v___x_4281_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_pos_4282_);
lean_ctor_set(v_reuseFailAlloc_4289_, 1, v_res_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
else
{
return v___x_4281_;
}
}
else
{
lean_object* v_presentation_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_presentation_4291_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4291_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4292_ = lean_unsigned_to_nat(0u);
v___x_4293_ = lean_unsigned_to_nat(60u);
v___x_4294_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4294_, 0, v_presentation_4291_);
v___x_4295_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4292_, v___x_4293_, v___x_4294_, v_a_3772_);
return v___x_4295_;
}
}
case 25:
{
lean_object* v_presentation_4296_; 
lean_dec_ref(v_config_3770_);
v_presentation_4296_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4296_);
lean_dec_ref_known(v_x_3771_, 1);
if (lean_obj_tag(v_presentation_4296_) == 0)
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = lean_unsigned_to_nat(999999999u);
v___x_4299_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7));
v___x_4300_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4297_, v___x_4298_, v___x_4299_, v_a_3772_);
return v___x_4300_;
}
else
{
lean_object* v_digits_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v_digits_4301_ = lean_ctor_get(v_presentation_4296_, 0);
lean_inc(v_digits_4301_);
lean_dec_ref_known(v_presentation_4296_, 1);
v___x_4302_ = lean_unsigned_to_nat(0u);
v___x_4303_ = lean_unsigned_to_nat(999999999u);
v___x_4304_ = lean_unsigned_to_nat(9u);
v___x_4305_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed), 3, 2);
lean_closure_set(v___x_4305_, 0, v_digits_4301_);
lean_closure_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4302_, v___x_4303_, v___x_4305_, v_a_3772_);
return v___x_4306_;
}
}
case 26:
{
lean_object* v_presentation_4307_; lean_object* v___x_4308_; 
lean_dec_ref(v_config_3770_);
v_presentation_4307_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4307_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4308_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4307_, v_a_3772_);
lean_dec(v_presentation_4307_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_pos_4309_; lean_object* v_res_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4318_; 
v_pos_4309_ = lean_ctor_get(v___x_4308_, 0);
v_res_4310_ = lean_ctor_get(v___x_4308_, 1);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4312_ = v___x_4308_;
v_isShared_4313_ = v_isSharedCheck_4318_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_res_4310_);
lean_inc(v_pos_4309_);
lean_dec(v___x_4308_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4318_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4314_; lean_object* v___x_4316_; 
v___x_4314_ = lean_nat_to_int(v_res_4310_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 1, v___x_4314_);
v___x_4316_ = v___x_4312_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_pos_4309_);
lean_ctor_set(v_reuseFailAlloc_4317_, 1, v___x_4314_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
else
{
lean_object* v_pos_4319_; lean_object* v_err_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
v_pos_4319_ = lean_ctor_get(v___x_4308_, 0);
v_err_4320_ = lean_ctor_get(v___x_4308_, 1);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4308_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_err_4320_);
lean_inc(v_pos_4319_);
lean_dec(v___x_4308_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_pos_4319_);
lean_ctor_set(v_reuseFailAlloc_4326_, 1, v_err_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
case 27:
{
lean_object* v_presentation_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
lean_dec_ref(v_config_3770_);
v_presentation_4328_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4328_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4329_ = lean_unsigned_to_nat(0u);
v___x_4330_ = lean_unsigned_to_nat(999999999u);
v___x_4331_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4331_, 0, v_presentation_4328_);
v___x_4332_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4329_, v___x_4330_, v___x_4331_, v_a_3772_);
return v___x_4332_;
}
case 28:
{
lean_object* v_presentation_4333_; lean_object* v___x_4334_; 
lean_dec_ref(v_config_3770_);
v_presentation_4333_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_presentation_4333_);
lean_dec_ref_known(v_x_3771_, 1);
v___x_4334_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4333_, v_a_3772_);
lean_dec(v_presentation_4333_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_pos_4335_; lean_object* v_res_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4344_; 
v_pos_4335_ = lean_ctor_get(v___x_4334_, 0);
v_res_4336_ = lean_ctor_get(v___x_4334_, 1);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4338_ = v___x_4334_;
v_isShared_4339_ = v_isSharedCheck_4344_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_res_4336_);
lean_inc(v_pos_4335_);
lean_dec(v___x_4334_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4344_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4340_; lean_object* v___x_4342_; 
v___x_4340_ = lean_nat_to_int(v_res_4336_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 1, v___x_4340_);
v___x_4342_ = v___x_4338_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_pos_4335_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v___x_4340_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
else
{
lean_object* v_pos_4345_; lean_object* v_err_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
v_pos_4345_ = lean_ctor_get(v___x_4334_, 0);
v_err_4346_ = lean_ctor_get(v___x_4334_, 1);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4334_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_err_4346_);
lean_inc(v_pos_4345_);
lean_dec(v___x_4334_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_pos_4345_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v_err_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
case 29:
{
uint8_t v_presentation_4354_; 
lean_dec_ref(v_config_3770_);
v_presentation_4354_ = lean_ctor_get_uint8(v_x_3771_, 0);
lean_dec_ref_known(v_x_3771_, 0);
if (v_presentation_4354_ == 0)
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4355_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
v___x_4356_ = l_Std_Internal_Parsec_String_pstring(v___x_4355_, v_a_3772_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_pos_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
v_pos_4357_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4364_ == 0)
{
lean_object* v_unused_4365_; 
v_unused_4365_ = lean_ctor_get(v___x_4356_, 1);
lean_dec(v_unused_4365_);
v___x_4359_ = v___x_4356_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_pos_4357_);
lean_dec(v___x_4356_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
lean_ctor_set(v___x_4359_, 1, v___x_4355_);
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_pos_4357_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v___x_4355_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
else
{
return v___x_4356_;
}
}
else
{
lean_object* v___x_4366_; 
v___x_4366_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3772_);
return v___x_4366_;
}
}
case 32:
{
uint8_t v_presentation_4367_; 
lean_dec_ref(v_config_3770_);
v_presentation_4367_ = lean_ctor_get_uint8(v_x_3771_, 0);
lean_dec_ref_known(v_x_3771_, 0);
if (v_presentation_4367_ == 0)
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4368_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4369_ = l_Std_Internal_Parsec_String_pstring(v___x_4368_, v_a_3772_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_pos_4370_; uint8_t v___x_4371_; uint8_t v___x_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; 
v_pos_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_pos_4370_);
lean_dec_ref_known(v___x_4369_, 2);
v___x_4371_ = 2;
v___x_4372_ = 1;
v___x_4373_ = 1;
v___x_4374_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4371_, v___x_4372_, v___x_4373_, v_pos_4370_);
return v___x_4374_;
}
else
{
lean_object* v_pos_4375_; lean_object* v_err_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
v_pos_4375_ = lean_ctor_get(v___x_4369_, 0);
v_err_4376_ = lean_ctor_get(v___x_4369_, 1);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4369_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_err_4376_);
lean_inc(v_pos_4375_);
lean_dec(v___x_4369_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_pos_4375_);
lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_err_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
else
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4385_ = l_Std_Internal_Parsec_String_pstring(v___x_4384_, v_a_3772_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_pos_4386_; uint8_t v___x_4387_; uint8_t v___x_4388_; uint8_t v___x_4389_; lean_object* v___x_4390_; 
v_pos_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_pos_4386_);
lean_dec_ref_known(v___x_4385_, 2);
v___x_4387_ = 0;
v___x_4388_ = 2;
v___x_4389_ = 1;
v___x_4390_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4387_, v___x_4388_, v___x_4389_, v_pos_4386_);
return v___x_4390_;
}
else
{
lean_object* v_pos_4391_; lean_object* v_err_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
v_pos_4391_ = lean_ctor_get(v___x_4385_, 0);
v_err_4392_ = lean_ctor_get(v___x_4385_, 1);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4385_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_err_4392_);
lean_inc(v_pos_4391_);
lean_dec(v___x_4385_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_pos_4391_);
lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_err_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
}
case 33:
{
uint8_t v_presentation_4400_; 
lean_dec_ref(v_config_3770_);
v_presentation_4400_ = lean_ctor_get_uint8(v_x_3771_, 0);
lean_dec_ref_known(v_x_3771_, 0);
switch(v_presentation_4400_)
{
case 0:
{
uint8_t v___x_4401_; uint8_t v___x_4402_; uint8_t v___x_4403_; lean_object* v___x_4404_; 
v___x_4401_ = 2;
v___x_4402_ = 1;
v___x_4403_ = 0;
lean_inc_ref(v_a_3772_);
v___x_4404_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4401_, v___x_4402_, v___x_4403_, v_a_3772_);
v___y_3784_ = v___x_4404_;
goto v___jp_3783_;
}
case 1:
{
uint8_t v___x_4405_; uint8_t v___x_4406_; uint8_t v___x_4407_; lean_object* v___x_4408_; 
v___x_4405_ = 0;
v___x_4406_ = 1;
v___x_4407_ = 0;
lean_inc_ref(v_a_3772_);
v___x_4408_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4405_, v___x_4406_, v___x_4407_, v_a_3772_);
v___y_3784_ = v___x_4408_;
goto v___jp_3783_;
}
case 2:
{
uint8_t v___x_4409_; uint8_t v___x_4410_; uint8_t v___x_4411_; lean_object* v___x_4412_; 
v___x_4409_ = 0;
v___x_4410_ = 1;
v___x_4411_ = 1;
lean_inc_ref(v_a_3772_);
v___x_4412_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4409_, v___x_4410_, v___x_4411_, v_a_3772_);
v___y_3784_ = v___x_4412_;
goto v___jp_3783_;
}
case 3:
{
uint8_t v___x_4413_; uint8_t v___x_4414_; uint8_t v___x_4415_; lean_object* v___x_4416_; 
v___x_4413_ = 0;
v___x_4414_ = 2;
v___x_4415_ = 0;
lean_inc_ref(v_a_3772_);
v___x_4416_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4413_, v___x_4414_, v___x_4415_, v_a_3772_);
v___y_3784_ = v___x_4416_;
goto v___jp_3783_;
}
default: 
{
uint8_t v___x_4417_; uint8_t v___x_4418_; uint8_t v___x_4419_; lean_object* v___x_4420_; 
v___x_4417_ = 0;
v___x_4418_ = 2;
v___x_4419_ = 1;
lean_inc_ref(v_a_3772_);
v___x_4420_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4417_, v___x_4418_, v___x_4419_, v_a_3772_);
v___y_3784_ = v___x_4420_;
goto v___jp_3783_;
}
}
}
case 34:
{
uint8_t v_presentation_4421_; 
lean_dec_ref(v_config_3770_);
v_presentation_4421_ = lean_ctor_get_uint8(v_x_3771_, 0);
lean_dec_ref_known(v_x_3771_, 0);
switch(v_presentation_4421_)
{
case 0:
{
uint8_t v___x_4422_; uint8_t v___x_4423_; uint8_t v___x_4424_; lean_object* v___x_4425_; 
v___x_4422_ = 2;
v___x_4423_ = 1;
v___x_4424_ = 0;
v___x_4425_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4422_, v___x_4423_, v___x_4424_, v_a_3772_);
return v___x_4425_;
}
case 1:
{
uint8_t v___x_4426_; uint8_t v___x_4427_; uint8_t v___x_4428_; lean_object* v___x_4429_; 
v___x_4426_ = 0;
v___x_4427_ = 1;
v___x_4428_ = 0;
v___x_4429_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4426_, v___x_4427_, v___x_4428_, v_a_3772_);
return v___x_4429_;
}
case 2:
{
uint8_t v___x_4430_; uint8_t v___x_4431_; uint8_t v___x_4432_; lean_object* v___x_4433_; 
v___x_4430_ = 0;
v___x_4431_ = 2;
v___x_4432_ = 1;
v___x_4433_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4430_, v___x_4431_, v___x_4432_, v_a_3772_);
return v___x_4433_;
}
case 3:
{
uint8_t v___x_4434_; uint8_t v___x_4435_; uint8_t v___x_4436_; lean_object* v___x_4437_; 
v___x_4434_ = 0;
v___x_4435_ = 2;
v___x_4436_ = 0;
v___x_4437_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4434_, v___x_4435_, v___x_4436_, v_a_3772_);
return v___x_4437_;
}
default: 
{
uint8_t v___x_4438_; uint8_t v___x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = 0;
v___x_4439_ = 1;
v___x_4440_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4438_, v___x_4438_, v___x_4439_, v_a_3772_);
return v___x_4440_;
}
}
}
case 35:
{
uint8_t v_presentation_4441_; 
lean_dec_ref(v_config_3770_);
v_presentation_4441_ = lean_ctor_get_uint8(v_x_3771_, 0);
lean_dec_ref_known(v_x_3771_, 0);
switch(v_presentation_4441_)
{
case 0:
{
uint8_t v___x_4442_; uint8_t v___x_4443_; uint8_t v___x_4444_; lean_object* v___x_4445_; 
v___x_4442_ = 0;
v___x_4443_ = 1;
v___x_4444_ = 0;
v___x_4445_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4442_, v___x_4443_, v___x_4444_, v_a_3772_);
return v___x_4445_;
}
case 1:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4446_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4447_ = l_Std_Internal_Parsec_String_pstring(v___x_4446_, v_a_3772_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_pos_4448_; uint8_t v___x_4449_; uint8_t v___x_4450_; uint8_t v___x_4451_; lean_object* v___x_4452_; 
v_pos_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc_n(v_pos_4448_, 2);
lean_dec_ref_known(v___x_4447_, 2);
v___x_4449_ = 0;
v___x_4450_ = 1;
v___x_4451_ = 1;
v___x_4452_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4449_, v___x_4450_, v___x_4451_, v_pos_4448_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_dec(v_pos_4448_);
return v___x_4452_;
}
else
{
lean_object* v_pos_4453_; lean_object* v_snd_4454_; lean_object* v_snd_4455_; uint8_t v_decide_4456_; 
v_pos_4453_ = lean_ctor_get(v___x_4452_, 0);
v_snd_4454_ = lean_ctor_get(v_pos_4448_, 1);
lean_inc(v_snd_4454_);
lean_dec(v_pos_4448_);
v_snd_4455_ = lean_ctor_get(v_pos_4453_, 1);
v_decide_4456_ = lean_nat_dec_eq(v_snd_4454_, v_snd_4455_);
lean_dec(v_snd_4454_);
if (v_decide_4456_ == 0)
{
return v___x_4452_;
}
else
{
lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4464_; 
lean_inc(v_pos_4453_);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4464_ == 0)
{
lean_object* v_unused_4465_; lean_object* v_unused_4466_; 
v_unused_4465_ = lean_ctor_get(v___x_4452_, 1);
lean_dec(v_unused_4465_);
v_unused_4466_ = lean_ctor_get(v___x_4452_, 0);
lean_dec(v_unused_4466_);
v___x_4458_ = v___x_4452_;
v_isShared_4459_ = v_isSharedCheck_4464_;
goto v_resetjp_4457_;
}
else
{
lean_dec(v___x_4452_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4464_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4460_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4459_ == 0)
{
lean_ctor_set_tag(v___x_4458_, 0);
lean_ctor_set(v___x_4458_, 1, v___x_4460_);
v___x_4462_ = v___x_4458_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_pos_4453_);
lean_ctor_set(v_reuseFailAlloc_4463_, 1, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
else
{
lean_object* v_pos_4467_; lean_object* v_err_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
v_pos_4467_ = lean_ctor_get(v___x_4447_, 0);
v_err_4468_ = lean_ctor_get(v___x_4447_, 1);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4447_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_err_4468_);
lean_inc(v_pos_4467_);
lean_dec(v___x_4447_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_pos_4467_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v_err_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
default: 
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
lean_inc_ref(v_a_3772_);
v___x_4477_ = l_Std_Internal_Parsec_String_pstring(v___x_4476_, v_a_3772_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_pos_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4486_; 
lean_dec_ref(v_a_3772_);
v_pos_4478_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4486_ == 0)
{
lean_object* v_unused_4487_; 
v_unused_4487_ = lean_ctor_get(v___x_4477_, 1);
lean_dec(v_unused_4487_);
v___x_4480_ = v___x_4477_;
v_isShared_4481_ = v_isSharedCheck_4486_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_pos_4478_);
lean_dec(v___x_4477_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4486_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4482_; lean_object* v___x_4484_; 
v___x_4482_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 1, v___x_4482_);
v___x_4484_ = v___x_4480_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_pos_4478_);
lean_ctor_set(v_reuseFailAlloc_4485_, 1, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
else
{
lean_object* v_pos_4488_; lean_object* v_err_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4502_; 
v_pos_4488_ = lean_ctor_get(v___x_4477_, 0);
v_err_4489_ = lean_ctor_get(v___x_4477_, 1);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4491_ = v___x_4477_;
v_isShared_4492_ = v_isSharedCheck_4502_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_err_4489_);
lean_inc(v_pos_4488_);
lean_dec(v___x_4477_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4502_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v_snd_4493_; lean_object* v_snd_4494_; uint8_t v_decide_4495_; 
v_snd_4493_ = lean_ctor_get(v_a_3772_, 1);
lean_inc(v_snd_4493_);
lean_dec_ref(v_a_3772_);
v_snd_4494_ = lean_ctor_get(v_pos_4488_, 1);
v_decide_4495_ = lean_nat_dec_eq(v_snd_4493_, v_snd_4494_);
lean_dec(v_snd_4493_);
if (v_decide_4495_ == 0)
{
lean_object* v___x_4497_; 
if (v_isShared_4492_ == 0)
{
v___x_4497_ = v___x_4491_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_pos_4488_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v_err_4489_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
else
{
uint8_t v___x_4499_; uint8_t v___x_4500_; lean_object* v___x_4501_; 
lean_del_object(v___x_4491_);
lean_dec(v_err_4489_);
v___x_4499_ = 0;
v___x_4500_ = 2;
v___x_4501_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4499_, v___x_4500_, v_decide_4495_, v_pos_4488_);
return v___x_4501_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_4503_; 
lean_dec_ref(v_x_3771_);
lean_dec_ref(v_config_3770_);
v___x_4503_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3772_);
return v___x_4503_;
}
}
v___jp_3773_:
{
lean_object* v_dateformat_3775_; lean_object* v_symbols_3776_; lean_object* v___x_3777_; 
v_dateformat_3775_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3775_);
lean_dec_ref(v_config_3770_);
v_symbols_3776_ = lean_ctor_get(v_dateformat_3775_, 1);
lean_inc_ref(v_symbols_3776_);
lean_dec_ref(v_dateformat_3775_);
v___x_3777_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_3776_, v___y_3774_);
return v___x_3777_;
}
v___jp_3778_:
{
lean_object* v_dateformat_3780_; lean_object* v_symbols_3781_; lean_object* v___x_3782_; 
v_dateformat_3780_ = lean_ctor_get(v_config_3770_, 0);
lean_inc_ref(v_dateformat_3780_);
lean_dec_ref(v_config_3770_);
v_symbols_3781_ = lean_ctor_get(v_dateformat_3780_, 1);
lean_inc_ref(v_symbols_3781_);
lean_dec_ref(v_dateformat_3780_);
v___x_3782_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_3781_, v___y_3779_);
return v___x_3782_;
}
v___jp_3783_:
{
if (lean_obj_tag(v___y_3784_) == 0)
{
lean_dec_ref(v_a_3772_);
return v___y_3784_;
}
else
{
lean_object* v_pos_3785_; lean_object* v_snd_3786_; lean_object* v_snd_3787_; uint8_t v_decide_3788_; 
v_pos_3785_ = lean_ctor_get(v___y_3784_, 0);
v_snd_3786_ = lean_ctor_get(v_a_3772_, 1);
lean_inc(v_snd_3786_);
lean_dec_ref(v_a_3772_);
v_snd_3787_ = lean_ctor_get(v_pos_3785_, 1);
v_decide_3788_ = lean_nat_dec_eq(v_snd_3786_, v_snd_3787_);
lean_dec(v_snd_3786_);
if (v_decide_3788_ == 0)
{
return v___y_3784_;
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_inc(v_pos_3785_);
lean_dec_ref_known(v___y_3784_, 2);
v___x_3789_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
v___x_3790_ = l_Std_Internal_Parsec_String_pstring(v___x_3789_, v_pos_3785_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_pos_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3799_; 
v_pos_3791_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; 
v_unused_3800_ = lean_ctor_get(v___x_3790_, 1);
lean_dec(v_unused_3800_);
v___x_3793_ = v___x_3790_;
v_isShared_3794_ = v_isSharedCheck_3799_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_pos_3791_);
lean_dec(v___x_3790_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3799_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3795_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 1, v___x_3795_);
v___x_3797_ = v___x_3793_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_pos_3791_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
else
{
lean_object* v_pos_3801_; lean_object* v_err_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
v_pos_3801_ = lean_ctor_get(v___x_3790_, 0);
v_err_3802_ = lean_ctor_get(v___x_3790_, 1);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3790_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_err_3802_);
lean_inc(v_pos_3801_);
lean_dec(v___x_3790_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_pos_3801_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_err_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(lean_object* v_dateformat_4504_, lean_object* v_date_4505_, lean_object* v_part_4506_){
_start:
{
if (lean_obj_tag(v_part_4506_) == 0)
{
lean_object* v_val_4507_; 
lean_dec_ref(v_date_4505_);
v_val_4507_ = lean_ctor_get(v_part_4506_, 0);
lean_inc_ref(v_val_4507_);
lean_dec_ref_known(v_part_4506_, 1);
return v_val_4507_;
}
else
{
lean_object* v_modifier_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v_modifier_4508_ = lean_ctor_get(v_part_4506_, 0);
lean_inc_ref(v_modifier_4508_);
lean_dec_ref_known(v_part_4506_, 1);
v___x_4509_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_4508_, v_dateformat_4504_, v_date_4505_);
v___x_4510_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_4504_, v_modifier_4508_, v___x_4509_);
return v___x_4510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate___boxed(lean_object* v_dateformat_4511_, lean_object* v_date_4512_, lean_object* v_part_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_4511_, v_date_4512_, v_part_4513_);
lean_dec_ref(v_dateformat_4511_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object* v_date_4515_, lean_object* v_modifier_4516_, lean_object* v_data_4517_){
_start:
{
switch(lean_obj_tag(v_modifier_4516_))
{
case 0:
{
lean_object* v_y_4518_; lean_object* v_u_4519_; lean_object* v_Y_4520_; lean_object* v_D_4521_; lean_object* v_M_4522_; lean_object* v_L_4523_; lean_object* v_d_4524_; lean_object* v_Q_4525_; lean_object* v_q_4526_; lean_object* v_w_4527_; lean_object* v_W_4528_; lean_object* v_E_4529_; lean_object* v_e_4530_; lean_object* v_c_4531_; lean_object* v_F_4532_; lean_object* v_a_4533_; lean_object* v_b_4534_; lean_object* v_B_4535_; lean_object* v_h_4536_; lean_object* v_K_4537_; lean_object* v_k_4538_; lean_object* v_H_4539_; lean_object* v_m_4540_; lean_object* v_s_4541_; lean_object* v_S_4542_; lean_object* v_A_4543_; lean_object* v_n_4544_; lean_object* v_N_4545_; lean_object* v_V_4546_; lean_object* v_z_4547_; lean_object* v_zabbrev_4548_; lean_object* v_v_4549_; lean_object* v_O_4550_; lean_object* v_X_4551_; lean_object* v_x_4552_; lean_object* v_Z_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4561_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_y_4518_ = lean_ctor_get(v_date_4515_, 1);
v_u_4519_ = lean_ctor_get(v_date_4515_, 2);
v_Y_4520_ = lean_ctor_get(v_date_4515_, 3);
v_D_4521_ = lean_ctor_get(v_date_4515_, 4);
v_M_4522_ = lean_ctor_get(v_date_4515_, 5);
v_L_4523_ = lean_ctor_get(v_date_4515_, 6);
v_d_4524_ = lean_ctor_get(v_date_4515_, 7);
v_Q_4525_ = lean_ctor_get(v_date_4515_, 8);
v_q_4526_ = lean_ctor_get(v_date_4515_, 9);
v_w_4527_ = lean_ctor_get(v_date_4515_, 10);
v_W_4528_ = lean_ctor_get(v_date_4515_, 11);
v_E_4529_ = lean_ctor_get(v_date_4515_, 12);
v_e_4530_ = lean_ctor_get(v_date_4515_, 13);
v_c_4531_ = lean_ctor_get(v_date_4515_, 14);
v_F_4532_ = lean_ctor_get(v_date_4515_, 15);
v_a_4533_ = lean_ctor_get(v_date_4515_, 16);
v_b_4534_ = lean_ctor_get(v_date_4515_, 17);
v_B_4535_ = lean_ctor_get(v_date_4515_, 18);
v_h_4536_ = lean_ctor_get(v_date_4515_, 19);
v_K_4537_ = lean_ctor_get(v_date_4515_, 20);
v_k_4538_ = lean_ctor_get(v_date_4515_, 21);
v_H_4539_ = lean_ctor_get(v_date_4515_, 22);
v_m_4540_ = lean_ctor_get(v_date_4515_, 23);
v_s_4541_ = lean_ctor_get(v_date_4515_, 24);
v_S_4542_ = lean_ctor_get(v_date_4515_, 25);
v_A_4543_ = lean_ctor_get(v_date_4515_, 26);
v_n_4544_ = lean_ctor_get(v_date_4515_, 27);
v_N_4545_ = lean_ctor_get(v_date_4515_, 28);
v_V_4546_ = lean_ctor_get(v_date_4515_, 29);
v_z_4547_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_4548_ = lean_ctor_get(v_date_4515_, 31);
v_v_4549_ = lean_ctor_get(v_date_4515_, 32);
v_O_4550_ = lean_ctor_get(v_date_4515_, 33);
v_X_4551_ = lean_ctor_get(v_date_4515_, 34);
v_x_4552_ = lean_ctor_get(v_date_4515_, 35);
v_Z_4553_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_4561_ == 0)
{
lean_object* v_unused_4562_; 
v_unused_4562_ = lean_ctor_get(v_date_4515_, 0);
lean_dec(v_unused_4562_);
v___x_4555_ = v_date_4515_;
v_isShared_4556_ = v_isSharedCheck_4561_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_Z_4553_);
lean_inc(v_x_4552_);
lean_inc(v_X_4551_);
lean_inc(v_O_4550_);
lean_inc(v_v_4549_);
lean_inc(v_zabbrev_4548_);
lean_inc(v_z_4547_);
lean_inc(v_V_4546_);
lean_inc(v_N_4545_);
lean_inc(v_n_4544_);
lean_inc(v_A_4543_);
lean_inc(v_S_4542_);
lean_inc(v_s_4541_);
lean_inc(v_m_4540_);
lean_inc(v_H_4539_);
lean_inc(v_k_4538_);
lean_inc(v_K_4537_);
lean_inc(v_h_4536_);
lean_inc(v_B_4535_);
lean_inc(v_b_4534_);
lean_inc(v_a_4533_);
lean_inc(v_F_4532_);
lean_inc(v_c_4531_);
lean_inc(v_e_4530_);
lean_inc(v_E_4529_);
lean_inc(v_W_4528_);
lean_inc(v_w_4527_);
lean_inc(v_q_4526_);
lean_inc(v_Q_4525_);
lean_inc(v_d_4524_);
lean_inc(v_L_4523_);
lean_inc(v_M_4522_);
lean_inc(v_D_4521_);
lean_inc(v_Y_4520_);
lean_inc(v_u_4519_);
lean_inc(v_y_4518_);
lean_dec(v_date_4515_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4561_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4557_; lean_object* v___x_4559_; 
v___x_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4557_, 0, v_data_4517_);
if (v_isShared_4556_ == 0)
{
lean_ctor_set(v___x_4555_, 0, v___x_4557_);
v___x_4559_ = v___x_4555_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v_y_4518_);
lean_ctor_set(v_reuseFailAlloc_4560_, 2, v_u_4519_);
lean_ctor_set(v_reuseFailAlloc_4560_, 3, v_Y_4520_);
lean_ctor_set(v_reuseFailAlloc_4560_, 4, v_D_4521_);
lean_ctor_set(v_reuseFailAlloc_4560_, 5, v_M_4522_);
lean_ctor_set(v_reuseFailAlloc_4560_, 6, v_L_4523_);
lean_ctor_set(v_reuseFailAlloc_4560_, 7, v_d_4524_);
lean_ctor_set(v_reuseFailAlloc_4560_, 8, v_Q_4525_);
lean_ctor_set(v_reuseFailAlloc_4560_, 9, v_q_4526_);
lean_ctor_set(v_reuseFailAlloc_4560_, 10, v_w_4527_);
lean_ctor_set(v_reuseFailAlloc_4560_, 11, v_W_4528_);
lean_ctor_set(v_reuseFailAlloc_4560_, 12, v_E_4529_);
lean_ctor_set(v_reuseFailAlloc_4560_, 13, v_e_4530_);
lean_ctor_set(v_reuseFailAlloc_4560_, 14, v_c_4531_);
lean_ctor_set(v_reuseFailAlloc_4560_, 15, v_F_4532_);
lean_ctor_set(v_reuseFailAlloc_4560_, 16, v_a_4533_);
lean_ctor_set(v_reuseFailAlloc_4560_, 17, v_b_4534_);
lean_ctor_set(v_reuseFailAlloc_4560_, 18, v_B_4535_);
lean_ctor_set(v_reuseFailAlloc_4560_, 19, v_h_4536_);
lean_ctor_set(v_reuseFailAlloc_4560_, 20, v_K_4537_);
lean_ctor_set(v_reuseFailAlloc_4560_, 21, v_k_4538_);
lean_ctor_set(v_reuseFailAlloc_4560_, 22, v_H_4539_);
lean_ctor_set(v_reuseFailAlloc_4560_, 23, v_m_4540_);
lean_ctor_set(v_reuseFailAlloc_4560_, 24, v_s_4541_);
lean_ctor_set(v_reuseFailAlloc_4560_, 25, v_S_4542_);
lean_ctor_set(v_reuseFailAlloc_4560_, 26, v_A_4543_);
lean_ctor_set(v_reuseFailAlloc_4560_, 27, v_n_4544_);
lean_ctor_set(v_reuseFailAlloc_4560_, 28, v_N_4545_);
lean_ctor_set(v_reuseFailAlloc_4560_, 29, v_V_4546_);
lean_ctor_set(v_reuseFailAlloc_4560_, 30, v_z_4547_);
lean_ctor_set(v_reuseFailAlloc_4560_, 31, v_zabbrev_4548_);
lean_ctor_set(v_reuseFailAlloc_4560_, 32, v_v_4549_);
lean_ctor_set(v_reuseFailAlloc_4560_, 33, v_O_4550_);
lean_ctor_set(v_reuseFailAlloc_4560_, 34, v_X_4551_);
lean_ctor_set(v_reuseFailAlloc_4560_, 35, v_x_4552_);
lean_ctor_set(v_reuseFailAlloc_4560_, 36, v_Z_4553_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
case 1:
{
lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4613_; 
v_isSharedCheck_4613_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_4613_ == 0)
{
lean_object* v_unused_4614_; 
v_unused_4614_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_4614_);
v___x_4564_ = v_modifier_4516_;
v_isShared_4565_ = v_isSharedCheck_4613_;
goto v_resetjp_4563_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4613_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v_G_4566_; lean_object* v_y_4567_; lean_object* v_Y_4568_; lean_object* v_D_4569_; lean_object* v_M_4570_; lean_object* v_L_4571_; lean_object* v_d_4572_; lean_object* v_Q_4573_; lean_object* v_q_4574_; lean_object* v_w_4575_; lean_object* v_W_4576_; lean_object* v_E_4577_; lean_object* v_e_4578_; lean_object* v_c_4579_; lean_object* v_F_4580_; lean_object* v_a_4581_; lean_object* v_b_4582_; lean_object* v_B_4583_; lean_object* v_h_4584_; lean_object* v_K_4585_; lean_object* v_k_4586_; lean_object* v_H_4587_; lean_object* v_m_4588_; lean_object* v_s_4589_; lean_object* v_S_4590_; lean_object* v_A_4591_; lean_object* v_n_4592_; lean_object* v_N_4593_; lean_object* v_V_4594_; lean_object* v_z_4595_; lean_object* v_zabbrev_4596_; lean_object* v_v_4597_; lean_object* v_O_4598_; lean_object* v_X_4599_; lean_object* v_x_4600_; lean_object* v_Z_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4611_; 
v_G_4566_ = lean_ctor_get(v_date_4515_, 0);
v_y_4567_ = lean_ctor_get(v_date_4515_, 1);
v_Y_4568_ = lean_ctor_get(v_date_4515_, 3);
v_D_4569_ = lean_ctor_get(v_date_4515_, 4);
v_M_4570_ = lean_ctor_get(v_date_4515_, 5);
v_L_4571_ = lean_ctor_get(v_date_4515_, 6);
v_d_4572_ = lean_ctor_get(v_date_4515_, 7);
v_Q_4573_ = lean_ctor_get(v_date_4515_, 8);
v_q_4574_ = lean_ctor_get(v_date_4515_, 9);
v_w_4575_ = lean_ctor_get(v_date_4515_, 10);
v_W_4576_ = lean_ctor_get(v_date_4515_, 11);
v_E_4577_ = lean_ctor_get(v_date_4515_, 12);
v_e_4578_ = lean_ctor_get(v_date_4515_, 13);
v_c_4579_ = lean_ctor_get(v_date_4515_, 14);
v_F_4580_ = lean_ctor_get(v_date_4515_, 15);
v_a_4581_ = lean_ctor_get(v_date_4515_, 16);
v_b_4582_ = lean_ctor_get(v_date_4515_, 17);
v_B_4583_ = lean_ctor_get(v_date_4515_, 18);
v_h_4584_ = lean_ctor_get(v_date_4515_, 19);
v_K_4585_ = lean_ctor_get(v_date_4515_, 20);
v_k_4586_ = lean_ctor_get(v_date_4515_, 21);
v_H_4587_ = lean_ctor_get(v_date_4515_, 22);
v_m_4588_ = lean_ctor_get(v_date_4515_, 23);
v_s_4589_ = lean_ctor_get(v_date_4515_, 24);
v_S_4590_ = lean_ctor_get(v_date_4515_, 25);
v_A_4591_ = lean_ctor_get(v_date_4515_, 26);
v_n_4592_ = lean_ctor_get(v_date_4515_, 27);
v_N_4593_ = lean_ctor_get(v_date_4515_, 28);
v_V_4594_ = lean_ctor_get(v_date_4515_, 29);
v_z_4595_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_4596_ = lean_ctor_get(v_date_4515_, 31);
v_v_4597_ = lean_ctor_get(v_date_4515_, 32);
v_O_4598_ = lean_ctor_get(v_date_4515_, 33);
v_X_4599_ = lean_ctor_get(v_date_4515_, 34);
v_x_4600_ = lean_ctor_get(v_date_4515_, 35);
v_Z_4601_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_4611_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_4611_ == 0)
{
lean_object* v_unused_4612_; 
v_unused_4612_ = lean_ctor_get(v_date_4515_, 2);
lean_dec(v_unused_4612_);
v___x_4603_ = v_date_4515_;
v_isShared_4604_ = v_isSharedCheck_4611_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_Z_4601_);
lean_inc(v_x_4600_);
lean_inc(v_X_4599_);
lean_inc(v_O_4598_);
lean_inc(v_v_4597_);
lean_inc(v_zabbrev_4596_);
lean_inc(v_z_4595_);
lean_inc(v_V_4594_);
lean_inc(v_N_4593_);
lean_inc(v_n_4592_);
lean_inc(v_A_4591_);
lean_inc(v_S_4590_);
lean_inc(v_s_4589_);
lean_inc(v_m_4588_);
lean_inc(v_H_4587_);
lean_inc(v_k_4586_);
lean_inc(v_K_4585_);
lean_inc(v_h_4584_);
lean_inc(v_B_4583_);
lean_inc(v_b_4582_);
lean_inc(v_a_4581_);
lean_inc(v_F_4580_);
lean_inc(v_c_4579_);
lean_inc(v_e_4578_);
lean_inc(v_E_4577_);
lean_inc(v_W_4576_);
lean_inc(v_w_4575_);
lean_inc(v_q_4574_);
lean_inc(v_Q_4573_);
lean_inc(v_d_4572_);
lean_inc(v_L_4571_);
lean_inc(v_M_4570_);
lean_inc(v_D_4569_);
lean_inc(v_Y_4568_);
lean_inc(v_y_4567_);
lean_inc(v_G_4566_);
lean_dec(v_date_4515_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4611_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v_data_4517_);
v___x_4606_ = v___x_4564_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_data_4517_);
v___x_4606_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
lean_object* v___x_4608_; 
if (v_isShared_4604_ == 0)
{
lean_ctor_set(v___x_4603_, 2, v___x_4606_);
v___x_4608_ = v___x_4603_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_G_4566_);
lean_ctor_set(v_reuseFailAlloc_4609_, 1, v_y_4567_);
lean_ctor_set(v_reuseFailAlloc_4609_, 2, v___x_4606_);
lean_ctor_set(v_reuseFailAlloc_4609_, 3, v_Y_4568_);
lean_ctor_set(v_reuseFailAlloc_4609_, 4, v_D_4569_);
lean_ctor_set(v_reuseFailAlloc_4609_, 5, v_M_4570_);
lean_ctor_set(v_reuseFailAlloc_4609_, 6, v_L_4571_);
lean_ctor_set(v_reuseFailAlloc_4609_, 7, v_d_4572_);
lean_ctor_set(v_reuseFailAlloc_4609_, 8, v_Q_4573_);
lean_ctor_set(v_reuseFailAlloc_4609_, 9, v_q_4574_);
lean_ctor_set(v_reuseFailAlloc_4609_, 10, v_w_4575_);
lean_ctor_set(v_reuseFailAlloc_4609_, 11, v_W_4576_);
lean_ctor_set(v_reuseFailAlloc_4609_, 12, v_E_4577_);
lean_ctor_set(v_reuseFailAlloc_4609_, 13, v_e_4578_);
lean_ctor_set(v_reuseFailAlloc_4609_, 14, v_c_4579_);
lean_ctor_set(v_reuseFailAlloc_4609_, 15, v_F_4580_);
lean_ctor_set(v_reuseFailAlloc_4609_, 16, v_a_4581_);
lean_ctor_set(v_reuseFailAlloc_4609_, 17, v_b_4582_);
lean_ctor_set(v_reuseFailAlloc_4609_, 18, v_B_4583_);
lean_ctor_set(v_reuseFailAlloc_4609_, 19, v_h_4584_);
lean_ctor_set(v_reuseFailAlloc_4609_, 20, v_K_4585_);
lean_ctor_set(v_reuseFailAlloc_4609_, 21, v_k_4586_);
lean_ctor_set(v_reuseFailAlloc_4609_, 22, v_H_4587_);
lean_ctor_set(v_reuseFailAlloc_4609_, 23, v_m_4588_);
lean_ctor_set(v_reuseFailAlloc_4609_, 24, v_s_4589_);
lean_ctor_set(v_reuseFailAlloc_4609_, 25, v_S_4590_);
lean_ctor_set(v_reuseFailAlloc_4609_, 26, v_A_4591_);
lean_ctor_set(v_reuseFailAlloc_4609_, 27, v_n_4592_);
lean_ctor_set(v_reuseFailAlloc_4609_, 28, v_N_4593_);
lean_ctor_set(v_reuseFailAlloc_4609_, 29, v_V_4594_);
lean_ctor_set(v_reuseFailAlloc_4609_, 30, v_z_4595_);
lean_ctor_set(v_reuseFailAlloc_4609_, 31, v_zabbrev_4596_);
lean_ctor_set(v_reuseFailAlloc_4609_, 32, v_v_4597_);
lean_ctor_set(v_reuseFailAlloc_4609_, 33, v_O_4598_);
lean_ctor_set(v_reuseFailAlloc_4609_, 34, v_X_4599_);
lean_ctor_set(v_reuseFailAlloc_4609_, 35, v_x_4600_);
lean_ctor_set(v_reuseFailAlloc_4609_, 36, v_Z_4601_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
}
case 2:
{
lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4665_; 
v_isSharedCheck_4665_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_4665_ == 0)
{
lean_object* v_unused_4666_; 
v_unused_4666_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_4666_);
v___x_4616_ = v_modifier_4516_;
v_isShared_4617_ = v_isSharedCheck_4665_;
goto v_resetjp_4615_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4665_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v_G_4618_; lean_object* v_u_4619_; lean_object* v_Y_4620_; lean_object* v_D_4621_; lean_object* v_M_4622_; lean_object* v_L_4623_; lean_object* v_d_4624_; lean_object* v_Q_4625_; lean_object* v_q_4626_; lean_object* v_w_4627_; lean_object* v_W_4628_; lean_object* v_E_4629_; lean_object* v_e_4630_; lean_object* v_c_4631_; lean_object* v_F_4632_; lean_object* v_a_4633_; lean_object* v_b_4634_; lean_object* v_B_4635_; lean_object* v_h_4636_; lean_object* v_K_4637_; lean_object* v_k_4638_; lean_object* v_H_4639_; lean_object* v_m_4640_; lean_object* v_s_4641_; lean_object* v_S_4642_; lean_object* v_A_4643_; lean_object* v_n_4644_; lean_object* v_N_4645_; lean_object* v_V_4646_; lean_object* v_z_4647_; lean_object* v_zabbrev_4648_; lean_object* v_v_4649_; lean_object* v_O_4650_; lean_object* v_X_4651_; lean_object* v_x_4652_; lean_object* v_Z_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4663_; 
v_G_4618_ = lean_ctor_get(v_date_4515_, 0);
v_u_4619_ = lean_ctor_get(v_date_4515_, 2);
v_Y_4620_ = lean_ctor_get(v_date_4515_, 3);
v_D_4621_ = lean_ctor_get(v_date_4515_, 4);
v_M_4622_ = lean_ctor_get(v_date_4515_, 5);
v_L_4623_ = lean_ctor_get(v_date_4515_, 6);
v_d_4624_ = lean_ctor_get(v_date_4515_, 7);
v_Q_4625_ = lean_ctor_get(v_date_4515_, 8);
v_q_4626_ = lean_ctor_get(v_date_4515_, 9);
v_w_4627_ = lean_ctor_get(v_date_4515_, 10);
v_W_4628_ = lean_ctor_get(v_date_4515_, 11);
v_E_4629_ = lean_ctor_get(v_date_4515_, 12);
v_e_4630_ = lean_ctor_get(v_date_4515_, 13);
v_c_4631_ = lean_ctor_get(v_date_4515_, 14);
v_F_4632_ = lean_ctor_get(v_date_4515_, 15);
v_a_4633_ = lean_ctor_get(v_date_4515_, 16);
v_b_4634_ = lean_ctor_get(v_date_4515_, 17);
v_B_4635_ = lean_ctor_get(v_date_4515_, 18);
v_h_4636_ = lean_ctor_get(v_date_4515_, 19);
v_K_4637_ = lean_ctor_get(v_date_4515_, 20);
v_k_4638_ = lean_ctor_get(v_date_4515_, 21);
v_H_4639_ = lean_ctor_get(v_date_4515_, 22);
v_m_4640_ = lean_ctor_get(v_date_4515_, 23);
v_s_4641_ = lean_ctor_get(v_date_4515_, 24);
v_S_4642_ = lean_ctor_get(v_date_4515_, 25);
v_A_4643_ = lean_ctor_get(v_date_4515_, 26);
v_n_4644_ = lean_ctor_get(v_date_4515_, 27);
v_N_4645_ = lean_ctor_get(v_date_4515_, 28);
v_V_4646_ = lean_ctor_get(v_date_4515_, 29);
v_z_4647_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_4648_ = lean_ctor_get(v_date_4515_, 31);
v_v_4649_ = lean_ctor_get(v_date_4515_, 32);
v_O_4650_ = lean_ctor_get(v_date_4515_, 33);
v_X_4651_ = lean_ctor_get(v_date_4515_, 34);
v_x_4652_ = lean_ctor_get(v_date_4515_, 35);
v_Z_4653_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_4663_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_4663_ == 0)
{
lean_object* v_unused_4664_; 
v_unused_4664_ = lean_ctor_get(v_date_4515_, 1);
lean_dec(v_unused_4664_);
v___x_4655_ = v_date_4515_;
v_isShared_4656_ = v_isSharedCheck_4663_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_Z_4653_);
lean_inc(v_x_4652_);
lean_inc(v_X_4651_);
lean_inc(v_O_4650_);
lean_inc(v_v_4649_);
lean_inc(v_zabbrev_4648_);
lean_inc(v_z_4647_);
lean_inc(v_V_4646_);
lean_inc(v_N_4645_);
lean_inc(v_n_4644_);
lean_inc(v_A_4643_);
lean_inc(v_S_4642_);
lean_inc(v_s_4641_);
lean_inc(v_m_4640_);
lean_inc(v_H_4639_);
lean_inc(v_k_4638_);
lean_inc(v_K_4637_);
lean_inc(v_h_4636_);
lean_inc(v_B_4635_);
lean_inc(v_b_4634_);
lean_inc(v_a_4633_);
lean_inc(v_F_4632_);
lean_inc(v_c_4631_);
lean_inc(v_e_4630_);
lean_inc(v_E_4629_);
lean_inc(v_W_4628_);
lean_inc(v_w_4627_);
lean_inc(v_q_4626_);
lean_inc(v_Q_4625_);
lean_inc(v_d_4624_);
lean_inc(v_L_4623_);
lean_inc(v_M_4622_);
lean_inc(v_D_4621_);
lean_inc(v_Y_4620_);
lean_inc(v_u_4619_);
lean_inc(v_G_4618_);
lean_dec(v_date_4515_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4663_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4617_ == 0)
{
lean_ctor_set_tag(v___x_4616_, 1);
lean_ctor_set(v___x_4616_, 0, v_data_4517_);
v___x_4658_ = v___x_4616_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_data_4517_);
v___x_4658_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
lean_object* v___x_4660_; 
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 1, v___x_4658_);
v___x_4660_ = v___x_4655_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_G_4618_);
lean_ctor_set(v_reuseFailAlloc_4661_, 1, v___x_4658_);
lean_ctor_set(v_reuseFailAlloc_4661_, 2, v_u_4619_);
lean_ctor_set(v_reuseFailAlloc_4661_, 3, v_Y_4620_);
lean_ctor_set(v_reuseFailAlloc_4661_, 4, v_D_4621_);
lean_ctor_set(v_reuseFailAlloc_4661_, 5, v_M_4622_);
lean_ctor_set(v_reuseFailAlloc_4661_, 6, v_L_4623_);
lean_ctor_set(v_reuseFailAlloc_4661_, 7, v_d_4624_);
lean_ctor_set(v_reuseFailAlloc_4661_, 8, v_Q_4625_);
lean_ctor_set(v_reuseFailAlloc_4661_, 9, v_q_4626_);
lean_ctor_set(v_reuseFailAlloc_4661_, 10, v_w_4627_);
lean_ctor_set(v_reuseFailAlloc_4661_, 11, v_W_4628_);
lean_ctor_set(v_reuseFailAlloc_4661_, 12, v_E_4629_);
lean_ctor_set(v_reuseFailAlloc_4661_, 13, v_e_4630_);
lean_ctor_set(v_reuseFailAlloc_4661_, 14, v_c_4631_);
lean_ctor_set(v_reuseFailAlloc_4661_, 15, v_F_4632_);
lean_ctor_set(v_reuseFailAlloc_4661_, 16, v_a_4633_);
lean_ctor_set(v_reuseFailAlloc_4661_, 17, v_b_4634_);
lean_ctor_set(v_reuseFailAlloc_4661_, 18, v_B_4635_);
lean_ctor_set(v_reuseFailAlloc_4661_, 19, v_h_4636_);
lean_ctor_set(v_reuseFailAlloc_4661_, 20, v_K_4637_);
lean_ctor_set(v_reuseFailAlloc_4661_, 21, v_k_4638_);
lean_ctor_set(v_reuseFailAlloc_4661_, 22, v_H_4639_);
lean_ctor_set(v_reuseFailAlloc_4661_, 23, v_m_4640_);
lean_ctor_set(v_reuseFailAlloc_4661_, 24, v_s_4641_);
lean_ctor_set(v_reuseFailAlloc_4661_, 25, v_S_4642_);
lean_ctor_set(v_reuseFailAlloc_4661_, 26, v_A_4643_);
lean_ctor_set(v_reuseFailAlloc_4661_, 27, v_n_4644_);
lean_ctor_set(v_reuseFailAlloc_4661_, 28, v_N_4645_);
lean_ctor_set(v_reuseFailAlloc_4661_, 29, v_V_4646_);
lean_ctor_set(v_reuseFailAlloc_4661_, 30, v_z_4647_);
lean_ctor_set(v_reuseFailAlloc_4661_, 31, v_zabbrev_4648_);
lean_ctor_set(v_reuseFailAlloc_4661_, 32, v_v_4649_);
lean_ctor_set(v_reuseFailAlloc_4661_, 33, v_O_4650_);
lean_ctor_set(v_reuseFailAlloc_4661_, 34, v_X_4651_);
lean_ctor_set(v_reuseFailAlloc_4661_, 35, v_x_4652_);
lean_ctor_set(v_reuseFailAlloc_4661_, 36, v_Z_4653_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
}
case 3:
{
lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4717_; 
v_isSharedCheck_4717_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_4717_ == 0)
{
lean_object* v_unused_4718_; 
v_unused_4718_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_4718_);
v___x_4668_ = v_modifier_4516_;
v_isShared_4669_ = v_isSharedCheck_4717_;
goto v_resetjp_4667_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4717_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v_G_4670_; lean_object* v_y_4671_; lean_object* v_u_4672_; lean_object* v_Y_4673_; lean_object* v_M_4674_; lean_object* v_L_4675_; lean_object* v_d_4676_; lean_object* v_Q_4677_; lean_object* v_q_4678_; lean_object* v_w_4679_; lean_object* v_W_4680_; lean_object* v_E_4681_; lean_object* v_e_4682_; lean_object* v_c_4683_; lean_object* v_F_4684_; lean_object* v_a_4685_; lean_object* v_b_4686_; lean_object* v_B_4687_; lean_object* v_h_4688_; lean_object* v_K_4689_; lean_object* v_k_4690_; lean_object* v_H_4691_; lean_object* v_m_4692_; lean_object* v_s_4693_; lean_object* v_S_4694_; lean_object* v_A_4695_; lean_object* v_n_4696_; lean_object* v_N_4697_; lean_object* v_V_4698_; lean_object* v_z_4699_; lean_object* v_zabbrev_4700_; lean_object* v_v_4701_; lean_object* v_O_4702_; lean_object* v_X_4703_; lean_object* v_x_4704_; lean_object* v_Z_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4715_; 
v_G_4670_ = lean_ctor_get(v_date_4515_, 0);
v_y_4671_ = lean_ctor_get(v_date_4515_, 1);
v_u_4672_ = lean_ctor_get(v_date_4515_, 2);
v_Y_4673_ = lean_ctor_get(v_date_4515_, 3);
v_M_4674_ = lean_ctor_get(v_date_4515_, 5);
v_L_4675_ = lean_ctor_get(v_date_4515_, 6);
v_d_4676_ = lean_ctor_get(v_date_4515_, 7);
v_Q_4677_ = lean_ctor_get(v_date_4515_, 8);
v_q_4678_ = lean_ctor_get(v_date_4515_, 9);
v_w_4679_ = lean_ctor_get(v_date_4515_, 10);
v_W_4680_ = lean_ctor_get(v_date_4515_, 11);
v_E_4681_ = lean_ctor_get(v_date_4515_, 12);
v_e_4682_ = lean_ctor_get(v_date_4515_, 13);
v_c_4683_ = lean_ctor_get(v_date_4515_, 14);
v_F_4684_ = lean_ctor_get(v_date_4515_, 15);
v_a_4685_ = lean_ctor_get(v_date_4515_, 16);
v_b_4686_ = lean_ctor_get(v_date_4515_, 17);
v_B_4687_ = lean_ctor_get(v_date_4515_, 18);
v_h_4688_ = lean_ctor_get(v_date_4515_, 19);
v_K_4689_ = lean_ctor_get(v_date_4515_, 20);
v_k_4690_ = lean_ctor_get(v_date_4515_, 21);
v_H_4691_ = lean_ctor_get(v_date_4515_, 22);
v_m_4692_ = lean_ctor_get(v_date_4515_, 23);
v_s_4693_ = lean_ctor_get(v_date_4515_, 24);
v_S_4694_ = lean_ctor_get(v_date_4515_, 25);
v_A_4695_ = lean_ctor_get(v_date_4515_, 26);
v_n_4696_ = lean_ctor_get(v_date_4515_, 27);
v_N_4697_ = lean_ctor_get(v_date_4515_, 28);
v_V_4698_ = lean_ctor_get(v_date_4515_, 29);
v_z_4699_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_4700_ = lean_ctor_get(v_date_4515_, 31);
v_v_4701_ = lean_ctor_get(v_date_4515_, 32);
v_O_4702_ = lean_ctor_get(v_date_4515_, 33);
v_X_4703_ = lean_ctor_get(v_date_4515_, 34);
v_x_4704_ = lean_ctor_get(v_date_4515_, 35);
v_Z_4705_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_4715_ == 0)
{
lean_object* v_unused_4716_; 
v_unused_4716_ = lean_ctor_get(v_date_4515_, 4);
lean_dec(v_unused_4716_);
v___x_4707_ = v_date_4515_;
v_isShared_4708_ = v_isSharedCheck_4715_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_Z_4705_);
lean_inc(v_x_4704_);
lean_inc(v_X_4703_);
lean_inc(v_O_4702_);
lean_inc(v_v_4701_);
lean_inc(v_zabbrev_4700_);
lean_inc(v_z_4699_);
lean_inc(v_V_4698_);
lean_inc(v_N_4697_);
lean_inc(v_n_4696_);
lean_inc(v_A_4695_);
lean_inc(v_S_4694_);
lean_inc(v_s_4693_);
lean_inc(v_m_4692_);
lean_inc(v_H_4691_);
lean_inc(v_k_4690_);
lean_inc(v_K_4689_);
lean_inc(v_h_4688_);
lean_inc(v_B_4687_);
lean_inc(v_b_4686_);
lean_inc(v_a_4685_);
lean_inc(v_F_4684_);
lean_inc(v_c_4683_);
lean_inc(v_e_4682_);
lean_inc(v_E_4681_);
lean_inc(v_W_4680_);
lean_inc(v_w_4679_);
lean_inc(v_q_4678_);
lean_inc(v_Q_4677_);
lean_inc(v_d_4676_);
lean_inc(v_L_4675_);
lean_inc(v_M_4674_);
lean_inc(v_Y_4673_);
lean_inc(v_u_4672_);
lean_inc(v_y_4671_);
lean_inc(v_G_4670_);
lean_dec(v_date_4515_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4715_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4669_ == 0)
{
lean_ctor_set_tag(v___x_4668_, 1);
lean_ctor_set(v___x_4668_, 0, v_data_4517_);
v___x_4710_ = v___x_4668_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_data_4517_);
v___x_4710_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4712_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 4, v___x_4710_);
v___x_4712_ = v___x_4707_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_G_4670_);
lean_ctor_set(v_reuseFailAlloc_4713_, 1, v_y_4671_);
lean_ctor_set(v_reuseFailAlloc_4713_, 2, v_u_4672_);
lean_ctor_set(v_reuseFailAlloc_4713_, 3, v_Y_4673_);
lean_ctor_set(v_reuseFailAlloc_4713_, 4, v___x_4710_);
lean_ctor_set(v_reuseFailAlloc_4713_, 5, v_M_4674_);
lean_ctor_set(v_reuseFailAlloc_4713_, 6, v_L_4675_);
lean_ctor_set(v_reuseFailAlloc_4713_, 7, v_d_4676_);
lean_ctor_set(v_reuseFailAlloc_4713_, 8, v_Q_4677_);
lean_ctor_set(v_reuseFailAlloc_4713_, 9, v_q_4678_);
lean_ctor_set(v_reuseFailAlloc_4713_, 10, v_w_4679_);
lean_ctor_set(v_reuseFailAlloc_4713_, 11, v_W_4680_);
lean_ctor_set(v_reuseFailAlloc_4713_, 12, v_E_4681_);
lean_ctor_set(v_reuseFailAlloc_4713_, 13, v_e_4682_);
lean_ctor_set(v_reuseFailAlloc_4713_, 14, v_c_4683_);
lean_ctor_set(v_reuseFailAlloc_4713_, 15, v_F_4684_);
lean_ctor_set(v_reuseFailAlloc_4713_, 16, v_a_4685_);
lean_ctor_set(v_reuseFailAlloc_4713_, 17, v_b_4686_);
lean_ctor_set(v_reuseFailAlloc_4713_, 18, v_B_4687_);
lean_ctor_set(v_reuseFailAlloc_4713_, 19, v_h_4688_);
lean_ctor_set(v_reuseFailAlloc_4713_, 20, v_K_4689_);
lean_ctor_set(v_reuseFailAlloc_4713_, 21, v_k_4690_);
lean_ctor_set(v_reuseFailAlloc_4713_, 22, v_H_4691_);
lean_ctor_set(v_reuseFailAlloc_4713_, 23, v_m_4692_);
lean_ctor_set(v_reuseFailAlloc_4713_, 24, v_s_4693_);
lean_ctor_set(v_reuseFailAlloc_4713_, 25, v_S_4694_);
lean_ctor_set(v_reuseFailAlloc_4713_, 26, v_A_4695_);
lean_ctor_set(v_reuseFailAlloc_4713_, 27, v_n_4696_);
lean_ctor_set(v_reuseFailAlloc_4713_, 28, v_N_4697_);
lean_ctor_set(v_reuseFailAlloc_4713_, 29, v_V_4698_);
lean_ctor_set(v_reuseFailAlloc_4713_, 30, v_z_4699_);
lean_ctor_set(v_reuseFailAlloc_4713_, 31, v_zabbrev_4700_);
lean_ctor_set(v_reuseFailAlloc_4713_, 32, v_v_4701_);
lean_ctor_set(v_reuseFailAlloc_4713_, 33, v_O_4702_);
lean_ctor_set(v_reuseFailAlloc_4713_, 34, v_X_4703_);
lean_ctor_set(v_reuseFailAlloc_4713_, 35, v_x_4704_);
lean_ctor_set(v_reuseFailAlloc_4713_, 36, v_Z_4705_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
}
}
case 4:
{
lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4769_; 
v_isSharedCheck_4769_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_4769_ == 0)
{
lean_object* v_unused_4770_; 
v_unused_4770_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_4770_);
v___x_4720_ = v_modifier_4516_;
v_isShared_4721_ = v_isSharedCheck_4769_;
goto v_resetjp_4719_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4769_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v_G_4722_; lean_object* v_y_4723_; lean_object* v_u_4724_; lean_object* v_Y_4725_; lean_object* v_D_4726_; lean_object* v_L_4727_; lean_object* v_d_4728_; lean_object* v_Q_4729_; lean_object* v_q_4730_; lean_object* v_w_4731_; lean_object* v_W_4732_; lean_object* v_E_4733_; lean_object* v_e_4734_; lean_object* v_c_4735_; lean_object* v_F_4736_; lean_object* v_a_4737_; lean_object* v_b_4738_; lean_object* v_B_4739_; lean_object* v_h_4740_; lean_object* v_K_4741_; lean_object* v_k_4742_; lean_object* v_H_4743_; lean_object* v_m_4744_; lean_object* v_s_4745_; lean_object* v_S_4746_; lean_object* v_A_4747_; lean_object* v_n_4748_; lean_object* v_N_4749_; lean_object* v_V_4750_; lean_object* v_z_4751_; lean_object* v_zabbrev_4752_; lean_object* v_v_4753_; lean_object* v_O_4754_; lean_object* v_X_4755_; lean_object* v_x_4756_; lean_object* v_Z_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4767_; 
v_G_4722_ = lean_ctor_get(v_date_4515_, 0);
v_y_4723_ = lean_ctor_get(v_date_4515_, 1);
v_u_4724_ = lean_ctor_get(v_date_4515_, 2);
v_Y_4725_ = lean_ctor_get(v_date_4515_, 3);
v_D_4726_ = lean_ctor_get(v_date_4515_, 4);
v_L_4727_ = lean_ctor_get(v_date_4515_, 6);
v_d_4728_ = lean_ctor_get(v_date_4515_, 7);
v_Q_4729_ = lean_ctor_get(v_date_4515_, 8);
v_q_4730_ = lean_ctor_get(v_date_4515_, 9);
v_w_4731_ = lean_ctor_get(v_date_4515_, 10);
v_W_4732_ = lean_ctor_get(v_date_4515_, 11);
v_E_4733_ = lean_ctor_get(v_date_4515_, 12);
v_e_4734_ = lean_ctor_get(v_date_4515_, 13);
v_c_4735_ = lean_ctor_get(v_date_4515_, 14);
v_F_4736_ = lean_ctor_get(v_date_4515_, 15);
v_a_4737_ = lean_ctor_get(v_date_4515_, 16);
v_b_4738_ = lean_ctor_get(v_date_4515_, 17);
v_B_4739_ = lean_ctor_get(v_date_4515_, 18);
v_h_4740_ = lean_ctor_get(v_date_4515_, 19);
v_K_4741_ = lean_ctor_get(v_date_4515_, 20);
v_k_4742_ = lean_ctor_get(v_date_4515_, 21);
v_H_4743_ = lean_ctor_get(v_date_4515_, 22);
v_m_4744_ = lean_ctor_get(v_date_4515_, 23);
v_s_4745_ = lean_ctor_get(v_date_4515_, 24);
v_S_4746_ = lean_ctor_get(v_date_4515_, 25);
v_A_4747_ = lean_ctor_get(v_date_4515_, 26);
v_n_4748_ = lean_ctor_get(v_date_4515_, 27);
v_N_4749_ = lean_ctor_get(v_date_4515_, 28);
v_V_4750_ = lean_ctor_get(v_date_4515_, 29);
v_z_4751_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_4752_ = lean_ctor_get(v_date_4515_, 31);
v_v_4753_ = lean_ctor_get(v_date_4515_, 32);
v_O_4754_ = lean_ctor_get(v_date_4515_, 33);
v_X_4755_ = lean_ctor_get(v_date_4515_, 34);
v_x_4756_ = lean_ctor_get(v_date_4515_, 35);
v_Z_4757_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_4767_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_4767_ == 0)
{
lean_object* v_unused_4768_; 
v_unused_4768_ = lean_ctor_get(v_date_4515_, 5);
lean_dec(v_unused_4768_);
v___x_4759_ = v_date_4515_;
v_isShared_4760_ = v_isSharedCheck_4767_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_Z_4757_);
lean_inc(v_x_4756_);
lean_inc(v_X_4755_);
lean_inc(v_O_4754_);
lean_inc(v_v_4753_);
lean_inc(v_zabbrev_4752_);
lean_inc(v_z_4751_);
lean_inc(v_V_4750_);
lean_inc(v_N_4749_);
lean_inc(v_n_4748_);
lean_inc(v_A_4747_);
lean_inc(v_S_4746_);
lean_inc(v_s_4745_);
lean_inc(v_m_4744_);
lean_inc(v_H_4743_);
lean_inc(v_k_4742_);
lean_inc(v_K_4741_);
lean_inc(v_h_4740_);
lean_inc(v_B_4739_);
lean_inc(v_b_4738_);
lean_inc(v_a_4737_);
lean_inc(v_F_4736_);
lean_inc(v_c_4735_);
lean_inc(v_e_4734_);
lean_inc(v_E_4733_);
lean_inc(v_W_4732_);
lean_inc(v_w_4731_);
lean_inc(v_q_4730_);
lean_inc(v_Q_4729_);
lean_inc(v_d_4728_);
lean_inc(v_L_4727_);
lean_inc(v_D_4726_);
lean_inc(v_Y_4725_);
lean_inc(v_u_4724_);
lean_inc(v_y_4723_);
lean_inc(v_G_4722_);
lean_dec(v_date_4515_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4767_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4721_ == 0)
{
lean_ctor_set_tag(v___x_4720_, 1);
lean_ctor_set(v___x_4720_, 0, v_data_4517_);
v___x_4762_ = v___x_4720_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_data_4517_);
v___x_4762_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4764_; 
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 5, v___x_4762_);
v___x_4764_ = v___x_4759_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_G_4722_);
lean_ctor_set(v_reuseFailAlloc_4765_, 1, v_y_4723_);
lean_ctor_set(v_reuseFailAlloc_4765_, 2, v_u_4724_);
lean_ctor_set(v_reuseFailAlloc_4765_, 3, v_Y_4725_);
lean_ctor_set(v_reuseFailAlloc_4765_, 4, v_D_4726_);
lean_ctor_set(v_reuseFailAlloc_4765_, 5, v___x_4762_);
lean_ctor_set(v_reuseFailAlloc_4765_, 6, v_L_4727_);
lean_ctor_set(v_reuseFailAlloc_4765_, 7, v_d_4728_);
lean_ctor_set(v_reuseFailAlloc_4765_, 8, v_Q_4729_);
lean_ctor_set(v_reuseFailAlloc_4765_, 9, v_q_4730_);
lean_ctor_set(v_reuseFailAlloc_4765_, 10, v_w_4731_);
lean_ctor_set(v_reuseFailAlloc_4765_, 11, v_W_4732_);
lean_ctor_set(v_reuseFailAlloc_4765_, 12, v_E_4733_);
lean_ctor_set(v_reuseFailAlloc_4765_, 13, v_e_4734_);
lean_ctor_set(v_reuseFailAlloc_4765_, 14, v_c_4735_);
lean_ctor_set(v_reuseFailAlloc_4765_, 15, v_F_4736_);
lean_ctor_set(v_reuseFailAlloc_4765_, 16, v_a_4737_);
lean_ctor_set(v_reuseFailAlloc_4765_, 17, v_b_4738_);
lean_ctor_set(v_reuseFailAlloc_4765_, 18, v_B_4739_);
lean_ctor_set(v_reuseFailAlloc_4765_, 19, v_h_4740_);
lean_ctor_set(v_reuseFailAlloc_4765_, 20, v_K_4741_);
lean_ctor_set(v_reuseFailAlloc_4765_, 21, v_k_4742_);
lean_ctor_set(v_reuseFailAlloc_4765_, 22, v_H_4743_);
lean_ctor_set(v_reuseFailAlloc_4765_, 23, v_m_4744_);
lean_ctor_set(v_reuseFailAlloc_4765_, 24, v_s_4745_);
lean_ctor_set(v_reuseFailAlloc_4765_, 25, v_S_4746_);
lean_ctor_set(v_reuseFailAlloc_4765_, 26, v_A_4747_);
lean_ctor_set(v_reuseFailAlloc_4765_, 27, v_n_4748_);
lean_ctor_set(v_reuseFailAlloc_4765_, 28, v_N_4749_);
lean_ctor_set(v_reuseFailAlloc_4765_, 29, v_V_4750_);
lean_ctor_set(v_reuseFailAlloc_4765_, 30, v_z_4751_);
lean_ctor_set(v_reuseFailAlloc_4765_, 31, v_zabbrev_4752_);
lean_ctor_set(v_reuseFailAlloc_4765_, 32, v_v_4753_);
lean_ctor_set(v_reuseFailAlloc_4765_, 33, v_O_4754_);
lean_ctor_set(v_reuseFailAlloc_4765_, 34, v_X_4755_);
lean_ctor_set(v_reuseFailAlloc_4765_, 35, v_x_4756_);
lean_ctor_set(v_reuseFailAlloc_4765_, 36, v_Z_4757_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
}
case 5:
{
lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4821_; 
v_isSharedCheck_4821_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_4821_ == 0)
{
lean_object* v_unused_4822_; 
v_unused_4822_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_4822_);
v___x_4772_ = v_modifier_4516_;
v_isShared_4773_ = v_isSharedCheck_4821_;
goto v_resetjp_4771_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4821_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v_G_4774_; lean_object* v_y_4775_; lean_object* v_u_4776_; lean_object* v_Y_4777_; lean_object* v_D_4778_; lean_object* v_M_4779_; lean_object* v_d_4780_; lean_object* v_Q_4781_; lean_object* v_q_4782_; lean_object* v_w_4783_; lean_object* v_W_4784_; lean_object* v_E_4785_; lean_object* v_e_4786_; lean_object* v_c_4787_; lean_object* v_F_4788_; lean_object* v_a_4789_; lean_object* v_b_4790_; lean_object* v_B_4791_; lean_object* v_h_4792_; lean_object* v_K_4793_; lean_object* v_k_4794_; lean_object* v_H_4795_; lean_object* v_m_4796_; lean_object* v_s_4797_; lean_object* v_S_4798_; lean_object* v_A_4799_; lean_object* v_n_4800_; lean_object* v_N_4801_; lean_object* v_V_4802_; lean_object* v_z_4803_; lean_object* v_zabbrev_4804_; lean_object* v_v_4805_; lean_object* v_O_4806_; lean_object* v_X_4807_; lean_object* v_x_4808_; lean_object* v_Z_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4819_; 
v_G_4774_ = lean_ctor_get(v_date_4515_, 0);
v_y_4775_ = lean_ctor_get(v_date_4515_, 1);
v_u_4776_ = lean_ctor_get(v_date_4515_, 2);
v_Y_4777_ = lean_ctor_get(v_date_4515_, 3);
v_D_4778_ = lean_ctor_get(v_date_4515_, 4);
v_M_4779_ = lean_ctor_get(v_date_4515_, 5);
v_d_4780_ = lean_ctor_get(v_date_4515_, 7);
v_Q_4781_ = lean_ctor_get(v_date_4515_, 8);
v_q_4782_ = lean_ctor_get(v_date_4515_, 9);
v_w_4783_ = lean_ctor_get(v_date_4515_, 10);
v_W_4784_ = lean_ctor_get(v_date_4515_, 11);
v_E_4785_ = lean_ctor_get(v_date_4515_, 12);
v_e_4786_ = lean_ctor_get(v_date_4515_, 13);
v_c_4787_ = lean_ctor_get(v_date_4515_, 14);
v_F_4788_ = lean_ctor_get(v_date_4515_, 15);
v_a_4789_ = lean_ctor_get(v_date_4515_, 16);
v_b_4790_ = lean_ctor_get(v_date_4515_, 17);
v_B_4791_ = lean_ctor_get(v_date_4515_, 18);
v_h_4792_ = lean_ctor_get(v_date_4515_, 19);
v_K_4793_ = lean_ctor_get(v_date_4515_, 20);
v_k_4794_ = lean_ctor_get(v_date_4515_, 21);
v_H_4795_ = lean_ctor_get(v_date_4515_, 22);
v_m_4796_ = lean_ctor_get(v_date_4515_, 23);
v_s_4797_ = lean_ctor_get(v_date_4515_, 24);
v_S_4798_ = lean_ctor_get(v_date_4515_, 25);
v_A_4799_ = lean_ctor_get(v_date_4515_, 26);
v_n_4800_ = lean_ctor_get(v_date_4515_, 27);
v_N_4801_ = lean_ctor_get(v_date_4515_, 28);
v_V_4802_ = lean_ctor_get(v_date_4515_, 29);
v_z_4803_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_4804_ = lean_ctor_get(v_date_4515_, 31);
v_v_4805_ = lean_ctor_get(v_date_4515_, 32);
v_O_4806_ = lean_ctor_get(v_date_4515_, 33);
v_X_4807_ = lean_ctor_get(v_date_4515_, 34);
v_x_4808_ = lean_ctor_get(v_date_4515_, 35);
v_Z_4809_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_4819_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_4819_ == 0)
{
lean_object* v_unused_4820_; 
v_unused_4820_ = lean_ctor_get(v_date_4515_, 6);
lean_dec(v_unused_4820_);
v___x_4811_ = v_date_4515_;
v_isShared_4812_ = v_isSharedCheck_4819_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_Z_4809_);
lean_inc(v_x_4808_);
lean_inc(v_X_4807_);
lean_inc(v_O_4806_);
lean_inc(v_v_4805_);
lean_inc(v_zabbrev_4804_);
lean_inc(v_z_4803_);
lean_inc(v_V_4802_);
lean_inc(v_N_4801_);
lean_inc(v_n_4800_);
lean_inc(v_A_4799_);
lean_inc(v_S_4798_);
lean_inc(v_s_4797_);
lean_inc(v_m_4796_);
lean_inc(v_H_4795_);
lean_inc(v_k_4794_);
lean_inc(v_K_4793_);
lean_inc(v_h_4792_);
lean_inc(v_B_4791_);
lean_inc(v_b_4790_);
lean_inc(v_a_4789_);
lean_inc(v_F_4788_);
lean_inc(v_c_4787_);
lean_inc(v_e_4786_);
lean_inc(v_E_4785_);
lean_inc(v_W_4784_);
lean_inc(v_w_4783_);
lean_inc(v_q_4782_);
lean_inc(v_Q_4781_);
lean_inc(v_d_4780_);
lean_inc(v_M_4779_);
lean_inc(v_D_4778_);
lean_inc(v_Y_4777_);
lean_inc(v_u_4776_);
lean_inc(v_y_4775_);
lean_inc(v_G_4774_);
lean_dec(v_date_4515_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4819_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4814_; 
if (v_isShared_4773_ == 0)
{
lean_ctor_set_tag(v___x_4772_, 1);
lean_ctor_set(v___x_4772_, 0, v_data_4517_);
v___x_4814_ = v___x_4772_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_data_4517_);
v___x_4814_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
lean_object* v___x_4816_; 
if (v_isShared_4812_ == 0)
{
lean_ctor_set(v___x_4811_, 6, v___x_4814_);
v___x_4816_ = v___x_4811_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_G_4774_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_y_4775_);
lean_ctor_set(v_reuseFailAlloc_4817_, 2, v_u_4776_);
lean_ctor_set(v_reuseFailAlloc_4817_, 3, v_Y_4777_);
lean_ctor_set(v_reuseFailAlloc_4817_, 4, v_D_4778_);
lean_ctor_set(v_reuseFailAlloc_4817_, 5, v_M_4779_);
lean_ctor_set(v_reuseFailAlloc_4817_, 6, v___x_4814_);
lean_ctor_set(v_reuseFailAlloc_4817_, 7, v_d_4780_);
lean_ctor_set(v_reuseFailAlloc_4817_, 8, v_Q_4781_);
lean_ctor_set(v_reuseFailAlloc_4817_, 9, v_q_4782_);
lean_ctor_set(v_reuseFailAlloc_4817_, 10, v_w_4783_);
lean_ctor_set(v_reuseFailAlloc_4817_, 11, v_W_4784_);
lean_ctor_set(v_reuseFailAlloc_4817_, 12, v_E_4785_);
lean_ctor_set(v_reuseFailAlloc_4817_, 13, v_e_4786_);
lean_ctor_set(v_reuseFailAlloc_4817_, 14, v_c_4787_);
lean_ctor_set(v_reuseFailAlloc_4817_, 15, v_F_4788_);
lean_ctor_set(v_reuseFailAlloc_4817_, 16, v_a_4789_);
lean_ctor_set(v_reuseFailAlloc_4817_, 17, v_b_4790_);
lean_ctor_set(v_reuseFailAlloc_4817_, 18, v_B_4791_);
lean_ctor_set(v_reuseFailAlloc_4817_, 19, v_h_4792_);
lean_ctor_set(v_reuseFailAlloc_4817_, 20, v_K_4793_);
lean_ctor_set(v_reuseFailAlloc_4817_, 21, v_k_4794_);
lean_ctor_set(v_reuseFailAlloc_4817_, 22, v_H_4795_);
lean_ctor_set(v_reuseFailAlloc_4817_, 23, v_m_4796_);
lean_ctor_set(v_reuseFailAlloc_4817_, 24, v_s_4797_);
lean_ctor_set(v_reuseFailAlloc_4817_, 25, v_S_4798_);
lean_ctor_set(v_reuseFailAlloc_4817_, 26, v_A_4799_);
lean_ctor_set(v_reuseFailAlloc_4817_, 27, v_n_4800_);
lean_ctor_set(v_reuseFailAlloc_4817_, 28, v_N_4801_);
lean_ctor_set(v_reuseFailAlloc_4817_, 29, v_V_4802_);
lean_ctor_set(v_reuseFailAlloc_4817_, 30, v_z_4803_);
lean_ctor_set(v_reuseFailAlloc_4817_, 31, v_zabbrev_4804_);
lean_ctor_set(v_reuseFailAlloc_4817_, 32, v_v_4805_);
lean_ctor_set(v_reuseFailAlloc_4817_, 33, v_O_4806_);
lean_ctor_set(v_reuseFailAlloc_4817_, 34, v_X_4807_);
lean_ctor_set(v_reuseFailAlloc_4817_, 35, v_x_4808_);
lean_ctor_set(v_reuseFailAlloc_4817_, 36, v_Z_4809_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
}
case 6:
{
lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4873_; 
v_isSharedCheck_4873_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_4873_ == 0)
{
lean_object* v_unused_4874_; 
v_unused_4874_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_4874_);
v___x_4824_ = v_modifier_4516_;
v_isShared_4825_ = v_isSharedCheck_4873_;
goto v_resetjp_4823_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4873_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v_G_4826_; lean_object* v_y_4827_; lean_object* v_u_4828_; lean_object* v_Y_4829_; lean_object* v_D_4830_; lean_object* v_M_4831_; lean_object* v_L_4832_; lean_object* v_Q_4833_; lean_object* v_q_4834_; lean_object* v_w_4835_; lean_object* v_W_4836_; lean_object* v_E_4837_; lean_object* v_e_4838_; lean_object* v_c_4839_; lean_object* v_F_4840_; lean_object* v_a_4841_; lean_object* v_b_4842_; lean_object* v_B_4843_; lean_object* v_h_4844_; lean_object* v_K_4845_; lean_object* v_k_4846_; lean_object* v_H_4847_; lean_object* v_m_4848_; lean_object* v_s_4849_; lean_object* v_S_4850_; lean_object* v_A_4851_; lean_object* v_n_4852_; lean_object* v_N_4853_; lean_object* v_V_4854_; lean_object* v_z_4855_; lean_object* v_zabbrev_4856_; lean_object* v_v_4857_; lean_object* v_O_4858_; lean_object* v_X_4859_; lean_object* v_x_4860_; lean_object* v_Z_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4871_; 
v_G_4826_ = lean_ctor_get(v_date_4515_, 0);
v_y_4827_ = lean_ctor_get(v_date_4515_, 1);
v_u_4828_ = lean_ctor_get(v_date_4515_, 2);
v_Y_4829_ = lean_ctor_get(v_date_4515_, 3);
v_D_4830_ = lean_ctor_get(v_date_4515_, 4);
v_M_4831_ = lean_ctor_get(v_date_4515_, 5);
v_L_4832_ = lean_ctor_get(v_date_4515_, 6);
v_Q_4833_ = lean_ctor_get(v_date_4515_, 8);
v_q_4834_ = lean_ctor_get(v_date_4515_, 9);
v_w_4835_ = lean_ctor_get(v_date_4515_, 10);
v_W_4836_ = lean_ctor_get(v_date_4515_, 11);
v_E_4837_ = lean_ctor_get(v_date_4515_, 12);
v_e_4838_ = lean_ctor_get(v_date_4515_, 13);
v_c_4839_ = lean_ctor_get(v_date_4515_, 14);
v_F_4840_ = lean_ctor_get(v_date_4515_, 15);
v_a_4841_ = lean_ctor_get(v_date_4515_, 16);
v_b_4842_ = lean_ctor_get(v_date_4515_, 17);
v_B_4843_ = lean_ctor_get(v_date_4515_, 18);
v_h_4844_ = lean_ctor_get(v_date_4515_, 19);
v_K_4845_ = lean_ctor_get(v_date_4515_, 20);
v_k_4846_ = lean_ctor_get(v_date_4515_, 21);
v_H_4847_ = lean_ctor_get(v_date_4515_, 22);
v_m_4848_ = lean_ctor_get(v_date_4515_, 23);
v_s_4849_ = lean_ctor_get(v_date_4515_, 24);
v_S_4850_ = lean_ctor_get(v_date_4515_, 25);
v_A_4851_ = lean_ctor_get(v_date_4515_, 26);
v_n_4852_ = lean_ctor_get(v_date_4515_, 27);
v_N_4853_ = lean_ctor_get(v_date_4515_, 28);
v_V_4854_ = lean_ctor_get(v_date_4515_, 29);
v_z_4855_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_4856_ = lean_ctor_get(v_date_4515_, 31);
v_v_4857_ = lean_ctor_get(v_date_4515_, 32);
v_O_4858_ = lean_ctor_get(v_date_4515_, 33);
v_X_4859_ = lean_ctor_get(v_date_4515_, 34);
v_x_4860_ = lean_ctor_get(v_date_4515_, 35);
v_Z_4861_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_4871_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_4871_ == 0)
{
lean_object* v_unused_4872_; 
v_unused_4872_ = lean_ctor_get(v_date_4515_, 7);
lean_dec(v_unused_4872_);
v___x_4863_ = v_date_4515_;
v_isShared_4864_ = v_isSharedCheck_4871_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_Z_4861_);
lean_inc(v_x_4860_);
lean_inc(v_X_4859_);
lean_inc(v_O_4858_);
lean_inc(v_v_4857_);
lean_inc(v_zabbrev_4856_);
lean_inc(v_z_4855_);
lean_inc(v_V_4854_);
lean_inc(v_N_4853_);
lean_inc(v_n_4852_);
lean_inc(v_A_4851_);
lean_inc(v_S_4850_);
lean_inc(v_s_4849_);
lean_inc(v_m_4848_);
lean_inc(v_H_4847_);
lean_inc(v_k_4846_);
lean_inc(v_K_4845_);
lean_inc(v_h_4844_);
lean_inc(v_B_4843_);
lean_inc(v_b_4842_);
lean_inc(v_a_4841_);
lean_inc(v_F_4840_);
lean_inc(v_c_4839_);
lean_inc(v_e_4838_);
lean_inc(v_E_4837_);
lean_inc(v_W_4836_);
lean_inc(v_w_4835_);
lean_inc(v_q_4834_);
lean_inc(v_Q_4833_);
lean_inc(v_L_4832_);
lean_inc(v_M_4831_);
lean_inc(v_D_4830_);
lean_inc(v_Y_4829_);
lean_inc(v_u_4828_);
lean_inc(v_y_4827_);
lean_inc(v_G_4826_);
lean_dec(v_date_4515_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4871_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4825_ == 0)
{
lean_ctor_set_tag(v___x_4824_, 1);
lean_ctor_set(v___x_4824_, 0, v_data_4517_);
v___x_4866_ = v___x_4824_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_data_4517_);
v___x_4866_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
lean_object* v___x_4868_; 
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 7, v___x_4866_);
v___x_4868_ = v___x_4863_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_G_4826_);
lean_ctor_set(v_reuseFailAlloc_4869_, 1, v_y_4827_);
lean_ctor_set(v_reuseFailAlloc_4869_, 2, v_u_4828_);
lean_ctor_set(v_reuseFailAlloc_4869_, 3, v_Y_4829_);
lean_ctor_set(v_reuseFailAlloc_4869_, 4, v_D_4830_);
lean_ctor_set(v_reuseFailAlloc_4869_, 5, v_M_4831_);
lean_ctor_set(v_reuseFailAlloc_4869_, 6, v_L_4832_);
lean_ctor_set(v_reuseFailAlloc_4869_, 7, v___x_4866_);
lean_ctor_set(v_reuseFailAlloc_4869_, 8, v_Q_4833_);
lean_ctor_set(v_reuseFailAlloc_4869_, 9, v_q_4834_);
lean_ctor_set(v_reuseFailAlloc_4869_, 10, v_w_4835_);
lean_ctor_set(v_reuseFailAlloc_4869_, 11, v_W_4836_);
lean_ctor_set(v_reuseFailAlloc_4869_, 12, v_E_4837_);
lean_ctor_set(v_reuseFailAlloc_4869_, 13, v_e_4838_);
lean_ctor_set(v_reuseFailAlloc_4869_, 14, v_c_4839_);
lean_ctor_set(v_reuseFailAlloc_4869_, 15, v_F_4840_);
lean_ctor_set(v_reuseFailAlloc_4869_, 16, v_a_4841_);
lean_ctor_set(v_reuseFailAlloc_4869_, 17, v_b_4842_);
lean_ctor_set(v_reuseFailAlloc_4869_, 18, v_B_4843_);
lean_ctor_set(v_reuseFailAlloc_4869_, 19, v_h_4844_);
lean_ctor_set(v_reuseFailAlloc_4869_, 20, v_K_4845_);
lean_ctor_set(v_reuseFailAlloc_4869_, 21, v_k_4846_);
lean_ctor_set(v_reuseFailAlloc_4869_, 22, v_H_4847_);
lean_ctor_set(v_reuseFailAlloc_4869_, 23, v_m_4848_);
lean_ctor_set(v_reuseFailAlloc_4869_, 24, v_s_4849_);
lean_ctor_set(v_reuseFailAlloc_4869_, 25, v_S_4850_);
lean_ctor_set(v_reuseFailAlloc_4869_, 26, v_A_4851_);
lean_ctor_set(v_reuseFailAlloc_4869_, 27, v_n_4852_);
lean_ctor_set(v_reuseFailAlloc_4869_, 28, v_N_4853_);
lean_ctor_set(v_reuseFailAlloc_4869_, 29, v_V_4854_);
lean_ctor_set(v_reuseFailAlloc_4869_, 30, v_z_4855_);
lean_ctor_set(v_reuseFailAlloc_4869_, 31, v_zabbrev_4856_);
lean_ctor_set(v_reuseFailAlloc_4869_, 32, v_v_4857_);
lean_ctor_set(v_reuseFailAlloc_4869_, 33, v_O_4858_);
lean_ctor_set(v_reuseFailAlloc_4869_, 34, v_X_4859_);
lean_ctor_set(v_reuseFailAlloc_4869_, 35, v_x_4860_);
lean_ctor_set(v_reuseFailAlloc_4869_, 36, v_Z_4861_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
}
case 7:
{
lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4925_; 
v_isSharedCheck_4925_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_4925_ == 0)
{
lean_object* v_unused_4926_; 
v_unused_4926_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_4926_);
v___x_4876_ = v_modifier_4516_;
v_isShared_4877_ = v_isSharedCheck_4925_;
goto v_resetjp_4875_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4925_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v_G_4878_; lean_object* v_y_4879_; lean_object* v_u_4880_; lean_object* v_Y_4881_; lean_object* v_D_4882_; lean_object* v_M_4883_; lean_object* v_L_4884_; lean_object* v_d_4885_; lean_object* v_q_4886_; lean_object* v_w_4887_; lean_object* v_W_4888_; lean_object* v_E_4889_; lean_object* v_e_4890_; lean_object* v_c_4891_; lean_object* v_F_4892_; lean_object* v_a_4893_; lean_object* v_b_4894_; lean_object* v_B_4895_; lean_object* v_h_4896_; lean_object* v_K_4897_; lean_object* v_k_4898_; lean_object* v_H_4899_; lean_object* v_m_4900_; lean_object* v_s_4901_; lean_object* v_S_4902_; lean_object* v_A_4903_; lean_object* v_n_4904_; lean_object* v_N_4905_; lean_object* v_V_4906_; lean_object* v_z_4907_; lean_object* v_zabbrev_4908_; lean_object* v_v_4909_; lean_object* v_O_4910_; lean_object* v_X_4911_; lean_object* v_x_4912_; lean_object* v_Z_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4923_; 
v_G_4878_ = lean_ctor_get(v_date_4515_, 0);
v_y_4879_ = lean_ctor_get(v_date_4515_, 1);
v_u_4880_ = lean_ctor_get(v_date_4515_, 2);
v_Y_4881_ = lean_ctor_get(v_date_4515_, 3);
v_D_4882_ = lean_ctor_get(v_date_4515_, 4);
v_M_4883_ = lean_ctor_get(v_date_4515_, 5);
v_L_4884_ = lean_ctor_get(v_date_4515_, 6);
v_d_4885_ = lean_ctor_get(v_date_4515_, 7);
v_q_4886_ = lean_ctor_get(v_date_4515_, 9);
v_w_4887_ = lean_ctor_get(v_date_4515_, 10);
v_W_4888_ = lean_ctor_get(v_date_4515_, 11);
v_E_4889_ = lean_ctor_get(v_date_4515_, 12);
v_e_4890_ = lean_ctor_get(v_date_4515_, 13);
v_c_4891_ = lean_ctor_get(v_date_4515_, 14);
v_F_4892_ = lean_ctor_get(v_date_4515_, 15);
v_a_4893_ = lean_ctor_get(v_date_4515_, 16);
v_b_4894_ = lean_ctor_get(v_date_4515_, 17);
v_B_4895_ = lean_ctor_get(v_date_4515_, 18);
v_h_4896_ = lean_ctor_get(v_date_4515_, 19);
v_K_4897_ = lean_ctor_get(v_date_4515_, 20);
v_k_4898_ = lean_ctor_get(v_date_4515_, 21);
v_H_4899_ = lean_ctor_get(v_date_4515_, 22);
v_m_4900_ = lean_ctor_get(v_date_4515_, 23);
v_s_4901_ = lean_ctor_get(v_date_4515_, 24);
v_S_4902_ = lean_ctor_get(v_date_4515_, 25);
v_A_4903_ = lean_ctor_get(v_date_4515_, 26);
v_n_4904_ = lean_ctor_get(v_date_4515_, 27);
v_N_4905_ = lean_ctor_get(v_date_4515_, 28);
v_V_4906_ = lean_ctor_get(v_date_4515_, 29);
v_z_4907_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_4908_ = lean_ctor_get(v_date_4515_, 31);
v_v_4909_ = lean_ctor_get(v_date_4515_, 32);
v_O_4910_ = lean_ctor_get(v_date_4515_, 33);
v_X_4911_ = lean_ctor_get(v_date_4515_, 34);
v_x_4912_ = lean_ctor_get(v_date_4515_, 35);
v_Z_4913_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_4923_ == 0)
{
lean_object* v_unused_4924_; 
v_unused_4924_ = lean_ctor_get(v_date_4515_, 8);
lean_dec(v_unused_4924_);
v___x_4915_ = v_date_4515_;
v_isShared_4916_ = v_isSharedCheck_4923_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_Z_4913_);
lean_inc(v_x_4912_);
lean_inc(v_X_4911_);
lean_inc(v_O_4910_);
lean_inc(v_v_4909_);
lean_inc(v_zabbrev_4908_);
lean_inc(v_z_4907_);
lean_inc(v_V_4906_);
lean_inc(v_N_4905_);
lean_inc(v_n_4904_);
lean_inc(v_A_4903_);
lean_inc(v_S_4902_);
lean_inc(v_s_4901_);
lean_inc(v_m_4900_);
lean_inc(v_H_4899_);
lean_inc(v_k_4898_);
lean_inc(v_K_4897_);
lean_inc(v_h_4896_);
lean_inc(v_B_4895_);
lean_inc(v_b_4894_);
lean_inc(v_a_4893_);
lean_inc(v_F_4892_);
lean_inc(v_c_4891_);
lean_inc(v_e_4890_);
lean_inc(v_E_4889_);
lean_inc(v_W_4888_);
lean_inc(v_w_4887_);
lean_inc(v_q_4886_);
lean_inc(v_d_4885_);
lean_inc(v_L_4884_);
lean_inc(v_M_4883_);
lean_inc(v_D_4882_);
lean_inc(v_Y_4881_);
lean_inc(v_u_4880_);
lean_inc(v_y_4879_);
lean_inc(v_G_4878_);
lean_dec(v_date_4515_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4923_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4877_ == 0)
{
lean_ctor_set_tag(v___x_4876_, 1);
lean_ctor_set(v___x_4876_, 0, v_data_4517_);
v___x_4918_ = v___x_4876_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_data_4517_);
v___x_4918_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
lean_object* v___x_4920_; 
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 8, v___x_4918_);
v___x_4920_ = v___x_4915_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_G_4878_);
lean_ctor_set(v_reuseFailAlloc_4921_, 1, v_y_4879_);
lean_ctor_set(v_reuseFailAlloc_4921_, 2, v_u_4880_);
lean_ctor_set(v_reuseFailAlloc_4921_, 3, v_Y_4881_);
lean_ctor_set(v_reuseFailAlloc_4921_, 4, v_D_4882_);
lean_ctor_set(v_reuseFailAlloc_4921_, 5, v_M_4883_);
lean_ctor_set(v_reuseFailAlloc_4921_, 6, v_L_4884_);
lean_ctor_set(v_reuseFailAlloc_4921_, 7, v_d_4885_);
lean_ctor_set(v_reuseFailAlloc_4921_, 8, v___x_4918_);
lean_ctor_set(v_reuseFailAlloc_4921_, 9, v_q_4886_);
lean_ctor_set(v_reuseFailAlloc_4921_, 10, v_w_4887_);
lean_ctor_set(v_reuseFailAlloc_4921_, 11, v_W_4888_);
lean_ctor_set(v_reuseFailAlloc_4921_, 12, v_E_4889_);
lean_ctor_set(v_reuseFailAlloc_4921_, 13, v_e_4890_);
lean_ctor_set(v_reuseFailAlloc_4921_, 14, v_c_4891_);
lean_ctor_set(v_reuseFailAlloc_4921_, 15, v_F_4892_);
lean_ctor_set(v_reuseFailAlloc_4921_, 16, v_a_4893_);
lean_ctor_set(v_reuseFailAlloc_4921_, 17, v_b_4894_);
lean_ctor_set(v_reuseFailAlloc_4921_, 18, v_B_4895_);
lean_ctor_set(v_reuseFailAlloc_4921_, 19, v_h_4896_);
lean_ctor_set(v_reuseFailAlloc_4921_, 20, v_K_4897_);
lean_ctor_set(v_reuseFailAlloc_4921_, 21, v_k_4898_);
lean_ctor_set(v_reuseFailAlloc_4921_, 22, v_H_4899_);
lean_ctor_set(v_reuseFailAlloc_4921_, 23, v_m_4900_);
lean_ctor_set(v_reuseFailAlloc_4921_, 24, v_s_4901_);
lean_ctor_set(v_reuseFailAlloc_4921_, 25, v_S_4902_);
lean_ctor_set(v_reuseFailAlloc_4921_, 26, v_A_4903_);
lean_ctor_set(v_reuseFailAlloc_4921_, 27, v_n_4904_);
lean_ctor_set(v_reuseFailAlloc_4921_, 28, v_N_4905_);
lean_ctor_set(v_reuseFailAlloc_4921_, 29, v_V_4906_);
lean_ctor_set(v_reuseFailAlloc_4921_, 30, v_z_4907_);
lean_ctor_set(v_reuseFailAlloc_4921_, 31, v_zabbrev_4908_);
lean_ctor_set(v_reuseFailAlloc_4921_, 32, v_v_4909_);
lean_ctor_set(v_reuseFailAlloc_4921_, 33, v_O_4910_);
lean_ctor_set(v_reuseFailAlloc_4921_, 34, v_X_4911_);
lean_ctor_set(v_reuseFailAlloc_4921_, 35, v_x_4912_);
lean_ctor_set(v_reuseFailAlloc_4921_, 36, v_Z_4913_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
}
case 8:
{
lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4977_; 
v_isSharedCheck_4977_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_4977_ == 0)
{
lean_object* v_unused_4978_; 
v_unused_4978_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_4978_);
v___x_4928_ = v_modifier_4516_;
v_isShared_4929_ = v_isSharedCheck_4977_;
goto v_resetjp_4927_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4977_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v_G_4930_; lean_object* v_y_4931_; lean_object* v_u_4932_; lean_object* v_Y_4933_; lean_object* v_D_4934_; lean_object* v_M_4935_; lean_object* v_L_4936_; lean_object* v_d_4937_; lean_object* v_Q_4938_; lean_object* v_w_4939_; lean_object* v_W_4940_; lean_object* v_E_4941_; lean_object* v_e_4942_; lean_object* v_c_4943_; lean_object* v_F_4944_; lean_object* v_a_4945_; lean_object* v_b_4946_; lean_object* v_B_4947_; lean_object* v_h_4948_; lean_object* v_K_4949_; lean_object* v_k_4950_; lean_object* v_H_4951_; lean_object* v_m_4952_; lean_object* v_s_4953_; lean_object* v_S_4954_; lean_object* v_A_4955_; lean_object* v_n_4956_; lean_object* v_N_4957_; lean_object* v_V_4958_; lean_object* v_z_4959_; lean_object* v_zabbrev_4960_; lean_object* v_v_4961_; lean_object* v_O_4962_; lean_object* v_X_4963_; lean_object* v_x_4964_; lean_object* v_Z_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4975_; 
v_G_4930_ = lean_ctor_get(v_date_4515_, 0);
v_y_4931_ = lean_ctor_get(v_date_4515_, 1);
v_u_4932_ = lean_ctor_get(v_date_4515_, 2);
v_Y_4933_ = lean_ctor_get(v_date_4515_, 3);
v_D_4934_ = lean_ctor_get(v_date_4515_, 4);
v_M_4935_ = lean_ctor_get(v_date_4515_, 5);
v_L_4936_ = lean_ctor_get(v_date_4515_, 6);
v_d_4937_ = lean_ctor_get(v_date_4515_, 7);
v_Q_4938_ = lean_ctor_get(v_date_4515_, 8);
v_w_4939_ = lean_ctor_get(v_date_4515_, 10);
v_W_4940_ = lean_ctor_get(v_date_4515_, 11);
v_E_4941_ = lean_ctor_get(v_date_4515_, 12);
v_e_4942_ = lean_ctor_get(v_date_4515_, 13);
v_c_4943_ = lean_ctor_get(v_date_4515_, 14);
v_F_4944_ = lean_ctor_get(v_date_4515_, 15);
v_a_4945_ = lean_ctor_get(v_date_4515_, 16);
v_b_4946_ = lean_ctor_get(v_date_4515_, 17);
v_B_4947_ = lean_ctor_get(v_date_4515_, 18);
v_h_4948_ = lean_ctor_get(v_date_4515_, 19);
v_K_4949_ = lean_ctor_get(v_date_4515_, 20);
v_k_4950_ = lean_ctor_get(v_date_4515_, 21);
v_H_4951_ = lean_ctor_get(v_date_4515_, 22);
v_m_4952_ = lean_ctor_get(v_date_4515_, 23);
v_s_4953_ = lean_ctor_get(v_date_4515_, 24);
v_S_4954_ = lean_ctor_get(v_date_4515_, 25);
v_A_4955_ = lean_ctor_get(v_date_4515_, 26);
v_n_4956_ = lean_ctor_get(v_date_4515_, 27);
v_N_4957_ = lean_ctor_get(v_date_4515_, 28);
v_V_4958_ = lean_ctor_get(v_date_4515_, 29);
v_z_4959_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_4960_ = lean_ctor_get(v_date_4515_, 31);
v_v_4961_ = lean_ctor_get(v_date_4515_, 32);
v_O_4962_ = lean_ctor_get(v_date_4515_, 33);
v_X_4963_ = lean_ctor_get(v_date_4515_, 34);
v_x_4964_ = lean_ctor_get(v_date_4515_, 35);
v_Z_4965_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_4975_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_4975_ == 0)
{
lean_object* v_unused_4976_; 
v_unused_4976_ = lean_ctor_get(v_date_4515_, 9);
lean_dec(v_unused_4976_);
v___x_4967_ = v_date_4515_;
v_isShared_4968_ = v_isSharedCheck_4975_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_Z_4965_);
lean_inc(v_x_4964_);
lean_inc(v_X_4963_);
lean_inc(v_O_4962_);
lean_inc(v_v_4961_);
lean_inc(v_zabbrev_4960_);
lean_inc(v_z_4959_);
lean_inc(v_V_4958_);
lean_inc(v_N_4957_);
lean_inc(v_n_4956_);
lean_inc(v_A_4955_);
lean_inc(v_S_4954_);
lean_inc(v_s_4953_);
lean_inc(v_m_4952_);
lean_inc(v_H_4951_);
lean_inc(v_k_4950_);
lean_inc(v_K_4949_);
lean_inc(v_h_4948_);
lean_inc(v_B_4947_);
lean_inc(v_b_4946_);
lean_inc(v_a_4945_);
lean_inc(v_F_4944_);
lean_inc(v_c_4943_);
lean_inc(v_e_4942_);
lean_inc(v_E_4941_);
lean_inc(v_W_4940_);
lean_inc(v_w_4939_);
lean_inc(v_Q_4938_);
lean_inc(v_d_4937_);
lean_inc(v_L_4936_);
lean_inc(v_M_4935_);
lean_inc(v_D_4934_);
lean_inc(v_Y_4933_);
lean_inc(v_u_4932_);
lean_inc(v_y_4931_);
lean_inc(v_G_4930_);
lean_dec(v_date_4515_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4975_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4970_; 
if (v_isShared_4929_ == 0)
{
lean_ctor_set_tag(v___x_4928_, 1);
lean_ctor_set(v___x_4928_, 0, v_data_4517_);
v___x_4970_ = v___x_4928_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_data_4517_);
v___x_4970_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4972_; 
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 9, v___x_4970_);
v___x_4972_ = v___x_4967_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_G_4930_);
lean_ctor_set(v_reuseFailAlloc_4973_, 1, v_y_4931_);
lean_ctor_set(v_reuseFailAlloc_4973_, 2, v_u_4932_);
lean_ctor_set(v_reuseFailAlloc_4973_, 3, v_Y_4933_);
lean_ctor_set(v_reuseFailAlloc_4973_, 4, v_D_4934_);
lean_ctor_set(v_reuseFailAlloc_4973_, 5, v_M_4935_);
lean_ctor_set(v_reuseFailAlloc_4973_, 6, v_L_4936_);
lean_ctor_set(v_reuseFailAlloc_4973_, 7, v_d_4937_);
lean_ctor_set(v_reuseFailAlloc_4973_, 8, v_Q_4938_);
lean_ctor_set(v_reuseFailAlloc_4973_, 9, v___x_4970_);
lean_ctor_set(v_reuseFailAlloc_4973_, 10, v_w_4939_);
lean_ctor_set(v_reuseFailAlloc_4973_, 11, v_W_4940_);
lean_ctor_set(v_reuseFailAlloc_4973_, 12, v_E_4941_);
lean_ctor_set(v_reuseFailAlloc_4973_, 13, v_e_4942_);
lean_ctor_set(v_reuseFailAlloc_4973_, 14, v_c_4943_);
lean_ctor_set(v_reuseFailAlloc_4973_, 15, v_F_4944_);
lean_ctor_set(v_reuseFailAlloc_4973_, 16, v_a_4945_);
lean_ctor_set(v_reuseFailAlloc_4973_, 17, v_b_4946_);
lean_ctor_set(v_reuseFailAlloc_4973_, 18, v_B_4947_);
lean_ctor_set(v_reuseFailAlloc_4973_, 19, v_h_4948_);
lean_ctor_set(v_reuseFailAlloc_4973_, 20, v_K_4949_);
lean_ctor_set(v_reuseFailAlloc_4973_, 21, v_k_4950_);
lean_ctor_set(v_reuseFailAlloc_4973_, 22, v_H_4951_);
lean_ctor_set(v_reuseFailAlloc_4973_, 23, v_m_4952_);
lean_ctor_set(v_reuseFailAlloc_4973_, 24, v_s_4953_);
lean_ctor_set(v_reuseFailAlloc_4973_, 25, v_S_4954_);
lean_ctor_set(v_reuseFailAlloc_4973_, 26, v_A_4955_);
lean_ctor_set(v_reuseFailAlloc_4973_, 27, v_n_4956_);
lean_ctor_set(v_reuseFailAlloc_4973_, 28, v_N_4957_);
lean_ctor_set(v_reuseFailAlloc_4973_, 29, v_V_4958_);
lean_ctor_set(v_reuseFailAlloc_4973_, 30, v_z_4959_);
lean_ctor_set(v_reuseFailAlloc_4973_, 31, v_zabbrev_4960_);
lean_ctor_set(v_reuseFailAlloc_4973_, 32, v_v_4961_);
lean_ctor_set(v_reuseFailAlloc_4973_, 33, v_O_4962_);
lean_ctor_set(v_reuseFailAlloc_4973_, 34, v_X_4963_);
lean_ctor_set(v_reuseFailAlloc_4973_, 35, v_x_4964_);
lean_ctor_set(v_reuseFailAlloc_4973_, 36, v_Z_4965_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
}
case 9:
{
lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_5029_; 
v_isSharedCheck_5029_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5029_ == 0)
{
lean_object* v_unused_5030_; 
v_unused_5030_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5030_);
v___x_4980_ = v_modifier_4516_;
v_isShared_4981_ = v_isSharedCheck_5029_;
goto v_resetjp_4979_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_5029_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v_G_4982_; lean_object* v_y_4983_; lean_object* v_u_4984_; lean_object* v_D_4985_; lean_object* v_M_4986_; lean_object* v_L_4987_; lean_object* v_d_4988_; lean_object* v_Q_4989_; lean_object* v_q_4990_; lean_object* v_w_4991_; lean_object* v_W_4992_; lean_object* v_E_4993_; lean_object* v_e_4994_; lean_object* v_c_4995_; lean_object* v_F_4996_; lean_object* v_a_4997_; lean_object* v_b_4998_; lean_object* v_B_4999_; lean_object* v_h_5000_; lean_object* v_K_5001_; lean_object* v_k_5002_; lean_object* v_H_5003_; lean_object* v_m_5004_; lean_object* v_s_5005_; lean_object* v_S_5006_; lean_object* v_A_5007_; lean_object* v_n_5008_; lean_object* v_N_5009_; lean_object* v_V_5010_; lean_object* v_z_5011_; lean_object* v_zabbrev_5012_; lean_object* v_v_5013_; lean_object* v_O_5014_; lean_object* v_X_5015_; lean_object* v_x_5016_; lean_object* v_Z_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5027_; 
v_G_4982_ = lean_ctor_get(v_date_4515_, 0);
v_y_4983_ = lean_ctor_get(v_date_4515_, 1);
v_u_4984_ = lean_ctor_get(v_date_4515_, 2);
v_D_4985_ = lean_ctor_get(v_date_4515_, 4);
v_M_4986_ = lean_ctor_get(v_date_4515_, 5);
v_L_4987_ = lean_ctor_get(v_date_4515_, 6);
v_d_4988_ = lean_ctor_get(v_date_4515_, 7);
v_Q_4989_ = lean_ctor_get(v_date_4515_, 8);
v_q_4990_ = lean_ctor_get(v_date_4515_, 9);
v_w_4991_ = lean_ctor_get(v_date_4515_, 10);
v_W_4992_ = lean_ctor_get(v_date_4515_, 11);
v_E_4993_ = lean_ctor_get(v_date_4515_, 12);
v_e_4994_ = lean_ctor_get(v_date_4515_, 13);
v_c_4995_ = lean_ctor_get(v_date_4515_, 14);
v_F_4996_ = lean_ctor_get(v_date_4515_, 15);
v_a_4997_ = lean_ctor_get(v_date_4515_, 16);
v_b_4998_ = lean_ctor_get(v_date_4515_, 17);
v_B_4999_ = lean_ctor_get(v_date_4515_, 18);
v_h_5000_ = lean_ctor_get(v_date_4515_, 19);
v_K_5001_ = lean_ctor_get(v_date_4515_, 20);
v_k_5002_ = lean_ctor_get(v_date_4515_, 21);
v_H_5003_ = lean_ctor_get(v_date_4515_, 22);
v_m_5004_ = lean_ctor_get(v_date_4515_, 23);
v_s_5005_ = lean_ctor_get(v_date_4515_, 24);
v_S_5006_ = lean_ctor_get(v_date_4515_, 25);
v_A_5007_ = lean_ctor_get(v_date_4515_, 26);
v_n_5008_ = lean_ctor_get(v_date_4515_, 27);
v_N_5009_ = lean_ctor_get(v_date_4515_, 28);
v_V_5010_ = lean_ctor_get(v_date_4515_, 29);
v_z_5011_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5012_ = lean_ctor_get(v_date_4515_, 31);
v_v_5013_ = lean_ctor_get(v_date_4515_, 32);
v_O_5014_ = lean_ctor_get(v_date_4515_, 33);
v_X_5015_ = lean_ctor_get(v_date_4515_, 34);
v_x_5016_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5017_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5027_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5027_ == 0)
{
lean_object* v_unused_5028_; 
v_unused_5028_ = lean_ctor_get(v_date_4515_, 3);
lean_dec(v_unused_5028_);
v___x_5019_ = v_date_4515_;
v_isShared_5020_ = v_isSharedCheck_5027_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_Z_5017_);
lean_inc(v_x_5016_);
lean_inc(v_X_5015_);
lean_inc(v_O_5014_);
lean_inc(v_v_5013_);
lean_inc(v_zabbrev_5012_);
lean_inc(v_z_5011_);
lean_inc(v_V_5010_);
lean_inc(v_N_5009_);
lean_inc(v_n_5008_);
lean_inc(v_A_5007_);
lean_inc(v_S_5006_);
lean_inc(v_s_5005_);
lean_inc(v_m_5004_);
lean_inc(v_H_5003_);
lean_inc(v_k_5002_);
lean_inc(v_K_5001_);
lean_inc(v_h_5000_);
lean_inc(v_B_4999_);
lean_inc(v_b_4998_);
lean_inc(v_a_4997_);
lean_inc(v_F_4996_);
lean_inc(v_c_4995_);
lean_inc(v_e_4994_);
lean_inc(v_E_4993_);
lean_inc(v_W_4992_);
lean_inc(v_w_4991_);
lean_inc(v_q_4990_);
lean_inc(v_Q_4989_);
lean_inc(v_d_4988_);
lean_inc(v_L_4987_);
lean_inc(v_M_4986_);
lean_inc(v_D_4985_);
lean_inc(v_u_4984_);
lean_inc(v_y_4983_);
lean_inc(v_G_4982_);
lean_dec(v_date_4515_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5027_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5022_; 
if (v_isShared_4981_ == 0)
{
lean_ctor_set_tag(v___x_4980_, 1);
lean_ctor_set(v___x_4980_, 0, v_data_4517_);
v___x_5022_ = v___x_4980_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_data_4517_);
v___x_5022_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
lean_object* v___x_5024_; 
if (v_isShared_5020_ == 0)
{
lean_ctor_set(v___x_5019_, 3, v___x_5022_);
v___x_5024_ = v___x_5019_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_G_4982_);
lean_ctor_set(v_reuseFailAlloc_5025_, 1, v_y_4983_);
lean_ctor_set(v_reuseFailAlloc_5025_, 2, v_u_4984_);
lean_ctor_set(v_reuseFailAlloc_5025_, 3, v___x_5022_);
lean_ctor_set(v_reuseFailAlloc_5025_, 4, v_D_4985_);
lean_ctor_set(v_reuseFailAlloc_5025_, 5, v_M_4986_);
lean_ctor_set(v_reuseFailAlloc_5025_, 6, v_L_4987_);
lean_ctor_set(v_reuseFailAlloc_5025_, 7, v_d_4988_);
lean_ctor_set(v_reuseFailAlloc_5025_, 8, v_Q_4989_);
lean_ctor_set(v_reuseFailAlloc_5025_, 9, v_q_4990_);
lean_ctor_set(v_reuseFailAlloc_5025_, 10, v_w_4991_);
lean_ctor_set(v_reuseFailAlloc_5025_, 11, v_W_4992_);
lean_ctor_set(v_reuseFailAlloc_5025_, 12, v_E_4993_);
lean_ctor_set(v_reuseFailAlloc_5025_, 13, v_e_4994_);
lean_ctor_set(v_reuseFailAlloc_5025_, 14, v_c_4995_);
lean_ctor_set(v_reuseFailAlloc_5025_, 15, v_F_4996_);
lean_ctor_set(v_reuseFailAlloc_5025_, 16, v_a_4997_);
lean_ctor_set(v_reuseFailAlloc_5025_, 17, v_b_4998_);
lean_ctor_set(v_reuseFailAlloc_5025_, 18, v_B_4999_);
lean_ctor_set(v_reuseFailAlloc_5025_, 19, v_h_5000_);
lean_ctor_set(v_reuseFailAlloc_5025_, 20, v_K_5001_);
lean_ctor_set(v_reuseFailAlloc_5025_, 21, v_k_5002_);
lean_ctor_set(v_reuseFailAlloc_5025_, 22, v_H_5003_);
lean_ctor_set(v_reuseFailAlloc_5025_, 23, v_m_5004_);
lean_ctor_set(v_reuseFailAlloc_5025_, 24, v_s_5005_);
lean_ctor_set(v_reuseFailAlloc_5025_, 25, v_S_5006_);
lean_ctor_set(v_reuseFailAlloc_5025_, 26, v_A_5007_);
lean_ctor_set(v_reuseFailAlloc_5025_, 27, v_n_5008_);
lean_ctor_set(v_reuseFailAlloc_5025_, 28, v_N_5009_);
lean_ctor_set(v_reuseFailAlloc_5025_, 29, v_V_5010_);
lean_ctor_set(v_reuseFailAlloc_5025_, 30, v_z_5011_);
lean_ctor_set(v_reuseFailAlloc_5025_, 31, v_zabbrev_5012_);
lean_ctor_set(v_reuseFailAlloc_5025_, 32, v_v_5013_);
lean_ctor_set(v_reuseFailAlloc_5025_, 33, v_O_5014_);
lean_ctor_set(v_reuseFailAlloc_5025_, 34, v_X_5015_);
lean_ctor_set(v_reuseFailAlloc_5025_, 35, v_x_5016_);
lean_ctor_set(v_reuseFailAlloc_5025_, 36, v_Z_5017_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
}
case 10:
{
lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5081_; 
v_isSharedCheck_5081_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5081_ == 0)
{
lean_object* v_unused_5082_; 
v_unused_5082_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5082_);
v___x_5032_ = v_modifier_4516_;
v_isShared_5033_ = v_isSharedCheck_5081_;
goto v_resetjp_5031_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5081_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v_G_5034_; lean_object* v_y_5035_; lean_object* v_u_5036_; lean_object* v_Y_5037_; lean_object* v_D_5038_; lean_object* v_M_5039_; lean_object* v_L_5040_; lean_object* v_d_5041_; lean_object* v_Q_5042_; lean_object* v_q_5043_; lean_object* v_W_5044_; lean_object* v_E_5045_; lean_object* v_e_5046_; lean_object* v_c_5047_; lean_object* v_F_5048_; lean_object* v_a_5049_; lean_object* v_b_5050_; lean_object* v_B_5051_; lean_object* v_h_5052_; lean_object* v_K_5053_; lean_object* v_k_5054_; lean_object* v_H_5055_; lean_object* v_m_5056_; lean_object* v_s_5057_; lean_object* v_S_5058_; lean_object* v_A_5059_; lean_object* v_n_5060_; lean_object* v_N_5061_; lean_object* v_V_5062_; lean_object* v_z_5063_; lean_object* v_zabbrev_5064_; lean_object* v_v_5065_; lean_object* v_O_5066_; lean_object* v_X_5067_; lean_object* v_x_5068_; lean_object* v_Z_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5079_; 
v_G_5034_ = lean_ctor_get(v_date_4515_, 0);
v_y_5035_ = lean_ctor_get(v_date_4515_, 1);
v_u_5036_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5037_ = lean_ctor_get(v_date_4515_, 3);
v_D_5038_ = lean_ctor_get(v_date_4515_, 4);
v_M_5039_ = lean_ctor_get(v_date_4515_, 5);
v_L_5040_ = lean_ctor_get(v_date_4515_, 6);
v_d_5041_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5042_ = lean_ctor_get(v_date_4515_, 8);
v_q_5043_ = lean_ctor_get(v_date_4515_, 9);
v_W_5044_ = lean_ctor_get(v_date_4515_, 11);
v_E_5045_ = lean_ctor_get(v_date_4515_, 12);
v_e_5046_ = lean_ctor_get(v_date_4515_, 13);
v_c_5047_ = lean_ctor_get(v_date_4515_, 14);
v_F_5048_ = lean_ctor_get(v_date_4515_, 15);
v_a_5049_ = lean_ctor_get(v_date_4515_, 16);
v_b_5050_ = lean_ctor_get(v_date_4515_, 17);
v_B_5051_ = lean_ctor_get(v_date_4515_, 18);
v_h_5052_ = lean_ctor_get(v_date_4515_, 19);
v_K_5053_ = lean_ctor_get(v_date_4515_, 20);
v_k_5054_ = lean_ctor_get(v_date_4515_, 21);
v_H_5055_ = lean_ctor_get(v_date_4515_, 22);
v_m_5056_ = lean_ctor_get(v_date_4515_, 23);
v_s_5057_ = lean_ctor_get(v_date_4515_, 24);
v_S_5058_ = lean_ctor_get(v_date_4515_, 25);
v_A_5059_ = lean_ctor_get(v_date_4515_, 26);
v_n_5060_ = lean_ctor_get(v_date_4515_, 27);
v_N_5061_ = lean_ctor_get(v_date_4515_, 28);
v_V_5062_ = lean_ctor_get(v_date_4515_, 29);
v_z_5063_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5064_ = lean_ctor_get(v_date_4515_, 31);
v_v_5065_ = lean_ctor_get(v_date_4515_, 32);
v_O_5066_ = lean_ctor_get(v_date_4515_, 33);
v_X_5067_ = lean_ctor_get(v_date_4515_, 34);
v_x_5068_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5069_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5079_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5079_ == 0)
{
lean_object* v_unused_5080_; 
v_unused_5080_ = lean_ctor_get(v_date_4515_, 10);
lean_dec(v_unused_5080_);
v___x_5071_ = v_date_4515_;
v_isShared_5072_ = v_isSharedCheck_5079_;
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
lean_inc(v_B_5051_);
lean_inc(v_b_5050_);
lean_inc(v_a_5049_);
lean_inc(v_F_5048_);
lean_inc(v_c_5047_);
lean_inc(v_e_5046_);
lean_inc(v_E_5045_);
lean_inc(v_W_5044_);
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
lean_dec(v_date_4515_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5079_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5033_ == 0)
{
lean_ctor_set_tag(v___x_5032_, 1);
lean_ctor_set(v___x_5032_, 0, v_data_4517_);
v___x_5074_ = v___x_5032_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_data_4517_);
v___x_5074_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5076_; 
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 10, v___x_5074_);
v___x_5076_ = v___x_5071_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_G_5034_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v_y_5035_);
lean_ctor_set(v_reuseFailAlloc_5077_, 2, v_u_5036_);
lean_ctor_set(v_reuseFailAlloc_5077_, 3, v_Y_5037_);
lean_ctor_set(v_reuseFailAlloc_5077_, 4, v_D_5038_);
lean_ctor_set(v_reuseFailAlloc_5077_, 5, v_M_5039_);
lean_ctor_set(v_reuseFailAlloc_5077_, 6, v_L_5040_);
lean_ctor_set(v_reuseFailAlloc_5077_, 7, v_d_5041_);
lean_ctor_set(v_reuseFailAlloc_5077_, 8, v_Q_5042_);
lean_ctor_set(v_reuseFailAlloc_5077_, 9, v_q_5043_);
lean_ctor_set(v_reuseFailAlloc_5077_, 10, v___x_5074_);
lean_ctor_set(v_reuseFailAlloc_5077_, 11, v_W_5044_);
lean_ctor_set(v_reuseFailAlloc_5077_, 12, v_E_5045_);
lean_ctor_set(v_reuseFailAlloc_5077_, 13, v_e_5046_);
lean_ctor_set(v_reuseFailAlloc_5077_, 14, v_c_5047_);
lean_ctor_set(v_reuseFailAlloc_5077_, 15, v_F_5048_);
lean_ctor_set(v_reuseFailAlloc_5077_, 16, v_a_5049_);
lean_ctor_set(v_reuseFailAlloc_5077_, 17, v_b_5050_);
lean_ctor_set(v_reuseFailAlloc_5077_, 18, v_B_5051_);
lean_ctor_set(v_reuseFailAlloc_5077_, 19, v_h_5052_);
lean_ctor_set(v_reuseFailAlloc_5077_, 20, v_K_5053_);
lean_ctor_set(v_reuseFailAlloc_5077_, 21, v_k_5054_);
lean_ctor_set(v_reuseFailAlloc_5077_, 22, v_H_5055_);
lean_ctor_set(v_reuseFailAlloc_5077_, 23, v_m_5056_);
lean_ctor_set(v_reuseFailAlloc_5077_, 24, v_s_5057_);
lean_ctor_set(v_reuseFailAlloc_5077_, 25, v_S_5058_);
lean_ctor_set(v_reuseFailAlloc_5077_, 26, v_A_5059_);
lean_ctor_set(v_reuseFailAlloc_5077_, 27, v_n_5060_);
lean_ctor_set(v_reuseFailAlloc_5077_, 28, v_N_5061_);
lean_ctor_set(v_reuseFailAlloc_5077_, 29, v_V_5062_);
lean_ctor_set(v_reuseFailAlloc_5077_, 30, v_z_5063_);
lean_ctor_set(v_reuseFailAlloc_5077_, 31, v_zabbrev_5064_);
lean_ctor_set(v_reuseFailAlloc_5077_, 32, v_v_5065_);
lean_ctor_set(v_reuseFailAlloc_5077_, 33, v_O_5066_);
lean_ctor_set(v_reuseFailAlloc_5077_, 34, v_X_5067_);
lean_ctor_set(v_reuseFailAlloc_5077_, 35, v_x_5068_);
lean_ctor_set(v_reuseFailAlloc_5077_, 36, v_Z_5069_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
}
case 11:
{
lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5133_; 
v_isSharedCheck_5133_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5133_ == 0)
{
lean_object* v_unused_5134_; 
v_unused_5134_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5134_);
v___x_5084_ = v_modifier_4516_;
v_isShared_5085_ = v_isSharedCheck_5133_;
goto v_resetjp_5083_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5133_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v_G_5086_; lean_object* v_y_5087_; lean_object* v_u_5088_; lean_object* v_Y_5089_; lean_object* v_D_5090_; lean_object* v_M_5091_; lean_object* v_L_5092_; lean_object* v_d_5093_; lean_object* v_Q_5094_; lean_object* v_q_5095_; lean_object* v_w_5096_; lean_object* v_E_5097_; lean_object* v_e_5098_; lean_object* v_c_5099_; lean_object* v_F_5100_; lean_object* v_a_5101_; lean_object* v_b_5102_; lean_object* v_B_5103_; lean_object* v_h_5104_; lean_object* v_K_5105_; lean_object* v_k_5106_; lean_object* v_H_5107_; lean_object* v_m_5108_; lean_object* v_s_5109_; lean_object* v_S_5110_; lean_object* v_A_5111_; lean_object* v_n_5112_; lean_object* v_N_5113_; lean_object* v_V_5114_; lean_object* v_z_5115_; lean_object* v_zabbrev_5116_; lean_object* v_v_5117_; lean_object* v_O_5118_; lean_object* v_X_5119_; lean_object* v_x_5120_; lean_object* v_Z_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5131_; 
v_G_5086_ = lean_ctor_get(v_date_4515_, 0);
v_y_5087_ = lean_ctor_get(v_date_4515_, 1);
v_u_5088_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5089_ = lean_ctor_get(v_date_4515_, 3);
v_D_5090_ = lean_ctor_get(v_date_4515_, 4);
v_M_5091_ = lean_ctor_get(v_date_4515_, 5);
v_L_5092_ = lean_ctor_get(v_date_4515_, 6);
v_d_5093_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5094_ = lean_ctor_get(v_date_4515_, 8);
v_q_5095_ = lean_ctor_get(v_date_4515_, 9);
v_w_5096_ = lean_ctor_get(v_date_4515_, 10);
v_E_5097_ = lean_ctor_get(v_date_4515_, 12);
v_e_5098_ = lean_ctor_get(v_date_4515_, 13);
v_c_5099_ = lean_ctor_get(v_date_4515_, 14);
v_F_5100_ = lean_ctor_get(v_date_4515_, 15);
v_a_5101_ = lean_ctor_get(v_date_4515_, 16);
v_b_5102_ = lean_ctor_get(v_date_4515_, 17);
v_B_5103_ = lean_ctor_get(v_date_4515_, 18);
v_h_5104_ = lean_ctor_get(v_date_4515_, 19);
v_K_5105_ = lean_ctor_get(v_date_4515_, 20);
v_k_5106_ = lean_ctor_get(v_date_4515_, 21);
v_H_5107_ = lean_ctor_get(v_date_4515_, 22);
v_m_5108_ = lean_ctor_get(v_date_4515_, 23);
v_s_5109_ = lean_ctor_get(v_date_4515_, 24);
v_S_5110_ = lean_ctor_get(v_date_4515_, 25);
v_A_5111_ = lean_ctor_get(v_date_4515_, 26);
v_n_5112_ = lean_ctor_get(v_date_4515_, 27);
v_N_5113_ = lean_ctor_get(v_date_4515_, 28);
v_V_5114_ = lean_ctor_get(v_date_4515_, 29);
v_z_5115_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5116_ = lean_ctor_get(v_date_4515_, 31);
v_v_5117_ = lean_ctor_get(v_date_4515_, 32);
v_O_5118_ = lean_ctor_get(v_date_4515_, 33);
v_X_5119_ = lean_ctor_get(v_date_4515_, 34);
v_x_5120_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5121_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5131_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5131_ == 0)
{
lean_object* v_unused_5132_; 
v_unused_5132_ = lean_ctor_get(v_date_4515_, 11);
lean_dec(v_unused_5132_);
v___x_5123_ = v_date_4515_;
v_isShared_5124_ = v_isSharedCheck_5131_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_Z_5121_);
lean_inc(v_x_5120_);
lean_inc(v_X_5119_);
lean_inc(v_O_5118_);
lean_inc(v_v_5117_);
lean_inc(v_zabbrev_5116_);
lean_inc(v_z_5115_);
lean_inc(v_V_5114_);
lean_inc(v_N_5113_);
lean_inc(v_n_5112_);
lean_inc(v_A_5111_);
lean_inc(v_S_5110_);
lean_inc(v_s_5109_);
lean_inc(v_m_5108_);
lean_inc(v_H_5107_);
lean_inc(v_k_5106_);
lean_inc(v_K_5105_);
lean_inc(v_h_5104_);
lean_inc(v_B_5103_);
lean_inc(v_b_5102_);
lean_inc(v_a_5101_);
lean_inc(v_F_5100_);
lean_inc(v_c_5099_);
lean_inc(v_e_5098_);
lean_inc(v_E_5097_);
lean_inc(v_w_5096_);
lean_inc(v_q_5095_);
lean_inc(v_Q_5094_);
lean_inc(v_d_5093_);
lean_inc(v_L_5092_);
lean_inc(v_M_5091_);
lean_inc(v_D_5090_);
lean_inc(v_Y_5089_);
lean_inc(v_u_5088_);
lean_inc(v_y_5087_);
lean_inc(v_G_5086_);
lean_dec(v_date_4515_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5131_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5085_ == 0)
{
lean_ctor_set_tag(v___x_5084_, 1);
lean_ctor_set(v___x_5084_, 0, v_data_4517_);
v___x_5126_ = v___x_5084_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_data_4517_);
v___x_5126_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
lean_object* v___x_5128_; 
if (v_isShared_5124_ == 0)
{
lean_ctor_set(v___x_5123_, 11, v___x_5126_);
v___x_5128_ = v___x_5123_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_G_5086_);
lean_ctor_set(v_reuseFailAlloc_5129_, 1, v_y_5087_);
lean_ctor_set(v_reuseFailAlloc_5129_, 2, v_u_5088_);
lean_ctor_set(v_reuseFailAlloc_5129_, 3, v_Y_5089_);
lean_ctor_set(v_reuseFailAlloc_5129_, 4, v_D_5090_);
lean_ctor_set(v_reuseFailAlloc_5129_, 5, v_M_5091_);
lean_ctor_set(v_reuseFailAlloc_5129_, 6, v_L_5092_);
lean_ctor_set(v_reuseFailAlloc_5129_, 7, v_d_5093_);
lean_ctor_set(v_reuseFailAlloc_5129_, 8, v_Q_5094_);
lean_ctor_set(v_reuseFailAlloc_5129_, 9, v_q_5095_);
lean_ctor_set(v_reuseFailAlloc_5129_, 10, v_w_5096_);
lean_ctor_set(v_reuseFailAlloc_5129_, 11, v___x_5126_);
lean_ctor_set(v_reuseFailAlloc_5129_, 12, v_E_5097_);
lean_ctor_set(v_reuseFailAlloc_5129_, 13, v_e_5098_);
lean_ctor_set(v_reuseFailAlloc_5129_, 14, v_c_5099_);
lean_ctor_set(v_reuseFailAlloc_5129_, 15, v_F_5100_);
lean_ctor_set(v_reuseFailAlloc_5129_, 16, v_a_5101_);
lean_ctor_set(v_reuseFailAlloc_5129_, 17, v_b_5102_);
lean_ctor_set(v_reuseFailAlloc_5129_, 18, v_B_5103_);
lean_ctor_set(v_reuseFailAlloc_5129_, 19, v_h_5104_);
lean_ctor_set(v_reuseFailAlloc_5129_, 20, v_K_5105_);
lean_ctor_set(v_reuseFailAlloc_5129_, 21, v_k_5106_);
lean_ctor_set(v_reuseFailAlloc_5129_, 22, v_H_5107_);
lean_ctor_set(v_reuseFailAlloc_5129_, 23, v_m_5108_);
lean_ctor_set(v_reuseFailAlloc_5129_, 24, v_s_5109_);
lean_ctor_set(v_reuseFailAlloc_5129_, 25, v_S_5110_);
lean_ctor_set(v_reuseFailAlloc_5129_, 26, v_A_5111_);
lean_ctor_set(v_reuseFailAlloc_5129_, 27, v_n_5112_);
lean_ctor_set(v_reuseFailAlloc_5129_, 28, v_N_5113_);
lean_ctor_set(v_reuseFailAlloc_5129_, 29, v_V_5114_);
lean_ctor_set(v_reuseFailAlloc_5129_, 30, v_z_5115_);
lean_ctor_set(v_reuseFailAlloc_5129_, 31, v_zabbrev_5116_);
lean_ctor_set(v_reuseFailAlloc_5129_, 32, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5129_, 33, v_O_5118_);
lean_ctor_set(v_reuseFailAlloc_5129_, 34, v_X_5119_);
lean_ctor_set(v_reuseFailAlloc_5129_, 35, v_x_5120_);
lean_ctor_set(v_reuseFailAlloc_5129_, 36, v_Z_5121_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
}
case 12:
{
lean_object* v_G_5135_; lean_object* v_y_5136_; lean_object* v_u_5137_; lean_object* v_Y_5138_; lean_object* v_D_5139_; lean_object* v_M_5140_; lean_object* v_L_5141_; lean_object* v_d_5142_; lean_object* v_Q_5143_; lean_object* v_q_5144_; lean_object* v_w_5145_; lean_object* v_W_5146_; lean_object* v_e_5147_; lean_object* v_c_5148_; lean_object* v_F_5149_; lean_object* v_a_5150_; lean_object* v_b_5151_; lean_object* v_B_5152_; lean_object* v_h_5153_; lean_object* v_K_5154_; lean_object* v_k_5155_; lean_object* v_H_5156_; lean_object* v_m_5157_; lean_object* v_s_5158_; lean_object* v_S_5159_; lean_object* v_A_5160_; lean_object* v_n_5161_; lean_object* v_N_5162_; lean_object* v_V_5163_; lean_object* v_z_5164_; lean_object* v_zabbrev_5165_; lean_object* v_v_5166_; lean_object* v_O_5167_; lean_object* v_X_5168_; lean_object* v_x_5169_; lean_object* v_Z_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5178_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_G_5135_ = lean_ctor_get(v_date_4515_, 0);
v_y_5136_ = lean_ctor_get(v_date_4515_, 1);
v_u_5137_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5138_ = lean_ctor_get(v_date_4515_, 3);
v_D_5139_ = lean_ctor_get(v_date_4515_, 4);
v_M_5140_ = lean_ctor_get(v_date_4515_, 5);
v_L_5141_ = lean_ctor_get(v_date_4515_, 6);
v_d_5142_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5143_ = lean_ctor_get(v_date_4515_, 8);
v_q_5144_ = lean_ctor_get(v_date_4515_, 9);
v_w_5145_ = lean_ctor_get(v_date_4515_, 10);
v_W_5146_ = lean_ctor_get(v_date_4515_, 11);
v_e_5147_ = lean_ctor_get(v_date_4515_, 13);
v_c_5148_ = lean_ctor_get(v_date_4515_, 14);
v_F_5149_ = lean_ctor_get(v_date_4515_, 15);
v_a_5150_ = lean_ctor_get(v_date_4515_, 16);
v_b_5151_ = lean_ctor_get(v_date_4515_, 17);
v_B_5152_ = lean_ctor_get(v_date_4515_, 18);
v_h_5153_ = lean_ctor_get(v_date_4515_, 19);
v_K_5154_ = lean_ctor_get(v_date_4515_, 20);
v_k_5155_ = lean_ctor_get(v_date_4515_, 21);
v_H_5156_ = lean_ctor_get(v_date_4515_, 22);
v_m_5157_ = lean_ctor_get(v_date_4515_, 23);
v_s_5158_ = lean_ctor_get(v_date_4515_, 24);
v_S_5159_ = lean_ctor_get(v_date_4515_, 25);
v_A_5160_ = lean_ctor_get(v_date_4515_, 26);
v_n_5161_ = lean_ctor_get(v_date_4515_, 27);
v_N_5162_ = lean_ctor_get(v_date_4515_, 28);
v_V_5163_ = lean_ctor_get(v_date_4515_, 29);
v_z_5164_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5165_ = lean_ctor_get(v_date_4515_, 31);
v_v_5166_ = lean_ctor_get(v_date_4515_, 32);
v_O_5167_ = lean_ctor_get(v_date_4515_, 33);
v_X_5168_ = lean_ctor_get(v_date_4515_, 34);
v_x_5169_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5170_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5178_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5178_ == 0)
{
lean_object* v_unused_5179_; 
v_unused_5179_ = lean_ctor_get(v_date_4515_, 12);
lean_dec(v_unused_5179_);
v___x_5172_ = v_date_4515_;
v_isShared_5173_ = v_isSharedCheck_5178_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_Z_5170_);
lean_inc(v_x_5169_);
lean_inc(v_X_5168_);
lean_inc(v_O_5167_);
lean_inc(v_v_5166_);
lean_inc(v_zabbrev_5165_);
lean_inc(v_z_5164_);
lean_inc(v_V_5163_);
lean_inc(v_N_5162_);
lean_inc(v_n_5161_);
lean_inc(v_A_5160_);
lean_inc(v_S_5159_);
lean_inc(v_s_5158_);
lean_inc(v_m_5157_);
lean_inc(v_H_5156_);
lean_inc(v_k_5155_);
lean_inc(v_K_5154_);
lean_inc(v_h_5153_);
lean_inc(v_B_5152_);
lean_inc(v_b_5151_);
lean_inc(v_a_5150_);
lean_inc(v_F_5149_);
lean_inc(v_c_5148_);
lean_inc(v_e_5147_);
lean_inc(v_W_5146_);
lean_inc(v_w_5145_);
lean_inc(v_q_5144_);
lean_inc(v_Q_5143_);
lean_inc(v_d_5142_);
lean_inc(v_L_5141_);
lean_inc(v_M_5140_);
lean_inc(v_D_5139_);
lean_inc(v_Y_5138_);
lean_inc(v_u_5137_);
lean_inc(v_y_5136_);
lean_inc(v_G_5135_);
lean_dec(v_date_4515_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5178_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5174_; lean_object* v___x_5176_; 
v___x_5174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5174_, 0, v_data_4517_);
if (v_isShared_5173_ == 0)
{
lean_ctor_set(v___x_5172_, 12, v___x_5174_);
v___x_5176_ = v___x_5172_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_G_5135_);
lean_ctor_set(v_reuseFailAlloc_5177_, 1, v_y_5136_);
lean_ctor_set(v_reuseFailAlloc_5177_, 2, v_u_5137_);
lean_ctor_set(v_reuseFailAlloc_5177_, 3, v_Y_5138_);
lean_ctor_set(v_reuseFailAlloc_5177_, 4, v_D_5139_);
lean_ctor_set(v_reuseFailAlloc_5177_, 5, v_M_5140_);
lean_ctor_set(v_reuseFailAlloc_5177_, 6, v_L_5141_);
lean_ctor_set(v_reuseFailAlloc_5177_, 7, v_d_5142_);
lean_ctor_set(v_reuseFailAlloc_5177_, 8, v_Q_5143_);
lean_ctor_set(v_reuseFailAlloc_5177_, 9, v_q_5144_);
lean_ctor_set(v_reuseFailAlloc_5177_, 10, v_w_5145_);
lean_ctor_set(v_reuseFailAlloc_5177_, 11, v_W_5146_);
lean_ctor_set(v_reuseFailAlloc_5177_, 12, v___x_5174_);
lean_ctor_set(v_reuseFailAlloc_5177_, 13, v_e_5147_);
lean_ctor_set(v_reuseFailAlloc_5177_, 14, v_c_5148_);
lean_ctor_set(v_reuseFailAlloc_5177_, 15, v_F_5149_);
lean_ctor_set(v_reuseFailAlloc_5177_, 16, v_a_5150_);
lean_ctor_set(v_reuseFailAlloc_5177_, 17, v_b_5151_);
lean_ctor_set(v_reuseFailAlloc_5177_, 18, v_B_5152_);
lean_ctor_set(v_reuseFailAlloc_5177_, 19, v_h_5153_);
lean_ctor_set(v_reuseFailAlloc_5177_, 20, v_K_5154_);
lean_ctor_set(v_reuseFailAlloc_5177_, 21, v_k_5155_);
lean_ctor_set(v_reuseFailAlloc_5177_, 22, v_H_5156_);
lean_ctor_set(v_reuseFailAlloc_5177_, 23, v_m_5157_);
lean_ctor_set(v_reuseFailAlloc_5177_, 24, v_s_5158_);
lean_ctor_set(v_reuseFailAlloc_5177_, 25, v_S_5159_);
lean_ctor_set(v_reuseFailAlloc_5177_, 26, v_A_5160_);
lean_ctor_set(v_reuseFailAlloc_5177_, 27, v_n_5161_);
lean_ctor_set(v_reuseFailAlloc_5177_, 28, v_N_5162_);
lean_ctor_set(v_reuseFailAlloc_5177_, 29, v_V_5163_);
lean_ctor_set(v_reuseFailAlloc_5177_, 30, v_z_5164_);
lean_ctor_set(v_reuseFailAlloc_5177_, 31, v_zabbrev_5165_);
lean_ctor_set(v_reuseFailAlloc_5177_, 32, v_v_5166_);
lean_ctor_set(v_reuseFailAlloc_5177_, 33, v_O_5167_);
lean_ctor_set(v_reuseFailAlloc_5177_, 34, v_X_5168_);
lean_ctor_set(v_reuseFailAlloc_5177_, 35, v_x_5169_);
lean_ctor_set(v_reuseFailAlloc_5177_, 36, v_Z_5170_);
v___x_5176_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
return v___x_5176_;
}
}
}
case 13:
{
lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5230_; 
v_isSharedCheck_5230_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5230_ == 0)
{
lean_object* v_unused_5231_; 
v_unused_5231_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5231_);
v___x_5181_ = v_modifier_4516_;
v_isShared_5182_ = v_isSharedCheck_5230_;
goto v_resetjp_5180_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5230_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v_G_5183_; lean_object* v_y_5184_; lean_object* v_u_5185_; lean_object* v_Y_5186_; lean_object* v_D_5187_; lean_object* v_M_5188_; lean_object* v_L_5189_; lean_object* v_d_5190_; lean_object* v_Q_5191_; lean_object* v_q_5192_; lean_object* v_w_5193_; lean_object* v_W_5194_; lean_object* v_E_5195_; lean_object* v_c_5196_; lean_object* v_F_5197_; lean_object* v_a_5198_; lean_object* v_b_5199_; lean_object* v_B_5200_; lean_object* v_h_5201_; lean_object* v_K_5202_; lean_object* v_k_5203_; lean_object* v_H_5204_; lean_object* v_m_5205_; lean_object* v_s_5206_; lean_object* v_S_5207_; lean_object* v_A_5208_; lean_object* v_n_5209_; lean_object* v_N_5210_; lean_object* v_V_5211_; lean_object* v_z_5212_; lean_object* v_zabbrev_5213_; lean_object* v_v_5214_; lean_object* v_O_5215_; lean_object* v_X_5216_; lean_object* v_x_5217_; lean_object* v_Z_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5228_; 
v_G_5183_ = lean_ctor_get(v_date_4515_, 0);
v_y_5184_ = lean_ctor_get(v_date_4515_, 1);
v_u_5185_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5186_ = lean_ctor_get(v_date_4515_, 3);
v_D_5187_ = lean_ctor_get(v_date_4515_, 4);
v_M_5188_ = lean_ctor_get(v_date_4515_, 5);
v_L_5189_ = lean_ctor_get(v_date_4515_, 6);
v_d_5190_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5191_ = lean_ctor_get(v_date_4515_, 8);
v_q_5192_ = lean_ctor_get(v_date_4515_, 9);
v_w_5193_ = lean_ctor_get(v_date_4515_, 10);
v_W_5194_ = lean_ctor_get(v_date_4515_, 11);
v_E_5195_ = lean_ctor_get(v_date_4515_, 12);
v_c_5196_ = lean_ctor_get(v_date_4515_, 14);
v_F_5197_ = lean_ctor_get(v_date_4515_, 15);
v_a_5198_ = lean_ctor_get(v_date_4515_, 16);
v_b_5199_ = lean_ctor_get(v_date_4515_, 17);
v_B_5200_ = lean_ctor_get(v_date_4515_, 18);
v_h_5201_ = lean_ctor_get(v_date_4515_, 19);
v_K_5202_ = lean_ctor_get(v_date_4515_, 20);
v_k_5203_ = lean_ctor_get(v_date_4515_, 21);
v_H_5204_ = lean_ctor_get(v_date_4515_, 22);
v_m_5205_ = lean_ctor_get(v_date_4515_, 23);
v_s_5206_ = lean_ctor_get(v_date_4515_, 24);
v_S_5207_ = lean_ctor_get(v_date_4515_, 25);
v_A_5208_ = lean_ctor_get(v_date_4515_, 26);
v_n_5209_ = lean_ctor_get(v_date_4515_, 27);
v_N_5210_ = lean_ctor_get(v_date_4515_, 28);
v_V_5211_ = lean_ctor_get(v_date_4515_, 29);
v_z_5212_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5213_ = lean_ctor_get(v_date_4515_, 31);
v_v_5214_ = lean_ctor_get(v_date_4515_, 32);
v_O_5215_ = lean_ctor_get(v_date_4515_, 33);
v_X_5216_ = lean_ctor_get(v_date_4515_, 34);
v_x_5217_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5218_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5228_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5228_ == 0)
{
lean_object* v_unused_5229_; 
v_unused_5229_ = lean_ctor_get(v_date_4515_, 13);
lean_dec(v_unused_5229_);
v___x_5220_ = v_date_4515_;
v_isShared_5221_ = v_isSharedCheck_5228_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_Z_5218_);
lean_inc(v_x_5217_);
lean_inc(v_X_5216_);
lean_inc(v_O_5215_);
lean_inc(v_v_5214_);
lean_inc(v_zabbrev_5213_);
lean_inc(v_z_5212_);
lean_inc(v_V_5211_);
lean_inc(v_N_5210_);
lean_inc(v_n_5209_);
lean_inc(v_A_5208_);
lean_inc(v_S_5207_);
lean_inc(v_s_5206_);
lean_inc(v_m_5205_);
lean_inc(v_H_5204_);
lean_inc(v_k_5203_);
lean_inc(v_K_5202_);
lean_inc(v_h_5201_);
lean_inc(v_B_5200_);
lean_inc(v_b_5199_);
lean_inc(v_a_5198_);
lean_inc(v_F_5197_);
lean_inc(v_c_5196_);
lean_inc(v_E_5195_);
lean_inc(v_W_5194_);
lean_inc(v_w_5193_);
lean_inc(v_q_5192_);
lean_inc(v_Q_5191_);
lean_inc(v_d_5190_);
lean_inc(v_L_5189_);
lean_inc(v_M_5188_);
lean_inc(v_D_5187_);
lean_inc(v_Y_5186_);
lean_inc(v_u_5185_);
lean_inc(v_y_5184_);
lean_inc(v_G_5183_);
lean_dec(v_date_4515_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5228_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5182_ == 0)
{
lean_ctor_set_tag(v___x_5181_, 1);
lean_ctor_set(v___x_5181_, 0, v_data_4517_);
v___x_5223_ = v___x_5181_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_data_4517_);
v___x_5223_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
lean_object* v___x_5225_; 
if (v_isShared_5221_ == 0)
{
lean_ctor_set(v___x_5220_, 13, v___x_5223_);
v___x_5225_ = v___x_5220_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_G_5183_);
lean_ctor_set(v_reuseFailAlloc_5226_, 1, v_y_5184_);
lean_ctor_set(v_reuseFailAlloc_5226_, 2, v_u_5185_);
lean_ctor_set(v_reuseFailAlloc_5226_, 3, v_Y_5186_);
lean_ctor_set(v_reuseFailAlloc_5226_, 4, v_D_5187_);
lean_ctor_set(v_reuseFailAlloc_5226_, 5, v_M_5188_);
lean_ctor_set(v_reuseFailAlloc_5226_, 6, v_L_5189_);
lean_ctor_set(v_reuseFailAlloc_5226_, 7, v_d_5190_);
lean_ctor_set(v_reuseFailAlloc_5226_, 8, v_Q_5191_);
lean_ctor_set(v_reuseFailAlloc_5226_, 9, v_q_5192_);
lean_ctor_set(v_reuseFailAlloc_5226_, 10, v_w_5193_);
lean_ctor_set(v_reuseFailAlloc_5226_, 11, v_W_5194_);
lean_ctor_set(v_reuseFailAlloc_5226_, 12, v_E_5195_);
lean_ctor_set(v_reuseFailAlloc_5226_, 13, v___x_5223_);
lean_ctor_set(v_reuseFailAlloc_5226_, 14, v_c_5196_);
lean_ctor_set(v_reuseFailAlloc_5226_, 15, v_F_5197_);
lean_ctor_set(v_reuseFailAlloc_5226_, 16, v_a_5198_);
lean_ctor_set(v_reuseFailAlloc_5226_, 17, v_b_5199_);
lean_ctor_set(v_reuseFailAlloc_5226_, 18, v_B_5200_);
lean_ctor_set(v_reuseFailAlloc_5226_, 19, v_h_5201_);
lean_ctor_set(v_reuseFailAlloc_5226_, 20, v_K_5202_);
lean_ctor_set(v_reuseFailAlloc_5226_, 21, v_k_5203_);
lean_ctor_set(v_reuseFailAlloc_5226_, 22, v_H_5204_);
lean_ctor_set(v_reuseFailAlloc_5226_, 23, v_m_5205_);
lean_ctor_set(v_reuseFailAlloc_5226_, 24, v_s_5206_);
lean_ctor_set(v_reuseFailAlloc_5226_, 25, v_S_5207_);
lean_ctor_set(v_reuseFailAlloc_5226_, 26, v_A_5208_);
lean_ctor_set(v_reuseFailAlloc_5226_, 27, v_n_5209_);
lean_ctor_set(v_reuseFailAlloc_5226_, 28, v_N_5210_);
lean_ctor_set(v_reuseFailAlloc_5226_, 29, v_V_5211_);
lean_ctor_set(v_reuseFailAlloc_5226_, 30, v_z_5212_);
lean_ctor_set(v_reuseFailAlloc_5226_, 31, v_zabbrev_5213_);
lean_ctor_set(v_reuseFailAlloc_5226_, 32, v_v_5214_);
lean_ctor_set(v_reuseFailAlloc_5226_, 33, v_O_5215_);
lean_ctor_set(v_reuseFailAlloc_5226_, 34, v_X_5216_);
lean_ctor_set(v_reuseFailAlloc_5226_, 35, v_x_5217_);
lean_ctor_set(v_reuseFailAlloc_5226_, 36, v_Z_5218_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
}
case 14:
{
lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5282_; 
v_isSharedCheck_5282_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5282_ == 0)
{
lean_object* v_unused_5283_; 
v_unused_5283_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5283_);
v___x_5233_ = v_modifier_4516_;
v_isShared_5234_ = v_isSharedCheck_5282_;
goto v_resetjp_5232_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5282_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v_G_5235_; lean_object* v_y_5236_; lean_object* v_u_5237_; lean_object* v_Y_5238_; lean_object* v_D_5239_; lean_object* v_M_5240_; lean_object* v_L_5241_; lean_object* v_d_5242_; lean_object* v_Q_5243_; lean_object* v_q_5244_; lean_object* v_w_5245_; lean_object* v_W_5246_; lean_object* v_E_5247_; lean_object* v_e_5248_; lean_object* v_F_5249_; lean_object* v_a_5250_; lean_object* v_b_5251_; lean_object* v_B_5252_; lean_object* v_h_5253_; lean_object* v_K_5254_; lean_object* v_k_5255_; lean_object* v_H_5256_; lean_object* v_m_5257_; lean_object* v_s_5258_; lean_object* v_S_5259_; lean_object* v_A_5260_; lean_object* v_n_5261_; lean_object* v_N_5262_; lean_object* v_V_5263_; lean_object* v_z_5264_; lean_object* v_zabbrev_5265_; lean_object* v_v_5266_; lean_object* v_O_5267_; lean_object* v_X_5268_; lean_object* v_x_5269_; lean_object* v_Z_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5280_; 
v_G_5235_ = lean_ctor_get(v_date_4515_, 0);
v_y_5236_ = lean_ctor_get(v_date_4515_, 1);
v_u_5237_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5238_ = lean_ctor_get(v_date_4515_, 3);
v_D_5239_ = lean_ctor_get(v_date_4515_, 4);
v_M_5240_ = lean_ctor_get(v_date_4515_, 5);
v_L_5241_ = lean_ctor_get(v_date_4515_, 6);
v_d_5242_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5243_ = lean_ctor_get(v_date_4515_, 8);
v_q_5244_ = lean_ctor_get(v_date_4515_, 9);
v_w_5245_ = lean_ctor_get(v_date_4515_, 10);
v_W_5246_ = lean_ctor_get(v_date_4515_, 11);
v_E_5247_ = lean_ctor_get(v_date_4515_, 12);
v_e_5248_ = lean_ctor_get(v_date_4515_, 13);
v_F_5249_ = lean_ctor_get(v_date_4515_, 15);
v_a_5250_ = lean_ctor_get(v_date_4515_, 16);
v_b_5251_ = lean_ctor_get(v_date_4515_, 17);
v_B_5252_ = lean_ctor_get(v_date_4515_, 18);
v_h_5253_ = lean_ctor_get(v_date_4515_, 19);
v_K_5254_ = lean_ctor_get(v_date_4515_, 20);
v_k_5255_ = lean_ctor_get(v_date_4515_, 21);
v_H_5256_ = lean_ctor_get(v_date_4515_, 22);
v_m_5257_ = lean_ctor_get(v_date_4515_, 23);
v_s_5258_ = lean_ctor_get(v_date_4515_, 24);
v_S_5259_ = lean_ctor_get(v_date_4515_, 25);
v_A_5260_ = lean_ctor_get(v_date_4515_, 26);
v_n_5261_ = lean_ctor_get(v_date_4515_, 27);
v_N_5262_ = lean_ctor_get(v_date_4515_, 28);
v_V_5263_ = lean_ctor_get(v_date_4515_, 29);
v_z_5264_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5265_ = lean_ctor_get(v_date_4515_, 31);
v_v_5266_ = lean_ctor_get(v_date_4515_, 32);
v_O_5267_ = lean_ctor_get(v_date_4515_, 33);
v_X_5268_ = lean_ctor_get(v_date_4515_, 34);
v_x_5269_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5270_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5280_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5280_ == 0)
{
lean_object* v_unused_5281_; 
v_unused_5281_ = lean_ctor_get(v_date_4515_, 14);
lean_dec(v_unused_5281_);
v___x_5272_ = v_date_4515_;
v_isShared_5273_ = v_isSharedCheck_5280_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_Z_5270_);
lean_inc(v_x_5269_);
lean_inc(v_X_5268_);
lean_inc(v_O_5267_);
lean_inc(v_v_5266_);
lean_inc(v_zabbrev_5265_);
lean_inc(v_z_5264_);
lean_inc(v_V_5263_);
lean_inc(v_N_5262_);
lean_inc(v_n_5261_);
lean_inc(v_A_5260_);
lean_inc(v_S_5259_);
lean_inc(v_s_5258_);
lean_inc(v_m_5257_);
lean_inc(v_H_5256_);
lean_inc(v_k_5255_);
lean_inc(v_K_5254_);
lean_inc(v_h_5253_);
lean_inc(v_B_5252_);
lean_inc(v_b_5251_);
lean_inc(v_a_5250_);
lean_inc(v_F_5249_);
lean_inc(v_e_5248_);
lean_inc(v_E_5247_);
lean_inc(v_W_5246_);
lean_inc(v_w_5245_);
lean_inc(v_q_5244_);
lean_inc(v_Q_5243_);
lean_inc(v_d_5242_);
lean_inc(v_L_5241_);
lean_inc(v_M_5240_);
lean_inc(v_D_5239_);
lean_inc(v_Y_5238_);
lean_inc(v_u_5237_);
lean_inc(v_y_5236_);
lean_inc(v_G_5235_);
lean_dec(v_date_4515_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5280_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5275_; 
if (v_isShared_5234_ == 0)
{
lean_ctor_set_tag(v___x_5233_, 1);
lean_ctor_set(v___x_5233_, 0, v_data_4517_);
v___x_5275_ = v___x_5233_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v_data_4517_);
v___x_5275_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
lean_object* v___x_5277_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 14, v___x_5275_);
v___x_5277_ = v___x_5272_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v_G_5235_);
lean_ctor_set(v_reuseFailAlloc_5278_, 1, v_y_5236_);
lean_ctor_set(v_reuseFailAlloc_5278_, 2, v_u_5237_);
lean_ctor_set(v_reuseFailAlloc_5278_, 3, v_Y_5238_);
lean_ctor_set(v_reuseFailAlloc_5278_, 4, v_D_5239_);
lean_ctor_set(v_reuseFailAlloc_5278_, 5, v_M_5240_);
lean_ctor_set(v_reuseFailAlloc_5278_, 6, v_L_5241_);
lean_ctor_set(v_reuseFailAlloc_5278_, 7, v_d_5242_);
lean_ctor_set(v_reuseFailAlloc_5278_, 8, v_Q_5243_);
lean_ctor_set(v_reuseFailAlloc_5278_, 9, v_q_5244_);
lean_ctor_set(v_reuseFailAlloc_5278_, 10, v_w_5245_);
lean_ctor_set(v_reuseFailAlloc_5278_, 11, v_W_5246_);
lean_ctor_set(v_reuseFailAlloc_5278_, 12, v_E_5247_);
lean_ctor_set(v_reuseFailAlloc_5278_, 13, v_e_5248_);
lean_ctor_set(v_reuseFailAlloc_5278_, 14, v___x_5275_);
lean_ctor_set(v_reuseFailAlloc_5278_, 15, v_F_5249_);
lean_ctor_set(v_reuseFailAlloc_5278_, 16, v_a_5250_);
lean_ctor_set(v_reuseFailAlloc_5278_, 17, v_b_5251_);
lean_ctor_set(v_reuseFailAlloc_5278_, 18, v_B_5252_);
lean_ctor_set(v_reuseFailAlloc_5278_, 19, v_h_5253_);
lean_ctor_set(v_reuseFailAlloc_5278_, 20, v_K_5254_);
lean_ctor_set(v_reuseFailAlloc_5278_, 21, v_k_5255_);
lean_ctor_set(v_reuseFailAlloc_5278_, 22, v_H_5256_);
lean_ctor_set(v_reuseFailAlloc_5278_, 23, v_m_5257_);
lean_ctor_set(v_reuseFailAlloc_5278_, 24, v_s_5258_);
lean_ctor_set(v_reuseFailAlloc_5278_, 25, v_S_5259_);
lean_ctor_set(v_reuseFailAlloc_5278_, 26, v_A_5260_);
lean_ctor_set(v_reuseFailAlloc_5278_, 27, v_n_5261_);
lean_ctor_set(v_reuseFailAlloc_5278_, 28, v_N_5262_);
lean_ctor_set(v_reuseFailAlloc_5278_, 29, v_V_5263_);
lean_ctor_set(v_reuseFailAlloc_5278_, 30, v_z_5264_);
lean_ctor_set(v_reuseFailAlloc_5278_, 31, v_zabbrev_5265_);
lean_ctor_set(v_reuseFailAlloc_5278_, 32, v_v_5266_);
lean_ctor_set(v_reuseFailAlloc_5278_, 33, v_O_5267_);
lean_ctor_set(v_reuseFailAlloc_5278_, 34, v_X_5268_);
lean_ctor_set(v_reuseFailAlloc_5278_, 35, v_x_5269_);
lean_ctor_set(v_reuseFailAlloc_5278_, 36, v_Z_5270_);
v___x_5277_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
return v___x_5277_;
}
}
}
}
}
case 15:
{
lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5334_; 
v_isSharedCheck_5334_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5334_ == 0)
{
lean_object* v_unused_5335_; 
v_unused_5335_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5335_);
v___x_5285_ = v_modifier_4516_;
v_isShared_5286_ = v_isSharedCheck_5334_;
goto v_resetjp_5284_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5334_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v_G_5287_; lean_object* v_y_5288_; lean_object* v_u_5289_; lean_object* v_Y_5290_; lean_object* v_D_5291_; lean_object* v_M_5292_; lean_object* v_L_5293_; lean_object* v_d_5294_; lean_object* v_Q_5295_; lean_object* v_q_5296_; lean_object* v_w_5297_; lean_object* v_W_5298_; lean_object* v_E_5299_; lean_object* v_e_5300_; lean_object* v_c_5301_; lean_object* v_a_5302_; lean_object* v_b_5303_; lean_object* v_B_5304_; lean_object* v_h_5305_; lean_object* v_K_5306_; lean_object* v_k_5307_; lean_object* v_H_5308_; lean_object* v_m_5309_; lean_object* v_s_5310_; lean_object* v_S_5311_; lean_object* v_A_5312_; lean_object* v_n_5313_; lean_object* v_N_5314_; lean_object* v_V_5315_; lean_object* v_z_5316_; lean_object* v_zabbrev_5317_; lean_object* v_v_5318_; lean_object* v_O_5319_; lean_object* v_X_5320_; lean_object* v_x_5321_; lean_object* v_Z_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5332_; 
v_G_5287_ = lean_ctor_get(v_date_4515_, 0);
v_y_5288_ = lean_ctor_get(v_date_4515_, 1);
v_u_5289_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5290_ = lean_ctor_get(v_date_4515_, 3);
v_D_5291_ = lean_ctor_get(v_date_4515_, 4);
v_M_5292_ = lean_ctor_get(v_date_4515_, 5);
v_L_5293_ = lean_ctor_get(v_date_4515_, 6);
v_d_5294_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5295_ = lean_ctor_get(v_date_4515_, 8);
v_q_5296_ = lean_ctor_get(v_date_4515_, 9);
v_w_5297_ = lean_ctor_get(v_date_4515_, 10);
v_W_5298_ = lean_ctor_get(v_date_4515_, 11);
v_E_5299_ = lean_ctor_get(v_date_4515_, 12);
v_e_5300_ = lean_ctor_get(v_date_4515_, 13);
v_c_5301_ = lean_ctor_get(v_date_4515_, 14);
v_a_5302_ = lean_ctor_get(v_date_4515_, 16);
v_b_5303_ = lean_ctor_get(v_date_4515_, 17);
v_B_5304_ = lean_ctor_get(v_date_4515_, 18);
v_h_5305_ = lean_ctor_get(v_date_4515_, 19);
v_K_5306_ = lean_ctor_get(v_date_4515_, 20);
v_k_5307_ = lean_ctor_get(v_date_4515_, 21);
v_H_5308_ = lean_ctor_get(v_date_4515_, 22);
v_m_5309_ = lean_ctor_get(v_date_4515_, 23);
v_s_5310_ = lean_ctor_get(v_date_4515_, 24);
v_S_5311_ = lean_ctor_get(v_date_4515_, 25);
v_A_5312_ = lean_ctor_get(v_date_4515_, 26);
v_n_5313_ = lean_ctor_get(v_date_4515_, 27);
v_N_5314_ = lean_ctor_get(v_date_4515_, 28);
v_V_5315_ = lean_ctor_get(v_date_4515_, 29);
v_z_5316_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5317_ = lean_ctor_get(v_date_4515_, 31);
v_v_5318_ = lean_ctor_get(v_date_4515_, 32);
v_O_5319_ = lean_ctor_get(v_date_4515_, 33);
v_X_5320_ = lean_ctor_get(v_date_4515_, 34);
v_x_5321_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5322_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5332_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5332_ == 0)
{
lean_object* v_unused_5333_; 
v_unused_5333_ = lean_ctor_get(v_date_4515_, 15);
lean_dec(v_unused_5333_);
v___x_5324_ = v_date_4515_;
v_isShared_5325_ = v_isSharedCheck_5332_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_Z_5322_);
lean_inc(v_x_5321_);
lean_inc(v_X_5320_);
lean_inc(v_O_5319_);
lean_inc(v_v_5318_);
lean_inc(v_zabbrev_5317_);
lean_inc(v_z_5316_);
lean_inc(v_V_5315_);
lean_inc(v_N_5314_);
lean_inc(v_n_5313_);
lean_inc(v_A_5312_);
lean_inc(v_S_5311_);
lean_inc(v_s_5310_);
lean_inc(v_m_5309_);
lean_inc(v_H_5308_);
lean_inc(v_k_5307_);
lean_inc(v_K_5306_);
lean_inc(v_h_5305_);
lean_inc(v_B_5304_);
lean_inc(v_b_5303_);
lean_inc(v_a_5302_);
lean_inc(v_c_5301_);
lean_inc(v_e_5300_);
lean_inc(v_E_5299_);
lean_inc(v_W_5298_);
lean_inc(v_w_5297_);
lean_inc(v_q_5296_);
lean_inc(v_Q_5295_);
lean_inc(v_d_5294_);
lean_inc(v_L_5293_);
lean_inc(v_M_5292_);
lean_inc(v_D_5291_);
lean_inc(v_Y_5290_);
lean_inc(v_u_5289_);
lean_inc(v_y_5288_);
lean_inc(v_G_5287_);
lean_dec(v_date_4515_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5332_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5327_; 
if (v_isShared_5286_ == 0)
{
lean_ctor_set_tag(v___x_5285_, 1);
lean_ctor_set(v___x_5285_, 0, v_data_4517_);
v___x_5327_ = v___x_5285_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_data_4517_);
v___x_5327_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
lean_object* v___x_5329_; 
if (v_isShared_5325_ == 0)
{
lean_ctor_set(v___x_5324_, 15, v___x_5327_);
v___x_5329_ = v___x_5324_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_G_5287_);
lean_ctor_set(v_reuseFailAlloc_5330_, 1, v_y_5288_);
lean_ctor_set(v_reuseFailAlloc_5330_, 2, v_u_5289_);
lean_ctor_set(v_reuseFailAlloc_5330_, 3, v_Y_5290_);
lean_ctor_set(v_reuseFailAlloc_5330_, 4, v_D_5291_);
lean_ctor_set(v_reuseFailAlloc_5330_, 5, v_M_5292_);
lean_ctor_set(v_reuseFailAlloc_5330_, 6, v_L_5293_);
lean_ctor_set(v_reuseFailAlloc_5330_, 7, v_d_5294_);
lean_ctor_set(v_reuseFailAlloc_5330_, 8, v_Q_5295_);
lean_ctor_set(v_reuseFailAlloc_5330_, 9, v_q_5296_);
lean_ctor_set(v_reuseFailAlloc_5330_, 10, v_w_5297_);
lean_ctor_set(v_reuseFailAlloc_5330_, 11, v_W_5298_);
lean_ctor_set(v_reuseFailAlloc_5330_, 12, v_E_5299_);
lean_ctor_set(v_reuseFailAlloc_5330_, 13, v_e_5300_);
lean_ctor_set(v_reuseFailAlloc_5330_, 14, v_c_5301_);
lean_ctor_set(v_reuseFailAlloc_5330_, 15, v___x_5327_);
lean_ctor_set(v_reuseFailAlloc_5330_, 16, v_a_5302_);
lean_ctor_set(v_reuseFailAlloc_5330_, 17, v_b_5303_);
lean_ctor_set(v_reuseFailAlloc_5330_, 18, v_B_5304_);
lean_ctor_set(v_reuseFailAlloc_5330_, 19, v_h_5305_);
lean_ctor_set(v_reuseFailAlloc_5330_, 20, v_K_5306_);
lean_ctor_set(v_reuseFailAlloc_5330_, 21, v_k_5307_);
lean_ctor_set(v_reuseFailAlloc_5330_, 22, v_H_5308_);
lean_ctor_set(v_reuseFailAlloc_5330_, 23, v_m_5309_);
lean_ctor_set(v_reuseFailAlloc_5330_, 24, v_s_5310_);
lean_ctor_set(v_reuseFailAlloc_5330_, 25, v_S_5311_);
lean_ctor_set(v_reuseFailAlloc_5330_, 26, v_A_5312_);
lean_ctor_set(v_reuseFailAlloc_5330_, 27, v_n_5313_);
lean_ctor_set(v_reuseFailAlloc_5330_, 28, v_N_5314_);
lean_ctor_set(v_reuseFailAlloc_5330_, 29, v_V_5315_);
lean_ctor_set(v_reuseFailAlloc_5330_, 30, v_z_5316_);
lean_ctor_set(v_reuseFailAlloc_5330_, 31, v_zabbrev_5317_);
lean_ctor_set(v_reuseFailAlloc_5330_, 32, v_v_5318_);
lean_ctor_set(v_reuseFailAlloc_5330_, 33, v_O_5319_);
lean_ctor_set(v_reuseFailAlloc_5330_, 34, v_X_5320_);
lean_ctor_set(v_reuseFailAlloc_5330_, 35, v_x_5321_);
lean_ctor_set(v_reuseFailAlloc_5330_, 36, v_Z_5322_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
}
case 16:
{
lean_object* v_G_5336_; lean_object* v_y_5337_; lean_object* v_u_5338_; lean_object* v_Y_5339_; lean_object* v_D_5340_; lean_object* v_M_5341_; lean_object* v_L_5342_; lean_object* v_d_5343_; lean_object* v_Q_5344_; lean_object* v_q_5345_; lean_object* v_w_5346_; lean_object* v_W_5347_; lean_object* v_E_5348_; lean_object* v_e_5349_; lean_object* v_c_5350_; lean_object* v_F_5351_; lean_object* v_b_5352_; lean_object* v_B_5353_; lean_object* v_h_5354_; lean_object* v_K_5355_; lean_object* v_k_5356_; lean_object* v_H_5357_; lean_object* v_m_5358_; lean_object* v_s_5359_; lean_object* v_S_5360_; lean_object* v_A_5361_; lean_object* v_n_5362_; lean_object* v_N_5363_; lean_object* v_V_5364_; lean_object* v_z_5365_; lean_object* v_zabbrev_5366_; lean_object* v_v_5367_; lean_object* v_O_5368_; lean_object* v_X_5369_; lean_object* v_x_5370_; lean_object* v_Z_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5379_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_G_5336_ = lean_ctor_get(v_date_4515_, 0);
v_y_5337_ = lean_ctor_get(v_date_4515_, 1);
v_u_5338_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5339_ = lean_ctor_get(v_date_4515_, 3);
v_D_5340_ = lean_ctor_get(v_date_4515_, 4);
v_M_5341_ = lean_ctor_get(v_date_4515_, 5);
v_L_5342_ = lean_ctor_get(v_date_4515_, 6);
v_d_5343_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5344_ = lean_ctor_get(v_date_4515_, 8);
v_q_5345_ = lean_ctor_get(v_date_4515_, 9);
v_w_5346_ = lean_ctor_get(v_date_4515_, 10);
v_W_5347_ = lean_ctor_get(v_date_4515_, 11);
v_E_5348_ = lean_ctor_get(v_date_4515_, 12);
v_e_5349_ = lean_ctor_get(v_date_4515_, 13);
v_c_5350_ = lean_ctor_get(v_date_4515_, 14);
v_F_5351_ = lean_ctor_get(v_date_4515_, 15);
v_b_5352_ = lean_ctor_get(v_date_4515_, 17);
v_B_5353_ = lean_ctor_get(v_date_4515_, 18);
v_h_5354_ = lean_ctor_get(v_date_4515_, 19);
v_K_5355_ = lean_ctor_get(v_date_4515_, 20);
v_k_5356_ = lean_ctor_get(v_date_4515_, 21);
v_H_5357_ = lean_ctor_get(v_date_4515_, 22);
v_m_5358_ = lean_ctor_get(v_date_4515_, 23);
v_s_5359_ = lean_ctor_get(v_date_4515_, 24);
v_S_5360_ = lean_ctor_get(v_date_4515_, 25);
v_A_5361_ = lean_ctor_get(v_date_4515_, 26);
v_n_5362_ = lean_ctor_get(v_date_4515_, 27);
v_N_5363_ = lean_ctor_get(v_date_4515_, 28);
v_V_5364_ = lean_ctor_get(v_date_4515_, 29);
v_z_5365_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5366_ = lean_ctor_get(v_date_4515_, 31);
v_v_5367_ = lean_ctor_get(v_date_4515_, 32);
v_O_5368_ = lean_ctor_get(v_date_4515_, 33);
v_X_5369_ = lean_ctor_get(v_date_4515_, 34);
v_x_5370_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5371_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5379_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5379_ == 0)
{
lean_object* v_unused_5380_; 
v_unused_5380_ = lean_ctor_get(v_date_4515_, 16);
lean_dec(v_unused_5380_);
v___x_5373_ = v_date_4515_;
v_isShared_5374_ = v_isSharedCheck_5379_;
goto v_resetjp_5372_;
}
else
{
lean_inc(v_Z_5371_);
lean_inc(v_x_5370_);
lean_inc(v_X_5369_);
lean_inc(v_O_5368_);
lean_inc(v_v_5367_);
lean_inc(v_zabbrev_5366_);
lean_inc(v_z_5365_);
lean_inc(v_V_5364_);
lean_inc(v_N_5363_);
lean_inc(v_n_5362_);
lean_inc(v_A_5361_);
lean_inc(v_S_5360_);
lean_inc(v_s_5359_);
lean_inc(v_m_5358_);
lean_inc(v_H_5357_);
lean_inc(v_k_5356_);
lean_inc(v_K_5355_);
lean_inc(v_h_5354_);
lean_inc(v_B_5353_);
lean_inc(v_b_5352_);
lean_inc(v_F_5351_);
lean_inc(v_c_5350_);
lean_inc(v_e_5349_);
lean_inc(v_E_5348_);
lean_inc(v_W_5347_);
lean_inc(v_w_5346_);
lean_inc(v_q_5345_);
lean_inc(v_Q_5344_);
lean_inc(v_d_5343_);
lean_inc(v_L_5342_);
lean_inc(v_M_5341_);
lean_inc(v_D_5340_);
lean_inc(v_Y_5339_);
lean_inc(v_u_5338_);
lean_inc(v_y_5337_);
lean_inc(v_G_5336_);
lean_dec(v_date_4515_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5379_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5375_; lean_object* v___x_5377_; 
v___x_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5375_, 0, v_data_4517_);
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 16, v___x_5375_);
v___x_5377_ = v___x_5373_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5378_; 
v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5378_, 0, v_G_5336_);
lean_ctor_set(v_reuseFailAlloc_5378_, 1, v_y_5337_);
lean_ctor_set(v_reuseFailAlloc_5378_, 2, v_u_5338_);
lean_ctor_set(v_reuseFailAlloc_5378_, 3, v_Y_5339_);
lean_ctor_set(v_reuseFailAlloc_5378_, 4, v_D_5340_);
lean_ctor_set(v_reuseFailAlloc_5378_, 5, v_M_5341_);
lean_ctor_set(v_reuseFailAlloc_5378_, 6, v_L_5342_);
lean_ctor_set(v_reuseFailAlloc_5378_, 7, v_d_5343_);
lean_ctor_set(v_reuseFailAlloc_5378_, 8, v_Q_5344_);
lean_ctor_set(v_reuseFailAlloc_5378_, 9, v_q_5345_);
lean_ctor_set(v_reuseFailAlloc_5378_, 10, v_w_5346_);
lean_ctor_set(v_reuseFailAlloc_5378_, 11, v_W_5347_);
lean_ctor_set(v_reuseFailAlloc_5378_, 12, v_E_5348_);
lean_ctor_set(v_reuseFailAlloc_5378_, 13, v_e_5349_);
lean_ctor_set(v_reuseFailAlloc_5378_, 14, v_c_5350_);
lean_ctor_set(v_reuseFailAlloc_5378_, 15, v_F_5351_);
lean_ctor_set(v_reuseFailAlloc_5378_, 16, v___x_5375_);
lean_ctor_set(v_reuseFailAlloc_5378_, 17, v_b_5352_);
lean_ctor_set(v_reuseFailAlloc_5378_, 18, v_B_5353_);
lean_ctor_set(v_reuseFailAlloc_5378_, 19, v_h_5354_);
lean_ctor_set(v_reuseFailAlloc_5378_, 20, v_K_5355_);
lean_ctor_set(v_reuseFailAlloc_5378_, 21, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5378_, 22, v_H_5357_);
lean_ctor_set(v_reuseFailAlloc_5378_, 23, v_m_5358_);
lean_ctor_set(v_reuseFailAlloc_5378_, 24, v_s_5359_);
lean_ctor_set(v_reuseFailAlloc_5378_, 25, v_S_5360_);
lean_ctor_set(v_reuseFailAlloc_5378_, 26, v_A_5361_);
lean_ctor_set(v_reuseFailAlloc_5378_, 27, v_n_5362_);
lean_ctor_set(v_reuseFailAlloc_5378_, 28, v_N_5363_);
lean_ctor_set(v_reuseFailAlloc_5378_, 29, v_V_5364_);
lean_ctor_set(v_reuseFailAlloc_5378_, 30, v_z_5365_);
lean_ctor_set(v_reuseFailAlloc_5378_, 31, v_zabbrev_5366_);
lean_ctor_set(v_reuseFailAlloc_5378_, 32, v_v_5367_);
lean_ctor_set(v_reuseFailAlloc_5378_, 33, v_O_5368_);
lean_ctor_set(v_reuseFailAlloc_5378_, 34, v_X_5369_);
lean_ctor_set(v_reuseFailAlloc_5378_, 35, v_x_5370_);
lean_ctor_set(v_reuseFailAlloc_5378_, 36, v_Z_5371_);
v___x_5377_ = v_reuseFailAlloc_5378_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
return v___x_5377_;
}
}
}
case 17:
{
lean_object* v_G_5381_; lean_object* v_y_5382_; lean_object* v_u_5383_; lean_object* v_Y_5384_; lean_object* v_D_5385_; lean_object* v_M_5386_; lean_object* v_L_5387_; lean_object* v_d_5388_; lean_object* v_Q_5389_; lean_object* v_q_5390_; lean_object* v_w_5391_; lean_object* v_W_5392_; lean_object* v_E_5393_; lean_object* v_e_5394_; lean_object* v_c_5395_; lean_object* v_F_5396_; lean_object* v_a_5397_; lean_object* v_B_5398_; lean_object* v_h_5399_; lean_object* v_K_5400_; lean_object* v_k_5401_; lean_object* v_H_5402_; lean_object* v_m_5403_; lean_object* v_s_5404_; lean_object* v_S_5405_; lean_object* v_A_5406_; lean_object* v_n_5407_; lean_object* v_N_5408_; lean_object* v_V_5409_; lean_object* v_z_5410_; lean_object* v_zabbrev_5411_; lean_object* v_v_5412_; lean_object* v_O_5413_; lean_object* v_X_5414_; lean_object* v_x_5415_; lean_object* v_Z_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5424_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_G_5381_ = lean_ctor_get(v_date_4515_, 0);
v_y_5382_ = lean_ctor_get(v_date_4515_, 1);
v_u_5383_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5384_ = lean_ctor_get(v_date_4515_, 3);
v_D_5385_ = lean_ctor_get(v_date_4515_, 4);
v_M_5386_ = lean_ctor_get(v_date_4515_, 5);
v_L_5387_ = lean_ctor_get(v_date_4515_, 6);
v_d_5388_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5389_ = lean_ctor_get(v_date_4515_, 8);
v_q_5390_ = lean_ctor_get(v_date_4515_, 9);
v_w_5391_ = lean_ctor_get(v_date_4515_, 10);
v_W_5392_ = lean_ctor_get(v_date_4515_, 11);
v_E_5393_ = lean_ctor_get(v_date_4515_, 12);
v_e_5394_ = lean_ctor_get(v_date_4515_, 13);
v_c_5395_ = lean_ctor_get(v_date_4515_, 14);
v_F_5396_ = lean_ctor_get(v_date_4515_, 15);
v_a_5397_ = lean_ctor_get(v_date_4515_, 16);
v_B_5398_ = lean_ctor_get(v_date_4515_, 18);
v_h_5399_ = lean_ctor_get(v_date_4515_, 19);
v_K_5400_ = lean_ctor_get(v_date_4515_, 20);
v_k_5401_ = lean_ctor_get(v_date_4515_, 21);
v_H_5402_ = lean_ctor_get(v_date_4515_, 22);
v_m_5403_ = lean_ctor_get(v_date_4515_, 23);
v_s_5404_ = lean_ctor_get(v_date_4515_, 24);
v_S_5405_ = lean_ctor_get(v_date_4515_, 25);
v_A_5406_ = lean_ctor_get(v_date_4515_, 26);
v_n_5407_ = lean_ctor_get(v_date_4515_, 27);
v_N_5408_ = lean_ctor_get(v_date_4515_, 28);
v_V_5409_ = lean_ctor_get(v_date_4515_, 29);
v_z_5410_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5411_ = lean_ctor_get(v_date_4515_, 31);
v_v_5412_ = lean_ctor_get(v_date_4515_, 32);
v_O_5413_ = lean_ctor_get(v_date_4515_, 33);
v_X_5414_ = lean_ctor_get(v_date_4515_, 34);
v_x_5415_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5416_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5424_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5424_ == 0)
{
lean_object* v_unused_5425_; 
v_unused_5425_ = lean_ctor_get(v_date_4515_, 17);
lean_dec(v_unused_5425_);
v___x_5418_ = v_date_4515_;
v_isShared_5419_ = v_isSharedCheck_5424_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_Z_5416_);
lean_inc(v_x_5415_);
lean_inc(v_X_5414_);
lean_inc(v_O_5413_);
lean_inc(v_v_5412_);
lean_inc(v_zabbrev_5411_);
lean_inc(v_z_5410_);
lean_inc(v_V_5409_);
lean_inc(v_N_5408_);
lean_inc(v_n_5407_);
lean_inc(v_A_5406_);
lean_inc(v_S_5405_);
lean_inc(v_s_5404_);
lean_inc(v_m_5403_);
lean_inc(v_H_5402_);
lean_inc(v_k_5401_);
lean_inc(v_K_5400_);
lean_inc(v_h_5399_);
lean_inc(v_B_5398_);
lean_inc(v_a_5397_);
lean_inc(v_F_5396_);
lean_inc(v_c_5395_);
lean_inc(v_e_5394_);
lean_inc(v_E_5393_);
lean_inc(v_W_5392_);
lean_inc(v_w_5391_);
lean_inc(v_q_5390_);
lean_inc(v_Q_5389_);
lean_inc(v_d_5388_);
lean_inc(v_L_5387_);
lean_inc(v_M_5386_);
lean_inc(v_D_5385_);
lean_inc(v_Y_5384_);
lean_inc(v_u_5383_);
lean_inc(v_y_5382_);
lean_inc(v_G_5381_);
lean_dec(v_date_4515_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5424_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5420_; lean_object* v___x_5422_; 
v___x_5420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5420_, 0, v_data_4517_);
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 17, v___x_5420_);
v___x_5422_ = v___x_5418_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_G_5381_);
lean_ctor_set(v_reuseFailAlloc_5423_, 1, v_y_5382_);
lean_ctor_set(v_reuseFailAlloc_5423_, 2, v_u_5383_);
lean_ctor_set(v_reuseFailAlloc_5423_, 3, v_Y_5384_);
lean_ctor_set(v_reuseFailAlloc_5423_, 4, v_D_5385_);
lean_ctor_set(v_reuseFailAlloc_5423_, 5, v_M_5386_);
lean_ctor_set(v_reuseFailAlloc_5423_, 6, v_L_5387_);
lean_ctor_set(v_reuseFailAlloc_5423_, 7, v_d_5388_);
lean_ctor_set(v_reuseFailAlloc_5423_, 8, v_Q_5389_);
lean_ctor_set(v_reuseFailAlloc_5423_, 9, v_q_5390_);
lean_ctor_set(v_reuseFailAlloc_5423_, 10, v_w_5391_);
lean_ctor_set(v_reuseFailAlloc_5423_, 11, v_W_5392_);
lean_ctor_set(v_reuseFailAlloc_5423_, 12, v_E_5393_);
lean_ctor_set(v_reuseFailAlloc_5423_, 13, v_e_5394_);
lean_ctor_set(v_reuseFailAlloc_5423_, 14, v_c_5395_);
lean_ctor_set(v_reuseFailAlloc_5423_, 15, v_F_5396_);
lean_ctor_set(v_reuseFailAlloc_5423_, 16, v_a_5397_);
lean_ctor_set(v_reuseFailAlloc_5423_, 17, v___x_5420_);
lean_ctor_set(v_reuseFailAlloc_5423_, 18, v_B_5398_);
lean_ctor_set(v_reuseFailAlloc_5423_, 19, v_h_5399_);
lean_ctor_set(v_reuseFailAlloc_5423_, 20, v_K_5400_);
lean_ctor_set(v_reuseFailAlloc_5423_, 21, v_k_5401_);
lean_ctor_set(v_reuseFailAlloc_5423_, 22, v_H_5402_);
lean_ctor_set(v_reuseFailAlloc_5423_, 23, v_m_5403_);
lean_ctor_set(v_reuseFailAlloc_5423_, 24, v_s_5404_);
lean_ctor_set(v_reuseFailAlloc_5423_, 25, v_S_5405_);
lean_ctor_set(v_reuseFailAlloc_5423_, 26, v_A_5406_);
lean_ctor_set(v_reuseFailAlloc_5423_, 27, v_n_5407_);
lean_ctor_set(v_reuseFailAlloc_5423_, 28, v_N_5408_);
lean_ctor_set(v_reuseFailAlloc_5423_, 29, v_V_5409_);
lean_ctor_set(v_reuseFailAlloc_5423_, 30, v_z_5410_);
lean_ctor_set(v_reuseFailAlloc_5423_, 31, v_zabbrev_5411_);
lean_ctor_set(v_reuseFailAlloc_5423_, 32, v_v_5412_);
lean_ctor_set(v_reuseFailAlloc_5423_, 33, v_O_5413_);
lean_ctor_set(v_reuseFailAlloc_5423_, 34, v_X_5414_);
lean_ctor_set(v_reuseFailAlloc_5423_, 35, v_x_5415_);
lean_ctor_set(v_reuseFailAlloc_5423_, 36, v_Z_5416_);
v___x_5422_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
return v___x_5422_;
}
}
}
case 18:
{
lean_object* v_G_5426_; lean_object* v_y_5427_; lean_object* v_u_5428_; lean_object* v_Y_5429_; lean_object* v_D_5430_; lean_object* v_M_5431_; lean_object* v_L_5432_; lean_object* v_d_5433_; lean_object* v_Q_5434_; lean_object* v_q_5435_; lean_object* v_w_5436_; lean_object* v_W_5437_; lean_object* v_E_5438_; lean_object* v_e_5439_; lean_object* v_c_5440_; lean_object* v_F_5441_; lean_object* v_a_5442_; lean_object* v_b_5443_; lean_object* v_h_5444_; lean_object* v_K_5445_; lean_object* v_k_5446_; lean_object* v_H_5447_; lean_object* v_m_5448_; lean_object* v_s_5449_; lean_object* v_S_5450_; lean_object* v_A_5451_; lean_object* v_n_5452_; lean_object* v_N_5453_; lean_object* v_V_5454_; lean_object* v_z_5455_; lean_object* v_zabbrev_5456_; lean_object* v_v_5457_; lean_object* v_O_5458_; lean_object* v_X_5459_; lean_object* v_x_5460_; lean_object* v_Z_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5469_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_G_5426_ = lean_ctor_get(v_date_4515_, 0);
v_y_5427_ = lean_ctor_get(v_date_4515_, 1);
v_u_5428_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5429_ = lean_ctor_get(v_date_4515_, 3);
v_D_5430_ = lean_ctor_get(v_date_4515_, 4);
v_M_5431_ = lean_ctor_get(v_date_4515_, 5);
v_L_5432_ = lean_ctor_get(v_date_4515_, 6);
v_d_5433_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5434_ = lean_ctor_get(v_date_4515_, 8);
v_q_5435_ = lean_ctor_get(v_date_4515_, 9);
v_w_5436_ = lean_ctor_get(v_date_4515_, 10);
v_W_5437_ = lean_ctor_get(v_date_4515_, 11);
v_E_5438_ = lean_ctor_get(v_date_4515_, 12);
v_e_5439_ = lean_ctor_get(v_date_4515_, 13);
v_c_5440_ = lean_ctor_get(v_date_4515_, 14);
v_F_5441_ = lean_ctor_get(v_date_4515_, 15);
v_a_5442_ = lean_ctor_get(v_date_4515_, 16);
v_b_5443_ = lean_ctor_get(v_date_4515_, 17);
v_h_5444_ = lean_ctor_get(v_date_4515_, 19);
v_K_5445_ = lean_ctor_get(v_date_4515_, 20);
v_k_5446_ = lean_ctor_get(v_date_4515_, 21);
v_H_5447_ = lean_ctor_get(v_date_4515_, 22);
v_m_5448_ = lean_ctor_get(v_date_4515_, 23);
v_s_5449_ = lean_ctor_get(v_date_4515_, 24);
v_S_5450_ = lean_ctor_get(v_date_4515_, 25);
v_A_5451_ = lean_ctor_get(v_date_4515_, 26);
v_n_5452_ = lean_ctor_get(v_date_4515_, 27);
v_N_5453_ = lean_ctor_get(v_date_4515_, 28);
v_V_5454_ = lean_ctor_get(v_date_4515_, 29);
v_z_5455_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5456_ = lean_ctor_get(v_date_4515_, 31);
v_v_5457_ = lean_ctor_get(v_date_4515_, 32);
v_O_5458_ = lean_ctor_get(v_date_4515_, 33);
v_X_5459_ = lean_ctor_get(v_date_4515_, 34);
v_x_5460_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5461_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5469_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5469_ == 0)
{
lean_object* v_unused_5470_; 
v_unused_5470_ = lean_ctor_get(v_date_4515_, 18);
lean_dec(v_unused_5470_);
v___x_5463_ = v_date_4515_;
v_isShared_5464_ = v_isSharedCheck_5469_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_Z_5461_);
lean_inc(v_x_5460_);
lean_inc(v_X_5459_);
lean_inc(v_O_5458_);
lean_inc(v_v_5457_);
lean_inc(v_zabbrev_5456_);
lean_inc(v_z_5455_);
lean_inc(v_V_5454_);
lean_inc(v_N_5453_);
lean_inc(v_n_5452_);
lean_inc(v_A_5451_);
lean_inc(v_S_5450_);
lean_inc(v_s_5449_);
lean_inc(v_m_5448_);
lean_inc(v_H_5447_);
lean_inc(v_k_5446_);
lean_inc(v_K_5445_);
lean_inc(v_h_5444_);
lean_inc(v_b_5443_);
lean_inc(v_a_5442_);
lean_inc(v_F_5441_);
lean_inc(v_c_5440_);
lean_inc(v_e_5439_);
lean_inc(v_E_5438_);
lean_inc(v_W_5437_);
lean_inc(v_w_5436_);
lean_inc(v_q_5435_);
lean_inc(v_Q_5434_);
lean_inc(v_d_5433_);
lean_inc(v_L_5432_);
lean_inc(v_M_5431_);
lean_inc(v_D_5430_);
lean_inc(v_Y_5429_);
lean_inc(v_u_5428_);
lean_inc(v_y_5427_);
lean_inc(v_G_5426_);
lean_dec(v_date_4515_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5469_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v___x_5465_; lean_object* v___x_5467_; 
v___x_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5465_, 0, v_data_4517_);
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 18, v___x_5465_);
v___x_5467_ = v___x_5463_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_G_5426_);
lean_ctor_set(v_reuseFailAlloc_5468_, 1, v_y_5427_);
lean_ctor_set(v_reuseFailAlloc_5468_, 2, v_u_5428_);
lean_ctor_set(v_reuseFailAlloc_5468_, 3, v_Y_5429_);
lean_ctor_set(v_reuseFailAlloc_5468_, 4, v_D_5430_);
lean_ctor_set(v_reuseFailAlloc_5468_, 5, v_M_5431_);
lean_ctor_set(v_reuseFailAlloc_5468_, 6, v_L_5432_);
lean_ctor_set(v_reuseFailAlloc_5468_, 7, v_d_5433_);
lean_ctor_set(v_reuseFailAlloc_5468_, 8, v_Q_5434_);
lean_ctor_set(v_reuseFailAlloc_5468_, 9, v_q_5435_);
lean_ctor_set(v_reuseFailAlloc_5468_, 10, v_w_5436_);
lean_ctor_set(v_reuseFailAlloc_5468_, 11, v_W_5437_);
lean_ctor_set(v_reuseFailAlloc_5468_, 12, v_E_5438_);
lean_ctor_set(v_reuseFailAlloc_5468_, 13, v_e_5439_);
lean_ctor_set(v_reuseFailAlloc_5468_, 14, v_c_5440_);
lean_ctor_set(v_reuseFailAlloc_5468_, 15, v_F_5441_);
lean_ctor_set(v_reuseFailAlloc_5468_, 16, v_a_5442_);
lean_ctor_set(v_reuseFailAlloc_5468_, 17, v_b_5443_);
lean_ctor_set(v_reuseFailAlloc_5468_, 18, v___x_5465_);
lean_ctor_set(v_reuseFailAlloc_5468_, 19, v_h_5444_);
lean_ctor_set(v_reuseFailAlloc_5468_, 20, v_K_5445_);
lean_ctor_set(v_reuseFailAlloc_5468_, 21, v_k_5446_);
lean_ctor_set(v_reuseFailAlloc_5468_, 22, v_H_5447_);
lean_ctor_set(v_reuseFailAlloc_5468_, 23, v_m_5448_);
lean_ctor_set(v_reuseFailAlloc_5468_, 24, v_s_5449_);
lean_ctor_set(v_reuseFailAlloc_5468_, 25, v_S_5450_);
lean_ctor_set(v_reuseFailAlloc_5468_, 26, v_A_5451_);
lean_ctor_set(v_reuseFailAlloc_5468_, 27, v_n_5452_);
lean_ctor_set(v_reuseFailAlloc_5468_, 28, v_N_5453_);
lean_ctor_set(v_reuseFailAlloc_5468_, 29, v_V_5454_);
lean_ctor_set(v_reuseFailAlloc_5468_, 30, v_z_5455_);
lean_ctor_set(v_reuseFailAlloc_5468_, 31, v_zabbrev_5456_);
lean_ctor_set(v_reuseFailAlloc_5468_, 32, v_v_5457_);
lean_ctor_set(v_reuseFailAlloc_5468_, 33, v_O_5458_);
lean_ctor_set(v_reuseFailAlloc_5468_, 34, v_X_5459_);
lean_ctor_set(v_reuseFailAlloc_5468_, 35, v_x_5460_);
lean_ctor_set(v_reuseFailAlloc_5468_, 36, v_Z_5461_);
v___x_5467_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
return v___x_5467_;
}
}
}
case 19:
{
lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5521_; 
v_isSharedCheck_5521_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5521_ == 0)
{
lean_object* v_unused_5522_; 
v_unused_5522_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5522_);
v___x_5472_ = v_modifier_4516_;
v_isShared_5473_ = v_isSharedCheck_5521_;
goto v_resetjp_5471_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5521_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
lean_object* v_G_5474_; lean_object* v_y_5475_; lean_object* v_u_5476_; lean_object* v_Y_5477_; lean_object* v_D_5478_; lean_object* v_M_5479_; lean_object* v_L_5480_; lean_object* v_d_5481_; lean_object* v_Q_5482_; lean_object* v_q_5483_; lean_object* v_w_5484_; lean_object* v_W_5485_; lean_object* v_E_5486_; lean_object* v_e_5487_; lean_object* v_c_5488_; lean_object* v_F_5489_; lean_object* v_a_5490_; lean_object* v_b_5491_; lean_object* v_B_5492_; lean_object* v_K_5493_; lean_object* v_k_5494_; lean_object* v_H_5495_; lean_object* v_m_5496_; lean_object* v_s_5497_; lean_object* v_S_5498_; lean_object* v_A_5499_; lean_object* v_n_5500_; lean_object* v_N_5501_; lean_object* v_V_5502_; lean_object* v_z_5503_; lean_object* v_zabbrev_5504_; lean_object* v_v_5505_; lean_object* v_O_5506_; lean_object* v_X_5507_; lean_object* v_x_5508_; lean_object* v_Z_5509_; lean_object* v___x_5511_; uint8_t v_isShared_5512_; uint8_t v_isSharedCheck_5519_; 
v_G_5474_ = lean_ctor_get(v_date_4515_, 0);
v_y_5475_ = lean_ctor_get(v_date_4515_, 1);
v_u_5476_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5477_ = lean_ctor_get(v_date_4515_, 3);
v_D_5478_ = lean_ctor_get(v_date_4515_, 4);
v_M_5479_ = lean_ctor_get(v_date_4515_, 5);
v_L_5480_ = lean_ctor_get(v_date_4515_, 6);
v_d_5481_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5482_ = lean_ctor_get(v_date_4515_, 8);
v_q_5483_ = lean_ctor_get(v_date_4515_, 9);
v_w_5484_ = lean_ctor_get(v_date_4515_, 10);
v_W_5485_ = lean_ctor_get(v_date_4515_, 11);
v_E_5486_ = lean_ctor_get(v_date_4515_, 12);
v_e_5487_ = lean_ctor_get(v_date_4515_, 13);
v_c_5488_ = lean_ctor_get(v_date_4515_, 14);
v_F_5489_ = lean_ctor_get(v_date_4515_, 15);
v_a_5490_ = lean_ctor_get(v_date_4515_, 16);
v_b_5491_ = lean_ctor_get(v_date_4515_, 17);
v_B_5492_ = lean_ctor_get(v_date_4515_, 18);
v_K_5493_ = lean_ctor_get(v_date_4515_, 20);
v_k_5494_ = lean_ctor_get(v_date_4515_, 21);
v_H_5495_ = lean_ctor_get(v_date_4515_, 22);
v_m_5496_ = lean_ctor_get(v_date_4515_, 23);
v_s_5497_ = lean_ctor_get(v_date_4515_, 24);
v_S_5498_ = lean_ctor_get(v_date_4515_, 25);
v_A_5499_ = lean_ctor_get(v_date_4515_, 26);
v_n_5500_ = lean_ctor_get(v_date_4515_, 27);
v_N_5501_ = lean_ctor_get(v_date_4515_, 28);
v_V_5502_ = lean_ctor_get(v_date_4515_, 29);
v_z_5503_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5504_ = lean_ctor_get(v_date_4515_, 31);
v_v_5505_ = lean_ctor_get(v_date_4515_, 32);
v_O_5506_ = lean_ctor_get(v_date_4515_, 33);
v_X_5507_ = lean_ctor_get(v_date_4515_, 34);
v_x_5508_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5509_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5519_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5519_ == 0)
{
lean_object* v_unused_5520_; 
v_unused_5520_ = lean_ctor_get(v_date_4515_, 19);
lean_dec(v_unused_5520_);
v___x_5511_ = v_date_4515_;
v_isShared_5512_ = v_isSharedCheck_5519_;
goto v_resetjp_5510_;
}
else
{
lean_inc(v_Z_5509_);
lean_inc(v_x_5508_);
lean_inc(v_X_5507_);
lean_inc(v_O_5506_);
lean_inc(v_v_5505_);
lean_inc(v_zabbrev_5504_);
lean_inc(v_z_5503_);
lean_inc(v_V_5502_);
lean_inc(v_N_5501_);
lean_inc(v_n_5500_);
lean_inc(v_A_5499_);
lean_inc(v_S_5498_);
lean_inc(v_s_5497_);
lean_inc(v_m_5496_);
lean_inc(v_H_5495_);
lean_inc(v_k_5494_);
lean_inc(v_K_5493_);
lean_inc(v_B_5492_);
lean_inc(v_b_5491_);
lean_inc(v_a_5490_);
lean_inc(v_F_5489_);
lean_inc(v_c_5488_);
lean_inc(v_e_5487_);
lean_inc(v_E_5486_);
lean_inc(v_W_5485_);
lean_inc(v_w_5484_);
lean_inc(v_q_5483_);
lean_inc(v_Q_5482_);
lean_inc(v_d_5481_);
lean_inc(v_L_5480_);
lean_inc(v_M_5479_);
lean_inc(v_D_5478_);
lean_inc(v_Y_5477_);
lean_inc(v_u_5476_);
lean_inc(v_y_5475_);
lean_inc(v_G_5474_);
lean_dec(v_date_4515_);
v___x_5511_ = lean_box(0);
v_isShared_5512_ = v_isSharedCheck_5519_;
goto v_resetjp_5510_;
}
v_resetjp_5510_:
{
lean_object* v___x_5514_; 
if (v_isShared_5473_ == 0)
{
lean_ctor_set_tag(v___x_5472_, 1);
lean_ctor_set(v___x_5472_, 0, v_data_4517_);
v___x_5514_ = v___x_5472_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_data_4517_);
v___x_5514_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
lean_object* v___x_5516_; 
if (v_isShared_5512_ == 0)
{
lean_ctor_set(v___x_5511_, 19, v___x_5514_);
v___x_5516_ = v___x_5511_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_G_5474_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v_y_5475_);
lean_ctor_set(v_reuseFailAlloc_5517_, 2, v_u_5476_);
lean_ctor_set(v_reuseFailAlloc_5517_, 3, v_Y_5477_);
lean_ctor_set(v_reuseFailAlloc_5517_, 4, v_D_5478_);
lean_ctor_set(v_reuseFailAlloc_5517_, 5, v_M_5479_);
lean_ctor_set(v_reuseFailAlloc_5517_, 6, v_L_5480_);
lean_ctor_set(v_reuseFailAlloc_5517_, 7, v_d_5481_);
lean_ctor_set(v_reuseFailAlloc_5517_, 8, v_Q_5482_);
lean_ctor_set(v_reuseFailAlloc_5517_, 9, v_q_5483_);
lean_ctor_set(v_reuseFailAlloc_5517_, 10, v_w_5484_);
lean_ctor_set(v_reuseFailAlloc_5517_, 11, v_W_5485_);
lean_ctor_set(v_reuseFailAlloc_5517_, 12, v_E_5486_);
lean_ctor_set(v_reuseFailAlloc_5517_, 13, v_e_5487_);
lean_ctor_set(v_reuseFailAlloc_5517_, 14, v_c_5488_);
lean_ctor_set(v_reuseFailAlloc_5517_, 15, v_F_5489_);
lean_ctor_set(v_reuseFailAlloc_5517_, 16, v_a_5490_);
lean_ctor_set(v_reuseFailAlloc_5517_, 17, v_b_5491_);
lean_ctor_set(v_reuseFailAlloc_5517_, 18, v_B_5492_);
lean_ctor_set(v_reuseFailAlloc_5517_, 19, v___x_5514_);
lean_ctor_set(v_reuseFailAlloc_5517_, 20, v_K_5493_);
lean_ctor_set(v_reuseFailAlloc_5517_, 21, v_k_5494_);
lean_ctor_set(v_reuseFailAlloc_5517_, 22, v_H_5495_);
lean_ctor_set(v_reuseFailAlloc_5517_, 23, v_m_5496_);
lean_ctor_set(v_reuseFailAlloc_5517_, 24, v_s_5497_);
lean_ctor_set(v_reuseFailAlloc_5517_, 25, v_S_5498_);
lean_ctor_set(v_reuseFailAlloc_5517_, 26, v_A_5499_);
lean_ctor_set(v_reuseFailAlloc_5517_, 27, v_n_5500_);
lean_ctor_set(v_reuseFailAlloc_5517_, 28, v_N_5501_);
lean_ctor_set(v_reuseFailAlloc_5517_, 29, v_V_5502_);
lean_ctor_set(v_reuseFailAlloc_5517_, 30, v_z_5503_);
lean_ctor_set(v_reuseFailAlloc_5517_, 31, v_zabbrev_5504_);
lean_ctor_set(v_reuseFailAlloc_5517_, 32, v_v_5505_);
lean_ctor_set(v_reuseFailAlloc_5517_, 33, v_O_5506_);
lean_ctor_set(v_reuseFailAlloc_5517_, 34, v_X_5507_);
lean_ctor_set(v_reuseFailAlloc_5517_, 35, v_x_5508_);
lean_ctor_set(v_reuseFailAlloc_5517_, 36, v_Z_5509_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
}
}
}
case 20:
{
lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5573_; 
v_isSharedCheck_5573_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5573_ == 0)
{
lean_object* v_unused_5574_; 
v_unused_5574_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5574_);
v___x_5524_ = v_modifier_4516_;
v_isShared_5525_ = v_isSharedCheck_5573_;
goto v_resetjp_5523_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5573_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v_G_5526_; lean_object* v_y_5527_; lean_object* v_u_5528_; lean_object* v_Y_5529_; lean_object* v_D_5530_; lean_object* v_M_5531_; lean_object* v_L_5532_; lean_object* v_d_5533_; lean_object* v_Q_5534_; lean_object* v_q_5535_; lean_object* v_w_5536_; lean_object* v_W_5537_; lean_object* v_E_5538_; lean_object* v_e_5539_; lean_object* v_c_5540_; lean_object* v_F_5541_; lean_object* v_a_5542_; lean_object* v_b_5543_; lean_object* v_B_5544_; lean_object* v_h_5545_; lean_object* v_k_5546_; lean_object* v_H_5547_; lean_object* v_m_5548_; lean_object* v_s_5549_; lean_object* v_S_5550_; lean_object* v_A_5551_; lean_object* v_n_5552_; lean_object* v_N_5553_; lean_object* v_V_5554_; lean_object* v_z_5555_; lean_object* v_zabbrev_5556_; lean_object* v_v_5557_; lean_object* v_O_5558_; lean_object* v_X_5559_; lean_object* v_x_5560_; lean_object* v_Z_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5571_; 
v_G_5526_ = lean_ctor_get(v_date_4515_, 0);
v_y_5527_ = lean_ctor_get(v_date_4515_, 1);
v_u_5528_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5529_ = lean_ctor_get(v_date_4515_, 3);
v_D_5530_ = lean_ctor_get(v_date_4515_, 4);
v_M_5531_ = lean_ctor_get(v_date_4515_, 5);
v_L_5532_ = lean_ctor_get(v_date_4515_, 6);
v_d_5533_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5534_ = lean_ctor_get(v_date_4515_, 8);
v_q_5535_ = lean_ctor_get(v_date_4515_, 9);
v_w_5536_ = lean_ctor_get(v_date_4515_, 10);
v_W_5537_ = lean_ctor_get(v_date_4515_, 11);
v_E_5538_ = lean_ctor_get(v_date_4515_, 12);
v_e_5539_ = lean_ctor_get(v_date_4515_, 13);
v_c_5540_ = lean_ctor_get(v_date_4515_, 14);
v_F_5541_ = lean_ctor_get(v_date_4515_, 15);
v_a_5542_ = lean_ctor_get(v_date_4515_, 16);
v_b_5543_ = lean_ctor_get(v_date_4515_, 17);
v_B_5544_ = lean_ctor_get(v_date_4515_, 18);
v_h_5545_ = lean_ctor_get(v_date_4515_, 19);
v_k_5546_ = lean_ctor_get(v_date_4515_, 21);
v_H_5547_ = lean_ctor_get(v_date_4515_, 22);
v_m_5548_ = lean_ctor_get(v_date_4515_, 23);
v_s_5549_ = lean_ctor_get(v_date_4515_, 24);
v_S_5550_ = lean_ctor_get(v_date_4515_, 25);
v_A_5551_ = lean_ctor_get(v_date_4515_, 26);
v_n_5552_ = lean_ctor_get(v_date_4515_, 27);
v_N_5553_ = lean_ctor_get(v_date_4515_, 28);
v_V_5554_ = lean_ctor_get(v_date_4515_, 29);
v_z_5555_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5556_ = lean_ctor_get(v_date_4515_, 31);
v_v_5557_ = lean_ctor_get(v_date_4515_, 32);
v_O_5558_ = lean_ctor_get(v_date_4515_, 33);
v_X_5559_ = lean_ctor_get(v_date_4515_, 34);
v_x_5560_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5561_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5571_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5571_ == 0)
{
lean_object* v_unused_5572_; 
v_unused_5572_ = lean_ctor_get(v_date_4515_, 20);
lean_dec(v_unused_5572_);
v___x_5563_ = v_date_4515_;
v_isShared_5564_ = v_isSharedCheck_5571_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_Z_5561_);
lean_inc(v_x_5560_);
lean_inc(v_X_5559_);
lean_inc(v_O_5558_);
lean_inc(v_v_5557_);
lean_inc(v_zabbrev_5556_);
lean_inc(v_z_5555_);
lean_inc(v_V_5554_);
lean_inc(v_N_5553_);
lean_inc(v_n_5552_);
lean_inc(v_A_5551_);
lean_inc(v_S_5550_);
lean_inc(v_s_5549_);
lean_inc(v_m_5548_);
lean_inc(v_H_5547_);
lean_inc(v_k_5546_);
lean_inc(v_h_5545_);
lean_inc(v_B_5544_);
lean_inc(v_b_5543_);
lean_inc(v_a_5542_);
lean_inc(v_F_5541_);
lean_inc(v_c_5540_);
lean_inc(v_e_5539_);
lean_inc(v_E_5538_);
lean_inc(v_W_5537_);
lean_inc(v_w_5536_);
lean_inc(v_q_5535_);
lean_inc(v_Q_5534_);
lean_inc(v_d_5533_);
lean_inc(v_L_5532_);
lean_inc(v_M_5531_);
lean_inc(v_D_5530_);
lean_inc(v_Y_5529_);
lean_inc(v_u_5528_);
lean_inc(v_y_5527_);
lean_inc(v_G_5526_);
lean_dec(v_date_4515_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5571_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5566_; 
if (v_isShared_5525_ == 0)
{
lean_ctor_set_tag(v___x_5524_, 1);
lean_ctor_set(v___x_5524_, 0, v_data_4517_);
v___x_5566_ = v___x_5524_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_data_4517_);
v___x_5566_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___x_5568_; 
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 20, v___x_5566_);
v___x_5568_ = v___x_5563_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_G_5526_);
lean_ctor_set(v_reuseFailAlloc_5569_, 1, v_y_5527_);
lean_ctor_set(v_reuseFailAlloc_5569_, 2, v_u_5528_);
lean_ctor_set(v_reuseFailAlloc_5569_, 3, v_Y_5529_);
lean_ctor_set(v_reuseFailAlloc_5569_, 4, v_D_5530_);
lean_ctor_set(v_reuseFailAlloc_5569_, 5, v_M_5531_);
lean_ctor_set(v_reuseFailAlloc_5569_, 6, v_L_5532_);
lean_ctor_set(v_reuseFailAlloc_5569_, 7, v_d_5533_);
lean_ctor_set(v_reuseFailAlloc_5569_, 8, v_Q_5534_);
lean_ctor_set(v_reuseFailAlloc_5569_, 9, v_q_5535_);
lean_ctor_set(v_reuseFailAlloc_5569_, 10, v_w_5536_);
lean_ctor_set(v_reuseFailAlloc_5569_, 11, v_W_5537_);
lean_ctor_set(v_reuseFailAlloc_5569_, 12, v_E_5538_);
lean_ctor_set(v_reuseFailAlloc_5569_, 13, v_e_5539_);
lean_ctor_set(v_reuseFailAlloc_5569_, 14, v_c_5540_);
lean_ctor_set(v_reuseFailAlloc_5569_, 15, v_F_5541_);
lean_ctor_set(v_reuseFailAlloc_5569_, 16, v_a_5542_);
lean_ctor_set(v_reuseFailAlloc_5569_, 17, v_b_5543_);
lean_ctor_set(v_reuseFailAlloc_5569_, 18, v_B_5544_);
lean_ctor_set(v_reuseFailAlloc_5569_, 19, v_h_5545_);
lean_ctor_set(v_reuseFailAlloc_5569_, 20, v___x_5566_);
lean_ctor_set(v_reuseFailAlloc_5569_, 21, v_k_5546_);
lean_ctor_set(v_reuseFailAlloc_5569_, 22, v_H_5547_);
lean_ctor_set(v_reuseFailAlloc_5569_, 23, v_m_5548_);
lean_ctor_set(v_reuseFailAlloc_5569_, 24, v_s_5549_);
lean_ctor_set(v_reuseFailAlloc_5569_, 25, v_S_5550_);
lean_ctor_set(v_reuseFailAlloc_5569_, 26, v_A_5551_);
lean_ctor_set(v_reuseFailAlloc_5569_, 27, v_n_5552_);
lean_ctor_set(v_reuseFailAlloc_5569_, 28, v_N_5553_);
lean_ctor_set(v_reuseFailAlloc_5569_, 29, v_V_5554_);
lean_ctor_set(v_reuseFailAlloc_5569_, 30, v_z_5555_);
lean_ctor_set(v_reuseFailAlloc_5569_, 31, v_zabbrev_5556_);
lean_ctor_set(v_reuseFailAlloc_5569_, 32, v_v_5557_);
lean_ctor_set(v_reuseFailAlloc_5569_, 33, v_O_5558_);
lean_ctor_set(v_reuseFailAlloc_5569_, 34, v_X_5559_);
lean_ctor_set(v_reuseFailAlloc_5569_, 35, v_x_5560_);
lean_ctor_set(v_reuseFailAlloc_5569_, 36, v_Z_5561_);
v___x_5568_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
return v___x_5568_;
}
}
}
}
}
case 21:
{
lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5625_; 
v_isSharedCheck_5625_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5625_ == 0)
{
lean_object* v_unused_5626_; 
v_unused_5626_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5626_);
v___x_5576_ = v_modifier_4516_;
v_isShared_5577_ = v_isSharedCheck_5625_;
goto v_resetjp_5575_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5625_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v_G_5578_; lean_object* v_y_5579_; lean_object* v_u_5580_; lean_object* v_Y_5581_; lean_object* v_D_5582_; lean_object* v_M_5583_; lean_object* v_L_5584_; lean_object* v_d_5585_; lean_object* v_Q_5586_; lean_object* v_q_5587_; lean_object* v_w_5588_; lean_object* v_W_5589_; lean_object* v_E_5590_; lean_object* v_e_5591_; lean_object* v_c_5592_; lean_object* v_F_5593_; lean_object* v_a_5594_; lean_object* v_b_5595_; lean_object* v_B_5596_; lean_object* v_h_5597_; lean_object* v_K_5598_; lean_object* v_H_5599_; lean_object* v_m_5600_; lean_object* v_s_5601_; lean_object* v_S_5602_; lean_object* v_A_5603_; lean_object* v_n_5604_; lean_object* v_N_5605_; lean_object* v_V_5606_; lean_object* v_z_5607_; lean_object* v_zabbrev_5608_; lean_object* v_v_5609_; lean_object* v_O_5610_; lean_object* v_X_5611_; lean_object* v_x_5612_; lean_object* v_Z_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5623_; 
v_G_5578_ = lean_ctor_get(v_date_4515_, 0);
v_y_5579_ = lean_ctor_get(v_date_4515_, 1);
v_u_5580_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5581_ = lean_ctor_get(v_date_4515_, 3);
v_D_5582_ = lean_ctor_get(v_date_4515_, 4);
v_M_5583_ = lean_ctor_get(v_date_4515_, 5);
v_L_5584_ = lean_ctor_get(v_date_4515_, 6);
v_d_5585_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5586_ = lean_ctor_get(v_date_4515_, 8);
v_q_5587_ = lean_ctor_get(v_date_4515_, 9);
v_w_5588_ = lean_ctor_get(v_date_4515_, 10);
v_W_5589_ = lean_ctor_get(v_date_4515_, 11);
v_E_5590_ = lean_ctor_get(v_date_4515_, 12);
v_e_5591_ = lean_ctor_get(v_date_4515_, 13);
v_c_5592_ = lean_ctor_get(v_date_4515_, 14);
v_F_5593_ = lean_ctor_get(v_date_4515_, 15);
v_a_5594_ = lean_ctor_get(v_date_4515_, 16);
v_b_5595_ = lean_ctor_get(v_date_4515_, 17);
v_B_5596_ = lean_ctor_get(v_date_4515_, 18);
v_h_5597_ = lean_ctor_get(v_date_4515_, 19);
v_K_5598_ = lean_ctor_get(v_date_4515_, 20);
v_H_5599_ = lean_ctor_get(v_date_4515_, 22);
v_m_5600_ = lean_ctor_get(v_date_4515_, 23);
v_s_5601_ = lean_ctor_get(v_date_4515_, 24);
v_S_5602_ = lean_ctor_get(v_date_4515_, 25);
v_A_5603_ = lean_ctor_get(v_date_4515_, 26);
v_n_5604_ = lean_ctor_get(v_date_4515_, 27);
v_N_5605_ = lean_ctor_get(v_date_4515_, 28);
v_V_5606_ = lean_ctor_get(v_date_4515_, 29);
v_z_5607_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5608_ = lean_ctor_get(v_date_4515_, 31);
v_v_5609_ = lean_ctor_get(v_date_4515_, 32);
v_O_5610_ = lean_ctor_get(v_date_4515_, 33);
v_X_5611_ = lean_ctor_get(v_date_4515_, 34);
v_x_5612_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5613_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5623_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5623_ == 0)
{
lean_object* v_unused_5624_; 
v_unused_5624_ = lean_ctor_get(v_date_4515_, 21);
lean_dec(v_unused_5624_);
v___x_5615_ = v_date_4515_;
v_isShared_5616_ = v_isSharedCheck_5623_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_Z_5613_);
lean_inc(v_x_5612_);
lean_inc(v_X_5611_);
lean_inc(v_O_5610_);
lean_inc(v_v_5609_);
lean_inc(v_zabbrev_5608_);
lean_inc(v_z_5607_);
lean_inc(v_V_5606_);
lean_inc(v_N_5605_);
lean_inc(v_n_5604_);
lean_inc(v_A_5603_);
lean_inc(v_S_5602_);
lean_inc(v_s_5601_);
lean_inc(v_m_5600_);
lean_inc(v_H_5599_);
lean_inc(v_K_5598_);
lean_inc(v_h_5597_);
lean_inc(v_B_5596_);
lean_inc(v_b_5595_);
lean_inc(v_a_5594_);
lean_inc(v_F_5593_);
lean_inc(v_c_5592_);
lean_inc(v_e_5591_);
lean_inc(v_E_5590_);
lean_inc(v_W_5589_);
lean_inc(v_w_5588_);
lean_inc(v_q_5587_);
lean_inc(v_Q_5586_);
lean_inc(v_d_5585_);
lean_inc(v_L_5584_);
lean_inc(v_M_5583_);
lean_inc(v_D_5582_);
lean_inc(v_Y_5581_);
lean_inc(v_u_5580_);
lean_inc(v_y_5579_);
lean_inc(v_G_5578_);
lean_dec(v_date_4515_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5623_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5618_; 
if (v_isShared_5577_ == 0)
{
lean_ctor_set_tag(v___x_5576_, 1);
lean_ctor_set(v___x_5576_, 0, v_data_4517_);
v___x_5618_ = v___x_5576_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_data_4517_);
v___x_5618_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
lean_object* v___x_5620_; 
if (v_isShared_5616_ == 0)
{
lean_ctor_set(v___x_5615_, 21, v___x_5618_);
v___x_5620_ = v___x_5615_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_G_5578_);
lean_ctor_set(v_reuseFailAlloc_5621_, 1, v_y_5579_);
lean_ctor_set(v_reuseFailAlloc_5621_, 2, v_u_5580_);
lean_ctor_set(v_reuseFailAlloc_5621_, 3, v_Y_5581_);
lean_ctor_set(v_reuseFailAlloc_5621_, 4, v_D_5582_);
lean_ctor_set(v_reuseFailAlloc_5621_, 5, v_M_5583_);
lean_ctor_set(v_reuseFailAlloc_5621_, 6, v_L_5584_);
lean_ctor_set(v_reuseFailAlloc_5621_, 7, v_d_5585_);
lean_ctor_set(v_reuseFailAlloc_5621_, 8, v_Q_5586_);
lean_ctor_set(v_reuseFailAlloc_5621_, 9, v_q_5587_);
lean_ctor_set(v_reuseFailAlloc_5621_, 10, v_w_5588_);
lean_ctor_set(v_reuseFailAlloc_5621_, 11, v_W_5589_);
lean_ctor_set(v_reuseFailAlloc_5621_, 12, v_E_5590_);
lean_ctor_set(v_reuseFailAlloc_5621_, 13, v_e_5591_);
lean_ctor_set(v_reuseFailAlloc_5621_, 14, v_c_5592_);
lean_ctor_set(v_reuseFailAlloc_5621_, 15, v_F_5593_);
lean_ctor_set(v_reuseFailAlloc_5621_, 16, v_a_5594_);
lean_ctor_set(v_reuseFailAlloc_5621_, 17, v_b_5595_);
lean_ctor_set(v_reuseFailAlloc_5621_, 18, v_B_5596_);
lean_ctor_set(v_reuseFailAlloc_5621_, 19, v_h_5597_);
lean_ctor_set(v_reuseFailAlloc_5621_, 20, v_K_5598_);
lean_ctor_set(v_reuseFailAlloc_5621_, 21, v___x_5618_);
lean_ctor_set(v_reuseFailAlloc_5621_, 22, v_H_5599_);
lean_ctor_set(v_reuseFailAlloc_5621_, 23, v_m_5600_);
lean_ctor_set(v_reuseFailAlloc_5621_, 24, v_s_5601_);
lean_ctor_set(v_reuseFailAlloc_5621_, 25, v_S_5602_);
lean_ctor_set(v_reuseFailAlloc_5621_, 26, v_A_5603_);
lean_ctor_set(v_reuseFailAlloc_5621_, 27, v_n_5604_);
lean_ctor_set(v_reuseFailAlloc_5621_, 28, v_N_5605_);
lean_ctor_set(v_reuseFailAlloc_5621_, 29, v_V_5606_);
lean_ctor_set(v_reuseFailAlloc_5621_, 30, v_z_5607_);
lean_ctor_set(v_reuseFailAlloc_5621_, 31, v_zabbrev_5608_);
lean_ctor_set(v_reuseFailAlloc_5621_, 32, v_v_5609_);
lean_ctor_set(v_reuseFailAlloc_5621_, 33, v_O_5610_);
lean_ctor_set(v_reuseFailAlloc_5621_, 34, v_X_5611_);
lean_ctor_set(v_reuseFailAlloc_5621_, 35, v_x_5612_);
lean_ctor_set(v_reuseFailAlloc_5621_, 36, v_Z_5613_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
}
}
}
case 22:
{
lean_object* v___x_5628_; uint8_t v_isShared_5629_; uint8_t v_isSharedCheck_5677_; 
v_isSharedCheck_5677_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5677_ == 0)
{
lean_object* v_unused_5678_; 
v_unused_5678_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5678_);
v___x_5628_ = v_modifier_4516_;
v_isShared_5629_ = v_isSharedCheck_5677_;
goto v_resetjp_5627_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5628_ = lean_box(0);
v_isShared_5629_ = v_isSharedCheck_5677_;
goto v_resetjp_5627_;
}
v_resetjp_5627_:
{
lean_object* v_G_5630_; lean_object* v_y_5631_; lean_object* v_u_5632_; lean_object* v_Y_5633_; lean_object* v_D_5634_; lean_object* v_M_5635_; lean_object* v_L_5636_; lean_object* v_d_5637_; lean_object* v_Q_5638_; lean_object* v_q_5639_; lean_object* v_w_5640_; lean_object* v_W_5641_; lean_object* v_E_5642_; lean_object* v_e_5643_; lean_object* v_c_5644_; lean_object* v_F_5645_; lean_object* v_a_5646_; lean_object* v_b_5647_; lean_object* v_B_5648_; lean_object* v_h_5649_; lean_object* v_K_5650_; lean_object* v_k_5651_; lean_object* v_m_5652_; lean_object* v_s_5653_; lean_object* v_S_5654_; lean_object* v_A_5655_; lean_object* v_n_5656_; lean_object* v_N_5657_; lean_object* v_V_5658_; lean_object* v_z_5659_; lean_object* v_zabbrev_5660_; lean_object* v_v_5661_; lean_object* v_O_5662_; lean_object* v_X_5663_; lean_object* v_x_5664_; lean_object* v_Z_5665_; lean_object* v___x_5667_; uint8_t v_isShared_5668_; uint8_t v_isSharedCheck_5675_; 
v_G_5630_ = lean_ctor_get(v_date_4515_, 0);
v_y_5631_ = lean_ctor_get(v_date_4515_, 1);
v_u_5632_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5633_ = lean_ctor_get(v_date_4515_, 3);
v_D_5634_ = lean_ctor_get(v_date_4515_, 4);
v_M_5635_ = lean_ctor_get(v_date_4515_, 5);
v_L_5636_ = lean_ctor_get(v_date_4515_, 6);
v_d_5637_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5638_ = lean_ctor_get(v_date_4515_, 8);
v_q_5639_ = lean_ctor_get(v_date_4515_, 9);
v_w_5640_ = lean_ctor_get(v_date_4515_, 10);
v_W_5641_ = lean_ctor_get(v_date_4515_, 11);
v_E_5642_ = lean_ctor_get(v_date_4515_, 12);
v_e_5643_ = lean_ctor_get(v_date_4515_, 13);
v_c_5644_ = lean_ctor_get(v_date_4515_, 14);
v_F_5645_ = lean_ctor_get(v_date_4515_, 15);
v_a_5646_ = lean_ctor_get(v_date_4515_, 16);
v_b_5647_ = lean_ctor_get(v_date_4515_, 17);
v_B_5648_ = lean_ctor_get(v_date_4515_, 18);
v_h_5649_ = lean_ctor_get(v_date_4515_, 19);
v_K_5650_ = lean_ctor_get(v_date_4515_, 20);
v_k_5651_ = lean_ctor_get(v_date_4515_, 21);
v_m_5652_ = lean_ctor_get(v_date_4515_, 23);
v_s_5653_ = lean_ctor_get(v_date_4515_, 24);
v_S_5654_ = lean_ctor_get(v_date_4515_, 25);
v_A_5655_ = lean_ctor_get(v_date_4515_, 26);
v_n_5656_ = lean_ctor_get(v_date_4515_, 27);
v_N_5657_ = lean_ctor_get(v_date_4515_, 28);
v_V_5658_ = lean_ctor_get(v_date_4515_, 29);
v_z_5659_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5660_ = lean_ctor_get(v_date_4515_, 31);
v_v_5661_ = lean_ctor_get(v_date_4515_, 32);
v_O_5662_ = lean_ctor_get(v_date_4515_, 33);
v_X_5663_ = lean_ctor_get(v_date_4515_, 34);
v_x_5664_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5665_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5675_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5675_ == 0)
{
lean_object* v_unused_5676_; 
v_unused_5676_ = lean_ctor_get(v_date_4515_, 22);
lean_dec(v_unused_5676_);
v___x_5667_ = v_date_4515_;
v_isShared_5668_ = v_isSharedCheck_5675_;
goto v_resetjp_5666_;
}
else
{
lean_inc(v_Z_5665_);
lean_inc(v_x_5664_);
lean_inc(v_X_5663_);
lean_inc(v_O_5662_);
lean_inc(v_v_5661_);
lean_inc(v_zabbrev_5660_);
lean_inc(v_z_5659_);
lean_inc(v_V_5658_);
lean_inc(v_N_5657_);
lean_inc(v_n_5656_);
lean_inc(v_A_5655_);
lean_inc(v_S_5654_);
lean_inc(v_s_5653_);
lean_inc(v_m_5652_);
lean_inc(v_k_5651_);
lean_inc(v_K_5650_);
lean_inc(v_h_5649_);
lean_inc(v_B_5648_);
lean_inc(v_b_5647_);
lean_inc(v_a_5646_);
lean_inc(v_F_5645_);
lean_inc(v_c_5644_);
lean_inc(v_e_5643_);
lean_inc(v_E_5642_);
lean_inc(v_W_5641_);
lean_inc(v_w_5640_);
lean_inc(v_q_5639_);
lean_inc(v_Q_5638_);
lean_inc(v_d_5637_);
lean_inc(v_L_5636_);
lean_inc(v_M_5635_);
lean_inc(v_D_5634_);
lean_inc(v_Y_5633_);
lean_inc(v_u_5632_);
lean_inc(v_y_5631_);
lean_inc(v_G_5630_);
lean_dec(v_date_4515_);
v___x_5667_ = lean_box(0);
v_isShared_5668_ = v_isSharedCheck_5675_;
goto v_resetjp_5666_;
}
v_resetjp_5666_:
{
lean_object* v___x_5670_; 
if (v_isShared_5629_ == 0)
{
lean_ctor_set_tag(v___x_5628_, 1);
lean_ctor_set(v___x_5628_, 0, v_data_4517_);
v___x_5670_ = v___x_5628_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5674_; 
v_reuseFailAlloc_5674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_data_4517_);
v___x_5670_ = v_reuseFailAlloc_5674_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
lean_object* v___x_5672_; 
if (v_isShared_5668_ == 0)
{
lean_ctor_set(v___x_5667_, 22, v___x_5670_);
v___x_5672_ = v___x_5667_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5673_; 
v_reuseFailAlloc_5673_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5673_, 0, v_G_5630_);
lean_ctor_set(v_reuseFailAlloc_5673_, 1, v_y_5631_);
lean_ctor_set(v_reuseFailAlloc_5673_, 2, v_u_5632_);
lean_ctor_set(v_reuseFailAlloc_5673_, 3, v_Y_5633_);
lean_ctor_set(v_reuseFailAlloc_5673_, 4, v_D_5634_);
lean_ctor_set(v_reuseFailAlloc_5673_, 5, v_M_5635_);
lean_ctor_set(v_reuseFailAlloc_5673_, 6, v_L_5636_);
lean_ctor_set(v_reuseFailAlloc_5673_, 7, v_d_5637_);
lean_ctor_set(v_reuseFailAlloc_5673_, 8, v_Q_5638_);
lean_ctor_set(v_reuseFailAlloc_5673_, 9, v_q_5639_);
lean_ctor_set(v_reuseFailAlloc_5673_, 10, v_w_5640_);
lean_ctor_set(v_reuseFailAlloc_5673_, 11, v_W_5641_);
lean_ctor_set(v_reuseFailAlloc_5673_, 12, v_E_5642_);
lean_ctor_set(v_reuseFailAlloc_5673_, 13, v_e_5643_);
lean_ctor_set(v_reuseFailAlloc_5673_, 14, v_c_5644_);
lean_ctor_set(v_reuseFailAlloc_5673_, 15, v_F_5645_);
lean_ctor_set(v_reuseFailAlloc_5673_, 16, v_a_5646_);
lean_ctor_set(v_reuseFailAlloc_5673_, 17, v_b_5647_);
lean_ctor_set(v_reuseFailAlloc_5673_, 18, v_B_5648_);
lean_ctor_set(v_reuseFailAlloc_5673_, 19, v_h_5649_);
lean_ctor_set(v_reuseFailAlloc_5673_, 20, v_K_5650_);
lean_ctor_set(v_reuseFailAlloc_5673_, 21, v_k_5651_);
lean_ctor_set(v_reuseFailAlloc_5673_, 22, v___x_5670_);
lean_ctor_set(v_reuseFailAlloc_5673_, 23, v_m_5652_);
lean_ctor_set(v_reuseFailAlloc_5673_, 24, v_s_5653_);
lean_ctor_set(v_reuseFailAlloc_5673_, 25, v_S_5654_);
lean_ctor_set(v_reuseFailAlloc_5673_, 26, v_A_5655_);
lean_ctor_set(v_reuseFailAlloc_5673_, 27, v_n_5656_);
lean_ctor_set(v_reuseFailAlloc_5673_, 28, v_N_5657_);
lean_ctor_set(v_reuseFailAlloc_5673_, 29, v_V_5658_);
lean_ctor_set(v_reuseFailAlloc_5673_, 30, v_z_5659_);
lean_ctor_set(v_reuseFailAlloc_5673_, 31, v_zabbrev_5660_);
lean_ctor_set(v_reuseFailAlloc_5673_, 32, v_v_5661_);
lean_ctor_set(v_reuseFailAlloc_5673_, 33, v_O_5662_);
lean_ctor_set(v_reuseFailAlloc_5673_, 34, v_X_5663_);
lean_ctor_set(v_reuseFailAlloc_5673_, 35, v_x_5664_);
lean_ctor_set(v_reuseFailAlloc_5673_, 36, v_Z_5665_);
v___x_5672_ = v_reuseFailAlloc_5673_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
return v___x_5672_;
}
}
}
}
}
case 23:
{
lean_object* v___x_5680_; uint8_t v_isShared_5681_; uint8_t v_isSharedCheck_5729_; 
v_isSharedCheck_5729_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5729_ == 0)
{
lean_object* v_unused_5730_; 
v_unused_5730_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5730_);
v___x_5680_ = v_modifier_4516_;
v_isShared_5681_ = v_isSharedCheck_5729_;
goto v_resetjp_5679_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5680_ = lean_box(0);
v_isShared_5681_ = v_isSharedCheck_5729_;
goto v_resetjp_5679_;
}
v_resetjp_5679_:
{
lean_object* v_G_5682_; lean_object* v_y_5683_; lean_object* v_u_5684_; lean_object* v_Y_5685_; lean_object* v_D_5686_; lean_object* v_M_5687_; lean_object* v_L_5688_; lean_object* v_d_5689_; lean_object* v_Q_5690_; lean_object* v_q_5691_; lean_object* v_w_5692_; lean_object* v_W_5693_; lean_object* v_E_5694_; lean_object* v_e_5695_; lean_object* v_c_5696_; lean_object* v_F_5697_; lean_object* v_a_5698_; lean_object* v_b_5699_; lean_object* v_B_5700_; lean_object* v_h_5701_; lean_object* v_K_5702_; lean_object* v_k_5703_; lean_object* v_H_5704_; lean_object* v_s_5705_; lean_object* v_S_5706_; lean_object* v_A_5707_; lean_object* v_n_5708_; lean_object* v_N_5709_; lean_object* v_V_5710_; lean_object* v_z_5711_; lean_object* v_zabbrev_5712_; lean_object* v_v_5713_; lean_object* v_O_5714_; lean_object* v_X_5715_; lean_object* v_x_5716_; lean_object* v_Z_5717_; lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5727_; 
v_G_5682_ = lean_ctor_get(v_date_4515_, 0);
v_y_5683_ = lean_ctor_get(v_date_4515_, 1);
v_u_5684_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5685_ = lean_ctor_get(v_date_4515_, 3);
v_D_5686_ = lean_ctor_get(v_date_4515_, 4);
v_M_5687_ = lean_ctor_get(v_date_4515_, 5);
v_L_5688_ = lean_ctor_get(v_date_4515_, 6);
v_d_5689_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5690_ = lean_ctor_get(v_date_4515_, 8);
v_q_5691_ = lean_ctor_get(v_date_4515_, 9);
v_w_5692_ = lean_ctor_get(v_date_4515_, 10);
v_W_5693_ = lean_ctor_get(v_date_4515_, 11);
v_E_5694_ = lean_ctor_get(v_date_4515_, 12);
v_e_5695_ = lean_ctor_get(v_date_4515_, 13);
v_c_5696_ = lean_ctor_get(v_date_4515_, 14);
v_F_5697_ = lean_ctor_get(v_date_4515_, 15);
v_a_5698_ = lean_ctor_get(v_date_4515_, 16);
v_b_5699_ = lean_ctor_get(v_date_4515_, 17);
v_B_5700_ = lean_ctor_get(v_date_4515_, 18);
v_h_5701_ = lean_ctor_get(v_date_4515_, 19);
v_K_5702_ = lean_ctor_get(v_date_4515_, 20);
v_k_5703_ = lean_ctor_get(v_date_4515_, 21);
v_H_5704_ = lean_ctor_get(v_date_4515_, 22);
v_s_5705_ = lean_ctor_get(v_date_4515_, 24);
v_S_5706_ = lean_ctor_get(v_date_4515_, 25);
v_A_5707_ = lean_ctor_get(v_date_4515_, 26);
v_n_5708_ = lean_ctor_get(v_date_4515_, 27);
v_N_5709_ = lean_ctor_get(v_date_4515_, 28);
v_V_5710_ = lean_ctor_get(v_date_4515_, 29);
v_z_5711_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5712_ = lean_ctor_get(v_date_4515_, 31);
v_v_5713_ = lean_ctor_get(v_date_4515_, 32);
v_O_5714_ = lean_ctor_get(v_date_4515_, 33);
v_X_5715_ = lean_ctor_get(v_date_4515_, 34);
v_x_5716_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5717_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5727_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5727_ == 0)
{
lean_object* v_unused_5728_; 
v_unused_5728_ = lean_ctor_get(v_date_4515_, 23);
lean_dec(v_unused_5728_);
v___x_5719_ = v_date_4515_;
v_isShared_5720_ = v_isSharedCheck_5727_;
goto v_resetjp_5718_;
}
else
{
lean_inc(v_Z_5717_);
lean_inc(v_x_5716_);
lean_inc(v_X_5715_);
lean_inc(v_O_5714_);
lean_inc(v_v_5713_);
lean_inc(v_zabbrev_5712_);
lean_inc(v_z_5711_);
lean_inc(v_V_5710_);
lean_inc(v_N_5709_);
lean_inc(v_n_5708_);
lean_inc(v_A_5707_);
lean_inc(v_S_5706_);
lean_inc(v_s_5705_);
lean_inc(v_H_5704_);
lean_inc(v_k_5703_);
lean_inc(v_K_5702_);
lean_inc(v_h_5701_);
lean_inc(v_B_5700_);
lean_inc(v_b_5699_);
lean_inc(v_a_5698_);
lean_inc(v_F_5697_);
lean_inc(v_c_5696_);
lean_inc(v_e_5695_);
lean_inc(v_E_5694_);
lean_inc(v_W_5693_);
lean_inc(v_w_5692_);
lean_inc(v_q_5691_);
lean_inc(v_Q_5690_);
lean_inc(v_d_5689_);
lean_inc(v_L_5688_);
lean_inc(v_M_5687_);
lean_inc(v_D_5686_);
lean_inc(v_Y_5685_);
lean_inc(v_u_5684_);
lean_inc(v_y_5683_);
lean_inc(v_G_5682_);
lean_dec(v_date_4515_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5727_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v___x_5722_; 
if (v_isShared_5681_ == 0)
{
lean_ctor_set_tag(v___x_5680_, 1);
lean_ctor_set(v___x_5680_, 0, v_data_4517_);
v___x_5722_ = v___x_5680_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_data_4517_);
v___x_5722_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
lean_object* v___x_5724_; 
if (v_isShared_5720_ == 0)
{
lean_ctor_set(v___x_5719_, 23, v___x_5722_);
v___x_5724_ = v___x_5719_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v_G_5682_);
lean_ctor_set(v_reuseFailAlloc_5725_, 1, v_y_5683_);
lean_ctor_set(v_reuseFailAlloc_5725_, 2, v_u_5684_);
lean_ctor_set(v_reuseFailAlloc_5725_, 3, v_Y_5685_);
lean_ctor_set(v_reuseFailAlloc_5725_, 4, v_D_5686_);
lean_ctor_set(v_reuseFailAlloc_5725_, 5, v_M_5687_);
lean_ctor_set(v_reuseFailAlloc_5725_, 6, v_L_5688_);
lean_ctor_set(v_reuseFailAlloc_5725_, 7, v_d_5689_);
lean_ctor_set(v_reuseFailAlloc_5725_, 8, v_Q_5690_);
lean_ctor_set(v_reuseFailAlloc_5725_, 9, v_q_5691_);
lean_ctor_set(v_reuseFailAlloc_5725_, 10, v_w_5692_);
lean_ctor_set(v_reuseFailAlloc_5725_, 11, v_W_5693_);
lean_ctor_set(v_reuseFailAlloc_5725_, 12, v_E_5694_);
lean_ctor_set(v_reuseFailAlloc_5725_, 13, v_e_5695_);
lean_ctor_set(v_reuseFailAlloc_5725_, 14, v_c_5696_);
lean_ctor_set(v_reuseFailAlloc_5725_, 15, v_F_5697_);
lean_ctor_set(v_reuseFailAlloc_5725_, 16, v_a_5698_);
lean_ctor_set(v_reuseFailAlloc_5725_, 17, v_b_5699_);
lean_ctor_set(v_reuseFailAlloc_5725_, 18, v_B_5700_);
lean_ctor_set(v_reuseFailAlloc_5725_, 19, v_h_5701_);
lean_ctor_set(v_reuseFailAlloc_5725_, 20, v_K_5702_);
lean_ctor_set(v_reuseFailAlloc_5725_, 21, v_k_5703_);
lean_ctor_set(v_reuseFailAlloc_5725_, 22, v_H_5704_);
lean_ctor_set(v_reuseFailAlloc_5725_, 23, v___x_5722_);
lean_ctor_set(v_reuseFailAlloc_5725_, 24, v_s_5705_);
lean_ctor_set(v_reuseFailAlloc_5725_, 25, v_S_5706_);
lean_ctor_set(v_reuseFailAlloc_5725_, 26, v_A_5707_);
lean_ctor_set(v_reuseFailAlloc_5725_, 27, v_n_5708_);
lean_ctor_set(v_reuseFailAlloc_5725_, 28, v_N_5709_);
lean_ctor_set(v_reuseFailAlloc_5725_, 29, v_V_5710_);
lean_ctor_set(v_reuseFailAlloc_5725_, 30, v_z_5711_);
lean_ctor_set(v_reuseFailAlloc_5725_, 31, v_zabbrev_5712_);
lean_ctor_set(v_reuseFailAlloc_5725_, 32, v_v_5713_);
lean_ctor_set(v_reuseFailAlloc_5725_, 33, v_O_5714_);
lean_ctor_set(v_reuseFailAlloc_5725_, 34, v_X_5715_);
lean_ctor_set(v_reuseFailAlloc_5725_, 35, v_x_5716_);
lean_ctor_set(v_reuseFailAlloc_5725_, 36, v_Z_5717_);
v___x_5724_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
return v___x_5724_;
}
}
}
}
}
case 24:
{
lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5781_; 
v_isSharedCheck_5781_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5781_ == 0)
{
lean_object* v_unused_5782_; 
v_unused_5782_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5782_);
v___x_5732_ = v_modifier_4516_;
v_isShared_5733_ = v_isSharedCheck_5781_;
goto v_resetjp_5731_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5781_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v_G_5734_; lean_object* v_y_5735_; lean_object* v_u_5736_; lean_object* v_Y_5737_; lean_object* v_D_5738_; lean_object* v_M_5739_; lean_object* v_L_5740_; lean_object* v_d_5741_; lean_object* v_Q_5742_; lean_object* v_q_5743_; lean_object* v_w_5744_; lean_object* v_W_5745_; lean_object* v_E_5746_; lean_object* v_e_5747_; lean_object* v_c_5748_; lean_object* v_F_5749_; lean_object* v_a_5750_; lean_object* v_b_5751_; lean_object* v_B_5752_; lean_object* v_h_5753_; lean_object* v_K_5754_; lean_object* v_k_5755_; lean_object* v_H_5756_; lean_object* v_m_5757_; lean_object* v_S_5758_; lean_object* v_A_5759_; lean_object* v_n_5760_; lean_object* v_N_5761_; lean_object* v_V_5762_; lean_object* v_z_5763_; lean_object* v_zabbrev_5764_; lean_object* v_v_5765_; lean_object* v_O_5766_; lean_object* v_X_5767_; lean_object* v_x_5768_; lean_object* v_Z_5769_; lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5779_; 
v_G_5734_ = lean_ctor_get(v_date_4515_, 0);
v_y_5735_ = lean_ctor_get(v_date_4515_, 1);
v_u_5736_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5737_ = lean_ctor_get(v_date_4515_, 3);
v_D_5738_ = lean_ctor_get(v_date_4515_, 4);
v_M_5739_ = lean_ctor_get(v_date_4515_, 5);
v_L_5740_ = lean_ctor_get(v_date_4515_, 6);
v_d_5741_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5742_ = lean_ctor_get(v_date_4515_, 8);
v_q_5743_ = lean_ctor_get(v_date_4515_, 9);
v_w_5744_ = lean_ctor_get(v_date_4515_, 10);
v_W_5745_ = lean_ctor_get(v_date_4515_, 11);
v_E_5746_ = lean_ctor_get(v_date_4515_, 12);
v_e_5747_ = lean_ctor_get(v_date_4515_, 13);
v_c_5748_ = lean_ctor_get(v_date_4515_, 14);
v_F_5749_ = lean_ctor_get(v_date_4515_, 15);
v_a_5750_ = lean_ctor_get(v_date_4515_, 16);
v_b_5751_ = lean_ctor_get(v_date_4515_, 17);
v_B_5752_ = lean_ctor_get(v_date_4515_, 18);
v_h_5753_ = lean_ctor_get(v_date_4515_, 19);
v_K_5754_ = lean_ctor_get(v_date_4515_, 20);
v_k_5755_ = lean_ctor_get(v_date_4515_, 21);
v_H_5756_ = lean_ctor_get(v_date_4515_, 22);
v_m_5757_ = lean_ctor_get(v_date_4515_, 23);
v_S_5758_ = lean_ctor_get(v_date_4515_, 25);
v_A_5759_ = lean_ctor_get(v_date_4515_, 26);
v_n_5760_ = lean_ctor_get(v_date_4515_, 27);
v_N_5761_ = lean_ctor_get(v_date_4515_, 28);
v_V_5762_ = lean_ctor_get(v_date_4515_, 29);
v_z_5763_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5764_ = lean_ctor_get(v_date_4515_, 31);
v_v_5765_ = lean_ctor_get(v_date_4515_, 32);
v_O_5766_ = lean_ctor_get(v_date_4515_, 33);
v_X_5767_ = lean_ctor_get(v_date_4515_, 34);
v_x_5768_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5769_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5779_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5779_ == 0)
{
lean_object* v_unused_5780_; 
v_unused_5780_ = lean_ctor_get(v_date_4515_, 24);
lean_dec(v_unused_5780_);
v___x_5771_ = v_date_4515_;
v_isShared_5772_ = v_isSharedCheck_5779_;
goto v_resetjp_5770_;
}
else
{
lean_inc(v_Z_5769_);
lean_inc(v_x_5768_);
lean_inc(v_X_5767_);
lean_inc(v_O_5766_);
lean_inc(v_v_5765_);
lean_inc(v_zabbrev_5764_);
lean_inc(v_z_5763_);
lean_inc(v_V_5762_);
lean_inc(v_N_5761_);
lean_inc(v_n_5760_);
lean_inc(v_A_5759_);
lean_inc(v_S_5758_);
lean_inc(v_m_5757_);
lean_inc(v_H_5756_);
lean_inc(v_k_5755_);
lean_inc(v_K_5754_);
lean_inc(v_h_5753_);
lean_inc(v_B_5752_);
lean_inc(v_b_5751_);
lean_inc(v_a_5750_);
lean_inc(v_F_5749_);
lean_inc(v_c_5748_);
lean_inc(v_e_5747_);
lean_inc(v_E_5746_);
lean_inc(v_W_5745_);
lean_inc(v_w_5744_);
lean_inc(v_q_5743_);
lean_inc(v_Q_5742_);
lean_inc(v_d_5741_);
lean_inc(v_L_5740_);
lean_inc(v_M_5739_);
lean_inc(v_D_5738_);
lean_inc(v_Y_5737_);
lean_inc(v_u_5736_);
lean_inc(v_y_5735_);
lean_inc(v_G_5734_);
lean_dec(v_date_4515_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5779_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
lean_object* v___x_5774_; 
if (v_isShared_5733_ == 0)
{
lean_ctor_set_tag(v___x_5732_, 1);
lean_ctor_set(v___x_5732_, 0, v_data_4517_);
v___x_5774_ = v___x_5732_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_data_4517_);
v___x_5774_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
lean_object* v___x_5776_; 
if (v_isShared_5772_ == 0)
{
lean_ctor_set(v___x_5771_, 24, v___x_5774_);
v___x_5776_ = v___x_5771_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_G_5734_);
lean_ctor_set(v_reuseFailAlloc_5777_, 1, v_y_5735_);
lean_ctor_set(v_reuseFailAlloc_5777_, 2, v_u_5736_);
lean_ctor_set(v_reuseFailAlloc_5777_, 3, v_Y_5737_);
lean_ctor_set(v_reuseFailAlloc_5777_, 4, v_D_5738_);
lean_ctor_set(v_reuseFailAlloc_5777_, 5, v_M_5739_);
lean_ctor_set(v_reuseFailAlloc_5777_, 6, v_L_5740_);
lean_ctor_set(v_reuseFailAlloc_5777_, 7, v_d_5741_);
lean_ctor_set(v_reuseFailAlloc_5777_, 8, v_Q_5742_);
lean_ctor_set(v_reuseFailAlloc_5777_, 9, v_q_5743_);
lean_ctor_set(v_reuseFailAlloc_5777_, 10, v_w_5744_);
lean_ctor_set(v_reuseFailAlloc_5777_, 11, v_W_5745_);
lean_ctor_set(v_reuseFailAlloc_5777_, 12, v_E_5746_);
lean_ctor_set(v_reuseFailAlloc_5777_, 13, v_e_5747_);
lean_ctor_set(v_reuseFailAlloc_5777_, 14, v_c_5748_);
lean_ctor_set(v_reuseFailAlloc_5777_, 15, v_F_5749_);
lean_ctor_set(v_reuseFailAlloc_5777_, 16, v_a_5750_);
lean_ctor_set(v_reuseFailAlloc_5777_, 17, v_b_5751_);
lean_ctor_set(v_reuseFailAlloc_5777_, 18, v_B_5752_);
lean_ctor_set(v_reuseFailAlloc_5777_, 19, v_h_5753_);
lean_ctor_set(v_reuseFailAlloc_5777_, 20, v_K_5754_);
lean_ctor_set(v_reuseFailAlloc_5777_, 21, v_k_5755_);
lean_ctor_set(v_reuseFailAlloc_5777_, 22, v_H_5756_);
lean_ctor_set(v_reuseFailAlloc_5777_, 23, v_m_5757_);
lean_ctor_set(v_reuseFailAlloc_5777_, 24, v___x_5774_);
lean_ctor_set(v_reuseFailAlloc_5777_, 25, v_S_5758_);
lean_ctor_set(v_reuseFailAlloc_5777_, 26, v_A_5759_);
lean_ctor_set(v_reuseFailAlloc_5777_, 27, v_n_5760_);
lean_ctor_set(v_reuseFailAlloc_5777_, 28, v_N_5761_);
lean_ctor_set(v_reuseFailAlloc_5777_, 29, v_V_5762_);
lean_ctor_set(v_reuseFailAlloc_5777_, 30, v_z_5763_);
lean_ctor_set(v_reuseFailAlloc_5777_, 31, v_zabbrev_5764_);
lean_ctor_set(v_reuseFailAlloc_5777_, 32, v_v_5765_);
lean_ctor_set(v_reuseFailAlloc_5777_, 33, v_O_5766_);
lean_ctor_set(v_reuseFailAlloc_5777_, 34, v_X_5767_);
lean_ctor_set(v_reuseFailAlloc_5777_, 35, v_x_5768_);
lean_ctor_set(v_reuseFailAlloc_5777_, 36, v_Z_5769_);
v___x_5776_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
return v___x_5776_;
}
}
}
}
}
case 25:
{
lean_object* v___x_5784_; uint8_t v_isShared_5785_; uint8_t v_isSharedCheck_5833_; 
v_isSharedCheck_5833_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5833_ == 0)
{
lean_object* v_unused_5834_; 
v_unused_5834_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5834_);
v___x_5784_ = v_modifier_4516_;
v_isShared_5785_ = v_isSharedCheck_5833_;
goto v_resetjp_5783_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5784_ = lean_box(0);
v_isShared_5785_ = v_isSharedCheck_5833_;
goto v_resetjp_5783_;
}
v_resetjp_5783_:
{
lean_object* v_G_5786_; lean_object* v_y_5787_; lean_object* v_u_5788_; lean_object* v_Y_5789_; lean_object* v_D_5790_; lean_object* v_M_5791_; lean_object* v_L_5792_; lean_object* v_d_5793_; lean_object* v_Q_5794_; lean_object* v_q_5795_; lean_object* v_w_5796_; lean_object* v_W_5797_; lean_object* v_E_5798_; lean_object* v_e_5799_; lean_object* v_c_5800_; lean_object* v_F_5801_; lean_object* v_a_5802_; lean_object* v_b_5803_; lean_object* v_B_5804_; lean_object* v_h_5805_; lean_object* v_K_5806_; lean_object* v_k_5807_; lean_object* v_H_5808_; lean_object* v_m_5809_; lean_object* v_s_5810_; lean_object* v_A_5811_; lean_object* v_n_5812_; lean_object* v_N_5813_; lean_object* v_V_5814_; lean_object* v_z_5815_; lean_object* v_zabbrev_5816_; lean_object* v_v_5817_; lean_object* v_O_5818_; lean_object* v_X_5819_; lean_object* v_x_5820_; lean_object* v_Z_5821_; lean_object* v___x_5823_; uint8_t v_isShared_5824_; uint8_t v_isSharedCheck_5831_; 
v_G_5786_ = lean_ctor_get(v_date_4515_, 0);
v_y_5787_ = lean_ctor_get(v_date_4515_, 1);
v_u_5788_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5789_ = lean_ctor_get(v_date_4515_, 3);
v_D_5790_ = lean_ctor_get(v_date_4515_, 4);
v_M_5791_ = lean_ctor_get(v_date_4515_, 5);
v_L_5792_ = lean_ctor_get(v_date_4515_, 6);
v_d_5793_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5794_ = lean_ctor_get(v_date_4515_, 8);
v_q_5795_ = lean_ctor_get(v_date_4515_, 9);
v_w_5796_ = lean_ctor_get(v_date_4515_, 10);
v_W_5797_ = lean_ctor_get(v_date_4515_, 11);
v_E_5798_ = lean_ctor_get(v_date_4515_, 12);
v_e_5799_ = lean_ctor_get(v_date_4515_, 13);
v_c_5800_ = lean_ctor_get(v_date_4515_, 14);
v_F_5801_ = lean_ctor_get(v_date_4515_, 15);
v_a_5802_ = lean_ctor_get(v_date_4515_, 16);
v_b_5803_ = lean_ctor_get(v_date_4515_, 17);
v_B_5804_ = lean_ctor_get(v_date_4515_, 18);
v_h_5805_ = lean_ctor_get(v_date_4515_, 19);
v_K_5806_ = lean_ctor_get(v_date_4515_, 20);
v_k_5807_ = lean_ctor_get(v_date_4515_, 21);
v_H_5808_ = lean_ctor_get(v_date_4515_, 22);
v_m_5809_ = lean_ctor_get(v_date_4515_, 23);
v_s_5810_ = lean_ctor_get(v_date_4515_, 24);
v_A_5811_ = lean_ctor_get(v_date_4515_, 26);
v_n_5812_ = lean_ctor_get(v_date_4515_, 27);
v_N_5813_ = lean_ctor_get(v_date_4515_, 28);
v_V_5814_ = lean_ctor_get(v_date_4515_, 29);
v_z_5815_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5816_ = lean_ctor_get(v_date_4515_, 31);
v_v_5817_ = lean_ctor_get(v_date_4515_, 32);
v_O_5818_ = lean_ctor_get(v_date_4515_, 33);
v_X_5819_ = lean_ctor_get(v_date_4515_, 34);
v_x_5820_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5821_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5831_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5831_ == 0)
{
lean_object* v_unused_5832_; 
v_unused_5832_ = lean_ctor_get(v_date_4515_, 25);
lean_dec(v_unused_5832_);
v___x_5823_ = v_date_4515_;
v_isShared_5824_ = v_isSharedCheck_5831_;
goto v_resetjp_5822_;
}
else
{
lean_inc(v_Z_5821_);
lean_inc(v_x_5820_);
lean_inc(v_X_5819_);
lean_inc(v_O_5818_);
lean_inc(v_v_5817_);
lean_inc(v_zabbrev_5816_);
lean_inc(v_z_5815_);
lean_inc(v_V_5814_);
lean_inc(v_N_5813_);
lean_inc(v_n_5812_);
lean_inc(v_A_5811_);
lean_inc(v_s_5810_);
lean_inc(v_m_5809_);
lean_inc(v_H_5808_);
lean_inc(v_k_5807_);
lean_inc(v_K_5806_);
lean_inc(v_h_5805_);
lean_inc(v_B_5804_);
lean_inc(v_b_5803_);
lean_inc(v_a_5802_);
lean_inc(v_F_5801_);
lean_inc(v_c_5800_);
lean_inc(v_e_5799_);
lean_inc(v_E_5798_);
lean_inc(v_W_5797_);
lean_inc(v_w_5796_);
lean_inc(v_q_5795_);
lean_inc(v_Q_5794_);
lean_inc(v_d_5793_);
lean_inc(v_L_5792_);
lean_inc(v_M_5791_);
lean_inc(v_D_5790_);
lean_inc(v_Y_5789_);
lean_inc(v_u_5788_);
lean_inc(v_y_5787_);
lean_inc(v_G_5786_);
lean_dec(v_date_4515_);
v___x_5823_ = lean_box(0);
v_isShared_5824_ = v_isSharedCheck_5831_;
goto v_resetjp_5822_;
}
v_resetjp_5822_:
{
lean_object* v___x_5826_; 
if (v_isShared_5785_ == 0)
{
lean_ctor_set_tag(v___x_5784_, 1);
lean_ctor_set(v___x_5784_, 0, v_data_4517_);
v___x_5826_ = v___x_5784_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v_data_4517_);
v___x_5826_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
lean_object* v___x_5828_; 
if (v_isShared_5824_ == 0)
{
lean_ctor_set(v___x_5823_, 25, v___x_5826_);
v___x_5828_ = v___x_5823_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v_G_5786_);
lean_ctor_set(v_reuseFailAlloc_5829_, 1, v_y_5787_);
lean_ctor_set(v_reuseFailAlloc_5829_, 2, v_u_5788_);
lean_ctor_set(v_reuseFailAlloc_5829_, 3, v_Y_5789_);
lean_ctor_set(v_reuseFailAlloc_5829_, 4, v_D_5790_);
lean_ctor_set(v_reuseFailAlloc_5829_, 5, v_M_5791_);
lean_ctor_set(v_reuseFailAlloc_5829_, 6, v_L_5792_);
lean_ctor_set(v_reuseFailAlloc_5829_, 7, v_d_5793_);
lean_ctor_set(v_reuseFailAlloc_5829_, 8, v_Q_5794_);
lean_ctor_set(v_reuseFailAlloc_5829_, 9, v_q_5795_);
lean_ctor_set(v_reuseFailAlloc_5829_, 10, v_w_5796_);
lean_ctor_set(v_reuseFailAlloc_5829_, 11, v_W_5797_);
lean_ctor_set(v_reuseFailAlloc_5829_, 12, v_E_5798_);
lean_ctor_set(v_reuseFailAlloc_5829_, 13, v_e_5799_);
lean_ctor_set(v_reuseFailAlloc_5829_, 14, v_c_5800_);
lean_ctor_set(v_reuseFailAlloc_5829_, 15, v_F_5801_);
lean_ctor_set(v_reuseFailAlloc_5829_, 16, v_a_5802_);
lean_ctor_set(v_reuseFailAlloc_5829_, 17, v_b_5803_);
lean_ctor_set(v_reuseFailAlloc_5829_, 18, v_B_5804_);
lean_ctor_set(v_reuseFailAlloc_5829_, 19, v_h_5805_);
lean_ctor_set(v_reuseFailAlloc_5829_, 20, v_K_5806_);
lean_ctor_set(v_reuseFailAlloc_5829_, 21, v_k_5807_);
lean_ctor_set(v_reuseFailAlloc_5829_, 22, v_H_5808_);
lean_ctor_set(v_reuseFailAlloc_5829_, 23, v_m_5809_);
lean_ctor_set(v_reuseFailAlloc_5829_, 24, v_s_5810_);
lean_ctor_set(v_reuseFailAlloc_5829_, 25, v___x_5826_);
lean_ctor_set(v_reuseFailAlloc_5829_, 26, v_A_5811_);
lean_ctor_set(v_reuseFailAlloc_5829_, 27, v_n_5812_);
lean_ctor_set(v_reuseFailAlloc_5829_, 28, v_N_5813_);
lean_ctor_set(v_reuseFailAlloc_5829_, 29, v_V_5814_);
lean_ctor_set(v_reuseFailAlloc_5829_, 30, v_z_5815_);
lean_ctor_set(v_reuseFailAlloc_5829_, 31, v_zabbrev_5816_);
lean_ctor_set(v_reuseFailAlloc_5829_, 32, v_v_5817_);
lean_ctor_set(v_reuseFailAlloc_5829_, 33, v_O_5818_);
lean_ctor_set(v_reuseFailAlloc_5829_, 34, v_X_5819_);
lean_ctor_set(v_reuseFailAlloc_5829_, 35, v_x_5820_);
lean_ctor_set(v_reuseFailAlloc_5829_, 36, v_Z_5821_);
v___x_5828_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
return v___x_5828_;
}
}
}
}
}
case 26:
{
lean_object* v___x_5836_; uint8_t v_isShared_5837_; uint8_t v_isSharedCheck_5885_; 
v_isSharedCheck_5885_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5885_ == 0)
{
lean_object* v_unused_5886_; 
v_unused_5886_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5886_);
v___x_5836_ = v_modifier_4516_;
v_isShared_5837_ = v_isSharedCheck_5885_;
goto v_resetjp_5835_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5836_ = lean_box(0);
v_isShared_5837_ = v_isSharedCheck_5885_;
goto v_resetjp_5835_;
}
v_resetjp_5835_:
{
lean_object* v_G_5838_; lean_object* v_y_5839_; lean_object* v_u_5840_; lean_object* v_Y_5841_; lean_object* v_D_5842_; lean_object* v_M_5843_; lean_object* v_L_5844_; lean_object* v_d_5845_; lean_object* v_Q_5846_; lean_object* v_q_5847_; lean_object* v_w_5848_; lean_object* v_W_5849_; lean_object* v_E_5850_; lean_object* v_e_5851_; lean_object* v_c_5852_; lean_object* v_F_5853_; lean_object* v_a_5854_; lean_object* v_b_5855_; lean_object* v_B_5856_; lean_object* v_h_5857_; lean_object* v_K_5858_; lean_object* v_k_5859_; lean_object* v_H_5860_; lean_object* v_m_5861_; lean_object* v_s_5862_; lean_object* v_S_5863_; lean_object* v_n_5864_; lean_object* v_N_5865_; lean_object* v_V_5866_; lean_object* v_z_5867_; lean_object* v_zabbrev_5868_; lean_object* v_v_5869_; lean_object* v_O_5870_; lean_object* v_X_5871_; lean_object* v_x_5872_; lean_object* v_Z_5873_; lean_object* v___x_5875_; uint8_t v_isShared_5876_; uint8_t v_isSharedCheck_5883_; 
v_G_5838_ = lean_ctor_get(v_date_4515_, 0);
v_y_5839_ = lean_ctor_get(v_date_4515_, 1);
v_u_5840_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5841_ = lean_ctor_get(v_date_4515_, 3);
v_D_5842_ = lean_ctor_get(v_date_4515_, 4);
v_M_5843_ = lean_ctor_get(v_date_4515_, 5);
v_L_5844_ = lean_ctor_get(v_date_4515_, 6);
v_d_5845_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5846_ = lean_ctor_get(v_date_4515_, 8);
v_q_5847_ = lean_ctor_get(v_date_4515_, 9);
v_w_5848_ = lean_ctor_get(v_date_4515_, 10);
v_W_5849_ = lean_ctor_get(v_date_4515_, 11);
v_E_5850_ = lean_ctor_get(v_date_4515_, 12);
v_e_5851_ = lean_ctor_get(v_date_4515_, 13);
v_c_5852_ = lean_ctor_get(v_date_4515_, 14);
v_F_5853_ = lean_ctor_get(v_date_4515_, 15);
v_a_5854_ = lean_ctor_get(v_date_4515_, 16);
v_b_5855_ = lean_ctor_get(v_date_4515_, 17);
v_B_5856_ = lean_ctor_get(v_date_4515_, 18);
v_h_5857_ = lean_ctor_get(v_date_4515_, 19);
v_K_5858_ = lean_ctor_get(v_date_4515_, 20);
v_k_5859_ = lean_ctor_get(v_date_4515_, 21);
v_H_5860_ = lean_ctor_get(v_date_4515_, 22);
v_m_5861_ = lean_ctor_get(v_date_4515_, 23);
v_s_5862_ = lean_ctor_get(v_date_4515_, 24);
v_S_5863_ = lean_ctor_get(v_date_4515_, 25);
v_n_5864_ = lean_ctor_get(v_date_4515_, 27);
v_N_5865_ = lean_ctor_get(v_date_4515_, 28);
v_V_5866_ = lean_ctor_get(v_date_4515_, 29);
v_z_5867_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5868_ = lean_ctor_get(v_date_4515_, 31);
v_v_5869_ = lean_ctor_get(v_date_4515_, 32);
v_O_5870_ = lean_ctor_get(v_date_4515_, 33);
v_X_5871_ = lean_ctor_get(v_date_4515_, 34);
v_x_5872_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5873_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5883_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5883_ == 0)
{
lean_object* v_unused_5884_; 
v_unused_5884_ = lean_ctor_get(v_date_4515_, 26);
lean_dec(v_unused_5884_);
v___x_5875_ = v_date_4515_;
v_isShared_5876_ = v_isSharedCheck_5883_;
goto v_resetjp_5874_;
}
else
{
lean_inc(v_Z_5873_);
lean_inc(v_x_5872_);
lean_inc(v_X_5871_);
lean_inc(v_O_5870_);
lean_inc(v_v_5869_);
lean_inc(v_zabbrev_5868_);
lean_inc(v_z_5867_);
lean_inc(v_V_5866_);
lean_inc(v_N_5865_);
lean_inc(v_n_5864_);
lean_inc(v_S_5863_);
lean_inc(v_s_5862_);
lean_inc(v_m_5861_);
lean_inc(v_H_5860_);
lean_inc(v_k_5859_);
lean_inc(v_K_5858_);
lean_inc(v_h_5857_);
lean_inc(v_B_5856_);
lean_inc(v_b_5855_);
lean_inc(v_a_5854_);
lean_inc(v_F_5853_);
lean_inc(v_c_5852_);
lean_inc(v_e_5851_);
lean_inc(v_E_5850_);
lean_inc(v_W_5849_);
lean_inc(v_w_5848_);
lean_inc(v_q_5847_);
lean_inc(v_Q_5846_);
lean_inc(v_d_5845_);
lean_inc(v_L_5844_);
lean_inc(v_M_5843_);
lean_inc(v_D_5842_);
lean_inc(v_Y_5841_);
lean_inc(v_u_5840_);
lean_inc(v_y_5839_);
lean_inc(v_G_5838_);
lean_dec(v_date_4515_);
v___x_5875_ = lean_box(0);
v_isShared_5876_ = v_isSharedCheck_5883_;
goto v_resetjp_5874_;
}
v_resetjp_5874_:
{
lean_object* v___x_5878_; 
if (v_isShared_5837_ == 0)
{
lean_ctor_set_tag(v___x_5836_, 1);
lean_ctor_set(v___x_5836_, 0, v_data_4517_);
v___x_5878_ = v___x_5836_;
goto v_reusejp_5877_;
}
else
{
lean_object* v_reuseFailAlloc_5882_; 
v_reuseFailAlloc_5882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5882_, 0, v_data_4517_);
v___x_5878_ = v_reuseFailAlloc_5882_;
goto v_reusejp_5877_;
}
v_reusejp_5877_:
{
lean_object* v___x_5880_; 
if (v_isShared_5876_ == 0)
{
lean_ctor_set(v___x_5875_, 26, v___x_5878_);
v___x_5880_ = v___x_5875_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5881_; 
v_reuseFailAlloc_5881_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_G_5838_);
lean_ctor_set(v_reuseFailAlloc_5881_, 1, v_y_5839_);
lean_ctor_set(v_reuseFailAlloc_5881_, 2, v_u_5840_);
lean_ctor_set(v_reuseFailAlloc_5881_, 3, v_Y_5841_);
lean_ctor_set(v_reuseFailAlloc_5881_, 4, v_D_5842_);
lean_ctor_set(v_reuseFailAlloc_5881_, 5, v_M_5843_);
lean_ctor_set(v_reuseFailAlloc_5881_, 6, v_L_5844_);
lean_ctor_set(v_reuseFailAlloc_5881_, 7, v_d_5845_);
lean_ctor_set(v_reuseFailAlloc_5881_, 8, v_Q_5846_);
lean_ctor_set(v_reuseFailAlloc_5881_, 9, v_q_5847_);
lean_ctor_set(v_reuseFailAlloc_5881_, 10, v_w_5848_);
lean_ctor_set(v_reuseFailAlloc_5881_, 11, v_W_5849_);
lean_ctor_set(v_reuseFailAlloc_5881_, 12, v_E_5850_);
lean_ctor_set(v_reuseFailAlloc_5881_, 13, v_e_5851_);
lean_ctor_set(v_reuseFailAlloc_5881_, 14, v_c_5852_);
lean_ctor_set(v_reuseFailAlloc_5881_, 15, v_F_5853_);
lean_ctor_set(v_reuseFailAlloc_5881_, 16, v_a_5854_);
lean_ctor_set(v_reuseFailAlloc_5881_, 17, v_b_5855_);
lean_ctor_set(v_reuseFailAlloc_5881_, 18, v_B_5856_);
lean_ctor_set(v_reuseFailAlloc_5881_, 19, v_h_5857_);
lean_ctor_set(v_reuseFailAlloc_5881_, 20, v_K_5858_);
lean_ctor_set(v_reuseFailAlloc_5881_, 21, v_k_5859_);
lean_ctor_set(v_reuseFailAlloc_5881_, 22, v_H_5860_);
lean_ctor_set(v_reuseFailAlloc_5881_, 23, v_m_5861_);
lean_ctor_set(v_reuseFailAlloc_5881_, 24, v_s_5862_);
lean_ctor_set(v_reuseFailAlloc_5881_, 25, v_S_5863_);
lean_ctor_set(v_reuseFailAlloc_5881_, 26, v___x_5878_);
lean_ctor_set(v_reuseFailAlloc_5881_, 27, v_n_5864_);
lean_ctor_set(v_reuseFailAlloc_5881_, 28, v_N_5865_);
lean_ctor_set(v_reuseFailAlloc_5881_, 29, v_V_5866_);
lean_ctor_set(v_reuseFailAlloc_5881_, 30, v_z_5867_);
lean_ctor_set(v_reuseFailAlloc_5881_, 31, v_zabbrev_5868_);
lean_ctor_set(v_reuseFailAlloc_5881_, 32, v_v_5869_);
lean_ctor_set(v_reuseFailAlloc_5881_, 33, v_O_5870_);
lean_ctor_set(v_reuseFailAlloc_5881_, 34, v_X_5871_);
lean_ctor_set(v_reuseFailAlloc_5881_, 35, v_x_5872_);
lean_ctor_set(v_reuseFailAlloc_5881_, 36, v_Z_5873_);
v___x_5880_ = v_reuseFailAlloc_5881_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
return v___x_5880_;
}
}
}
}
}
case 27:
{
lean_object* v___x_5888_; uint8_t v_isShared_5889_; uint8_t v_isSharedCheck_5937_; 
v_isSharedCheck_5937_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5937_ == 0)
{
lean_object* v_unused_5938_; 
v_unused_5938_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5938_);
v___x_5888_ = v_modifier_4516_;
v_isShared_5889_ = v_isSharedCheck_5937_;
goto v_resetjp_5887_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5888_ = lean_box(0);
v_isShared_5889_ = v_isSharedCheck_5937_;
goto v_resetjp_5887_;
}
v_resetjp_5887_:
{
lean_object* v_G_5890_; lean_object* v_y_5891_; lean_object* v_u_5892_; lean_object* v_Y_5893_; lean_object* v_D_5894_; lean_object* v_M_5895_; lean_object* v_L_5896_; lean_object* v_d_5897_; lean_object* v_Q_5898_; lean_object* v_q_5899_; lean_object* v_w_5900_; lean_object* v_W_5901_; lean_object* v_E_5902_; lean_object* v_e_5903_; lean_object* v_c_5904_; lean_object* v_F_5905_; lean_object* v_a_5906_; lean_object* v_b_5907_; lean_object* v_B_5908_; lean_object* v_h_5909_; lean_object* v_K_5910_; lean_object* v_k_5911_; lean_object* v_H_5912_; lean_object* v_m_5913_; lean_object* v_s_5914_; lean_object* v_S_5915_; lean_object* v_A_5916_; lean_object* v_N_5917_; lean_object* v_V_5918_; lean_object* v_z_5919_; lean_object* v_zabbrev_5920_; lean_object* v_v_5921_; lean_object* v_O_5922_; lean_object* v_X_5923_; lean_object* v_x_5924_; lean_object* v_Z_5925_; lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_5935_; 
v_G_5890_ = lean_ctor_get(v_date_4515_, 0);
v_y_5891_ = lean_ctor_get(v_date_4515_, 1);
v_u_5892_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5893_ = lean_ctor_get(v_date_4515_, 3);
v_D_5894_ = lean_ctor_get(v_date_4515_, 4);
v_M_5895_ = lean_ctor_get(v_date_4515_, 5);
v_L_5896_ = lean_ctor_get(v_date_4515_, 6);
v_d_5897_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5898_ = lean_ctor_get(v_date_4515_, 8);
v_q_5899_ = lean_ctor_get(v_date_4515_, 9);
v_w_5900_ = lean_ctor_get(v_date_4515_, 10);
v_W_5901_ = lean_ctor_get(v_date_4515_, 11);
v_E_5902_ = lean_ctor_get(v_date_4515_, 12);
v_e_5903_ = lean_ctor_get(v_date_4515_, 13);
v_c_5904_ = lean_ctor_get(v_date_4515_, 14);
v_F_5905_ = lean_ctor_get(v_date_4515_, 15);
v_a_5906_ = lean_ctor_get(v_date_4515_, 16);
v_b_5907_ = lean_ctor_get(v_date_4515_, 17);
v_B_5908_ = lean_ctor_get(v_date_4515_, 18);
v_h_5909_ = lean_ctor_get(v_date_4515_, 19);
v_K_5910_ = lean_ctor_get(v_date_4515_, 20);
v_k_5911_ = lean_ctor_get(v_date_4515_, 21);
v_H_5912_ = lean_ctor_get(v_date_4515_, 22);
v_m_5913_ = lean_ctor_get(v_date_4515_, 23);
v_s_5914_ = lean_ctor_get(v_date_4515_, 24);
v_S_5915_ = lean_ctor_get(v_date_4515_, 25);
v_A_5916_ = lean_ctor_get(v_date_4515_, 26);
v_N_5917_ = lean_ctor_get(v_date_4515_, 28);
v_V_5918_ = lean_ctor_get(v_date_4515_, 29);
v_z_5919_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5920_ = lean_ctor_get(v_date_4515_, 31);
v_v_5921_ = lean_ctor_get(v_date_4515_, 32);
v_O_5922_ = lean_ctor_get(v_date_4515_, 33);
v_X_5923_ = lean_ctor_get(v_date_4515_, 34);
v_x_5924_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5925_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5935_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5935_ == 0)
{
lean_object* v_unused_5936_; 
v_unused_5936_ = lean_ctor_get(v_date_4515_, 27);
lean_dec(v_unused_5936_);
v___x_5927_ = v_date_4515_;
v_isShared_5928_ = v_isSharedCheck_5935_;
goto v_resetjp_5926_;
}
else
{
lean_inc(v_Z_5925_);
lean_inc(v_x_5924_);
lean_inc(v_X_5923_);
lean_inc(v_O_5922_);
lean_inc(v_v_5921_);
lean_inc(v_zabbrev_5920_);
lean_inc(v_z_5919_);
lean_inc(v_V_5918_);
lean_inc(v_N_5917_);
lean_inc(v_A_5916_);
lean_inc(v_S_5915_);
lean_inc(v_s_5914_);
lean_inc(v_m_5913_);
lean_inc(v_H_5912_);
lean_inc(v_k_5911_);
lean_inc(v_K_5910_);
lean_inc(v_h_5909_);
lean_inc(v_B_5908_);
lean_inc(v_b_5907_);
lean_inc(v_a_5906_);
lean_inc(v_F_5905_);
lean_inc(v_c_5904_);
lean_inc(v_e_5903_);
lean_inc(v_E_5902_);
lean_inc(v_W_5901_);
lean_inc(v_w_5900_);
lean_inc(v_q_5899_);
lean_inc(v_Q_5898_);
lean_inc(v_d_5897_);
lean_inc(v_L_5896_);
lean_inc(v_M_5895_);
lean_inc(v_D_5894_);
lean_inc(v_Y_5893_);
lean_inc(v_u_5892_);
lean_inc(v_y_5891_);
lean_inc(v_G_5890_);
lean_dec(v_date_4515_);
v___x_5927_ = lean_box(0);
v_isShared_5928_ = v_isSharedCheck_5935_;
goto v_resetjp_5926_;
}
v_resetjp_5926_:
{
lean_object* v___x_5930_; 
if (v_isShared_5889_ == 0)
{
lean_ctor_set_tag(v___x_5888_, 1);
lean_ctor_set(v___x_5888_, 0, v_data_4517_);
v___x_5930_ = v___x_5888_;
goto v_reusejp_5929_;
}
else
{
lean_object* v_reuseFailAlloc_5934_; 
v_reuseFailAlloc_5934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_data_4517_);
v___x_5930_ = v_reuseFailAlloc_5934_;
goto v_reusejp_5929_;
}
v_reusejp_5929_:
{
lean_object* v___x_5932_; 
if (v_isShared_5928_ == 0)
{
lean_ctor_set(v___x_5927_, 27, v___x_5930_);
v___x_5932_ = v___x_5927_;
goto v_reusejp_5931_;
}
else
{
lean_object* v_reuseFailAlloc_5933_; 
v_reuseFailAlloc_5933_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_G_5890_);
lean_ctor_set(v_reuseFailAlloc_5933_, 1, v_y_5891_);
lean_ctor_set(v_reuseFailAlloc_5933_, 2, v_u_5892_);
lean_ctor_set(v_reuseFailAlloc_5933_, 3, v_Y_5893_);
lean_ctor_set(v_reuseFailAlloc_5933_, 4, v_D_5894_);
lean_ctor_set(v_reuseFailAlloc_5933_, 5, v_M_5895_);
lean_ctor_set(v_reuseFailAlloc_5933_, 6, v_L_5896_);
lean_ctor_set(v_reuseFailAlloc_5933_, 7, v_d_5897_);
lean_ctor_set(v_reuseFailAlloc_5933_, 8, v_Q_5898_);
lean_ctor_set(v_reuseFailAlloc_5933_, 9, v_q_5899_);
lean_ctor_set(v_reuseFailAlloc_5933_, 10, v_w_5900_);
lean_ctor_set(v_reuseFailAlloc_5933_, 11, v_W_5901_);
lean_ctor_set(v_reuseFailAlloc_5933_, 12, v_E_5902_);
lean_ctor_set(v_reuseFailAlloc_5933_, 13, v_e_5903_);
lean_ctor_set(v_reuseFailAlloc_5933_, 14, v_c_5904_);
lean_ctor_set(v_reuseFailAlloc_5933_, 15, v_F_5905_);
lean_ctor_set(v_reuseFailAlloc_5933_, 16, v_a_5906_);
lean_ctor_set(v_reuseFailAlloc_5933_, 17, v_b_5907_);
lean_ctor_set(v_reuseFailAlloc_5933_, 18, v_B_5908_);
lean_ctor_set(v_reuseFailAlloc_5933_, 19, v_h_5909_);
lean_ctor_set(v_reuseFailAlloc_5933_, 20, v_K_5910_);
lean_ctor_set(v_reuseFailAlloc_5933_, 21, v_k_5911_);
lean_ctor_set(v_reuseFailAlloc_5933_, 22, v_H_5912_);
lean_ctor_set(v_reuseFailAlloc_5933_, 23, v_m_5913_);
lean_ctor_set(v_reuseFailAlloc_5933_, 24, v_s_5914_);
lean_ctor_set(v_reuseFailAlloc_5933_, 25, v_S_5915_);
lean_ctor_set(v_reuseFailAlloc_5933_, 26, v_A_5916_);
lean_ctor_set(v_reuseFailAlloc_5933_, 27, v___x_5930_);
lean_ctor_set(v_reuseFailAlloc_5933_, 28, v_N_5917_);
lean_ctor_set(v_reuseFailAlloc_5933_, 29, v_V_5918_);
lean_ctor_set(v_reuseFailAlloc_5933_, 30, v_z_5919_);
lean_ctor_set(v_reuseFailAlloc_5933_, 31, v_zabbrev_5920_);
lean_ctor_set(v_reuseFailAlloc_5933_, 32, v_v_5921_);
lean_ctor_set(v_reuseFailAlloc_5933_, 33, v_O_5922_);
lean_ctor_set(v_reuseFailAlloc_5933_, 34, v_X_5923_);
lean_ctor_set(v_reuseFailAlloc_5933_, 35, v_x_5924_);
lean_ctor_set(v_reuseFailAlloc_5933_, 36, v_Z_5925_);
v___x_5932_ = v_reuseFailAlloc_5933_;
goto v_reusejp_5931_;
}
v_reusejp_5931_:
{
return v___x_5932_;
}
}
}
}
}
case 28:
{
lean_object* v___x_5940_; uint8_t v_isShared_5941_; uint8_t v_isSharedCheck_5989_; 
v_isSharedCheck_5989_ = !lean_is_exclusive(v_modifier_4516_);
if (v_isSharedCheck_5989_ == 0)
{
lean_object* v_unused_5990_; 
v_unused_5990_ = lean_ctor_get(v_modifier_4516_, 0);
lean_dec(v_unused_5990_);
v___x_5940_ = v_modifier_4516_;
v_isShared_5941_ = v_isSharedCheck_5989_;
goto v_resetjp_5939_;
}
else
{
lean_dec(v_modifier_4516_);
v___x_5940_ = lean_box(0);
v_isShared_5941_ = v_isSharedCheck_5989_;
goto v_resetjp_5939_;
}
v_resetjp_5939_:
{
lean_object* v_G_5942_; lean_object* v_y_5943_; lean_object* v_u_5944_; lean_object* v_Y_5945_; lean_object* v_D_5946_; lean_object* v_M_5947_; lean_object* v_L_5948_; lean_object* v_d_5949_; lean_object* v_Q_5950_; lean_object* v_q_5951_; lean_object* v_w_5952_; lean_object* v_W_5953_; lean_object* v_E_5954_; lean_object* v_e_5955_; lean_object* v_c_5956_; lean_object* v_F_5957_; lean_object* v_a_5958_; lean_object* v_b_5959_; lean_object* v_B_5960_; lean_object* v_h_5961_; lean_object* v_K_5962_; lean_object* v_k_5963_; lean_object* v_H_5964_; lean_object* v_m_5965_; lean_object* v_s_5966_; lean_object* v_S_5967_; lean_object* v_A_5968_; lean_object* v_n_5969_; lean_object* v_V_5970_; lean_object* v_z_5971_; lean_object* v_zabbrev_5972_; lean_object* v_v_5973_; lean_object* v_O_5974_; lean_object* v_X_5975_; lean_object* v_x_5976_; lean_object* v_Z_5977_; lean_object* v___x_5979_; uint8_t v_isShared_5980_; uint8_t v_isSharedCheck_5987_; 
v_G_5942_ = lean_ctor_get(v_date_4515_, 0);
v_y_5943_ = lean_ctor_get(v_date_4515_, 1);
v_u_5944_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5945_ = lean_ctor_get(v_date_4515_, 3);
v_D_5946_ = lean_ctor_get(v_date_4515_, 4);
v_M_5947_ = lean_ctor_get(v_date_4515_, 5);
v_L_5948_ = lean_ctor_get(v_date_4515_, 6);
v_d_5949_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5950_ = lean_ctor_get(v_date_4515_, 8);
v_q_5951_ = lean_ctor_get(v_date_4515_, 9);
v_w_5952_ = lean_ctor_get(v_date_4515_, 10);
v_W_5953_ = lean_ctor_get(v_date_4515_, 11);
v_E_5954_ = lean_ctor_get(v_date_4515_, 12);
v_e_5955_ = lean_ctor_get(v_date_4515_, 13);
v_c_5956_ = lean_ctor_get(v_date_4515_, 14);
v_F_5957_ = lean_ctor_get(v_date_4515_, 15);
v_a_5958_ = lean_ctor_get(v_date_4515_, 16);
v_b_5959_ = lean_ctor_get(v_date_4515_, 17);
v_B_5960_ = lean_ctor_get(v_date_4515_, 18);
v_h_5961_ = lean_ctor_get(v_date_4515_, 19);
v_K_5962_ = lean_ctor_get(v_date_4515_, 20);
v_k_5963_ = lean_ctor_get(v_date_4515_, 21);
v_H_5964_ = lean_ctor_get(v_date_4515_, 22);
v_m_5965_ = lean_ctor_get(v_date_4515_, 23);
v_s_5966_ = lean_ctor_get(v_date_4515_, 24);
v_S_5967_ = lean_ctor_get(v_date_4515_, 25);
v_A_5968_ = lean_ctor_get(v_date_4515_, 26);
v_n_5969_ = lean_ctor_get(v_date_4515_, 27);
v_V_5970_ = lean_ctor_get(v_date_4515_, 29);
v_z_5971_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_5972_ = lean_ctor_get(v_date_4515_, 31);
v_v_5973_ = lean_ctor_get(v_date_4515_, 32);
v_O_5974_ = lean_ctor_get(v_date_4515_, 33);
v_X_5975_ = lean_ctor_get(v_date_4515_, 34);
v_x_5976_ = lean_ctor_get(v_date_4515_, 35);
v_Z_5977_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_5987_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_5987_ == 0)
{
lean_object* v_unused_5988_; 
v_unused_5988_ = lean_ctor_get(v_date_4515_, 28);
lean_dec(v_unused_5988_);
v___x_5979_ = v_date_4515_;
v_isShared_5980_ = v_isSharedCheck_5987_;
goto v_resetjp_5978_;
}
else
{
lean_inc(v_Z_5977_);
lean_inc(v_x_5976_);
lean_inc(v_X_5975_);
lean_inc(v_O_5974_);
lean_inc(v_v_5973_);
lean_inc(v_zabbrev_5972_);
lean_inc(v_z_5971_);
lean_inc(v_V_5970_);
lean_inc(v_n_5969_);
lean_inc(v_A_5968_);
lean_inc(v_S_5967_);
lean_inc(v_s_5966_);
lean_inc(v_m_5965_);
lean_inc(v_H_5964_);
lean_inc(v_k_5963_);
lean_inc(v_K_5962_);
lean_inc(v_h_5961_);
lean_inc(v_B_5960_);
lean_inc(v_b_5959_);
lean_inc(v_a_5958_);
lean_inc(v_F_5957_);
lean_inc(v_c_5956_);
lean_inc(v_e_5955_);
lean_inc(v_E_5954_);
lean_inc(v_W_5953_);
lean_inc(v_w_5952_);
lean_inc(v_q_5951_);
lean_inc(v_Q_5950_);
lean_inc(v_d_5949_);
lean_inc(v_L_5948_);
lean_inc(v_M_5947_);
lean_inc(v_D_5946_);
lean_inc(v_Y_5945_);
lean_inc(v_u_5944_);
lean_inc(v_y_5943_);
lean_inc(v_G_5942_);
lean_dec(v_date_4515_);
v___x_5979_ = lean_box(0);
v_isShared_5980_ = v_isSharedCheck_5987_;
goto v_resetjp_5978_;
}
v_resetjp_5978_:
{
lean_object* v___x_5982_; 
if (v_isShared_5941_ == 0)
{
lean_ctor_set_tag(v___x_5940_, 1);
lean_ctor_set(v___x_5940_, 0, v_data_4517_);
v___x_5982_ = v___x_5940_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5986_; 
v_reuseFailAlloc_5986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5986_, 0, v_data_4517_);
v___x_5982_ = v_reuseFailAlloc_5986_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
lean_object* v___x_5984_; 
if (v_isShared_5980_ == 0)
{
lean_ctor_set(v___x_5979_, 28, v___x_5982_);
v___x_5984_ = v___x_5979_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_5985_; 
v_reuseFailAlloc_5985_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_G_5942_);
lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_y_5943_);
lean_ctor_set(v_reuseFailAlloc_5985_, 2, v_u_5944_);
lean_ctor_set(v_reuseFailAlloc_5985_, 3, v_Y_5945_);
lean_ctor_set(v_reuseFailAlloc_5985_, 4, v_D_5946_);
lean_ctor_set(v_reuseFailAlloc_5985_, 5, v_M_5947_);
lean_ctor_set(v_reuseFailAlloc_5985_, 6, v_L_5948_);
lean_ctor_set(v_reuseFailAlloc_5985_, 7, v_d_5949_);
lean_ctor_set(v_reuseFailAlloc_5985_, 8, v_Q_5950_);
lean_ctor_set(v_reuseFailAlloc_5985_, 9, v_q_5951_);
lean_ctor_set(v_reuseFailAlloc_5985_, 10, v_w_5952_);
lean_ctor_set(v_reuseFailAlloc_5985_, 11, v_W_5953_);
lean_ctor_set(v_reuseFailAlloc_5985_, 12, v_E_5954_);
lean_ctor_set(v_reuseFailAlloc_5985_, 13, v_e_5955_);
lean_ctor_set(v_reuseFailAlloc_5985_, 14, v_c_5956_);
lean_ctor_set(v_reuseFailAlloc_5985_, 15, v_F_5957_);
lean_ctor_set(v_reuseFailAlloc_5985_, 16, v_a_5958_);
lean_ctor_set(v_reuseFailAlloc_5985_, 17, v_b_5959_);
lean_ctor_set(v_reuseFailAlloc_5985_, 18, v_B_5960_);
lean_ctor_set(v_reuseFailAlloc_5985_, 19, v_h_5961_);
lean_ctor_set(v_reuseFailAlloc_5985_, 20, v_K_5962_);
lean_ctor_set(v_reuseFailAlloc_5985_, 21, v_k_5963_);
lean_ctor_set(v_reuseFailAlloc_5985_, 22, v_H_5964_);
lean_ctor_set(v_reuseFailAlloc_5985_, 23, v_m_5965_);
lean_ctor_set(v_reuseFailAlloc_5985_, 24, v_s_5966_);
lean_ctor_set(v_reuseFailAlloc_5985_, 25, v_S_5967_);
lean_ctor_set(v_reuseFailAlloc_5985_, 26, v_A_5968_);
lean_ctor_set(v_reuseFailAlloc_5985_, 27, v_n_5969_);
lean_ctor_set(v_reuseFailAlloc_5985_, 28, v___x_5982_);
lean_ctor_set(v_reuseFailAlloc_5985_, 29, v_V_5970_);
lean_ctor_set(v_reuseFailAlloc_5985_, 30, v_z_5971_);
lean_ctor_set(v_reuseFailAlloc_5985_, 31, v_zabbrev_5972_);
lean_ctor_set(v_reuseFailAlloc_5985_, 32, v_v_5973_);
lean_ctor_set(v_reuseFailAlloc_5985_, 33, v_O_5974_);
lean_ctor_set(v_reuseFailAlloc_5985_, 34, v_X_5975_);
lean_ctor_set(v_reuseFailAlloc_5985_, 35, v_x_5976_);
lean_ctor_set(v_reuseFailAlloc_5985_, 36, v_Z_5977_);
v___x_5984_ = v_reuseFailAlloc_5985_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
return v___x_5984_;
}
}
}
}
}
case 29:
{
lean_object* v_G_5991_; lean_object* v_y_5992_; lean_object* v_u_5993_; lean_object* v_Y_5994_; lean_object* v_D_5995_; lean_object* v_M_5996_; lean_object* v_L_5997_; lean_object* v_d_5998_; lean_object* v_Q_5999_; lean_object* v_q_6000_; lean_object* v_w_6001_; lean_object* v_W_6002_; lean_object* v_E_6003_; lean_object* v_e_6004_; lean_object* v_c_6005_; lean_object* v_F_6006_; lean_object* v_a_6007_; lean_object* v_b_6008_; lean_object* v_B_6009_; lean_object* v_h_6010_; lean_object* v_K_6011_; lean_object* v_k_6012_; lean_object* v_H_6013_; lean_object* v_m_6014_; lean_object* v_s_6015_; lean_object* v_S_6016_; lean_object* v_A_6017_; lean_object* v_n_6018_; lean_object* v_N_6019_; lean_object* v_z_6020_; lean_object* v_zabbrev_6021_; lean_object* v_v_6022_; lean_object* v_O_6023_; lean_object* v_X_6024_; lean_object* v_x_6025_; lean_object* v_Z_6026_; lean_object* v___x_6028_; uint8_t v_isShared_6029_; uint8_t v_isSharedCheck_6034_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_G_5991_ = lean_ctor_get(v_date_4515_, 0);
v_y_5992_ = lean_ctor_get(v_date_4515_, 1);
v_u_5993_ = lean_ctor_get(v_date_4515_, 2);
v_Y_5994_ = lean_ctor_get(v_date_4515_, 3);
v_D_5995_ = lean_ctor_get(v_date_4515_, 4);
v_M_5996_ = lean_ctor_get(v_date_4515_, 5);
v_L_5997_ = lean_ctor_get(v_date_4515_, 6);
v_d_5998_ = lean_ctor_get(v_date_4515_, 7);
v_Q_5999_ = lean_ctor_get(v_date_4515_, 8);
v_q_6000_ = lean_ctor_get(v_date_4515_, 9);
v_w_6001_ = lean_ctor_get(v_date_4515_, 10);
v_W_6002_ = lean_ctor_get(v_date_4515_, 11);
v_E_6003_ = lean_ctor_get(v_date_4515_, 12);
v_e_6004_ = lean_ctor_get(v_date_4515_, 13);
v_c_6005_ = lean_ctor_get(v_date_4515_, 14);
v_F_6006_ = lean_ctor_get(v_date_4515_, 15);
v_a_6007_ = lean_ctor_get(v_date_4515_, 16);
v_b_6008_ = lean_ctor_get(v_date_4515_, 17);
v_B_6009_ = lean_ctor_get(v_date_4515_, 18);
v_h_6010_ = lean_ctor_get(v_date_4515_, 19);
v_K_6011_ = lean_ctor_get(v_date_4515_, 20);
v_k_6012_ = lean_ctor_get(v_date_4515_, 21);
v_H_6013_ = lean_ctor_get(v_date_4515_, 22);
v_m_6014_ = lean_ctor_get(v_date_4515_, 23);
v_s_6015_ = lean_ctor_get(v_date_4515_, 24);
v_S_6016_ = lean_ctor_get(v_date_4515_, 25);
v_A_6017_ = lean_ctor_get(v_date_4515_, 26);
v_n_6018_ = lean_ctor_get(v_date_4515_, 27);
v_N_6019_ = lean_ctor_get(v_date_4515_, 28);
v_z_6020_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_6021_ = lean_ctor_get(v_date_4515_, 31);
v_v_6022_ = lean_ctor_get(v_date_4515_, 32);
v_O_6023_ = lean_ctor_get(v_date_4515_, 33);
v_X_6024_ = lean_ctor_get(v_date_4515_, 34);
v_x_6025_ = lean_ctor_get(v_date_4515_, 35);
v_Z_6026_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_6034_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_6034_ == 0)
{
lean_object* v_unused_6035_; 
v_unused_6035_ = lean_ctor_get(v_date_4515_, 29);
lean_dec(v_unused_6035_);
v___x_6028_ = v_date_4515_;
v_isShared_6029_ = v_isSharedCheck_6034_;
goto v_resetjp_6027_;
}
else
{
lean_inc(v_Z_6026_);
lean_inc(v_x_6025_);
lean_inc(v_X_6024_);
lean_inc(v_O_6023_);
lean_inc(v_v_6022_);
lean_inc(v_zabbrev_6021_);
lean_inc(v_z_6020_);
lean_inc(v_N_6019_);
lean_inc(v_n_6018_);
lean_inc(v_A_6017_);
lean_inc(v_S_6016_);
lean_inc(v_s_6015_);
lean_inc(v_m_6014_);
lean_inc(v_H_6013_);
lean_inc(v_k_6012_);
lean_inc(v_K_6011_);
lean_inc(v_h_6010_);
lean_inc(v_B_6009_);
lean_inc(v_b_6008_);
lean_inc(v_a_6007_);
lean_inc(v_F_6006_);
lean_inc(v_c_6005_);
lean_inc(v_e_6004_);
lean_inc(v_E_6003_);
lean_inc(v_W_6002_);
lean_inc(v_w_6001_);
lean_inc(v_q_6000_);
lean_inc(v_Q_5999_);
lean_inc(v_d_5998_);
lean_inc(v_L_5997_);
lean_inc(v_M_5996_);
lean_inc(v_D_5995_);
lean_inc(v_Y_5994_);
lean_inc(v_u_5993_);
lean_inc(v_y_5992_);
lean_inc(v_G_5991_);
lean_dec(v_date_4515_);
v___x_6028_ = lean_box(0);
v_isShared_6029_ = v_isSharedCheck_6034_;
goto v_resetjp_6027_;
}
v_resetjp_6027_:
{
lean_object* v___x_6030_; lean_object* v___x_6032_; 
v___x_6030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6030_, 0, v_data_4517_);
if (v_isShared_6029_ == 0)
{
lean_ctor_set(v___x_6028_, 29, v___x_6030_);
v___x_6032_ = v___x_6028_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v_G_5991_);
lean_ctor_set(v_reuseFailAlloc_6033_, 1, v_y_5992_);
lean_ctor_set(v_reuseFailAlloc_6033_, 2, v_u_5993_);
lean_ctor_set(v_reuseFailAlloc_6033_, 3, v_Y_5994_);
lean_ctor_set(v_reuseFailAlloc_6033_, 4, v_D_5995_);
lean_ctor_set(v_reuseFailAlloc_6033_, 5, v_M_5996_);
lean_ctor_set(v_reuseFailAlloc_6033_, 6, v_L_5997_);
lean_ctor_set(v_reuseFailAlloc_6033_, 7, v_d_5998_);
lean_ctor_set(v_reuseFailAlloc_6033_, 8, v_Q_5999_);
lean_ctor_set(v_reuseFailAlloc_6033_, 9, v_q_6000_);
lean_ctor_set(v_reuseFailAlloc_6033_, 10, v_w_6001_);
lean_ctor_set(v_reuseFailAlloc_6033_, 11, v_W_6002_);
lean_ctor_set(v_reuseFailAlloc_6033_, 12, v_E_6003_);
lean_ctor_set(v_reuseFailAlloc_6033_, 13, v_e_6004_);
lean_ctor_set(v_reuseFailAlloc_6033_, 14, v_c_6005_);
lean_ctor_set(v_reuseFailAlloc_6033_, 15, v_F_6006_);
lean_ctor_set(v_reuseFailAlloc_6033_, 16, v_a_6007_);
lean_ctor_set(v_reuseFailAlloc_6033_, 17, v_b_6008_);
lean_ctor_set(v_reuseFailAlloc_6033_, 18, v_B_6009_);
lean_ctor_set(v_reuseFailAlloc_6033_, 19, v_h_6010_);
lean_ctor_set(v_reuseFailAlloc_6033_, 20, v_K_6011_);
lean_ctor_set(v_reuseFailAlloc_6033_, 21, v_k_6012_);
lean_ctor_set(v_reuseFailAlloc_6033_, 22, v_H_6013_);
lean_ctor_set(v_reuseFailAlloc_6033_, 23, v_m_6014_);
lean_ctor_set(v_reuseFailAlloc_6033_, 24, v_s_6015_);
lean_ctor_set(v_reuseFailAlloc_6033_, 25, v_S_6016_);
lean_ctor_set(v_reuseFailAlloc_6033_, 26, v_A_6017_);
lean_ctor_set(v_reuseFailAlloc_6033_, 27, v_n_6018_);
lean_ctor_set(v_reuseFailAlloc_6033_, 28, v_N_6019_);
lean_ctor_set(v_reuseFailAlloc_6033_, 29, v___x_6030_);
lean_ctor_set(v_reuseFailAlloc_6033_, 30, v_z_6020_);
lean_ctor_set(v_reuseFailAlloc_6033_, 31, v_zabbrev_6021_);
lean_ctor_set(v_reuseFailAlloc_6033_, 32, v_v_6022_);
lean_ctor_set(v_reuseFailAlloc_6033_, 33, v_O_6023_);
lean_ctor_set(v_reuseFailAlloc_6033_, 34, v_X_6024_);
lean_ctor_set(v_reuseFailAlloc_6033_, 35, v_x_6025_);
lean_ctor_set(v_reuseFailAlloc_6033_, 36, v_Z_6026_);
v___x_6032_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
return v___x_6032_;
}
}
}
case 30:
{
uint8_t v_presentation_6036_; 
v_presentation_6036_ = lean_ctor_get_uint8(v_modifier_4516_, 0);
lean_dec_ref_known(v_modifier_4516_, 0);
if (v_presentation_6036_ == 0)
{
lean_object* v_G_6037_; lean_object* v_y_6038_; lean_object* v_u_6039_; lean_object* v_Y_6040_; lean_object* v_D_6041_; lean_object* v_M_6042_; lean_object* v_L_6043_; lean_object* v_d_6044_; lean_object* v_Q_6045_; lean_object* v_q_6046_; lean_object* v_w_6047_; lean_object* v_W_6048_; lean_object* v_E_6049_; lean_object* v_e_6050_; lean_object* v_c_6051_; lean_object* v_F_6052_; lean_object* v_a_6053_; lean_object* v_b_6054_; lean_object* v_B_6055_; lean_object* v_h_6056_; lean_object* v_K_6057_; lean_object* v_k_6058_; lean_object* v_H_6059_; lean_object* v_m_6060_; lean_object* v_s_6061_; lean_object* v_S_6062_; lean_object* v_A_6063_; lean_object* v_n_6064_; lean_object* v_N_6065_; lean_object* v_V_6066_; lean_object* v_z_6067_; lean_object* v_v_6068_; lean_object* v_O_6069_; lean_object* v_X_6070_; lean_object* v_x_6071_; lean_object* v_Z_6072_; lean_object* v___x_6074_; uint8_t v_isShared_6075_; uint8_t v_isSharedCheck_6080_; 
v_G_6037_ = lean_ctor_get(v_date_4515_, 0);
v_y_6038_ = lean_ctor_get(v_date_4515_, 1);
v_u_6039_ = lean_ctor_get(v_date_4515_, 2);
v_Y_6040_ = lean_ctor_get(v_date_4515_, 3);
v_D_6041_ = lean_ctor_get(v_date_4515_, 4);
v_M_6042_ = lean_ctor_get(v_date_4515_, 5);
v_L_6043_ = lean_ctor_get(v_date_4515_, 6);
v_d_6044_ = lean_ctor_get(v_date_4515_, 7);
v_Q_6045_ = lean_ctor_get(v_date_4515_, 8);
v_q_6046_ = lean_ctor_get(v_date_4515_, 9);
v_w_6047_ = lean_ctor_get(v_date_4515_, 10);
v_W_6048_ = lean_ctor_get(v_date_4515_, 11);
v_E_6049_ = lean_ctor_get(v_date_4515_, 12);
v_e_6050_ = lean_ctor_get(v_date_4515_, 13);
v_c_6051_ = lean_ctor_get(v_date_4515_, 14);
v_F_6052_ = lean_ctor_get(v_date_4515_, 15);
v_a_6053_ = lean_ctor_get(v_date_4515_, 16);
v_b_6054_ = lean_ctor_get(v_date_4515_, 17);
v_B_6055_ = lean_ctor_get(v_date_4515_, 18);
v_h_6056_ = lean_ctor_get(v_date_4515_, 19);
v_K_6057_ = lean_ctor_get(v_date_4515_, 20);
v_k_6058_ = lean_ctor_get(v_date_4515_, 21);
v_H_6059_ = lean_ctor_get(v_date_4515_, 22);
v_m_6060_ = lean_ctor_get(v_date_4515_, 23);
v_s_6061_ = lean_ctor_get(v_date_4515_, 24);
v_S_6062_ = lean_ctor_get(v_date_4515_, 25);
v_A_6063_ = lean_ctor_get(v_date_4515_, 26);
v_n_6064_ = lean_ctor_get(v_date_4515_, 27);
v_N_6065_ = lean_ctor_get(v_date_4515_, 28);
v_V_6066_ = lean_ctor_get(v_date_4515_, 29);
v_z_6067_ = lean_ctor_get(v_date_4515_, 30);
v_v_6068_ = lean_ctor_get(v_date_4515_, 32);
v_O_6069_ = lean_ctor_get(v_date_4515_, 33);
v_X_6070_ = lean_ctor_get(v_date_4515_, 34);
v_x_6071_ = lean_ctor_get(v_date_4515_, 35);
v_Z_6072_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_6080_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_6080_ == 0)
{
lean_object* v_unused_6081_; 
v_unused_6081_ = lean_ctor_get(v_date_4515_, 31);
lean_dec(v_unused_6081_);
v___x_6074_ = v_date_4515_;
v_isShared_6075_ = v_isSharedCheck_6080_;
goto v_resetjp_6073_;
}
else
{
lean_inc(v_Z_6072_);
lean_inc(v_x_6071_);
lean_inc(v_X_6070_);
lean_inc(v_O_6069_);
lean_inc(v_v_6068_);
lean_inc(v_z_6067_);
lean_inc(v_V_6066_);
lean_inc(v_N_6065_);
lean_inc(v_n_6064_);
lean_inc(v_A_6063_);
lean_inc(v_S_6062_);
lean_inc(v_s_6061_);
lean_inc(v_m_6060_);
lean_inc(v_H_6059_);
lean_inc(v_k_6058_);
lean_inc(v_K_6057_);
lean_inc(v_h_6056_);
lean_inc(v_B_6055_);
lean_inc(v_b_6054_);
lean_inc(v_a_6053_);
lean_inc(v_F_6052_);
lean_inc(v_c_6051_);
lean_inc(v_e_6050_);
lean_inc(v_E_6049_);
lean_inc(v_W_6048_);
lean_inc(v_w_6047_);
lean_inc(v_q_6046_);
lean_inc(v_Q_6045_);
lean_inc(v_d_6044_);
lean_inc(v_L_6043_);
lean_inc(v_M_6042_);
lean_inc(v_D_6041_);
lean_inc(v_Y_6040_);
lean_inc(v_u_6039_);
lean_inc(v_y_6038_);
lean_inc(v_G_6037_);
lean_dec(v_date_4515_);
v___x_6074_ = lean_box(0);
v_isShared_6075_ = v_isSharedCheck_6080_;
goto v_resetjp_6073_;
}
v_resetjp_6073_:
{
lean_object* v___x_6076_; lean_object* v___x_6078_; 
v___x_6076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6076_, 0, v_data_4517_);
if (v_isShared_6075_ == 0)
{
lean_ctor_set(v___x_6074_, 31, v___x_6076_);
v___x_6078_ = v___x_6074_;
goto v_reusejp_6077_;
}
else
{
lean_object* v_reuseFailAlloc_6079_; 
v_reuseFailAlloc_6079_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6079_, 0, v_G_6037_);
lean_ctor_set(v_reuseFailAlloc_6079_, 1, v_y_6038_);
lean_ctor_set(v_reuseFailAlloc_6079_, 2, v_u_6039_);
lean_ctor_set(v_reuseFailAlloc_6079_, 3, v_Y_6040_);
lean_ctor_set(v_reuseFailAlloc_6079_, 4, v_D_6041_);
lean_ctor_set(v_reuseFailAlloc_6079_, 5, v_M_6042_);
lean_ctor_set(v_reuseFailAlloc_6079_, 6, v_L_6043_);
lean_ctor_set(v_reuseFailAlloc_6079_, 7, v_d_6044_);
lean_ctor_set(v_reuseFailAlloc_6079_, 8, v_Q_6045_);
lean_ctor_set(v_reuseFailAlloc_6079_, 9, v_q_6046_);
lean_ctor_set(v_reuseFailAlloc_6079_, 10, v_w_6047_);
lean_ctor_set(v_reuseFailAlloc_6079_, 11, v_W_6048_);
lean_ctor_set(v_reuseFailAlloc_6079_, 12, v_E_6049_);
lean_ctor_set(v_reuseFailAlloc_6079_, 13, v_e_6050_);
lean_ctor_set(v_reuseFailAlloc_6079_, 14, v_c_6051_);
lean_ctor_set(v_reuseFailAlloc_6079_, 15, v_F_6052_);
lean_ctor_set(v_reuseFailAlloc_6079_, 16, v_a_6053_);
lean_ctor_set(v_reuseFailAlloc_6079_, 17, v_b_6054_);
lean_ctor_set(v_reuseFailAlloc_6079_, 18, v_B_6055_);
lean_ctor_set(v_reuseFailAlloc_6079_, 19, v_h_6056_);
lean_ctor_set(v_reuseFailAlloc_6079_, 20, v_K_6057_);
lean_ctor_set(v_reuseFailAlloc_6079_, 21, v_k_6058_);
lean_ctor_set(v_reuseFailAlloc_6079_, 22, v_H_6059_);
lean_ctor_set(v_reuseFailAlloc_6079_, 23, v_m_6060_);
lean_ctor_set(v_reuseFailAlloc_6079_, 24, v_s_6061_);
lean_ctor_set(v_reuseFailAlloc_6079_, 25, v_S_6062_);
lean_ctor_set(v_reuseFailAlloc_6079_, 26, v_A_6063_);
lean_ctor_set(v_reuseFailAlloc_6079_, 27, v_n_6064_);
lean_ctor_set(v_reuseFailAlloc_6079_, 28, v_N_6065_);
lean_ctor_set(v_reuseFailAlloc_6079_, 29, v_V_6066_);
lean_ctor_set(v_reuseFailAlloc_6079_, 30, v_z_6067_);
lean_ctor_set(v_reuseFailAlloc_6079_, 31, v___x_6076_);
lean_ctor_set(v_reuseFailAlloc_6079_, 32, v_v_6068_);
lean_ctor_set(v_reuseFailAlloc_6079_, 33, v_O_6069_);
lean_ctor_set(v_reuseFailAlloc_6079_, 34, v_X_6070_);
lean_ctor_set(v_reuseFailAlloc_6079_, 35, v_x_6071_);
lean_ctor_set(v_reuseFailAlloc_6079_, 36, v_Z_6072_);
v___x_6078_ = v_reuseFailAlloc_6079_;
goto v_reusejp_6077_;
}
v_reusejp_6077_:
{
return v___x_6078_;
}
}
}
else
{
lean_object* v_G_6082_; lean_object* v_y_6083_; lean_object* v_u_6084_; lean_object* v_Y_6085_; lean_object* v_D_6086_; lean_object* v_M_6087_; lean_object* v_L_6088_; lean_object* v_d_6089_; lean_object* v_Q_6090_; lean_object* v_q_6091_; lean_object* v_w_6092_; lean_object* v_W_6093_; lean_object* v_E_6094_; lean_object* v_e_6095_; lean_object* v_c_6096_; lean_object* v_F_6097_; lean_object* v_a_6098_; lean_object* v_b_6099_; lean_object* v_B_6100_; lean_object* v_h_6101_; lean_object* v_K_6102_; lean_object* v_k_6103_; lean_object* v_H_6104_; lean_object* v_m_6105_; lean_object* v_s_6106_; lean_object* v_S_6107_; lean_object* v_A_6108_; lean_object* v_n_6109_; lean_object* v_N_6110_; lean_object* v_V_6111_; lean_object* v_zabbrev_6112_; lean_object* v_v_6113_; lean_object* v_O_6114_; lean_object* v_X_6115_; lean_object* v_x_6116_; lean_object* v_Z_6117_; lean_object* v___x_6119_; uint8_t v_isShared_6120_; uint8_t v_isSharedCheck_6125_; 
v_G_6082_ = lean_ctor_get(v_date_4515_, 0);
v_y_6083_ = lean_ctor_get(v_date_4515_, 1);
v_u_6084_ = lean_ctor_get(v_date_4515_, 2);
v_Y_6085_ = lean_ctor_get(v_date_4515_, 3);
v_D_6086_ = lean_ctor_get(v_date_4515_, 4);
v_M_6087_ = lean_ctor_get(v_date_4515_, 5);
v_L_6088_ = lean_ctor_get(v_date_4515_, 6);
v_d_6089_ = lean_ctor_get(v_date_4515_, 7);
v_Q_6090_ = lean_ctor_get(v_date_4515_, 8);
v_q_6091_ = lean_ctor_get(v_date_4515_, 9);
v_w_6092_ = lean_ctor_get(v_date_4515_, 10);
v_W_6093_ = lean_ctor_get(v_date_4515_, 11);
v_E_6094_ = lean_ctor_get(v_date_4515_, 12);
v_e_6095_ = lean_ctor_get(v_date_4515_, 13);
v_c_6096_ = lean_ctor_get(v_date_4515_, 14);
v_F_6097_ = lean_ctor_get(v_date_4515_, 15);
v_a_6098_ = lean_ctor_get(v_date_4515_, 16);
v_b_6099_ = lean_ctor_get(v_date_4515_, 17);
v_B_6100_ = lean_ctor_get(v_date_4515_, 18);
v_h_6101_ = lean_ctor_get(v_date_4515_, 19);
v_K_6102_ = lean_ctor_get(v_date_4515_, 20);
v_k_6103_ = lean_ctor_get(v_date_4515_, 21);
v_H_6104_ = lean_ctor_get(v_date_4515_, 22);
v_m_6105_ = lean_ctor_get(v_date_4515_, 23);
v_s_6106_ = lean_ctor_get(v_date_4515_, 24);
v_S_6107_ = lean_ctor_get(v_date_4515_, 25);
v_A_6108_ = lean_ctor_get(v_date_4515_, 26);
v_n_6109_ = lean_ctor_get(v_date_4515_, 27);
v_N_6110_ = lean_ctor_get(v_date_4515_, 28);
v_V_6111_ = lean_ctor_get(v_date_4515_, 29);
v_zabbrev_6112_ = lean_ctor_get(v_date_4515_, 31);
v_v_6113_ = lean_ctor_get(v_date_4515_, 32);
v_O_6114_ = lean_ctor_get(v_date_4515_, 33);
v_X_6115_ = lean_ctor_get(v_date_4515_, 34);
v_x_6116_ = lean_ctor_get(v_date_4515_, 35);
v_Z_6117_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_6125_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_6125_ == 0)
{
lean_object* v_unused_6126_; 
v_unused_6126_ = lean_ctor_get(v_date_4515_, 30);
lean_dec(v_unused_6126_);
v___x_6119_ = v_date_4515_;
v_isShared_6120_ = v_isSharedCheck_6125_;
goto v_resetjp_6118_;
}
else
{
lean_inc(v_Z_6117_);
lean_inc(v_x_6116_);
lean_inc(v_X_6115_);
lean_inc(v_O_6114_);
lean_inc(v_v_6113_);
lean_inc(v_zabbrev_6112_);
lean_inc(v_V_6111_);
lean_inc(v_N_6110_);
lean_inc(v_n_6109_);
lean_inc(v_A_6108_);
lean_inc(v_S_6107_);
lean_inc(v_s_6106_);
lean_inc(v_m_6105_);
lean_inc(v_H_6104_);
lean_inc(v_k_6103_);
lean_inc(v_K_6102_);
lean_inc(v_h_6101_);
lean_inc(v_B_6100_);
lean_inc(v_b_6099_);
lean_inc(v_a_6098_);
lean_inc(v_F_6097_);
lean_inc(v_c_6096_);
lean_inc(v_e_6095_);
lean_inc(v_E_6094_);
lean_inc(v_W_6093_);
lean_inc(v_w_6092_);
lean_inc(v_q_6091_);
lean_inc(v_Q_6090_);
lean_inc(v_d_6089_);
lean_inc(v_L_6088_);
lean_inc(v_M_6087_);
lean_inc(v_D_6086_);
lean_inc(v_Y_6085_);
lean_inc(v_u_6084_);
lean_inc(v_y_6083_);
lean_inc(v_G_6082_);
lean_dec(v_date_4515_);
v___x_6119_ = lean_box(0);
v_isShared_6120_ = v_isSharedCheck_6125_;
goto v_resetjp_6118_;
}
v_resetjp_6118_:
{
lean_object* v___x_6121_; lean_object* v___x_6123_; 
v___x_6121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6121_, 0, v_data_4517_);
if (v_isShared_6120_ == 0)
{
lean_ctor_set(v___x_6119_, 30, v___x_6121_);
v___x_6123_ = v___x_6119_;
goto v_reusejp_6122_;
}
else
{
lean_object* v_reuseFailAlloc_6124_; 
v_reuseFailAlloc_6124_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_G_6082_);
lean_ctor_set(v_reuseFailAlloc_6124_, 1, v_y_6083_);
lean_ctor_set(v_reuseFailAlloc_6124_, 2, v_u_6084_);
lean_ctor_set(v_reuseFailAlloc_6124_, 3, v_Y_6085_);
lean_ctor_set(v_reuseFailAlloc_6124_, 4, v_D_6086_);
lean_ctor_set(v_reuseFailAlloc_6124_, 5, v_M_6087_);
lean_ctor_set(v_reuseFailAlloc_6124_, 6, v_L_6088_);
lean_ctor_set(v_reuseFailAlloc_6124_, 7, v_d_6089_);
lean_ctor_set(v_reuseFailAlloc_6124_, 8, v_Q_6090_);
lean_ctor_set(v_reuseFailAlloc_6124_, 9, v_q_6091_);
lean_ctor_set(v_reuseFailAlloc_6124_, 10, v_w_6092_);
lean_ctor_set(v_reuseFailAlloc_6124_, 11, v_W_6093_);
lean_ctor_set(v_reuseFailAlloc_6124_, 12, v_E_6094_);
lean_ctor_set(v_reuseFailAlloc_6124_, 13, v_e_6095_);
lean_ctor_set(v_reuseFailAlloc_6124_, 14, v_c_6096_);
lean_ctor_set(v_reuseFailAlloc_6124_, 15, v_F_6097_);
lean_ctor_set(v_reuseFailAlloc_6124_, 16, v_a_6098_);
lean_ctor_set(v_reuseFailAlloc_6124_, 17, v_b_6099_);
lean_ctor_set(v_reuseFailAlloc_6124_, 18, v_B_6100_);
lean_ctor_set(v_reuseFailAlloc_6124_, 19, v_h_6101_);
lean_ctor_set(v_reuseFailAlloc_6124_, 20, v_K_6102_);
lean_ctor_set(v_reuseFailAlloc_6124_, 21, v_k_6103_);
lean_ctor_set(v_reuseFailAlloc_6124_, 22, v_H_6104_);
lean_ctor_set(v_reuseFailAlloc_6124_, 23, v_m_6105_);
lean_ctor_set(v_reuseFailAlloc_6124_, 24, v_s_6106_);
lean_ctor_set(v_reuseFailAlloc_6124_, 25, v_S_6107_);
lean_ctor_set(v_reuseFailAlloc_6124_, 26, v_A_6108_);
lean_ctor_set(v_reuseFailAlloc_6124_, 27, v_n_6109_);
lean_ctor_set(v_reuseFailAlloc_6124_, 28, v_N_6110_);
lean_ctor_set(v_reuseFailAlloc_6124_, 29, v_V_6111_);
lean_ctor_set(v_reuseFailAlloc_6124_, 30, v___x_6121_);
lean_ctor_set(v_reuseFailAlloc_6124_, 31, v_zabbrev_6112_);
lean_ctor_set(v_reuseFailAlloc_6124_, 32, v_v_6113_);
lean_ctor_set(v_reuseFailAlloc_6124_, 33, v_O_6114_);
lean_ctor_set(v_reuseFailAlloc_6124_, 34, v_X_6115_);
lean_ctor_set(v_reuseFailAlloc_6124_, 35, v_x_6116_);
lean_ctor_set(v_reuseFailAlloc_6124_, 36, v_Z_6117_);
v___x_6123_ = v_reuseFailAlloc_6124_;
goto v_reusejp_6122_;
}
v_reusejp_6122_:
{
return v___x_6123_;
}
}
}
}
case 31:
{
lean_object* v_G_6127_; lean_object* v_y_6128_; lean_object* v_u_6129_; lean_object* v_Y_6130_; lean_object* v_D_6131_; lean_object* v_M_6132_; lean_object* v_L_6133_; lean_object* v_d_6134_; lean_object* v_Q_6135_; lean_object* v_q_6136_; lean_object* v_w_6137_; lean_object* v_W_6138_; lean_object* v_E_6139_; lean_object* v_e_6140_; lean_object* v_c_6141_; lean_object* v_F_6142_; lean_object* v_a_6143_; lean_object* v_b_6144_; lean_object* v_B_6145_; lean_object* v_h_6146_; lean_object* v_K_6147_; lean_object* v_k_6148_; lean_object* v_H_6149_; lean_object* v_m_6150_; lean_object* v_s_6151_; lean_object* v_S_6152_; lean_object* v_A_6153_; lean_object* v_n_6154_; lean_object* v_N_6155_; lean_object* v_V_6156_; lean_object* v_z_6157_; lean_object* v_zabbrev_6158_; lean_object* v_O_6159_; lean_object* v_X_6160_; lean_object* v_x_6161_; lean_object* v_Z_6162_; lean_object* v___x_6164_; uint8_t v_isShared_6165_; uint8_t v_isSharedCheck_6170_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_G_6127_ = lean_ctor_get(v_date_4515_, 0);
v_y_6128_ = lean_ctor_get(v_date_4515_, 1);
v_u_6129_ = lean_ctor_get(v_date_4515_, 2);
v_Y_6130_ = lean_ctor_get(v_date_4515_, 3);
v_D_6131_ = lean_ctor_get(v_date_4515_, 4);
v_M_6132_ = lean_ctor_get(v_date_4515_, 5);
v_L_6133_ = lean_ctor_get(v_date_4515_, 6);
v_d_6134_ = lean_ctor_get(v_date_4515_, 7);
v_Q_6135_ = lean_ctor_get(v_date_4515_, 8);
v_q_6136_ = lean_ctor_get(v_date_4515_, 9);
v_w_6137_ = lean_ctor_get(v_date_4515_, 10);
v_W_6138_ = lean_ctor_get(v_date_4515_, 11);
v_E_6139_ = lean_ctor_get(v_date_4515_, 12);
v_e_6140_ = lean_ctor_get(v_date_4515_, 13);
v_c_6141_ = lean_ctor_get(v_date_4515_, 14);
v_F_6142_ = lean_ctor_get(v_date_4515_, 15);
v_a_6143_ = lean_ctor_get(v_date_4515_, 16);
v_b_6144_ = lean_ctor_get(v_date_4515_, 17);
v_B_6145_ = lean_ctor_get(v_date_4515_, 18);
v_h_6146_ = lean_ctor_get(v_date_4515_, 19);
v_K_6147_ = lean_ctor_get(v_date_4515_, 20);
v_k_6148_ = lean_ctor_get(v_date_4515_, 21);
v_H_6149_ = lean_ctor_get(v_date_4515_, 22);
v_m_6150_ = lean_ctor_get(v_date_4515_, 23);
v_s_6151_ = lean_ctor_get(v_date_4515_, 24);
v_S_6152_ = lean_ctor_get(v_date_4515_, 25);
v_A_6153_ = lean_ctor_get(v_date_4515_, 26);
v_n_6154_ = lean_ctor_get(v_date_4515_, 27);
v_N_6155_ = lean_ctor_get(v_date_4515_, 28);
v_V_6156_ = lean_ctor_get(v_date_4515_, 29);
v_z_6157_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_6158_ = lean_ctor_get(v_date_4515_, 31);
v_O_6159_ = lean_ctor_get(v_date_4515_, 33);
v_X_6160_ = lean_ctor_get(v_date_4515_, 34);
v_x_6161_ = lean_ctor_get(v_date_4515_, 35);
v_Z_6162_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_6170_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_6170_ == 0)
{
lean_object* v_unused_6171_; 
v_unused_6171_ = lean_ctor_get(v_date_4515_, 32);
lean_dec(v_unused_6171_);
v___x_6164_ = v_date_4515_;
v_isShared_6165_ = v_isSharedCheck_6170_;
goto v_resetjp_6163_;
}
else
{
lean_inc(v_Z_6162_);
lean_inc(v_x_6161_);
lean_inc(v_X_6160_);
lean_inc(v_O_6159_);
lean_inc(v_zabbrev_6158_);
lean_inc(v_z_6157_);
lean_inc(v_V_6156_);
lean_inc(v_N_6155_);
lean_inc(v_n_6154_);
lean_inc(v_A_6153_);
lean_inc(v_S_6152_);
lean_inc(v_s_6151_);
lean_inc(v_m_6150_);
lean_inc(v_H_6149_);
lean_inc(v_k_6148_);
lean_inc(v_K_6147_);
lean_inc(v_h_6146_);
lean_inc(v_B_6145_);
lean_inc(v_b_6144_);
lean_inc(v_a_6143_);
lean_inc(v_F_6142_);
lean_inc(v_c_6141_);
lean_inc(v_e_6140_);
lean_inc(v_E_6139_);
lean_inc(v_W_6138_);
lean_inc(v_w_6137_);
lean_inc(v_q_6136_);
lean_inc(v_Q_6135_);
lean_inc(v_d_6134_);
lean_inc(v_L_6133_);
lean_inc(v_M_6132_);
lean_inc(v_D_6131_);
lean_inc(v_Y_6130_);
lean_inc(v_u_6129_);
lean_inc(v_y_6128_);
lean_inc(v_G_6127_);
lean_dec(v_date_4515_);
v___x_6164_ = lean_box(0);
v_isShared_6165_ = v_isSharedCheck_6170_;
goto v_resetjp_6163_;
}
v_resetjp_6163_:
{
lean_object* v___x_6166_; lean_object* v___x_6168_; 
v___x_6166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6166_, 0, v_data_4517_);
if (v_isShared_6165_ == 0)
{
lean_ctor_set(v___x_6164_, 32, v___x_6166_);
v___x_6168_ = v___x_6164_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v_G_6127_);
lean_ctor_set(v_reuseFailAlloc_6169_, 1, v_y_6128_);
lean_ctor_set(v_reuseFailAlloc_6169_, 2, v_u_6129_);
lean_ctor_set(v_reuseFailAlloc_6169_, 3, v_Y_6130_);
lean_ctor_set(v_reuseFailAlloc_6169_, 4, v_D_6131_);
lean_ctor_set(v_reuseFailAlloc_6169_, 5, v_M_6132_);
lean_ctor_set(v_reuseFailAlloc_6169_, 6, v_L_6133_);
lean_ctor_set(v_reuseFailAlloc_6169_, 7, v_d_6134_);
lean_ctor_set(v_reuseFailAlloc_6169_, 8, v_Q_6135_);
lean_ctor_set(v_reuseFailAlloc_6169_, 9, v_q_6136_);
lean_ctor_set(v_reuseFailAlloc_6169_, 10, v_w_6137_);
lean_ctor_set(v_reuseFailAlloc_6169_, 11, v_W_6138_);
lean_ctor_set(v_reuseFailAlloc_6169_, 12, v_E_6139_);
lean_ctor_set(v_reuseFailAlloc_6169_, 13, v_e_6140_);
lean_ctor_set(v_reuseFailAlloc_6169_, 14, v_c_6141_);
lean_ctor_set(v_reuseFailAlloc_6169_, 15, v_F_6142_);
lean_ctor_set(v_reuseFailAlloc_6169_, 16, v_a_6143_);
lean_ctor_set(v_reuseFailAlloc_6169_, 17, v_b_6144_);
lean_ctor_set(v_reuseFailAlloc_6169_, 18, v_B_6145_);
lean_ctor_set(v_reuseFailAlloc_6169_, 19, v_h_6146_);
lean_ctor_set(v_reuseFailAlloc_6169_, 20, v_K_6147_);
lean_ctor_set(v_reuseFailAlloc_6169_, 21, v_k_6148_);
lean_ctor_set(v_reuseFailAlloc_6169_, 22, v_H_6149_);
lean_ctor_set(v_reuseFailAlloc_6169_, 23, v_m_6150_);
lean_ctor_set(v_reuseFailAlloc_6169_, 24, v_s_6151_);
lean_ctor_set(v_reuseFailAlloc_6169_, 25, v_S_6152_);
lean_ctor_set(v_reuseFailAlloc_6169_, 26, v_A_6153_);
lean_ctor_set(v_reuseFailAlloc_6169_, 27, v_n_6154_);
lean_ctor_set(v_reuseFailAlloc_6169_, 28, v_N_6155_);
lean_ctor_set(v_reuseFailAlloc_6169_, 29, v_V_6156_);
lean_ctor_set(v_reuseFailAlloc_6169_, 30, v_z_6157_);
lean_ctor_set(v_reuseFailAlloc_6169_, 31, v_zabbrev_6158_);
lean_ctor_set(v_reuseFailAlloc_6169_, 32, v___x_6166_);
lean_ctor_set(v_reuseFailAlloc_6169_, 33, v_O_6159_);
lean_ctor_set(v_reuseFailAlloc_6169_, 34, v_X_6160_);
lean_ctor_set(v_reuseFailAlloc_6169_, 35, v_x_6161_);
lean_ctor_set(v_reuseFailAlloc_6169_, 36, v_Z_6162_);
v___x_6168_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
return v___x_6168_;
}
}
}
case 32:
{
lean_object* v_G_6172_; lean_object* v_y_6173_; lean_object* v_u_6174_; lean_object* v_Y_6175_; lean_object* v_D_6176_; lean_object* v_M_6177_; lean_object* v_L_6178_; lean_object* v_d_6179_; lean_object* v_Q_6180_; lean_object* v_q_6181_; lean_object* v_w_6182_; lean_object* v_W_6183_; lean_object* v_E_6184_; lean_object* v_e_6185_; lean_object* v_c_6186_; lean_object* v_F_6187_; lean_object* v_a_6188_; lean_object* v_b_6189_; lean_object* v_B_6190_; lean_object* v_h_6191_; lean_object* v_K_6192_; lean_object* v_k_6193_; lean_object* v_H_6194_; lean_object* v_m_6195_; lean_object* v_s_6196_; lean_object* v_S_6197_; lean_object* v_A_6198_; lean_object* v_n_6199_; lean_object* v_N_6200_; lean_object* v_V_6201_; lean_object* v_z_6202_; lean_object* v_zabbrev_6203_; lean_object* v_v_6204_; lean_object* v_X_6205_; lean_object* v_x_6206_; lean_object* v_Z_6207_; lean_object* v___x_6209_; uint8_t v_isShared_6210_; uint8_t v_isSharedCheck_6215_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_G_6172_ = lean_ctor_get(v_date_4515_, 0);
v_y_6173_ = lean_ctor_get(v_date_4515_, 1);
v_u_6174_ = lean_ctor_get(v_date_4515_, 2);
v_Y_6175_ = lean_ctor_get(v_date_4515_, 3);
v_D_6176_ = lean_ctor_get(v_date_4515_, 4);
v_M_6177_ = lean_ctor_get(v_date_4515_, 5);
v_L_6178_ = lean_ctor_get(v_date_4515_, 6);
v_d_6179_ = lean_ctor_get(v_date_4515_, 7);
v_Q_6180_ = lean_ctor_get(v_date_4515_, 8);
v_q_6181_ = lean_ctor_get(v_date_4515_, 9);
v_w_6182_ = lean_ctor_get(v_date_4515_, 10);
v_W_6183_ = lean_ctor_get(v_date_4515_, 11);
v_E_6184_ = lean_ctor_get(v_date_4515_, 12);
v_e_6185_ = lean_ctor_get(v_date_4515_, 13);
v_c_6186_ = lean_ctor_get(v_date_4515_, 14);
v_F_6187_ = lean_ctor_get(v_date_4515_, 15);
v_a_6188_ = lean_ctor_get(v_date_4515_, 16);
v_b_6189_ = lean_ctor_get(v_date_4515_, 17);
v_B_6190_ = lean_ctor_get(v_date_4515_, 18);
v_h_6191_ = lean_ctor_get(v_date_4515_, 19);
v_K_6192_ = lean_ctor_get(v_date_4515_, 20);
v_k_6193_ = lean_ctor_get(v_date_4515_, 21);
v_H_6194_ = lean_ctor_get(v_date_4515_, 22);
v_m_6195_ = lean_ctor_get(v_date_4515_, 23);
v_s_6196_ = lean_ctor_get(v_date_4515_, 24);
v_S_6197_ = lean_ctor_get(v_date_4515_, 25);
v_A_6198_ = lean_ctor_get(v_date_4515_, 26);
v_n_6199_ = lean_ctor_get(v_date_4515_, 27);
v_N_6200_ = lean_ctor_get(v_date_4515_, 28);
v_V_6201_ = lean_ctor_get(v_date_4515_, 29);
v_z_6202_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_6203_ = lean_ctor_get(v_date_4515_, 31);
v_v_6204_ = lean_ctor_get(v_date_4515_, 32);
v_X_6205_ = lean_ctor_get(v_date_4515_, 34);
v_x_6206_ = lean_ctor_get(v_date_4515_, 35);
v_Z_6207_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_6215_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_6215_ == 0)
{
lean_object* v_unused_6216_; 
v_unused_6216_ = lean_ctor_get(v_date_4515_, 33);
lean_dec(v_unused_6216_);
v___x_6209_ = v_date_4515_;
v_isShared_6210_ = v_isSharedCheck_6215_;
goto v_resetjp_6208_;
}
else
{
lean_inc(v_Z_6207_);
lean_inc(v_x_6206_);
lean_inc(v_X_6205_);
lean_inc(v_v_6204_);
lean_inc(v_zabbrev_6203_);
lean_inc(v_z_6202_);
lean_inc(v_V_6201_);
lean_inc(v_N_6200_);
lean_inc(v_n_6199_);
lean_inc(v_A_6198_);
lean_inc(v_S_6197_);
lean_inc(v_s_6196_);
lean_inc(v_m_6195_);
lean_inc(v_H_6194_);
lean_inc(v_k_6193_);
lean_inc(v_K_6192_);
lean_inc(v_h_6191_);
lean_inc(v_B_6190_);
lean_inc(v_b_6189_);
lean_inc(v_a_6188_);
lean_inc(v_F_6187_);
lean_inc(v_c_6186_);
lean_inc(v_e_6185_);
lean_inc(v_E_6184_);
lean_inc(v_W_6183_);
lean_inc(v_w_6182_);
lean_inc(v_q_6181_);
lean_inc(v_Q_6180_);
lean_inc(v_d_6179_);
lean_inc(v_L_6178_);
lean_inc(v_M_6177_);
lean_inc(v_D_6176_);
lean_inc(v_Y_6175_);
lean_inc(v_u_6174_);
lean_inc(v_y_6173_);
lean_inc(v_G_6172_);
lean_dec(v_date_4515_);
v___x_6209_ = lean_box(0);
v_isShared_6210_ = v_isSharedCheck_6215_;
goto v_resetjp_6208_;
}
v_resetjp_6208_:
{
lean_object* v___x_6211_; lean_object* v___x_6213_; 
v___x_6211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6211_, 0, v_data_4517_);
if (v_isShared_6210_ == 0)
{
lean_ctor_set(v___x_6209_, 33, v___x_6211_);
v___x_6213_ = v___x_6209_;
goto v_reusejp_6212_;
}
else
{
lean_object* v_reuseFailAlloc_6214_; 
v_reuseFailAlloc_6214_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6214_, 0, v_G_6172_);
lean_ctor_set(v_reuseFailAlloc_6214_, 1, v_y_6173_);
lean_ctor_set(v_reuseFailAlloc_6214_, 2, v_u_6174_);
lean_ctor_set(v_reuseFailAlloc_6214_, 3, v_Y_6175_);
lean_ctor_set(v_reuseFailAlloc_6214_, 4, v_D_6176_);
lean_ctor_set(v_reuseFailAlloc_6214_, 5, v_M_6177_);
lean_ctor_set(v_reuseFailAlloc_6214_, 6, v_L_6178_);
lean_ctor_set(v_reuseFailAlloc_6214_, 7, v_d_6179_);
lean_ctor_set(v_reuseFailAlloc_6214_, 8, v_Q_6180_);
lean_ctor_set(v_reuseFailAlloc_6214_, 9, v_q_6181_);
lean_ctor_set(v_reuseFailAlloc_6214_, 10, v_w_6182_);
lean_ctor_set(v_reuseFailAlloc_6214_, 11, v_W_6183_);
lean_ctor_set(v_reuseFailAlloc_6214_, 12, v_E_6184_);
lean_ctor_set(v_reuseFailAlloc_6214_, 13, v_e_6185_);
lean_ctor_set(v_reuseFailAlloc_6214_, 14, v_c_6186_);
lean_ctor_set(v_reuseFailAlloc_6214_, 15, v_F_6187_);
lean_ctor_set(v_reuseFailAlloc_6214_, 16, v_a_6188_);
lean_ctor_set(v_reuseFailAlloc_6214_, 17, v_b_6189_);
lean_ctor_set(v_reuseFailAlloc_6214_, 18, v_B_6190_);
lean_ctor_set(v_reuseFailAlloc_6214_, 19, v_h_6191_);
lean_ctor_set(v_reuseFailAlloc_6214_, 20, v_K_6192_);
lean_ctor_set(v_reuseFailAlloc_6214_, 21, v_k_6193_);
lean_ctor_set(v_reuseFailAlloc_6214_, 22, v_H_6194_);
lean_ctor_set(v_reuseFailAlloc_6214_, 23, v_m_6195_);
lean_ctor_set(v_reuseFailAlloc_6214_, 24, v_s_6196_);
lean_ctor_set(v_reuseFailAlloc_6214_, 25, v_S_6197_);
lean_ctor_set(v_reuseFailAlloc_6214_, 26, v_A_6198_);
lean_ctor_set(v_reuseFailAlloc_6214_, 27, v_n_6199_);
lean_ctor_set(v_reuseFailAlloc_6214_, 28, v_N_6200_);
lean_ctor_set(v_reuseFailAlloc_6214_, 29, v_V_6201_);
lean_ctor_set(v_reuseFailAlloc_6214_, 30, v_z_6202_);
lean_ctor_set(v_reuseFailAlloc_6214_, 31, v_zabbrev_6203_);
lean_ctor_set(v_reuseFailAlloc_6214_, 32, v_v_6204_);
lean_ctor_set(v_reuseFailAlloc_6214_, 33, v___x_6211_);
lean_ctor_set(v_reuseFailAlloc_6214_, 34, v_X_6205_);
lean_ctor_set(v_reuseFailAlloc_6214_, 35, v_x_6206_);
lean_ctor_set(v_reuseFailAlloc_6214_, 36, v_Z_6207_);
v___x_6213_ = v_reuseFailAlloc_6214_;
goto v_reusejp_6212_;
}
v_reusejp_6212_:
{
return v___x_6213_;
}
}
}
case 33:
{
lean_object* v_G_6217_; lean_object* v_y_6218_; lean_object* v_u_6219_; lean_object* v_Y_6220_; lean_object* v_D_6221_; lean_object* v_M_6222_; lean_object* v_L_6223_; lean_object* v_d_6224_; lean_object* v_Q_6225_; lean_object* v_q_6226_; lean_object* v_w_6227_; lean_object* v_W_6228_; lean_object* v_E_6229_; lean_object* v_e_6230_; lean_object* v_c_6231_; lean_object* v_F_6232_; lean_object* v_a_6233_; lean_object* v_b_6234_; lean_object* v_B_6235_; lean_object* v_h_6236_; lean_object* v_K_6237_; lean_object* v_k_6238_; lean_object* v_H_6239_; lean_object* v_m_6240_; lean_object* v_s_6241_; lean_object* v_S_6242_; lean_object* v_A_6243_; lean_object* v_n_6244_; lean_object* v_N_6245_; lean_object* v_V_6246_; lean_object* v_z_6247_; lean_object* v_zabbrev_6248_; lean_object* v_v_6249_; lean_object* v_O_6250_; lean_object* v_x_6251_; lean_object* v_Z_6252_; lean_object* v___x_6254_; uint8_t v_isShared_6255_; uint8_t v_isSharedCheck_6260_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_G_6217_ = lean_ctor_get(v_date_4515_, 0);
v_y_6218_ = lean_ctor_get(v_date_4515_, 1);
v_u_6219_ = lean_ctor_get(v_date_4515_, 2);
v_Y_6220_ = lean_ctor_get(v_date_4515_, 3);
v_D_6221_ = lean_ctor_get(v_date_4515_, 4);
v_M_6222_ = lean_ctor_get(v_date_4515_, 5);
v_L_6223_ = lean_ctor_get(v_date_4515_, 6);
v_d_6224_ = lean_ctor_get(v_date_4515_, 7);
v_Q_6225_ = lean_ctor_get(v_date_4515_, 8);
v_q_6226_ = lean_ctor_get(v_date_4515_, 9);
v_w_6227_ = lean_ctor_get(v_date_4515_, 10);
v_W_6228_ = lean_ctor_get(v_date_4515_, 11);
v_E_6229_ = lean_ctor_get(v_date_4515_, 12);
v_e_6230_ = lean_ctor_get(v_date_4515_, 13);
v_c_6231_ = lean_ctor_get(v_date_4515_, 14);
v_F_6232_ = lean_ctor_get(v_date_4515_, 15);
v_a_6233_ = lean_ctor_get(v_date_4515_, 16);
v_b_6234_ = lean_ctor_get(v_date_4515_, 17);
v_B_6235_ = lean_ctor_get(v_date_4515_, 18);
v_h_6236_ = lean_ctor_get(v_date_4515_, 19);
v_K_6237_ = lean_ctor_get(v_date_4515_, 20);
v_k_6238_ = lean_ctor_get(v_date_4515_, 21);
v_H_6239_ = lean_ctor_get(v_date_4515_, 22);
v_m_6240_ = lean_ctor_get(v_date_4515_, 23);
v_s_6241_ = lean_ctor_get(v_date_4515_, 24);
v_S_6242_ = lean_ctor_get(v_date_4515_, 25);
v_A_6243_ = lean_ctor_get(v_date_4515_, 26);
v_n_6244_ = lean_ctor_get(v_date_4515_, 27);
v_N_6245_ = lean_ctor_get(v_date_4515_, 28);
v_V_6246_ = lean_ctor_get(v_date_4515_, 29);
v_z_6247_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_6248_ = lean_ctor_get(v_date_4515_, 31);
v_v_6249_ = lean_ctor_get(v_date_4515_, 32);
v_O_6250_ = lean_ctor_get(v_date_4515_, 33);
v_x_6251_ = lean_ctor_get(v_date_4515_, 35);
v_Z_6252_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_6260_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_6260_ == 0)
{
lean_object* v_unused_6261_; 
v_unused_6261_ = lean_ctor_get(v_date_4515_, 34);
lean_dec(v_unused_6261_);
v___x_6254_ = v_date_4515_;
v_isShared_6255_ = v_isSharedCheck_6260_;
goto v_resetjp_6253_;
}
else
{
lean_inc(v_Z_6252_);
lean_inc(v_x_6251_);
lean_inc(v_O_6250_);
lean_inc(v_v_6249_);
lean_inc(v_zabbrev_6248_);
lean_inc(v_z_6247_);
lean_inc(v_V_6246_);
lean_inc(v_N_6245_);
lean_inc(v_n_6244_);
lean_inc(v_A_6243_);
lean_inc(v_S_6242_);
lean_inc(v_s_6241_);
lean_inc(v_m_6240_);
lean_inc(v_H_6239_);
lean_inc(v_k_6238_);
lean_inc(v_K_6237_);
lean_inc(v_h_6236_);
lean_inc(v_B_6235_);
lean_inc(v_b_6234_);
lean_inc(v_a_6233_);
lean_inc(v_F_6232_);
lean_inc(v_c_6231_);
lean_inc(v_e_6230_);
lean_inc(v_E_6229_);
lean_inc(v_W_6228_);
lean_inc(v_w_6227_);
lean_inc(v_q_6226_);
lean_inc(v_Q_6225_);
lean_inc(v_d_6224_);
lean_inc(v_L_6223_);
lean_inc(v_M_6222_);
lean_inc(v_D_6221_);
lean_inc(v_Y_6220_);
lean_inc(v_u_6219_);
lean_inc(v_y_6218_);
lean_inc(v_G_6217_);
lean_dec(v_date_4515_);
v___x_6254_ = lean_box(0);
v_isShared_6255_ = v_isSharedCheck_6260_;
goto v_resetjp_6253_;
}
v_resetjp_6253_:
{
lean_object* v___x_6256_; lean_object* v___x_6258_; 
v___x_6256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6256_, 0, v_data_4517_);
if (v_isShared_6255_ == 0)
{
lean_ctor_set(v___x_6254_, 34, v___x_6256_);
v___x_6258_ = v___x_6254_;
goto v_reusejp_6257_;
}
else
{
lean_object* v_reuseFailAlloc_6259_; 
v_reuseFailAlloc_6259_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6259_, 0, v_G_6217_);
lean_ctor_set(v_reuseFailAlloc_6259_, 1, v_y_6218_);
lean_ctor_set(v_reuseFailAlloc_6259_, 2, v_u_6219_);
lean_ctor_set(v_reuseFailAlloc_6259_, 3, v_Y_6220_);
lean_ctor_set(v_reuseFailAlloc_6259_, 4, v_D_6221_);
lean_ctor_set(v_reuseFailAlloc_6259_, 5, v_M_6222_);
lean_ctor_set(v_reuseFailAlloc_6259_, 6, v_L_6223_);
lean_ctor_set(v_reuseFailAlloc_6259_, 7, v_d_6224_);
lean_ctor_set(v_reuseFailAlloc_6259_, 8, v_Q_6225_);
lean_ctor_set(v_reuseFailAlloc_6259_, 9, v_q_6226_);
lean_ctor_set(v_reuseFailAlloc_6259_, 10, v_w_6227_);
lean_ctor_set(v_reuseFailAlloc_6259_, 11, v_W_6228_);
lean_ctor_set(v_reuseFailAlloc_6259_, 12, v_E_6229_);
lean_ctor_set(v_reuseFailAlloc_6259_, 13, v_e_6230_);
lean_ctor_set(v_reuseFailAlloc_6259_, 14, v_c_6231_);
lean_ctor_set(v_reuseFailAlloc_6259_, 15, v_F_6232_);
lean_ctor_set(v_reuseFailAlloc_6259_, 16, v_a_6233_);
lean_ctor_set(v_reuseFailAlloc_6259_, 17, v_b_6234_);
lean_ctor_set(v_reuseFailAlloc_6259_, 18, v_B_6235_);
lean_ctor_set(v_reuseFailAlloc_6259_, 19, v_h_6236_);
lean_ctor_set(v_reuseFailAlloc_6259_, 20, v_K_6237_);
lean_ctor_set(v_reuseFailAlloc_6259_, 21, v_k_6238_);
lean_ctor_set(v_reuseFailAlloc_6259_, 22, v_H_6239_);
lean_ctor_set(v_reuseFailAlloc_6259_, 23, v_m_6240_);
lean_ctor_set(v_reuseFailAlloc_6259_, 24, v_s_6241_);
lean_ctor_set(v_reuseFailAlloc_6259_, 25, v_S_6242_);
lean_ctor_set(v_reuseFailAlloc_6259_, 26, v_A_6243_);
lean_ctor_set(v_reuseFailAlloc_6259_, 27, v_n_6244_);
lean_ctor_set(v_reuseFailAlloc_6259_, 28, v_N_6245_);
lean_ctor_set(v_reuseFailAlloc_6259_, 29, v_V_6246_);
lean_ctor_set(v_reuseFailAlloc_6259_, 30, v_z_6247_);
lean_ctor_set(v_reuseFailAlloc_6259_, 31, v_zabbrev_6248_);
lean_ctor_set(v_reuseFailAlloc_6259_, 32, v_v_6249_);
lean_ctor_set(v_reuseFailAlloc_6259_, 33, v_O_6250_);
lean_ctor_set(v_reuseFailAlloc_6259_, 34, v___x_6256_);
lean_ctor_set(v_reuseFailAlloc_6259_, 35, v_x_6251_);
lean_ctor_set(v_reuseFailAlloc_6259_, 36, v_Z_6252_);
v___x_6258_ = v_reuseFailAlloc_6259_;
goto v_reusejp_6257_;
}
v_reusejp_6257_:
{
return v___x_6258_;
}
}
}
case 34:
{
lean_object* v_G_6262_; lean_object* v_y_6263_; lean_object* v_u_6264_; lean_object* v_Y_6265_; lean_object* v_D_6266_; lean_object* v_M_6267_; lean_object* v_L_6268_; lean_object* v_d_6269_; lean_object* v_Q_6270_; lean_object* v_q_6271_; lean_object* v_w_6272_; lean_object* v_W_6273_; lean_object* v_E_6274_; lean_object* v_e_6275_; lean_object* v_c_6276_; lean_object* v_F_6277_; lean_object* v_a_6278_; lean_object* v_b_6279_; lean_object* v_B_6280_; lean_object* v_h_6281_; lean_object* v_K_6282_; lean_object* v_k_6283_; lean_object* v_H_6284_; lean_object* v_m_6285_; lean_object* v_s_6286_; lean_object* v_S_6287_; lean_object* v_A_6288_; lean_object* v_n_6289_; lean_object* v_N_6290_; lean_object* v_V_6291_; lean_object* v_z_6292_; lean_object* v_zabbrev_6293_; lean_object* v_v_6294_; lean_object* v_O_6295_; lean_object* v_X_6296_; lean_object* v_Z_6297_; lean_object* v___x_6299_; uint8_t v_isShared_6300_; uint8_t v_isSharedCheck_6305_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_G_6262_ = lean_ctor_get(v_date_4515_, 0);
v_y_6263_ = lean_ctor_get(v_date_4515_, 1);
v_u_6264_ = lean_ctor_get(v_date_4515_, 2);
v_Y_6265_ = lean_ctor_get(v_date_4515_, 3);
v_D_6266_ = lean_ctor_get(v_date_4515_, 4);
v_M_6267_ = lean_ctor_get(v_date_4515_, 5);
v_L_6268_ = lean_ctor_get(v_date_4515_, 6);
v_d_6269_ = lean_ctor_get(v_date_4515_, 7);
v_Q_6270_ = lean_ctor_get(v_date_4515_, 8);
v_q_6271_ = lean_ctor_get(v_date_4515_, 9);
v_w_6272_ = lean_ctor_get(v_date_4515_, 10);
v_W_6273_ = lean_ctor_get(v_date_4515_, 11);
v_E_6274_ = lean_ctor_get(v_date_4515_, 12);
v_e_6275_ = lean_ctor_get(v_date_4515_, 13);
v_c_6276_ = lean_ctor_get(v_date_4515_, 14);
v_F_6277_ = lean_ctor_get(v_date_4515_, 15);
v_a_6278_ = lean_ctor_get(v_date_4515_, 16);
v_b_6279_ = lean_ctor_get(v_date_4515_, 17);
v_B_6280_ = lean_ctor_get(v_date_4515_, 18);
v_h_6281_ = lean_ctor_get(v_date_4515_, 19);
v_K_6282_ = lean_ctor_get(v_date_4515_, 20);
v_k_6283_ = lean_ctor_get(v_date_4515_, 21);
v_H_6284_ = lean_ctor_get(v_date_4515_, 22);
v_m_6285_ = lean_ctor_get(v_date_4515_, 23);
v_s_6286_ = lean_ctor_get(v_date_4515_, 24);
v_S_6287_ = lean_ctor_get(v_date_4515_, 25);
v_A_6288_ = lean_ctor_get(v_date_4515_, 26);
v_n_6289_ = lean_ctor_get(v_date_4515_, 27);
v_N_6290_ = lean_ctor_get(v_date_4515_, 28);
v_V_6291_ = lean_ctor_get(v_date_4515_, 29);
v_z_6292_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_6293_ = lean_ctor_get(v_date_4515_, 31);
v_v_6294_ = lean_ctor_get(v_date_4515_, 32);
v_O_6295_ = lean_ctor_get(v_date_4515_, 33);
v_X_6296_ = lean_ctor_get(v_date_4515_, 34);
v_Z_6297_ = lean_ctor_get(v_date_4515_, 36);
v_isSharedCheck_6305_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_6305_ == 0)
{
lean_object* v_unused_6306_; 
v_unused_6306_ = lean_ctor_get(v_date_4515_, 35);
lean_dec(v_unused_6306_);
v___x_6299_ = v_date_4515_;
v_isShared_6300_ = v_isSharedCheck_6305_;
goto v_resetjp_6298_;
}
else
{
lean_inc(v_Z_6297_);
lean_inc(v_X_6296_);
lean_inc(v_O_6295_);
lean_inc(v_v_6294_);
lean_inc(v_zabbrev_6293_);
lean_inc(v_z_6292_);
lean_inc(v_V_6291_);
lean_inc(v_N_6290_);
lean_inc(v_n_6289_);
lean_inc(v_A_6288_);
lean_inc(v_S_6287_);
lean_inc(v_s_6286_);
lean_inc(v_m_6285_);
lean_inc(v_H_6284_);
lean_inc(v_k_6283_);
lean_inc(v_K_6282_);
lean_inc(v_h_6281_);
lean_inc(v_B_6280_);
lean_inc(v_b_6279_);
lean_inc(v_a_6278_);
lean_inc(v_F_6277_);
lean_inc(v_c_6276_);
lean_inc(v_e_6275_);
lean_inc(v_E_6274_);
lean_inc(v_W_6273_);
lean_inc(v_w_6272_);
lean_inc(v_q_6271_);
lean_inc(v_Q_6270_);
lean_inc(v_d_6269_);
lean_inc(v_L_6268_);
lean_inc(v_M_6267_);
lean_inc(v_D_6266_);
lean_inc(v_Y_6265_);
lean_inc(v_u_6264_);
lean_inc(v_y_6263_);
lean_inc(v_G_6262_);
lean_dec(v_date_4515_);
v___x_6299_ = lean_box(0);
v_isShared_6300_ = v_isSharedCheck_6305_;
goto v_resetjp_6298_;
}
v_resetjp_6298_:
{
lean_object* v___x_6301_; lean_object* v___x_6303_; 
v___x_6301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6301_, 0, v_data_4517_);
if (v_isShared_6300_ == 0)
{
lean_ctor_set(v___x_6299_, 35, v___x_6301_);
v___x_6303_ = v___x_6299_;
goto v_reusejp_6302_;
}
else
{
lean_object* v_reuseFailAlloc_6304_; 
v_reuseFailAlloc_6304_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6304_, 0, v_G_6262_);
lean_ctor_set(v_reuseFailAlloc_6304_, 1, v_y_6263_);
lean_ctor_set(v_reuseFailAlloc_6304_, 2, v_u_6264_);
lean_ctor_set(v_reuseFailAlloc_6304_, 3, v_Y_6265_);
lean_ctor_set(v_reuseFailAlloc_6304_, 4, v_D_6266_);
lean_ctor_set(v_reuseFailAlloc_6304_, 5, v_M_6267_);
lean_ctor_set(v_reuseFailAlloc_6304_, 6, v_L_6268_);
lean_ctor_set(v_reuseFailAlloc_6304_, 7, v_d_6269_);
lean_ctor_set(v_reuseFailAlloc_6304_, 8, v_Q_6270_);
lean_ctor_set(v_reuseFailAlloc_6304_, 9, v_q_6271_);
lean_ctor_set(v_reuseFailAlloc_6304_, 10, v_w_6272_);
lean_ctor_set(v_reuseFailAlloc_6304_, 11, v_W_6273_);
lean_ctor_set(v_reuseFailAlloc_6304_, 12, v_E_6274_);
lean_ctor_set(v_reuseFailAlloc_6304_, 13, v_e_6275_);
lean_ctor_set(v_reuseFailAlloc_6304_, 14, v_c_6276_);
lean_ctor_set(v_reuseFailAlloc_6304_, 15, v_F_6277_);
lean_ctor_set(v_reuseFailAlloc_6304_, 16, v_a_6278_);
lean_ctor_set(v_reuseFailAlloc_6304_, 17, v_b_6279_);
lean_ctor_set(v_reuseFailAlloc_6304_, 18, v_B_6280_);
lean_ctor_set(v_reuseFailAlloc_6304_, 19, v_h_6281_);
lean_ctor_set(v_reuseFailAlloc_6304_, 20, v_K_6282_);
lean_ctor_set(v_reuseFailAlloc_6304_, 21, v_k_6283_);
lean_ctor_set(v_reuseFailAlloc_6304_, 22, v_H_6284_);
lean_ctor_set(v_reuseFailAlloc_6304_, 23, v_m_6285_);
lean_ctor_set(v_reuseFailAlloc_6304_, 24, v_s_6286_);
lean_ctor_set(v_reuseFailAlloc_6304_, 25, v_S_6287_);
lean_ctor_set(v_reuseFailAlloc_6304_, 26, v_A_6288_);
lean_ctor_set(v_reuseFailAlloc_6304_, 27, v_n_6289_);
lean_ctor_set(v_reuseFailAlloc_6304_, 28, v_N_6290_);
lean_ctor_set(v_reuseFailAlloc_6304_, 29, v_V_6291_);
lean_ctor_set(v_reuseFailAlloc_6304_, 30, v_z_6292_);
lean_ctor_set(v_reuseFailAlloc_6304_, 31, v_zabbrev_6293_);
lean_ctor_set(v_reuseFailAlloc_6304_, 32, v_v_6294_);
lean_ctor_set(v_reuseFailAlloc_6304_, 33, v_O_6295_);
lean_ctor_set(v_reuseFailAlloc_6304_, 34, v_X_6296_);
lean_ctor_set(v_reuseFailAlloc_6304_, 35, v___x_6301_);
lean_ctor_set(v_reuseFailAlloc_6304_, 36, v_Z_6297_);
v___x_6303_ = v_reuseFailAlloc_6304_;
goto v_reusejp_6302_;
}
v_reusejp_6302_:
{
return v___x_6303_;
}
}
}
default: 
{
lean_object* v_G_6307_; lean_object* v_y_6308_; lean_object* v_u_6309_; lean_object* v_Y_6310_; lean_object* v_D_6311_; lean_object* v_M_6312_; lean_object* v_L_6313_; lean_object* v_d_6314_; lean_object* v_Q_6315_; lean_object* v_q_6316_; lean_object* v_w_6317_; lean_object* v_W_6318_; lean_object* v_E_6319_; lean_object* v_e_6320_; lean_object* v_c_6321_; lean_object* v_F_6322_; lean_object* v_a_6323_; lean_object* v_b_6324_; lean_object* v_B_6325_; lean_object* v_h_6326_; lean_object* v_K_6327_; lean_object* v_k_6328_; lean_object* v_H_6329_; lean_object* v_m_6330_; lean_object* v_s_6331_; lean_object* v_S_6332_; lean_object* v_A_6333_; lean_object* v_n_6334_; lean_object* v_N_6335_; lean_object* v_V_6336_; lean_object* v_z_6337_; lean_object* v_zabbrev_6338_; lean_object* v_v_6339_; lean_object* v_O_6340_; lean_object* v_X_6341_; lean_object* v_x_6342_; lean_object* v___x_6344_; uint8_t v_isShared_6345_; uint8_t v_isSharedCheck_6350_; 
lean_dec_ref_known(v_modifier_4516_, 0);
v_G_6307_ = lean_ctor_get(v_date_4515_, 0);
v_y_6308_ = lean_ctor_get(v_date_4515_, 1);
v_u_6309_ = lean_ctor_get(v_date_4515_, 2);
v_Y_6310_ = lean_ctor_get(v_date_4515_, 3);
v_D_6311_ = lean_ctor_get(v_date_4515_, 4);
v_M_6312_ = lean_ctor_get(v_date_4515_, 5);
v_L_6313_ = lean_ctor_get(v_date_4515_, 6);
v_d_6314_ = lean_ctor_get(v_date_4515_, 7);
v_Q_6315_ = lean_ctor_get(v_date_4515_, 8);
v_q_6316_ = lean_ctor_get(v_date_4515_, 9);
v_w_6317_ = lean_ctor_get(v_date_4515_, 10);
v_W_6318_ = lean_ctor_get(v_date_4515_, 11);
v_E_6319_ = lean_ctor_get(v_date_4515_, 12);
v_e_6320_ = lean_ctor_get(v_date_4515_, 13);
v_c_6321_ = lean_ctor_get(v_date_4515_, 14);
v_F_6322_ = lean_ctor_get(v_date_4515_, 15);
v_a_6323_ = lean_ctor_get(v_date_4515_, 16);
v_b_6324_ = lean_ctor_get(v_date_4515_, 17);
v_B_6325_ = lean_ctor_get(v_date_4515_, 18);
v_h_6326_ = lean_ctor_get(v_date_4515_, 19);
v_K_6327_ = lean_ctor_get(v_date_4515_, 20);
v_k_6328_ = lean_ctor_get(v_date_4515_, 21);
v_H_6329_ = lean_ctor_get(v_date_4515_, 22);
v_m_6330_ = lean_ctor_get(v_date_4515_, 23);
v_s_6331_ = lean_ctor_get(v_date_4515_, 24);
v_S_6332_ = lean_ctor_get(v_date_4515_, 25);
v_A_6333_ = lean_ctor_get(v_date_4515_, 26);
v_n_6334_ = lean_ctor_get(v_date_4515_, 27);
v_N_6335_ = lean_ctor_get(v_date_4515_, 28);
v_V_6336_ = lean_ctor_get(v_date_4515_, 29);
v_z_6337_ = lean_ctor_get(v_date_4515_, 30);
v_zabbrev_6338_ = lean_ctor_get(v_date_4515_, 31);
v_v_6339_ = lean_ctor_get(v_date_4515_, 32);
v_O_6340_ = lean_ctor_get(v_date_4515_, 33);
v_X_6341_ = lean_ctor_get(v_date_4515_, 34);
v_x_6342_ = lean_ctor_get(v_date_4515_, 35);
v_isSharedCheck_6350_ = !lean_is_exclusive(v_date_4515_);
if (v_isSharedCheck_6350_ == 0)
{
lean_object* v_unused_6351_; 
v_unused_6351_ = lean_ctor_get(v_date_4515_, 36);
lean_dec(v_unused_6351_);
v___x_6344_ = v_date_4515_;
v_isShared_6345_ = v_isSharedCheck_6350_;
goto v_resetjp_6343_;
}
else
{
lean_inc(v_x_6342_);
lean_inc(v_X_6341_);
lean_inc(v_O_6340_);
lean_inc(v_v_6339_);
lean_inc(v_zabbrev_6338_);
lean_inc(v_z_6337_);
lean_inc(v_V_6336_);
lean_inc(v_N_6335_);
lean_inc(v_n_6334_);
lean_inc(v_A_6333_);
lean_inc(v_S_6332_);
lean_inc(v_s_6331_);
lean_inc(v_m_6330_);
lean_inc(v_H_6329_);
lean_inc(v_k_6328_);
lean_inc(v_K_6327_);
lean_inc(v_h_6326_);
lean_inc(v_B_6325_);
lean_inc(v_b_6324_);
lean_inc(v_a_6323_);
lean_inc(v_F_6322_);
lean_inc(v_c_6321_);
lean_inc(v_e_6320_);
lean_inc(v_E_6319_);
lean_inc(v_W_6318_);
lean_inc(v_w_6317_);
lean_inc(v_q_6316_);
lean_inc(v_Q_6315_);
lean_inc(v_d_6314_);
lean_inc(v_L_6313_);
lean_inc(v_M_6312_);
lean_inc(v_D_6311_);
lean_inc(v_Y_6310_);
lean_inc(v_u_6309_);
lean_inc(v_y_6308_);
lean_inc(v_G_6307_);
lean_dec(v_date_4515_);
v___x_6344_ = lean_box(0);
v_isShared_6345_ = v_isSharedCheck_6350_;
goto v_resetjp_6343_;
}
v_resetjp_6343_:
{
lean_object* v___x_6346_; lean_object* v___x_6348_; 
v___x_6346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6346_, 0, v_data_4517_);
if (v_isShared_6345_ == 0)
{
lean_ctor_set(v___x_6344_, 36, v___x_6346_);
v___x_6348_ = v___x_6344_;
goto v_reusejp_6347_;
}
else
{
lean_object* v_reuseFailAlloc_6349_; 
v_reuseFailAlloc_6349_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6349_, 0, v_G_6307_);
lean_ctor_set(v_reuseFailAlloc_6349_, 1, v_y_6308_);
lean_ctor_set(v_reuseFailAlloc_6349_, 2, v_u_6309_);
lean_ctor_set(v_reuseFailAlloc_6349_, 3, v_Y_6310_);
lean_ctor_set(v_reuseFailAlloc_6349_, 4, v_D_6311_);
lean_ctor_set(v_reuseFailAlloc_6349_, 5, v_M_6312_);
lean_ctor_set(v_reuseFailAlloc_6349_, 6, v_L_6313_);
lean_ctor_set(v_reuseFailAlloc_6349_, 7, v_d_6314_);
lean_ctor_set(v_reuseFailAlloc_6349_, 8, v_Q_6315_);
lean_ctor_set(v_reuseFailAlloc_6349_, 9, v_q_6316_);
lean_ctor_set(v_reuseFailAlloc_6349_, 10, v_w_6317_);
lean_ctor_set(v_reuseFailAlloc_6349_, 11, v_W_6318_);
lean_ctor_set(v_reuseFailAlloc_6349_, 12, v_E_6319_);
lean_ctor_set(v_reuseFailAlloc_6349_, 13, v_e_6320_);
lean_ctor_set(v_reuseFailAlloc_6349_, 14, v_c_6321_);
lean_ctor_set(v_reuseFailAlloc_6349_, 15, v_F_6322_);
lean_ctor_set(v_reuseFailAlloc_6349_, 16, v_a_6323_);
lean_ctor_set(v_reuseFailAlloc_6349_, 17, v_b_6324_);
lean_ctor_set(v_reuseFailAlloc_6349_, 18, v_B_6325_);
lean_ctor_set(v_reuseFailAlloc_6349_, 19, v_h_6326_);
lean_ctor_set(v_reuseFailAlloc_6349_, 20, v_K_6327_);
lean_ctor_set(v_reuseFailAlloc_6349_, 21, v_k_6328_);
lean_ctor_set(v_reuseFailAlloc_6349_, 22, v_H_6329_);
lean_ctor_set(v_reuseFailAlloc_6349_, 23, v_m_6330_);
lean_ctor_set(v_reuseFailAlloc_6349_, 24, v_s_6331_);
lean_ctor_set(v_reuseFailAlloc_6349_, 25, v_S_6332_);
lean_ctor_set(v_reuseFailAlloc_6349_, 26, v_A_6333_);
lean_ctor_set(v_reuseFailAlloc_6349_, 27, v_n_6334_);
lean_ctor_set(v_reuseFailAlloc_6349_, 28, v_N_6335_);
lean_ctor_set(v_reuseFailAlloc_6349_, 29, v_V_6336_);
lean_ctor_set(v_reuseFailAlloc_6349_, 30, v_z_6337_);
lean_ctor_set(v_reuseFailAlloc_6349_, 31, v_zabbrev_6338_);
lean_ctor_set(v_reuseFailAlloc_6349_, 32, v_v_6339_);
lean_ctor_set(v_reuseFailAlloc_6349_, 33, v_O_6340_);
lean_ctor_set(v_reuseFailAlloc_6349_, 34, v_X_6341_);
lean_ctor_set(v_reuseFailAlloc_6349_, 35, v_x_6342_);
lean_ctor_set(v_reuseFailAlloc_6349_, 36, v___x_6346_);
v___x_6348_ = v_reuseFailAlloc_6349_;
goto v_reusejp_6347_;
}
v_reusejp_6347_:
{
return v___x_6348_;
}
}
}
}
}
}
lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object* v_year_6352_, uint8_t v_x_6353_){
_start:
{
if (v_x_6353_ == 0)
{
lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; 
v___x_6354_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6355_ = lean_int_add(v_year_6352_, v___x_6354_);
v___x_6356_ = lean_int_neg(v___x_6355_);
lean_dec(v___x_6355_);
return v___x_6356_;
}
else
{
lean_inc(v_year_6352_);
return v_year_6352_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra_0interp(lean_interpreter_value* stack)
{
lean_object* v_year_6352_ = stack[0].m_obj;
uint8_t v_x_6353_ = stack[1].m_num;
lean_object* v_res_6357_;
v_res_6357_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6352_, v_x_6353_);
stack->m_obj
 = v_res_6357_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object* v_year_6358_, lean_object* v_x_6359_){
_start:
{
uint8_t v_x_42__boxed_6360_; lean_object* v_res_6361_; 
v_x_42__boxed_6360_ = lean_unbox(v_x_6359_);
v_res_6361_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6358_, v_x_42__boxed_6360_);
lean_dec(v_year_6358_);
return v_res_6361_;
}
}
uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t v_x_6362_){
_start:
{
switch(v_x_6362_)
{
case 1:
{
uint8_t v___x_6363_; 
v___x_6363_ = 1;
return v___x_6363_;
}
case 2:
{
uint8_t v___x_6364_; 
v___x_6364_ = 1;
return v___x_6364_;
}
default: 
{
uint8_t v___x_6365_; 
v___x_6365_ = 0;
return v___x_6365_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_6362_ = stack[0].m_num;
uint8_t v_res_6366_;
v_res_6366_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_6362_);
stack->m_num = v_res_6366_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object* v_x_6367_){
_start:
{
uint8_t v_x_28__boxed_6368_; uint8_t v_res_6369_; lean_object* v_r_6370_; 
v_x_28__boxed_6368_ = lean_unbox(v_x_6367_);
v_res_6369_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_28__boxed_6368_);
v_r_6370_ = lean_box(v_res_6369_);
return v_r_6370_;
}
}
uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(uint8_t v_x_6371_){
_start:
{
switch(v_x_6371_)
{
case 3:
{
uint8_t v___x_6372_; 
v___x_6372_ = 1;
return v___x_6372_;
}
case 4:
{
uint8_t v___x_6373_; 
v___x_6373_ = 1;
return v___x_6373_;
}
case 5:
{
uint8_t v___x_6374_; 
v___x_6374_ = 1;
return v___x_6374_;
}
default: 
{
uint8_t v___x_6375_; 
v___x_6375_ = 0;
return v___x_6375_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_6371_ = stack[0].m_num;
uint8_t v_res_6376_;
v_res_6376_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_x_6371_);
stack->m_num = v_res_6376_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object* v_x_6377_){
_start:
{
uint8_t v_x_38__boxed_6378_; uint8_t v_res_6379_; lean_object* v_r_6380_; 
v_x_38__boxed_6378_ = lean_unbox(v_x_6377_);
v_res_6379_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_x_38__boxed_6378_);
v_r_6380_ = lean_box(v_res_6379_);
return v_r_6380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object* v_val_6381_, lean_object* v_x_6382_){
_start:
{
lean_inc_ref(v_val_6381_);
return v_val_6381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object* v_val_6383_, lean_object* v_x_6384_){
_start:
{
lean_object* v_res_6385_; 
v_res_6385_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v_val_6383_, v_x_6384_);
lean_dec_ref(v_val_6383_);
return v_res_6385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object* v___y_6386_, lean_object* v_00___6387_){
_start:
{
uint8_t v___x_6388_; lean_object* v___x_6389_; 
v___x_6388_ = 1;
v___x_6389_ = l_Std_Time_TimeZone_Offset_toIsoString(v___y_6386_, v___x_6388_);
return v___x_6389_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1(void){
_start:
{
lean_object* v___x_6392_; lean_object* v___x_6393_; 
v___x_6392_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6393_ = lean_int_neg(v___x_6392_);
return v___x_6393_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2(void){
_start:
{
lean_object* v___x_6394_; lean_object* v___x_6395_; 
v___x_6394_ = lean_unsigned_to_nat(1000000u);
v___x_6395_ = lean_nat_to_int(v___x_6394_);
return v___x_6395_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3(void){
_start:
{
lean_object* v___x_6396_; uint8_t v___x_6397_; lean_object* v___x_6398_; 
v___x_6396_ = lean_unsigned_to_nat(0u);
v___x_6397_ = 1;
v___x_6398_ = l_Std_Time_Second_instOfNatOrdinal(v___x_6397_, v___x_6396_);
return v___x_6398_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4(void){
_start:
{
lean_object* v___x_6399_; lean_object* v___x_6400_; lean_object* v___x_6401_; 
v___x_6399_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_6400_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6401_ = lean_int_add(v___x_6400_, v___x_6399_);
return v___x_6401_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5(void){
_start:
{
lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; 
v___x_6402_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6403_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4);
v___x_6404_ = lean_int_sub(v___x_6403_, v___x_6402_);
return v___x_6404_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6(void){
_start:
{
lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v_range_6407_; 
v___x_6405_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6406_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v_range_6407_ = lean_int_add(v___x_6406_, v___x_6405_);
return v_range_6407_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7(void){
_start:
{
lean_object* v___x_6408_; lean_object* v___x_6409_; 
v___x_6408_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6409_ = lean_int_sub(v___x_6408_, v___x_6408_);
return v___x_6409_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8(void){
_start:
{
lean_object* v_range_6410_; lean_object* v___x_6411_; lean_object* v___x_6412_; 
v_range_6410_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6411_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7);
v___x_6412_ = lean_int_emod(v___x_6411_, v_range_6410_);
return v___x_6412_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9(void){
_start:
{
lean_object* v_range_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; 
v_range_6413_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6414_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6415_ = lean_int_add(v___x_6414_, v_range_6413_);
return v___x_6415_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10(void){
_start:
{
lean_object* v_range_6416_; lean_object* v___x_6417_; lean_object* v___x_6418_; 
v_range_6416_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6417_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9);
v___x_6418_ = lean_int_emod(v___x_6417_, v_range_6416_);
return v___x_6418_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11(void){
_start:
{
lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; 
v___x_6419_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6420_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10);
v___x_6421_ = lean_int_add(v___x_6420_, v___x_6419_);
return v___x_6421_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12(void){
_start:
{
lean_object* v___x_6422_; lean_object* v___x_6423_; 
v___x_6422_ = lean_unsigned_to_nat(30u);
v___x_6423_ = lean_nat_to_int(v___x_6422_);
return v___x_6423_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13(void){
_start:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; 
v___x_6424_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12);
v___x_6425_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6426_ = lean_int_add(v___x_6425_, v___x_6424_);
return v___x_6426_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14(void){
_start:
{
lean_object* v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; 
v___x_6427_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6428_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13);
v___x_6429_ = lean_int_sub(v___x_6428_, v___x_6427_);
return v___x_6429_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15(void){
_start:
{
lean_object* v___x_6430_; lean_object* v___x_6431_; lean_object* v_range_6432_; 
v___x_6430_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6431_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14);
v_range_6432_ = lean_int_add(v___x_6431_, v___x_6430_);
return v_range_6432_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16(void){
_start:
{
lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; 
v___x_6433_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6434_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6435_ = lean_int_sub(v___x_6434_, v___x_6433_);
return v___x_6435_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17(void){
_start:
{
lean_object* v_range_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; 
v_range_6436_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6437_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6438_ = lean_int_emod(v___x_6437_, v_range_6436_);
return v___x_6438_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18(void){
_start:
{
lean_object* v_range_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; 
v_range_6439_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6440_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6441_ = lean_int_add(v___x_6440_, v_range_6439_);
return v___x_6441_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19(void){
_start:
{
lean_object* v_range_6442_; lean_object* v___x_6443_; lean_object* v___x_6444_; 
v_range_6442_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6443_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6444_ = lean_int_emod(v___x_6443_, v_range_6442_);
return v___x_6444_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20(void){
_start:
{
lean_object* v___x_6445_; lean_object* v___x_6446_; lean_object* v___x_6447_; 
v___x_6445_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6446_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19);
v___x_6447_ = lean_int_add(v___x_6446_, v___x_6445_);
return v___x_6447_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21(void){
_start:
{
lean_object* v___x_6448_; lean_object* v___x_6449_; 
v___x_6448_ = lean_unsigned_to_nat(11u);
v___x_6449_ = lean_nat_to_int(v___x_6448_);
return v___x_6449_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22(void){
_start:
{
lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; 
v___x_6450_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21);
v___x_6451_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6452_ = lean_int_add(v___x_6451_, v___x_6450_);
return v___x_6452_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23(void){
_start:
{
lean_object* v___x_6453_; lean_object* v___x_6454_; lean_object* v___x_6455_; 
v___x_6453_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6454_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22);
v___x_6455_ = lean_int_sub(v___x_6454_, v___x_6453_);
return v___x_6455_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24(void){
_start:
{
lean_object* v___x_6456_; lean_object* v___x_6457_; lean_object* v_range_6458_; 
v___x_6456_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6457_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23);
v_range_6458_ = lean_int_add(v___x_6457_, v___x_6456_);
return v_range_6458_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25(void){
_start:
{
lean_object* v_range_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; 
v_range_6459_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6460_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6461_ = lean_int_emod(v___x_6460_, v_range_6459_);
return v___x_6461_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26(void){
_start:
{
lean_object* v_range_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; 
v_range_6462_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6463_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25);
v___x_6464_ = lean_int_add(v___x_6463_, v_range_6462_);
return v___x_6464_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27(void){
_start:
{
lean_object* v_range_6465_; lean_object* v___x_6466_; lean_object* v___x_6467_; 
v_range_6465_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6466_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6467_ = lean_int_emod(v___x_6466_, v_range_6465_);
return v___x_6467_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28(void){
_start:
{
lean_object* v___x_6468_; lean_object* v___x_6469_; lean_object* v___x_6470_; 
v___x_6468_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6469_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27);
v___x_6470_ = lean_int_add(v___x_6469_, v___x_6468_);
return v___x_6470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object* v_builder_6471_, lean_object* v_aw_6472_){
_start:
{
lean_object* v___y_6474_; lean_object* v___y_6475_; lean_object* v___y_6514_; lean_object* v___y_6515_; lean_object* v___y_6518_; lean_object* v___y_6519_; lean_object* v___y_6520_; lean_object* v___y_6521_; lean_object* v___y_6522_; uint8_t v___y_6523_; lean_object* v___y_6531_; lean_object* v___y_6532_; lean_object* v___y_6533_; lean_object* v___y_6534_; lean_object* v___y_6535_; lean_object* v___y_6536_; lean_object* v___y_6541_; lean_object* v___y_6542_; lean_object* v___y_6543_; lean_object* v___y_6544_; lean_object* v___y_6545_; lean_object* v_G_6553_; lean_object* v_y_6554_; lean_object* v_u_6555_; lean_object* v_Y_6556_; lean_object* v_M_6557_; lean_object* v_L_6558_; lean_object* v_d_6559_; lean_object* v_a_6560_; lean_object* v_b_6561_; lean_object* v_B_6562_; lean_object* v_h_6563_; lean_object* v_K_6564_; lean_object* v_k_6565_; lean_object* v_H_6566_; lean_object* v_m_6567_; lean_object* v_s_6568_; lean_object* v_S_6569_; lean_object* v_A_6570_; lean_object* v_n_6571_; lean_object* v_N_6572_; lean_object* v_V_6573_; lean_object* v_z_6574_; lean_object* v_zabbrev_6575_; lean_object* v_v_6576_; lean_object* v_O_6577_; lean_object* v_X_6578_; lean_object* v_x_6579_; lean_object* v_Z_6580_; lean_object* v___y_6582_; lean_object* v___y_6583_; lean_object* v___y_6584_; lean_object* v___y_6585_; lean_object* v___y_6586_; lean_object* v___y_6587_; lean_object* v___y_6588_; lean_object* v___y_6589_; lean_object* v___y_6598_; lean_object* v___y_6599_; lean_object* v___y_6600_; lean_object* v___y_6601_; lean_object* v___y_6602_; lean_object* v___y_6603_; lean_object* v___y_6604_; lean_object* v___y_6609_; lean_object* v___y_6610_; lean_object* v___y_6611_; lean_object* v___y_6612_; lean_object* v___y_6613_; lean_object* v___y_6614_; lean_object* v___y_6618_; lean_object* v___y_6619_; lean_object* v___y_6620_; lean_object* v___y_6621_; lean_object* v___y_6622_; lean_object* v___y_6626_; lean_object* v___y_6627_; lean_object* v___y_6628_; lean_object* v___y_6629_; lean_object* v___y_6637_; lean_object* v___y_6638_; lean_object* v___y_6639_; lean_object* v___y_6640_; uint8_t v_val_6641_; lean_object* v___y_6649_; lean_object* v___y_6650_; lean_object* v___y_6651_; lean_object* v___y_6652_; lean_object* v___y_6662_; lean_object* v___y_6663_; lean_object* v___y_6664_; uint8_t v___y_6665_; lean_object* v___y_6672_; lean_object* v___y_6673_; lean_object* v___y_6674_; lean_object* v___y_6679_; lean_object* v___y_6680_; lean_object* v___y_6684_; lean_object* v___y_6685_; lean_object* v___y_6686_; lean_object* v___y_6693_; lean_object* v___y_6694_; lean_object* v___y_6695_; lean_object* v___y_6700_; 
v_G_6553_ = lean_ctor_get(v_builder_6471_, 0);
lean_inc(v_G_6553_);
v_y_6554_ = lean_ctor_get(v_builder_6471_, 1);
lean_inc(v_y_6554_);
v_u_6555_ = lean_ctor_get(v_builder_6471_, 2);
lean_inc(v_u_6555_);
v_Y_6556_ = lean_ctor_get(v_builder_6471_, 3);
lean_inc(v_Y_6556_);
v_M_6557_ = lean_ctor_get(v_builder_6471_, 5);
lean_inc(v_M_6557_);
v_L_6558_ = lean_ctor_get(v_builder_6471_, 6);
lean_inc(v_L_6558_);
v_d_6559_ = lean_ctor_get(v_builder_6471_, 7);
lean_inc(v_d_6559_);
v_a_6560_ = lean_ctor_get(v_builder_6471_, 16);
lean_inc(v_a_6560_);
v_b_6561_ = lean_ctor_get(v_builder_6471_, 17);
lean_inc(v_b_6561_);
v_B_6562_ = lean_ctor_get(v_builder_6471_, 18);
lean_inc(v_B_6562_);
v_h_6563_ = lean_ctor_get(v_builder_6471_, 19);
lean_inc(v_h_6563_);
v_K_6564_ = lean_ctor_get(v_builder_6471_, 20);
lean_inc(v_K_6564_);
v_k_6565_ = lean_ctor_get(v_builder_6471_, 21);
lean_inc(v_k_6565_);
v_H_6566_ = lean_ctor_get(v_builder_6471_, 22);
lean_inc(v_H_6566_);
v_m_6567_ = lean_ctor_get(v_builder_6471_, 23);
lean_inc(v_m_6567_);
v_s_6568_ = lean_ctor_get(v_builder_6471_, 24);
lean_inc(v_s_6568_);
v_S_6569_ = lean_ctor_get(v_builder_6471_, 25);
lean_inc(v_S_6569_);
v_A_6570_ = lean_ctor_get(v_builder_6471_, 26);
lean_inc(v_A_6570_);
v_n_6571_ = lean_ctor_get(v_builder_6471_, 27);
lean_inc(v_n_6571_);
v_N_6572_ = lean_ctor_get(v_builder_6471_, 28);
lean_inc(v_N_6572_);
v_V_6573_ = lean_ctor_get(v_builder_6471_, 29);
lean_inc(v_V_6573_);
v_z_6574_ = lean_ctor_get(v_builder_6471_, 30);
lean_inc(v_z_6574_);
v_zabbrev_6575_ = lean_ctor_get(v_builder_6471_, 31);
lean_inc(v_zabbrev_6575_);
v_v_6576_ = lean_ctor_get(v_builder_6471_, 32);
lean_inc(v_v_6576_);
v_O_6577_ = lean_ctor_get(v_builder_6471_, 33);
lean_inc(v_O_6577_);
v_X_6578_ = lean_ctor_get(v_builder_6471_, 34);
lean_inc(v_X_6578_);
v_x_6579_ = lean_ctor_get(v_builder_6471_, 35);
lean_inc(v_x_6579_);
v_Z_6580_ = lean_ctor_get(v_builder_6471_, 36);
lean_inc(v_Z_6580_);
lean_dec_ref(v_builder_6471_);
if (lean_obj_tag(v_O_6577_) == 0)
{
if (lean_obj_tag(v_X_6578_) == 0)
{
if (lean_obj_tag(v_x_6579_) == 0)
{
if (lean_obj_tag(v_Z_6580_) == 0)
{
lean_object* v___x_6707_; 
v___x_6707_ = l_Std_Time_TimeZone_Offset_zero;
v___y_6700_ = v___x_6707_;
goto v___jp_6699_;
}
else
{
lean_object* v_val_6708_; 
v_val_6708_ = lean_ctor_get(v_Z_6580_, 0);
lean_inc(v_val_6708_);
lean_dec_ref_known(v_Z_6580_, 1);
v___y_6700_ = v_val_6708_;
goto v___jp_6699_;
}
}
else
{
lean_object* v_val_6709_; 
lean_dec(v_Z_6580_);
v_val_6709_ = lean_ctor_get(v_x_6579_, 0);
lean_inc(v_val_6709_);
lean_dec_ref_known(v_x_6579_, 1);
v___y_6700_ = v_val_6709_;
goto v___jp_6699_;
}
}
else
{
lean_object* v_val_6710_; 
lean_dec(v_Z_6580_);
lean_dec(v_x_6579_);
v_val_6710_ = lean_ctor_get(v_X_6578_, 0);
lean_inc(v_val_6710_);
lean_dec_ref_known(v_X_6578_, 1);
v___y_6700_ = v_val_6710_;
goto v___jp_6699_;
}
}
else
{
lean_object* v_val_6711_; 
lean_dec(v_Z_6580_);
lean_dec(v_x_6579_);
lean_dec(v_X_6578_);
v_val_6711_ = lean_ctor_get(v_O_6577_, 0);
lean_inc(v_val_6711_);
lean_dec_ref_known(v_O_6577_, 1);
v___y_6700_ = v_val_6711_;
goto v___jp_6699_;
}
v___jp_6473_:
{
if (lean_obj_tag(v___y_6474_) == 0)
{
lean_object* v___x_6476_; 
lean_dec_ref(v___y_6475_);
v___x_6476_ = lean_box(0);
return v___x_6476_;
}
else
{
lean_object* v_val_6477_; lean_object* v___x_6479_; uint8_t v_isShared_6480_; uint8_t v_isSharedCheck_6512_; 
v_val_6477_ = lean_ctor_get(v___y_6474_, 0);
v_isSharedCheck_6512_ = !lean_is_exclusive(v___y_6474_);
if (v_isSharedCheck_6512_ == 0)
{
v___x_6479_ = v___y_6474_;
v_isShared_6480_ = v_isSharedCheck_6512_;
goto v_resetjp_6478_;
}
else
{
lean_inc(v_val_6477_);
lean_dec(v___y_6474_);
v___x_6479_ = lean_box(0);
v_isShared_6480_ = v_isSharedCheck_6512_;
goto v_resetjp_6478_;
}
v_resetjp_6478_:
{
lean_object* v_offset_6481_; lean_object* v_name_6482_; lean_object* v_abbreviation_6483_; uint8_t v_isDST_6484_; uint8_t v___x_6485_; uint8_t v___x_6486_; lean_object* v_ltt_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v_wt_6491_; lean_object* v_ltt_6492_; lean_object* v_tz_6493_; lean_object* v_offset_6494_; lean_object* v_second_6495_; lean_object* v_nano_6496_; lean_object* v___f_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v___x_6501_; lean_object* v___x_6502_; lean_object* v_nanos_6503_; lean_object* v___x_6504_; lean_object* v_nanos_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6510_; 
v_offset_6481_ = lean_ctor_get(v___y_6475_, 0);
lean_inc(v_offset_6481_);
v_name_6482_ = lean_ctor_get(v___y_6475_, 1);
lean_inc_ref(v_name_6482_);
v_abbreviation_6483_ = lean_ctor_get(v___y_6475_, 2);
lean_inc_ref(v_abbreviation_6483_);
v_isDST_6484_ = lean_ctor_get_uint8(v___y_6475_, sizeof(void*)*3);
lean_dec_ref(v___y_6475_);
v___x_6485_ = 0;
v___x_6486_ = 1;
v_ltt_6487_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6487_, 0, v_offset_6481_);
lean_ctor_set(v_ltt_6487_, 1, v_abbreviation_6483_);
lean_ctor_set(v_ltt_6487_, 2, v_name_6482_);
lean_ctor_set_uint8(v_ltt_6487_, sizeof(void*)*3, v_isDST_6484_);
lean_ctor_set_uint8(v_ltt_6487_, sizeof(void*)*3 + 1, v___x_6485_);
lean_ctor_set_uint8(v_ltt_6487_, sizeof(void*)*3 + 2, v___x_6486_);
v___x_6488_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6489_ = lean_box(0);
v___x_6490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6490_, 0, v_ltt_6487_);
lean_ctor_set(v___x_6490_, 1, v___x_6488_);
lean_ctor_set(v___x_6490_, 2, v___x_6489_);
lean_inc(v_val_6477_);
v_wt_6491_ = l_Std_Time_PlainDateTime_toWallTime(v_val_6477_);
lean_inc_ref(v___x_6490_);
v_ltt_6492_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_6490_, v_wt_6491_);
v_tz_6493_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_6492_);
lean_dec_ref(v_ltt_6492_);
v_offset_6494_ = lean_ctor_get(v_tz_6493_, 0);
v_second_6495_ = lean_ctor_get(v_wt_6491_, 0);
lean_inc(v_second_6495_);
v_nano_6496_ = lean_ctor_get(v_wt_6491_, 1);
lean_inc(v_nano_6496_);
lean_dec_ref(v_wt_6491_);
v___f_6497_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6497_, 0, v_val_6477_);
v___x_6498_ = lean_mk_thunk(v___f_6497_);
v___x_6499_ = lean_int_neg(v_offset_6494_);
v___x_6500_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1);
v___x_6501_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6502_ = lean_int_mul(v_second_6495_, v___x_6501_);
lean_dec(v_second_6495_);
v_nanos_6503_ = lean_int_add(v___x_6502_, v_nano_6496_);
lean_dec(v_nano_6496_);
lean_dec(v___x_6502_);
v___x_6504_ = lean_int_mul(v___x_6499_, v___x_6501_);
lean_dec(v___x_6499_);
v_nanos_6505_ = lean_int_add(v___x_6504_, v___x_6500_);
lean_dec(v___x_6504_);
v___x_6506_ = lean_int_add(v_nanos_6503_, v_nanos_6505_);
lean_dec(v_nanos_6505_);
lean_dec(v_nanos_6503_);
v___x_6507_ = l_Std_Time_Duration_ofNanoseconds(v___x_6506_);
lean_dec(v___x_6506_);
v___x_6508_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6508_, 0, v___x_6498_);
lean_ctor_set(v___x_6508_, 1, v___x_6507_);
lean_ctor_set(v___x_6508_, 2, v___x_6490_);
lean_ctor_set(v___x_6508_, 3, v_tz_6493_);
if (v_isShared_6480_ == 0)
{
lean_ctor_set(v___x_6479_, 0, v___x_6508_);
v___x_6510_ = v___x_6479_;
goto v_reusejp_6509_;
}
else
{
lean_object* v_reuseFailAlloc_6511_; 
v_reuseFailAlloc_6511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6511_, 0, v___x_6508_);
v___x_6510_ = v_reuseFailAlloc_6511_;
goto v_reusejp_6509_;
}
v_reusejp_6509_:
{
return v___x_6510_;
}
}
}
}
v___jp_6513_:
{
if (lean_obj_tag(v_aw_6472_) == 0)
{
lean_object* v_a_6516_; 
lean_dec_ref(v___y_6514_);
v_a_6516_ = lean_ctor_get(v_aw_6472_, 0);
lean_inc_ref(v_a_6516_);
lean_dec_ref_known(v_aw_6472_, 1);
v___y_6474_ = v___y_6515_;
v___y_6475_ = v_a_6516_;
goto v___jp_6473_;
}
else
{
v___y_6474_ = v___y_6515_;
v___y_6475_ = v___y_6514_;
goto v___jp_6473_;
}
}
v___jp_6517_:
{
lean_object* v___x_6524_; uint8_t v___x_6525_; 
v___x_6524_ = l_Std_Time_Month_Ordinal_days(v___y_6523_, v___y_6521_);
v___x_6525_ = lean_int_dec_le(v___y_6518_, v___x_6524_);
lean_dec(v___x_6524_);
if (v___x_6525_ == 0)
{
lean_object* v___x_6526_; 
lean_dec(v___y_6521_);
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6519_);
lean_dec(v___y_6518_);
v___x_6526_ = lean_box(0);
v___y_6514_ = v___y_6522_;
v___y_6515_ = v___x_6526_;
goto v___jp_6513_;
}
else
{
lean_object* v_date_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; 
v_date_6527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_date_6527_, 0, v___y_6520_);
lean_ctor_set(v_date_6527_, 1, v___y_6521_);
lean_ctor_set(v_date_6527_, 2, v___y_6518_);
v___x_6528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6528_, 0, v_date_6527_);
lean_ctor_set(v___x_6528_, 1, v___y_6519_);
v___x_6529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6529_, 0, v___x_6528_);
v___y_6514_ = v___y_6522_;
v___y_6515_ = v___x_6529_;
goto v___jp_6513_;
}
}
v___jp_6530_:
{
lean_object* v___x_6537_; lean_object* v___x_6538_; uint8_t v___x_6539_; 
v___x_6537_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_6538_ = lean_int_mod(v___y_6534_, v___x_6537_);
v___x_6539_ = lean_int_dec_eq(v___x_6538_, v___y_6535_);
lean_dec(v___x_6538_);
v___y_6518_ = v___y_6531_;
v___y_6519_ = v___y_6533_;
v___y_6520_ = v___y_6534_;
v___y_6521_ = v___y_6532_;
v___y_6522_ = v___y_6536_;
v___y_6523_ = v___x_6539_;
goto v___jp_6517_;
}
v___jp_6540_:
{
lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; uint8_t v___x_6549_; 
v___x_6546_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_6547_ = lean_int_mod(v___y_6543_, v___x_6546_);
v___x_6548_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6549_ = lean_int_dec_eq(v___x_6547_, v___x_6548_);
lean_dec(v___x_6547_);
if (v___x_6549_ == 0)
{
v___y_6518_ = v___y_6541_;
v___y_6519_ = v___y_6545_;
v___y_6520_ = v___y_6543_;
v___y_6521_ = v___y_6542_;
v___y_6522_ = v___y_6544_;
v___y_6523_ = v___x_6549_;
goto v___jp_6517_;
}
else
{
lean_object* v___x_6550_; lean_object* v___x_6551_; uint8_t v___x_6552_; 
v___x_6550_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6551_ = lean_int_mod(v___y_6543_, v___x_6550_);
v___x_6552_ = lean_int_dec_eq(v___x_6551_, v___x_6548_);
lean_dec(v___x_6551_);
if (v___x_6552_ == 0)
{
if (v___x_6549_ == 0)
{
v___y_6531_ = v___y_6541_;
v___y_6532_ = v___y_6542_;
v___y_6533_ = v___y_6545_;
v___y_6534_ = v___y_6543_;
v___y_6535_ = v___x_6548_;
v___y_6536_ = v___y_6544_;
goto v___jp_6530_;
}
else
{
v___y_6518_ = v___y_6541_;
v___y_6519_ = v___y_6545_;
v___y_6520_ = v___y_6543_;
v___y_6521_ = v___y_6542_;
v___y_6522_ = v___y_6544_;
v___y_6523_ = v___x_6549_;
goto v___jp_6517_;
}
}
else
{
v___y_6531_ = v___y_6541_;
v___y_6532_ = v___y_6542_;
v___y_6533_ = v___y_6545_;
v___y_6534_ = v___y_6543_;
v___y_6535_ = v___x_6548_;
v___y_6536_ = v___y_6544_;
goto v___jp_6530_;
}
}
}
v___jp_6581_:
{
if (lean_obj_tag(v_N_6572_) == 0)
{
if (lean_obj_tag(v_A_6570_) == 0)
{
lean_object* v___x_6590_; 
v___x_6590_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6590_, 0, v___y_6586_);
lean_ctor_set(v___x_6590_, 1, v___y_6587_);
lean_ctor_set(v___x_6590_, 2, v___y_6585_);
lean_ctor_set(v___x_6590_, 3, v___y_6589_);
v___y_6541_ = v___y_6582_;
v___y_6542_ = v___y_6584_;
v___y_6543_ = v___y_6583_;
v___y_6544_ = v___y_6588_;
v___y_6545_ = v___x_6590_;
goto v___jp_6540_;
}
else
{
lean_object* v_val_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; 
lean_dec(v___y_6589_);
lean_dec(v___y_6587_);
lean_dec(v___y_6586_);
lean_dec(v___y_6585_);
v_val_6591_ = lean_ctor_get(v_A_6570_, 0);
lean_inc(v_val_6591_);
lean_dec_ref_known(v_A_6570_, 1);
v___x_6592_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2);
v___x_6593_ = lean_int_mul(v_val_6591_, v___x_6592_);
lean_dec(v_val_6591_);
v___x_6594_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_6593_);
lean_dec(v___x_6593_);
v___y_6541_ = v___y_6582_;
v___y_6542_ = v___y_6584_;
v___y_6543_ = v___y_6583_;
v___y_6544_ = v___y_6588_;
v___y_6545_ = v___x_6594_;
goto v___jp_6540_;
}
}
else
{
lean_object* v_val_6595_; lean_object* v___x_6596_; 
lean_dec(v___y_6589_);
lean_dec(v___y_6587_);
lean_dec(v___y_6586_);
lean_dec(v___y_6585_);
lean_dec(v_A_6570_);
v_val_6595_ = lean_ctor_get(v_N_6572_, 0);
lean_inc(v_val_6595_);
lean_dec_ref_known(v_N_6572_, 1);
v___x_6596_ = l_Std_Time_PlainTime_ofNanoseconds(v_val_6595_);
lean_dec(v_val_6595_);
v___y_6541_ = v___y_6582_;
v___y_6542_ = v___y_6584_;
v___y_6543_ = v___y_6583_;
v___y_6544_ = v___y_6588_;
v___y_6545_ = v___x_6596_;
goto v___jp_6540_;
}
}
v___jp_6597_:
{
if (lean_obj_tag(v_n_6571_) == 0)
{
if (lean_obj_tag(v_S_6569_) == 0)
{
lean_object* v___x_6605_; 
v___x_6605_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6582_ = v___y_6598_;
v___y_6583_ = v___y_6600_;
v___y_6584_ = v___y_6599_;
v___y_6585_ = v___y_6604_;
v___y_6586_ = v___y_6601_;
v___y_6587_ = v___y_6602_;
v___y_6588_ = v___y_6603_;
v___y_6589_ = v___x_6605_;
goto v___jp_6581_;
}
else
{
lean_object* v_val_6606_; 
v_val_6606_ = lean_ctor_get(v_S_6569_, 0);
lean_inc(v_val_6606_);
lean_dec_ref_known(v_S_6569_, 1);
v___y_6582_ = v___y_6598_;
v___y_6583_ = v___y_6600_;
v___y_6584_ = v___y_6599_;
v___y_6585_ = v___y_6604_;
v___y_6586_ = v___y_6601_;
v___y_6587_ = v___y_6602_;
v___y_6588_ = v___y_6603_;
v___y_6589_ = v_val_6606_;
goto v___jp_6581_;
}
}
else
{
lean_object* v_val_6607_; 
lean_dec(v_S_6569_);
v_val_6607_ = lean_ctor_get(v_n_6571_, 0);
lean_inc(v_val_6607_);
lean_dec_ref_known(v_n_6571_, 1);
v___y_6582_ = v___y_6598_;
v___y_6583_ = v___y_6600_;
v___y_6584_ = v___y_6599_;
v___y_6585_ = v___y_6604_;
v___y_6586_ = v___y_6601_;
v___y_6587_ = v___y_6602_;
v___y_6588_ = v___y_6603_;
v___y_6589_ = v_val_6607_;
goto v___jp_6581_;
}
}
v___jp_6608_:
{
if (lean_obj_tag(v_s_6568_) == 0)
{
lean_object* v___x_6615_; 
v___x_6615_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3);
v___y_6598_ = v___y_6609_;
v___y_6599_ = v___y_6611_;
v___y_6600_ = v___y_6610_;
v___y_6601_ = v___y_6612_;
v___y_6602_ = v___y_6614_;
v___y_6603_ = v___y_6613_;
v___y_6604_ = v___x_6615_;
goto v___jp_6597_;
}
else
{
lean_object* v_val_6616_; 
v_val_6616_ = lean_ctor_get(v_s_6568_, 0);
lean_inc(v_val_6616_);
lean_dec_ref_known(v_s_6568_, 1);
v___y_6598_ = v___y_6609_;
v___y_6599_ = v___y_6611_;
v___y_6600_ = v___y_6610_;
v___y_6601_ = v___y_6612_;
v___y_6602_ = v___y_6614_;
v___y_6603_ = v___y_6613_;
v___y_6604_ = v_val_6616_;
goto v___jp_6597_;
}
}
v___jp_6617_:
{
if (lean_obj_tag(v_m_6567_) == 0)
{
lean_object* v___x_6623_; 
v___x_6623_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11);
v___y_6609_ = v___y_6618_;
v___y_6610_ = v___y_6620_;
v___y_6611_ = v___y_6619_;
v___y_6612_ = v___y_6622_;
v___y_6613_ = v___y_6621_;
v___y_6614_ = v___x_6623_;
goto v___jp_6608_;
}
else
{
lean_object* v_val_6624_; 
v_val_6624_ = lean_ctor_get(v_m_6567_, 0);
lean_inc(v_val_6624_);
lean_dec_ref_known(v_m_6567_, 1);
v___y_6609_ = v___y_6618_;
v___y_6610_ = v___y_6620_;
v___y_6611_ = v___y_6619_;
v___y_6612_ = v___y_6622_;
v___y_6613_ = v___y_6621_;
v___y_6614_ = v_val_6624_;
goto v___jp_6608_;
}
}
v___jp_6625_:
{
if (lean_obj_tag(v_k_6565_) == 0)
{
if (lean_obj_tag(v_H_6566_) == 0)
{
lean_object* v___x_6630_; 
v___x_6630_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6618_ = v___y_6626_;
v___y_6619_ = v___y_6628_;
v___y_6620_ = v___y_6627_;
v___y_6621_ = v___y_6629_;
v___y_6622_ = v___x_6630_;
goto v___jp_6617_;
}
else
{
lean_object* v_val_6631_; 
v_val_6631_ = lean_ctor_get(v_H_6566_, 0);
lean_inc(v_val_6631_);
lean_dec_ref_known(v_H_6566_, 1);
v___y_6618_ = v___y_6626_;
v___y_6619_ = v___y_6628_;
v___y_6620_ = v___y_6627_;
v___y_6621_ = v___y_6629_;
v___y_6622_ = v_val_6631_;
goto v___jp_6617_;
}
}
else
{
if (lean_obj_tag(v_H_6566_) == 0)
{
lean_object* v_val_6632_; lean_object* v___x_6633_; lean_object* v___x_6634_; 
v_val_6632_ = lean_ctor_get(v_k_6565_, 0);
lean_inc(v_val_6632_);
lean_dec_ref_known(v_k_6565_, 1);
v___x_6633_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_6634_ = lean_int_add(v_val_6632_, v___x_6633_);
lean_dec(v_val_6632_);
v___y_6618_ = v___y_6626_;
v___y_6619_ = v___y_6628_;
v___y_6620_ = v___y_6627_;
v___y_6621_ = v___y_6629_;
v___y_6622_ = v___x_6634_;
goto v___jp_6617_;
}
else
{
lean_object* v_val_6635_; 
lean_dec_ref_known(v_k_6565_, 1);
v_val_6635_ = lean_ctor_get(v_H_6566_, 0);
lean_inc(v_val_6635_);
lean_dec_ref_known(v_H_6566_, 1);
v___y_6618_ = v___y_6626_;
v___y_6619_ = v___y_6628_;
v___y_6620_ = v___y_6627_;
v___y_6621_ = v___y_6629_;
v___y_6622_ = v_val_6635_;
goto v___jp_6617_;
}
}
}
v___jp_6636_:
{
if (lean_obj_tag(v_h_6563_) == 0)
{
if (lean_obj_tag(v_K_6564_) == 0)
{
v___y_6626_ = v___y_6637_;
v___y_6627_ = v___y_6639_;
v___y_6628_ = v___y_6638_;
v___y_6629_ = v___y_6640_;
goto v___jp_6625_;
}
else
{
lean_object* v_val_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; 
lean_dec(v_H_6566_);
lean_dec(v_k_6565_);
v_val_6642_ = lean_ctor_get(v_K_6564_, 0);
lean_inc(v_val_6642_);
lean_dec_ref_known(v_K_6564_, 1);
v___x_6643_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6644_ = lean_int_add(v_val_6642_, v___x_6643_);
lean_dec(v_val_6642_);
v___x_6645_ = l_Std_Time_HourMarker_toAbsolute(v_val_6641_, v___x_6644_);
lean_dec(v___x_6644_);
v___y_6618_ = v___y_6637_;
v___y_6619_ = v___y_6638_;
v___y_6620_ = v___y_6639_;
v___y_6621_ = v___y_6640_;
v___y_6622_ = v___x_6645_;
goto v___jp_6617_;
}
}
else
{
lean_object* v_val_6646_; lean_object* v___x_6647_; 
lean_dec(v_H_6566_);
lean_dec(v_k_6565_);
lean_dec(v_K_6564_);
v_val_6646_ = lean_ctor_get(v_h_6563_, 0);
lean_inc(v_val_6646_);
lean_dec_ref_known(v_h_6563_, 1);
v___x_6647_ = l_Std_Time_HourMarker_toAbsolute(v_val_6641_, v_val_6646_);
lean_dec(v_val_6646_);
v___y_6618_ = v___y_6637_;
v___y_6619_ = v___y_6638_;
v___y_6620_ = v___y_6639_;
v___y_6621_ = v___y_6640_;
v___y_6622_ = v___x_6647_;
goto v___jp_6617_;
}
}
v___jp_6648_:
{
if (lean_obj_tag(v_a_6560_) == 0)
{
if (lean_obj_tag(v_b_6561_) == 0)
{
if (lean_obj_tag(v_B_6562_) == 0)
{
lean_dec(v_K_6564_);
lean_dec(v_h_6563_);
v___y_6626_ = v___y_6649_;
v___y_6627_ = v___y_6652_;
v___y_6628_ = v___y_6650_;
v___y_6629_ = v___y_6651_;
goto v___jp_6625_;
}
else
{
lean_object* v_val_6653_; uint8_t v___x_6654_; uint8_t v___x_6655_; 
v_val_6653_ = lean_ctor_get(v_B_6562_, 0);
lean_inc(v_val_6653_);
lean_dec_ref_known(v_B_6562_, 1);
v___x_6654_ = lean_unbox(v_val_6653_);
lean_dec(v_val_6653_);
v___x_6655_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v___x_6654_);
v___y_6637_ = v___y_6649_;
v___y_6638_ = v___y_6650_;
v___y_6639_ = v___y_6652_;
v___y_6640_ = v___y_6651_;
v_val_6641_ = v___x_6655_;
goto v___jp_6636_;
}
}
else
{
lean_object* v_val_6656_; uint8_t v___x_6657_; uint8_t v___x_6658_; 
lean_dec(v_B_6562_);
v_val_6656_ = lean_ctor_get(v_b_6561_, 0);
lean_inc(v_val_6656_);
lean_dec_ref_known(v_b_6561_, 1);
v___x_6657_ = lean_unbox(v_val_6656_);
lean_dec(v_val_6656_);
v___x_6658_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v___x_6657_);
v___y_6637_ = v___y_6649_;
v___y_6638_ = v___y_6650_;
v___y_6639_ = v___y_6652_;
v___y_6640_ = v___y_6651_;
v_val_6641_ = v___x_6658_;
goto v___jp_6636_;
}
}
else
{
lean_object* v_val_6659_; uint8_t v___x_6660_; 
lean_dec(v_B_6562_);
lean_dec(v_b_6561_);
v_val_6659_ = lean_ctor_get(v_a_6560_, 0);
lean_inc(v_val_6659_);
lean_dec_ref_known(v_a_6560_, 1);
v___x_6660_ = lean_unbox(v_val_6659_);
lean_dec(v_val_6659_);
v___y_6637_ = v___y_6649_;
v___y_6638_ = v___y_6650_;
v___y_6639_ = v___y_6652_;
v___y_6640_ = v___y_6651_;
v_val_6641_ = v___x_6660_;
goto v___jp_6636_;
}
}
v___jp_6661_:
{
if (lean_obj_tag(v_u_6555_) == 0)
{
if (lean_obj_tag(v_y_6554_) == 0)
{
if (lean_obj_tag(v_Y_6556_) == 0)
{
lean_object* v___x_6666_; 
v___x_6666_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6649_ = v___y_6662_;
v___y_6650_ = v___y_6663_;
v___y_6651_ = v___y_6664_;
v___y_6652_ = v___x_6666_;
goto v___jp_6648_;
}
else
{
lean_object* v_val_6667_; 
v_val_6667_ = lean_ctor_get(v_Y_6556_, 0);
lean_inc(v_val_6667_);
lean_dec_ref_known(v_Y_6556_, 1);
v___y_6649_ = v___y_6662_;
v___y_6650_ = v___y_6663_;
v___y_6651_ = v___y_6664_;
v___y_6652_ = v_val_6667_;
goto v___jp_6648_;
}
}
else
{
lean_object* v_val_6668_; lean_object* v___x_6669_; 
lean_dec(v_Y_6556_);
v_val_6668_ = lean_ctor_get(v_y_6554_, 0);
lean_inc(v_val_6668_);
lean_dec_ref_known(v_y_6554_, 1);
v___x_6669_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6668_, v___y_6665_);
lean_dec(v_val_6668_);
v___y_6649_ = v___y_6662_;
v___y_6650_ = v___y_6663_;
v___y_6651_ = v___y_6664_;
v___y_6652_ = v___x_6669_;
goto v___jp_6648_;
}
}
else
{
lean_object* v_val_6670_; 
lean_dec(v_Y_6556_);
lean_dec(v_y_6554_);
v_val_6670_ = lean_ctor_get(v_u_6555_, 0);
lean_inc(v_val_6670_);
lean_dec_ref_known(v_u_6555_, 1);
v___y_6649_ = v___y_6662_;
v___y_6650_ = v___y_6663_;
v___y_6651_ = v___y_6664_;
v___y_6652_ = v_val_6670_;
goto v___jp_6648_;
}
}
v___jp_6671_:
{
if (lean_obj_tag(v_G_6553_) == 0)
{
uint8_t v___x_6675_; 
v___x_6675_ = 1;
v___y_6662_ = v___y_6674_;
v___y_6663_ = v___y_6672_;
v___y_6664_ = v___y_6673_;
v___y_6665_ = v___x_6675_;
goto v___jp_6661_;
}
else
{
lean_object* v_val_6676_; uint8_t v___x_6677_; 
v_val_6676_ = lean_ctor_get(v_G_6553_, 0);
lean_inc(v_val_6676_);
lean_dec_ref_known(v_G_6553_, 1);
v___x_6677_ = lean_unbox(v_val_6676_);
lean_dec(v_val_6676_);
v___y_6662_ = v___y_6674_;
v___y_6663_ = v___y_6672_;
v___y_6664_ = v___y_6673_;
v___y_6665_ = v___x_6677_;
goto v___jp_6661_;
}
}
v___jp_6678_:
{
if (lean_obj_tag(v_d_6559_) == 0)
{
lean_object* v___x_6681_; 
v___x_6681_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20);
v___y_6672_ = v___y_6680_;
v___y_6673_ = v___y_6679_;
v___y_6674_ = v___x_6681_;
goto v___jp_6671_;
}
else
{
lean_object* v_val_6682_; 
v_val_6682_ = lean_ctor_get(v_d_6559_, 0);
lean_inc(v_val_6682_);
lean_dec_ref_known(v_d_6559_, 1);
v___y_6672_ = v___y_6680_;
v___y_6673_ = v___y_6679_;
v___y_6674_ = v_val_6682_;
goto v___jp_6671_;
}
}
v___jp_6683_:
{
uint8_t v___x_6687_; lean_object* v_tz_6688_; 
v___x_6687_ = 0;
v_tz_6688_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tz_6688_, 0, v___y_6684_);
lean_ctor_set(v_tz_6688_, 1, v___y_6685_);
lean_ctor_set(v_tz_6688_, 2, v___y_6686_);
lean_ctor_set_uint8(v_tz_6688_, sizeof(void*)*3, v___x_6687_);
if (lean_obj_tag(v_M_6557_) == 0)
{
if (lean_obj_tag(v_L_6558_) == 0)
{
lean_object* v___x_6689_; 
v___x_6689_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28);
v___y_6679_ = v_tz_6688_;
v___y_6680_ = v___x_6689_;
goto v___jp_6678_;
}
else
{
lean_object* v_val_6690_; 
v_val_6690_ = lean_ctor_get(v_L_6558_, 0);
lean_inc(v_val_6690_);
lean_dec_ref_known(v_L_6558_, 1);
v___y_6679_ = v_tz_6688_;
v___y_6680_ = v_val_6690_;
goto v___jp_6678_;
}
}
else
{
lean_object* v_val_6691_; 
lean_dec(v_L_6558_);
v_val_6691_ = lean_ctor_get(v_M_6557_, 0);
lean_inc(v_val_6691_);
lean_dec_ref_known(v_M_6557_, 1);
v___y_6679_ = v_tz_6688_;
v___y_6680_ = v_val_6691_;
goto v___jp_6678_;
}
}
v___jp_6692_:
{
if (lean_obj_tag(v_zabbrev_6575_) == 0)
{
lean_object* v___x_6696_; lean_object* v___x_6697_; 
v___x_6696_ = lean_box(0);
v___x_6697_ = lean_apply_1(v___y_6693_, v___x_6696_);
v___y_6684_ = v___y_6694_;
v___y_6685_ = v___y_6695_;
v___y_6686_ = v___x_6697_;
goto v___jp_6683_;
}
else
{
lean_object* v_val_6698_; 
lean_dec_ref(v___y_6693_);
v_val_6698_ = lean_ctor_get(v_zabbrev_6575_, 0);
lean_inc(v_val_6698_);
lean_dec_ref_known(v_zabbrev_6575_, 1);
v___y_6684_ = v___y_6694_;
v___y_6685_ = v___y_6695_;
v___y_6686_ = v_val_6698_;
goto v___jp_6683_;
}
}
v___jp_6699_:
{
lean_object* v___f_6701_; 
lean_inc(v___y_6700_);
v___f_6701_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1), 2, 1);
lean_closure_set(v___f_6701_, 0, v___y_6700_);
if (lean_obj_tag(v_V_6573_) == 0)
{
if (lean_obj_tag(v_v_6576_) == 0)
{
if (lean_obj_tag(v_z_6574_) == 0)
{
lean_object* v___x_6702_; lean_object* v___x_6703_; 
v___x_6702_ = lean_box(0);
lean_inc(v___y_6700_);
v___x_6703_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(v___y_6700_, v___x_6702_);
v___y_6693_ = v___f_6701_;
v___y_6694_ = v___y_6700_;
v___y_6695_ = v___x_6703_;
goto v___jp_6692_;
}
else
{
lean_object* v_val_6704_; 
v_val_6704_ = lean_ctor_get(v_z_6574_, 0);
lean_inc(v_val_6704_);
lean_dec_ref_known(v_z_6574_, 1);
v___y_6693_ = v___f_6701_;
v___y_6694_ = v___y_6700_;
v___y_6695_ = v_val_6704_;
goto v___jp_6692_;
}
}
else
{
lean_object* v_val_6705_; 
lean_dec(v_z_6574_);
v_val_6705_ = lean_ctor_get(v_v_6576_, 0);
lean_inc(v_val_6705_);
lean_dec_ref_known(v_v_6576_, 1);
v___y_6693_ = v___f_6701_;
v___y_6694_ = v___y_6700_;
v___y_6695_ = v_val_6705_;
goto v___jp_6692_;
}
}
else
{
lean_object* v_val_6706_; 
lean_dec(v_v_6576_);
lean_dec(v_z_6574_);
v_val_6706_ = lean_ctor_get(v_V_6573_, 0);
lean_inc(v_val_6706_);
lean_dec_ref_known(v_V_6573_, 1);
v___y_6693_ = v___f_6701_;
v___y_6694_ = v___y_6700_;
v___y_6695_ = v_val_6706_;
goto v___jp_6692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object* v_date_6712_, lean_object* v_config_6713_, lean_object* v_mod_6714_, lean_object* v_a_6715_){
_start:
{
if (lean_obj_tag(v_mod_6714_) == 0)
{
lean_object* v_val_6716_; lean_object* v___x_6717_; 
lean_dec_ref(v_config_6713_);
v_val_6716_ = lean_ctor_get(v_mod_6714_, 0);
lean_inc_ref(v_val_6716_);
lean_dec_ref_known(v_mod_6714_, 1);
v___x_6717_ = l_Std_Internal_Parsec_String_pstring(v_val_6716_, v_a_6715_);
if (lean_obj_tag(v___x_6717_) == 0)
{
lean_object* v_pos_6718_; lean_object* v___x_6720_; uint8_t v_isShared_6721_; uint8_t v_isSharedCheck_6725_; 
v_pos_6718_ = lean_ctor_get(v___x_6717_, 0);
v_isSharedCheck_6725_ = !lean_is_exclusive(v___x_6717_);
if (v_isSharedCheck_6725_ == 0)
{
lean_object* v_unused_6726_; 
v_unused_6726_ = lean_ctor_get(v___x_6717_, 1);
lean_dec(v_unused_6726_);
v___x_6720_ = v___x_6717_;
v_isShared_6721_ = v_isSharedCheck_6725_;
goto v_resetjp_6719_;
}
else
{
lean_inc(v_pos_6718_);
lean_dec(v___x_6717_);
v___x_6720_ = lean_box(0);
v_isShared_6721_ = v_isSharedCheck_6725_;
goto v_resetjp_6719_;
}
v_resetjp_6719_:
{
lean_object* v___x_6723_; 
if (v_isShared_6721_ == 0)
{
lean_ctor_set(v___x_6720_, 1, v_date_6712_);
v___x_6723_ = v___x_6720_;
goto v_reusejp_6722_;
}
else
{
lean_object* v_reuseFailAlloc_6724_; 
v_reuseFailAlloc_6724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6724_, 0, v_pos_6718_);
lean_ctor_set(v_reuseFailAlloc_6724_, 1, v_date_6712_);
v___x_6723_ = v_reuseFailAlloc_6724_;
goto v_reusejp_6722_;
}
v_reusejp_6722_:
{
return v___x_6723_;
}
}
}
else
{
lean_object* v_pos_6727_; lean_object* v_err_6728_; lean_object* v___x_6730_; uint8_t v_isShared_6731_; uint8_t v_isSharedCheck_6735_; 
lean_dec_ref(v_date_6712_);
v_pos_6727_ = lean_ctor_get(v___x_6717_, 0);
v_err_6728_ = lean_ctor_get(v___x_6717_, 1);
v_isSharedCheck_6735_ = !lean_is_exclusive(v___x_6717_);
if (v_isSharedCheck_6735_ == 0)
{
v___x_6730_ = v___x_6717_;
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
else
{
lean_inc(v_err_6728_);
lean_inc(v_pos_6727_);
lean_dec(v___x_6717_);
v___x_6730_ = lean_box(0);
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
v_resetjp_6729_:
{
lean_object* v___x_6733_; 
if (v_isShared_6731_ == 0)
{
v___x_6733_ = v___x_6730_;
goto v_reusejp_6732_;
}
else
{
lean_object* v_reuseFailAlloc_6734_; 
v_reuseFailAlloc_6734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6734_, 0, v_pos_6727_);
lean_ctor_set(v_reuseFailAlloc_6734_, 1, v_err_6728_);
v___x_6733_ = v_reuseFailAlloc_6734_;
goto v_reusejp_6732_;
}
v_reusejp_6732_:
{
return v___x_6733_;
}
}
}
}
else
{
lean_object* v_modifier_6736_; lean_object* v___x_6737_; 
v_modifier_6736_ = lean_ctor_get(v_mod_6714_, 0);
lean_inc_ref_n(v_modifier_6736_, 2);
lean_dec_ref_known(v_mod_6714_, 1);
v___x_6737_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6713_, v_modifier_6736_, v_a_6715_);
if (lean_obj_tag(v___x_6737_) == 0)
{
lean_object* v_pos_6738_; lean_object* v_res_6739_; lean_object* v___x_6741_; uint8_t v_isShared_6742_; uint8_t v_isSharedCheck_6747_; 
v_pos_6738_ = lean_ctor_get(v___x_6737_, 0);
v_res_6739_ = lean_ctor_get(v___x_6737_, 1);
v_isSharedCheck_6747_ = !lean_is_exclusive(v___x_6737_);
if (v_isSharedCheck_6747_ == 0)
{
v___x_6741_ = v___x_6737_;
v_isShared_6742_ = v_isSharedCheck_6747_;
goto v_resetjp_6740_;
}
else
{
lean_inc(v_res_6739_);
lean_inc(v_pos_6738_);
lean_dec(v___x_6737_);
v___x_6741_ = lean_box(0);
v_isShared_6742_ = v_isSharedCheck_6747_;
goto v_resetjp_6740_;
}
v_resetjp_6740_:
{
lean_object* v___x_6743_; lean_object* v___x_6745_; 
v___x_6743_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(v_date_6712_, v_modifier_6736_, v_res_6739_);
if (v_isShared_6742_ == 0)
{
lean_ctor_set(v___x_6741_, 1, v___x_6743_);
v___x_6745_ = v___x_6741_;
goto v_reusejp_6744_;
}
else
{
lean_object* v_reuseFailAlloc_6746_; 
v_reuseFailAlloc_6746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6746_, 0, v_pos_6738_);
lean_ctor_set(v_reuseFailAlloc_6746_, 1, v___x_6743_);
v___x_6745_ = v_reuseFailAlloc_6746_;
goto v_reusejp_6744_;
}
v_reusejp_6744_:
{
return v___x_6745_;
}
}
}
else
{
lean_object* v_pos_6748_; lean_object* v_err_6749_; lean_object* v___x_6751_; uint8_t v_isShared_6752_; uint8_t v_isSharedCheck_6756_; 
lean_dec_ref(v_modifier_6736_);
lean_dec_ref(v_date_6712_);
v_pos_6748_ = lean_ctor_get(v___x_6737_, 0);
v_err_6749_ = lean_ctor_get(v___x_6737_, 1);
v_isSharedCheck_6756_ = !lean_is_exclusive(v___x_6737_);
if (v_isSharedCheck_6756_ == 0)
{
v___x_6751_ = v___x_6737_;
v_isShared_6752_ = v_isSharedCheck_6756_;
goto v_resetjp_6750_;
}
else
{
lean_inc(v_err_6749_);
lean_inc(v_pos_6748_);
lean_dec(v___x_6737_);
v___x_6751_ = lean_box(0);
v_isShared_6752_ = v_isSharedCheck_6756_;
goto v_resetjp_6750_;
}
v_resetjp_6750_:
{
lean_object* v___x_6754_; 
if (v_isShared_6752_ == 0)
{
v___x_6754_ = v___x_6751_;
goto v_reusejp_6753_;
}
else
{
lean_object* v_reuseFailAlloc_6755_; 
v_reuseFailAlloc_6755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6755_, 0, v_pos_6748_);
lean_ctor_set(v_reuseFailAlloc_6755_, 1, v_err_6749_);
v___x_6754_ = v_reuseFailAlloc_6755_;
goto v_reusejp_6753_;
}
v_reusejp_6753_:
{
return v___x_6754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object* v_input_6757_, lean_object* v_config_6758_){
_start:
{
lean_object* v___x_6759_; lean_object* v___x_6760_; 
v___x_6759_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6760_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6759_, v_input_6757_);
if (lean_obj_tag(v___x_6760_) == 0)
{
lean_object* v_a_6761_; lean_object* v___x_6763_; uint8_t v_isShared_6764_; uint8_t v_isSharedCheck_6768_; 
lean_dec_ref(v_config_6758_);
v_a_6761_ = lean_ctor_get(v___x_6760_, 0);
v_isSharedCheck_6768_ = !lean_is_exclusive(v___x_6760_);
if (v_isSharedCheck_6768_ == 0)
{
v___x_6763_ = v___x_6760_;
v_isShared_6764_ = v_isSharedCheck_6768_;
goto v_resetjp_6762_;
}
else
{
lean_inc(v_a_6761_);
lean_dec(v___x_6760_);
v___x_6763_ = lean_box(0);
v_isShared_6764_ = v_isSharedCheck_6768_;
goto v_resetjp_6762_;
}
v_resetjp_6762_:
{
lean_object* v___x_6766_; 
if (v_isShared_6764_ == 0)
{
v___x_6766_ = v___x_6763_;
goto v_reusejp_6765_;
}
else
{
lean_object* v_reuseFailAlloc_6767_; 
v_reuseFailAlloc_6767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6767_, 0, v_a_6761_);
v___x_6766_ = v_reuseFailAlloc_6767_;
goto v_reusejp_6765_;
}
v_reusejp_6765_:
{
return v___x_6766_;
}
}
}
else
{
lean_object* v_a_6769_; lean_object* v___x_6771_; uint8_t v_isShared_6772_; uint8_t v_isSharedCheck_6777_; 
v_a_6769_ = lean_ctor_get(v___x_6760_, 0);
v_isSharedCheck_6777_ = !lean_is_exclusive(v___x_6760_);
if (v_isSharedCheck_6777_ == 0)
{
v___x_6771_ = v___x_6760_;
v_isShared_6772_ = v_isSharedCheck_6777_;
goto v_resetjp_6770_;
}
else
{
lean_inc(v_a_6769_);
lean_dec(v___x_6760_);
v___x_6771_ = lean_box(0);
v_isShared_6772_ = v_isSharedCheck_6777_;
goto v_resetjp_6770_;
}
v_resetjp_6770_:
{
lean_object* v___x_6773_; lean_object* v___x_6775_; 
v___x_6773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6773_, 0, v_config_6758_);
lean_ctor_set(v___x_6773_, 1, v_a_6769_);
if (v_isShared_6772_ == 0)
{
lean_ctor_set(v___x_6771_, 0, v___x_6773_);
v___x_6775_ = v___x_6771_;
goto v_reusejp_6774_;
}
else
{
lean_object* v_reuseFailAlloc_6776_; 
v_reuseFailAlloc_6776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6776_, 0, v___x_6773_);
v___x_6775_ = v_reuseFailAlloc_6776_;
goto v_reusejp_6774_;
}
v_reusejp_6774_:
{
return v___x_6775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object* v_tz_6778_, lean_object* v_input_6779_, lean_object* v_config_6780_){
_start:
{
lean_object* v___x_6781_; 
v___x_6781_ = l_Std_Time_GenericFormat_spec___redArg(v_input_6779_, v_config_6780_);
return v___x_6781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object* v_tz_6782_, lean_object* v_input_6783_, lean_object* v_config_6784_){
_start:
{
lean_object* v_res_6785_; 
v_res_6785_ = l_Std_Time_GenericFormat_spec(v_tz_6782_, v_input_6783_, v_config_6784_);
lean_dec(v_tz_6782_);
return v_res_6785_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(lean_object* v_msg_6786_){
_start:
{
lean_object* v___x_6787_; lean_object* v___x_6788_; 
v___x_6787_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
v___x_6788_ = lean_panic_fn_borrowed(v___x_6787_, v_msg_6786_);
return v___x_6788_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object* v_tz_6789_, lean_object* v_msg_6790_){
_start:
{
lean_object* v___x_6791_; 
v___x_6791_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v_msg_6790_);
return v___x_6791_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object* v_tz_6792_, lean_object* v_msg_6793_){
_start:
{
lean_object* v_res_6794_; 
v_res_6794_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6792_, v_msg_6793_);
lean_dec(v_tz_6792_);
return v_res_6794_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object* v_tz_6797_, lean_object* v_input_6798_, lean_object* v_config_6799_){
_start:
{
lean_object* v___x_6800_; lean_object* v___x_6801_; 
v___x_6800_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6801_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6800_, v_input_6798_);
if (lean_obj_tag(v___x_6801_) == 0)
{
lean_object* v_a_6802_; lean_object* v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6805_; lean_object* v___x_6806_; lean_object* v___x_6807_; lean_object* v___x_6808_; 
lean_dec_ref(v_config_6799_);
v_a_6802_ = lean_ctor_get(v___x_6801_, 0);
lean_inc(v_a_6802_);
lean_dec_ref_known(v___x_6801_, 1);
v___x_6803_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6804_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__1));
v___x_6805_ = lean_unsigned_to_nat(1071u);
v___x_6806_ = lean_unsigned_to_nat(18u);
v___x_6807_ = l_mkPanicMessageWithDecl(v___x_6803_, v___x_6804_, v___x_6805_, v___x_6806_, v_a_6802_);
lean_dec(v_a_6802_);
v___x_6808_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v___x_6807_);
return v___x_6808_;
}
else
{
lean_object* v_a_6809_; lean_object* v___x_6810_; 
v_a_6809_ = lean_ctor_get(v___x_6801_, 0);
lean_inc(v_a_6809_);
lean_dec_ref_known(v___x_6801_, 1);
v___x_6810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6810_, 0, v_config_6799_);
lean_ctor_set(v___x_6810_, 1, v_a_6809_);
return v___x_6810_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object* v_tz_6811_, lean_object* v_input_6812_, lean_object* v_config_6813_){
_start:
{
lean_object* v_res_6814_; 
v_res_6814_ = l_Std_Time_GenericFormat_spec_x21(v_tz_6811_, v_input_6812_, v_config_6813_);
lean_dec(v_tz_6811_);
return v_res_6814_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(lean_object* v_x_6815_, lean_object* v_x_6816_){
_start:
{
if (lean_obj_tag(v_x_6816_) == 0)
{
return v_x_6815_;
}
else
{
lean_object* v_head_6817_; lean_object* v_tail_6818_; lean_object* v___x_6819_; 
v_head_6817_ = lean_ctor_get(v_x_6816_, 0);
v_tail_6818_ = lean_ctor_get(v_x_6816_, 1);
v___x_6819_ = lean_string_append(v_x_6815_, v_head_6817_);
v_x_6815_ = v___x_6819_;
v_x_6816_ = v_tail_6818_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1___boxed(lean_object* v_x_6821_, lean_object* v_x_6822_){
_start:
{
lean_object* v_res_6823_; 
v_res_6823_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v_x_6821_, v_x_6822_);
lean_dec(v_x_6822_);
return v_res_6823_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(lean_object* v_tz_6824_, lean_object* v_timestamp_6825_, lean_object* v___x_6826_, lean_object* v_x_6827_){
_start:
{
lean_object* v_offset_6828_; lean_object* v_second_6829_; lean_object* v_nano_6830_; lean_object* v___x_6831_; lean_object* v___x_6832_; lean_object* v___x_6833_; lean_object* v_nanos_6834_; lean_object* v___x_6835_; lean_object* v_nanos_6836_; lean_object* v___x_6837_; lean_object* v___x_6838_; lean_object* v___x_6839_; 
v_offset_6828_ = lean_ctor_get(v_tz_6824_, 0);
v_second_6829_ = lean_ctor_get(v_timestamp_6825_, 0);
v_nano_6830_ = lean_ctor_get(v_timestamp_6825_, 1);
v___x_6831_ = lean_nat_to_int(v___x_6826_);
v___x_6832_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6833_ = lean_int_mul(v_second_6829_, v___x_6832_);
v_nanos_6834_ = lean_int_add(v___x_6833_, v_nano_6830_);
lean_dec(v___x_6833_);
v___x_6835_ = lean_int_mul(v_offset_6828_, v___x_6832_);
v_nanos_6836_ = lean_int_add(v___x_6835_, v___x_6831_);
lean_dec(v___x_6831_);
lean_dec(v___x_6835_);
v___x_6837_ = lean_int_add(v_nanos_6834_, v_nanos_6836_);
lean_dec(v_nanos_6836_);
lean_dec(v_nanos_6834_);
v___x_6838_ = l_Std_Time_Duration_ofNanoseconds(v___x_6837_);
lean_dec(v___x_6837_);
v___x_6839_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_6838_);
return v___x_6839_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed(lean_object* v_tz_6840_, lean_object* v_timestamp_6841_, lean_object* v___x_6842_, lean_object* v_x_6843_){
_start:
{
lean_object* v_res_6844_; 
v_res_6844_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(v_tz_6840_, v_timestamp_6841_, v___x_6842_, v_x_6843_);
lean_dec_ref(v_timestamp_6841_);
lean_dec_ref(v_tz_6840_);
return v_res_6844_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(lean_object* v_aw_6845_, lean_object* v_date_6846_, lean_object* v_dateformat_6847_, lean_object* v_a_6848_, lean_object* v_a_6849_){
_start:
{
if (lean_obj_tag(v_a_6848_) == 0)
{
lean_object* v___x_6850_; 
lean_dec_ref(v_date_6846_);
v___x_6850_ = l_List_reverse___redArg(v_a_6849_);
return v___x_6850_;
}
else
{
lean_object* v_head_6851_; lean_object* v_tail_6852_; lean_object* v___x_6854_; uint8_t v_isShared_6855_; uint8_t v_isSharedCheck_6881_; 
v_head_6851_ = lean_ctor_get(v_a_6848_, 0);
v_tail_6852_ = lean_ctor_get(v_a_6848_, 1);
v_isSharedCheck_6881_ = !lean_is_exclusive(v_a_6848_);
if (v_isSharedCheck_6881_ == 0)
{
v___x_6854_ = v_a_6848_;
v_isShared_6855_ = v_isSharedCheck_6881_;
goto v_resetjp_6853_;
}
else
{
lean_inc(v_tail_6852_);
lean_inc(v_head_6851_);
lean_dec(v_a_6848_);
v___x_6854_ = lean_box(0);
v_isShared_6855_ = v_isSharedCheck_6881_;
goto v_resetjp_6853_;
}
v_resetjp_6853_:
{
lean_object* v___y_6857_; 
if (lean_obj_tag(v_aw_6845_) == 0)
{
lean_object* v_a_6862_; lean_object* v_offset_6863_; lean_object* v_name_6864_; lean_object* v_abbreviation_6865_; uint8_t v_isDST_6866_; lean_object* v_timestamp_6867_; uint8_t v___x_6868_; uint8_t v___x_6869_; lean_object* v_ltt_6870_; lean_object* v___x_6871_; lean_object* v___x_6872_; lean_object* v___x_6873_; lean_object* v___x_6874_; lean_object* v_tz_6875_; lean_object* v___f_6876_; lean_object* v___x_6877_; lean_object* v___x_6878_; lean_object* v___x_6879_; 
v_a_6862_ = lean_ctor_get(v_aw_6845_, 0);
v_offset_6863_ = lean_ctor_get(v_a_6862_, 0);
v_name_6864_ = lean_ctor_get(v_a_6862_, 1);
v_abbreviation_6865_ = lean_ctor_get(v_a_6862_, 2);
v_isDST_6866_ = lean_ctor_get_uint8(v_a_6862_, sizeof(void*)*3);
v_timestamp_6867_ = lean_ctor_get(v_date_6846_, 1);
v___x_6868_ = 0;
v___x_6869_ = 1;
lean_inc_ref(v_name_6864_);
lean_inc_ref(v_abbreviation_6865_);
lean_inc(v_offset_6863_);
v_ltt_6870_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6870_, 0, v_offset_6863_);
lean_ctor_set(v_ltt_6870_, 1, v_abbreviation_6865_);
lean_ctor_set(v_ltt_6870_, 2, v_name_6864_);
lean_ctor_set_uint8(v_ltt_6870_, sizeof(void*)*3, v_isDST_6866_);
lean_ctor_set_uint8(v_ltt_6870_, sizeof(void*)*3 + 1, v___x_6868_);
lean_ctor_set_uint8(v_ltt_6870_, sizeof(void*)*3 + 2, v___x_6869_);
v___x_6871_ = lean_unsigned_to_nat(0u);
v___x_6872_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6873_ = lean_box(0);
v___x_6874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6874_, 0, v_ltt_6870_);
lean_ctor_set(v___x_6874_, 1, v___x_6872_);
lean_ctor_set(v___x_6874_, 2, v___x_6873_);
lean_inc_ref(v___x_6874_);
v_tz_6875_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_6874_, v_timestamp_6867_);
lean_inc_ref_n(v_timestamp_6867_, 2);
lean_inc_ref(v_tz_6875_);
v___f_6876_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_6876_, 0, v_tz_6875_);
lean_closure_set(v___f_6876_, 1, v_timestamp_6867_);
lean_closure_set(v___f_6876_, 2, v___x_6871_);
v___x_6877_ = lean_mk_thunk(v___f_6876_);
v___x_6878_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6878_, 0, v___x_6877_);
lean_ctor_set(v___x_6878_, 1, v_timestamp_6867_);
lean_ctor_set(v___x_6878_, 2, v___x_6874_);
lean_ctor_set(v___x_6878_, 3, v_tz_6875_);
v___x_6879_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6847_, v___x_6878_, v_head_6851_);
v___y_6857_ = v___x_6879_;
goto v___jp_6856_;
}
else
{
lean_object* v___x_6880_; 
lean_inc_ref(v_date_6846_);
v___x_6880_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6847_, v_date_6846_, v_head_6851_);
v___y_6857_ = v___x_6880_;
goto v___jp_6856_;
}
v___jp_6856_:
{
lean_object* v___x_6859_; 
if (v_isShared_6855_ == 0)
{
lean_ctor_set(v___x_6854_, 1, v_a_6849_);
lean_ctor_set(v___x_6854_, 0, v___y_6857_);
v___x_6859_ = v___x_6854_;
goto v_reusejp_6858_;
}
else
{
lean_object* v_reuseFailAlloc_6861_; 
v_reuseFailAlloc_6861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6861_, 0, v___y_6857_);
lean_ctor_set(v_reuseFailAlloc_6861_, 1, v_a_6849_);
v___x_6859_ = v_reuseFailAlloc_6861_;
goto v_reusejp_6858_;
}
v_reusejp_6858_:
{
v_a_6848_ = v_tail_6852_;
v_a_6849_ = v___x_6859_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0___boxed(lean_object* v_aw_6882_, lean_object* v_date_6883_, lean_object* v_dateformat_6884_, lean_object* v_a_6885_, lean_object* v_a_6886_){
_start:
{
lean_object* v_res_6887_; 
v_res_6887_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(v_aw_6882_, v_date_6883_, v_dateformat_6884_, v_a_6885_, v_a_6886_);
lean_dec_ref(v_dateformat_6884_);
lean_dec(v_aw_6882_);
return v_res_6887_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(lean_object* v_aw_6888_, lean_object* v_date_6889_, lean_object* v_dateformat_6890_, lean_object* v_a_6891_, lean_object* v_a_6892_){
_start:
{
if (lean_obj_tag(v_a_6891_) == 0)
{
lean_object* v___x_6893_; 
lean_dec_ref(v_date_6889_);
v___x_6893_ = l_List_reverse___redArg(v_a_6892_);
return v___x_6893_;
}
else
{
lean_object* v_head_6894_; lean_object* v_tail_6895_; lean_object* v___x_6897_; uint8_t v_isShared_6898_; uint8_t v_isSharedCheck_6924_; 
v_head_6894_ = lean_ctor_get(v_a_6891_, 0);
v_tail_6895_ = lean_ctor_get(v_a_6891_, 1);
v_isSharedCheck_6924_ = !lean_is_exclusive(v_a_6891_);
if (v_isSharedCheck_6924_ == 0)
{
v___x_6897_ = v_a_6891_;
v_isShared_6898_ = v_isSharedCheck_6924_;
goto v_resetjp_6896_;
}
else
{
lean_inc(v_tail_6895_);
lean_inc(v_head_6894_);
lean_dec(v_a_6891_);
v___x_6897_ = lean_box(0);
v_isShared_6898_ = v_isSharedCheck_6924_;
goto v_resetjp_6896_;
}
v_resetjp_6896_:
{
lean_object* v___y_6900_; 
if (lean_obj_tag(v_aw_6888_) == 0)
{
lean_object* v_a_6905_; lean_object* v_offset_6906_; lean_object* v_name_6907_; lean_object* v_abbreviation_6908_; uint8_t v_isDST_6909_; lean_object* v_timestamp_6910_; uint8_t v___x_6911_; uint8_t v___x_6912_; lean_object* v_ltt_6913_; lean_object* v___x_6914_; lean_object* v___x_6915_; lean_object* v___x_6916_; lean_object* v___x_6917_; lean_object* v_tz_6918_; lean_object* v___f_6919_; lean_object* v___x_6920_; lean_object* v___x_6921_; lean_object* v___x_6922_; 
v_a_6905_ = lean_ctor_get(v_aw_6888_, 0);
v_offset_6906_ = lean_ctor_get(v_a_6905_, 0);
v_name_6907_ = lean_ctor_get(v_a_6905_, 1);
v_abbreviation_6908_ = lean_ctor_get(v_a_6905_, 2);
v_isDST_6909_ = lean_ctor_get_uint8(v_a_6905_, sizeof(void*)*3);
v_timestamp_6910_ = lean_ctor_get(v_date_6889_, 1);
v___x_6911_ = 0;
v___x_6912_ = 1;
lean_inc_ref(v_name_6907_);
lean_inc_ref(v_abbreviation_6908_);
lean_inc(v_offset_6906_);
v_ltt_6913_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6913_, 0, v_offset_6906_);
lean_ctor_set(v_ltt_6913_, 1, v_abbreviation_6908_);
lean_ctor_set(v_ltt_6913_, 2, v_name_6907_);
lean_ctor_set_uint8(v_ltt_6913_, sizeof(void*)*3, v_isDST_6909_);
lean_ctor_set_uint8(v_ltt_6913_, sizeof(void*)*3 + 1, v___x_6911_);
lean_ctor_set_uint8(v_ltt_6913_, sizeof(void*)*3 + 2, v___x_6912_);
v___x_6914_ = lean_unsigned_to_nat(0u);
v___x_6915_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6916_ = lean_box(0);
v___x_6917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6917_, 0, v_ltt_6913_);
lean_ctor_set(v___x_6917_, 1, v___x_6915_);
lean_ctor_set(v___x_6917_, 2, v___x_6916_);
lean_inc_ref(v___x_6917_);
v_tz_6918_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_6917_, v_timestamp_6910_);
lean_inc_ref_n(v_timestamp_6910_, 2);
lean_inc_ref(v_tz_6918_);
v___f_6919_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_6919_, 0, v_tz_6918_);
lean_closure_set(v___f_6919_, 1, v_timestamp_6910_);
lean_closure_set(v___f_6919_, 2, v___x_6914_);
v___x_6920_ = lean_mk_thunk(v___f_6919_);
v___x_6921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6921_, 0, v___x_6920_);
lean_ctor_set(v___x_6921_, 1, v_timestamp_6910_);
lean_ctor_set(v___x_6921_, 2, v___x_6917_);
lean_ctor_set(v___x_6921_, 3, v_tz_6918_);
v___x_6922_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6890_, v___x_6921_, v_head_6894_);
v___y_6900_ = v___x_6922_;
goto v___jp_6899_;
}
else
{
lean_object* v___x_6923_; 
lean_inc_ref(v_date_6889_);
v___x_6923_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6890_, v_date_6889_, v_head_6894_);
v___y_6900_ = v___x_6923_;
goto v___jp_6899_;
}
v___jp_6899_:
{
lean_object* v___x_6902_; 
if (v_isShared_6898_ == 0)
{
lean_ctor_set(v___x_6897_, 1, v_a_6892_);
lean_ctor_set(v___x_6897_, 0, v___y_6900_);
v___x_6902_ = v___x_6897_;
goto v_reusejp_6901_;
}
else
{
lean_object* v_reuseFailAlloc_6904_; 
v_reuseFailAlloc_6904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6904_, 0, v___y_6900_);
lean_ctor_set(v_reuseFailAlloc_6904_, 1, v_a_6892_);
v___x_6902_ = v_reuseFailAlloc_6904_;
goto v_reusejp_6901_;
}
v_reusejp_6901_:
{
lean_object* v___x_6903_; 
v___x_6903_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(v_aw_6888_, v_date_6889_, v_dateformat_6890_, v_tail_6895_, v___x_6902_);
return v___x_6903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___boxed(lean_object* v_aw_6925_, lean_object* v_date_6926_, lean_object* v_dateformat_6927_, lean_object* v_a_6928_, lean_object* v_a_6929_){
_start:
{
lean_object* v_res_6930_; 
v_res_6930_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6925_, v_date_6926_, v_dateformat_6927_, v_a_6928_, v_a_6929_);
lean_dec_ref(v_dateformat_6927_);
lean_dec(v_aw_6925_);
return v_res_6930_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object* v_aw_6931_, lean_object* v_format_6932_, lean_object* v_date_6933_){
_start:
{
lean_object* v_config_6934_; lean_object* v_string_6935_; lean_object* v_dateformat_6936_; lean_object* v___x_6937_; lean_object* v___x_6938_; lean_object* v___x_6939_; lean_object* v___x_6940_; 
v_config_6934_ = lean_ctor_get(v_format_6932_, 0);
lean_inc_ref(v_config_6934_);
v_string_6935_ = lean_ctor_get(v_format_6932_, 1);
lean_inc(v_string_6935_);
lean_dec_ref(v_format_6932_);
v_dateformat_6936_ = lean_ctor_get(v_config_6934_, 0);
lean_inc_ref(v_dateformat_6936_);
lean_dec_ref(v_config_6934_);
v___x_6937_ = lean_box(0);
v___x_6938_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6931_, v_date_6933_, v_dateformat_6936_, v_string_6935_, v___x_6937_);
lean_dec_ref(v_dateformat_6936_);
v___x_6939_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_6940_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v___x_6939_, v___x_6938_);
lean_dec(v___x_6938_);
return v___x_6940_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object* v_aw_6941_, lean_object* v_format_6942_, lean_object* v_date_6943_){
_start:
{
lean_object* v_res_6944_; 
v_res_6944_ = l_Std_Time_GenericFormat_format(v_aw_6941_, v_format_6942_, v_date_6943_);
lean_dec(v_aw_6941_);
return v_res_6944_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object* v_config_6948_, lean_object* v_aw_6949_, lean_object* v_builder_6950_, lean_object* v_x_6951_, lean_object* v_a_6952_){
_start:
{
if (lean_obj_tag(v_x_6951_) == 0)
{
lean_object* v___x_6953_; 
lean_dec_ref(v_config_6948_);
v___x_6953_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_6950_, v_aw_6949_);
if (lean_obj_tag(v___x_6953_) == 0)
{
lean_object* v___x_6954_; lean_object* v___x_6955_; 
v___x_6954_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1));
v___x_6955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6955_, 0, v_a_6952_);
lean_ctor_set(v___x_6955_, 1, v___x_6954_);
return v___x_6955_;
}
else
{
lean_object* v_val_6956_; lean_object* v___x_6957_; 
v_val_6956_ = lean_ctor_get(v___x_6953_, 0);
lean_inc(v_val_6956_);
lean_dec_ref_known(v___x_6953_, 1);
v___x_6957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6957_, 0, v_a_6952_);
lean_ctor_set(v___x_6957_, 1, v_val_6956_);
return v___x_6957_;
}
}
else
{
lean_object* v_head_6958_; lean_object* v_tail_6959_; lean_object* v___x_6960_; 
v_head_6958_ = lean_ctor_get(v_x_6951_, 0);
lean_inc(v_head_6958_);
v_tail_6959_ = lean_ctor_get(v_x_6951_, 1);
lean_inc(v_tail_6959_);
lean_dec_ref_known(v_x_6951_, 2);
lean_inc_ref(v_config_6948_);
v___x_6960_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(v_builder_6950_, v_config_6948_, v_head_6958_, v_a_6952_);
if (lean_obj_tag(v___x_6960_) == 0)
{
lean_object* v_pos_6961_; lean_object* v_res_6962_; 
v_pos_6961_ = lean_ctor_get(v___x_6960_, 0);
lean_inc(v_pos_6961_);
v_res_6962_ = lean_ctor_get(v___x_6960_, 1);
lean_inc(v_res_6962_);
lean_dec_ref_known(v___x_6960_, 2);
v_builder_6950_ = v_res_6962_;
v_x_6951_ = v_tail_6959_;
v_a_6952_ = v_pos_6961_;
goto _start;
}
else
{
lean_object* v_pos_6964_; lean_object* v_err_6965_; lean_object* v___x_6967_; uint8_t v_isShared_6968_; uint8_t v_isSharedCheck_6972_; 
lean_dec(v_tail_6959_);
lean_dec(v_aw_6949_);
lean_dec_ref(v_config_6948_);
v_pos_6964_ = lean_ctor_get(v___x_6960_, 0);
v_err_6965_ = lean_ctor_get(v___x_6960_, 1);
v_isSharedCheck_6972_ = !lean_is_exclusive(v___x_6960_);
if (v_isSharedCheck_6972_ == 0)
{
v___x_6967_ = v___x_6960_;
v_isShared_6968_ = v_isSharedCheck_6972_;
goto v_resetjp_6966_;
}
else
{
lean_inc(v_err_6965_);
lean_inc(v_pos_6964_);
lean_dec(v___x_6960_);
v___x_6967_ = lean_box(0);
v_isShared_6968_ = v_isSharedCheck_6972_;
goto v_resetjp_6966_;
}
v_resetjp_6966_:
{
lean_object* v___x_6970_; 
if (v_isShared_6968_ == 0)
{
v___x_6970_ = v___x_6967_;
goto v_reusejp_6969_;
}
else
{
lean_object* v_reuseFailAlloc_6971_; 
v_reuseFailAlloc_6971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6971_, 0, v_pos_6964_);
lean_ctor_set(v_reuseFailAlloc_6971_, 1, v_err_6965_);
v___x_6970_ = v_reuseFailAlloc_6971_;
goto v_reusejp_6969_;
}
v_reusejp_6969_:
{
return v___x_6970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object* v_format_6975_, lean_object* v_config_6976_, lean_object* v_aw_6977_, lean_object* v_a_6978_){
_start:
{
lean_object* v___x_6979_; lean_object* v___x_6980_; 
v___x_6979_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0));
v___x_6980_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(v_config_6976_, v_aw_6977_, v___x_6979_, v_format_6975_, v_a_6978_);
return v___x_6980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object* v_config_6984_, lean_object* v_format_6985_, lean_object* v_func_6986_, lean_object* v_a_6987_){
_start:
{
if (lean_obj_tag(v_format_6985_) == 0)
{
lean_dec_ref(v_config_6984_);
if (lean_obj_tag(v_func_6986_) == 0)
{
lean_object* v___x_6988_; lean_object* v___x_6989_; 
v___x_6988_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1));
v___x_6989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6989_, 0, v_a_6987_);
lean_ctor_set(v___x_6989_, 1, v___x_6988_);
return v___x_6989_;
}
else
{
lean_object* v_val_6990_; lean_object* v_fst_6991_; lean_object* v_snd_6992_; lean_object* v___x_6993_; uint8_t v_decide_6994_; 
v_val_6990_ = lean_ctor_get(v_func_6986_, 0);
lean_inc(v_val_6990_);
lean_dec_ref_known(v_func_6986_, 1);
v_fst_6991_ = lean_ctor_get(v_a_6987_, 0);
v_snd_6992_ = lean_ctor_get(v_a_6987_, 1);
v___x_6993_ = lean_string_utf8_byte_size(v_fst_6991_);
v_decide_6994_ = lean_nat_dec_eq(v_snd_6992_, v___x_6993_);
if (v_decide_6994_ == 0)
{
lean_object* v___x_6995_; lean_object* v___x_6996_; 
lean_dec(v_val_6990_);
v___x_6995_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
v___x_6996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6996_, 0, v_a_6987_);
lean_ctor_set(v___x_6996_, 1, v___x_6995_);
return v___x_6996_;
}
else
{
lean_object* v___x_6997_; 
v___x_6997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6997_, 0, v_a_6987_);
lean_ctor_set(v___x_6997_, 1, v_val_6990_);
return v___x_6997_;
}
}
}
else
{
lean_object* v_head_6998_; 
v_head_6998_ = lean_ctor_get(v_format_6985_, 0);
lean_inc(v_head_6998_);
if (lean_obj_tag(v_head_6998_) == 0)
{
lean_object* v_tail_6999_; lean_object* v_val_7000_; lean_object* v___x_7001_; 
v_tail_6999_ = lean_ctor_get(v_format_6985_, 1);
lean_inc(v_tail_6999_);
lean_dec_ref_known(v_format_6985_, 2);
v_val_7000_ = lean_ctor_get(v_head_6998_, 0);
lean_inc_ref(v_val_7000_);
lean_dec_ref_known(v_head_6998_, 1);
v___x_7001_ = l_Std_Internal_Parsec_String_pstring(v_val_7000_, v_a_6987_);
if (lean_obj_tag(v___x_7001_) == 0)
{
lean_object* v_pos_7002_; 
v_pos_7002_ = lean_ctor_get(v___x_7001_, 0);
lean_inc(v_pos_7002_);
lean_dec_ref_known(v___x_7001_, 2);
v_format_6985_ = v_tail_6999_;
v_a_6987_ = v_pos_7002_;
goto _start;
}
else
{
lean_object* v_pos_7004_; lean_object* v_err_7005_; lean_object* v___x_7007_; uint8_t v_isShared_7008_; uint8_t v_isSharedCheck_7012_; 
lean_dec(v_tail_6999_);
lean_dec(v_func_6986_);
lean_dec_ref(v_config_6984_);
v_pos_7004_ = lean_ctor_get(v___x_7001_, 0);
v_err_7005_ = lean_ctor_get(v___x_7001_, 1);
v_isSharedCheck_7012_ = !lean_is_exclusive(v___x_7001_);
if (v_isSharedCheck_7012_ == 0)
{
v___x_7007_ = v___x_7001_;
v_isShared_7008_ = v_isSharedCheck_7012_;
goto v_resetjp_7006_;
}
else
{
lean_inc(v_err_7005_);
lean_inc(v_pos_7004_);
lean_dec(v___x_7001_);
v___x_7007_ = lean_box(0);
v_isShared_7008_ = v_isSharedCheck_7012_;
goto v_resetjp_7006_;
}
v_resetjp_7006_:
{
lean_object* v___x_7010_; 
if (v_isShared_7008_ == 0)
{
v___x_7010_ = v___x_7007_;
goto v_reusejp_7009_;
}
else
{
lean_object* v_reuseFailAlloc_7011_; 
v_reuseFailAlloc_7011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7011_, 0, v_pos_7004_);
lean_ctor_set(v_reuseFailAlloc_7011_, 1, v_err_7005_);
v___x_7010_ = v_reuseFailAlloc_7011_;
goto v_reusejp_7009_;
}
v_reusejp_7009_:
{
return v___x_7010_;
}
}
}
}
else
{
lean_object* v_tail_7013_; lean_object* v_modifier_7014_; lean_object* v___x_7015_; 
v_tail_7013_ = lean_ctor_get(v_format_6985_, 1);
lean_inc(v_tail_7013_);
lean_dec_ref_known(v_format_6985_, 2);
v_modifier_7014_ = lean_ctor_get(v_head_6998_, 0);
lean_inc_ref(v_modifier_7014_);
lean_dec_ref_known(v_head_6998_, 1);
lean_inc_ref(v_config_6984_);
v___x_7015_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6984_, v_modifier_7014_, v_a_6987_);
if (lean_obj_tag(v___x_7015_) == 0)
{
lean_object* v_pos_7016_; lean_object* v_res_7017_; lean_object* v___x_7018_; 
v_pos_7016_ = lean_ctor_get(v___x_7015_, 0);
lean_inc(v_pos_7016_);
v_res_7017_ = lean_ctor_get(v___x_7015_, 1);
lean_inc(v_res_7017_);
lean_dec_ref_known(v___x_7015_, 2);
v___x_7018_ = lean_apply_1(v_func_6986_, v_res_7017_);
v_format_6985_ = v_tail_7013_;
v_func_6986_ = v___x_7018_;
v_a_6987_ = v_pos_7016_;
goto _start;
}
else
{
lean_object* v_pos_7020_; lean_object* v_err_7021_; lean_object* v___x_7023_; uint8_t v_isShared_7024_; uint8_t v_isSharedCheck_7028_; 
lean_dec(v_tail_7013_);
lean_dec(v_func_6986_);
lean_dec_ref(v_config_6984_);
v_pos_7020_ = lean_ctor_get(v___x_7015_, 0);
v_err_7021_ = lean_ctor_get(v___x_7015_, 1);
v_isSharedCheck_7028_ = !lean_is_exclusive(v___x_7015_);
if (v_isSharedCheck_7028_ == 0)
{
v___x_7023_ = v___x_7015_;
v_isShared_7024_ = v_isSharedCheck_7028_;
goto v_resetjp_7022_;
}
else
{
lean_inc(v_err_7021_);
lean_inc(v_pos_7020_);
lean_dec(v___x_7015_);
v___x_7023_ = lean_box(0);
v_isShared_7024_ = v_isSharedCheck_7028_;
goto v_resetjp_7022_;
}
v_resetjp_7022_:
{
lean_object* v___x_7026_; 
if (v_isShared_7024_ == 0)
{
v___x_7026_ = v___x_7023_;
goto v_reusejp_7025_;
}
else
{
lean_object* v_reuseFailAlloc_7027_; 
v_reuseFailAlloc_7027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7027_, 0, v_pos_7020_);
lean_ctor_set(v_reuseFailAlloc_7027_, 1, v_err_7021_);
v___x_7026_ = v_reuseFailAlloc_7027_;
goto v_reusejp_7025_;
}
v_reusejp_7025_:
{
return v___x_7026_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object* v_00_u03b1_7029_, lean_object* v_config_7030_, lean_object* v_format_7031_, lean_object* v_func_7032_, lean_object* v_a_7033_){
_start:
{
lean_object* v___x_7034_; 
v___x_7034_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7030_, v_format_7031_, v_func_7032_, v_a_7033_);
return v___x_7034_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object* v_format_7035_, lean_object* v_config_7036_, lean_object* v_func_7037_, lean_object* v_a_7038_){
_start:
{
lean_object* v___x_7039_; 
v___x_7039_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7036_, v_format_7035_, v_func_7037_, v_a_7038_);
return v___x_7039_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object* v_00_u03b1_7040_, lean_object* v_format_7041_, lean_object* v_config_7042_, lean_object* v_func_7043_, lean_object* v_a_7044_){
_start:
{
lean_object* v___x_7045_; 
v___x_7045_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7042_, v_format_7041_, v_func_7043_, v_a_7044_);
return v___x_7045_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object* v_string_7046_, lean_object* v_config_7047_, lean_object* v_aw_7048_, lean_object* v___y_7049_){
_start:
{
lean_object* v___x_7050_; 
v___x_7050_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(v_string_7046_, v_config_7047_, v_aw_7048_, v___y_7049_);
if (lean_obj_tag(v___x_7050_) == 0)
{
lean_object* v_pos_7051_; lean_object* v_fst_7052_; lean_object* v_snd_7053_; lean_object* v___x_7054_; uint8_t v_decide_7055_; 
v_pos_7051_ = lean_ctor_get(v___x_7050_, 0);
v_fst_7052_ = lean_ctor_get(v_pos_7051_, 0);
v_snd_7053_ = lean_ctor_get(v_pos_7051_, 1);
v___x_7054_ = lean_string_utf8_byte_size(v_fst_7052_);
v_decide_7055_ = lean_nat_dec_eq(v_snd_7053_, v___x_7054_);
if (v_decide_7055_ == 0)
{
lean_object* v___x_7057_; uint8_t v_isShared_7058_; uint8_t v_isSharedCheck_7063_; 
lean_inc(v_pos_7051_);
v_isSharedCheck_7063_ = !lean_is_exclusive(v___x_7050_);
if (v_isSharedCheck_7063_ == 0)
{
lean_object* v_unused_7064_; lean_object* v_unused_7065_; 
v_unused_7064_ = lean_ctor_get(v___x_7050_, 1);
lean_dec(v_unused_7064_);
v_unused_7065_ = lean_ctor_get(v___x_7050_, 0);
lean_dec(v_unused_7065_);
v___x_7057_ = v___x_7050_;
v_isShared_7058_ = v_isSharedCheck_7063_;
goto v_resetjp_7056_;
}
else
{
lean_dec(v___x_7050_);
v___x_7057_ = lean_box(0);
v_isShared_7058_ = v_isSharedCheck_7063_;
goto v_resetjp_7056_;
}
v_resetjp_7056_:
{
lean_object* v___x_7059_; lean_object* v___x_7061_; 
v___x_7059_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_7058_ == 0)
{
lean_ctor_set_tag(v___x_7057_, 1);
lean_ctor_set(v___x_7057_, 1, v___x_7059_);
v___x_7061_ = v___x_7057_;
goto v_reusejp_7060_;
}
else
{
lean_object* v_reuseFailAlloc_7062_; 
v_reuseFailAlloc_7062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7062_, 0, v_pos_7051_);
lean_ctor_set(v_reuseFailAlloc_7062_, 1, v___x_7059_);
v___x_7061_ = v_reuseFailAlloc_7062_;
goto v_reusejp_7060_;
}
v_reusejp_7060_:
{
return v___x_7061_;
}
}
}
else
{
return v___x_7050_;
}
}
else
{
return v___x_7050_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object* v_aw_7066_, lean_object* v_format_7067_, lean_object* v_input_7068_){
_start:
{
lean_object* v_config_7069_; lean_object* v_string_7070_; lean_object* v___f_7071_; lean_object* v___x_7072_; 
v_config_7069_ = lean_ctor_get(v_format_7067_, 0);
lean_inc_ref(v_config_7069_);
v_string_7070_ = lean_ctor_get(v_format_7067_, 1);
lean_inc(v_string_7070_);
lean_dec_ref(v_format_7067_);
v___f_7071_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parse___lam__0), 4, 3);
lean_closure_set(v___f_7071_, 0, v_string_7070_);
lean_closure_set(v___f_7071_, 1, v_config_7069_);
lean_closure_set(v___f_7071_, 2, v_aw_7066_);
v___x_7072_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7071_, v_input_7068_);
return v___x_7072_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object* v_msg_7073_){
_start:
{
lean_object* v___x_7074_; lean_object* v___x_7075_; 
v___x_7074_ = l_Std_Time_instInhabitedDateTime;
v___x_7075_ = lean_panic_fn_borrowed(v___x_7074_, v_msg_7073_);
return v___x_7075_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object* v_aw_7077_, lean_object* v_format_7078_, lean_object* v_input_7079_){
_start:
{
lean_object* v___x_7080_; 
v___x_7080_ = l_Std_Time_GenericFormat_parse(v_aw_7077_, v_format_7078_, v_input_7079_);
if (lean_obj_tag(v___x_7080_) == 0)
{
lean_object* v_a_7081_; lean_object* v___x_7082_; lean_object* v___x_7083_; lean_object* v___x_7084_; lean_object* v___x_7085_; lean_object* v___x_7086_; lean_object* v___x_7087_; 
v_a_7081_ = lean_ctor_get(v___x_7080_, 0);
lean_inc(v_a_7081_);
lean_dec_ref_known(v___x_7080_, 1);
v___x_7082_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7083_ = ((lean_object*)(l_Std_Time_GenericFormat_parse_x21___closed__0));
v___x_7084_ = lean_unsigned_to_nat(1124u);
v___x_7085_ = lean_unsigned_to_nat(18u);
v___x_7086_ = l_mkPanicMessageWithDecl(v___x_7082_, v___x_7083_, v___x_7084_, v___x_7085_, v_a_7081_);
lean_dec(v_a_7081_);
v___x_7087_ = l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(v___x_7086_);
return v___x_7087_;
}
else
{
lean_object* v_a_7088_; 
v_a_7088_ = lean_ctor_get(v___x_7080_, 0);
lean_inc(v_a_7088_);
lean_dec_ref_known(v___x_7080_, 1);
return v_a_7088_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object* v_config_7089_, lean_object* v_string_7090_, lean_object* v_builder_7091_, lean_object* v___y_7092_){
_start:
{
lean_object* v___x_7093_; 
v___x_7093_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7089_, v_string_7090_, v_builder_7091_, v___y_7092_);
return v___x_7093_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object* v_format_7094_, lean_object* v_builder_7095_, lean_object* v_input_7096_){
_start:
{
lean_object* v_config_7097_; lean_object* v_string_7098_; lean_object* v___f_7099_; lean_object* v___x_7100_; 
v_config_7097_ = lean_ctor_get(v_format_7094_, 0);
lean_inc_ref(v_config_7097_);
v_string_7098_ = lean_ctor_get(v_format_7094_, 1);
lean_inc(v_string_7098_);
lean_dec_ref(v_format_7094_);
v___f_7099_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0), 4, 3);
lean_closure_set(v___f_7099_, 0, v_config_7097_);
lean_closure_set(v___f_7099_, 1, v_string_7098_);
lean_closure_set(v___f_7099_, 2, v_builder_7095_);
v___x_7100_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7099_, v_input_7096_);
return v___x_7100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object* v_aw_7101_, lean_object* v_00_u03b1_7102_, lean_object* v_format_7103_, lean_object* v_builder_7104_, lean_object* v_input_7105_){
_start:
{
lean_object* v___x_7106_; 
v___x_7106_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7103_, v_builder_7104_, v_input_7105_);
return v___x_7106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object* v_aw_7107_, lean_object* v_00_u03b1_7108_, lean_object* v_format_7109_, lean_object* v_builder_7110_, lean_object* v_input_7111_){
_start:
{
lean_object* v_res_7112_; 
v_res_7112_ = l_Std_Time_GenericFormat_parseBuilder(v_aw_7107_, v_00_u03b1_7108_, v_format_7109_, v_builder_7110_, v_input_7111_);
lean_dec(v_aw_7107_);
return v_res_7112_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object* v_inst_7114_, lean_object* v_format_7115_, lean_object* v_builder_7116_, lean_object* v_input_7117_){
_start:
{
lean_object* v___x_7118_; 
v___x_7118_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7115_, v_builder_7116_, v_input_7117_);
if (lean_obj_tag(v___x_7118_) == 0)
{
lean_object* v_a_7119_; lean_object* v___x_7120_; lean_object* v___x_7121_; lean_object* v___x_7122_; lean_object* v___x_7123_; lean_object* v___x_7124_; lean_object* v___x_7125_; 
v_a_7119_ = lean_ctor_get(v___x_7118_, 0);
lean_inc(v_a_7119_);
lean_dec_ref_known(v___x_7118_, 1);
v___x_7120_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7121_ = ((lean_object*)(l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0));
v___x_7122_ = lean_unsigned_to_nat(1138u);
v___x_7123_ = lean_unsigned_to_nat(18u);
v___x_7124_ = l_mkPanicMessageWithDecl(v___x_7120_, v___x_7121_, v___x_7122_, v___x_7123_, v_a_7119_);
lean_dec(v_a_7119_);
v___x_7125_ = l_panic___redArg(v_inst_7114_, v___x_7124_);
return v___x_7125_;
}
else
{
lean_object* v_a_7126_; 
v_a_7126_ = lean_ctor_get(v___x_7118_, 0);
lean_inc(v_a_7126_);
lean_dec_ref_known(v___x_7118_, 1);
return v_a_7126_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object* v_inst_7127_, lean_object* v_format_7128_, lean_object* v_builder_7129_, lean_object* v_input_7130_){
_start:
{
lean_object* v_res_7131_; 
v_res_7131_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7127_, v_format_7128_, v_builder_7129_, v_input_7130_);
lean_dec(v_inst_7127_);
return v_res_7131_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object* v_00_u03b1_7132_, lean_object* v_aw_7133_, lean_object* v_inst_7134_, lean_object* v_format_7135_, lean_object* v_builder_7136_, lean_object* v_input_7137_){
_start:
{
lean_object* v___x_7138_; 
v___x_7138_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7134_, v_format_7135_, v_builder_7136_, v_input_7137_);
return v___x_7138_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object* v_00_u03b1_7139_, lean_object* v_aw_7140_, lean_object* v_inst_7141_, lean_object* v_format_7142_, lean_object* v_builder_7143_, lean_object* v_input_7144_){
_start:
{
lean_object* v_res_7145_; 
v_res_7145_ = l_Std_Time_GenericFormat_parseBuilder_x21(v_00_u03b1_7139_, v_aw_7140_, v_inst_7141_, v_format_7142_, v_builder_7143_, v_input_7144_);
lean_dec(v_inst_7141_);
lean_dec(v_aw_7140_);
return v_res_7145_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object* v_getInfo_7146_, lean_object* v_dateformat_7147_, lean_object* v_data_7148_, lean_object* v_format_7149_){
_start:
{
if (lean_obj_tag(v_format_7149_) == 0)
{
lean_object* v___x_7150_; 
lean_dec_ref(v_getInfo_7146_);
v___x_7150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7150_, 0, v_data_7148_);
return v___x_7150_;
}
else
{
lean_object* v_head_7151_; 
v_head_7151_ = lean_ctor_get(v_format_7149_, 0);
lean_inc(v_head_7151_);
if (lean_obj_tag(v_head_7151_) == 0)
{
lean_object* v_tail_7152_; lean_object* v_val_7153_; lean_object* v___x_7154_; 
v_tail_7152_ = lean_ctor_get(v_format_7149_, 1);
lean_inc(v_tail_7152_);
lean_dec_ref_known(v_format_7149_, 2);
v_val_7153_ = lean_ctor_get(v_head_7151_, 0);
lean_inc_ref(v_val_7153_);
lean_dec_ref_known(v_head_7151_, 1);
v___x_7154_ = lean_string_append(v_data_7148_, v_val_7153_);
lean_dec_ref(v_val_7153_);
v_data_7148_ = v___x_7154_;
v_format_7149_ = v_tail_7152_;
goto _start;
}
else
{
lean_object* v_tail_7156_; lean_object* v_modifier_7157_; lean_object* v___x_7158_; 
v_tail_7156_ = lean_ctor_get(v_format_7149_, 1);
lean_inc(v_tail_7156_);
lean_dec_ref_known(v_format_7149_, 2);
v_modifier_7157_ = lean_ctor_get(v_head_7151_, 0);
lean_inc_ref_n(v_modifier_7157_, 2);
lean_dec_ref_known(v_head_7151_, 1);
lean_inc_ref(v_getInfo_7146_);
v___x_7158_ = lean_apply_1(v_getInfo_7146_, v_modifier_7157_);
if (lean_obj_tag(v___x_7158_) == 0)
{
lean_object* v___x_7159_; 
lean_dec_ref(v_modifier_7157_);
lean_dec(v_tail_7156_);
lean_dec_ref(v_data_7148_);
lean_dec_ref(v_getInfo_7146_);
v___x_7159_ = lean_box(0);
return v___x_7159_;
}
else
{
lean_object* v_val_7160_; lean_object* v___x_7161_; lean_object* v___x_7162_; 
v_val_7160_ = lean_ctor_get(v___x_7158_, 0);
lean_inc(v_val_7160_);
lean_dec_ref_known(v___x_7158_, 1);
v___x_7161_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7147_, v_modifier_7157_, v_val_7160_);
v___x_7162_ = lean_string_append(v_data_7148_, v___x_7161_);
lean_dec_ref(v___x_7161_);
v_data_7148_ = v___x_7162_;
v_format_7149_ = v_tail_7156_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go___boxed(lean_object* v_getInfo_7164_, lean_object* v_dateformat_7165_, lean_object* v_data_7166_, lean_object* v_format_7167_){
_start:
{
lean_object* v_res_7168_; 
v_res_7168_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7164_, v_dateformat_7165_, v_data_7166_, v_format_7167_);
lean_dec_ref(v_dateformat_7165_);
return v_res_7168_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object* v_format_7169_, lean_object* v_getInfo_7170_){
_start:
{
lean_object* v_config_7171_; lean_object* v_string_7172_; lean_object* v_dateformat_7173_; lean_object* v___x_7174_; lean_object* v___x_7175_; 
v_config_7171_ = lean_ctor_get(v_format_7169_, 0);
lean_inc_ref(v_config_7171_);
v_string_7172_ = lean_ctor_get(v_format_7169_, 1);
lean_inc(v_string_7172_);
lean_dec_ref(v_format_7169_);
v_dateformat_7173_ = lean_ctor_get(v_config_7171_, 0);
lean_inc_ref(v_dateformat_7173_);
lean_dec_ref(v_config_7171_);
v___x_7174_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7175_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7170_, v_dateformat_7173_, v___x_7174_, v_string_7172_);
lean_dec_ref(v_dateformat_7173_);
return v___x_7175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object* v_aw_7176_, lean_object* v_format_7177_, lean_object* v_getInfo_7178_){
_start:
{
lean_object* v___x_7179_; 
v___x_7179_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7177_, v_getInfo_7178_);
return v___x_7179_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object* v_aw_7180_, lean_object* v_format_7181_, lean_object* v_getInfo_7182_){
_start:
{
lean_object* v_res_7183_; 
v_res_7183_ = l_Std_Time_GenericFormat_formatGeneric(v_aw_7180_, v_format_7181_, v_getInfo_7182_);
lean_dec(v_aw_7180_);
return v_res_7183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object* v_dateformat_7184_, lean_object* v_data_7185_, lean_object* v_format_7186_){
_start:
{
if (lean_obj_tag(v_format_7186_) == 0)
{
lean_dec_ref(v_dateformat_7184_);
return v_data_7185_;
}
else
{
lean_object* v_head_7187_; 
v_head_7187_ = lean_ctor_get(v_format_7186_, 0);
lean_inc(v_head_7187_);
if (lean_obj_tag(v_head_7187_) == 0)
{
lean_object* v_tail_7188_; lean_object* v_val_7189_; lean_object* v___x_7190_; 
v_tail_7188_ = lean_ctor_get(v_format_7186_, 1);
lean_inc(v_tail_7188_);
lean_dec_ref_known(v_format_7186_, 2);
v_val_7189_ = lean_ctor_get(v_head_7187_, 0);
lean_inc_ref(v_val_7189_);
lean_dec_ref_known(v_head_7187_, 1);
v___x_7190_ = lean_string_append(v_data_7185_, v_val_7189_);
lean_dec_ref(v_val_7189_);
v_data_7185_ = v___x_7190_;
v_format_7186_ = v_tail_7188_;
goto _start;
}
else
{
lean_object* v_tail_7192_; lean_object* v_modifier_7193_; lean_object* v___f_7194_; 
v_tail_7192_ = lean_ctor_get(v_format_7186_, 1);
lean_inc(v_tail_7192_);
lean_dec_ref_known(v_format_7186_, 2);
v_modifier_7193_ = lean_ctor_get(v_head_7187_, 0);
lean_inc_ref(v_modifier_7193_);
lean_dec_ref_known(v_head_7187_, 1);
v___f_7194_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0), 5, 4);
lean_closure_set(v___f_7194_, 0, v_dateformat_7184_);
lean_closure_set(v___f_7194_, 1, v_modifier_7193_);
lean_closure_set(v___f_7194_, 2, v_data_7185_);
lean_closure_set(v___f_7194_, 3, v_tail_7192_);
return v___f_7194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object* v_dateformat_7195_, lean_object* v_modifier_7196_, lean_object* v_data_7197_, lean_object* v_tail_7198_, lean_object* v___y_7199_){
_start:
{
lean_object* v___x_7200_; lean_object* v___x_7201_; lean_object* v___x_7202_; 
v___x_7200_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7195_, v_modifier_7196_, v___y_7199_);
v___x_7201_ = lean_string_append(v_data_7197_, v___x_7200_);
lean_dec_ref(v___x_7200_);
v___x_7202_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7195_, v___x_7201_, v_tail_7198_);
return v___x_7202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object* v_format_7203_){
_start:
{
lean_object* v_config_7204_; lean_object* v_string_7205_; lean_object* v_dateformat_7206_; lean_object* v___x_7207_; lean_object* v___x_7208_; 
v_config_7204_ = lean_ctor_get(v_format_7203_, 0);
lean_inc_ref(v_config_7204_);
v_string_7205_ = lean_ctor_get(v_format_7203_, 1);
lean_inc(v_string_7205_);
lean_dec_ref(v_format_7203_);
v_dateformat_7206_ = lean_ctor_get(v_config_7204_, 0);
lean_inc_ref(v_dateformat_7206_);
lean_dec_ref(v_config_7204_);
v___x_7207_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7208_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7206_, v___x_7207_, v_string_7205_);
return v___x_7208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object* v_aw_7209_, lean_object* v_format_7210_){
_start:
{
lean_object* v___x_7211_; 
v___x_7211_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v_format_7210_);
return v___x_7211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object* v_aw_7212_, lean_object* v_format_7213_){
_start:
{
lean_object* v_res_7214_; 
v_res_7214_ = l_Std_Time_GenericFormat_formatBuilder(v_aw_7212_, v_format_7213_);
lean_dec(v_aw_7212_);
return v_res_7214_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instFormatGenericFormatFormatTypeString(lean_object* v_aw_7215_){
_start:
{
lean_object* v___x_7216_; lean_object* v___x_7217_; lean_object* v___x_7218_; 
lean_inc(v_aw_7215_);
v___x_7216_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_formatBuilder___boxed), 2, 1);
lean_closure_set(v___x_7216_, 0, v_aw_7215_);
v___x_7217_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___boxed), 5, 1);
lean_closure_set(v___x_7217_, 0, v_aw_7215_);
v___x_7218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7218_, 0, v___x_7216_);
lean_ctor_set(v___x_7218_, 1, v___x_7217_);
return v___x_7218_;
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
