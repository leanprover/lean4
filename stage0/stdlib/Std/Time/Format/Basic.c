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
static lean_object* _init_l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0(void){
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
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg(){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg___boxed(lean_object* v___dummy_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_Time_instInhabitedGenericFormat_default___redArg();
return v_res_163_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0(void){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_Time_instInhabitedGenericFormat_default___redArg();
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default(lean_object* v_awareness_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___boxed(lean_object* v_awareness_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_Time_instInhabitedGenericFormat_default(v_awareness_167_);
lean_dec(v_awareness_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___redArg(){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_170_;
}
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint8_t v_decide_273_, uint32_t v___x_274_, lean_object* v___y_275_){
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object* v_decide_343_, lean_object* v___x_344_, lean_object* v___y_345_){
_start:
{
uint8_t v_decide_10974__boxed_346_; uint32_t v___x_10975__boxed_347_; lean_object* v_res_348_; 
v_decide_10974__boxed_346_ = lean_unbox(v_decide_343_);
v___x_10975__boxed_347_ = lean_unbox_uint32(v___x_344_);
lean_dec(v___x_344_);
v_res_348_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(v_decide_10974__boxed_346_, v___x_10975__boxed_347_, v___y_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(lean_object* v_acc_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_fst_351_; lean_object* v_snd_352_; lean_object* v_pos_354_; lean_object* v_snd_355_; lean_object* v_err_356_; lean_object* v___x_360_; uint8_t v_decide_361_; 
v_fst_351_ = lean_ctor_get(v_a_350_, 0);
v_snd_352_ = lean_ctor_get(v_a_350_, 1);
lean_inc(v_snd_352_);
v___x_360_ = lean_string_utf8_byte_size(v_fst_351_);
v_decide_361_ = lean_nat_dec_eq(v_snd_352_, v___x_360_);
if (v_decide_361_ == 0)
{
uint32_t v___x_362_; uint32_t v_c_363_; uint8_t v___x_364_; 
v___x_362_ = 39;
v_c_363_ = lean_string_utf8_get_fast(v_fst_351_, v_snd_352_);
v___x_364_ = lean_uint32_dec_eq(v_c_363_, v___x_362_);
if (v___x_364_ == 0)
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_374_; 
lean_inc(v_fst_351_);
v_isSharedCheck_374_ = !lean_is_exclusive(v_a_350_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; lean_object* v_unused_376_; 
v_unused_375_ = lean_ctor_get(v_a_350_, 1);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_a_350_, 0);
lean_dec(v_unused_376_);
v___x_366_ = v_a_350_;
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
else
{
lean_dec(v_a_350_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v_it_x27_370_; 
v___x_368_ = lean_string_utf8_next_fast(v_fst_351_, v_snd_352_);
lean_dec(v_snd_352_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v___x_368_);
v_it_x27_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_fst_351_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_368_);
v_it_x27_370_ = v_reuseFailAlloc_373_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; 
v___x_371_ = lean_string_push(v_acc_349_, v_c_363_);
v_acc_349_ = v___x_371_;
v_a_350_ = v_it_x27_370_;
goto _start;
}
}
}
else
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_352_);
v_pos_354_ = v_a_350_;
v_snd_355_ = v_snd_352_;
v_err_356_ = v___x_377_;
goto v___jp_353_;
}
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
lean_inc(v_snd_352_);
v_pos_354_ = v_a_350_;
v_snd_355_ = v_snd_352_;
v_err_356_ = v___x_378_;
goto v___jp_353_;
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
lean_dec_ref(v_acc_349_);
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
lean_ctor_set(v___x_359_, 1, v_acc_349_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(lean_object* v_acc_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v_pos_384_; lean_object* v_snd_385_; lean_object* v_err_386_; lean_object* v___x_390_; uint8_t v_decide_391_; 
v_fst_381_ = lean_ctor_get(v_a_380_, 0);
v_snd_382_ = lean_ctor_get(v_a_380_, 1);
lean_inc(v_snd_382_);
v___x_390_ = lean_string_utf8_byte_size(v_fst_381_);
v_decide_391_ = lean_nat_dec_eq(v_snd_382_, v___x_390_);
if (v_decide_391_ == 0)
{
uint32_t v___x_392_; uint32_t v_c_393_; uint8_t v___x_394_; 
v___x_392_ = 39;
v_c_393_ = lean_string_utf8_get_fast(v_fst_381_, v_snd_382_);
v___x_394_ = lean_uint32_dec_eq(v_c_393_, v___x_392_);
if (v___x_394_ == 0)
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_404_; 
lean_inc(v_fst_381_);
v_isSharedCheck_404_ = !lean_is_exclusive(v_a_380_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; lean_object* v_unused_406_; 
v_unused_405_ = lean_ctor_get(v_a_380_, 1);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_a_380_, 0);
lean_dec(v_unused_406_);
v___x_396_ = v_a_380_;
v_isShared_397_ = v_isSharedCheck_404_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_a_380_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_404_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v_it_x27_400_; 
v___x_398_ = lean_string_utf8_next_fast(v_fst_381_, v_snd_382_);
lean_dec(v_snd_382_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_398_);
v_it_x27_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_fst_381_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v___x_398_);
v_it_x27_400_ = v_reuseFailAlloc_403_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_string_push(v_acc_379_, v_c_393_);
v___x_402_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(v___x_401_, v_it_x27_400_);
return v___x_402_;
}
}
}
else
{
lean_object* v___x_407_; 
v___x_407_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_382_);
v_pos_384_ = v_a_380_;
v_snd_385_ = v_snd_382_;
v_err_386_ = v___x_407_;
goto v___jp_383_;
}
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
lean_inc(v_snd_382_);
v_pos_384_ = v_a_380_;
v_snd_385_ = v_snd_382_;
v_err_386_ = v___x_408_;
goto v___jp_383_;
}
v___jp_383_:
{
uint8_t v_decide_387_; 
v_decide_387_ = lean_nat_dec_eq(v_snd_382_, v_snd_385_);
lean_dec(v_snd_385_);
lean_dec(v_snd_382_);
if (v_decide_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec_ref(v_acc_379_);
lean_inc(v_err_386_);
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v_pos_384_);
lean_ctor_set(v___x_388_, 1, v_err_386_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_pos_384_);
lean_ctor_set(v___x_389_, 1, v_acc_379_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(uint8_t v_decide_412_, uint32_t v___x_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_fst_418_; lean_object* v_snd_419_; lean_object* v___x_420_; uint8_t v_decide_421_; 
v_fst_418_ = lean_ctor_get(v___y_414_, 0);
v_snd_419_ = lean_ctor_get(v___y_414_, 1);
v___x_420_ = lean_string_utf8_byte_size(v_fst_418_);
v_decide_421_ = lean_nat_dec_eq(v_snd_419_, v___x_420_);
if (v_decide_421_ == 0)
{
if (v_decide_412_ == 0)
{
goto v___jp_415_;
}
else
{
uint32_t v_c_422_; uint8_t v___x_423_; 
v_c_422_ = lean_string_utf8_get_fast(v_fst_418_, v_snd_419_);
v___x_423_ = lean_uint32_dec_eq(v_c_422_, v___x_413_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1));
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v___y_414_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
return v___x_425_;
}
else
{
lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_479_; 
lean_inc(v_snd_419_);
lean_inc(v_fst_418_);
v_isSharedCheck_479_ = !lean_is_exclusive(v___y_414_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; lean_object* v_unused_481_; 
v_unused_480_ = lean_ctor_get(v___y_414_, 1);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v___y_414_, 0);
lean_dec(v_unused_481_);
v___x_427_ = v___y_414_;
v_isShared_428_ = v_isSharedCheck_479_;
goto v_resetjp_426_;
}
else
{
lean_dec(v___y_414_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_479_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v_it_x27_431_; 
v___x_429_ = lean_string_utf8_next_fast(v_fst_418_, v_snd_419_);
lean_dec(v_snd_419_);
lean_inc(v_fst_418_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 1, v___x_429_);
v_it_x27_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_fst_418_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_429_);
v_it_x27_431_ = v_reuseFailAlloc_478_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
uint8_t v_decide_435_; 
v_decide_435_ = lean_nat_dec_eq(v___x_429_, v___x_420_);
if (v_decide_435_ == 0)
{
if (v___x_423_ == 0)
{
lean_dec(v_fst_418_);
goto v___jp_432_;
}
else
{
uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_string_utf8_get_fast(v_fst_418_, v___x_429_);
v___x_437_ = lean_uint32_dec_eq(v___x_436_, v___x_413_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v_it_x27_431_);
v___x_438_ = lean_string_utf8_next_fast(v_fst_418_, v___x_429_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v_fst_418_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_441_ = lean_string_push(v___x_440_, v___x_436_);
v___x_442_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(v___x_441_, v___x_439_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_pos_443_; lean_object* v_res_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_475_; 
v_pos_443_ = lean_ctor_get(v___x_442_, 0);
v_res_444_ = lean_ctor_get(v___x_442_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_475_ == 0)
{
v___x_446_ = v___x_442_;
v_isShared_447_ = v_isSharedCheck_475_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_res_444_);
lean_inc(v_pos_443_);
lean_dec(v___x_442_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_475_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_450_; uint8_t v_decide_451_; 
v_fst_448_ = lean_ctor_get(v_pos_443_, 0);
v_snd_449_ = lean_ctor_get(v_pos_443_, 1);
v___x_450_ = lean_string_utf8_byte_size(v_fst_448_);
v_decide_451_ = lean_nat_dec_eq(v_snd_449_, v___x_450_);
if (v_decide_451_ == 0)
{
uint32_t v_c_452_; uint8_t v___x_453_; 
v_c_452_ = lean_string_utf8_get_fast(v_fst_448_, v_snd_449_);
v___x_453_ = lean_uint32_dec_eq(v_c_452_, v___x_413_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_456_; 
lean_dec(v_res_444_);
v___x_454_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1));
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 1);
lean_ctor_set(v___x_446_, 1, v___x_454_);
v___x_456_ = v___x_446_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_pos_443_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
else
{
lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_468_; 
lean_inc(v_snd_449_);
lean_inc(v_fst_448_);
v_isSharedCheck_468_ = !lean_is_exclusive(v_pos_443_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; 
v_unused_469_ = lean_ctor_get(v_pos_443_, 1);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_pos_443_, 0);
lean_dec(v_unused_470_);
v___x_459_ = v_pos_443_;
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
else
{
lean_dec(v_pos_443_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v_it_x27_463_; 
v___x_461_ = lean_string_utf8_next_fast(v_fst_448_, v_snd_449_);
lean_dec(v_snd_449_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_461_);
v_it_x27_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_fst_448_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_461_);
v_it_x27_463_ = v_reuseFailAlloc_467_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_465_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_it_x27_463_);
v___x_465_ = v___x_446_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_it_x27_463_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_res_444_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_473_; 
lean_dec(v_res_444_);
v___x_471_ = lean_box(0);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 1);
lean_ctor_set(v___x_446_, 1, v___x_471_);
v___x_473_ = v___x_446_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_pos_443_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
return v___x_442_;
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v_fst_418_);
v___x_476_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v_it_x27_431_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
return v___x_477_;
}
}
}
else
{
lean_dec(v_fst_418_);
goto v___jp_432_;
}
v___jp_432_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_434_, 0, v_it_x27_431_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
return v___x_434_;
}
}
}
}
}
}
else
{
goto v___jp_415_;
}
v___jp_415_:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_box(0);
v___x_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_417_, 0, v___y_414_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object* v_decide_482_, lean_object* v___x_483_, lean_object* v___y_484_){
_start:
{
uint8_t v_decide_11224__boxed_485_; uint32_t v___x_11225__boxed_486_; lean_object* v_res_487_; 
v_decide_11224__boxed_485_ = lean_unbox(v_decide_482_);
v___x_11225__boxed_486_ = lean_unbox_uint32(v___x_483_);
lean_dec(v___x_483_);
v_res_487_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(v_decide_11224__boxed_485_, v___x_11225__boxed_486_, v___y_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object* v_acc_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_fst_490_; lean_object* v_snd_491_; lean_object* v_pos_493_; lean_object* v_snd_494_; lean_object* v_err_495_; lean_object* v___x_501_; uint8_t v_decide_502_; 
v_fst_490_ = lean_ctor_get(v_a_489_, 0);
v_snd_491_ = lean_ctor_get(v_a_489_, 1);
lean_inc(v_snd_491_);
v___x_501_ = lean_string_utf8_byte_size(v_fst_490_);
v_decide_502_ = lean_nat_dec_eq(v_snd_491_, v___x_501_);
if (v_decide_502_ == 0)
{
uint32_t v___x_503_; uint32_t v___x_504_; uint8_t v___x_505_; uint32_t v_c_506_; lean_object* v___x_507_; lean_object* v_it_x27_508_; uint8_t v___y_510_; uint8_t v___y_511_; uint8_t v___y_515_; uint8_t v___y_516_; uint8_t v___y_517_; uint8_t v___y_519_; uint8_t v___y_520_; uint8_t v___y_523_; uint8_t v___y_526_; uint8_t v___y_528_; uint32_t v___x_533_; uint8_t v___x_534_; 
v___x_503_ = 39;
v___x_504_ = 34;
v___x_505_ = 1;
v_c_506_ = lean_string_utf8_get_fast(v_fst_490_, v_snd_491_);
v___x_507_ = lean_string_utf8_next_fast(v_fst_490_, v_snd_491_);
lean_inc(v_fst_490_);
v_it_x27_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_508_, 0, v_fst_490_);
lean_ctor_set(v_it_x27_508_, 1, v___x_507_);
v___x_533_ = 65;
v___x_534_ = lean_uint32_dec_le(v___x_533_, v_c_506_);
if (v___x_534_ == 0)
{
v___y_528_ = v___x_534_;
goto v___jp_527_;
}
else
{
uint32_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 90;
v___x_536_ = lean_uint32_dec_le(v_c_506_, v___x_535_);
v___y_528_ = v___x_536_;
goto v___jp_527_;
}
v___jp_509_:
{
if (v___y_510_ == 0)
{
lean_dec_ref_known(v_it_x27_508_, 2);
goto v___jp_499_;
}
else
{
if (v___y_511_ == 0)
{
lean_dec_ref_known(v_it_x27_508_, 2);
goto v___jp_499_;
}
else
{
lean_object* v___x_512_; 
lean_dec(v_snd_491_);
lean_dec_ref(v_a_489_);
v___x_512_ = lean_string_push(v_acc_488_, v_c_506_);
v_acc_488_ = v___x_512_;
v_a_489_ = v_it_x27_508_;
goto _start;
}
}
}
v___jp_514_:
{
if (v___y_516_ == 0)
{
v___y_510_ = v___y_515_;
v___y_511_ = v___y_516_;
goto v___jp_509_;
}
else
{
v___y_510_ = v___y_515_;
v___y_511_ = v___y_517_;
goto v___jp_509_;
}
}
v___jp_518_:
{
uint8_t v___x_521_; 
v___x_521_ = lean_uint32_dec_eq(v_c_506_, v___x_504_);
if (v___x_521_ == 0)
{
v___y_515_ = v___y_519_;
v___y_516_ = v___y_520_;
v___y_517_ = v___x_505_;
goto v___jp_514_;
}
else
{
v___y_515_ = v___y_519_;
v___y_516_ = v___y_520_;
v___y_517_ = v_decide_502_;
goto v___jp_514_;
}
}
v___jp_522_:
{
uint8_t v___x_524_; 
v___x_524_ = lean_uint32_dec_eq(v_c_506_, v___x_503_);
if (v___x_524_ == 0)
{
v___y_519_ = v___y_523_;
v___y_520_ = v___x_505_;
goto v___jp_518_;
}
else
{
v___y_519_ = v___y_523_;
v___y_520_ = v_decide_502_;
goto v___jp_518_;
}
}
v___jp_525_:
{
if (v___y_526_ == 0)
{
v___y_523_ = v___x_505_;
goto v___jp_522_;
}
else
{
v___y_523_ = v_decide_502_;
goto v___jp_522_;
}
}
v___jp_527_:
{
if (v___y_528_ == 0)
{
uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 97;
v___x_530_ = lean_uint32_dec_le(v___x_529_, v_c_506_);
if (v___x_530_ == 0)
{
v___y_526_ = v___x_530_;
goto v___jp_525_;
}
else
{
uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 122;
v___x_532_ = lean_uint32_dec_le(v_c_506_, v___x_531_);
v___y_526_ = v___x_532_;
goto v___jp_525_;
}
}
else
{
v___y_523_ = v_decide_502_;
goto v___jp_522_;
}
}
}
else
{
lean_object* v___x_537_; 
v___x_537_ = lean_box(0);
lean_inc(v_snd_491_);
v_pos_493_ = v_a_489_;
v_snd_494_ = v_snd_491_;
v_err_495_ = v___x_537_;
goto v___jp_492_;
}
v___jp_492_:
{
uint8_t v_decide_496_; 
v_decide_496_ = lean_nat_dec_eq(v_snd_491_, v_snd_494_);
lean_dec(v_snd_494_);
lean_dec(v_snd_491_);
if (v_decide_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec_ref(v_acc_488_);
lean_inc(v_err_495_);
v___x_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_497_, 0, v_pos_493_);
lean_ctor_set(v___x_497_, 1, v_err_495_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v_pos_493_);
lean_ctor_set(v___x_498_, 1, v_acc_488_);
return v___x_498_;
}
}
v___jp_499_:
{
lean_object* v___x_500_; 
v___x_500_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_491_);
v_pos_493_ = v_a_489_;
v_snd_494_ = v_snd_491_;
v_err_495_ = v___x_500_;
goto v___jp_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint8_t v_decide_538_, uint32_t v___x_539_, uint32_t v___x_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_fst_548_; lean_object* v_snd_549_; lean_object* v___x_550_; uint8_t v_decide_551_; 
v_fst_548_ = lean_ctor_get(v___y_541_, 0);
v_snd_549_ = lean_ctor_get(v___y_541_, 1);
v___x_550_ = lean_string_utf8_byte_size(v_fst_548_);
v_decide_551_ = lean_nat_dec_eq(v_snd_549_, v___x_550_);
if (v_decide_551_ == 0)
{
if (v_decide_538_ == 0)
{
goto v___jp_545_;
}
else
{
uint32_t v_c_552_; lean_object* v___x_553_; lean_object* v_it_x27_554_; uint8_t v___y_556_; uint8_t v___y_557_; uint8_t v___y_562_; uint8_t v___y_563_; uint8_t v___y_564_; uint8_t v___y_566_; uint8_t v___y_567_; uint8_t v___y_570_; uint8_t v___y_573_; uint8_t v___y_575_; uint32_t v___x_580_; uint8_t v___x_581_; 
v_c_552_ = lean_string_utf8_get_fast(v_fst_548_, v_snd_549_);
v___x_553_ = lean_string_utf8_next_fast(v_fst_548_, v_snd_549_);
lean_inc(v_fst_548_);
v_it_x27_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_554_, 0, v_fst_548_);
lean_ctor_set(v_it_x27_554_, 1, v___x_553_);
v___x_580_ = 65;
v___x_581_ = lean_uint32_dec_le(v___x_580_, v_c_552_);
if (v___x_581_ == 0)
{
v___y_575_ = v___x_581_;
goto v___jp_574_;
}
else
{
uint32_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = 90;
v___x_583_ = lean_uint32_dec_le(v_c_552_, v___x_582_);
v___y_575_ = v___x_583_;
goto v___jp_574_;
}
v___jp_555_:
{
if (v___y_556_ == 0)
{
lean_dec_ref_known(v_it_x27_554_, 2);
goto v___jp_542_;
}
else
{
if (v___y_557_ == 0)
{
lean_dec_ref_known(v_it_x27_554_, 2);
goto v___jp_542_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref(v___y_541_);
v___x_558_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_559_ = lean_string_push(v___x_558_, v_c_552_);
v___x_560_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(v___x_559_, v_it_x27_554_);
return v___x_560_;
}
}
}
v___jp_561_:
{
if (v___y_563_ == 0)
{
v___y_556_ = v___y_562_;
v___y_557_ = v___y_563_;
goto v___jp_555_;
}
else
{
v___y_556_ = v___y_562_;
v___y_557_ = v___y_564_;
goto v___jp_555_;
}
}
v___jp_565_:
{
uint8_t v___x_568_; 
v___x_568_ = lean_uint32_dec_eq(v_c_552_, v___x_539_);
if (v___x_568_ == 0)
{
v___y_562_ = v___y_566_;
v___y_563_ = v___y_567_;
v___y_564_ = v_decide_538_;
goto v___jp_561_;
}
else
{
v___y_562_ = v___y_566_;
v___y_563_ = v___y_567_;
v___y_564_ = v_decide_551_;
goto v___jp_561_;
}
}
v___jp_569_:
{
uint8_t v___x_571_; 
v___x_571_ = lean_uint32_dec_eq(v_c_552_, v___x_540_);
if (v___x_571_ == 0)
{
v___y_566_ = v___y_570_;
v___y_567_ = v_decide_538_;
goto v___jp_565_;
}
else
{
v___y_566_ = v___y_570_;
v___y_567_ = v_decide_551_;
goto v___jp_565_;
}
}
v___jp_572_:
{
if (v___y_573_ == 0)
{
v___y_570_ = v_decide_538_;
goto v___jp_569_;
}
else
{
v___y_570_ = v_decide_551_;
goto v___jp_569_;
}
}
v___jp_574_:
{
if (v___y_575_ == 0)
{
uint32_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = 97;
v___x_577_ = lean_uint32_dec_le(v___x_576_, v_c_552_);
if (v___x_577_ == 0)
{
v___y_573_ = v___x_577_;
goto v___jp_572_;
}
else
{
uint32_t v___x_578_; uint8_t v___x_579_; 
v___x_578_ = 122;
v___x_579_ = lean_uint32_dec_le(v_c_552_, v___x_578_);
v___y_573_ = v___x_579_;
goto v___jp_572_;
}
}
else
{
v___y_570_ = v_decide_551_;
goto v___jp_569_;
}
}
}
}
else
{
goto v___jp_545_;
}
v___jp_542_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_544_, 0, v___y_541_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_box(0);
v___x_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_547_, 0, v___y_541_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object* v_decide_584_, lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v___y_587_){
_start:
{
uint8_t v_decide_11452__boxed_588_; uint32_t v___x_11453__boxed_589_; uint32_t v___x_11454__boxed_590_; lean_object* v_res_591_; 
v_decide_11452__boxed_588_ = lean_unbox(v_decide_584_);
v___x_11453__boxed_589_ = lean_unbox_uint32(v___x_585_);
lean_dec(v___x_585_);
v___x_11454__boxed_590_ = lean_unbox_uint32(v___x_586_);
lean_dec(v___x_586_);
v_res_591_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(v_decide_11452__boxed_588_, v___x_11453__boxed_589_, v___x_11454__boxed_590_, v___y_587_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t v___y_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_594_ = lean_string_push(v___x_593_, v___y_592_);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object* v___y_596_){
_start:
{
uint32_t v___y_11542__boxed_597_; lean_object* v_res_598_; 
v___y_11542__boxed_597_ = lean_unbox_uint32(v___y_596_);
lean_dec(v___y_596_);
v_res_598_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(v___y_11542__boxed_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(uint8_t v___x_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_606_; uint8_t v_decide_607_; 
v_fst_604_ = lean_ctor_get(v___y_600_, 0);
v_snd_605_ = lean_ctor_get(v___y_600_, 1);
v___x_606_ = lean_string_utf8_byte_size(v_fst_604_);
v_decide_607_ = lean_nat_dec_eq(v_snd_605_, v___x_606_);
if (v_decide_607_ == 0)
{
if (v___x_599_ == 0)
{
goto v___jp_601_;
}
else
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_618_; 
lean_inc(v_snd_605_);
lean_inc(v_fst_604_);
v_isSharedCheck_618_ = !lean_is_exclusive(v___y_600_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; lean_object* v_unused_620_; 
v_unused_619_ = lean_ctor_get(v___y_600_, 1);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v___y_600_, 0);
lean_dec(v_unused_620_);
v___x_609_ = v___y_600_;
v_isShared_610_ = v_isSharedCheck_618_;
goto v_resetjp_608_;
}
else
{
lean_dec(v___y_600_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_618_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
uint32_t v_c_611_; lean_object* v___x_612_; lean_object* v_it_x27_614_; 
v_c_611_ = lean_string_utf8_get_fast(v_fst_604_, v_snd_605_);
v___x_612_ = lean_string_utf8_next_fast(v_fst_604_, v_snd_605_);
lean_dec(v_snd_605_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v___x_612_);
v_it_x27_614_ = v___x_609_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_fst_604_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_612_);
v_it_x27_614_ = v_reuseFailAlloc_617_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_box_uint32(v_c_611_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_it_x27_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
return v___x_616_;
}
}
}
}
else
{
goto v___jp_601_;
}
v___jp_601_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_box(0);
v___x_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_603_, 0, v___y_600_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed(lean_object* v___x_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_11551__boxed_623_; lean_object* v_res_624_; 
v___x_11551__boxed_623_ = lean_unbox(v___x_621_);
v_res_624_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(v___x_11551__boxed_623_, v___y_622_);
return v_res_624_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1(void){
_start:
{
uint32_t v___x_629_; lean_object* v___x_630_; 
v___x_629_ = 34;
v___x_630_ = lean_box_uint32(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2(void){
_start:
{
uint32_t v___x_631_; lean_object* v___x_632_; 
v___x_631_ = 39;
v___x_632_ = lean_box_uint32(v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(lean_object* v_a_633_){
_start:
{
lean_object* v___x_634_; 
lean_inc_ref(v_a_633_);
v___x_634_ = l_Std_Time_parseModifier(v_a_633_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_pos_635_; lean_object* v_res_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_a_633_);
v_pos_635_ = lean_ctor_get(v___x_634_, 0);
v_res_636_ = lean_ctor_get(v___x_634_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_644_ == 0)
{
v___x_638_ = v___x_634_;
v_isShared_639_ = v_isSharedCheck_644_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_res_636_);
lean_inc(v_pos_635_);
lean_dec(v___x_634_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_644_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v_res_636_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v___x_640_);
v___x_642_ = v___x_638_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_pos_635_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
else
{
lean_object* v_pos_645_; lean_object* v_err_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_717_; 
v_pos_645_ = lean_ctor_get(v___x_634_, 0);
v_err_646_ = lean_ctor_get(v___x_634_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_717_ == 0)
{
v___x_648_ = v___x_634_;
v_isShared_649_ = v_isSharedCheck_717_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_err_646_);
lean_inc(v_pos_645_);
lean_dec(v___x_634_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_717_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_snd_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_715_; 
v_snd_650_ = lean_ctor_get(v_a_633_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_a_633_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v_a_633_, 0);
lean_dec(v_unused_716_);
v___x_652_ = v_a_633_;
v_isShared_653_ = v_isSharedCheck_715_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_snd_650_);
lean_dec(v_a_633_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_715_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_fst_654_; lean_object* v_snd_655_; uint8_t v_decide_656_; 
v_fst_654_ = lean_ctor_get(v_pos_645_, 0);
v_snd_655_ = lean_ctor_get(v_pos_645_, 1);
v_decide_656_ = lean_nat_dec_eq(v_snd_650_, v_snd_655_);
lean_dec(v_snd_650_);
if (v_decide_656_ == 0)
{
lean_object* v___x_658_; 
lean_del_object(v___x_652_);
if (v_isShared_649_ == 0)
{
v___x_658_ = v___x_648_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_pos_645_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_err_646_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
else
{
lean_object* v___f_660_; lean_object* v___y_662_; lean_object* v_pos_663_; lean_object* v_snd_664_; lean_object* v___x_690_; uint8_t v_decide_691_; 
lean_inc(v_snd_655_);
lean_dec(v_err_646_);
v___f_660_ = ((lean_object*)(l_Std_Time_instCoeStringFormatPart___closed__0));
v___x_690_ = lean_string_utf8_byte_size(v_fst_654_);
v_decide_691_ = lean_nat_dec_eq(v_snd_655_, v___x_690_);
if (v_decide_691_ == 0)
{
if (v_decide_656_ == 0)
{
lean_del_object(v___x_652_);
goto v___jp_685_;
}
else
{
uint32_t v___x_692_; uint32_t v_c_693_; uint8_t v___x_694_; 
lean_del_object(v___x_648_);
v___x_692_ = 92;
v_c_693_ = lean_string_utf8_get_fast(v_fst_654_, v_snd_655_);
v___x_694_ = lean_uint32_dec_eq(v_c_693_, v___x_692_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1));
lean_inc(v_pos_645_);
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 1);
lean_ctor_set(v___x_652_, 1, v___x_695_);
lean_ctor_set(v___x_652_, 0, v_pos_645_);
v___x_697_ = v___x_652_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_pos_645_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_inc(v_snd_655_);
v___y_662_ = v___x_697_;
v_pos_663_ = v_pos_645_;
v_snd_664_ = v_snd_655_;
goto v___jp_661_;
}
}
else
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_712_; 
lean_inc(v_fst_654_);
lean_del_object(v___x_652_);
v_isSharedCheck_712_ = !lean_is_exclusive(v_pos_645_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; lean_object* v_unused_714_; 
v_unused_713_ = lean_ctor_get(v_pos_645_, 1);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_pos_645_, 0);
lean_dec(v_unused_714_);
v___x_700_ = v_pos_645_;
v_isShared_701_ = v_isSharedCheck_712_;
goto v_resetjp_699_;
}
else
{
lean_dec(v_pos_645_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_712_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___f_702_; lean_object* v___x_703_; lean_object* v___f_704_; lean_object* v___x_705_; lean_object* v_it_x27_707_; 
v___f_702_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2));
v___x_703_ = lean_box(v___x_694_);
v___f_704_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed), 2, 1);
lean_closure_set(v___f_704_, 0, v___x_703_);
v___x_705_ = lean_string_utf8_next_fast(v_fst_654_, v_snd_655_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_705_);
v_it_x27_707_ = v___x_700_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_fst_654_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_705_);
v_it_x27_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; 
v___x_708_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_704_, v___f_702_, v_it_x27_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_dec(v_snd_655_);
return v___x_708_;
}
else
{
lean_object* v_pos_709_; lean_object* v_snd_710_; 
v_pos_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_pos_709_);
v_snd_710_ = lean_ctor_get(v_pos_709_, 1);
lean_inc(v_snd_710_);
v___y_662_ = v___x_708_;
v_pos_663_ = v_pos_709_;
v_snd_664_ = v_snd_710_;
goto v___jp_661_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_652_);
goto v___jp_685_;
}
v___jp_661_:
{
uint8_t v_decide_665_; 
v_decide_665_ = lean_nat_dec_eq(v_snd_655_, v_snd_664_);
lean_dec(v_snd_655_);
if (v_decide_665_ == 0)
{
lean_dec(v_snd_664_);
lean_dec_ref(v_pos_663_);
return v___y_662_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___f_668_; lean_object* v___x_669_; 
lean_dec_ref(v___y_662_);
v___x_666_ = lean_box(v_decide_665_);
v___x_667_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___f_668_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed), 3, 2);
lean_closure_set(v___f_668_, 0, v___x_666_);
lean_closure_set(v___f_668_, 1, v___x_667_);
v___x_669_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_668_, v___f_660_, v_pos_663_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_dec(v_snd_664_);
return v___x_669_;
}
else
{
lean_object* v_pos_670_; lean_object* v_snd_671_; uint8_t v_decide_672_; 
v_pos_670_ = lean_ctor_get(v___x_669_, 0);
v_snd_671_ = lean_ctor_get(v_pos_670_, 1);
v_decide_672_ = lean_nat_dec_eq(v_snd_664_, v_snd_671_);
lean_dec(v_snd_664_);
if (v_decide_672_ == 0)
{
return v___x_669_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___f_675_; lean_object* v___x_676_; 
lean_inc(v_snd_671_);
lean_inc(v_pos_670_);
lean_dec_ref_known(v___x_669_, 2);
v___x_673_ = lean_box(v_decide_672_);
v___x_674_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_675_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed), 3, 2);
lean_closure_set(v___f_675_, 0, v___x_673_);
lean_closure_set(v___f_675_, 1, v___x_674_);
v___x_676_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_675_, v___f_660_, v_pos_670_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_dec(v_snd_671_);
return v___x_676_;
}
else
{
lean_object* v_pos_677_; lean_object* v_snd_678_; uint8_t v_decide_679_; 
v_pos_677_ = lean_ctor_get(v___x_676_, 0);
v_snd_678_ = lean_ctor_get(v_pos_677_, 1);
v_decide_679_ = lean_nat_dec_eq(v_snd_671_, v_snd_678_);
lean_dec(v_snd_671_);
if (v_decide_679_ == 0)
{
return v___x_676_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___f_683_; lean_object* v___x_684_; 
lean_inc(v_pos_677_);
lean_dec_ref_known(v___x_676_, 2);
v___x_680_ = lean_box(v_decide_679_);
v___x_681_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___x_682_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_683_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed), 4, 3);
lean_closure_set(v___f_683_, 0, v___x_680_);
lean_closure_set(v___f_683_, 1, v___x_681_);
lean_closure_set(v___f_683_, 2, v___x_682_);
v___x_684_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_683_, v___f_660_, v_pos_677_);
return v___x_684_;
}
}
}
}
}
}
v___jp_685_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = lean_box(0);
lean_inc(v_pos_645_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_686_);
v___x_688_ = v___x_648_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_pos_645_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_inc(v_snd_655_);
v___y_662_ = v___x_688_;
v_pos_663_ = v_pos_645_;
v_snd_664_ = v_snd_655_;
goto v___jp_661_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(lean_object* v_acc_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___x_720_; 
lean_inc_ref(v_a_719_);
v___x_720_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(v_a_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_pos_721_; lean_object* v_res_722_; lean_object* v___x_723_; 
lean_dec_ref(v_a_719_);
v_pos_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_pos_721_);
v_res_722_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_res_722_);
lean_dec_ref_known(v___x_720_, 2);
v___x_723_ = lean_array_push(v_acc_718_, v_res_722_);
v_acc_718_ = v___x_723_;
v_a_719_ = v_pos_721_;
goto _start;
}
else
{
lean_object* v_pos_725_; lean_object* v_err_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_739_; 
v_pos_725_ = lean_ctor_get(v___x_720_, 0);
v_err_726_ = lean_ctor_get(v___x_720_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_739_ == 0)
{
v___x_728_ = v___x_720_;
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_err_726_);
lean_inc(v_pos_725_);
lean_dec(v___x_720_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_snd_730_; lean_object* v_snd_731_; uint8_t v_decide_732_; 
v_snd_730_ = lean_ctor_get(v_a_719_, 1);
lean_inc(v_snd_730_);
lean_dec_ref(v_a_719_);
v_snd_731_ = lean_ctor_get(v_pos_725_, 1);
v_decide_732_ = lean_nat_dec_eq(v_snd_730_, v_snd_731_);
lean_dec(v_snd_730_);
if (v_decide_732_ == 0)
{
lean_object* v___x_734_; 
lean_dec_ref(v_acc_718_);
if (v_isShared_729_ == 0)
{
v___x_734_ = v___x_728_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_pos_725_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_err_726_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
else
{
lean_object* v___x_737_; 
lean_dec(v_err_726_);
if (v_isShared_729_ == 0)
{
lean_ctor_set_tag(v___x_728_, 0);
lean_ctor_set(v___x_728_, 1, v_acc_718_);
v___x_737_ = v___x_728_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_pos_725_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_acc_718_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser(lean_object* v_a_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0));
v___x_747_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(v___x_746_, v_a_745_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_pos_748_; lean_object* v_res_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_765_; 
v_pos_748_ = lean_ctor_get(v___x_747_, 0);
v_res_749_ = lean_ctor_get(v___x_747_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_765_ == 0)
{
v___x_751_ = v___x_747_;
v_isShared_752_ = v_isSharedCheck_765_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_res_749_);
lean_inc(v_pos_748_);
lean_dec(v___x_747_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_765_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_fst_753_; lean_object* v_snd_754_; lean_object* v___x_755_; uint8_t v_decide_756_; 
v_fst_753_ = lean_ctor_get(v_pos_748_, 0);
v_snd_754_ = lean_ctor_get(v_pos_748_, 1);
v___x_755_ = lean_string_utf8_byte_size(v_fst_753_);
v_decide_756_ = lean_nat_dec_eq(v_snd_754_, v___x_755_);
if (v_decide_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_759_; 
lean_dec(v_res_749_);
v___x_757_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 1);
lean_ctor_set(v___x_751_, 1, v___x_757_);
v___x_759_ = v___x_751_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_pos_748_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
else
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_array_to_list(v_res_749_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_761_);
v___x_763_ = v___x_751_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_pos_748_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_pos_766_; lean_object* v_err_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
v_pos_766_ = lean_ctor_get(v___x_747_, 0);
v_err_767_ = lean_ctor_get(v___x_747_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_747_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_err_767_);
lean_inc(v_pos_766_);
lean_dec(v___x_747_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_pos_766_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_err_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParse(lean_object* v_s_775_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_777_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_776_, v_s_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(uint32_t v_a_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
lean_object* v_zero_781_; uint8_t v_isZero_782_; 
v_zero_781_ = lean_unsigned_to_nat(0u);
v_isZero_782_ = lean_nat_dec_eq(v_x_779_, v_zero_781_);
if (v_isZero_782_ == 1)
{
lean_dec(v_x_779_);
return v_x_780_;
}
else
{
lean_object* v_one_783_; lean_object* v_n_784_; lean_object* v___x_785_; 
v_one_783_ = lean_unsigned_to_nat(1u);
v_n_784_ = lean_nat_sub(v_x_779_, v_one_783_);
lean_dec(v_x_779_);
v___x_785_ = lean_string_push(v_x_780_, v_a_778_);
v_x_779_ = v_n_784_;
v_x_780_ = v___x_785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1___boxed(lean_object* v_a_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
uint32_t v_a_boxed_790_; lean_object* v_res_791_; 
v_a_boxed_790_ = lean_unbox_uint32(v_a_787_);
lean_dec(v_a_787_);
v_res_791_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_boxed_790_, v_x_788_, v_x_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(lean_object* v___x_792_, lean_object* v_s_793_, lean_object* v_a_794_, lean_object* v_b_795_){
_start:
{
uint8_t v_decide_796_; 
v_decide_796_ = lean_nat_dec_eq(v_a_794_, v___x_792_);
if (v_decide_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_string_utf8_next_fast(v_s_793_, v_a_794_);
lean_dec(v_a_794_);
v___x_798_ = lean_unsigned_to_nat(1u);
v___x_799_ = lean_nat_add(v_b_795_, v___x_798_);
lean_dec(v_b_795_);
v_a_794_ = v___x_797_;
v_b_795_ = v___x_799_;
goto _start;
}
else
{
lean_dec(v_a_794_);
return v_b_795_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg___boxed(lean_object* v___x_801_, lean_object* v_s_802_, lean_object* v_a_803_, lean_object* v_b_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_801_, v_s_802_, v_a_803_, v_b_804_);
lean_dec_ref(v_s_802_);
lean_dec(v___x_801_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(lean_object* v_n_806_, uint32_t v_a_807_, lean_object* v_s_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_809_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_string_utf8_byte_size(v_s_808_);
v___x_812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_811_, v_s_808_, v___x_810_, v___x_810_);
v___x_813_ = lean_nat_sub(v_n_806_, v___x_812_);
lean_dec(v___x_812_);
v___x_814_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_807_, v___x_813_, v___x_809_);
v___x_815_ = lean_string_append(v___x_814_, v_s_808_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii___boxed(lean_object* v_n_816_, lean_object* v_a_817_, lean_object* v_s_818_){
_start:
{
uint32_t v_a_boxed_819_; lean_object* v_res_820_; 
v_a_boxed_819_ = lean_unbox_uint32(v_a_817_);
lean_dec(v_a_817_);
v_res_820_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_n_816_, v_a_boxed_819_, v_s_818_);
lean_dec_ref(v_s_818_);
lean_dec(v_n_816_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(lean_object* v___x_821_, lean_object* v___x_822_, lean_object* v_s_823_, lean_object* v_inst_824_, lean_object* v_R_825_, lean_object* v_a_826_, lean_object* v_b_827_, lean_object* v_c_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_821_, v_s_823_, v_a_826_, v_b_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___boxed(lean_object* v___x_830_, lean_object* v___x_831_, lean_object* v_s_832_, lean_object* v_inst_833_, lean_object* v_R_834_, lean_object* v_a_835_, lean_object* v_b_836_, lean_object* v_c_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(v___x_830_, v___x_831_, v_s_832_, v_inst_833_, v_R_834_, v_a_835_, v_b_836_, v_c_837_);
lean_dec_ref(v_s_832_);
lean_dec_ref(v___x_831_);
lean_dec(v___x_830_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(lean_object* v_n_839_, uint32_t v_a_840_, lean_object* v_s_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_842_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_string_utf8_byte_size(v_s_841_);
v___x_845_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_844_, v_s_841_, v___x_843_, v___x_843_);
v___x_846_ = lean_nat_sub(v_n_839_, v___x_845_);
lean_dec(v___x_845_);
v___x_847_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_840_, v___x_846_, v___x_842_);
v___x_848_ = lean_string_append(v_s_841_, v___x_847_);
lean_dec_ref(v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii___boxed(lean_object* v_n_849_, lean_object* v_a_850_, lean_object* v_s_851_){
_start:
{
uint32_t v_a_boxed_852_; lean_object* v_res_853_; 
v_a_boxed_852_ = lean_unbox_uint32(v_a_850_);
lean_dec(v_a_850_);
v_res_853_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_n_849_, v_a_boxed_852_, v_s_851_);
lean_dec(v_n_849_);
return v_res_853_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_nat_to_int(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad(lean_object* v_size_857_, lean_object* v_n_858_, uint8_t v_cut_859_){
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
v___x_864_ = lean_string_utf8_byte_size(v_numStr_863_);
v___x_865_ = lean_nat_dec_lt(v_size_857_, v___x_864_);
if (v___x_865_ == 0)
{
uint32_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = 48;
v___x_867_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_size_857_, v___x_866_, v_numStr_863_);
lean_dec_ref(v_numStr_863_);
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
lean_inc_ref(v_fst_861_);
v___x_869_ = lean_string_append(v_fst_861_, v_numStr_863_);
lean_dec_ref(v_numStr_863_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_870_ = lean_nat_sub(v___x_864_, v_size_857_);
v___x_871_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_numStr_863_);
v___x_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_872_, 0, v_numStr_863_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
lean_ctor_set(v___x_872_, 2, v___x_864_);
v___x_873_ = l_String_Slice_Pos_nextn(v___x_872_, v___x_871_, v___x_870_);
lean_dec_ref_known(v___x_872_, 3);
v___x_874_ = lean_string_utf8_extract_fast(v_numStr_863_, v___x_873_, v___x_864_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___boxed(lean_object* v_size_881_, lean_object* v_n_882_, lean_object* v_cut_883_){
_start:
{
uint8_t v_cut_boxed_884_; lean_object* v_res_885_; 
v_cut_boxed_884_ = lean_unbox(v_cut_883_);
v_res_885_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_size_881_, v_n_882_, v_cut_boxed_884_);
lean_dec(v_size_881_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(lean_object* v_size_886_, lean_object* v_n_887_, uint8_t v_cut_888_){
_start:
{
lean_object* v_fst_890_; lean_object* v_snd_891_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_906_ = lean_int_dec_lt(v_n_887_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
v___x_907_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v_fst_890_ = v___x_907_;
v_snd_891_ = v_n_887_;
goto v___jp_889_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_909_ = lean_int_neg(v_n_887_);
lean_dec(v_n_887_);
v_fst_890_ = v___x_908_;
v_snd_891_ = v___x_909_;
goto v___jp_889_;
}
v___jp_889_:
{
lean_object* v_numStr_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_numStr_892_ = l_Int_repr(v_snd_891_);
lean_dec(v_snd_891_);
v___x_893_ = lean_string_length(v_numStr_892_);
v___x_894_ = lean_nat_dec_lt(v_size_886_, v___x_893_);
if (v___x_894_ == 0)
{
uint32_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = 48;
v___x_896_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_size_886_, v___x_895_, v_numStr_892_);
lean_dec(v_size_886_);
lean_inc_ref(v_fst_890_);
v___x_897_ = lean_string_append(v_fst_890_, v___x_896_);
lean_dec_ref(v___x_896_);
return v___x_897_;
}
else
{
if (v_cut_888_ == 0)
{
lean_object* v___x_898_; 
lean_dec(v_size_886_);
lean_inc_ref(v_fst_890_);
v___x_898_ = lean_string_append(v_fst_890_, v_numStr_892_);
lean_dec_ref(v_numStr_892_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_string_utf8_byte_size(v_numStr_892_);
lean_inc_ref(v_numStr_892_);
v___x_901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_901_, 0, v_numStr_892_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
lean_ctor_set(v___x_901_, 2, v___x_900_);
v___x_902_ = l_String_Slice_Pos_nextn(v___x_901_, v___x_899_, v_size_886_);
lean_dec_ref_known(v___x_901_, 3);
v___x_903_ = lean_string_utf8_extract_fast(v_numStr_892_, v___x_899_, v___x_902_);
lean_dec(v___x_902_);
lean_dec_ref(v_numStr_892_);
lean_inc_ref(v_fst_890_);
v___x_904_ = lean_string_append(v_fst_890_, v___x_903_);
lean_dec_ref(v___x_903_);
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate___boxed(lean_object* v_size_910_, lean_object* v_n_911_, lean_object* v_cut_912_){
_start:
{
uint8_t v_cut_boxed_913_; lean_object* v_res_914_; 
v_cut_boxed_913_ = lean_unbox(v_cut_912_);
v_res_914_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(v_size_910_, v_n_911_, v_cut_boxed_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(uint8_t v_x_915_){
_start:
{
if (v_x_915_ == 0)
{
lean_object* v___x_916_; 
v___x_916_ = lean_unsigned_to_nat(0u);
return v___x_916_;
}
else
{
lean_object* v___x_917_; 
v___x_917_ = lean_unsigned_to_nat(1u);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___boxed(lean_object* v_x_918_){
_start:
{
uint8_t v_x_40__boxed_919_; lean_object* v_res_920_; 
v_x_40__boxed_919_ = lean_unbox(v_x_918_);
v_res_920_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_x_40__boxed_919_);
return v_res_920_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_922_ = lean_int_neg(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(lean_object* v_symbols_923_, lean_object* v_month_924_){
_start:
{
lean_object* v_monthLong_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_monthLong_925_ = lean_ctor_get(v_symbols_923_, 0);
v___x_926_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_927_ = lean_int_add(v_month_924_, v___x_926_);
v___x_928_ = l_Int_toNat(v___x_927_);
lean_dec(v___x_927_);
v___x_929_ = lean_array_fget_borrowed(v_monthLong_925_, v___x_928_);
lean_dec(v___x_928_);
lean_inc(v___x_929_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___boxed(lean_object* v_symbols_930_, lean_object* v_month_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_930_, v_month_931_);
lean_dec(v_month_931_);
lean_dec_ref(v_symbols_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(lean_object* v_symbols_933_, lean_object* v_month_934_){
_start:
{
lean_object* v_monthShort_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_monthShort_935_ = lean_ctor_get(v_symbols_933_, 1);
v___x_936_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_937_ = lean_int_add(v_month_934_, v___x_936_);
v___x_938_ = l_Int_toNat(v___x_937_);
lean_dec(v___x_937_);
v___x_939_ = lean_array_fget_borrowed(v_monthShort_935_, v___x_938_);
lean_dec(v___x_938_);
lean_inc(v___x_939_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort___boxed(lean_object* v_symbols_940_, lean_object* v_month_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_940_, v_month_941_);
lean_dec(v_month_941_);
lean_dec_ref(v_symbols_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(lean_object* v_symbols_943_, lean_object* v_month_944_){
_start:
{
lean_object* v_monthNarrow_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_monthNarrow_945_ = lean_ctor_get(v_symbols_943_, 2);
v___x_946_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_947_ = lean_int_add(v_month_944_, v___x_946_);
v___x_948_ = l_Int_toNat(v___x_947_);
lean_dec(v___x_947_);
v___x_949_ = lean_array_fget_borrowed(v_monthNarrow_945_, v___x_948_);
lean_dec(v___x_948_);
lean_inc(v___x_949_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow___boxed(lean_object* v_symbols_950_, lean_object* v_month_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_950_, v_month_951_);
lean_dec(v_month_951_);
lean_dec_ref(v_symbols_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(lean_object* v_symbols_953_, uint8_t v_wd_954_){
_start:
{
lean_object* v_weekdayLong_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_weekdayLong_955_ = lean_ctor_get(v_symbols_953_, 3);
v___x_956_ = l_Std_Time_Weekday_toOrdinal(v_wd_954_);
v___x_957_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_958_ = lean_int_add(v___x_956_, v___x_957_);
lean_dec(v___x_956_);
v___x_959_ = l_Int_toNat(v___x_958_);
lean_dec(v___x_958_);
v___x_960_ = lean_array_fget_borrowed(v_weekdayLong_955_, v___x_959_);
lean_dec(v___x_959_);
lean_inc(v___x_960_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong___boxed(lean_object* v_symbols_961_, lean_object* v_wd_962_){
_start:
{
uint8_t v_wd_boxed_963_; lean_object* v_res_964_; 
v_wd_boxed_963_ = lean_unbox(v_wd_962_);
v_res_964_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_961_, v_wd_boxed_963_);
lean_dec_ref(v_symbols_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(lean_object* v_symbols_965_, uint8_t v_wd_966_){
_start:
{
lean_object* v_weekdayShort_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_weekdayShort_967_ = lean_ctor_get(v_symbols_965_, 4);
v___x_968_ = l_Std_Time_Weekday_toOrdinal(v_wd_966_);
v___x_969_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_970_ = lean_int_add(v___x_968_, v___x_969_);
lean_dec(v___x_968_);
v___x_971_ = l_Int_toNat(v___x_970_);
lean_dec(v___x_970_);
v___x_972_ = lean_array_fget_borrowed(v_weekdayShort_967_, v___x_971_);
lean_dec(v___x_971_);
lean_inc(v___x_972_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort___boxed(lean_object* v_symbols_973_, lean_object* v_wd_974_){
_start:
{
uint8_t v_wd_boxed_975_; lean_object* v_res_976_; 
v_wd_boxed_975_ = lean_unbox(v_wd_974_);
v_res_976_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_973_, v_wd_boxed_975_);
lean_dec_ref(v_symbols_973_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(lean_object* v_symbols_977_, uint8_t v_wd_978_){
_start:
{
lean_object* v_weekdayNarrow_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_weekdayNarrow_979_ = lean_ctor_get(v_symbols_977_, 5);
v___x_980_ = l_Std_Time_Weekday_toOrdinal(v_wd_978_);
v___x_981_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_982_ = lean_int_add(v___x_980_, v___x_981_);
lean_dec(v___x_980_);
v___x_983_ = l_Int_toNat(v___x_982_);
lean_dec(v___x_982_);
v___x_984_ = lean_array_fget_borrowed(v_weekdayNarrow_979_, v___x_983_);
lean_dec(v___x_983_);
lean_inc(v___x_984_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow___boxed(lean_object* v_symbols_985_, lean_object* v_wd_986_){
_start:
{
uint8_t v_wd_boxed_987_; lean_object* v_res_988_; 
v_wd_boxed_987_ = lean_unbox(v_wd_986_);
v_res_988_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_985_, v_wd_boxed_987_);
lean_dec_ref(v_symbols_985_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(lean_object* v_symbols_989_, uint8_t v_wd_990_){
_start:
{
lean_object* v_weekdayTwoLetter_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_weekdayTwoLetter_991_ = lean_ctor_get(v_symbols_989_, 6);
v___x_992_ = l_Std_Time_Weekday_toOrdinal(v_wd_990_);
v___x_993_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_994_ = lean_int_add(v___x_992_, v___x_993_);
lean_dec(v___x_992_);
v___x_995_ = l_Int_toNat(v___x_994_);
lean_dec(v___x_994_);
v___x_996_ = lean_array_fget_borrowed(v_weekdayTwoLetter_991_, v___x_995_);
lean_dec(v___x_995_);
lean_inc(v___x_996_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter___boxed(lean_object* v_symbols_997_, lean_object* v_wd_998_){
_start:
{
uint8_t v_wd_boxed_999_; lean_object* v_res_1000_; 
v_wd_boxed_999_ = lean_unbox(v_wd_998_);
v_res_1000_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_997_, v_wd_boxed_999_);
lean_dec_ref(v_symbols_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(lean_object* v_symbols_1001_, uint8_t v_era_1002_){
_start:
{
lean_object* v_eraShort_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_eraShort_1003_ = lean_ctor_get(v_symbols_1001_, 7);
v___x_1004_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1002_);
v___x_1005_ = lean_array_fget_borrowed(v_eraShort_1003_, v___x_1004_);
lean_dec(v___x_1004_);
lean_inc(v___x_1005_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort___boxed(lean_object* v_symbols_1006_, lean_object* v_era_1007_){
_start:
{
uint8_t v_era_boxed_1008_; lean_object* v_res_1009_; 
v_era_boxed_1008_ = lean_unbox(v_era_1007_);
v_res_1009_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1006_, v_era_boxed_1008_);
lean_dec_ref(v_symbols_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(lean_object* v_symbols_1010_, uint8_t v_era_1011_){
_start:
{
lean_object* v_eraLong_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_eraLong_1012_ = lean_ctor_get(v_symbols_1010_, 8);
v___x_1013_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1011_);
v___x_1014_ = lean_array_fget_borrowed(v_eraLong_1012_, v___x_1013_);
lean_dec(v___x_1013_);
lean_inc(v___x_1014_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong___boxed(lean_object* v_symbols_1015_, lean_object* v_era_1016_){
_start:
{
uint8_t v_era_boxed_1017_; lean_object* v_res_1018_; 
v_era_boxed_1017_ = lean_unbox(v_era_1016_);
v_res_1018_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1015_, v_era_boxed_1017_);
lean_dec_ref(v_symbols_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(lean_object* v_symbols_1019_, uint8_t v_era_1020_){
_start:
{
lean_object* v_eraNarrow_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_eraNarrow_1021_ = lean_ctor_get(v_symbols_1019_, 9);
v___x_1022_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1020_);
v___x_1023_ = lean_array_fget_borrowed(v_eraNarrow_1021_, v___x_1022_);
lean_dec(v___x_1022_);
lean_inc(v___x_1023_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow___boxed(lean_object* v_symbols_1024_, lean_object* v_era_1025_){
_start:
{
uint8_t v_era_boxed_1026_; lean_object* v_res_1027_; 
v_era_boxed_1026_ = lean_unbox(v_era_1025_);
v_res_1027_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1024_, v_era_boxed_1026_);
lean_dec_ref(v_symbols_1024_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(lean_object* v_x_1032_){
_start:
{
lean_object* v_natZero_1033_; lean_object* v_intZero_1034_; uint8_t v_isNeg_1035_; lean_object* v_a_1036_; uint8_t v_isZero_1037_; lean_object* v_one_1038_; lean_object* v_n_1039_; uint8_t v_isZero_1040_; 
v_natZero_1033_ = lean_unsigned_to_nat(0u);
v_intZero_1034_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v_isNeg_1035_ = lean_int_dec_lt(v_x_1032_, v_intZero_1034_);
v_a_1036_ = lean_nat_abs(v_x_1032_);
v_isZero_1037_ = lean_nat_dec_eq(v_a_1036_, v_natZero_1033_);
v_one_1038_ = lean_unsigned_to_nat(1u);
v_n_1039_ = lean_nat_sub(v_a_1036_, v_one_1038_);
lean_dec(v_a_1036_);
v_isZero_1040_ = lean_nat_dec_eq(v_n_1039_, v_natZero_1033_);
if (v_isZero_1040_ == 1)
{
lean_object* v___x_1041_; 
lean_dec(v_n_1039_);
v___x_1041_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
return v___x_1041_;
}
else
{
lean_object* v_n_1042_; uint8_t v_isZero_1043_; 
v_n_1042_ = lean_nat_sub(v_n_1039_, v_one_1038_);
lean_dec(v_n_1039_);
v_isZero_1043_ = lean_nat_dec_eq(v_n_1042_, v_natZero_1033_);
if (v_isZero_1043_ == 1)
{
lean_object* v___x_1044_; 
lean_dec(v_n_1042_);
v___x_1044_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
return v___x_1044_;
}
else
{
lean_object* v_n_1045_; uint8_t v_isZero_1046_; 
v_n_1045_ = lean_nat_sub(v_n_1042_, v_one_1038_);
lean_dec(v_n_1042_);
v_isZero_1046_ = lean_nat_dec_eq(v_n_1045_, v_natZero_1033_);
if (v_isZero_1046_ == 1)
{
lean_object* v___x_1047_; 
lean_dec(v_n_1045_);
v___x_1047_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
return v___x_1047_;
}
else
{
lean_object* v_n_1048_; uint8_t v_isZero_1049_; lean_object* v___x_1050_; 
v_n_1048_ = lean_nat_sub(v_n_1045_, v_one_1038_);
lean_dec(v_n_1045_);
v_isZero_1049_ = lean_nat_dec_eq(v_n_1048_, v_natZero_1033_);
lean_dec(v_n_1048_);
v___x_1050_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___boxed(lean_object* v_x_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_x_1051_);
lean_dec(v_x_1051_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(lean_object* v_symbols_1053_, lean_object* v_q_1054_){
_start:
{
lean_object* v_quarterShort_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_quarterShort_1055_ = lean_ctor_get(v_symbols_1053_, 10);
v___x_1056_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1057_ = lean_int_add(v_q_1054_, v___x_1056_);
v___x_1058_ = l_Int_toNat(v___x_1057_);
lean_dec(v___x_1057_);
v___x_1059_ = lean_array_fget_borrowed(v_quarterShort_1055_, v___x_1058_);
lean_dec(v___x_1058_);
lean_inc(v___x_1059_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort___boxed(lean_object* v_symbols_1060_, lean_object* v_q_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1060_, v_q_1061_);
lean_dec(v_q_1061_);
lean_dec_ref(v_symbols_1060_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(lean_object* v_symbols_1063_, lean_object* v_q_1064_){
_start:
{
lean_object* v_quarterLong_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_quarterLong_1065_ = lean_ctor_get(v_symbols_1063_, 11);
v___x_1066_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1067_ = lean_int_add(v_q_1064_, v___x_1066_);
v___x_1068_ = l_Int_toNat(v___x_1067_);
lean_dec(v___x_1067_);
v___x_1069_ = lean_array_fget_borrowed(v_quarterLong_1065_, v___x_1068_);
lean_dec(v___x_1068_);
lean_inc(v___x_1069_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong___boxed(lean_object* v_symbols_1070_, lean_object* v_q_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1070_, v_q_1071_);
lean_dec(v_q_1071_);
lean_dec_ref(v_symbols_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(lean_object* v_symbols_1073_, lean_object* v_q_1074_){
_start:
{
lean_object* v_quarterNarrow_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_quarterNarrow_1075_ = lean_ctor_get(v_symbols_1073_, 12);
v___x_1076_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1077_ = lean_int_add(v_q_1074_, v___x_1076_);
v___x_1078_ = l_Int_toNat(v___x_1077_);
lean_dec(v___x_1077_);
v___x_1079_ = lean_array_fget_borrowed(v_quarterNarrow_1075_, v___x_1078_);
lean_dec(v___x_1078_);
lean_inc(v___x_1079_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow___boxed(lean_object* v_symbols_1080_, lean_object* v_q_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1080_, v_q_1081_);
lean_dec(v_q_1081_);
lean_dec_ref(v_symbols_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(lean_object* v_symbols_1083_, uint8_t v_marker_1084_){
_start:
{
if (v_marker_1084_ == 0)
{
lean_object* v_amShort_1085_; 
v_amShort_1085_ = lean_ctor_get(v_symbols_1083_, 13);
lean_inc_ref(v_amShort_1085_);
return v_amShort_1085_;
}
else
{
lean_object* v_pmShort_1086_; 
v_pmShort_1086_ = lean_ctor_get(v_symbols_1083_, 14);
lean_inc_ref(v_pmShort_1086_);
return v_pmShort_1086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort___boxed(lean_object* v_symbols_1087_, lean_object* v_marker_1088_){
_start:
{
uint8_t v_marker_boxed_1089_; lean_object* v_res_1090_; 
v_marker_boxed_1089_ = lean_unbox(v_marker_1088_);
v_res_1090_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1087_, v_marker_boxed_1089_);
lean_dec_ref(v_symbols_1087_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(lean_object* v_symbols_1091_, uint8_t v_marker_1092_){
_start:
{
if (v_marker_1092_ == 0)
{
lean_object* v_amLong_1093_; 
v_amLong_1093_ = lean_ctor_get(v_symbols_1091_, 15);
lean_inc_ref(v_amLong_1093_);
return v_amLong_1093_;
}
else
{
lean_object* v_pmLong_1094_; 
v_pmLong_1094_ = lean_ctor_get(v_symbols_1091_, 16);
lean_inc_ref(v_pmLong_1094_);
return v_pmLong_1094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong___boxed(lean_object* v_symbols_1095_, lean_object* v_marker_1096_){
_start:
{
uint8_t v_marker_boxed_1097_; lean_object* v_res_1098_; 
v_marker_boxed_1097_ = lean_unbox(v_marker_1096_);
v_res_1098_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(v_symbols_1095_, v_marker_boxed_1097_);
lean_dec_ref(v_symbols_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(lean_object* v_symbols_1099_, uint8_t v_marker_1100_){
_start:
{
if (v_marker_1100_ == 0)
{
lean_object* v_amNarrow_1101_; 
v_amNarrow_1101_ = lean_ctor_get(v_symbols_1099_, 17);
lean_inc_ref(v_amNarrow_1101_);
return v_amNarrow_1101_;
}
else
{
lean_object* v_pmNarrow_1102_; 
v_pmNarrow_1102_ = lean_ctor_get(v_symbols_1099_, 18);
lean_inc_ref(v_pmNarrow_1102_);
return v_pmNarrow_1102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow___boxed(lean_object* v_symbols_1103_, lean_object* v_marker_1104_){
_start:
{
uint8_t v_marker_boxed_1105_; lean_object* v_res_1106_; 
v_marker_boxed_1105_ = lean_unbox(v_marker_1104_);
v_res_1106_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1103_, v_marker_boxed_1105_);
lean_dec_ref(v_symbols_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(lean_object* v_dp_1107_, uint8_t v_period_1108_){
_start:
{
switch(v_period_1108_)
{
case 0:
{
lean_object* v_am_1109_; 
v_am_1109_ = lean_ctor_get(v_dp_1107_, 0);
lean_inc_ref(v_am_1109_);
return v_am_1109_;
}
case 1:
{
lean_object* v_pm_1110_; 
v_pm_1110_ = lean_ctor_get(v_dp_1107_, 1);
lean_inc_ref(v_pm_1110_);
return v_pm_1110_;
}
case 2:
{
lean_object* v_noon_1111_; 
v_noon_1111_ = lean_ctor_get(v_dp_1107_, 2);
lean_inc_ref(v_noon_1111_);
return v_noon_1111_;
}
default: 
{
lean_object* v_midnight_1112_; 
v_midnight_1112_ = lean_ctor_get(v_dp_1107_, 3);
lean_inc_ref(v_midnight_1112_);
return v_midnight_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod___boxed(lean_object* v_dp_1113_, lean_object* v_period_1114_){
_start:
{
uint8_t v_period_boxed_1115_; lean_object* v_res_1116_; 
v_period_boxed_1115_ = lean_unbox(v_period_1114_);
v_res_1116_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dp_1113_, v_period_boxed_1115_);
lean_dec_ref(v_dp_1113_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t v_x_1117_){
_start:
{
switch(v_x_1117_)
{
case 0:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_unsigned_to_nat(0u);
return v___x_1118_;
}
case 1:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_unsigned_to_nat(1u);
return v___x_1119_;
}
case 2:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_unsigned_to_nat(2u);
return v___x_1120_;
}
case 3:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_unsigned_to_nat(3u);
return v___x_1121_;
}
case 4:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_unsigned_to_nat(4u);
return v___x_1122_;
}
default: 
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_unsigned_to_nat(5u);
return v___x_1123_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object* v_x_1124_){
_start:
{
uint8_t v_x_112__boxed_1125_; lean_object* v_res_1126_; 
v_x_112__boxed_1125_ = lean_unbox(v_x_1124_);
v_res_1126_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_x_112__boxed_1125_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(lean_object* v_arr_1127_, uint8_t v_period_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_period_1128_);
v___x_1130_ = lean_array_fget_borrowed(v_arr_1127_, v___x_1129_);
lean_dec(v___x_1129_);
lean_inc(v___x_1130_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod___boxed(lean_object* v_arr_1131_, lean_object* v_period_1132_){
_start:
{
uint8_t v_period_boxed_1133_; lean_object* v_res_1134_; 
v_period_boxed_1133_ = lean_unbox(v_period_1132_);
v_res_1134_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_arr_1131_, v_period_boxed_1133_);
lean_dec_ref(v_arr_1131_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(lean_object* v_data_1136_){
_start:
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1138_ = lean_int_dec_lt(v_data_1136_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1140_ = l_Int_repr(v_data_1136_);
v___x_1141_ = lean_string_append(v___x_1139_, v___x_1140_);
lean_dec_ref(v___x_1140_);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Int_repr(v_data_1136_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___boxed(lean_object* v_data_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(v_data_1143_);
lean_dec(v_data_1143_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(uint8_t v_x_1145_){
_start:
{
switch(v_x_1145_)
{
case 0:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
return v___x_1146_;
}
case 1:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_unsigned_to_nat(1u);
return v___x_1147_;
}
default: 
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_unsigned_to_nat(2u);
return v___x_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___boxed(lean_object* v_x_1149_){
_start:
{
uint8_t v_x_boxed_1150_; lean_object* v_res_1151_; 
v_x_boxed_1150_ = lean_unbox(v_x_1149_);
v_res_1151_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_x_boxed_1150_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(lean_object* v_k_1152_){
_start:
{
lean_inc(v_k_1152_);
return v_k_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg___boxed(lean_object* v_k_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(v_k_1153_);
lean_dec(v_k_1153_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_object* v_motive_1155_, lean_object* v_ctorIdx_1156_, uint8_t v_t_1157_, lean_object* v_h_1158_, lean_object* v_k_1159_){
_start:
{
lean_inc(v_k_1159_);
return v_k_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___boxed(lean_object* v_motive_1160_, lean_object* v_ctorIdx_1161_, lean_object* v_t_1162_, lean_object* v_h_1163_, lean_object* v_k_1164_){
_start:
{
uint8_t v_t_boxed_1165_; lean_object* v_res_1166_; 
v_t_boxed_1165_ = lean_unbox(v_t_1162_);
v_res_1166_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(v_motive_1160_, v_ctorIdx_1161_, v_t_boxed_1165_, v_h_1163_, v_k_1164_);
lean_dec(v_k_1164_);
lean_dec(v_ctorIdx_1161_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(lean_object* v_yes_1167_){
_start:
{
lean_inc(v_yes_1167_);
return v_yes_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg___boxed(lean_object* v_yes_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(v_yes_1168_);
lean_dec(v_yes_1168_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_object* v_motive_1170_, uint8_t v_t_1171_, lean_object* v_h_1172_, lean_object* v_yes_1173_){
_start:
{
lean_inc(v_yes_1173_);
return v_yes_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___boxed(lean_object* v_motive_1174_, lean_object* v_t_1175_, lean_object* v_h_1176_, lean_object* v_yes_1177_){
_start:
{
uint8_t v_t_boxed_1178_; lean_object* v_res_1179_; 
v_t_boxed_1178_ = lean_unbox(v_t_1175_);
v_res_1179_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(v_motive_1174_, v_t_boxed_1178_, v_h_1176_, v_yes_1177_);
lean_dec(v_yes_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(lean_object* v_no_1180_){
_start:
{
lean_inc(v_no_1180_);
return v_no_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg___boxed(lean_object* v_no_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(v_no_1181_);
lean_dec(v_no_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_object* v_motive_1183_, uint8_t v_t_1184_, lean_object* v_h_1185_, lean_object* v_no_1186_){
_start:
{
lean_inc(v_no_1186_);
return v_no_1186_;
}
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_object* v_motive_1196_, uint8_t v_t_1197_, lean_object* v_h_1198_, lean_object* v_optional_1199_){
_start:
{
lean_inc(v_optional_1199_);
return v_optional_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___boxed(lean_object* v_motive_1200_, lean_object* v_t_1201_, lean_object* v_h_1202_, lean_object* v_optional_1203_){
_start:
{
uint8_t v_t_boxed_1204_; lean_object* v_res_1205_; 
v_t_boxed_1204_ = lean_unbox(v_t_1201_);
v_res_1205_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(v_motive_1200_, v_t_boxed_1204_, v_h_1202_, v_optional_1203_);
lean_dec(v_optional_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(uint8_t v_x_1206_, uint8_t v_y_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_x_1206_);
v___x_1209_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_y_1207_);
v___x_1210_ = lean_nat_dec_eq(v___x_1208_, v___x_1209_);
lean_dec(v___x_1209_);
lean_dec(v___x_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq___boxed(lean_object* v_x_1211_, lean_object* v_y_1212_){
_start:
{
uint8_t v_x_21__boxed_1213_; uint8_t v_y_22__boxed_1214_; uint8_t v_res_1215_; lean_object* v_r_1216_; 
v_x_21__boxed_1213_ = lean_unbox(v_x_1211_);
v_y_22__boxed_1214_ = lean_unbox(v_y_1212_);
v_res_1215_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_x_21__boxed_1213_, v_y_22__boxed_1214_);
v_r_1216_ = lean_box(v_res_1215_);
return v_r_1216_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__1(lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Rat_ofInt(v_a_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_unsigned_to_nat(1000000000u);
v___x_1223_ = lean_nat_to_int(v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(lean_object* v_offset_1224_, uint8_t v_withMinutes_1225_, uint8_t v_withSeconds_1226_, uint8_t v_colon_1227_, uint8_t v_padHour_1228_){
_start:
{
lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; uint32_t v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; uint32_t v___y_1243_; lean_object* v___y_1247_; uint8_t v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; uint32_t v___y_1251_; uint8_t v___y_1252_; uint8_t v___y_1254_; lean_object* v___y_1255_; uint8_t v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; uint32_t v___y_1259_; uint8_t v___y_1260_; uint8_t v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; uint8_t v___y_1265_; lean_object* v___y_1266_; uint32_t v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1275_; uint8_t v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; uint8_t v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; uint32_t v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1289_; uint8_t v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; uint8_t v___y_1293_; lean_object* v___y_1294_; uint32_t v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1300_; uint8_t v___y_1301_; lean_object* v___y_1302_; uint8_t v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; uint8_t v___y_1306_; lean_object* v___y_1307_; uint32_t v___y_1308_; uint8_t v___y_1309_; lean_object* v___y_1311_; uint8_t v___y_1312_; uint8_t v___y_1313_; lean_object* v___y_1314_; uint8_t v___y_1315_; lean_object* v___y_1316_; uint8_t v___y_1317_; lean_object* v___y_1318_; uint32_t v___y_1319_; lean_object* v___y_1320_; uint8_t v___y_1321_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; uint32_t v___y_1326_; lean_object* v___y_1327_; lean_object* v_fst_1340_; lean_object* v_snd_1341_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1352_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1353_ = lean_int_dec_le(v___x_1352_, v_offset_1224_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1355_ = lean_int_neg(v_offset_1224_);
lean_dec(v_offset_1224_);
v_fst_1340_ = v___x_1354_;
v_snd_1341_ = v___x_1355_;
goto v___jp_1339_;
}
else
{
lean_object* v___x_1356_; 
v___x_1356_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1340_ = v___x_1356_;
v_snd_1341_ = v_offset_1224_;
goto v___jp_1339_;
}
v___jp_1229_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1235_ = lean_string_append(v___y_1232_, v___y_1234_);
v___x_1236_ = l_Int_repr(v___y_1231_);
lean_dec(v___y_1231_);
v___x_1237_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1230_, v___y_1233_, v___x_1236_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = lean_string_append(v___x_1235_, v___x_1237_);
lean_dec_ref(v___x_1237_);
return v___x_1238_;
}
v___jp_1239_:
{
if (v_colon_1227_ == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___y_1230_ = v___y_1240_;
v___y_1231_ = v___y_1241_;
v___y_1232_ = v___y_1242_;
v___y_1233_ = v___y_1243_;
v___y_1234_ = v___x_1244_;
goto v___jp_1229_;
}
else
{
lean_object* v___x_1245_; 
v___x_1245_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1230_ = v___y_1240_;
v___y_1231_ = v___y_1241_;
v___y_1232_ = v___y_1242_;
v___y_1233_ = v___y_1243_;
v___y_1234_ = v___x_1245_;
goto v___jp_1229_;
}
}
v___jp_1246_:
{
if (v___y_1248_ == 0)
{
if (v___y_1252_ == 0)
{
lean_dec(v___y_1250_);
return v___y_1249_;
}
else
{
v___y_1240_ = v___y_1247_;
v___y_1241_ = v___y_1250_;
v___y_1242_ = v___y_1249_;
v___y_1243_ = v___y_1251_;
goto v___jp_1239_;
}
}
else
{
v___y_1240_ = v___y_1247_;
v___y_1241_ = v___y_1250_;
v___y_1242_ = v___y_1249_;
v___y_1243_ = v___y_1251_;
goto v___jp_1239_;
}
}
v___jp_1253_:
{
if (v___y_1254_ == 0)
{
v___y_1247_ = v___y_1255_;
v___y_1248_ = v___y_1256_;
v___y_1249_ = v___y_1258_;
v___y_1250_ = v___y_1257_;
v___y_1251_ = v___y_1259_;
v___y_1252_ = v___y_1254_;
goto v___jp_1246_;
}
else
{
v___y_1247_ = v___y_1255_;
v___y_1248_ = v___y_1256_;
v___y_1249_ = v___y_1258_;
v___y_1250_ = v___y_1257_;
v___y_1251_ = v___y_1259_;
v___y_1252_ = v___y_1260_;
goto v___jp_1246_;
}
}
v___jp_1261_:
{
uint8_t v___x_1269_; uint8_t v___x_1270_; uint8_t v___x_1271_; 
v___x_1269_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1226_, v___y_1262_);
v___x_1270_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1226_, v___y_1265_);
v___x_1271_ = lean_int_dec_eq(v___y_1264_, v___y_1266_);
if (v___x_1271_ == 0)
{
uint8_t v___x_1272_; 
v___x_1272_ = 1;
v___y_1254_ = v___x_1270_;
v___y_1255_ = v___y_1263_;
v___y_1256_ = v___x_1269_;
v___y_1257_ = v___y_1264_;
v___y_1258_ = v___y_1268_;
v___y_1259_ = v___y_1267_;
v___y_1260_ = v___x_1272_;
goto v___jp_1253_;
}
else
{
uint8_t v___x_1273_; 
v___x_1273_ = 0;
v___y_1254_ = v___x_1270_;
v___y_1255_ = v___y_1263_;
v___y_1256_ = v___x_1269_;
v___y_1257_ = v___y_1264_;
v___y_1258_ = v___y_1268_;
v___y_1259_ = v___y_1267_;
v___y_1260_ = v___x_1273_;
goto v___jp_1253_;
}
}
v___jp_1274_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_string_append(v___y_1277_, v___y_1283_);
v___x_1285_ = l_Int_repr(v___y_1275_);
lean_dec(v___y_1275_);
v___x_1286_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1278_, v___y_1282_, v___x_1285_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = lean_string_append(v___x_1284_, v___x_1286_);
lean_dec_ref(v___x_1286_);
v___y_1262_ = v___y_1276_;
v___y_1263_ = v___y_1278_;
v___y_1264_ = v___y_1280_;
v___y_1265_ = v___y_1279_;
v___y_1266_ = v___y_1281_;
v___y_1267_ = v___y_1282_;
v___y_1268_ = v___x_1287_;
goto v___jp_1261_;
}
v___jp_1288_:
{
if (v_colon_1227_ == 0)
{
lean_object* v___x_1297_; 
v___x_1297_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___y_1275_ = v___y_1289_;
v___y_1276_ = v___y_1290_;
v___y_1277_ = v___y_1291_;
v___y_1278_ = v___y_1292_;
v___y_1279_ = v___y_1293_;
v___y_1280_ = v___y_1294_;
v___y_1281_ = v___y_1296_;
v___y_1282_ = v___y_1295_;
v___y_1283_ = v___x_1297_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1298_; 
v___x_1298_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1275_ = v___y_1289_;
v___y_1276_ = v___y_1290_;
v___y_1277_ = v___y_1291_;
v___y_1278_ = v___y_1292_;
v___y_1279_ = v___y_1293_;
v___y_1280_ = v___y_1294_;
v___y_1281_ = v___y_1296_;
v___y_1282_ = v___y_1295_;
v___y_1283_ = v___x_1298_;
goto v___jp_1274_;
}
}
v___jp_1299_:
{
if (v___y_1303_ == 0)
{
if (v___y_1309_ == 0)
{
lean_dec(v___y_1300_);
v___y_1262_ = v___y_1301_;
v___y_1263_ = v___y_1304_;
v___y_1264_ = v___y_1305_;
v___y_1265_ = v___y_1306_;
v___y_1266_ = v___y_1307_;
v___y_1267_ = v___y_1308_;
v___y_1268_ = v___y_1302_;
goto v___jp_1261_;
}
else
{
v___y_1289_ = v___y_1300_;
v___y_1290_ = v___y_1301_;
v___y_1291_ = v___y_1302_;
v___y_1292_ = v___y_1304_;
v___y_1293_ = v___y_1306_;
v___y_1294_ = v___y_1305_;
v___y_1295_ = v___y_1308_;
v___y_1296_ = v___y_1307_;
goto v___jp_1288_;
}
}
else
{
v___y_1289_ = v___y_1300_;
v___y_1290_ = v___y_1301_;
v___y_1291_ = v___y_1302_;
v___y_1292_ = v___y_1304_;
v___y_1293_ = v___y_1306_;
v___y_1294_ = v___y_1305_;
v___y_1295_ = v___y_1308_;
v___y_1296_ = v___y_1307_;
goto v___jp_1288_;
}
}
v___jp_1310_:
{
if (v___y_1312_ == 0)
{
v___y_1300_ = v___y_1311_;
v___y_1301_ = v___y_1313_;
v___y_1302_ = v___y_1314_;
v___y_1303_ = v___y_1315_;
v___y_1304_ = v___y_1316_;
v___y_1305_ = v___y_1318_;
v___y_1306_ = v___y_1317_;
v___y_1307_ = v___y_1320_;
v___y_1308_ = v___y_1319_;
v___y_1309_ = v___y_1312_;
goto v___jp_1299_;
}
else
{
v___y_1300_ = v___y_1311_;
v___y_1301_ = v___y_1313_;
v___y_1302_ = v___y_1314_;
v___y_1303_ = v___y_1315_;
v___y_1304_ = v___y_1316_;
v___y_1305_ = v___y_1318_;
v___y_1306_ = v___y_1317_;
v___y_1307_ = v___y_1320_;
v___y_1308_ = v___y_1319_;
v___y_1309_ = v___y_1321_;
goto v___jp_1299_;
}
}
v___jp_1322_:
{
lean_object* v_minute_1328_; lean_object* v_second_1329_; uint8_t v___x_1330_; uint8_t v___x_1331_; lean_object* v_data_1332_; uint8_t v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_minute_1328_ = lean_ctor_get(v___y_1325_, 1);
lean_inc(v_minute_1328_);
v_second_1329_ = lean_ctor_get(v___y_1325_, 2);
lean_inc(v_second_1329_);
lean_dec_ref(v___y_1325_);
v___x_1330_ = 0;
v___x_1331_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1225_, v___x_1330_);
lean_inc_ref(v___y_1323_);
v_data_1332_ = lean_string_append(v___y_1323_, v___y_1327_);
lean_dec_ref(v___y_1327_);
v___x_1333_ = 2;
v___x_1334_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1225_, v___x_1333_);
v___x_1335_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1336_ = lean_int_dec_eq(v_minute_1328_, v___x_1335_);
if (v___x_1336_ == 0)
{
uint8_t v___x_1337_; 
v___x_1337_ = 1;
v___y_1311_ = v_minute_1328_;
v___y_1312_ = v___x_1334_;
v___y_1313_ = v___x_1330_;
v___y_1314_ = v_data_1332_;
v___y_1315_ = v___x_1331_;
v___y_1316_ = v___y_1324_;
v___y_1317_ = v___x_1333_;
v___y_1318_ = v_second_1329_;
v___y_1319_ = v___y_1326_;
v___y_1320_ = v___x_1335_;
v___y_1321_ = v___x_1337_;
goto v___jp_1310_;
}
else
{
uint8_t v___x_1338_; 
v___x_1338_ = 0;
v___y_1311_ = v_minute_1328_;
v___y_1312_ = v___x_1334_;
v___y_1313_ = v___x_1330_;
v___y_1314_ = v_data_1332_;
v___y_1315_ = v___x_1331_;
v___y_1316_ = v___y_1324_;
v___y_1317_ = v___x_1333_;
v___y_1318_ = v_second_1329_;
v___y_1319_ = v___y_1326_;
v___y_1320_ = v___x_1335_;
v___y_1321_ = v___x_1338_;
goto v___jp_1310_;
}
}
v___jp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v_time_1344_; lean_object* v___x_1345_; uint32_t v___x_1346_; 
v___x_1342_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1343_ = lean_int_mul(v_snd_1341_, v___x_1342_);
lean_dec(v_snd_1341_);
v_time_1344_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1343_);
lean_dec(v___x_1343_);
v___x_1345_ = lean_unsigned_to_nat(2u);
v___x_1346_ = 48;
if (v_padHour_1228_ == 0)
{
lean_object* v_hour_1347_; lean_object* v___x_1348_; 
v_hour_1347_ = lean_ctor_get(v_time_1344_, 0);
v___x_1348_ = l_Int_repr(v_hour_1347_);
v___y_1323_ = v_fst_1340_;
v___y_1324_ = v___x_1345_;
v___y_1325_ = v_time_1344_;
v___y_1326_ = v___x_1346_;
v___y_1327_ = v___x_1348_;
goto v___jp_1322_;
}
else
{
lean_object* v_hour_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_hour_1349_ = lean_ctor_get(v_time_1344_, 0);
v___x_1350_ = l_Int_repr(v_hour_1349_);
v___x_1351_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1345_, v___x_1346_, v___x_1350_);
lean_dec_ref(v___x_1350_);
v___y_1323_ = v_fst_1340_;
v___y_1324_ = v___x_1345_;
v___y_1325_ = v_time_1344_;
v___y_1326_ = v___x_1346_;
v___y_1327_ = v___x_1351_;
goto v___jp_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___boxed(lean_object* v_offset_1357_, lean_object* v_withMinutes_1358_, lean_object* v_withSeconds_1359_, lean_object* v_colon_1360_, lean_object* v_padHour_1361_){
_start:
{
uint8_t v_withMinutes_boxed_1362_; uint8_t v_withSeconds_boxed_1363_; uint8_t v_colon_boxed_1364_; uint8_t v_padHour_boxed_1365_; lean_object* v_res_1366_; 
v_withMinutes_boxed_1362_ = lean_unbox(v_withMinutes_1358_);
v_withSeconds_boxed_1363_ = lean_unbox(v_withSeconds_1359_);
v_colon_boxed_1364_ = lean_unbox(v_colon_1360_);
v_padHour_boxed_1365_ = lean_unbox(v_padHour_1361_);
v_res_1366_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1357_, v_withMinutes_boxed_1362_, v_withSeconds_boxed_1363_, v_colon_boxed_1364_, v_padHour_boxed_1365_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0_spec__0(lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_nat_to_int(v_a_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(lean_object* v_a_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_nat_to_int(v_a_1369_);
v___x_1371_ = l_Rat_ofInt(v___x_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l_Std_Time_classifyDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_unsigned_to_nat(12u);
v___x_1373_ = lean_nat_to_int(v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod(lean_object* v_hour_1374_, lean_object* v_minute_1375_, lean_object* v_second_1376_){
_start:
{
lean_object* v___y_1378_; uint8_t v___y_1379_; uint8_t v___y_1385_; uint8_t v___y_1386_; lean_object* v___x_1390_; uint8_t v___x_1391_; uint8_t v___y_1393_; uint8_t v___x_1394_; 
v___x_1390_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1391_ = lean_int_dec_eq(v_hour_1374_, v___x_1390_);
v___x_1394_ = lean_int_dec_eq(v_minute_1375_, v___x_1390_);
if (v___x_1394_ == 0)
{
v___y_1393_ = v___x_1394_;
goto v___jp_1392_;
}
else
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_int_dec_eq(v_second_1376_, v___x_1390_);
v___y_1393_ = v___x_1395_;
goto v___jp_1392_;
}
v___jp_1377_:
{
if (v___y_1379_ == 0)
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_int_dec_lt(v_hour_1374_, v___y_1378_);
if (v___x_1380_ == 0)
{
uint8_t v___x_1381_; 
v___x_1381_ = 1;
return v___x_1381_;
}
else
{
uint8_t v___x_1382_; 
v___x_1382_ = 0;
return v___x_1382_;
}
}
else
{
uint8_t v___x_1383_; 
v___x_1383_ = 2;
return v___x_1383_;
}
}
v___jp_1384_:
{
if (v___y_1386_ == 0)
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1388_ = lean_int_dec_eq(v_hour_1374_, v___x_1387_);
if (v___x_1388_ == 0)
{
v___y_1378_ = v___x_1387_;
v___y_1379_ = v___x_1388_;
goto v___jp_1377_;
}
else
{
v___y_1378_ = v___x_1387_;
v___y_1379_ = v___y_1385_;
goto v___jp_1377_;
}
}
else
{
uint8_t v___x_1389_; 
v___x_1389_ = 3;
return v___x_1389_;
}
}
v___jp_1392_:
{
if (v___x_1391_ == 0)
{
v___y_1385_ = v___y_1393_;
v___y_1386_ = v___x_1391_;
goto v___jp_1384_;
}
else
{
v___y_1385_ = v___y_1393_;
v___y_1386_ = v___y_1393_;
goto v___jp_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___boxed(lean_object* v_hour_1396_, lean_object* v_minute_1397_, lean_object* v_second_1398_){
_start:
{
uint8_t v_res_1399_; lean_object* v_r_1400_; 
v_res_1399_ = l_Std_Time_classifyDayPeriod(v_hour_1396_, v_minute_1397_, v_second_1398_);
lean_dec(v_second_1398_);
lean_dec(v_minute_1397_);
lean_dec(v_hour_1396_);
v_r_1400_ = lean_box(v_res_1399_);
return v_r_1400_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_unsigned_to_nat(6u);
v___x_1402_ = lean_nat_to_int(v___x_1401_);
return v___x_1402_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__1(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_unsigned_to_nat(18u);
v___x_1404_ = lean_nat_to_int(v___x_1403_);
return v___x_1404_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__2(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_unsigned_to_nat(21u);
v___x_1406_ = lean_nat_to_int(v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object* v_hour_1407_, lean_object* v_minute_1408_, lean_object* v_second_1409_){
_start:
{
lean_object* v___y_1411_; uint8_t v___y_1412_; uint8_t v___y_1427_; uint8_t v___y_1428_; lean_object* v___x_1432_; uint8_t v___x_1433_; uint8_t v___y_1435_; uint8_t v___x_1436_; 
v___x_1432_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1433_ = lean_int_dec_eq(v_hour_1407_, v___x_1432_);
v___x_1436_ = lean_int_dec_eq(v_minute_1408_, v___x_1432_);
if (v___x_1436_ == 0)
{
v___y_1435_ = v___x_1436_;
goto v___jp_1434_;
}
else
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_int_dec_eq(v_second_1409_, v___x_1432_);
v___y_1435_ = v___x_1437_;
goto v___jp_1434_;
}
v___jp_1410_:
{
if (v___y_1412_ == 0)
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_1414_ = lean_int_dec_lt(v_hour_1407_, v___x_1413_);
if (v___x_1414_ == 0)
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_int_dec_lt(v_hour_1407_, v___y_1411_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__1, &l_Std_Time_classifyExtendedDayPeriod___closed__1_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__1);
v___x_1417_ = lean_int_dec_lt(v_hour_1407_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__2, &l_Std_Time_classifyExtendedDayPeriod___closed__2_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__2);
v___x_1419_ = lean_int_dec_lt(v_hour_1407_, v___x_1418_);
if (v___x_1419_ == 0)
{
uint8_t v___x_1420_; 
v___x_1420_ = 1;
return v___x_1420_;
}
else
{
uint8_t v___x_1421_; 
v___x_1421_ = 5;
return v___x_1421_;
}
}
else
{
uint8_t v___x_1422_; 
v___x_1422_ = 4;
return v___x_1422_;
}
}
else
{
uint8_t v___x_1423_; 
v___x_1423_ = 2;
return v___x_1423_;
}
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = 1;
return v___x_1424_;
}
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = 3;
return v___x_1425_;
}
}
v___jp_1426_:
{
if (v___y_1428_ == 0)
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1430_ = lean_int_dec_eq(v_hour_1407_, v___x_1429_);
if (v___x_1430_ == 0)
{
v___y_1411_ = v___x_1429_;
v___y_1412_ = v___x_1430_;
goto v___jp_1410_;
}
else
{
v___y_1411_ = v___x_1429_;
v___y_1412_ = v___y_1427_;
goto v___jp_1410_;
}
}
else
{
uint8_t v___x_1431_; 
v___x_1431_ = 0;
return v___x_1431_;
}
}
v___jp_1434_:
{
if (v___x_1433_ == 0)
{
v___y_1427_ = v___y_1435_;
v___y_1428_ = v___x_1433_;
goto v___jp_1426_;
}
else
{
v___y_1427_ = v___y_1435_;
v___y_1428_ = v___y_1435_;
goto v___jp_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyExtendedDayPeriod___boxed(lean_object* v_hour_1438_, lean_object* v_minute_1439_, lean_object* v_second_1440_){
_start:
{
uint8_t v_res_1441_; lean_object* v_r_1442_; 
v_res_1441_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1438_, v_minute_1439_, v_second_1440_);
lean_dec(v_second_1440_);
lean_dec(v_minute_1439_);
lean_dec(v_hour_1438_);
v_r_1442_ = lean_box(v_res_1441_);
return v_r_1442_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_unsigned_to_nat(100u);
v___x_1444_ = lean_nat_to_int(v___x_1443_);
return v___x_1444_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_unsigned_to_nat(7u);
v___x_1446_ = lean_nat_to_int(v___x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object* v_dateformat_1450_, lean_object* v_modifier_1451_, lean_object* v_data_1452_){
_start:
{
switch(lean_obj_tag(v_modifier_1451_))
{
case 0:
{
uint8_t v_presentation_1453_; 
v_presentation_1453_ = lean_ctor_get_uint8(v_modifier_1451_, 0);
lean_dec_ref_known(v_modifier_1451_, 0);
switch(v_presentation_1453_)
{
case 1:
{
lean_object* v_symbols_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; 
v_symbols_1454_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1455_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1456_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1454_, v___x_1455_);
return v___x_1456_;
}
case 2:
{
lean_object* v_symbols_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; 
v_symbols_1457_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1458_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1459_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1457_, v___x_1458_);
return v___x_1459_;
}
default: 
{
lean_object* v_symbols_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; 
v_symbols_1460_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1461_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1462_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1460_, v___x_1461_);
return v___x_1462_;
}
}
}
case 1:
{
lean_object* v_presentation_1463_; 
v_presentation_1463_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1463_);
lean_dec_ref_known(v_modifier_1451_, 1);
switch(lean_obj_tag(v_presentation_1463_))
{
case 0:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = 0;
v___x_1466_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1464_, v_data_1452_, v___x_1465_);
return v___x_1466_;
}
case 1:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1467_ = lean_unsigned_to_nat(2u);
v___x_1468_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1469_ = lean_int_emod(v_data_1452_, v___x_1468_);
lean_dec(v_data_1452_);
v___x_1470_ = 0;
v___x_1471_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1467_, v___x_1469_, v___x_1470_);
return v___x_1471_;
}
case 2:
{
lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = lean_unsigned_to_nat(4u);
v___x_1473_ = 0;
v___x_1474_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1472_, v_data_1452_, v___x_1473_);
return v___x_1474_;
}
default: 
{
lean_object* v_num_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; 
v_num_1475_ = lean_ctor_get(v_presentation_1463_, 0);
lean_inc(v_num_1475_);
lean_dec_ref_known(v_presentation_1463_, 1);
v___x_1476_ = 0;
v___x_1477_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1475_, v_data_1452_, v___x_1476_);
lean_dec(v_num_1475_);
return v___x_1477_;
}
}
}
case 2:
{
lean_object* v_presentation_1478_; lean_object* v___x_1479_; lean_object* v___y_1481_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_presentation_1478_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1478_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1479_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1496_ = lean_int_dec_le(v_data_1452_, v___x_1495_);
if (v___x_1496_ == 0)
{
v___y_1481_ = v_data_1452_;
goto v___jp_1480_;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_int_neg(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1498_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1499_ = lean_int_add(v___x_1497_, v___x_1498_);
lean_dec(v___x_1497_);
v___y_1481_ = v___x_1499_;
goto v___jp_1480_;
}
v___jp_1480_:
{
switch(lean_obj_tag(v_presentation_1478_))
{
case 0:
{
uint8_t v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = 0;
v___x_1483_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1479_, v___y_1481_, v___x_1482_);
return v___x_1483_;
}
case 1:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1484_ = lean_unsigned_to_nat(2u);
v___x_1485_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1486_ = lean_int_emod(v___y_1481_, v___x_1485_);
lean_dec(v___y_1481_);
v___x_1487_ = 0;
v___x_1488_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1484_, v___x_1486_, v___x_1487_);
return v___x_1488_;
}
case 2:
{
lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = lean_unsigned_to_nat(4u);
v___x_1490_ = 0;
v___x_1491_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1489_, v___y_1481_, v___x_1490_);
return v___x_1491_;
}
default: 
{
lean_object* v_num_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; 
v_num_1492_ = lean_ctor_get(v_presentation_1478_, 0);
lean_inc(v_num_1492_);
lean_dec_ref_known(v_presentation_1478_, 1);
v___x_1493_ = 0;
v___x_1494_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1492_, v___y_1481_, v___x_1493_);
lean_dec(v_num_1492_);
return v___x_1494_;
}
}
}
}
case 3:
{
lean_object* v_presentation_1500_; lean_object* v_snd_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; 
v_presentation_1500_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1500_);
lean_dec_ref_known(v_modifier_1451_, 1);
v_snd_1501_ = lean_ctor_get(v_data_1452_, 1);
lean_inc(v_snd_1501_);
lean_dec(v_data_1452_);
v___x_1502_ = 0;
v___x_1503_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1500_, v_snd_1501_, v___x_1502_);
lean_dec(v_presentation_1500_);
return v___x_1503_;
}
case 4:
{
lean_object* v_presentation_1504_; 
v_presentation_1504_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc_ref(v_presentation_1504_);
lean_dec_ref_known(v_modifier_1451_, 1);
if (lean_obj_tag(v_presentation_1504_) == 0)
{
lean_object* v_val_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; 
v_val_1505_ = lean_ctor_get(v_presentation_1504_, 0);
lean_inc(v_val_1505_);
lean_dec_ref_known(v_presentation_1504_, 1);
v___x_1506_ = 0;
v___x_1507_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1505_, v_data_1452_, v___x_1506_);
lean_dec(v_val_1505_);
return v___x_1507_;
}
else
{
lean_object* v_val_1508_; uint8_t v___x_1509_; 
v_val_1508_ = lean_ctor_get(v_presentation_1504_, 0);
lean_inc(v_val_1508_);
lean_dec_ref_known(v_presentation_1504_, 1);
v___x_1509_ = lean_unbox(v_val_1508_);
lean_dec(v_val_1508_);
switch(v___x_1509_)
{
case 1:
{
lean_object* v_symbols_1510_; lean_object* v___x_1511_; 
v_symbols_1510_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1511_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1510_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1511_;
}
case 2:
{
lean_object* v_symbols_1512_; lean_object* v___x_1513_; 
v_symbols_1512_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1513_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1512_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1513_;
}
default: 
{
lean_object* v_symbols_1514_; lean_object* v___x_1515_; 
v_symbols_1514_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1515_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1514_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1515_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1516_; 
v_presentation_1516_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc_ref(v_presentation_1516_);
lean_dec_ref_known(v_modifier_1451_, 1);
if (lean_obj_tag(v_presentation_1516_) == 0)
{
lean_object* v_val_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; 
v_val_1517_ = lean_ctor_get(v_presentation_1516_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v_presentation_1516_, 1);
v___x_1518_ = 0;
v___x_1519_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1517_, v_data_1452_, v___x_1518_);
lean_dec(v_val_1517_);
return v___x_1519_;
}
else
{
lean_object* v_val_1520_; uint8_t v___x_1521_; 
v_val_1520_ = lean_ctor_get(v_presentation_1516_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v_presentation_1516_, 1);
v___x_1521_ = lean_unbox(v_val_1520_);
lean_dec(v_val_1520_);
switch(v___x_1521_)
{
case 1:
{
lean_object* v_symbols_1522_; lean_object* v___x_1523_; 
v_symbols_1522_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1523_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1522_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1523_;
}
case 2:
{
lean_object* v_symbols_1524_; lean_object* v___x_1525_; 
v_symbols_1524_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1525_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1524_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1525_;
}
default: 
{
lean_object* v_symbols_1526_; lean_object* v___x_1527_; 
v_symbols_1526_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1527_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1526_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1527_;
}
}
}
}
case 6:
{
lean_object* v_presentation_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; 
v_presentation_1528_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1528_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1529_ = 0;
v___x_1530_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1528_, v_data_1452_, v___x_1529_);
lean_dec(v_presentation_1528_);
return v___x_1530_;
}
case 7:
{
lean_object* v_presentation_1531_; 
v_presentation_1531_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc_ref(v_presentation_1531_);
lean_dec_ref_known(v_modifier_1451_, 1);
if (lean_obj_tag(v_presentation_1531_) == 0)
{
lean_object* v_val_1532_; uint8_t v___x_1533_; lean_object* v___x_1534_; 
v_val_1532_ = lean_ctor_get(v_presentation_1531_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v_presentation_1531_, 1);
v___x_1533_ = 0;
v___x_1534_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1532_, v_data_1452_, v___x_1533_);
lean_dec(v_val_1532_);
return v___x_1534_;
}
else
{
lean_object* v_val_1535_; uint8_t v___x_1536_; 
v_val_1535_ = lean_ctor_get(v_presentation_1531_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v_presentation_1531_, 1);
v___x_1536_ = lean_unbox(v_val_1535_);
lean_dec(v_val_1535_);
switch(v___x_1536_)
{
case 0:
{
lean_object* v_symbols_1537_; lean_object* v___x_1538_; 
v_symbols_1537_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1538_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1537_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1538_;
}
case 1:
{
lean_object* v_symbols_1539_; lean_object* v___x_1540_; 
v_symbols_1539_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1540_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1539_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1540_;
}
case 2:
{
lean_object* v_symbols_1541_; lean_object* v___x_1542_; 
v_symbols_1541_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1542_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1541_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1542_;
}
default: 
{
lean_object* v___x_1543_; 
v___x_1543_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1543_;
}
}
}
}
case 8:
{
lean_object* v_presentation_1544_; 
v_presentation_1544_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc_ref(v_presentation_1544_);
lean_dec_ref_known(v_modifier_1451_, 1);
if (lean_obj_tag(v_presentation_1544_) == 0)
{
lean_object* v_val_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; 
v_val_1545_ = lean_ctor_get(v_presentation_1544_, 0);
lean_inc(v_val_1545_);
lean_dec_ref_known(v_presentation_1544_, 1);
v___x_1546_ = 0;
v___x_1547_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1545_, v_data_1452_, v___x_1546_);
lean_dec(v_val_1545_);
return v___x_1547_;
}
else
{
lean_object* v_val_1548_; uint8_t v___x_1549_; 
v_val_1548_ = lean_ctor_get(v_presentation_1544_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v_presentation_1544_, 1);
v___x_1549_ = lean_unbox(v_val_1548_);
lean_dec(v_val_1548_);
switch(v___x_1549_)
{
case 0:
{
lean_object* v_symbols_1550_; lean_object* v___x_1551_; 
v_symbols_1550_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1551_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1550_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1551_;
}
case 1:
{
lean_object* v_symbols_1552_; lean_object* v___x_1553_; 
v_symbols_1552_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1553_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1552_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1553_;
}
case 2:
{
lean_object* v_symbols_1554_; lean_object* v___x_1555_; 
v_symbols_1554_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1555_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1554_, v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1555_;
}
default: 
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1452_);
lean_dec(v_data_1452_);
return v___x_1556_;
}
}
}
}
case 9:
{
lean_object* v_presentation_1557_; lean_object* v___x_1558_; lean_object* v___y_1560_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_presentation_1557_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1557_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1558_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1575_ = lean_int_dec_le(v_data_1452_, v___x_1574_);
if (v___x_1575_ == 0)
{
v___y_1560_ = v_data_1452_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = lean_int_neg(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1577_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1578_ = lean_int_add(v___x_1576_, v___x_1577_);
lean_dec(v___x_1576_);
v___y_1560_ = v___x_1578_;
goto v___jp_1559_;
}
v___jp_1559_:
{
switch(lean_obj_tag(v_presentation_1557_))
{
case 0:
{
uint8_t v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = 0;
v___x_1562_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1558_, v___y_1560_, v___x_1561_);
return v___x_1562_;
}
case 1:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; 
v___x_1563_ = lean_unsigned_to_nat(2u);
v___x_1564_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1565_ = lean_int_emod(v___y_1560_, v___x_1564_);
lean_dec(v___y_1560_);
v___x_1566_ = 0;
v___x_1567_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1563_, v___x_1565_, v___x_1566_);
return v___x_1567_;
}
case 2:
{
lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = lean_unsigned_to_nat(4u);
v___x_1569_ = 0;
v___x_1570_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1568_, v___y_1560_, v___x_1569_);
return v___x_1570_;
}
default: 
{
lean_object* v_num_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; 
v_num_1571_ = lean_ctor_get(v_presentation_1557_, 0);
lean_inc(v_num_1571_);
lean_dec_ref_known(v_presentation_1557_, 1);
v___x_1572_ = 0;
v___x_1573_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1571_, v___y_1560_, v___x_1572_);
lean_dec(v_num_1571_);
return v___x_1573_;
}
}
}
}
case 10:
{
lean_object* v_presentation_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; 
v_presentation_1579_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1579_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1580_ = 0;
v___x_1581_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1579_, v_data_1452_, v___x_1580_);
lean_dec(v_presentation_1579_);
return v___x_1581_;
}
case 11:
{
lean_object* v_presentation_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; 
v_presentation_1582_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1582_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1583_ = 0;
v___x_1584_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1582_, v_data_1452_, v___x_1583_);
lean_dec(v_presentation_1582_);
return v___x_1584_;
}
case 12:
{
uint8_t v_presentation_1585_; 
v_presentation_1585_ = lean_ctor_get_uint8(v_modifier_1451_, 0);
lean_dec_ref_known(v_modifier_1451_, 0);
switch(v_presentation_1585_)
{
case 0:
{
lean_object* v_symbols_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; 
v_symbols_1586_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1587_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1588_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1586_, v___x_1587_);
return v___x_1588_;
}
case 1:
{
lean_object* v_symbols_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; 
v_symbols_1589_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1590_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1591_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1589_, v___x_1590_);
return v___x_1591_;
}
case 2:
{
lean_object* v_symbols_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; 
v_symbols_1592_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1593_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1594_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1592_, v___x_1593_);
return v___x_1594_;
}
default: 
{
lean_object* v_symbols_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; 
v_symbols_1595_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1596_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1597_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1595_, v___x_1596_);
return v___x_1597_;
}
}
}
case 13:
{
lean_object* v_presentation_1598_; 
v_presentation_1598_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc_ref(v_presentation_1598_);
lean_dec_ref_known(v_modifier_1451_, 1);
if (lean_obj_tag(v_presentation_1598_) == 0)
{
lean_object* v_val_1599_; uint8_t v_firstDayOfWeek_1600_; lean_object* v_firstOrd_1601_; uint8_t v___x_1602_; lean_object* v_dayOrd_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; lean_object* v___x_1611_; 
v_val_1599_ = lean_ctor_get(v_presentation_1598_, 0);
lean_inc(v_val_1599_);
lean_dec_ref_known(v_presentation_1598_, 1);
v_firstDayOfWeek_1600_ = lean_ctor_get_uint8(v_dateformat_1450_, sizeof(void*)*2);
v_firstOrd_1601_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1600_);
v___x_1602_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v_dayOrd_1603_ = l_Std_Time_Weekday_toOrdinal(v___x_1602_);
v___x_1604_ = lean_int_sub(v_dayOrd_1603_, v_firstOrd_1601_);
lean_dec(v_firstOrd_1601_);
lean_dec(v_dayOrd_1603_);
v___x_1605_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1606_ = lean_int_add(v___x_1604_, v___x_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_int_emod(v___x_1606_, v___x_1605_);
lean_dec(v___x_1606_);
v___x_1608_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1609_ = lean_int_add(v___x_1607_, v___x_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = 0;
v___x_1611_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1599_, v___x_1609_, v___x_1610_);
lean_dec(v_val_1599_);
return v___x_1611_;
}
else
{
lean_object* v_val_1612_; uint8_t v___x_1613_; 
v_val_1612_ = lean_ctor_get(v_presentation_1598_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v_presentation_1598_, 1);
v___x_1613_ = lean_unbox(v_val_1612_);
lean_dec(v_val_1612_);
switch(v___x_1613_)
{
case 0:
{
lean_object* v_symbols_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; 
v_symbols_1614_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1615_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1616_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1614_, v___x_1615_);
return v___x_1616_;
}
case 1:
{
lean_object* v_symbols_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; 
v_symbols_1617_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1618_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1619_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1617_, v___x_1618_);
return v___x_1619_;
}
case 2:
{
lean_object* v_symbols_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; 
v_symbols_1620_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1621_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1622_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1620_, v___x_1621_);
return v___x_1622_;
}
default: 
{
lean_object* v_symbols_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; 
v_symbols_1623_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1624_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1625_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1623_, v___x_1624_);
return v___x_1625_;
}
}
}
}
case 14:
{
lean_object* v_presentation_1626_; 
v_presentation_1626_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc_ref(v_presentation_1626_);
lean_dec_ref_known(v_modifier_1451_, 1);
if (lean_obj_tag(v_presentation_1626_) == 0)
{
lean_object* v_val_1627_; uint8_t v_firstDayOfWeek_1628_; lean_object* v_firstOrd_1629_; uint8_t v___x_1630_; lean_object* v_dayOrd_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; 
v_val_1627_ = lean_ctor_get(v_presentation_1626_, 0);
lean_inc(v_val_1627_);
lean_dec_ref_known(v_presentation_1626_, 1);
v_firstDayOfWeek_1628_ = lean_ctor_get_uint8(v_dateformat_1450_, sizeof(void*)*2);
v_firstOrd_1629_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1628_);
v___x_1630_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v_dayOrd_1631_ = l_Std_Time_Weekday_toOrdinal(v___x_1630_);
v___x_1632_ = lean_int_sub(v_dayOrd_1631_, v_firstOrd_1629_);
lean_dec(v_firstOrd_1629_);
lean_dec(v_dayOrd_1631_);
v___x_1633_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1634_ = lean_int_add(v___x_1632_, v___x_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_int_emod(v___x_1634_, v___x_1633_);
lean_dec(v___x_1634_);
v___x_1636_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1637_ = lean_int_add(v___x_1635_, v___x_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = 0;
v___x_1639_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1627_, v___x_1637_, v___x_1638_);
lean_dec(v_val_1627_);
return v___x_1639_;
}
else
{
lean_object* v_val_1640_; uint8_t v___x_1641_; 
v_val_1640_ = lean_ctor_get(v_presentation_1626_, 0);
lean_inc(v_val_1640_);
lean_dec_ref_known(v_presentation_1626_, 1);
v___x_1641_ = lean_unbox(v_val_1640_);
lean_dec(v_val_1640_);
switch(v___x_1641_)
{
case 0:
{
lean_object* v_symbols_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; 
v_symbols_1642_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1643_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1644_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1642_, v___x_1643_);
return v___x_1644_;
}
case 1:
{
lean_object* v_symbols_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; 
v_symbols_1645_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1646_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1647_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1645_, v___x_1646_);
return v___x_1647_;
}
case 2:
{
lean_object* v_symbols_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; 
v_symbols_1648_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1649_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1650_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1648_, v___x_1649_);
return v___x_1650_;
}
default: 
{
lean_object* v_symbols_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; 
v_symbols_1651_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1652_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1653_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1651_, v___x_1652_);
return v___x_1653_;
}
}
}
}
case 15:
{
lean_object* v_presentation_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; 
v_presentation_1654_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1654_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1655_ = 0;
v___x_1656_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1654_, v_data_1452_, v___x_1655_);
lean_dec(v_presentation_1654_);
return v___x_1656_;
}
case 16:
{
uint8_t v_presentation_1657_; 
v_presentation_1657_ = lean_ctor_get_uint8(v_modifier_1451_, 0);
lean_dec_ref_known(v_modifier_1451_, 0);
if (v_presentation_1657_ == 2)
{
lean_object* v_symbols_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; 
v_symbols_1658_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1659_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1660_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1658_, v___x_1659_);
return v___x_1660_;
}
else
{
lean_object* v_symbols_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; 
v_symbols_1661_ = lean_ctor_get(v_dateformat_1450_, 1);
v___x_1662_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1663_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1661_, v___x_1662_);
return v___x_1663_;
}
}
case 17:
{
uint8_t v_presentation_1664_; 
v_presentation_1664_ = lean_ctor_get_uint8(v_modifier_1451_, 0);
lean_dec_ref_known(v_modifier_1451_, 0);
switch(v_presentation_1664_)
{
case 1:
{
lean_object* v_symbols_1665_; lean_object* v_dayPeriodLong_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; 
v_symbols_1665_ = lean_ctor_get(v_dateformat_1450_, 1);
v_dayPeriodLong_1666_ = lean_ctor_get(v_symbols_1665_, 20);
v___x_1667_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1668_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodLong_1666_, v___x_1667_);
return v___x_1668_;
}
case 2:
{
lean_object* v_symbols_1669_; lean_object* v_dayPeriodNarrow_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; 
v_symbols_1669_ = lean_ctor_get(v_dateformat_1450_, 1);
v_dayPeriodNarrow_1670_ = lean_ctor_get(v_symbols_1669_, 21);
v___x_1671_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1672_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodNarrow_1670_, v___x_1671_);
return v___x_1672_;
}
default: 
{
lean_object* v_symbols_1673_; lean_object* v_dayPeriodShort_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; 
v_symbols_1673_ = lean_ctor_get(v_dateformat_1450_, 1);
v_dayPeriodShort_1674_ = lean_ctor_get(v_symbols_1673_, 19);
v___x_1675_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1676_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodShort_1674_, v___x_1675_);
return v___x_1676_;
}
}
}
case 18:
{
uint8_t v_presentation_1677_; 
v_presentation_1677_ = lean_ctor_get_uint8(v_modifier_1451_, 0);
lean_dec_ref_known(v_modifier_1451_, 0);
switch(v_presentation_1677_)
{
case 1:
{
lean_object* v_symbols_1678_; lean_object* v_extendedDayPeriodLong_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; 
v_symbols_1678_ = lean_ctor_get(v_dateformat_1450_, 1);
v_extendedDayPeriodLong_1679_ = lean_ctor_get(v_symbols_1678_, 23);
v___x_1680_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1681_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodLong_1679_, v___x_1680_);
return v___x_1681_;
}
case 2:
{
lean_object* v_symbols_1682_; lean_object* v_extendedDayPeriodNarrow_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; 
v_symbols_1682_ = lean_ctor_get(v_dateformat_1450_, 1);
v_extendedDayPeriodNarrow_1683_ = lean_ctor_get(v_symbols_1682_, 24);
v___x_1684_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1685_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodNarrow_1683_, v___x_1684_);
return v___x_1685_;
}
default: 
{
lean_object* v_symbols_1686_; lean_object* v_extendedDayPeriodShort_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; 
v_symbols_1686_ = lean_ctor_get(v_dateformat_1450_, 1);
v_extendedDayPeriodShort_1687_ = lean_ctor_get(v_symbols_1686_, 22);
v___x_1688_ = lean_unbox(v_data_1452_);
lean_dec(v_data_1452_);
v___x_1689_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodShort_1687_, v___x_1688_);
return v___x_1689_;
}
}
}
case 19:
{
lean_object* v_presentation_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; 
v_presentation_1690_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1690_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1691_ = 0;
v___x_1692_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1690_, v_data_1452_, v___x_1691_);
lean_dec(v_presentation_1690_);
return v___x_1692_;
}
case 20:
{
lean_object* v_presentation_1693_; uint8_t v___x_1694_; lean_object* v___x_1695_; 
v_presentation_1693_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1693_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1694_ = 0;
v___x_1695_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1693_, v_data_1452_, v___x_1694_);
lean_dec(v_presentation_1693_);
return v___x_1695_;
}
case 21:
{
lean_object* v_presentation_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; 
v_presentation_1696_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1696_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1697_ = 0;
v___x_1698_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1696_, v_data_1452_, v___x_1697_);
lean_dec(v_presentation_1696_);
return v___x_1698_;
}
case 22:
{
lean_object* v_presentation_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; 
v_presentation_1699_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1699_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1700_ = 0;
v___x_1701_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1699_, v_data_1452_, v___x_1700_);
lean_dec(v_presentation_1699_);
return v___x_1701_;
}
case 23:
{
lean_object* v_presentation_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; 
v_presentation_1702_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1702_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1703_ = 0;
v___x_1704_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1702_, v_data_1452_, v___x_1703_);
lean_dec(v_presentation_1702_);
return v___x_1704_;
}
case 24:
{
lean_object* v_presentation_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; 
v_presentation_1705_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1705_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1706_ = 0;
v___x_1707_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1705_, v_data_1452_, v___x_1706_);
lean_dec(v_presentation_1705_);
return v___x_1707_;
}
case 25:
{
lean_object* v_presentation_1708_; 
v_presentation_1708_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1708_);
lean_dec_ref_known(v_modifier_1451_, 1);
if (lean_obj_tag(v_presentation_1708_) == 0)
{
lean_object* v___x_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = lean_unsigned_to_nat(9u);
v___x_1710_ = 0;
v___x_1711_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1709_, v_data_1452_, v___x_1710_);
return v___x_1711_;
}
else
{
lean_object* v_digits_1712_; lean_object* v___x_1713_; uint32_t v___x_1714_; lean_object* v___x_1715_; lean_object* v_s_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_digits_1712_ = lean_ctor_get(v_presentation_1708_, 0);
lean_inc(v_digits_1712_);
lean_dec_ref_known(v_presentation_1708_, 1);
v___x_1713_ = lean_unsigned_to_nat(9u);
v___x_1714_ = 48;
v___x_1715_ = l_Int_repr(v_data_1452_);
lean_dec(v_data_1452_);
v_s_1716_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1713_, v___x_1714_, v___x_1715_);
lean_dec_ref(v___x_1715_);
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = lean_string_utf8_byte_size(v_s_1716_);
lean_inc_ref(v_s_1716_);
v___x_1719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1719_, 0, v_s_1716_);
lean_ctor_set(v___x_1719_, 1, v___x_1717_);
lean_ctor_set(v___x_1719_, 2, v___x_1718_);
v___x_1720_ = l_String_Slice_Pos_nextn(v___x_1719_, v___x_1717_, v_digits_1712_);
lean_dec_ref_known(v___x_1719_, 3);
v___x_1721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1721_, 0, v_s_1716_);
lean_ctor_set(v___x_1721_, 1, v___x_1717_);
lean_ctor_set(v___x_1721_, 2, v___x_1720_);
v___x_1722_ = l_String_Slice_toString(v___x_1721_);
lean_dec_ref_known(v___x_1721_, 3);
return v___x_1722_;
}
}
case 26:
{
lean_object* v_presentation_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; 
v_presentation_1723_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1723_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1724_ = 0;
v___x_1725_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1723_, v_data_1452_, v___x_1724_);
lean_dec(v_presentation_1723_);
return v___x_1725_;
}
case 27:
{
lean_object* v_presentation_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; 
v_presentation_1726_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1726_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1727_ = 0;
v___x_1728_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1726_, v_data_1452_, v___x_1727_);
lean_dec(v_presentation_1726_);
return v___x_1728_;
}
case 28:
{
lean_object* v_presentation_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; 
v_presentation_1729_ = lean_ctor_get(v_modifier_1451_, 0);
lean_inc(v_presentation_1729_);
lean_dec_ref_known(v_modifier_1451_, 1);
v___x_1730_ = 0;
v___x_1731_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1729_, v_data_1452_, v___x_1730_);
lean_dec(v_presentation_1729_);
return v___x_1731_;
}
case 29:
{
uint8_t v_presentation_1732_; 
v_presentation_1732_ = lean_ctor_get_uint8(v_modifier_1451_, 0);
lean_dec_ref_known(v_modifier_1451_, 0);
if (v_presentation_1732_ == 0)
{
lean_object* v___x_1733_; 
lean_dec(v_data_1452_);
v___x_1733_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1733_;
}
else
{
return v_data_1452_;
}
}
case 32:
{
uint8_t v_presentation_1734_; 
v_presentation_1734_ = lean_ctor_get_uint8(v_modifier_1451_, 0);
lean_dec_ref_known(v_modifier_1451_, 0);
if (v_presentation_1734_ == 0)
{
lean_object* v_fst_1736_; lean_object* v_snd_1737_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1761_ = lean_int_dec_eq(v_data_1452_, v___x_1760_);
if (v___x_1761_ == 0)
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_int_dec_le(v___x_1760_, v_data_1452_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1764_ = lean_int_neg(v_data_1452_);
lean_dec(v_data_1452_);
v_fst_1736_ = v___x_1763_;
v_snd_1737_ = v___x_1764_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1765_; 
v___x_1765_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1736_ = v___x_1765_;
v_snd_1737_ = v_data_1452_;
goto v___jp_1735_;
}
}
else
{
lean_object* v___x_1766_; 
lean_dec(v_data_1452_);
v___x_1766_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1766_;
}
v___jp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v_t_1740_; lean_object* v_hour_1741_; lean_object* v_minute_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1738_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1739_ = lean_int_mul(v_snd_1737_, v___x_1738_);
lean_dec(v_snd_1737_);
v_t_1740_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1739_);
lean_dec(v___x_1739_);
v_hour_1741_ = lean_ctor_get(v_t_1740_, 0);
lean_inc(v_hour_1741_);
v_minute_1742_ = lean_ctor_get(v_t_1740_, 1);
lean_inc(v_minute_1742_);
lean_dec_ref(v_t_1740_);
v___x_1743_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1744_ = lean_int_dec_eq(v_minute_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; uint32_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1745_ = lean_unsigned_to_nat(2u);
v___x_1746_ = 48;
v___x_1747_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1748_ = lean_string_append(v___x_1747_, v_fst_1736_);
v___x_1749_ = l_Int_repr(v_hour_1741_);
lean_dec(v_hour_1741_);
v___x_1750_ = lean_string_append(v___x_1748_, v___x_1749_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___x_1752_ = lean_string_append(v___x_1750_, v___x_1751_);
v___x_1753_ = l_Int_repr(v_minute_1742_);
lean_dec(v_minute_1742_);
v___x_1754_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1745_, v___x_1746_, v___x_1753_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = lean_string_append(v___x_1752_, v___x_1754_);
lean_dec_ref(v___x_1754_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec(v_minute_1742_);
v___x_1756_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1757_ = lean_string_append(v___x_1756_, v_fst_1736_);
v___x_1758_ = l_Int_repr(v_hour_1741_);
lean_dec(v_hour_1741_);
v___x_1759_ = lean_string_append(v___x_1757_, v___x_1758_);
lean_dec_ref(v___x_1758_);
return v___x_1759_;
}
}
}
else
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1768_ = lean_int_dec_eq(v_data_1452_, v___x_1767_);
if (v___x_1768_ == 0)
{
uint8_t v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1769_ = 1;
v___x_1770_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1771_ = 0;
v___x_1772_ = 1;
v___x_1773_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1771_, v___x_1772_, v___x_1769_, v___x_1769_);
v___x_1774_ = lean_string_append(v___x_1770_, v___x_1773_);
lean_dec_ref(v___x_1773_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; 
lean_dec(v_data_1452_);
v___x_1775_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1775_;
}
}
}
case 33:
{
uint8_t v_presentation_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_presentation_1776_ = lean_ctor_get_uint8(v_modifier_1451_, 0);
lean_dec_ref_known(v_modifier_1451_, 0);
v___x_1777_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1778_ = lean_int_dec_eq(v_data_1452_, v___x_1777_);
if (v___x_1778_ == 0)
{
uint8_t v___x_1779_; 
v___x_1779_ = 1;
switch(v_presentation_1776_)
{
case 0:
{
uint8_t v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = 2;
v___x_1781_ = 1;
v___x_1782_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1780_, v___x_1781_, v___x_1778_, v___x_1779_);
return v___x_1782_;
}
case 1:
{
uint8_t v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = 0;
v___x_1784_ = 1;
v___x_1785_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1783_, v___x_1784_, v___x_1778_, v___x_1779_);
return v___x_1785_;
}
case 2:
{
uint8_t v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = 0;
v___x_1787_ = 1;
v___x_1788_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1786_, v___x_1787_, v___x_1779_, v___x_1779_);
return v___x_1788_;
}
case 3:
{
uint8_t v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = 0;
v___x_1790_ = 2;
v___x_1791_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1789_, v___x_1790_, v___x_1778_, v___x_1779_);
return v___x_1791_;
}
default: 
{
uint8_t v___x_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = 0;
v___x_1793_ = 2;
v___x_1794_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1792_, v___x_1793_, v___x_1779_, v___x_1779_);
return v___x_1794_;
}
}
}
else
{
lean_object* v___x_1795_; 
lean_dec(v_data_1452_);
v___x_1795_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1795_;
}
}
case 34:
{
uint8_t v_presentation_1796_; 
v_presentation_1796_ = lean_ctor_get_uint8(v_modifier_1451_, 0);
lean_dec_ref_known(v_modifier_1451_, 0);
switch(v_presentation_1796_)
{
case 0:
{
uint8_t v___x_1797_; uint8_t v___x_1798_; uint8_t v___x_1799_; uint8_t v___x_1800_; lean_object* v___x_1801_; 
v___x_1797_ = 2;
v___x_1798_ = 1;
v___x_1799_ = 0;
v___x_1800_ = 1;
v___x_1801_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1797_, v___x_1798_, v___x_1799_, v___x_1800_);
return v___x_1801_;
}
case 1:
{
uint8_t v___x_1802_; uint8_t v___x_1803_; uint8_t v___x_1804_; uint8_t v___x_1805_; lean_object* v___x_1806_; 
v___x_1802_ = 0;
v___x_1803_ = 1;
v___x_1804_ = 0;
v___x_1805_ = 1;
v___x_1806_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1802_, v___x_1803_, v___x_1804_, v___x_1805_);
return v___x_1806_;
}
case 2:
{
uint8_t v___x_1807_; uint8_t v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = 0;
v___x_1808_ = 1;
v___x_1809_ = 1;
v___x_1810_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1807_, v___x_1808_, v___x_1809_, v___x_1809_);
return v___x_1810_;
}
case 3:
{
uint8_t v___x_1811_; uint8_t v___x_1812_; uint8_t v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; 
v___x_1811_ = 0;
v___x_1812_ = 2;
v___x_1813_ = 0;
v___x_1814_ = 1;
v___x_1815_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1811_, v___x_1812_, v___x_1813_, v___x_1814_);
return v___x_1815_;
}
default: 
{
uint8_t v___x_1816_; uint8_t v___x_1817_; uint8_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1816_ = 0;
v___x_1817_ = 2;
v___x_1818_ = 1;
v___x_1819_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1816_, v___x_1817_, v___x_1818_, v___x_1818_);
return v___x_1819_;
}
}
}
case 35:
{
uint8_t v_presentation_1820_; 
v_presentation_1820_ = lean_ctor_get_uint8(v_modifier_1451_, 0);
lean_dec_ref_known(v_modifier_1451_, 0);
switch(v_presentation_1820_)
{
case 0:
{
uint8_t v___x_1821_; uint8_t v___x_1822_; uint8_t v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1821_ = 0;
v___x_1822_ = 2;
v___x_1823_ = 0;
v___x_1824_ = 1;
v___x_1825_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1821_, v___x_1822_, v___x_1823_, v___x_1824_);
return v___x_1825_;
}
case 1:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1827_ = lean_int_dec_eq(v_data_1452_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; uint8_t v___x_1829_; uint8_t v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1828_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1829_ = 0;
v___x_1830_ = 1;
v___x_1831_ = 1;
v___x_1832_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1829_, v___x_1830_, v___x_1831_, v___x_1831_);
v___x_1833_ = lean_string_append(v___x_1828_, v___x_1832_);
lean_dec_ref(v___x_1832_);
return v___x_1833_;
}
else
{
lean_object* v___x_1834_; 
lean_dec(v_data_1452_);
v___x_1834_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1834_;
}
}
default: 
{
lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1835_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1836_ = lean_int_dec_eq(v_data_1452_, v___x_1835_);
if (v___x_1836_ == 0)
{
uint8_t v___x_1837_; uint8_t v___x_1838_; uint8_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1837_ = 1;
v___x_1838_ = 0;
v___x_1839_ = 2;
v___x_1840_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1452_, v___x_1838_, v___x_1839_, v___x_1837_, v___x_1837_);
return v___x_1840_;
}
else
{
lean_object* v___x_1841_; 
lean_dec(v_data_1452_);
v___x_1841_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1841_;
}
}
}
}
default: 
{
lean_dec_ref(v_modifier_1451_);
return v_data_1452_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___boxed(lean_object* v_dateformat_1842_, lean_object* v_modifier_1843_, lean_object* v_data_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_1842_, v_modifier_1843_, v_data_1844_);
lean_dec_ref(v_dateformat_1842_);
return v_res_1845_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_unsigned_to_nat(4u);
v___x_1847_ = lean_nat_to_int(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_unsigned_to_nat(400u);
v___x_1849_ = lean_nat_to_int(v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(lean_object* v_modifier_1850_, lean_object* v_dateformat_1851_, lean_object* v_date_1852_){
_start:
{
uint8_t v_firstDayOfWeek_1853_; lean_object* v_minimalDaysInFirstWeek_1854_; lean_object* v_date_1855_; lean_object* v_timezone_1856_; 
v_firstDayOfWeek_1853_ = lean_ctor_get_uint8(v_dateformat_1851_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1854_ = lean_ctor_get(v_dateformat_1851_, 0);
v_date_1855_ = lean_ctor_get(v_date_1852_, 0);
v_timezone_1856_ = lean_ctor_get(v_date_1852_, 3);
switch(lean_obj_tag(v_modifier_1850_))
{
case 0:
{
lean_object* v___x_1874_; lean_object* v_date_1875_; lean_object* v_year_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1874_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc_ref(v_date_1875_);
lean_dec(v___x_1874_);
v_year_1876_ = lean_ctor_get(v_date_1875_, 0);
lean_inc(v_year_1876_);
lean_dec_ref(v_date_1875_);
v___x_1877_ = l_Std_Time_Year_Offset_era(v_year_1876_);
lean_dec(v_year_1876_);
v___x_1878_ = lean_box(v___x_1877_);
return v___x_1878_;
}
case 1:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
goto v___jp_1857_;
}
case 2:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
goto v___jp_1857_;
}
case 3:
{
lean_object* v___x_1879_; lean_object* v_date_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1908_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1879_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; 
v_unused_1909_ = lean_ctor_get(v___x_1879_, 1);
lean_dec(v_unused_1909_);
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1908_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_date_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1908_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_year_1884_; lean_object* v_month_1885_; lean_object* v_day_1886_; uint8_t v___y_1888_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; uint8_t v___y_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v_year_1884_ = lean_ctor_get(v_date_1880_, 0);
lean_inc(v_year_1884_);
v_month_1885_ = lean_ctor_get(v_date_1880_, 1);
lean_inc(v_month_1885_);
v_day_1886_ = lean_ctor_get(v_date_1880_, 2);
lean_inc(v_day_1886_);
lean_dec_ref(v_date_1880_);
v___x_1895_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1896_ = lean_int_mod(v_year_1884_, v___x_1895_);
v___x_1897_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1898_ = lean_int_dec_eq(v___x_1896_, v___x_1897_);
lean_dec(v___x_1896_);
v___x_1901_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1902_ = lean_int_mod(v_year_1884_, v___x_1901_);
v___x_1903_ = lean_int_dec_eq(v___x_1902_, v___x_1897_);
lean_dec(v___x_1902_);
if (v___x_1903_ == 0)
{
uint8_t v___x_1904_; 
lean_dec(v_year_1884_);
v___x_1904_ = 1;
v___y_1900_ = v___x_1904_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1905_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1906_ = lean_int_mod(v_year_1884_, v___x_1905_);
lean_dec(v_year_1884_);
v___x_1907_ = lean_int_dec_eq(v___x_1906_, v___x_1897_);
lean_dec(v___x_1906_);
v___y_1900_ = v___x_1907_;
goto v___jp_1899_;
}
v___jp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 1, v_day_1886_);
lean_ctor_set(v___x_1882_, 0, v_month_1885_);
v___x_1890_ = v___x_1882_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_month_1885_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_day_1886_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = l_Std_Time_ValidDate_dayOfYear(v___y_1888_, v___x_1890_);
lean_dec_ref(v___x_1890_);
v___x_1892_ = lean_box(v___y_1888_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1891_);
return v___x_1893_;
}
}
v___jp_1899_:
{
if (v___x_1898_ == 0)
{
v___y_1888_ = v___x_1898_;
goto v___jp_1887_;
}
else
{
v___y_1888_ = v___y_1900_;
goto v___jp_1887_;
}
}
}
}
case 4:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
goto v___jp_1861_;
}
case 5:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
goto v___jp_1861_;
}
case 6:
{
lean_object* v___x_1910_; lean_object* v_date_1911_; lean_object* v_day_1912_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1910_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc_ref(v_date_1911_);
lean_dec(v___x_1910_);
v_day_1912_ = lean_ctor_get(v_date_1911_, 2);
lean_inc(v_day_1912_);
lean_dec_ref(v_date_1911_);
return v_day_1912_;
}
case 7:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
goto v___jp_1865_;
}
case 8:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
goto v___jp_1865_;
}
case 9:
{
lean_object* v___x_1913_; lean_object* v_date_1914_; lean_object* v___x_1915_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1913_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc_ref(v_date_1914_);
lean_dec(v___x_1913_);
v___x_1915_ = l_Std_Time_PlainDate_weekYear(v_date_1914_, v_firstDayOfWeek_1853_, v_minimalDaysInFirstWeek_1854_);
return v___x_1915_;
}
case 10:
{
lean_object* v___x_1916_; lean_object* v_date_1917_; lean_object* v___x_1918_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1916_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_date_1917_);
lean_dec(v___x_1916_);
v___x_1918_ = l_Std_Time_PlainDate_weekOfYear(v_date_1917_, v_firstDayOfWeek_1853_, v_minimalDaysInFirstWeek_1854_);
return v___x_1918_;
}
case 11:
{
lean_object* v___x_1919_; lean_object* v_date_1920_; lean_object* v___x_1921_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1919_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc_ref(v_date_1920_);
lean_dec(v___x_1919_);
v___x_1921_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1920_, v_firstDayOfWeek_1853_);
return v___x_1921_;
}
case 12:
{
lean_object* v___x_1922_; lean_object* v_date_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1922_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc_ref(v_date_1923_);
lean_dec(v___x_1922_);
v___x_1924_ = l_Std_Time_PlainDate_weekday(v_date_1923_);
v___x_1925_ = lean_box(v___x_1924_);
return v___x_1925_;
}
case 13:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
goto v___jp_1869_;
}
case 14:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
goto v___jp_1869_;
}
case 15:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_1852_);
lean_dec_ref(v_date_1852_);
return v___x_1926_;
}
case 16:
{
lean_object* v___x_1927_; lean_object* v_time_1928_; lean_object* v_hour_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1927_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1928_ = lean_ctor_get(v___x_1927_, 1);
lean_inc_ref(v_time_1928_);
lean_dec(v___x_1927_);
v_hour_1929_ = lean_ctor_get(v_time_1928_, 0);
lean_inc(v_hour_1929_);
lean_dec_ref(v_time_1928_);
v___x_1930_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1929_);
lean_dec(v_hour_1929_);
v___x_1931_ = lean_box(v___x_1930_);
return v___x_1931_;
}
case 17:
{
lean_object* v___x_1932_; lean_object* v_time_1933_; lean_object* v_hour_1934_; lean_object* v_minute_1935_; lean_object* v_second_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1932_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1933_ = lean_ctor_get(v___x_1932_, 1);
lean_inc_ref(v_time_1933_);
lean_dec(v___x_1932_);
v_hour_1934_ = lean_ctor_get(v_time_1933_, 0);
lean_inc(v_hour_1934_);
v_minute_1935_ = lean_ctor_get(v_time_1933_, 1);
lean_inc(v_minute_1935_);
v_second_1936_ = lean_ctor_get(v_time_1933_, 2);
lean_inc(v_second_1936_);
lean_dec_ref(v_time_1933_);
v___x_1937_ = l_Std_Time_classifyDayPeriod(v_hour_1934_, v_minute_1935_, v_second_1936_);
lean_dec(v_second_1936_);
lean_dec(v_minute_1935_);
lean_dec(v_hour_1934_);
v___x_1938_ = lean_box(v___x_1937_);
return v___x_1938_;
}
case 18:
{
lean_object* v___x_1939_; lean_object* v_time_1940_; lean_object* v_hour_1941_; lean_object* v_minute_1942_; lean_object* v_second_1943_; uint8_t v___x_1944_; lean_object* v___x_1945_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1939_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1940_ = lean_ctor_get(v___x_1939_, 1);
lean_inc_ref(v_time_1940_);
lean_dec(v___x_1939_);
v_hour_1941_ = lean_ctor_get(v_time_1940_, 0);
lean_inc(v_hour_1941_);
v_minute_1942_ = lean_ctor_get(v_time_1940_, 1);
lean_inc(v_minute_1942_);
v_second_1943_ = lean_ctor_get(v_time_1940_, 2);
lean_inc(v_second_1943_);
lean_dec_ref(v_time_1940_);
v___x_1944_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1941_, v_minute_1942_, v_second_1943_);
lean_dec(v_second_1943_);
lean_dec(v_minute_1942_);
lean_dec(v_hour_1941_);
v___x_1945_ = lean_box(v___x_1944_);
return v___x_1945_;
}
case 19:
{
lean_object* v___x_1946_; lean_object* v_time_1947_; lean_object* v_hour_1948_; lean_object* v___x_1949_; lean_object* v_fst_1950_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1946_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1947_ = lean_ctor_get(v___x_1946_, 1);
lean_inc_ref(v_time_1947_);
lean_dec(v___x_1946_);
v_hour_1948_ = lean_ctor_get(v_time_1947_, 0);
lean_inc(v_hour_1948_);
lean_dec_ref(v_time_1947_);
v___x_1949_ = l_Std_Time_HourMarker_toRelative(v_hour_1948_);
v_fst_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_fst_1950_);
lean_dec_ref(v___x_1949_);
return v_fst_1950_;
}
case 20:
{
lean_object* v___x_1951_; lean_object* v_time_1952_; lean_object* v_hour_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1951_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1952_ = lean_ctor_get(v___x_1951_, 1);
lean_inc_ref(v_time_1952_);
lean_dec(v___x_1951_);
v_hour_1953_ = lean_ctor_get(v_time_1952_, 0);
lean_inc(v_hour_1953_);
lean_dec_ref(v_time_1952_);
v___x_1954_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1955_ = lean_int_emod(v_hour_1953_, v___x_1954_);
lean_dec(v_hour_1953_);
return v___x_1955_;
}
case 21:
{
lean_object* v___x_1956_; lean_object* v_time_1957_; lean_object* v_hour_1958_; lean_object* v___x_1959_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1956_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1957_ = lean_ctor_get(v___x_1956_, 1);
lean_inc_ref(v_time_1957_);
lean_dec(v___x_1956_);
v_hour_1958_ = lean_ctor_get(v_time_1957_, 0);
lean_inc(v_hour_1958_);
lean_dec_ref(v_time_1957_);
v___x_1959_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1958_);
lean_dec(v_hour_1958_);
return v___x_1959_;
}
case 22:
{
lean_object* v___x_1960_; lean_object* v_time_1961_; lean_object* v_hour_1962_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1960_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1961_ = lean_ctor_get(v___x_1960_, 1);
lean_inc_ref(v_time_1961_);
lean_dec(v___x_1960_);
v_hour_1962_ = lean_ctor_get(v_time_1961_, 0);
lean_inc(v_hour_1962_);
lean_dec_ref(v_time_1961_);
return v_hour_1962_;
}
case 23:
{
lean_object* v___x_1963_; lean_object* v_time_1964_; lean_object* v_minute_1965_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1963_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1964_ = lean_ctor_get(v___x_1963_, 1);
lean_inc_ref(v_time_1964_);
lean_dec(v___x_1963_);
v_minute_1965_ = lean_ctor_get(v_time_1964_, 1);
lean_inc(v_minute_1965_);
lean_dec_ref(v_time_1964_);
return v_minute_1965_;
}
case 24:
{
lean_object* v___x_1966_; lean_object* v_time_1967_; lean_object* v_second_1968_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1966_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1967_ = lean_ctor_get(v___x_1966_, 1);
lean_inc_ref(v_time_1967_);
lean_dec(v___x_1966_);
v_second_1968_ = lean_ctor_get(v_time_1967_, 2);
lean_inc(v_second_1968_);
lean_dec_ref(v_time_1967_);
return v_second_1968_;
}
case 25:
{
lean_object* v___x_1969_; lean_object* v_time_1970_; lean_object* v_nanosecond_1971_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1969_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1970_ = lean_ctor_get(v___x_1969_, 1);
lean_inc_ref(v_time_1970_);
lean_dec(v___x_1969_);
v_nanosecond_1971_ = lean_ctor_get(v_time_1970_, 3);
lean_inc(v_nanosecond_1971_);
lean_dec_ref(v_time_1970_);
return v_nanosecond_1971_;
}
case 26:
{
lean_object* v___x_1972_; lean_object* v_time_1973_; lean_object* v___x_1974_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1972_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1973_ = lean_ctor_get(v___x_1972_, 1);
lean_inc_ref(v_time_1973_);
lean_dec(v___x_1972_);
v___x_1974_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1973_);
lean_dec_ref(v_time_1973_);
return v___x_1974_;
}
case 27:
{
lean_object* v___x_1975_; lean_object* v_time_1976_; lean_object* v_nanosecond_1977_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1975_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1976_ = lean_ctor_get(v___x_1975_, 1);
lean_inc_ref(v_time_1976_);
lean_dec(v___x_1975_);
v_nanosecond_1977_ = lean_ctor_get(v_time_1976_, 3);
lean_inc(v_nanosecond_1977_);
lean_dec_ref(v_time_1976_);
return v_nanosecond_1977_;
}
case 28:
{
lean_object* v___x_1978_; lean_object* v_time_1979_; lean_object* v___x_1980_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1852_);
v___x_1978_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1979_ = lean_ctor_get(v___x_1978_, 1);
lean_inc_ref(v_time_1979_);
lean_dec(v___x_1978_);
v___x_1980_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1979_);
lean_dec_ref(v_time_1979_);
return v___x_1980_;
}
case 29:
{
uint8_t v_presentation_1981_; 
lean_inc_ref(v_timezone_1856_);
lean_dec_ref(v_date_1852_);
v_presentation_1981_ = lean_ctor_get_uint8(v_modifier_1850_, 0);
if (v_presentation_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_dec_ref(v_timezone_1856_);
v___x_1982_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1982_;
}
else
{
lean_object* v_offset_1983_; lean_object* v_name_1984_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_offset_1983_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_1983_);
v_name_1984_ = lean_ctor_get(v_timezone_1856_, 1);
lean_inc_ref(v_name_1984_);
lean_dec_ref(v_timezone_1856_);
v___x_1999_ = lean_string_utf8_byte_size(v_name_1984_);
v___x_2000_ = lean_unsigned_to_nat(1u);
v___x_2001_ = lean_nat_dec_le(v___x_2000_, v___x_1999_);
if (v___x_2001_ == 0)
{
goto v___jp_1992_;
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2002_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2003_ = lean_unsigned_to_nat(0u);
v___x_2004_ = lean_string_memcmp(v_name_1984_, v___x_2002_, v___x_2003_, v___x_2003_, v___x_2000_);
if (v___x_2004_ == 0)
{
goto v___jp_1992_;
}
else
{
lean_dec_ref(v_name_1984_);
goto v___jp_1985_;
}
}
v___jp_1985_:
{
uint8_t v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1986_ = 1;
v___x_1987_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1988_ = 0;
v___x_1989_ = 1;
v___x_1990_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1983_, v___x_1988_, v___x_1989_, v___x_1986_, v___x_1986_);
v___x_1991_ = lean_string_append(v___x_1987_, v___x_1990_);
lean_dec_ref(v___x_1990_);
return v___x_1991_;
}
v___jp_1992_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1993_ = lean_string_utf8_byte_size(v_name_1984_);
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = lean_nat_dec_le(v___x_1994_, v___x_1993_);
if (v___x_1995_ == 0)
{
lean_dec(v_offset_1983_);
return v_name_1984_;
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1997_ = lean_unsigned_to_nat(0u);
v___x_1998_ = lean_string_memcmp(v_name_1984_, v___x_1996_, v___x_1997_, v___x_1997_, v___x_1994_);
if (v___x_1998_ == 0)
{
lean_dec(v_offset_1983_);
return v_name_1984_;
}
else
{
lean_dec_ref(v_name_1984_);
goto v___jp_1985_;
}
}
}
}
}
case 30:
{
uint8_t v_presentation_2005_; 
lean_inc_ref(v_timezone_1856_);
lean_dec_ref(v_date_1852_);
v_presentation_2005_ = lean_ctor_get_uint8(v_modifier_1850_, 0);
if (v_presentation_2005_ == 0)
{
lean_object* v_offset_2006_; lean_object* v_abbreviation_2007_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v_offset_2006_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_2006_);
v_abbreviation_2007_ = lean_ctor_get(v_timezone_1856_, 2);
lean_inc_ref(v_abbreviation_2007_);
lean_dec_ref(v_timezone_1856_);
v___x_2022_ = lean_string_utf8_byte_size(v_abbreviation_2007_);
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = lean_nat_dec_le(v___x_2023_, v___x_2022_);
if (v___x_2024_ == 0)
{
goto v___jp_2015_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2025_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2026_ = lean_unsigned_to_nat(0u);
v___x_2027_ = lean_string_memcmp(v_abbreviation_2007_, v___x_2025_, v___x_2026_, v___x_2026_, v___x_2023_);
if (v___x_2027_ == 0)
{
goto v___jp_2015_;
}
else
{
lean_dec_ref(v_abbreviation_2007_);
goto v___jp_2008_;
}
}
v___jp_2008_:
{
uint8_t v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2009_ = 1;
v___x_2010_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2011_ = 0;
v___x_2012_ = 1;
v___x_2013_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2006_, v___x_2011_, v___x_2012_, v___x_2009_, v___x_2009_);
v___x_2014_ = lean_string_append(v___x_2010_, v___x_2013_);
lean_dec_ref(v___x_2013_);
return v___x_2014_;
}
v___jp_2015_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2016_ = lean_string_utf8_byte_size(v_abbreviation_2007_);
v___x_2017_ = lean_unsigned_to_nat(1u);
v___x_2018_ = lean_nat_dec_le(v___x_2017_, v___x_2016_);
if (v___x_2018_ == 0)
{
lean_dec(v_offset_2006_);
return v_abbreviation_2007_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2019_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = lean_string_memcmp(v_abbreviation_2007_, v___x_2019_, v___x_2020_, v___x_2020_, v___x_2017_);
if (v___x_2021_ == 0)
{
lean_dec(v_offset_2006_);
return v_abbreviation_2007_;
}
else
{
lean_dec_ref(v_abbreviation_2007_);
goto v___jp_2008_;
}
}
}
}
else
{
lean_object* v_offset_2028_; lean_object* v_name_2029_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v_offset_2028_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_2028_);
v_name_2029_ = lean_ctor_get(v_timezone_1856_, 1);
lean_inc_ref(v_name_2029_);
lean_dec_ref(v_timezone_1856_);
v___x_2044_ = lean_string_utf8_byte_size(v_name_2029_);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_dec_le(v___x_2045_, v___x_2044_);
if (v___x_2046_ == 0)
{
goto v___jp_2037_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2047_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = lean_string_memcmp(v_name_2029_, v___x_2047_, v___x_2048_, v___x_2048_, v___x_2045_);
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
lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2038_ = lean_string_utf8_byte_size(v_name_2029_);
v___x_2039_ = lean_unsigned_to_nat(1u);
v___x_2040_ = lean_nat_dec_le(v___x_2039_, v___x_2038_);
if (v___x_2040_ == 0)
{
lean_dec(v_offset_2028_);
return v_name_2029_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2041_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = lean_string_memcmp(v_name_2029_, v___x_2041_, v___x_2042_, v___x_2042_, v___x_2039_);
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
case 31:
{
uint8_t v_presentation_2050_; 
lean_inc_ref(v_timezone_1856_);
lean_dec_ref(v_date_1852_);
v_presentation_2050_ = lean_ctor_get_uint8(v_modifier_1850_, 0);
if (v_presentation_2050_ == 0)
{
lean_object* v_offset_2051_; lean_object* v_abbreviation_2052_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_offset_2051_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_2051_);
v_abbreviation_2052_ = lean_ctor_get(v_timezone_1856_, 2);
lean_inc_ref(v_abbreviation_2052_);
lean_dec_ref(v_timezone_1856_);
v___x_2067_ = lean_string_utf8_byte_size(v_abbreviation_2052_);
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_dec_le(v___x_2068_, v___x_2067_);
if (v___x_2069_ == 0)
{
goto v___jp_2060_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2070_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_string_memcmp(v_abbreviation_2052_, v___x_2070_, v___x_2071_, v___x_2071_, v___x_2068_);
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
lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2061_ = lean_string_utf8_byte_size(v_abbreviation_2052_);
v___x_2062_ = lean_unsigned_to_nat(1u);
v___x_2063_ = lean_nat_dec_le(v___x_2062_, v___x_2061_);
if (v___x_2063_ == 0)
{
lean_dec(v_offset_2051_);
return v_abbreviation_2052_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2064_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = lean_string_memcmp(v_abbreviation_2052_, v___x_2064_, v___x_2065_, v___x_2065_, v___x_2062_);
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
lean_object* v_offset_2073_; lean_object* v_name_2074_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v_offset_2073_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_2073_);
v_name_2074_ = lean_ctor_get(v_timezone_1856_, 1);
lean_inc_ref(v_name_2074_);
lean_dec_ref(v_timezone_1856_);
v___x_2089_ = lean_string_utf8_byte_size(v_name_2074_);
v___x_2090_ = lean_unsigned_to_nat(1u);
v___x_2091_ = lean_nat_dec_le(v___x_2090_, v___x_2089_);
if (v___x_2091_ == 0)
{
goto v___jp_2082_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2092_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = lean_string_memcmp(v_name_2074_, v___x_2092_, v___x_2093_, v___x_2093_, v___x_2090_);
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
lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2083_ = lean_string_utf8_byte_size(v_name_2074_);
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_dec_le(v___x_2084_, v___x_2083_);
if (v___x_2085_ == 0)
{
lean_dec(v_offset_2073_);
return v_name_2074_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2086_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_string_memcmp(v_name_2074_, v___x_2086_, v___x_2087_, v___x_2087_, v___x_2084_);
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
default: 
{
lean_object* v_offset_2095_; 
lean_inc_ref(v_timezone_1856_);
lean_dec_ref(v_date_1852_);
v_offset_2095_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_2095_);
lean_dec_ref(v_timezone_1856_);
return v_offset_2095_;
}
}
v___jp_1857_:
{
lean_object* v___x_1858_; lean_object* v_date_1859_; lean_object* v_year_1860_; 
v___x_1858_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc_ref(v_date_1859_);
lean_dec(v___x_1858_);
v_year_1860_ = lean_ctor_get(v_date_1859_, 0);
lean_inc(v_year_1860_);
lean_dec_ref(v_date_1859_);
return v_year_1860_;
}
v___jp_1861_:
{
lean_object* v___x_1862_; lean_object* v_date_1863_; lean_object* v_month_1864_; 
v___x_1862_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc_ref(v_date_1863_);
lean_dec(v___x_1862_);
v_month_1864_ = lean_ctor_get(v_date_1863_, 1);
lean_inc(v_month_1864_);
lean_dec_ref(v_date_1863_);
return v_month_1864_;
}
v___jp_1865_:
{
lean_object* v___x_1866_; lean_object* v_date_1867_; lean_object* v___x_1868_; 
v___x_1866_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc_ref(v_date_1867_);
lean_dec(v___x_1866_);
v___x_1868_ = l_Std_Time_PlainDate_quarter(v_date_1867_);
lean_dec_ref(v_date_1867_);
return v___x_1868_;
}
v___jp_1869_:
{
lean_object* v___x_1870_; lean_object* v_date_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1870_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc_ref(v_date_1871_);
lean_dec(v___x_1870_);
v___x_1872_ = l_Std_Time_PlainDate_weekday(v_date_1871_);
v___x_1873_ = lean_box(v___x_1872_);
return v___x_1873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___boxed(lean_object* v_modifier_2096_, lean_object* v_dateformat_2097_, lean_object* v_date_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_2096_, v_dateformat_2097_, v_date_2098_);
lean_dec_ref(v_dateformat_2097_);
lean_dec_ref(v_modifier_2096_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0(lean_object* v___x_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
v___x_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___y_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0(lean_object* v___x_2104_, lean_object* v_b_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_fst_2107_; lean_object* v_snd_2108_; lean_object* v___x_2109_; 
v_fst_2107_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_fst_2107_);
v_snd_2108_ = lean_ctor_get(v___x_2104_, 1);
lean_inc(v_snd_2108_);
lean_dec_ref(v___x_2104_);
lean_inc_ref(v___y_2106_);
v___x_2109_ = lean_apply_1(v_b_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec_ref(v___y_2106_);
return v___x_2109_;
}
else
{
lean_object* v_pos_2110_; lean_object* v_snd_2111_; lean_object* v_snd_2112_; uint8_t v_decide_2113_; 
v_pos_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_pos_2110_);
v_snd_2111_ = lean_ctor_get(v___y_2106_, 1);
lean_inc(v_snd_2111_);
lean_dec_ref(v___y_2106_);
v_snd_2112_ = lean_ctor_get(v_pos_2110_, 1);
v_decide_2113_ = lean_nat_dec_eq(v_snd_2111_, v_snd_2112_);
lean_dec(v_snd_2111_);
if (v_decide_2113_ == 0)
{
lean_dec(v_pos_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
return v___x_2109_;
}
else
{
lean_object* v___x_2114_; 
lean_dec_ref_known(v___x_2109_, 2);
v___x_2114_ = l_Std_Internal_Parsec_String_pstring(v_fst_2107_, v_pos_2110_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_pos_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
v_pos_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v___x_2114_, 1);
lean_dec(v_unused_2123_);
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_pos_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 1, v_snd_2108_);
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_pos_2115_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_snd_2108_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
else
{
lean_object* v_pos_2124_; lean_object* v_err_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_snd_2108_);
v_pos_2124_ = lean_ctor_get(v___x_2114_, 0);
v_err_2125_ = lean_ctor_get(v___x_2114_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2114_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_err_2125_);
lean_inc(v_pos_2124_);
lean_dec(v___x_2114_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_pos_2124_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_err_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(lean_object* v_as_2133_, size_t v_i_2134_, size_t v_stop_2135_, lean_object* v_b_2136_, lean_object* v___y_2137_){
_start:
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_usize_dec_eq(v_i_2134_, v_stop_2135_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___f_2140_; size_t v___x_2141_; size_t v___x_2142_; 
v___x_2139_ = lean_array_uget_borrowed(v_as_2133_, v_i_2134_);
lean_inc(v___x_2139_);
v___f_2140_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2140_, 0, v___x_2139_);
lean_closure_set(v___f_2140_, 1, v_b_2136_);
v___x_2141_ = ((size_t)1ULL);
v___x_2142_ = lean_usize_add(v_i_2134_, v___x_2141_);
v_i_2134_ = v___x_2142_;
v_b_2136_ = v___f_2140_;
goto _start;
}
else
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_apply_1(v_b_2136_, v___y_2137_);
return v___x_2144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___boxed(lean_object* v_as_2145_, lean_object* v_i_2146_, lean_object* v_stop_2147_, lean_object* v_b_2148_, lean_object* v___y_2149_){
_start:
{
size_t v_i_boxed_2150_; size_t v_stop_boxed_2151_; lean_object* v_res_2152_; 
v_i_boxed_2150_ = lean_unbox_usize(v_i_2146_);
lean_dec(v_i_2146_);
v_stop_boxed_2151_ = lean_unbox_usize(v_stop_2147_);
lean_dec(v_stop_2147_);
v_res_2152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2145_, v_i_boxed_2150_, v_stop_boxed_2151_, v_b_2148_, v___y_2149_);
lean_dec_ref(v_as_2145_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(lean_object* v_pairs_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = lean_array_get_size(v_pairs_2158_);
v___x_2162_ = lean_nat_dec_lt(v___x_2160_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_a_2159_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
return v___x_2164_;
}
else
{
lean_object* v___f_2165_; uint8_t v___x_2166_; 
v___f_2165_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2));
v___x_2166_ = lean_nat_dec_le(v___x_2161_, v___x_2161_);
if (v___x_2166_ == 0)
{
if (v___x_2162_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_a_2159_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
return v___x_2168_;
}
else
{
size_t v___x_2169_; size_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = ((size_t)0ULL);
v___x_2170_ = lean_usize_of_nat(v___x_2161_);
v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2158_, v___x_2169_, v___x_2170_, v___f_2165_, v_a_2159_);
return v___x_2171_;
}
}
else
{
size_t v___x_2172_; size_t v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = ((size_t)0ULL);
v___x_2173_ = lean_usize_of_nat(v___x_2161_);
v___x_2174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2158_, v___x_2172_, v___x_2173_, v___f_2165_, v_a_2159_);
return v___x_2174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___boxed(lean_object* v_pairs_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2175_, v_a_2176_);
lean_dec_ref(v_pairs_2175_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(lean_object* v_00_u03b1_2178_, lean_object* v_pairs_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2179_, v_a_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___boxed(lean_object* v_00_u03b1_2182_, lean_object* v_pairs_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(v_00_u03b1_2182_, v_pairs_2183_, v_a_2184_);
lean_dec_ref(v_pairs_2183_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_object* v_00_u03b1_2186_, lean_object* v_as_2187_, size_t v_i_2188_, size_t v_stop_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2187_, v_i_2188_, v_stop_2189_, v_b_2190_, v___y_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___boxed(lean_object* v_00_u03b1_2193_, lean_object* v_as_2194_, lean_object* v_i_2195_, lean_object* v_stop_2196_, lean_object* v_b_2197_, lean_object* v___y_2198_){
_start:
{
size_t v_i_boxed_2199_; size_t v_stop_boxed_2200_; lean_object* v_res_2201_; 
v_i_boxed_2199_ = lean_unbox_usize(v_i_2195_);
lean_dec(v_i_2195_);
v_stop_boxed_2200_ = lean_unbox_usize(v_stop_2196_);
lean_dec(v_stop_2196_);
v_res_2201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(v_00_u03b1_2193_, v_as_2194_, v_i_boxed_2199_, v_stop_boxed_2200_, v_b_2197_, v___y_2198_);
lean_dec_ref(v_as_2194_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(size_t v_sz_2202_, size_t v_i_2203_, lean_object* v_bs_2204_){
_start:
{
uint8_t v___x_2205_; 
v___x_2205_ = lean_usize_dec_lt(v_i_2203_, v_sz_2202_);
if (v___x_2205_ == 0)
{
return v_bs_2204_;
}
else
{
lean_object* v_v_2206_; lean_object* v___x_2207_; lean_object* v_bs_x27_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; lean_object* v___x_2216_; 
v_v_2206_ = lean_array_uget(v_bs_2204_, v_i_2203_);
v___x_2207_ = lean_unsigned_to_nat(0u);
v_bs_x27_2208_ = lean_array_uset(v_bs_2204_, v_i_2203_, v___x_2207_);
v___x_2209_ = lean_usize_to_nat(v_i_2203_);
v___x_2210_ = lean_nat_to_int(v___x_2209_);
v___x_2211_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2212_ = lean_int_add(v___x_2210_, v___x_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v_v_2206_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = ((size_t)1ULL);
v___x_2215_ = lean_usize_add(v_i_2203_, v___x_2214_);
v___x_2216_ = lean_array_uset(v_bs_x27_2208_, v_i_2203_, v___x_2213_);
v_i_2203_ = v___x_2215_;
v_bs_2204_ = v___x_2216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2218_, lean_object* v_i_2219_, lean_object* v_bs_2220_){
_start:
{
size_t v_sz_boxed_2221_; size_t v_i_boxed_2222_; lean_object* v_res_2223_; 
v_sz_boxed_2221_ = lean_unbox_usize(v_sz_2218_);
lean_dec(v_sz_2218_);
v_i_boxed_2222_ = lean_unbox_usize(v_i_2219_);
lean_dec(v_i_2219_);
v_res_2223_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_boxed_2221_, v_i_boxed_2222_, v_bs_2220_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(lean_object* v_as_2224_, size_t v_sz_2225_, size_t v_i_2226_, lean_object* v_bs_2227_){
_start:
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_usize_dec_lt(v_i_2226_, v_sz_2225_);
if (v___x_2228_ == 0)
{
return v_bs_2227_;
}
else
{
lean_object* v_v_2229_; lean_object* v___x_2230_; lean_object* v_bs_x27_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; size_t v___x_2237_; size_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_v_2229_ = lean_array_uget(v_bs_2227_, v_i_2226_);
v___x_2230_ = lean_unsigned_to_nat(0u);
v_bs_x27_2231_ = lean_array_uset(v_bs_2227_, v_i_2226_, v___x_2230_);
v___x_2232_ = lean_usize_to_nat(v_i_2226_);
v___x_2233_ = lean_nat_to_int(v___x_2232_);
v___x_2234_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2235_ = lean_int_add(v___x_2233_, v___x_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2236_, 0, v_v_2229_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = ((size_t)1ULL);
v___x_2238_ = lean_usize_add(v_i_2226_, v___x_2237_);
v___x_2239_ = lean_array_uset(v_bs_x27_2231_, v_i_2226_, v___x_2236_);
v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2225_, v___x_2238_, v___x_2239_);
return v___x_2240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0___boxed(lean_object* v_as_2241_, lean_object* v_sz_2242_, lean_object* v_i_2243_, lean_object* v_bs_2244_){
_start:
{
size_t v_sz_boxed_2245_; size_t v_i_boxed_2246_; lean_object* v_res_2247_; 
v_sz_boxed_2245_ = lean_unbox_usize(v_sz_2242_);
lean_dec(v_sz_2242_);
v_i_boxed_2246_ = lean_unbox_usize(v_i_2243_);
lean_dec(v_i_2243_);
v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_as_2241_, v_sz_boxed_2245_, v_i_boxed_2246_, v_bs_2244_);
lean_dec_ref(v_as_2241_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(lean_object* v_arr_2248_){
_start:
{
size_t v_sz_2249_; size_t v___x_2250_; lean_object* v___x_2251_; 
v_sz_2249_ = lean_array_size(v_arr_2248_);
v___x_2250_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2248_);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2248_, v_sz_2249_, v___x_2250_, v_arr_2248_);
lean_dec_ref(v_arr_2248_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(lean_object* v_as_2252_, size_t v_sz_2253_, size_t v_i_2254_, lean_object* v_bs_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2253_, v_i_2254_, v_bs_2255_);
return v___x_2256_;
}
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
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object* v_x_2264_){
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object* v_x_2284_){
_start:
{
uint8_t v_res_2285_; lean_object* v_r_2286_; 
v_res_2285_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_x_2284_);
lean_dec(v_x_2284_);
v_r_2286_ = lean_box(v_res_2285_);
return v_r_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(size_t v_sz_2287_, size_t v_i_2288_, lean_object* v_bs_2289_){
_start:
{
uint8_t v___x_2290_; 
v___x_2290_ = lean_usize_dec_lt(v_i_2288_, v_sz_2287_);
if (v___x_2290_ == 0)
{
return v_bs_2289_;
}
else
{
lean_object* v_v_2291_; lean_object* v___x_2292_; lean_object* v_bs_x27_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v_v_2291_ = lean_array_uget(v_bs_2289_, v_i_2288_);
v___x_2292_ = lean_unsigned_to_nat(0u);
v_bs_x27_2293_ = lean_array_uset(v_bs_2289_, v_i_2288_, v___x_2292_);
v___x_2294_ = lean_usize_to_nat(v_i_2288_);
v___x_2295_ = lean_nat_to_int(v___x_2294_);
v___x_2296_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2297_ = lean_int_add(v___x_2295_, v___x_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = l_Std_Time_Weekday_ofOrdinal(v___x_2297_);
lean_dec(v___x_2297_);
v___x_2299_ = lean_box(v___x_2298_);
v___x_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2300_, 0, v_v_2291_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = ((size_t)1ULL);
v___x_2302_ = lean_usize_add(v_i_2288_, v___x_2301_);
v___x_2303_ = lean_array_uset(v_bs_x27_2293_, v_i_2288_, v___x_2300_);
v_i_2288_ = v___x_2302_;
v_bs_2289_ = v___x_2303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2305_, lean_object* v_i_2306_, lean_object* v_bs_2307_){
_start:
{
size_t v_sz_boxed_2308_; size_t v_i_boxed_2309_; lean_object* v_res_2310_; 
v_sz_boxed_2308_ = lean_unbox_usize(v_sz_2305_);
lean_dec(v_sz_2305_);
v_i_boxed_2309_ = lean_unbox_usize(v_i_2306_);
lean_dec(v_i_2306_);
v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_boxed_2308_, v_i_boxed_2309_, v_bs_2307_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(lean_object* v_as_2311_, size_t v_sz_2312_, size_t v_i_2313_, lean_object* v_bs_2314_){
_start:
{
uint8_t v___x_2315_; 
v___x_2315_ = lean_usize_dec_lt(v_i_2313_, v_sz_2312_);
if (v___x_2315_ == 0)
{
return v_bs_2314_;
}
else
{
lean_object* v_v_2316_; lean_object* v___x_2317_; lean_object* v_bs_x27_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; size_t v___x_2326_; size_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_v_2316_ = lean_array_uget(v_bs_2314_, v_i_2313_);
v___x_2317_ = lean_unsigned_to_nat(0u);
v_bs_x27_2318_ = lean_array_uset(v_bs_2314_, v_i_2313_, v___x_2317_);
v___x_2319_ = lean_usize_to_nat(v_i_2313_);
v___x_2320_ = lean_nat_to_int(v___x_2319_);
v___x_2321_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2322_ = lean_int_add(v___x_2320_, v___x_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = l_Std_Time_Weekday_ofOrdinal(v___x_2322_);
lean_dec(v___x_2322_);
v___x_2324_ = lean_box(v___x_2323_);
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v_v_2316_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = ((size_t)1ULL);
v___x_2327_ = lean_usize_add(v_i_2313_, v___x_2326_);
v___x_2328_ = lean_array_uset(v_bs_x27_2318_, v_i_2313_, v___x_2325_);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2312_, v___x_2327_, v___x_2328_);
return v___x_2329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0___boxed(lean_object* v_as_2330_, lean_object* v_sz_2331_, lean_object* v_i_2332_, lean_object* v_bs_2333_){
_start:
{
size_t v_sz_boxed_2334_; size_t v_i_boxed_2335_; lean_object* v_res_2336_; 
v_sz_boxed_2334_ = lean_unbox_usize(v_sz_2331_);
lean_dec(v_sz_2331_);
v_i_boxed_2335_ = lean_unbox_usize(v_i_2332_);
lean_dec(v_i_2332_);
v_res_2336_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_as_2330_, v_sz_boxed_2334_, v_i_boxed_2335_, v_bs_2333_);
lean_dec_ref(v_as_2330_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(lean_object* v_arr_2337_){
_start:
{
size_t v_sz_2338_; size_t v___x_2339_; lean_object* v___x_2340_; 
v_sz_2338_ = lean_array_size(v_arr_2337_);
v___x_2339_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2337_);
v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_arr_2337_, v_sz_2338_, v___x_2339_, v_arr_2337_);
lean_dec_ref(v_arr_2337_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(lean_object* v_as_2341_, size_t v_sz_2342_, size_t v_i_2343_, lean_object* v_bs_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2342_, v_i_2343_, v_bs_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___boxed(lean_object* v_as_2346_, lean_object* v_sz_2347_, lean_object* v_i_2348_, lean_object* v_bs_2349_){
_start:
{
size_t v_sz_boxed_2350_; size_t v_i_boxed_2351_; lean_object* v_res_2352_; 
v_sz_boxed_2350_ = lean_unbox_usize(v_sz_2347_);
lean_dec(v_sz_2347_);
v_i_boxed_2351_ = lean_unbox_usize(v_i_2348_);
lean_dec(v_i_2348_);
v_res_2352_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(v_as_2346_, v_sz_boxed_2350_, v_i_boxed_2351_, v_bs_2349_);
lean_dec_ref(v_as_2346_);
return v_res_2352_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object* v_x_2353_){
_start:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = lean_nat_dec_eq(v_x_2353_, v___x_2354_);
if (v___x_2355_ == 0)
{
uint8_t v___x_2356_; 
v___x_2356_ = 1;
return v___x_2356_;
}
else
{
uint8_t v___x_2357_; 
v___x_2357_ = 0;
return v___x_2357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object* v_x_2358_){
_start:
{
uint8_t v_res_2359_; lean_object* v_r_2360_; 
v_res_2359_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_x_2358_);
lean_dec(v_x_2358_);
v_r_2360_ = lean_box(v_res_2359_);
return v_r_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(size_t v_sz_2361_, size_t v_i_2362_, lean_object* v_bs_2363_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = lean_usize_dec_lt(v_i_2362_, v_sz_2361_);
if (v___x_2364_ == 0)
{
return v_bs_2363_;
}
else
{
lean_object* v_v_2365_; lean_object* v___x_2366_; lean_object* v_bs_x27_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; lean_object* v___x_2374_; 
v_v_2365_ = lean_array_uget(v_bs_2363_, v_i_2362_);
v___x_2366_ = lean_unsigned_to_nat(0u);
v_bs_x27_2367_ = lean_array_uset(v_bs_2363_, v_i_2362_, v___x_2366_);
v___x_2368_ = lean_usize_to_nat(v_i_2362_);
v___x_2369_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v___x_2368_);
lean_dec(v___x_2368_);
v___x_2370_ = lean_box(v___x_2369_);
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_v_2365_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = ((size_t)1ULL);
v___x_2373_ = lean_usize_add(v_i_2362_, v___x_2372_);
v___x_2374_ = lean_array_uset(v_bs_x27_2367_, v_i_2362_, v___x_2371_);
v_i_2362_ = v___x_2373_;
v_bs_2363_ = v___x_2374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg___boxed(lean_object* v_sz_2376_, lean_object* v_i_2377_, lean_object* v_bs_2378_){
_start:
{
size_t v_sz_boxed_2379_; size_t v_i_boxed_2380_; lean_object* v_res_2381_; 
v_sz_boxed_2379_ = lean_unbox_usize(v_sz_2376_);
lean_dec(v_sz_2376_);
v_i_boxed_2380_ = lean_unbox_usize(v_i_2377_);
lean_dec(v_i_2377_);
v_res_2381_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_boxed_2379_, v_i_boxed_2380_, v_bs_2378_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(lean_object* v_arr_2382_){
_start:
{
size_t v_sz_2383_; size_t v___x_2384_; lean_object* v___x_2385_; 
v_sz_2383_ = lean_array_size(v_arr_2382_);
v___x_2384_ = ((size_t)0ULL);
v___x_2385_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2383_, v___x_2384_, v_arr_2382_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(lean_object* v_as_2386_, size_t v_sz_2387_, size_t v_i_2388_, lean_object* v_bs_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2387_, v_i_2388_, v_bs_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___boxed(lean_object* v_as_2391_, lean_object* v_sz_2392_, lean_object* v_i_2393_, lean_object* v_bs_2394_){
_start:
{
size_t v_sz_boxed_2395_; size_t v_i_boxed_2396_; lean_object* v_res_2397_; 
v_sz_boxed_2395_ = lean_unbox_usize(v_sz_2392_);
lean_dec(v_sz_2392_);
v_i_boxed_2396_ = lean_unbox_usize(v_i_2393_);
lean_dec(v_i_2393_);
v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(v_as_2391_, v_sz_boxed_2395_, v_i_boxed_2396_, v_bs_2394_);
lean_dec_ref(v_as_2391_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(lean_object* v_arr_2398_){
_start:
{
size_t v_sz_2399_; size_t v___x_2400_; lean_object* v___x_2401_; 
v_sz_2399_ = lean_array_size(v_arr_2398_);
v___x_2400_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2398_);
v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2398_, v_sz_2399_, v___x_2400_, v_arr_2398_);
lean_dec_ref(v_arr_2398_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(lean_object* v_symbols_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_monthLong_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_monthLong_2404_ = lean_ctor_get(v_symbols_2402_, 0);
lean_inc_ref(v_monthLong_2404_);
lean_dec_ref(v_symbols_2402_);
v___x_2405_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthLong_2404_);
v___x_2406_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2405_, v_a_2403_);
lean_dec_ref(v___x_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object* v_symbols_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_monthShort_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_monthShort_2409_ = lean_ctor_get(v_symbols_2407_, 1);
lean_inc_ref(v_monthShort_2409_);
lean_dec_ref(v_symbols_2407_);
v___x_2410_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthShort_2409_);
v___x_2411_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2410_, v_a_2408_);
lean_dec_ref(v___x_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(lean_object* v_symbols_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_monthNarrow_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v_monthNarrow_2414_ = lean_ctor_get(v_symbols_2412_, 2);
lean_inc_ref(v_monthNarrow_2414_);
lean_dec_ref(v_symbols_2412_);
v___x_2415_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthNarrow_2414_);
v___x_2416_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2415_, v_a_2413_);
lean_dec_ref(v___x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(lean_object* v_symbols_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_weekdayLong_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_weekdayLong_2419_ = lean_ctor_get(v_symbols_2417_, 3);
lean_inc_ref(v_weekdayLong_2419_);
lean_dec_ref(v_symbols_2417_);
v___x_2420_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayLong_2419_);
v___x_2421_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2420_, v_a_2418_);
lean_dec_ref(v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(lean_object* v_symbols_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_weekdayShort_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_weekdayShort_2424_ = lean_ctor_get(v_symbols_2422_, 4);
lean_inc_ref(v_weekdayShort_2424_);
lean_dec_ref(v_symbols_2422_);
v___x_2425_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayShort_2424_);
v___x_2426_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2425_, v_a_2423_);
lean_dec_ref(v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(lean_object* v_symbols_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v_weekdayNarrow_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_weekdayNarrow_2429_ = lean_ctor_get(v_symbols_2427_, 5);
lean_inc_ref(v_weekdayNarrow_2429_);
lean_dec_ref(v_symbols_2427_);
v___x_2430_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayNarrow_2429_);
v___x_2431_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2430_, v_a_2428_);
lean_dec_ref(v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(lean_object* v_symbols_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_weekdayTwoLetter_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_weekdayTwoLetter_2434_ = lean_ctor_get(v_symbols_2432_, 6);
lean_inc_ref(v_weekdayTwoLetter_2434_);
lean_dec_ref(v_symbols_2432_);
v___x_2435_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayTwoLetter_2434_);
v___x_2436_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2435_, v_a_2433_);
lean_dec_ref(v___x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(lean_object* v_symbols_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_eraShort_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v_eraShort_2439_ = lean_ctor_get(v_symbols_2437_, 7);
lean_inc_ref(v_eraShort_2439_);
lean_dec_ref(v_symbols_2437_);
v___x_2440_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraShort_2439_);
v___x_2441_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2440_, v_a_2438_);
lean_dec_ref(v___x_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(lean_object* v_symbols_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v_eraLong_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_eraLong_2444_ = lean_ctor_get(v_symbols_2442_, 8);
lean_inc_ref(v_eraLong_2444_);
lean_dec_ref(v_symbols_2442_);
v___x_2445_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraLong_2444_);
v___x_2446_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2445_, v_a_2443_);
lean_dec_ref(v___x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(lean_object* v_symbols_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_eraNarrow_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_eraNarrow_2449_ = lean_ctor_get(v_symbols_2447_, 9);
lean_inc_ref(v_eraNarrow_2449_);
lean_dec_ref(v_symbols_2447_);
v___x_2450_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraNarrow_2449_);
v___x_2451_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2450_, v_a_2448_);
lean_dec_ref(v___x_2450_);
return v___x_2451_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_unsigned_to_nat(3u);
v___x_2453_ = lean_nat_to_int(v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber(lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
lean_inc_ref(v_a_2454_);
v___x_2456_ = l_Std_Internal_Parsec_String_pstring(v___x_2455_, v_a_2454_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_pos_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2465_; 
lean_dec_ref(v_a_2454_);
v_pos_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; 
v_unused_2466_ = lean_ctor_get(v___x_2456_, 1);
lean_dec(v_unused_2466_);
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_pos_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
v___x_2461_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 1, v___x_2461_);
v___x_2463_ = v___x_2459_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_pos_2457_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
else
{
lean_object* v_pos_2467_; lean_object* v_err_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2545_; 
v_pos_2467_ = lean_ctor_get(v___x_2456_, 0);
v_err_2468_ = lean_ctor_get(v___x_2456_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2470_ = v___x_2456_;
v_isShared_2471_ = v_isSharedCheck_2545_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_err_2468_);
lean_inc(v_pos_2467_);
lean_dec(v___x_2456_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2545_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_snd_2472_; lean_object* v_snd_2473_; uint8_t v_decide_2474_; 
v_snd_2472_ = lean_ctor_get(v_a_2454_, 1);
lean_inc(v_snd_2472_);
lean_dec_ref(v_a_2454_);
v_snd_2473_ = lean_ctor_get(v_pos_2467_, 1);
v_decide_2474_ = lean_nat_dec_eq(v_snd_2472_, v_snd_2473_);
lean_dec(v_snd_2472_);
if (v_decide_2474_ == 0)
{
lean_object* v___x_2476_; 
if (v_isShared_2471_ == 0)
{
v___x_2476_ = v___x_2470_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_pos_2467_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_err_2468_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_inc(v_snd_2473_);
lean_del_object(v___x_2470_);
lean_dec(v_err_2468_);
v___x_2478_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
v___x_2479_ = l_Std_Internal_Parsec_String_pstring(v___x_2478_, v_pos_2467_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_pos_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_snd_2473_);
v_pos_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2488_ == 0)
{
lean_object* v_unused_2489_; 
v_unused_2489_ = lean_ctor_get(v___x_2479_, 1);
lean_dec(v_unused_2489_);
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2488_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_pos_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2488_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2484_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2484_);
v___x_2486_ = v___x_2482_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_pos_2480_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
else
{
lean_object* v_pos_2490_; lean_object* v_err_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2544_; 
v_pos_2490_ = lean_ctor_get(v___x_2479_, 0);
v_err_2491_ = lean_ctor_get(v___x_2479_, 1);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2493_ = v___x_2479_;
v_isShared_2494_ = v_isSharedCheck_2544_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_err_2491_);
lean_inc(v_pos_2490_);
lean_dec(v___x_2479_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2544_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v_snd_2495_; uint8_t v_decide_2496_; 
v_snd_2495_ = lean_ctor_get(v_pos_2490_, 1);
v_decide_2496_ = lean_nat_dec_eq(v_snd_2473_, v_snd_2495_);
lean_dec(v_snd_2473_);
if (v_decide_2496_ == 0)
{
lean_object* v___x_2498_; 
if (v_isShared_2494_ == 0)
{
v___x_2498_ = v___x_2493_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_pos_2490_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_err_2491_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
else
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_inc(v_snd_2495_);
lean_del_object(v___x_2493_);
lean_dec(v_err_2491_);
v___x_2500_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
v___x_2501_ = l_Std_Internal_Parsec_String_pstring(v___x_2500_, v_pos_2490_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_pos_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v_snd_2495_);
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
v___x_2506_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0);
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
lean_object* v_pos_2512_; lean_object* v_err_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2543_; 
v_pos_2512_ = lean_ctor_get(v___x_2501_, 0);
v_err_2513_ = lean_ctor_get(v___x_2501_, 1);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2515_ = v___x_2501_;
v_isShared_2516_ = v_isSharedCheck_2543_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_err_2513_);
lean_inc(v_pos_2512_);
lean_dec(v___x_2501_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2543_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_snd_2517_; uint8_t v_decide_2518_; 
v_snd_2517_ = lean_ctor_get(v_pos_2512_, 1);
v_decide_2518_ = lean_nat_dec_eq(v_snd_2495_, v_snd_2517_);
lean_dec(v_snd_2495_);
if (v_decide_2518_ == 0)
{
lean_object* v___x_2520_; 
if (v_isShared_2516_ == 0)
{
v___x_2520_ = v___x_2515_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_pos_2512_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_err_2513_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_del_object(v___x_2515_);
lean_dec(v_err_2513_);
v___x_2522_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
v___x_2523_ = l_Std_Internal_Parsec_String_pstring(v___x_2522_, v_pos_2512_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_pos_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2532_; 
v_pos_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2523_, 1);
lean_dec(v_unused_2533_);
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_pos_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 1, v___x_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_pos_2524_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
else
{
lean_object* v_pos_2534_; lean_object* v_err_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
v_pos_2534_ = lean_ctor_get(v___x_2523_, 0);
v_err_2535_ = lean_ctor_get(v___x_2523_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2523_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_err_2535_);
lean_inc(v_pos_2534_);
lean_dec(v___x_2523_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_pos_2534_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_err_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(lean_object* v_symbols_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_quarterLong_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v_quarterLong_2548_ = lean_ctor_get(v_symbols_2546_, 11);
lean_inc_ref(v_quarterLong_2548_);
lean_dec_ref(v_symbols_2546_);
v___x_2549_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterLong_2548_);
v___x_2550_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2549_, v_a_2547_);
lean_dec_ref(v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(lean_object* v_symbols_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_quarterShort_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_quarterShort_2553_ = lean_ctor_get(v_symbols_2551_, 10);
lean_inc_ref(v_quarterShort_2553_);
lean_dec_ref(v_symbols_2551_);
v___x_2554_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterShort_2553_);
v___x_2555_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2554_, v_a_2552_);
lean_dec_ref(v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(lean_object* v_symbols_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v_quarterNarrow_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_quarterNarrow_2558_ = lean_ctor_get(v_symbols_2556_, 12);
lean_inc_ref(v_quarterNarrow_2558_);
lean_dec_ref(v_symbols_2556_);
v___x_2559_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterNarrow_2558_);
v___x_2560_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2559_, v_a_2557_);
lean_dec_ref(v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(lean_object* v_symbols_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_amShort_2563_; lean_object* v_pmShort_2564_; lean_object* v___x_2565_; 
v_amShort_2563_ = lean_ctor_get(v_symbols_2561_, 13);
lean_inc_ref(v_amShort_2563_);
v_pmShort_2564_ = lean_ctor_get(v_symbols_2561_, 14);
lean_inc_ref(v_pmShort_2564_);
lean_dec_ref(v_symbols_2561_);
lean_inc_ref(v_a_2562_);
v___x_2565_ = l_Std_Internal_Parsec_String_pstring(v_amShort_2563_, v_a_2562_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_pos_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2575_; 
lean_dec_ref(v_pmShort_2564_);
lean_dec_ref(v_a_2562_);
v_pos_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v___x_2565_, 1);
lean_dec(v_unused_2576_);
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2575_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_pos_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2575_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2570_ = 0;
v___x_2571_ = lean_box(v___x_2570_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 1, v___x_2571_);
v___x_2573_ = v___x_2568_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_pos_2566_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
lean_object* v_pos_2577_; lean_object* v_err_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2609_; 
v_pos_2577_ = lean_ctor_get(v___x_2565_, 0);
v_err_2578_ = lean_ctor_get(v___x_2565_, 1);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2580_ = v___x_2565_;
v_isShared_2581_ = v_isSharedCheck_2609_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_err_2578_);
lean_inc(v_pos_2577_);
lean_dec(v___x_2565_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2609_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_snd_2582_; lean_object* v_snd_2583_; uint8_t v_decide_2584_; 
v_snd_2582_ = lean_ctor_get(v_a_2562_, 1);
lean_inc(v_snd_2582_);
lean_dec_ref(v_a_2562_);
v_snd_2583_ = lean_ctor_get(v_pos_2577_, 1);
v_decide_2584_ = lean_nat_dec_eq(v_snd_2582_, v_snd_2583_);
lean_dec(v_snd_2582_);
if (v_decide_2584_ == 0)
{
lean_object* v___x_2586_; 
lean_dec_ref(v_pmShort_2564_);
if (v_isShared_2581_ == 0)
{
v___x_2586_ = v___x_2580_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_pos_2577_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_err_2578_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
else
{
lean_object* v___x_2588_; 
lean_del_object(v___x_2580_);
lean_dec(v_err_2578_);
v___x_2588_ = l_Std_Internal_Parsec_String_pstring(v_pmShort_2564_, v_pos_2577_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_pos_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2598_; 
v_pos_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; 
v_unused_2599_ = lean_ctor_get(v___x_2588_, 1);
lean_dec(v_unused_2599_);
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2598_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_pos_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2598_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2593_ = 1;
v___x_2594_ = lean_box(v___x_2593_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v___x_2594_);
v___x_2596_ = v___x_2591_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_pos_2589_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
else
{
lean_object* v_pos_2600_; lean_object* v_err_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
v_pos_2600_ = lean_ctor_get(v___x_2588_, 0);
v_err_2601_ = lean_ctor_get(v___x_2588_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2588_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_err_2601_);
lean_inc(v_pos_2600_);
lean_dec(v___x_2588_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_pos_2600_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_err_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(lean_object* v_symbols_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_amLong_2612_; lean_object* v_pmLong_2613_; lean_object* v___x_2614_; 
v_amLong_2612_ = lean_ctor_get(v_symbols_2610_, 15);
lean_inc_ref(v_amLong_2612_);
v_pmLong_2613_ = lean_ctor_get(v_symbols_2610_, 16);
lean_inc_ref(v_pmLong_2613_);
lean_dec_ref(v_symbols_2610_);
lean_inc_ref(v_a_2611_);
v___x_2614_ = l_Std_Internal_Parsec_String_pstring(v_amLong_2612_, v_a_2611_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_pos_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_pmLong_2613_);
lean_dec_ref(v_a_2611_);
v_pos_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2624_ == 0)
{
lean_object* v_unused_2625_; 
v_unused_2625_ = lean_ctor_get(v___x_2614_, 1);
lean_dec(v_unused_2625_);
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2624_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_pos_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2624_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
uint8_t v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2619_ = 0;
v___x_2620_ = lean_box(v___x_2619_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 1, v___x_2620_);
v___x_2622_ = v___x_2617_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_pos_2615_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
else
{
lean_object* v_pos_2626_; lean_object* v_err_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2658_; 
v_pos_2626_ = lean_ctor_get(v___x_2614_, 0);
v_err_2627_ = lean_ctor_get(v___x_2614_, 1);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2629_ = v___x_2614_;
v_isShared_2630_ = v_isSharedCheck_2658_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_err_2627_);
lean_inc(v_pos_2626_);
lean_dec(v___x_2614_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2658_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_snd_2631_; lean_object* v_snd_2632_; uint8_t v_decide_2633_; 
v_snd_2631_ = lean_ctor_get(v_a_2611_, 1);
lean_inc(v_snd_2631_);
lean_dec_ref(v_a_2611_);
v_snd_2632_ = lean_ctor_get(v_pos_2626_, 1);
v_decide_2633_ = lean_nat_dec_eq(v_snd_2631_, v_snd_2632_);
lean_dec(v_snd_2631_);
if (v_decide_2633_ == 0)
{
lean_object* v___x_2635_; 
lean_dec_ref(v_pmLong_2613_);
if (v_isShared_2630_ == 0)
{
v___x_2635_ = v___x_2629_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_pos_2626_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_err_2627_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
else
{
lean_object* v___x_2637_; 
lean_del_object(v___x_2629_);
lean_dec(v_err_2627_);
v___x_2637_ = l_Std_Internal_Parsec_String_pstring(v_pmLong_2613_, v_pos_2626_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_pos_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2647_; 
v_pos_2638_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; 
v_unused_2648_ = lean_ctor_get(v___x_2637_, 1);
lean_dec(v_unused_2648_);
v___x_2640_ = v___x_2637_;
v_isShared_2641_ = v_isSharedCheck_2647_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_pos_2638_);
lean_dec(v___x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2647_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2642_ = 1;
v___x_2643_ = lean_box(v___x_2642_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 1, v___x_2643_);
v___x_2645_ = v___x_2640_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_pos_2638_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
else
{
lean_object* v_pos_2649_; lean_object* v_err_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v_pos_2649_ = lean_ctor_get(v___x_2637_, 0);
v_err_2650_ = lean_ctor_get(v___x_2637_, 1);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2637_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_err_2650_);
lean_inc(v_pos_2649_);
lean_dec(v___x_2637_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_pos_2649_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_err_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(lean_object* v_symbols_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_amNarrow_2661_; lean_object* v_pmNarrow_2662_; lean_object* v___x_2663_; 
v_amNarrow_2661_ = lean_ctor_get(v_symbols_2659_, 17);
lean_inc_ref(v_amNarrow_2661_);
v_pmNarrow_2662_ = lean_ctor_get(v_symbols_2659_, 18);
lean_inc_ref(v_pmNarrow_2662_);
lean_dec_ref(v_symbols_2659_);
lean_inc_ref(v_a_2660_);
v___x_2663_ = l_Std_Internal_Parsec_String_pstring(v_amNarrow_2661_, v_a_2660_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_pos_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref(v_pmNarrow_2662_);
lean_dec_ref(v_a_2660_);
v_pos_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; 
v_unused_2674_ = lean_ctor_get(v___x_2663_, 1);
lean_dec(v_unused_2674_);
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2673_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_pos_2664_);
lean_dec(v___x_2663_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2673_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2668_ = 0;
v___x_2669_ = lean_box(v___x_2668_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2669_);
v___x_2671_ = v___x_2666_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_pos_2664_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
else
{
lean_object* v_pos_2675_; lean_object* v_err_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2707_; 
v_pos_2675_ = lean_ctor_get(v___x_2663_, 0);
v_err_2676_ = lean_ctor_get(v___x_2663_, 1);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2678_ = v___x_2663_;
v_isShared_2679_ = v_isSharedCheck_2707_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_err_2676_);
lean_inc(v_pos_2675_);
lean_dec(v___x_2663_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2707_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v_snd_2680_; lean_object* v_snd_2681_; uint8_t v_decide_2682_; 
v_snd_2680_ = lean_ctor_get(v_a_2660_, 1);
lean_inc(v_snd_2680_);
lean_dec_ref(v_a_2660_);
v_snd_2681_ = lean_ctor_get(v_pos_2675_, 1);
v_decide_2682_ = lean_nat_dec_eq(v_snd_2680_, v_snd_2681_);
lean_dec(v_snd_2680_);
if (v_decide_2682_ == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref(v_pmNarrow_2662_);
if (v_isShared_2679_ == 0)
{
v___x_2684_ = v___x_2678_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_pos_2675_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_err_2676_);
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
lean_del_object(v___x_2678_);
lean_dec(v_err_2676_);
v___x_2686_ = l_Std_Internal_Parsec_String_pstring(v_pmNarrow_2662_, v_pos_2675_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(lean_object* v_dp_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_am_2710_; lean_object* v_pm_2711_; lean_object* v_noon_2712_; lean_object* v_midnight_2713_; lean_object* v___x_2714_; 
v_am_2710_ = lean_ctor_get(v_dp_2708_, 0);
lean_inc_ref(v_am_2710_);
v_pm_2711_ = lean_ctor_get(v_dp_2708_, 1);
lean_inc_ref(v_pm_2711_);
v_noon_2712_ = lean_ctor_get(v_dp_2708_, 2);
lean_inc_ref(v_noon_2712_);
v_midnight_2713_ = lean_ctor_get(v_dp_2708_, 3);
lean_inc_ref(v_midnight_2713_);
lean_dec_ref(v_dp_2708_);
lean_inc_ref(v_a_2709_);
v___x_2714_ = l_Std_Internal_Parsec_String_pstring(v_midnight_2713_, v_a_2709_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_pos_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2724_; 
lean_dec_ref(v_noon_2712_);
lean_dec_ref(v_pm_2711_);
lean_dec_ref(v_am_2710_);
lean_dec_ref(v_a_2709_);
v_pos_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2724_ == 0)
{
lean_object* v_unused_2725_; 
v_unused_2725_ = lean_ctor_get(v___x_2714_, 1);
lean_dec(v_unused_2725_);
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2724_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_pos_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2724_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
uint8_t v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2719_ = 3;
v___x_2720_ = lean_box(v___x_2719_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v___x_2720_);
v___x_2722_ = v___x_2717_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_pos_2715_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
else
{
lean_object* v_pos_2726_; lean_object* v_err_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2804_; 
v_pos_2726_ = lean_ctor_get(v___x_2714_, 0);
v_err_2727_ = lean_ctor_get(v___x_2714_, 1);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2729_ = v___x_2714_;
v_isShared_2730_ = v_isSharedCheck_2804_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_err_2727_);
lean_inc(v_pos_2726_);
lean_dec(v___x_2714_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2804_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v_snd_2731_; lean_object* v_snd_2732_; uint8_t v_decide_2733_; 
v_snd_2731_ = lean_ctor_get(v_a_2709_, 1);
lean_inc(v_snd_2731_);
lean_dec_ref(v_a_2709_);
v_snd_2732_ = lean_ctor_get(v_pos_2726_, 1);
v_decide_2733_ = lean_nat_dec_eq(v_snd_2731_, v_snd_2732_);
lean_dec(v_snd_2731_);
if (v_decide_2733_ == 0)
{
lean_object* v___x_2735_; 
lean_dec_ref(v_noon_2712_);
lean_dec_ref(v_pm_2711_);
lean_dec_ref(v_am_2710_);
if (v_isShared_2730_ == 0)
{
v___x_2735_ = v___x_2729_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_pos_2726_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_err_2727_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
else
{
lean_object* v___x_2737_; 
lean_inc(v_snd_2732_);
lean_del_object(v___x_2729_);
lean_dec(v_err_2727_);
v___x_2737_ = l_Std_Internal_Parsec_String_pstring(v_noon_2712_, v_pos_2726_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_pos_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_snd_2732_);
lean_dec_ref(v_pm_2711_);
lean_dec_ref(v_am_2710_);
v_pos_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2747_ == 0)
{
lean_object* v_unused_2748_; 
v_unused_2748_ = lean_ctor_get(v___x_2737_, 1);
lean_dec(v_unused_2748_);
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_pos_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
uint8_t v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2742_ = 2;
v___x_2743_ = lean_box(v___x_2742_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 1, v___x_2743_);
v___x_2745_ = v___x_2740_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_pos_2738_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
else
{
lean_object* v_pos_2749_; lean_object* v_err_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2803_; 
v_pos_2749_ = lean_ctor_get(v___x_2737_, 0);
v_err_2750_ = lean_ctor_get(v___x_2737_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2752_ = v___x_2737_;
v_isShared_2753_ = v_isSharedCheck_2803_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_err_2750_);
lean_inc(v_pos_2749_);
lean_dec(v___x_2737_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2803_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v_snd_2754_; uint8_t v_decide_2755_; 
v_snd_2754_ = lean_ctor_get(v_pos_2749_, 1);
v_decide_2755_ = lean_nat_dec_eq(v_snd_2732_, v_snd_2754_);
lean_dec(v_snd_2732_);
if (v_decide_2755_ == 0)
{
lean_object* v___x_2757_; 
lean_dec_ref(v_pm_2711_);
lean_dec_ref(v_am_2710_);
if (v_isShared_2753_ == 0)
{
v___x_2757_ = v___x_2752_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_pos_2749_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_err_2750_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
else
{
lean_object* v___x_2759_; 
lean_inc(v_snd_2754_);
lean_del_object(v___x_2752_);
lean_dec(v_err_2750_);
v___x_2759_ = l_Std_Internal_Parsec_String_pstring(v_am_2710_, v_pos_2749_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_pos_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_snd_2754_);
lean_dec_ref(v_pm_2711_);
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
v___x_2764_ = 0;
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
lean_object* v_pos_2771_; lean_object* v_err_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2802_; 
v_pos_2771_ = lean_ctor_get(v___x_2759_, 0);
v_err_2772_ = lean_ctor_get(v___x_2759_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2774_ = v___x_2759_;
v_isShared_2775_ = v_isSharedCheck_2802_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_err_2772_);
lean_inc(v_pos_2771_);
lean_dec(v___x_2759_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2802_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v_snd_2776_; uint8_t v_decide_2777_; 
v_snd_2776_ = lean_ctor_get(v_pos_2771_, 1);
v_decide_2777_ = lean_nat_dec_eq(v_snd_2754_, v_snd_2776_);
lean_dec(v_snd_2754_);
if (v_decide_2777_ == 0)
{
lean_object* v___x_2779_; 
lean_dec_ref(v_pm_2711_);
if (v_isShared_2775_ == 0)
{
v___x_2779_ = v___x_2774_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_pos_2771_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_err_2772_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
else
{
lean_object* v___x_2781_; 
lean_del_object(v___x_2774_);
lean_dec(v_err_2772_);
v___x_2781_ = l_Std_Internal_Parsec_String_pstring(v_pm_2711_, v_pos_2771_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_pos_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2791_; 
v_pos_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2791_ == 0)
{
lean_object* v_unused_2792_; 
v_unused_2792_ = lean_ctor_get(v___x_2781_, 1);
lean_dec(v_unused_2792_);
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2791_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_pos_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2791_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
uint8_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2786_ = 1;
v___x_2787_ = lean_box(v___x_2786_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 1, v___x_2787_);
v___x_2789_ = v___x_2784_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_pos_2782_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
else
{
lean_object* v_pos_2793_; lean_object* v_err_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
v_pos_2793_ = lean_ctor_get(v___x_2781_, 0);
v_err_2794_ = lean_ctor_get(v___x_2781_, 1);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2781_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_err_2794_);
lean_inc(v_pos_2793_);
lean_dec(v___x_2781_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_pos_2793_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_err_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(lean_object* v_arr_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v_pairs_2844_; lean_object* v___x_2845_; 
v___x_2807_ = lean_unsigned_to_nat(6u);
v___x_2808_ = lean_unsigned_to_nat(0u);
v___x_2809_ = lean_array_fget_borrowed(v_arr_2805_, v___x_2808_);
v___x_2810_ = 0;
v___x_2811_ = lean_box(v___x_2810_);
lean_inc(v___x_2809_);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2809_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = lean_unsigned_to_nat(1u);
v___x_2814_ = lean_array_fget_borrowed(v_arr_2805_, v___x_2813_);
v___x_2815_ = 1;
v___x_2816_ = lean_box(v___x_2815_);
lean_inc(v___x_2814_);
v___x_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2814_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = lean_unsigned_to_nat(2u);
v___x_2819_ = lean_array_fget_borrowed(v_arr_2805_, v___x_2818_);
v___x_2820_ = 2;
v___x_2821_ = lean_box(v___x_2820_);
lean_inc(v___x_2819_);
v___x_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2819_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = lean_unsigned_to_nat(3u);
v___x_2824_ = lean_array_fget_borrowed(v_arr_2805_, v___x_2823_);
v___x_2825_ = 3;
v___x_2826_ = lean_box(v___x_2825_);
lean_inc(v___x_2824_);
v___x_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2824_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = lean_unsigned_to_nat(4u);
v___x_2829_ = lean_array_fget_borrowed(v_arr_2805_, v___x_2828_);
v___x_2830_ = 4;
v___x_2831_ = lean_box(v___x_2830_);
lean_inc(v___x_2829_);
v___x_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2829_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = lean_unsigned_to_nat(5u);
v___x_2834_ = lean_array_fget_borrowed(v_arr_2805_, v___x_2833_);
v___x_2835_ = 5;
v___x_2836_ = lean_box(v___x_2835_);
lean_inc(v___x_2834_);
v___x_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2834_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = lean_mk_empty_array_with_capacity(v___x_2807_);
v___x_2839_ = lean_array_push(v___x_2838_, v___x_2812_);
v___x_2840_ = lean_array_push(v___x_2839_, v___x_2817_);
v___x_2841_ = lean_array_push(v___x_2840_, v___x_2822_);
v___x_2842_ = lean_array_push(v___x_2841_, v___x_2827_);
v___x_2843_ = lean_array_push(v___x_2842_, v___x_2832_);
v_pairs_2844_ = lean_array_push(v___x_2843_, v___x_2837_);
v___x_2845_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2844_, v_a_2806_);
lean_dec_ref(v_pairs_2844_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom___boxed(lean_object* v_arr_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_arr_2846_, v_a_2847_);
lean_dec_ref(v_arr_2846_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(lean_object* v_parse_2849_, lean_object* v_size_2850_, lean_object* v_acc_2851_, lean_object* v_count_2852_, lean_object* v_a_2853_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_nat_dec_le(v_size_2850_, v_count_2852_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_inc_ref(v_parse_2849_);
v___x_2855_ = lean_apply_1(v_parse_2849_, v_a_2853_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_pos_2856_; lean_object* v_res_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_pos_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_pos_2856_);
v_res_2857_ = lean_ctor_get(v___x_2855_, 1);
lean_inc(v_res_2857_);
lean_dec_ref_known(v___x_2855_, 2);
v___x_2858_ = lean_array_push(v_acc_2851_, v_res_2857_);
v___x_2859_ = lean_unsigned_to_nat(1u);
v___x_2860_ = lean_nat_add(v_count_2852_, v___x_2859_);
lean_dec(v_count_2852_);
v_acc_2851_ = v___x_2858_;
v_count_2852_ = v___x_2860_;
v_a_2853_ = v_pos_2856_;
goto _start;
}
else
{
lean_object* v_pos_2862_; lean_object* v_err_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_count_2852_);
lean_dec_ref(v_acc_2851_);
lean_dec_ref(v_parse_2849_);
v_pos_2862_ = lean_ctor_get(v___x_2855_, 0);
v_err_2863_ = lean_ctor_get(v___x_2855_, 1);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2855_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_err_2863_);
lean_inc(v_pos_2862_);
lean_dec(v___x_2855_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_pos_2862_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_err_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v___x_2871_; 
lean_dec(v_count_2852_);
lean_dec_ref(v_parse_2849_);
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v_a_2853_);
lean_ctor_set(v___x_2871_, 1, v_acc_2851_);
return v___x_2871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg___boxed(lean_object* v_parse_2872_, lean_object* v_size_2873_, lean_object* v_acc_2874_, lean_object* v_count_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2872_, v_size_2873_, v_acc_2874_, v_count_2875_, v_a_2876_);
lean_dec(v_size_2873_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(lean_object* v_00_u03b1_2878_, lean_object* v_parse_2879_, lean_object* v_size_2880_, lean_object* v_acc_2881_, lean_object* v_count_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2879_, v_size_2880_, v_acc_2881_, v_count_2882_, v_a_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___boxed(lean_object* v_00_u03b1_2885_, lean_object* v_parse_2886_, lean_object* v_size_2887_, lean_object* v_acc_2888_, lean_object* v_count_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(v_00_u03b1_2885_, v_parse_2886_, v_size_2887_, v_acc_2888_, v_count_2889_, v_a_2890_);
lean_dec(v_size_2887_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(lean_object* v_parse_2894_, lean_object* v_size_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0));
v___x_2898_ = lean_unsigned_to_nat(12u);
v___x_2899_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2894_, v_size_2895_, v___x_2897_, v___x_2898_, v_a_2896_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___boxed(lean_object* v_parse_2900_, lean_object* v_size_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2900_, v_size_2901_, v_a_2902_);
lean_dec(v_size_2901_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly(lean_object* v_00_u03b1_2904_, lean_object* v_parse_2905_, lean_object* v_size_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2905_, v_size_2906_, v_a_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___boxed(lean_object* v_00_u03b1_2909_, lean_object* v_parse_2910_, lean_object* v_size_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly(v_00_u03b1_2909_, v_parse_2910_, v_size_2911_, v_a_2912_);
lean_dec(v_size_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object* v_parse_2914_, lean_object* v_size_2915_, lean_object* v_acc_2916_, lean_object* v_count_2917_, lean_object* v_a_2918_){
_start:
{
uint8_t v___x_2919_; 
v___x_2919_ = lean_nat_dec_le(v_size_2915_, v_count_2917_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; 
lean_inc_ref(v_parse_2914_);
v___x_2920_ = lean_apply_1(v_parse_2914_, v_a_2918_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_pos_2921_; lean_object* v_res_2922_; uint32_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_pos_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_pos_2921_);
v_res_2922_ = lean_ctor_get(v___x_2920_, 1);
lean_inc(v_res_2922_);
lean_dec_ref_known(v___x_2920_, 2);
v___x_2923_ = lean_unbox_uint32(v_res_2922_);
lean_dec(v_res_2922_);
v___x_2924_ = lean_string_push(v_acc_2916_, v___x_2923_);
v___x_2925_ = lean_unsigned_to_nat(1u);
v___x_2926_ = lean_nat_add(v_count_2917_, v___x_2925_);
lean_dec(v_count_2917_);
v_acc_2916_ = v___x_2924_;
v_count_2917_ = v___x_2926_;
v_a_2918_ = v_pos_2921_;
goto _start;
}
else
{
lean_object* v_pos_2928_; lean_object* v_err_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v_count_2917_);
lean_dec_ref(v_acc_2916_);
lean_dec_ref(v_parse_2914_);
v_pos_2928_ = lean_ctor_get(v___x_2920_, 0);
v_err_2929_ = lean_ctor_get(v___x_2920_, 1);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2920_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_err_2929_);
lean_inc(v_pos_2928_);
lean_dec(v___x_2920_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_pos_2928_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_err_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
else
{
lean_object* v___x_2937_; 
lean_dec(v_count_2917_);
lean_dec_ref(v_parse_2914_);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v_a_2918_);
lean_ctor_set(v___x_2937_, 1, v_acc_2916_);
return v___x_2937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object* v_parse_2938_, lean_object* v_size_2939_, lean_object* v_acc_2940_, lean_object* v_count_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2938_, v_size_2939_, v_acc_2940_, v_count_2941_, v_a_2942_);
lean_dec(v_size_2939_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object* v_parse_2944_, lean_object* v_size_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_2948_ = lean_unsigned_to_nat(0u);
v___x_2949_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2944_, v_size_2945_, v___x_2947_, v___x_2948_, v_a_2946_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object* v_parse_2950_, lean_object* v_size_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v_parse_2950_, v_size_2951_, v_a_2952_);
lean_dec(v_size_2951_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object* v_parser_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v_pos_2957_; lean_object* v_res_2958_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
lean_inc_ref(v_a_2955_);
v___x_2991_ = l_Std_Internal_Parsec_String_pstring(v___x_2990_, v_a_2955_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_pos_2992_; lean_object* v_res_2993_; lean_object* v___x_2994_; 
lean_dec_ref(v_a_2955_);
v_pos_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_pos_2992_);
v_res_2993_ = lean_ctor_get(v___x_2991_, 1);
lean_inc(v_res_2993_);
lean_dec_ref_known(v___x_2991_, 2);
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v_res_2993_);
v_pos_2957_ = v_pos_2992_;
v_res_2958_ = v___x_2994_;
goto v___jp_2956_;
}
else
{
lean_object* v_pos_2995_; lean_object* v_err_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3007_; 
v_pos_2995_ = lean_ctor_get(v___x_2991_, 0);
v_err_2996_ = lean_ctor_get(v___x_2991_, 1);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2998_ = v___x_2991_;
v_isShared_2999_ = v_isSharedCheck_3007_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_err_2996_);
lean_inc(v_pos_2995_);
lean_dec(v___x_2991_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3007_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v_snd_3000_; lean_object* v_snd_3001_; uint8_t v_decide_3002_; 
v_snd_3000_ = lean_ctor_get(v_a_2955_, 1);
lean_inc(v_snd_3000_);
lean_dec_ref(v_a_2955_);
v_snd_3001_ = lean_ctor_get(v_pos_2995_, 1);
v_decide_3002_ = lean_nat_dec_eq(v_snd_3000_, v_snd_3001_);
lean_dec(v_snd_3000_);
if (v_decide_3002_ == 0)
{
lean_object* v___x_3004_; 
lean_dec_ref(v_parser_2954_);
if (v_isShared_2999_ == 0)
{
v___x_3004_ = v___x_2998_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_pos_2995_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_err_2996_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
else
{
lean_object* v___x_3006_; 
lean_del_object(v___x_2998_);
lean_dec(v_err_2996_);
v___x_3006_ = lean_box(0);
v_pos_2957_ = v_pos_2995_;
v_res_2958_ = v___x_3006_;
goto v___jp_2956_;
}
}
}
v___jp_2956_:
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_apply_1(v_parser_2954_, v_pos_2957_);
if (lean_obj_tag(v___x_2959_) == 0)
{
if (lean_obj_tag(v_res_2958_) == 0)
{
lean_object* v_pos_2960_; lean_object* v_res_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2969_; 
v_pos_2960_ = lean_ctor_get(v___x_2959_, 0);
v_res_2961_ = lean_ctor_get(v___x_2959_, 1);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2963_ = v___x_2959_;
v_isShared_2964_ = v_isSharedCheck_2969_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_res_2961_);
lean_inc(v_pos_2960_);
lean_dec(v___x_2959_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2969_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2965_ = lean_nat_to_int(v_res_2961_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_2965_);
v___x_2967_ = v___x_2963_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_pos_2960_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
else
{
lean_object* v_pos_2970_; lean_object* v_res_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref_known(v_res_2958_, 1);
v_pos_2970_ = lean_ctor_get(v___x_2959_, 0);
v_res_2971_ = lean_ctor_get(v___x_2959_, 1);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2973_ = v___x_2959_;
v_isShared_2974_ = v_isSharedCheck_2980_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_res_2971_);
lean_inc(v_pos_2970_);
lean_dec(v___x_2959_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2980_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2975_ = lean_nat_to_int(v_res_2971_);
v___x_2976_ = lean_int_neg(v___x_2975_);
lean_dec(v___x_2975_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 1, v___x_2976_);
v___x_2978_ = v___x_2973_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_pos_2970_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_object* v_pos_2981_; lean_object* v_err_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec(v_res_2958_);
v_pos_2981_ = lean_ctor_get(v___x_2959_, 0);
v_err_2982_ = lean_ctor_get(v___x_2959_, 1);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2959_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_err_2982_);
lean_inc(v_pos_2981_);
lean_dec(v___x_2959_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_pos_2981_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_err_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___lam__0(lean_object* v___y_3008_){
_start:
{
lean_object* v_fst_3012_; lean_object* v_snd_3013_; lean_object* v___x_3014_; uint8_t v_decide_3015_; 
v_fst_3012_ = lean_ctor_get(v___y_3008_, 0);
v_snd_3013_ = lean_ctor_get(v___y_3008_, 1);
v___x_3014_ = lean_string_utf8_byte_size(v_fst_3012_);
v_decide_3015_ = lean_nat_dec_eq(v_snd_3013_, v___x_3014_);
if (v_decide_3015_ == 0)
{
uint32_t v_c_3016_; lean_object* v___x_3017_; lean_object* v_it_x27_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint32_t v___x_3021_; uint8_t v___x_3022_; 
v_c_3016_ = lean_string_utf8_get_fast(v_fst_3012_, v_snd_3013_);
v___x_3017_ = lean_string_utf8_next_fast(v_fst_3012_, v_snd_3013_);
lean_inc(v_fst_3012_);
v_it_x27_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3018_, 0, v_fst_3012_);
lean_ctor_set(v_it_x27_3018_, 1, v___x_3017_);
v___x_3019_ = lean_box_uint32(v_c_3016_);
v___x_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3020_, 0, v_it_x27_3018_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = 48;
v___x_3022_ = lean_uint32_dec_le(v___x_3021_, v_c_3016_);
if (v___x_3022_ == 0)
{
lean_dec_ref_known(v___x_3020_, 2);
goto v___jp_3009_;
}
else
{
uint32_t v___x_3023_; uint8_t v___x_3024_; 
v___x_3023_ = 57;
v___x_3024_ = lean_uint32_dec_le(v_c_3016_, v___x_3023_);
if (v___x_3024_ == 0)
{
lean_dec_ref_known(v___x_3020_, 2);
goto v___jp_3009_;
}
else
{
lean_dec_ref(v___y_3008_);
return v___x_3020_;
}
}
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_box(0);
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___y_3008_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
return v___x_3026_;
}
v___jp_3009_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___y_3008_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
return v___x_3011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object* v_size_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v___f_3030_; lean_object* v___x_3031_; 
v___f_3030_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3031_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3030_, v_size_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_pos_3032_; lean_object* v_res_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3044_; 
v_pos_3032_ = lean_ctor_get(v___x_3031_, 0);
v_res_3033_ = lean_ctor_get(v___x_3031_, 1);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3035_ = v___x_3031_;
v_isShared_3036_ = v_isSharedCheck_3044_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_res_3033_);
lean_inc(v_pos_3032_);
lean_dec(v___x_3031_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3044_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = lean_string_utf8_byte_size(v_res_3033_);
v___x_3039_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3039_, 0, v_res_3033_);
lean_ctor_set(v___x_3039_, 1, v___x_3037_);
lean_ctor_set(v___x_3039_, 2, v___x_3038_);
v___x_3040_ = l_String_Slice_toNat_x21(v___x_3039_);
lean_dec_ref_known(v___x_3039_, 3);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 1, v___x_3040_);
v___x_3042_ = v___x_3035_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_pos_3032_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
else
{
lean_object* v_pos_3045_; lean_object* v_err_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
v_pos_3045_ = lean_ctor_get(v___x_3031_, 0);
v_err_3046_ = lean_ctor_get(v___x_3031_, 1);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3031_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_err_3046_);
lean_inc(v_pos_3045_);
lean_dec(v___x_3031_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_pos_3045_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_err_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed(lean_object* v_size_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3054_, v_a_3055_);
lean_dec(v_size_3054_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object* v_acc_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_fst_3059_; lean_object* v_snd_3060_; lean_object* v_pos_3062_; lean_object* v_snd_3063_; lean_object* v_err_3064_; lean_object* v___x_3070_; uint8_t v_decide_3071_; 
v_fst_3059_ = lean_ctor_get(v_a_3058_, 0);
v_snd_3060_ = lean_ctor_get(v_a_3058_, 1);
lean_inc(v_snd_3060_);
v___x_3070_ = lean_string_utf8_byte_size(v_fst_3059_);
v_decide_3071_ = lean_nat_dec_eq(v_snd_3060_, v___x_3070_);
if (v_decide_3071_ == 0)
{
uint32_t v_c_3072_; uint32_t v___x_3073_; uint8_t v___x_3074_; 
v_c_3072_ = lean_string_utf8_get_fast(v_fst_3059_, v_snd_3060_);
v___x_3073_ = 48;
v___x_3074_ = lean_uint32_dec_le(v___x_3073_, v_c_3072_);
if (v___x_3074_ == 0)
{
goto v___jp_3068_;
}
else
{
uint32_t v___x_3075_; uint8_t v___x_3076_; 
v___x_3075_ = 57;
v___x_3076_ = lean_uint32_dec_le(v_c_3072_, v___x_3075_);
if (v___x_3076_ == 0)
{
goto v___jp_3068_;
}
else
{
lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3086_; 
lean_inc(v_fst_3059_);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_a_3058_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; lean_object* v_unused_3088_; 
v_unused_3087_ = lean_ctor_get(v_a_3058_, 1);
lean_dec(v_unused_3087_);
v_unused_3088_ = lean_ctor_get(v_a_3058_, 0);
lean_dec(v_unused_3088_);
v___x_3078_ = v_a_3058_;
v_isShared_3079_ = v_isSharedCheck_3086_;
goto v_resetjp_3077_;
}
else
{
lean_dec(v_a_3058_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3086_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v_it_x27_3082_; 
v___x_3080_ = lean_string_utf8_next_fast(v_fst_3059_, v_snd_3060_);
lean_dec(v_snd_3060_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v___x_3080_);
v_it_x27_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_fst_3059_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_3080_);
v_it_x27_3082_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_string_push(v_acc_3057_, v_c_3072_);
v_acc_3057_ = v___x_3083_;
v_a_3058_ = v_it_x27_3082_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_box(0);
lean_inc(v_snd_3060_);
v_pos_3062_ = v_a_3058_;
v_snd_3063_ = v_snd_3060_;
v_err_3064_ = v___x_3089_;
goto v___jp_3061_;
}
v___jp_3061_:
{
uint8_t v_decide_3065_; 
v_decide_3065_ = lean_nat_dec_eq(v_snd_3060_, v_snd_3063_);
lean_dec(v_snd_3063_);
lean_dec(v_snd_3060_);
if (v_decide_3065_ == 0)
{
lean_object* v___x_3066_; 
lean_dec_ref(v_acc_3057_);
lean_inc(v_err_3064_);
v___x_3066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3066_, 0, v_pos_3062_);
lean_ctor_set(v___x_3066_, 1, v_err_3064_);
return v___x_3066_;
}
else
{
lean_object* v___x_3067_; 
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v_pos_3062_);
lean_ctor_set(v___x_3067_, 1, v_acc_3057_);
return v___x_3067_;
}
}
v___jp_3068_:
{
lean_object* v___x_3069_; 
v___x_3069_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3060_);
v_pos_3062_ = v_a_3058_;
v_snd_3063_ = v_snd_3060_;
v_err_3064_ = v___x_3069_;
goto v___jp_3061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object* v_size_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v_pos_3093_; lean_object* v_res_3094_; lean_object* v___y_3101_; lean_object* v___f_3113_; lean_object* v___x_3114_; 
v___f_3113_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3114_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3113_, v_size_3090_, v_a_3091_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_pos_3115_; lean_object* v_res_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v_pos_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_pos_3115_);
v_res_3116_ = lean_ctor_get(v___x_3114_, 1);
lean_inc(v_res_3116_);
lean_dec_ref_known(v___x_3114_, 2);
v___x_3117_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3118_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(v___x_3117_, v_pos_3115_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_pos_3119_; lean_object* v_res_3120_; lean_object* v___x_3121_; 
v_pos_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_pos_3119_);
v_res_3120_ = lean_ctor_get(v___x_3118_, 1);
lean_inc(v_res_3120_);
lean_dec_ref_known(v___x_3118_, 2);
v___x_3121_ = lean_string_append(v_res_3116_, v_res_3120_);
lean_dec(v_res_3120_);
v_pos_3093_ = v_pos_3119_;
v_res_3094_ = v___x_3121_;
goto v___jp_3092_;
}
else
{
lean_dec(v_res_3116_);
v___y_3101_ = v___x_3118_;
goto v___jp_3100_;
}
}
else
{
v___y_3101_ = v___x_3114_;
goto v___jp_3100_;
}
v___jp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3095_ = lean_unsigned_to_nat(0u);
v___x_3096_ = lean_string_utf8_byte_size(v_res_3094_);
v___x_3097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3097_, 0, v_res_3094_);
lean_ctor_set(v___x_3097_, 1, v___x_3095_);
lean_ctor_set(v___x_3097_, 2, v___x_3096_);
v___x_3098_ = l_String_Slice_toNat_x21(v___x_3097_);
lean_dec_ref_known(v___x_3097_, 3);
v___x_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3099_, 0, v_pos_3093_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
return v___x_3099_;
}
v___jp_3100_:
{
if (lean_obj_tag(v___y_3101_) == 0)
{
lean_object* v_pos_3102_; lean_object* v_res_3103_; 
v_pos_3102_ = lean_ctor_get(v___y_3101_, 0);
lean_inc(v_pos_3102_);
v_res_3103_ = lean_ctor_get(v___y_3101_, 1);
lean_inc(v_res_3103_);
lean_dec_ref_known(v___y_3101_, 2);
v_pos_3093_ = v_pos_3102_;
v_res_3094_ = v_res_3103_;
goto v___jp_3092_;
}
else
{
lean_object* v_pos_3104_; lean_object* v_err_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
v_pos_3104_ = lean_ctor_get(v___y_3101_, 0);
v_err_3105_ = lean_ctor_get(v___y_3101_, 1);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___y_3101_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___y_3101_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_err_3105_);
lean_inc(v_pos_3104_);
lean_dec(v___y_3101_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_pos_3104_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_err_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object* v_size_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v_size_3122_, v_a_3123_);
lean_dec(v_size_3122_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object* v_size_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3127_ = lean_unsigned_to_nat(1u);
v___x_3128_ = lean_nat_dec_eq(v_size_3125_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; 
v___x_3129_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3125_, v_a_3126_);
return v___x_3129_;
}
else
{
lean_object* v___x_3130_; 
v___x_3130_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3127_, v_a_3126_);
return v___x_3130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed(lean_object* v_size_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_size_3131_, v_a_3132_);
lean_dec(v_size_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object* v_size_3134_, lean_object* v_pad_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_pos_3138_; lean_object* v_res_3139_; lean_object* v___f_3145_; lean_object* v___x_3146_; 
v___f_3145_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3146_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3145_, v_size_3134_, v_a_3136_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_pos_3147_; lean_object* v_res_3148_; uint32_t v___x_3149_; lean_object* v___x_3150_; 
v_pos_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_pos_3147_);
v_res_3148_ = lean_ctor_get(v___x_3146_, 1);
lean_inc(v_res_3148_);
lean_dec_ref_known(v___x_3146_, 2);
v___x_3149_ = 48;
v___x_3150_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_pad_3135_, v___x_3149_, v_res_3148_);
v_pos_3138_ = v_pos_3147_;
v_res_3139_ = v___x_3150_;
goto v___jp_3137_;
}
else
{
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_pos_3151_; lean_object* v_res_3152_; 
v_pos_3151_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_pos_3151_);
v_res_3152_ = lean_ctor_get(v___x_3146_, 1);
lean_inc(v_res_3152_);
lean_dec_ref_known(v___x_3146_, 2);
v_pos_3138_ = v_pos_3151_;
v_res_3139_ = v_res_3152_;
goto v___jp_3137_;
}
else
{
lean_object* v_pos_3153_; lean_object* v_err_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v_pos_3153_ = lean_ctor_get(v___x_3146_, 0);
v_err_3154_ = lean_ctor_get(v___x_3146_, 1);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3146_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_err_3154_);
lean_inc(v_pos_3153_);
lean_dec(v___x_3146_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_pos_3153_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_err_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object* v_size_3162_, lean_object* v_pad_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(v_size_3162_, v_pad_3163_, v_a_3164_);
lean_dec(v_pad_3163_);
lean_dec(v_size_3162_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object* v_acc_3166_, lean_object* v_a_3167_){
_start:
{
lean_object* v_fst_3168_; lean_object* v_snd_3169_; lean_object* v_pos_3171_; lean_object* v_snd_3172_; lean_object* v_err_3173_; lean_object* v___x_3177_; uint8_t v_decide_3178_; 
v_fst_3168_ = lean_ctor_get(v_a_3167_, 0);
v_snd_3169_ = lean_ctor_get(v_a_3167_, 1);
lean_inc(v_snd_3169_);
v___x_3177_ = lean_string_utf8_byte_size(v_fst_3168_);
v_decide_3178_ = lean_nat_dec_eq(v_snd_3169_, v___x_3177_);
if (v_decide_3178_ == 0)
{
uint32_t v_c_3179_; lean_object* v___x_3180_; lean_object* v_it_x27_3181_; uint8_t v___y_3186_; uint8_t v___y_3187_; uint8_t v___y_3190_; uint8_t v___y_3191_; uint8_t v___y_3192_; uint8_t v___y_3194_; uint8_t v___y_3195_; uint8_t v___y_3196_; uint8_t v___y_3197_; uint8_t v___y_3199_; uint8_t v___y_3200_; uint8_t v___y_3208_; uint8_t v___y_3214_; uint32_t v___x_3219_; uint8_t v___x_3220_; 
v_c_3179_ = lean_string_utf8_get_fast(v_fst_3168_, v_snd_3169_);
v___x_3180_ = lean_string_utf8_next_fast(v_fst_3168_, v_snd_3169_);
lean_inc(v_fst_3168_);
v_it_x27_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3181_, 0, v_fst_3168_);
lean_ctor_set(v_it_x27_3181_, 1, v___x_3180_);
v___x_3219_ = 65;
v___x_3220_ = lean_uint32_dec_le(v___x_3219_, v_c_3179_);
if (v___x_3220_ == 0)
{
v___y_3214_ = v___x_3220_;
goto v___jp_3213_;
}
else
{
uint32_t v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = 90;
v___x_3222_ = lean_uint32_dec_le(v_c_3179_, v___x_3221_);
v___y_3214_ = v___x_3222_;
goto v___jp_3213_;
}
v___jp_3182_:
{
lean_object* v___x_3183_; 
v___x_3183_ = lean_string_push(v_acc_3166_, v_c_3179_);
v_acc_3166_ = v___x_3183_;
v_a_3167_ = v_it_x27_3181_;
goto _start;
}
v___jp_3185_:
{
if (v___y_3186_ == 0)
{
if (v___y_3187_ == 0)
{
lean_object* v___x_3188_; 
lean_dec_ref_known(v_it_x27_3181_, 2);
v___x_3188_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3169_);
v_pos_3171_ = v_a_3167_;
v_snd_3172_ = v_snd_3169_;
v_err_3173_ = v___x_3188_;
goto v___jp_3170_;
}
else
{
lean_dec(v_snd_3169_);
lean_dec_ref(v_a_3167_);
goto v___jp_3182_;
}
}
else
{
lean_dec(v_snd_3169_);
lean_dec_ref(v_a_3167_);
goto v___jp_3182_;
}
}
v___jp_3189_:
{
if (v___y_3190_ == 0)
{
v___y_3186_ = v___y_3191_;
v___y_3187_ = v___y_3192_;
goto v___jp_3185_;
}
else
{
v___y_3186_ = v___y_3191_;
v___y_3187_ = v___y_3190_;
goto v___jp_3185_;
}
}
v___jp_3193_:
{
if (v___y_3195_ == 0)
{
v___y_3190_ = v___y_3194_;
v___y_3191_ = v___y_3196_;
v___y_3192_ = v___y_3197_;
goto v___jp_3189_;
}
else
{
v___y_3190_ = v___y_3194_;
v___y_3191_ = v___y_3196_;
v___y_3192_ = v___y_3195_;
goto v___jp_3189_;
}
}
v___jp_3198_:
{
uint32_t v___x_3201_; uint8_t v___x_3202_; uint32_t v___x_3203_; uint8_t v___x_3204_; 
v___x_3201_ = 95;
v___x_3202_ = lean_uint32_dec_eq(v_c_3179_, v___x_3201_);
v___x_3203_ = 45;
v___x_3204_ = lean_uint32_dec_eq(v_c_3179_, v___x_3203_);
if (v___x_3204_ == 0)
{
uint32_t v___x_3205_; uint8_t v___x_3206_; 
v___x_3205_ = 47;
v___x_3206_ = lean_uint32_dec_eq(v_c_3179_, v___x_3205_);
v___y_3194_ = v___y_3200_;
v___y_3195_ = v___x_3202_;
v___y_3196_ = v___y_3199_;
v___y_3197_ = v___x_3206_;
goto v___jp_3193_;
}
else
{
v___y_3194_ = v___y_3200_;
v___y_3195_ = v___x_3202_;
v___y_3196_ = v___y_3199_;
v___y_3197_ = v___x_3204_;
goto v___jp_3193_;
}
}
v___jp_3207_:
{
uint32_t v___x_3209_; uint8_t v___x_3210_; 
v___x_3209_ = 48;
v___x_3210_ = lean_uint32_dec_le(v___x_3209_, v_c_3179_);
if (v___x_3210_ == 0)
{
v___y_3199_ = v___y_3208_;
v___y_3200_ = v___x_3210_;
goto v___jp_3198_;
}
else
{
uint32_t v___x_3211_; uint8_t v___x_3212_; 
v___x_3211_ = 57;
v___x_3212_ = lean_uint32_dec_le(v_c_3179_, v___x_3211_);
v___y_3199_ = v___y_3208_;
v___y_3200_ = v___x_3212_;
goto v___jp_3198_;
}
}
v___jp_3213_:
{
if (v___y_3214_ == 0)
{
uint32_t v___x_3215_; uint8_t v___x_3216_; 
v___x_3215_ = 97;
v___x_3216_ = lean_uint32_dec_le(v___x_3215_, v_c_3179_);
if (v___x_3216_ == 0)
{
v___y_3208_ = v___x_3216_;
goto v___jp_3207_;
}
else
{
uint32_t v___x_3217_; uint8_t v___x_3218_; 
v___x_3217_ = 122;
v___x_3218_ = lean_uint32_dec_le(v_c_3179_, v___x_3217_);
v___y_3208_ = v___x_3218_;
goto v___jp_3207_;
}
}
else
{
v___y_3208_ = v___y_3214_;
goto v___jp_3207_;
}
}
}
else
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_box(0);
lean_inc(v_snd_3169_);
v_pos_3171_ = v_a_3167_;
v_snd_3172_ = v_snd_3169_;
v_err_3173_ = v___x_3223_;
goto v___jp_3170_;
}
v___jp_3170_:
{
uint8_t v_decide_3174_; 
v_decide_3174_ = lean_nat_dec_eq(v_snd_3169_, v_snd_3172_);
lean_dec(v_snd_3172_);
lean_dec(v_snd_3169_);
if (v_decide_3174_ == 0)
{
lean_object* v___x_3175_; 
lean_dec_ref(v_acc_3166_);
lean_inc(v_err_3173_);
v___x_3175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3175_, 0, v_pos_3171_);
lean_ctor_set(v___x_3175_, 1, v_err_3173_);
return v___x_3175_;
}
else
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v_pos_3171_);
lean_ctor_set(v___x_3176_, 1, v_acc_3166_);
return v___x_3176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object* v_acc_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v_fst_3226_; lean_object* v_snd_3227_; lean_object* v_pos_3229_; lean_object* v_snd_3230_; lean_object* v_err_3231_; lean_object* v___x_3235_; uint8_t v_decide_3236_; 
v_fst_3226_ = lean_ctor_get(v_a_3225_, 0);
v_snd_3227_ = lean_ctor_get(v_a_3225_, 1);
lean_inc(v_snd_3227_);
v___x_3235_ = lean_string_utf8_byte_size(v_fst_3226_);
v_decide_3236_ = lean_nat_dec_eq(v_snd_3227_, v___x_3235_);
if (v_decide_3236_ == 0)
{
uint32_t v_c_3237_; lean_object* v___x_3238_; lean_object* v_it_x27_3239_; uint8_t v___y_3244_; uint8_t v___y_3245_; uint8_t v___y_3248_; uint8_t v___y_3249_; uint8_t v___y_3250_; uint8_t v___y_3252_; uint8_t v___y_3253_; uint8_t v___y_3254_; uint8_t v___y_3255_; uint8_t v___y_3257_; uint8_t v___y_3258_; uint8_t v___y_3266_; uint8_t v___y_3272_; uint32_t v___x_3277_; uint8_t v___x_3278_; 
v_c_3237_ = lean_string_utf8_get_fast(v_fst_3226_, v_snd_3227_);
v___x_3238_ = lean_string_utf8_next_fast(v_fst_3226_, v_snd_3227_);
lean_inc(v_fst_3226_);
v_it_x27_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3239_, 0, v_fst_3226_);
lean_ctor_set(v_it_x27_3239_, 1, v___x_3238_);
v___x_3277_ = 65;
v___x_3278_ = lean_uint32_dec_le(v___x_3277_, v_c_3237_);
if (v___x_3278_ == 0)
{
v___y_3272_ = v___x_3278_;
goto v___jp_3271_;
}
else
{
uint32_t v___x_3279_; uint8_t v___x_3280_; 
v___x_3279_ = 90;
v___x_3280_ = lean_uint32_dec_le(v_c_3237_, v___x_3279_);
v___y_3272_ = v___x_3280_;
goto v___jp_3271_;
}
v___jp_3240_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_string_push(v_acc_3224_, v_c_3237_);
v___x_3242_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(v___x_3241_, v_it_x27_3239_);
return v___x_3242_;
}
v___jp_3243_:
{
if (v___y_3244_ == 0)
{
if (v___y_3245_ == 0)
{
lean_object* v___x_3246_; 
lean_dec_ref_known(v_it_x27_3239_, 2);
v___x_3246_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3227_);
v_pos_3229_ = v_a_3225_;
v_snd_3230_ = v_snd_3227_;
v_err_3231_ = v___x_3246_;
goto v___jp_3228_;
}
else
{
lean_dec(v_snd_3227_);
lean_dec_ref(v_a_3225_);
goto v___jp_3240_;
}
}
else
{
lean_dec(v_snd_3227_);
lean_dec_ref(v_a_3225_);
goto v___jp_3240_;
}
}
v___jp_3247_:
{
if (v___y_3248_ == 0)
{
v___y_3244_ = v___y_3249_;
v___y_3245_ = v___y_3250_;
goto v___jp_3243_;
}
else
{
v___y_3244_ = v___y_3249_;
v___y_3245_ = v___y_3248_;
goto v___jp_3243_;
}
}
v___jp_3251_:
{
if (v___y_3253_ == 0)
{
v___y_3248_ = v___y_3252_;
v___y_3249_ = v___y_3254_;
v___y_3250_ = v___y_3255_;
goto v___jp_3247_;
}
else
{
v___y_3248_ = v___y_3252_;
v___y_3249_ = v___y_3254_;
v___y_3250_ = v___y_3253_;
goto v___jp_3247_;
}
}
v___jp_3256_:
{
uint32_t v___x_3259_; uint8_t v___x_3260_; uint32_t v___x_3261_; uint8_t v___x_3262_; 
v___x_3259_ = 95;
v___x_3260_ = lean_uint32_dec_eq(v_c_3237_, v___x_3259_);
v___x_3261_ = 45;
v___x_3262_ = lean_uint32_dec_eq(v_c_3237_, v___x_3261_);
if (v___x_3262_ == 0)
{
uint32_t v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = 47;
v___x_3264_ = lean_uint32_dec_eq(v_c_3237_, v___x_3263_);
v___y_3252_ = v___y_3258_;
v___y_3253_ = v___x_3260_;
v___y_3254_ = v___y_3257_;
v___y_3255_ = v___x_3264_;
goto v___jp_3251_;
}
else
{
v___y_3252_ = v___y_3258_;
v___y_3253_ = v___x_3260_;
v___y_3254_ = v___y_3257_;
v___y_3255_ = v___x_3262_;
goto v___jp_3251_;
}
}
v___jp_3265_:
{
uint32_t v___x_3267_; uint8_t v___x_3268_; 
v___x_3267_ = 48;
v___x_3268_ = lean_uint32_dec_le(v___x_3267_, v_c_3237_);
if (v___x_3268_ == 0)
{
v___y_3257_ = v___y_3266_;
v___y_3258_ = v___x_3268_;
goto v___jp_3256_;
}
else
{
uint32_t v___x_3269_; uint8_t v___x_3270_; 
v___x_3269_ = 57;
v___x_3270_ = lean_uint32_dec_le(v_c_3237_, v___x_3269_);
v___y_3257_ = v___y_3266_;
v___y_3258_ = v___x_3270_;
goto v___jp_3256_;
}
}
v___jp_3271_:
{
if (v___y_3272_ == 0)
{
uint32_t v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = 97;
v___x_3274_ = lean_uint32_dec_le(v___x_3273_, v_c_3237_);
if (v___x_3274_ == 0)
{
v___y_3266_ = v___x_3274_;
goto v___jp_3265_;
}
else
{
uint32_t v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = 122;
v___x_3276_ = lean_uint32_dec_le(v_c_3237_, v___x_3275_);
v___y_3266_ = v___x_3276_;
goto v___jp_3265_;
}
}
else
{
v___y_3266_ = v___y_3272_;
goto v___jp_3265_;
}
}
}
else
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_box(0);
lean_inc(v_snd_3227_);
v_pos_3229_ = v_a_3225_;
v_snd_3230_ = v_snd_3227_;
v_err_3231_ = v___x_3281_;
goto v___jp_3228_;
}
v___jp_3228_:
{
uint8_t v_decide_3232_; 
v_decide_3232_ = lean_nat_dec_eq(v_snd_3227_, v_snd_3230_);
lean_dec(v_snd_3230_);
lean_dec(v_snd_3227_);
if (v_decide_3232_ == 0)
{
lean_object* v___x_3233_; 
lean_dec_ref(v_acc_3224_);
lean_inc(v_err_3231_);
v___x_3233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3233_, 0, v_pos_3229_);
lean_ctor_set(v___x_3233_, 1, v_err_3231_);
return v___x_3233_;
}
else
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v_pos_3229_);
lean_ctor_set(v___x_3234_, 1, v_acc_3224_);
return v___x_3234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object* v_a_3282_){
_start:
{
lean_object* v_fst_3283_; lean_object* v_snd_3284_; lean_object* v___x_3285_; uint8_t v_decide_3286_; 
v_fst_3283_ = lean_ctor_get(v_a_3282_, 0);
v_snd_3284_ = lean_ctor_get(v_a_3282_, 1);
v___x_3285_ = lean_string_utf8_byte_size(v_fst_3283_);
v_decide_3286_ = lean_nat_dec_eq(v_snd_3284_, v___x_3285_);
if (v_decide_3286_ == 0)
{
uint32_t v_c_3287_; lean_object* v___x_3288_; uint8_t v___y_3295_; uint8_t v___y_3296_; uint8_t v___y_3300_; uint8_t v___y_3301_; uint8_t v___y_3302_; uint8_t v___y_3304_; uint8_t v___y_3305_; uint8_t v___y_3306_; uint8_t v___y_3307_; uint8_t v___y_3309_; uint8_t v___y_3310_; uint8_t v___y_3318_; uint8_t v___y_3324_; uint32_t v___x_3329_; uint8_t v___x_3330_; 
v_c_3287_ = lean_string_utf8_get_fast(v_fst_3283_, v_snd_3284_);
v___x_3288_ = lean_string_utf8_next_fast(v_fst_3283_, v_snd_3284_);
v___x_3329_ = 65;
v___x_3330_ = lean_uint32_dec_le(v___x_3329_, v_c_3287_);
if (v___x_3330_ == 0)
{
v___y_3324_ = v___x_3330_;
goto v___jp_3323_;
}
else
{
uint32_t v___x_3331_; uint8_t v___x_3332_; 
v___x_3331_ = 90;
v___x_3332_ = lean_uint32_dec_le(v_c_3287_, v___x_3331_);
v___y_3324_ = v___x_3332_;
goto v___jp_3323_;
}
v___jp_3289_:
{
lean_object* v_it_x27_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_it_x27_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3290_, 0, v_fst_3283_);
lean_ctor_set(v_it_x27_3290_, 1, v___x_3288_);
v___x_3291_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3292_ = lean_string_push(v___x_3291_, v_c_3287_);
v___x_3293_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(v___x_3292_, v_it_x27_3290_);
return v___x_3293_;
}
v___jp_3294_:
{
if (v___y_3295_ == 0)
{
if (v___y_3296_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3298_, 0, v_a_3282_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
return v___x_3298_;
}
else
{
lean_inc(v_fst_3283_);
lean_dec_ref(v_a_3282_);
goto v___jp_3289_;
}
}
else
{
lean_inc(v_fst_3283_);
lean_dec_ref(v_a_3282_);
goto v___jp_3289_;
}
}
v___jp_3299_:
{
if (v___y_3301_ == 0)
{
v___y_3295_ = v___y_3300_;
v___y_3296_ = v___y_3302_;
goto v___jp_3294_;
}
else
{
v___y_3295_ = v___y_3300_;
v___y_3296_ = v___y_3301_;
goto v___jp_3294_;
}
}
v___jp_3303_:
{
if (v___y_3305_ == 0)
{
v___y_3300_ = v___y_3304_;
v___y_3301_ = v___y_3306_;
v___y_3302_ = v___y_3307_;
goto v___jp_3299_;
}
else
{
v___y_3300_ = v___y_3304_;
v___y_3301_ = v___y_3306_;
v___y_3302_ = v___y_3305_;
goto v___jp_3299_;
}
}
v___jp_3308_:
{
uint32_t v___x_3311_; uint8_t v___x_3312_; uint32_t v___x_3313_; uint8_t v___x_3314_; 
v___x_3311_ = 95;
v___x_3312_ = lean_uint32_dec_eq(v_c_3287_, v___x_3311_);
v___x_3313_ = 45;
v___x_3314_ = lean_uint32_dec_eq(v_c_3287_, v___x_3313_);
if (v___x_3314_ == 0)
{
uint32_t v___x_3315_; uint8_t v___x_3316_; 
v___x_3315_ = 47;
v___x_3316_ = lean_uint32_dec_eq(v_c_3287_, v___x_3315_);
v___y_3304_ = v___y_3309_;
v___y_3305_ = v___x_3312_;
v___y_3306_ = v___y_3310_;
v___y_3307_ = v___x_3316_;
goto v___jp_3303_;
}
else
{
v___y_3304_ = v___y_3309_;
v___y_3305_ = v___x_3312_;
v___y_3306_ = v___y_3310_;
v___y_3307_ = v___x_3314_;
goto v___jp_3303_;
}
}
v___jp_3317_:
{
uint32_t v___x_3319_; uint8_t v___x_3320_; 
v___x_3319_ = 48;
v___x_3320_ = lean_uint32_dec_le(v___x_3319_, v_c_3287_);
if (v___x_3320_ == 0)
{
v___y_3309_ = v___y_3318_;
v___y_3310_ = v___x_3320_;
goto v___jp_3308_;
}
else
{
uint32_t v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = 57;
v___x_3322_ = lean_uint32_dec_le(v_c_3287_, v___x_3321_);
v___y_3309_ = v___y_3318_;
v___y_3310_ = v___x_3322_;
goto v___jp_3308_;
}
}
v___jp_3323_:
{
if (v___y_3324_ == 0)
{
uint32_t v___x_3325_; uint8_t v___x_3326_; 
v___x_3325_ = 97;
v___x_3326_ = lean_uint32_dec_le(v___x_3325_, v_c_3287_);
if (v___x_3326_ == 0)
{
v___y_3318_ = v___x_3326_;
goto v___jp_3317_;
}
else
{
uint32_t v___x_3327_; uint8_t v___x_3328_; 
v___x_3327_ = 122;
v___x_3328_ = lean_uint32_dec_le(v_c_3287_, v___x_3327_);
v___y_3318_ = v___x_3328_;
goto v___jp_3317_;
}
}
else
{
v___y_3318_ = v___y_3324_;
goto v___jp_3317_;
}
}
}
else
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = lean_box(0);
v___x_3334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3334_, 0, v_a_3282_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
return v___x_3334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object* v_n_3337_, lean_object* v_m_3338_, lean_object* v_parser_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_apply_1(v_parser_3339_, v_a_3340_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_pos_3342_; lean_object* v_res_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3366_; 
v_pos_3342_ = lean_ctor_get(v___x_3341_, 0);
v_res_3343_ = lean_ctor_get(v___x_3341_, 1);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3345_ = v___x_3341_;
v_isShared_3346_ = v_isSharedCheck_3366_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_res_3343_);
lean_inc(v_pos_3342_);
lean_dec(v___x_3341_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3366_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
uint8_t v___y_3348_; uint8_t v___x_3364_; 
v___x_3364_ = lean_nat_dec_le(v_n_3337_, v_res_3343_);
if (v___x_3364_ == 0)
{
v___y_3348_ = v___x_3364_;
goto v___jp_3347_;
}
else
{
uint8_t v___x_3365_; 
v___x_3365_ = lean_nat_dec_le(v_res_3343_, v_m_3338_);
v___y_3348_ = v___x_3365_;
goto v___jp_3347_;
}
v___jp_3347_:
{
if (v___y_3348_ == 0)
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3358_; 
lean_dec(v_res_3343_);
v___x_3349_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0));
v___x_3350_ = l_Nat_reprFast(v_n_3337_);
v___x_3351_ = lean_string_append(v___x_3349_, v___x_3350_);
lean_dec_ref(v___x_3350_);
v___x_3352_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1));
v___x_3353_ = lean_string_append(v___x_3351_, v___x_3352_);
v___x_3354_ = l_Nat_reprFast(v_m_3338_);
v___x_3355_ = lean_string_append(v___x_3353_, v___x_3354_);
lean_dec_ref(v___x_3354_);
v___x_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set_tag(v___x_3345_, 1);
lean_ctor_set(v___x_3345_, 1, v___x_3356_);
v___x_3358_ = v___x_3345_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_pos_3342_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
else
{
lean_object* v___x_3360_; lean_object* v___x_3362_; 
lean_dec(v_m_3338_);
lean_dec(v_n_3337_);
v___x_3360_ = lean_nat_to_int(v_res_3343_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v___x_3360_);
v___x_3362_ = v___x_3345_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_pos_3342_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
else
{
lean_object* v_pos_3367_; lean_object* v_err_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec(v_m_3338_);
lean_dec(v_n_3337_);
v_pos_3367_ = lean_ctor_get(v___x_3341_, 0);
v_err_3368_ = lean_ctor_get(v___x_3341_, 1);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3341_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_err_3368_);
lean_inc(v_pos_3367_);
lean_dec(v___x_3341_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_pos_3367_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_err_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object* v_a_3376_){
_start:
{
lean_object* v_fst_3380_; lean_object* v_snd_3381_; lean_object* v___x_3382_; uint8_t v_decide_3383_; 
v_fst_3380_ = lean_ctor_get(v_a_3376_, 0);
v_snd_3381_ = lean_ctor_get(v_a_3376_, 1);
v___x_3382_ = lean_string_utf8_byte_size(v_fst_3380_);
v_decide_3383_ = lean_nat_dec_eq(v_snd_3381_, v___x_3382_);
if (v_decide_3383_ == 0)
{
uint32_t v_c_3384_; uint32_t v___x_3385_; uint8_t v___x_3386_; 
v_c_3384_ = lean_string_utf8_get_fast(v_fst_3380_, v_snd_3381_);
v___x_3385_ = 48;
v___x_3386_ = lean_uint32_dec_le(v___x_3385_, v_c_3384_);
if (v___x_3386_ == 0)
{
goto v___jp_3377_;
}
else
{
uint32_t v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = 57;
v___x_3388_ = lean_uint32_dec_le(v_c_3384_, v___x_3387_);
if (v___x_3388_ == 0)
{
goto v___jp_3377_;
}
else
{
lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3425_; 
lean_inc(v_snd_3381_);
lean_inc(v_fst_3380_);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_a_3376_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; lean_object* v_unused_3427_; 
v_unused_3426_ = lean_ctor_get(v_a_3376_, 1);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v_a_3376_, 0);
lean_dec(v_unused_3427_);
v___x_3390_ = v_a_3376_;
v_isShared_3391_ = v_isSharedCheck_3425_;
goto v_resetjp_3389_;
}
else
{
lean_dec(v_a_3376_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3425_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v_pos_3394_; lean_object* v_snd_3395_; lean_object* v_err_3396_; lean_object* v_it_x27_3404_; 
v___x_3392_ = lean_string_utf8_next_fast(v_fst_3380_, v_snd_3381_);
lean_dec(v_snd_3381_);
lean_inc(v_fst_3380_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 1, v___x_3392_);
v_it_x27_3404_ = v___x_3390_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_fst_3380_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v___x_3392_);
v_it_x27_3404_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3403_;
}
v___jp_3393_:
{
uint8_t v_decide_3397_; 
v_decide_3397_ = lean_nat_dec_eq(v___x_3392_, v_snd_3395_);
lean_dec(v_snd_3395_);
if (v_decide_3397_ == 0)
{
lean_object* v___x_3398_; 
lean_inc(v_err_3396_);
v___x_3398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3398_, 0, v_pos_3394_);
lean_ctor_set(v___x_3398_, 1, v_err_3396_);
return v___x_3398_;
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3399_ = lean_uint32_to_nat(v_c_3384_);
v___x_3400_ = lean_unsigned_to_nat(48u);
v___x_3401_ = lean_nat_sub(v___x_3399_, v___x_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v_pos_3394_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
return v___x_3402_;
}
}
v_reusejp_3403_:
{
uint8_t v_decide_3409_; 
v_decide_3409_ = lean_nat_dec_eq(v___x_3392_, v___x_3382_);
if (v_decide_3409_ == 0)
{
if (v___x_3388_ == 0)
{
lean_dec(v_fst_3380_);
goto v___jp_3407_;
}
else
{
uint32_t v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = lean_string_utf8_get_fast(v_fst_3380_, v___x_3392_);
v___x_3411_ = lean_uint32_dec_le(v___x_3385_, v___x_3410_);
if (v___x_3411_ == 0)
{
lean_dec(v_fst_3380_);
goto v___jp_3405_;
}
else
{
uint8_t v___x_3412_; 
v___x_3412_ = lean_uint32_dec_le(v___x_3410_, v___x_3387_);
if (v___x_3412_ == 0)
{
lean_dec(v_fst_3380_);
goto v___jp_3405_;
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec_ref(v_it_x27_3404_);
v___x_3413_ = lean_unsigned_to_nat(48u);
v___x_3414_ = lean_string_utf8_next_fast(v_fst_3380_, v___x_3392_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v_fst_3380_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = lean_uint32_to_nat(v_c_3384_);
v___x_3417_ = lean_nat_sub(v___x_3416_, v___x_3413_);
lean_dec(v___x_3416_);
v___x_3418_ = lean_unsigned_to_nat(10u);
v___x_3419_ = lean_nat_mul(v___x_3417_, v___x_3418_);
lean_dec(v___x_3417_);
v___x_3420_ = lean_uint32_to_nat(v___x_3410_);
v___x_3421_ = lean_nat_sub(v___x_3420_, v___x_3413_);
lean_dec(v___x_3420_);
v___x_3422_ = lean_nat_add(v___x_3419_, v___x_3421_);
lean_dec(v___x_3421_);
lean_dec(v___x_3419_);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3415_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
return v___x_3423_;
}
}
}
}
else
{
lean_dec(v_fst_3380_);
goto v___jp_3407_;
}
v___jp_3405_:
{
lean_object* v___x_3406_; 
v___x_3406_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v_pos_3394_ = v_it_x27_3404_;
v_snd_3395_ = v___x_3392_;
v_err_3396_ = v___x_3406_;
goto v___jp_3393_;
}
v___jp_3407_:
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_box(0);
v_pos_3394_ = v_it_x27_3404_;
v_snd_3395_ = v___x_3392_;
v_err_3396_ = v___x_3408_;
goto v___jp_3393_;
}
}
}
}
}
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_box(0);
v___x_3429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3429_, 0, v_a_3376_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
return v___x_3429_;
}
v___jp_3377_:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3379_, 0, v_a_3376_);
lean_ctor_set(v___x_3379_, 1, v___x_3378_);
return v___x_3379_;
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1(void){
_start:
{
uint32_t v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = 58;
v___x_3434_ = lean_box_uint32(v___x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(uint8_t v_withColon_3435_, lean_object* v___y_3436_){
_start:
{
if (v_withColon_3435_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___y_3436_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
return v___x_3438_;
}
else
{
lean_object* v_fst_3439_; lean_object* v_snd_3440_; lean_object* v___x_3441_; uint8_t v_decide_3442_; 
v_fst_3439_ = lean_ctor_get(v___y_3436_, 0);
v_snd_3440_ = lean_ctor_get(v___y_3436_, 1);
v___x_3441_ = lean_string_utf8_byte_size(v_fst_3439_);
v_decide_3442_ = lean_nat_dec_eq(v_snd_3440_, v___x_3441_);
if (v_decide_3442_ == 0)
{
uint32_t v___x_3443_; uint32_t v_c_3444_; uint8_t v___x_3445_; 
v___x_3443_ = 58;
v_c_3444_ = lean_string_utf8_get_fast(v_fst_3439_, v_snd_3440_);
v___x_3445_ = lean_uint32_dec_eq(v_c_3444_, v___x_3443_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1));
v___x_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___y_3436_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
return v___x_3447_;
}
else
{
lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3457_; 
lean_inc(v_snd_3440_);
lean_inc(v_fst_3439_);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___y_3436_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; lean_object* v_unused_3459_; 
v_unused_3458_ = lean_ctor_get(v___y_3436_, 1);
lean_dec(v_unused_3458_);
v_unused_3459_ = lean_ctor_get(v___y_3436_, 0);
lean_dec(v_unused_3459_);
v___x_3449_ = v___y_3436_;
v_isShared_3450_ = v_isSharedCheck_3457_;
goto v_resetjp_3448_;
}
else
{
lean_dec(v___y_3436_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3457_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v_it_x27_3453_; 
v___x_3451_ = lean_string_utf8_next_fast(v_fst_3439_, v_snd_3440_);
lean_dec(v_snd_3440_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 1, v___x_3451_);
v_it_x27_3453_ = v___x_3449_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_fst_3439_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v___x_3451_);
v_it_x27_3453_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3455_, 0, v_it_x27_3453_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
return v___x_3455_;
}
}
}
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = lean_box(0);
v___x_3461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___y_3436_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
return v___x_3461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed(lean_object* v_withColon_3462_, lean_object* v___y_3463_){
_start:
{
uint8_t v_withColon_boxed_3464_; lean_object* v_res_3465_; 
v_withColon_boxed_3464_ = lean_unbox(v_withColon_3462_);
v_res_3465_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(v_withColon_boxed_3464_, v___y_3463_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(lean_object* v_a_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = lean_nat_to_int(v_a_3466_);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___y_3467_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object* v___y_3470_, lean_object* v___f_3471_, lean_object* v_n_3472_, uint8_t v_reason_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_pos_3476_; lean_object* v_err_3477_; 
switch(v_reason_3473_)
{
case 0:
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_apply_1(v___y_3470_, v___y_3474_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_pos_3494_; lean_object* v___x_3495_; 
v_pos_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_pos_3494_);
lean_dec_ref_known(v___x_3493_, 2);
v___x_3495_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3494_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_pos_3496_; lean_object* v_res_3497_; lean_object* v___x_3498_; 
v_pos_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_pos_3496_);
v_res_3497_ = lean_ctor_get(v___x_3495_, 1);
lean_inc(v_res_3497_);
lean_dec_ref_known(v___x_3495_, 2);
v___x_3498_ = lean_apply_2(v___f_3471_, v_res_3497_, v_pos_3496_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_pos_3499_; lean_object* v_res_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3508_; 
v_pos_3499_ = lean_ctor_get(v___x_3498_, 0);
v_res_3500_ = lean_ctor_get(v___x_3498_, 1);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3502_ = v___x_3498_;
v_isShared_3503_ = v_isSharedCheck_3508_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_res_3500_);
lean_inc(v_pos_3499_);
lean_dec(v___x_3498_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3508_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v___x_3506_; 
v___x_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3504_, 0, v_res_3500_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v___x_3504_);
v___x_3506_ = v___x_3502_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_pos_3499_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
else
{
lean_object* v_pos_3509_; lean_object* v_err_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
v_pos_3509_ = lean_ctor_get(v___x_3498_, 0);
v_err_3510_ = lean_ctor_get(v___x_3498_, 1);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3498_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_err_3510_);
lean_inc(v_pos_3509_);
lean_dec(v___x_3498_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_pos_3509_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_err_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
lean_object* v_pos_3518_; lean_object* v_err_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec_ref(v___f_3471_);
v_pos_3518_ = lean_ctor_get(v___x_3495_, 0);
v_err_3519_ = lean_ctor_get(v___x_3495_, 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3495_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_err_3519_);
lean_inc(v_pos_3518_);
lean_dec(v___x_3495_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_pos_3518_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_err_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_object* v_pos_3527_; lean_object* v_err_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec_ref(v___f_3471_);
v_pos_3527_ = lean_ctor_get(v___x_3493_, 0);
v_err_3528_ = lean_ctor_get(v___x_3493_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3493_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_err_3528_);
lean_inc(v_pos_3527_);
lean_dec(v___x_3493_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_pos_3527_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_err_3528_);
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
case 1:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec_ref(v___f_3471_);
lean_dec_ref(v___y_3470_);
v___x_3536_ = lean_box(0);
v___x_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___y_3474_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
return v___x_3537_;
}
default: 
{
lean_object* v___x_3538_; 
lean_inc_ref(v___y_3474_);
v___x_3538_ = lean_apply_1(v___y_3470_, v___y_3474_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_pos_3539_; lean_object* v___x_3540_; 
v_pos_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_pos_3539_);
lean_dec_ref_known(v___x_3538_, 2);
v___x_3540_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3539_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_pos_3541_; lean_object* v_res_3542_; lean_object* v___x_3543_; 
v_pos_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_pos_3541_);
v_res_3542_ = lean_ctor_get(v___x_3540_, 1);
lean_inc(v_res_3542_);
lean_dec_ref_known(v___x_3540_, 2);
v___x_3543_ = lean_apply_2(v___f_3471_, v_res_3542_, v_pos_3541_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_pos_3544_; lean_object* v_res_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3553_; 
lean_dec_ref(v___y_3474_);
v_pos_3544_ = lean_ctor_get(v___x_3543_, 0);
v_res_3545_ = lean_ctor_get(v___x_3543_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3547_ = v___x_3543_;
v_isShared_3548_ = v_isSharedCheck_3553_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_res_3545_);
lean_inc(v_pos_3544_);
lean_dec(v___x_3543_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3553_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3549_, 0, v_res_3545_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 1, v___x_3549_);
v___x_3551_ = v___x_3547_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_pos_3544_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
else
{
lean_object* v_pos_3554_; lean_object* v_err_3555_; 
v_pos_3554_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_pos_3554_);
v_err_3555_ = lean_ctor_get(v___x_3543_, 1);
lean_inc(v_err_3555_);
lean_dec_ref_known(v___x_3543_, 2);
v_pos_3476_ = v_pos_3554_;
v_err_3477_ = v_err_3555_;
goto v___jp_3475_;
}
}
else
{
lean_object* v_pos_3556_; lean_object* v_err_3557_; 
lean_dec_ref(v___f_3471_);
v_pos_3556_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_pos_3556_);
v_err_3557_ = lean_ctor_get(v___x_3540_, 1);
lean_inc(v_err_3557_);
lean_dec_ref_known(v___x_3540_, 2);
v_pos_3476_ = v_pos_3556_;
v_err_3477_ = v_err_3557_;
goto v___jp_3475_;
}
}
else
{
lean_object* v_pos_3558_; lean_object* v_err_3559_; 
lean_dec_ref(v___f_3471_);
v_pos_3558_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_pos_3558_);
v_err_3559_ = lean_ctor_get(v___x_3538_, 1);
lean_inc(v_err_3559_);
lean_dec_ref_known(v___x_3538_, 2);
v_pos_3476_ = v_pos_3558_;
v_err_3477_ = v_err_3559_;
goto v___jp_3475_;
}
}
}
v___jp_3475_:
{
lean_object* v_snd_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3491_; 
v_snd_3478_ = lean_ctor_get(v___y_3474_, 1);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___y_3474_);
if (v_isSharedCheck_3491_ == 0)
{
lean_object* v_unused_3492_; 
v_unused_3492_ = lean_ctor_get(v___y_3474_, 0);
lean_dec(v_unused_3492_);
v___x_3480_ = v___y_3474_;
v_isShared_3481_ = v_isSharedCheck_3491_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_snd_3478_);
lean_dec(v___y_3474_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3491_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v_snd_3482_; uint8_t v_decide_3483_; 
v_snd_3482_ = lean_ctor_get(v_pos_3476_, 1);
v_decide_3483_ = lean_nat_dec_eq(v_snd_3478_, v_snd_3482_);
lean_dec(v_snd_3478_);
if (v_decide_3483_ == 0)
{
lean_object* v___x_3485_; 
if (v_isShared_3481_ == 0)
{
lean_ctor_set_tag(v___x_3480_, 1);
lean_ctor_set(v___x_3480_, 1, v_err_3477_);
lean_ctor_set(v___x_3480_, 0, v_pos_3476_);
v___x_3485_ = v___x_3480_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_pos_3476_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_err_3477_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3489_; 
lean_dec(v_err_3477_);
v___x_3487_ = lean_box(0);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 1, v___x_3487_);
lean_ctor_set(v___x_3480_, 0, v_pos_3476_);
v___x_3489_ = v___x_3480_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_pos_3476_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object* v___y_3560_, lean_object* v___f_3561_, lean_object* v_n_3562_, lean_object* v_reason_3563_, lean_object* v___y_3564_){
_start:
{
uint8_t v_reason_boxed_3565_; lean_object* v_res_3566_; 
v_reason_boxed_3565_ = lean_unbox(v_reason_3563_);
v_res_3566_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3560_, v___f_3561_, v_n_3562_, v_reason_boxed_3565_, v___y_3564_);
lean_dec_ref(v_n_3562_);
return v_res_3566_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = lean_unsigned_to_nat(3600u);
v___x_3568_ = lean_nat_to_int(v___x_3567_);
return v___x_3568_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = lean_unsigned_to_nat(1u);
v___x_3571_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3570_);
return v___x_3571_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = lean_unsigned_to_nat(59u);
v___x_3573_ = lean_nat_to_int(v___x_3572_);
return v___x_3573_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = lean_unsigned_to_nat(60u);
v___x_3577_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3576_);
return v___x_3577_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10(void){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = lean_unsigned_to_nat(23u);
v___x_3582_ = lean_nat_to_int(v___x_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t v_withMinutes_3589_, uint8_t v_withSeconds_3590_, uint8_t v_withColon_3591_, lean_object* v_a_3592_){
_start:
{
lean_object* v___y_3594_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v_fst_3628_; lean_object* v_snd_3629_; lean_object* v___x_3630_; lean_object* v___y_3631_; lean_object* v___f_3632_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; uint8_t v___y_3683_; lean_object* v_pos_3731_; lean_object* v_res_3732_; lean_object* v_pos_3751_; lean_object* v_fst_3752_; lean_object* v_snd_3753_; lean_object* v_err_3754_; lean_object* v___x_3767_; uint8_t v_decide_3768_; 
v_fst_3628_ = lean_ctor_get(v_a_3592_, 0);
lean_inc(v_fst_3628_);
v_snd_3629_ = lean_ctor_get(v_a_3592_, 1);
lean_inc(v_snd_3629_);
v___x_3630_ = lean_box(v_withColon_3591_);
v___y_3631_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed), 2, 1);
lean_closure_set(v___y_3631_, 0, v___x_3630_);
v___f_3632_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1));
v___x_3767_ = lean_string_utf8_byte_size(v_fst_3628_);
v_decide_3768_ = lean_nat_dec_eq(v_snd_3629_, v___x_3767_);
if (v_decide_3768_ == 0)
{
uint32_t v___x_3769_; uint32_t v_c_3770_; uint8_t v___x_3771_; 
v___x_3769_ = 43;
v_c_3770_ = lean_string_utf8_get_fast(v_fst_3628_, v_snd_3629_);
v___x_3771_ = lean_uint32_dec_eq(v_c_3770_, v___x_3769_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; 
v___x_3772_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14));
lean_inc(v_snd_3629_);
v_pos_3751_ = v_a_3592_;
v_fst_3752_ = v_fst_3628_;
v_snd_3753_ = v_snd_3629_;
v_err_3754_ = v___x_3772_;
goto v___jp_3750_;
}
else
{
lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3781_; 
v_isSharedCheck_3781_ = !lean_is_exclusive(v_a_3592_);
if (v_isSharedCheck_3781_ == 0)
{
lean_object* v_unused_3782_; lean_object* v_unused_3783_; 
v_unused_3782_ = lean_ctor_get(v_a_3592_, 1);
lean_dec(v_unused_3782_);
v_unused_3783_ = lean_ctor_get(v_a_3592_, 0);
lean_dec(v_unused_3783_);
v___x_3774_ = v_a_3592_;
v_isShared_3775_ = v_isSharedCheck_3781_;
goto v_resetjp_3773_;
}
else
{
lean_dec(v_a_3592_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3781_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; lean_object* v_it_x27_3778_; 
v___x_3776_ = lean_string_utf8_next_fast(v_fst_3628_, v_snd_3629_);
lean_dec(v_snd_3629_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 1, v___x_3776_);
v_it_x27_3778_ = v___x_3774_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_fst_3628_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v___x_3776_);
v_it_x27_3778_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v_pos_3731_ = v_it_x27_3778_;
v_res_3732_ = v___x_3779_;
goto v___jp_3730_;
}
}
}
}
else
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_box(0);
lean_inc(v_snd_3629_);
v_pos_3751_ = v_a_3592_;
v_fst_3752_ = v_fst_3628_;
v_snd_3753_ = v_snd_3629_;
v_err_3754_ = v___x_3784_;
goto v___jp_3750_;
}
v___jp_3593_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = lean_box(0);
v___x_3596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___y_3594_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
return v___x_3596_;
}
v___jp_3597_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3602_ = lean_int_add(v___y_3599_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec(v___y_3599_);
v___x_3603_ = lean_int_mul(v___x_3602_, v___y_3598_);
lean_dec(v___x_3602_);
v___x_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___y_3600_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
return v___x_3604_;
}
v___jp_3605_:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3613_ = lean_nat_to_int(v___y_3608_);
v___x_3614_ = lean_int_mul(v___y_3612_, v___x_3613_);
lean_dec(v___x_3613_);
lean_dec(v___y_3612_);
v___x_3615_ = lean_int_add(v___y_3609_, v___x_3614_);
lean_dec(v___x_3614_);
lean_dec(v___y_3609_);
if (lean_obj_tag(v___y_3607_) == 0)
{
lean_inc(v___y_3610_);
v___y_3598_ = v___y_3606_;
v___y_3599_ = v___x_3615_;
v___y_3600_ = v___y_3611_;
v___y_3601_ = v___y_3610_;
goto v___jp_3597_;
}
else
{
lean_object* v_val_3616_; 
v_val_3616_ = lean_ctor_get(v___y_3607_, 0);
lean_inc(v_val_3616_);
lean_dec_ref_known(v___y_3607_, 1);
v___y_3598_ = v___y_3606_;
v___y_3599_ = v___x_3615_;
v___y_3600_ = v___y_3611_;
v___y_3601_ = v_val_3616_;
goto v___jp_3597_;
}
}
v___jp_3617_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0);
v___x_3626_ = lean_int_mul(v___y_3620_, v___x_3625_);
lean_dec(v___y_3620_);
if (lean_obj_tag(v___y_3622_) == 0)
{
lean_inc(v___y_3623_);
v___y_3606_ = v___y_3618_;
v___y_3607_ = v___y_3619_;
v___y_3608_ = v___y_3621_;
v___y_3609_ = v___x_3626_;
v___y_3610_ = v___y_3623_;
v___y_3611_ = v___y_3624_;
v___y_3612_ = v___y_3623_;
goto v___jp_3605_;
}
else
{
lean_object* v_val_3627_; 
v_val_3627_ = lean_ctor_get(v___y_3622_, 0);
lean_inc(v_val_3627_);
lean_dec_ref_known(v___y_3622_, 1);
v___y_3606_ = v___y_3618_;
v___y_3607_ = v___y_3619_;
v___y_3608_ = v___y_3621_;
v___y_3609_ = v___x_3626_;
v___y_3610_ = v___y_3623_;
v___y_3611_ = v___y_3624_;
v___y_3612_ = v_val_3627_;
goto v___jp_3605_;
}
}
v___jp_3633_:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2);
v___x_3641_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3631_, v___f_3632_, v___x_3640_, v_withSeconds_3590_, v___y_3639_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_res_3642_; 
v_res_3642_ = lean_ctor_get(v___x_3641_, 1);
lean_inc(v_res_3642_);
if (lean_obj_tag(v_res_3642_) == 1)
{
lean_object* v_pos_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3666_; 
v_pos_3643_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3666_ == 0)
{
lean_object* v_unused_3667_; 
v_unused_3667_ = lean_ctor_get(v___x_3641_, 1);
lean_dec(v_unused_3667_);
v___x_3645_ = v___x_3641_;
v_isShared_3646_ = v_isSharedCheck_3666_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_pos_3643_);
lean_dec(v___x_3641_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3666_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v_val_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v_val_3647_ = lean_ctor_get(v_res_3642_, 0);
v___x_3648_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3);
v___x_3649_ = lean_int_dec_lt(v___x_3648_, v_val_3647_);
if (v___x_3649_ == 0)
{
lean_del_object(v___x_3645_);
v___y_3618_ = v___y_3634_;
v___y_3619_ = v_res_3642_;
v___y_3620_ = v___y_3635_;
v___y_3621_ = v___y_3636_;
v___y_3622_ = v___y_3638_;
v___y_3623_ = v___y_3637_;
v___y_3624_ = v_pos_3643_;
goto v___jp_3617_;
}
else
{
lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3664_; 
lean_inc(v_val_3647_);
lean_dec(v___y_3638_);
lean_dec(v___y_3636_);
lean_dec(v___y_3635_);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_res_3642_);
if (v_isSharedCheck_3664_ == 0)
{
lean_object* v_unused_3665_; 
v_unused_3665_ = lean_ctor_get(v_res_3642_, 0);
lean_dec(v_unused_3665_);
v___x_3651_ = v_res_3642_;
v_isShared_3652_ = v_isSharedCheck_3664_;
goto v_resetjp_3650_;
}
else
{
lean_dec(v_res_3642_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3664_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3659_; 
v___x_3653_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4));
v___x_3654_ = l_Int_repr(v_val_3647_);
lean_dec(v_val_3647_);
v___x_3655_ = lean_string_append(v___x_3653_, v___x_3654_);
lean_dec_ref(v___x_3654_);
v___x_3656_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5));
v___x_3657_ = lean_string_append(v___x_3655_, v___x_3656_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v___x_3657_);
v___x_3659_ = v___x_3651_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3661_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 1, v___x_3659_);
v___x_3661_ = v___x_3645_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_pos_3643_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3668_; 
v_pos_3668_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_pos_3668_);
lean_dec_ref_known(v___x_3641_, 2);
v___y_3618_ = v___y_3634_;
v___y_3619_ = v_res_3642_;
v___y_3620_ = v___y_3635_;
v___y_3621_ = v___y_3636_;
v___y_3622_ = v___y_3638_;
v___y_3623_ = v___y_3637_;
v___y_3624_ = v_pos_3668_;
goto v___jp_3617_;
}
}
else
{
lean_object* v_pos_3669_; lean_object* v_err_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v___y_3638_);
lean_dec(v___y_3636_);
lean_dec(v___y_3635_);
v_pos_3669_ = lean_ctor_get(v___x_3641_, 0);
v_err_3670_ = lean_ctor_get(v___x_3641_, 1);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3641_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_err_3670_);
lean_inc(v_pos_3669_);
lean_dec(v___x_3641_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_pos_3669_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_err_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
v___jp_3678_:
{
if (v___y_3683_ == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3684_ = lean_unsigned_to_nat(60u);
v___x_3685_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6);
lean_inc_ref(v___y_3631_);
v___x_3686_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3631_, v___f_3632_, v___x_3685_, v_withMinutes_3589_, v___y_3681_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_res_3687_; 
v_res_3687_ = lean_ctor_get(v___x_3686_, 1);
lean_inc(v_res_3687_);
if (lean_obj_tag(v_res_3687_) == 1)
{
lean_object* v_pos_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3711_; 
v_pos_3688_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; 
v_unused_3712_ = lean_ctor_get(v___x_3686_, 1);
lean_dec(v_unused_3712_);
v___x_3690_ = v___x_3686_;
v_isShared_3691_ = v_isSharedCheck_3711_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_pos_3688_);
lean_dec(v___x_3686_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3711_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v_val_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v_val_3692_ = lean_ctor_get(v_res_3687_, 0);
v___x_3693_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3);
v___x_3694_ = lean_int_dec_lt(v___x_3693_, v_val_3692_);
if (v___x_3694_ == 0)
{
lean_del_object(v___x_3690_);
v___y_3634_ = v___y_3679_;
v___y_3635_ = v___y_3680_;
v___y_3636_ = v___x_3684_;
v___y_3637_ = v___y_3682_;
v___y_3638_ = v_res_3687_;
v___y_3639_ = v_pos_3688_;
goto v___jp_3633_;
}
else
{
lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3709_; 
lean_inc(v_val_3692_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3631_);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_res_3687_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v_res_3687_, 0);
lean_dec(v_unused_3710_);
v___x_3696_ = v_res_3687_;
v_isShared_3697_ = v_isSharedCheck_3709_;
goto v_resetjp_3695_;
}
else
{
lean_dec(v_res_3687_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3709_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3698_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3699_ = l_Int_repr(v_val_3692_);
lean_dec(v_val_3692_);
v___x_3700_ = lean_string_append(v___x_3698_, v___x_3699_);
lean_dec_ref(v___x_3699_);
v___x_3701_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5));
v___x_3702_ = lean_string_append(v___x_3700_, v___x_3701_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v___x_3702_);
v___x_3704_ = v___x_3696_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3706_; 
if (v_isShared_3691_ == 0)
{
lean_ctor_set_tag(v___x_3690_, 1);
lean_ctor_set(v___x_3690_, 1, v___x_3704_);
v___x_3706_ = v___x_3690_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_pos_3688_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v___x_3704_);
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
}
}
else
{
lean_object* v_pos_3713_; 
v_pos_3713_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_pos_3713_);
lean_dec_ref_known(v___x_3686_, 2);
v___y_3634_ = v___y_3679_;
v___y_3635_ = v___y_3680_;
v___y_3636_ = v___x_3684_;
v___y_3637_ = v___y_3682_;
v___y_3638_ = v_res_3687_;
v___y_3639_ = v_pos_3713_;
goto v___jp_3633_;
}
}
else
{
lean_object* v_pos_3714_; lean_object* v_err_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3631_);
v_pos_3714_ = lean_ctor_get(v___x_3686_, 0);
v_err_3715_ = lean_ctor_get(v___x_3686_, 1);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3686_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_err_3715_);
lean_inc(v_pos_3714_);
lean_dec(v___x_3686_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_pos_3714_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_err_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
else
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
lean_dec_ref(v___y_3631_);
v___x_3723_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8));
v___x_3724_ = l_Int_repr(v___y_3680_);
lean_dec(v___y_3680_);
v___x_3725_ = lean_string_append(v___x_3723_, v___x_3724_);
lean_dec_ref(v___x_3724_);
v___x_3726_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9));
v___x_3727_ = lean_string_append(v___x_3725_, v___x_3726_);
v___x_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
v___x_3729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___y_3681_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
return v___x_3729_;
}
}
v___jp_3730_:
{
lean_object* v___x_3733_; 
v___x_3733_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3731_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_pos_3734_; lean_object* v_res_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; uint8_t v___x_3738_; 
v_pos_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_pos_3734_);
v_res_3735_ = lean_ctor_get(v___x_3733_, 1);
lean_inc(v_res_3735_);
lean_dec_ref_known(v___x_3733_, 2);
v___x_3736_ = lean_nat_to_int(v_res_3735_);
v___x_3737_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_3738_ = lean_int_dec_lt(v___x_3736_, v___x_3737_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3739_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10);
v___x_3740_ = lean_int_dec_lt(v___x_3739_, v___x_3736_);
v___y_3679_ = v_res_3732_;
v___y_3680_ = v___x_3736_;
v___y_3681_ = v_pos_3734_;
v___y_3682_ = v___x_3737_;
v___y_3683_ = v___x_3740_;
goto v___jp_3678_;
}
else
{
v___y_3679_ = v_res_3732_;
v___y_3680_ = v___x_3736_;
v___y_3681_ = v_pos_3734_;
v___y_3682_ = v___x_3737_;
v___y_3683_ = v___x_3738_;
goto v___jp_3678_;
}
}
else
{
lean_object* v_pos_3741_; lean_object* v_err_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec_ref(v___y_3631_);
v_pos_3741_ = lean_ctor_get(v___x_3733_, 0);
v_err_3742_ = lean_ctor_get(v___x_3733_, 1);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3733_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_err_3742_);
lean_inc(v_pos_3741_);
lean_dec(v___x_3733_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_pos_3741_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_err_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
v___jp_3750_:
{
uint8_t v_decide_3755_; 
v_decide_3755_ = lean_nat_dec_eq(v_snd_3629_, v_snd_3753_);
lean_dec(v_snd_3629_);
if (v_decide_3755_ == 0)
{
lean_object* v___x_3756_; 
lean_dec(v_snd_3753_);
lean_dec(v_fst_3752_);
lean_dec_ref(v___y_3631_);
lean_inc(v_err_3754_);
v___x_3756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3756_, 0, v_pos_3751_);
lean_ctor_set(v___x_3756_, 1, v_err_3754_);
return v___x_3756_;
}
else
{
lean_object* v___x_3757_; uint8_t v_decide_3758_; 
v___x_3757_ = lean_string_utf8_byte_size(v_fst_3752_);
v_decide_3758_ = lean_nat_dec_eq(v_snd_3753_, v___x_3757_);
if (v_decide_3758_ == 0)
{
if (v_decide_3755_ == 0)
{
lean_dec(v_snd_3753_);
lean_dec(v_fst_3752_);
lean_dec_ref(v___y_3631_);
v___y_3594_ = v_pos_3751_;
goto v___jp_3593_;
}
else
{
uint32_t v___x_3759_; uint32_t v_c_3760_; uint8_t v___x_3761_; 
v___x_3759_ = 45;
v_c_3760_ = lean_string_utf8_get_fast(v_fst_3752_, v_snd_3753_);
v___x_3761_ = lean_uint32_dec_eq(v_c_3760_, v___x_3759_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_dec(v_snd_3753_);
lean_dec(v_fst_3752_);
lean_dec_ref(v___y_3631_);
v___x_3762_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12));
v___x_3763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3763_, 0, v_pos_3751_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
return v___x_3763_;
}
else
{
lean_object* v___x_3764_; lean_object* v_it_x27_3765_; lean_object* v___x_3766_; 
lean_dec_ref(v_pos_3751_);
v___x_3764_ = lean_string_utf8_next_fast(v_fst_3752_, v_snd_3753_);
lean_dec(v_snd_3753_);
v_it_x27_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3765_, 0, v_fst_3752_);
lean_ctor_set(v_it_x27_3765_, 1, v___x_3764_);
v___x_3766_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v_pos_3731_ = v_it_x27_3765_;
v_res_3732_ = v___x_3766_;
goto v___jp_3730_;
}
}
}
else
{
lean_dec(v_snd_3753_);
lean_dec(v_fst_3752_);
lean_dec_ref(v___y_3631_);
v___y_3594_ = v_pos_3751_;
goto v___jp_3593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object* v_withMinutes_3785_, lean_object* v_withSeconds_3786_, lean_object* v_withColon_3787_, lean_object* v_a_3788_){
_start:
{
uint8_t v_withMinutes_boxed_3789_; uint8_t v_withSeconds_boxed_3790_; uint8_t v_withColon_boxed_3791_; lean_object* v_res_3792_; 
v_withMinutes_boxed_3789_ = lean_unbox(v_withMinutes_3785_);
v_withSeconds_boxed_3790_ = lean_unbox(v_withSeconds_3786_);
v_withColon_boxed_3791_ = lean_unbox(v_withColon_3787_);
v_res_3792_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_withMinutes_boxed_3789_, v_withSeconds_boxed_3790_, v_withColon_boxed_3791_, v_a_3788_);
return v_res_3792_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = lean_unsigned_to_nat(2000u);
v___x_3796_ = lean_nat_to_int(v___x_3795_);
return v___x_3796_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5(void){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3802_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3803_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3804_ = lean_int_sub(v___x_3803_, v___x_3802_);
return v___x_3804_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6(void){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v_range_3807_; 
v___x_3805_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3806_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5);
v_range_3807_ = lean_int_add(v___x_3806_, v___x_3805_);
return v_range_3807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object* v_config_3810_, lean_object* v_x_3811_, lean_object* v_a_3812_){
_start:
{
lean_object* v___y_3814_; lean_object* v___y_3819_; lean_object* v___y_3824_; 
switch(lean_obj_tag(v_x_3811_))
{
case 0:
{
uint8_t v_presentation_3850_; 
v_presentation_3850_ = lean_ctor_get_uint8(v_x_3811_, 0);
lean_dec_ref_known(v_x_3811_, 0);
switch(v_presentation_3850_)
{
case 1:
{
lean_object* v_dateformat_3851_; lean_object* v_symbols_3852_; lean_object* v___x_3853_; 
v_dateformat_3851_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_3851_);
lean_dec_ref(v_config_3810_);
v_symbols_3852_ = lean_ctor_get(v_dateformat_3851_, 1);
lean_inc_ref(v_symbols_3852_);
lean_dec_ref(v_dateformat_3851_);
v___x_3853_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(v_symbols_3852_, v_a_3812_);
return v___x_3853_;
}
case 2:
{
lean_object* v_dateformat_3854_; lean_object* v_symbols_3855_; lean_object* v___x_3856_; 
v_dateformat_3854_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_3854_);
lean_dec_ref(v_config_3810_);
v_symbols_3855_ = lean_ctor_get(v_dateformat_3854_, 1);
lean_inc_ref(v_symbols_3855_);
lean_dec_ref(v_dateformat_3854_);
v___x_3856_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(v_symbols_3855_, v_a_3812_);
return v___x_3856_;
}
default: 
{
lean_object* v_dateformat_3857_; lean_object* v_symbols_3858_; lean_object* v___x_3859_; 
v_dateformat_3857_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_3857_);
lean_dec_ref(v_config_3810_);
v_symbols_3858_ = lean_ctor_get(v_dateformat_3857_, 1);
lean_inc_ref(v_symbols_3858_);
lean_dec_ref(v_dateformat_3857_);
v___x_3859_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(v_symbols_3858_, v_a_3812_);
return v___x_3859_;
}
}
}
case 1:
{
lean_object* v_presentation_3860_; 
lean_dec_ref(v_config_3810_);
v_presentation_3860_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_3860_);
lean_dec_ref_known(v_x_3811_, 1);
switch(lean_obj_tag(v_presentation_3860_))
{
case 0:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_3862_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3861_, v_a_3812_);
return v___x_3862_;
}
case 1:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = lean_unsigned_to_nat(2u);
v___x_3864_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3863_, v_a_3812_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_pos_3865_; lean_object* v_res_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3876_; 
v_pos_3865_ = lean_ctor_get(v___x_3864_, 0);
v_res_3866_ = lean_ctor_get(v___x_3864_, 1);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3868_ = v___x_3864_;
v_isShared_3869_ = v_isSharedCheck_3876_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_res_3866_);
lean_inc(v_pos_3865_);
lean_dec(v___x_3864_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3876_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3874_; 
v___x_3870_ = lean_nat_to_int(v_res_3866_);
v___x_3871_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3872_ = lean_int_add(v___x_3871_, v___x_3870_);
lean_dec(v___x_3870_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 1, v___x_3872_);
v___x_3874_ = v___x_3868_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_pos_3865_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
else
{
lean_object* v_pos_3877_; lean_object* v_err_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
v_pos_3877_ = lean_ctor_get(v___x_3864_, 0);
v_err_3878_ = lean_ctor_get(v___x_3864_, 1);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3864_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_err_3878_);
lean_inc(v_pos_3877_);
lean_dec(v___x_3864_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_pos_3877_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_err_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
case 2:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_3887_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3886_, v_a_3812_);
return v___x_3887_;
}
default: 
{
lean_object* v_num_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v_num_3888_ = lean_ctor_get(v_presentation_3860_, 0);
lean_inc(v_num_3888_);
lean_dec_ref_known(v_presentation_3860_, 1);
v___x_3889_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_3889_, 0, v_num_3888_);
v___x_3890_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3889_, v_a_3812_);
return v___x_3890_;
}
}
}
case 2:
{
lean_object* v_presentation_3891_; 
lean_dec_ref(v_config_3810_);
v_presentation_3891_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_3891_);
lean_dec_ref_known(v_x_3811_, 1);
switch(lean_obj_tag(v_presentation_3891_))
{
case 0:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = lean_unsigned_to_nat(1u);
v___x_3893_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3892_, v_a_3812_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_pos_3894_; lean_object* v_res_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3903_; 
v_pos_3894_ = lean_ctor_get(v___x_3893_, 0);
v_res_3895_ = lean_ctor_get(v___x_3893_, 1);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3897_ = v___x_3893_;
v_isShared_3898_ = v_isSharedCheck_3903_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_res_3895_);
lean_inc(v_pos_3894_);
lean_dec(v___x_3893_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3903_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3899_; lean_object* v___x_3901_; 
v___x_3899_ = lean_nat_to_int(v_res_3895_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 1, v___x_3899_);
v___x_3901_ = v___x_3897_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_pos_3894_);
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
v_pos_3904_ = lean_ctor_get(v___x_3893_, 0);
v_err_3905_ = lean_ctor_get(v___x_3893_, 1);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3893_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_err_3905_);
lean_inc(v_pos_3904_);
lean_dec(v___x_3893_);
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
case 1:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = lean_unsigned_to_nat(2u);
v___x_3914_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3913_, v_a_3812_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_pos_3915_; lean_object* v_res_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3926_; 
v_pos_3915_ = lean_ctor_get(v___x_3914_, 0);
v_res_3916_ = lean_ctor_get(v___x_3914_, 1);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3918_ = v___x_3914_;
v_isShared_3919_ = v_isSharedCheck_3926_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_res_3916_);
lean_inc(v_pos_3915_);
lean_dec(v___x_3914_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3926_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3924_; 
v___x_3920_ = lean_nat_to_int(v_res_3916_);
v___x_3921_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3922_ = lean_int_add(v___x_3921_, v___x_3920_);
lean_dec(v___x_3920_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 1, v___x_3922_);
v___x_3924_ = v___x_3918_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_pos_3915_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v___x_3922_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
else
{
lean_object* v_pos_3927_; lean_object* v_err_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
v_pos_3927_ = lean_ctor_get(v___x_3914_, 0);
v_err_3928_ = lean_ctor_get(v___x_3914_, 1);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3914_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_err_3928_);
lean_inc(v_pos_3927_);
lean_dec(v___x_3914_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_pos_3927_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_err_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
case 2:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = lean_unsigned_to_nat(4u);
v___x_3937_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3936_, v_a_3812_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_pos_3938_; lean_object* v_res_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3947_; 
v_pos_3938_ = lean_ctor_get(v___x_3937_, 0);
v_res_3939_ = lean_ctor_get(v___x_3937_, 1);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3941_ = v___x_3937_;
v_isShared_3942_ = v_isSharedCheck_3947_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_res_3939_);
lean_inc(v_pos_3938_);
lean_dec(v___x_3937_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3947_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3943_ = lean_nat_to_int(v_res_3939_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 1, v___x_3943_);
v___x_3945_ = v___x_3941_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_pos_3938_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v___x_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
else
{
lean_object* v_pos_3948_; lean_object* v_err_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
v_pos_3948_ = lean_ctor_get(v___x_3937_, 0);
v_err_3949_ = lean_ctor_get(v___x_3937_, 1);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3937_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_err_3949_);
lean_inc(v_pos_3948_);
lean_dec(v___x_3937_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_pos_3948_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_err_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
default: 
{
lean_object* v_num_3957_; lean_object* v___x_3958_; 
v_num_3957_ = lean_ctor_get(v_presentation_3891_, 0);
lean_inc(v_num_3957_);
lean_dec_ref_known(v_presentation_3891_, 1);
v___x_3958_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_num_3957_, v_a_3812_);
lean_dec(v_num_3957_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_pos_3959_; lean_object* v_res_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3968_; 
v_pos_3959_ = lean_ctor_get(v___x_3958_, 0);
v_res_3960_ = lean_ctor_get(v___x_3958_, 1);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3962_ = v___x_3958_;
v_isShared_3963_ = v_isSharedCheck_3968_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_res_3960_);
lean_inc(v_pos_3959_);
lean_dec(v___x_3958_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3968_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3964_; lean_object* v___x_3966_; 
v___x_3964_ = lean_nat_to_int(v_res_3960_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 1, v___x_3964_);
v___x_3966_ = v___x_3962_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_pos_3959_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
else
{
lean_object* v_pos_3969_; lean_object* v_err_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
v_pos_3969_ = lean_ctor_get(v___x_3958_, 0);
v_err_3970_ = lean_ctor_get(v___x_3958_, 1);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3958_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_err_3970_);
lean_inc(v_pos_3969_);
lean_dec(v___x_3958_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_pos_3969_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v_err_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
}
}
case 3:
{
lean_object* v_presentation_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_dec_ref(v_config_3810_);
v_presentation_3978_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_3978_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_3979_ = lean_unsigned_to_nat(1u);
v___x_3980_ = lean_unsigned_to_nat(366u);
v___x_3981_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3981_, 0, v_presentation_3978_);
v___x_3982_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3979_, v___x_3980_, v___x_3981_, v_a_3812_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_pos_3983_; lean_object* v_res_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3994_; 
v_pos_3983_ = lean_ctor_get(v___x_3982_, 0);
v_res_3984_ = lean_ctor_get(v___x_3982_, 1);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3986_ = v___x_3982_;
v_isShared_3987_ = v_isSharedCheck_3994_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_res_3984_);
lean_inc(v_pos_3983_);
lean_dec(v___x_3982_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3994_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
uint8_t v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3988_ = 1;
v___x_3989_ = lean_box(v___x_3988_);
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
lean_ctor_set(v___x_3990_, 1, v_res_3984_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 1, v___x_3990_);
v___x_3992_ = v___x_3986_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_pos_3983_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
else
{
lean_object* v_pos_3995_; lean_object* v_err_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
v_pos_3995_ = lean_ctor_get(v___x_3982_, 0);
v_err_3996_ = lean_ctor_get(v___x_3982_, 1);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3982_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_err_3996_);
lean_inc(v_pos_3995_);
lean_dec(v___x_3982_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_pos_3995_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v_err_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
case 4:
{
lean_object* v_presentation_4004_; 
v_presentation_4004_ = lean_ctor_get(v_x_3811_, 0);
lean_inc_ref(v_presentation_4004_);
lean_dec_ref_known(v_x_3811_, 1);
if (lean_obj_tag(v_presentation_4004_) == 0)
{
lean_object* v_val_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_dec_ref(v_config_3810_);
v_val_4005_ = lean_ctor_get(v_presentation_4004_, 0);
lean_inc(v_val_4005_);
lean_dec_ref_known(v_presentation_4004_, 1);
v___x_4006_ = lean_unsigned_to_nat(1u);
v___x_4007_ = lean_unsigned_to_nat(12u);
v___x_4008_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4008_, 0, v_val_4005_);
v___x_4009_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4006_, v___x_4007_, v___x_4008_, v_a_3812_);
return v___x_4009_;
}
else
{
lean_object* v_val_4010_; uint8_t v___x_4011_; 
v_val_4010_ = lean_ctor_get(v_presentation_4004_, 0);
lean_inc(v_val_4010_);
lean_dec_ref_known(v_presentation_4004_, 1);
v___x_4011_ = lean_unbox(v_val_4010_);
lean_dec(v_val_4010_);
switch(v___x_4011_)
{
case 1:
{
lean_object* v_dateformat_4012_; lean_object* v_symbols_4013_; lean_object* v___x_4014_; 
v_dateformat_4012_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4012_);
lean_dec_ref(v_config_3810_);
v_symbols_4013_ = lean_ctor_get(v_dateformat_4012_, 1);
lean_inc_ref(v_symbols_4013_);
lean_dec_ref(v_dateformat_4012_);
v___x_4014_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_4013_, v_a_3812_);
return v___x_4014_;
}
case 2:
{
lean_object* v_dateformat_4015_; lean_object* v_symbols_4016_; lean_object* v___x_4017_; 
v_dateformat_4015_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4015_);
lean_dec_ref(v_config_3810_);
v_symbols_4016_ = lean_ctor_get(v_dateformat_4015_, 1);
lean_inc_ref(v_symbols_4016_);
lean_dec_ref(v_dateformat_4015_);
v___x_4017_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_4016_, v_a_3812_);
return v___x_4017_;
}
default: 
{
lean_object* v_dateformat_4018_; lean_object* v_symbols_4019_; lean_object* v___x_4020_; 
v_dateformat_4018_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4018_);
lean_dec_ref(v_config_3810_);
v_symbols_4019_ = lean_ctor_get(v_dateformat_4018_, 1);
lean_inc_ref(v_symbols_4019_);
lean_dec_ref(v_dateformat_4018_);
v___x_4020_ = l_Std_Time_parseMonthShort(v_symbols_4019_, v_a_3812_);
return v___x_4020_;
}
}
}
}
case 5:
{
lean_object* v_presentation_4021_; 
v_presentation_4021_ = lean_ctor_get(v_x_3811_, 0);
lean_inc_ref(v_presentation_4021_);
lean_dec_ref_known(v_x_3811_, 1);
if (lean_obj_tag(v_presentation_4021_) == 0)
{
lean_object* v_val_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
lean_dec_ref(v_config_3810_);
v_val_4022_ = lean_ctor_get(v_presentation_4021_, 0);
lean_inc(v_val_4022_);
lean_dec_ref_known(v_presentation_4021_, 1);
v___x_4023_ = lean_unsigned_to_nat(1u);
v___x_4024_ = lean_unsigned_to_nat(12u);
v___x_4025_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4025_, 0, v_val_4022_);
v___x_4026_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4023_, v___x_4024_, v___x_4025_, v_a_3812_);
return v___x_4026_;
}
else
{
lean_object* v_val_4027_; uint8_t v___x_4028_; 
v_val_4027_ = lean_ctor_get(v_presentation_4021_, 0);
lean_inc(v_val_4027_);
lean_dec_ref_known(v_presentation_4021_, 1);
v___x_4028_ = lean_unbox(v_val_4027_);
lean_dec(v_val_4027_);
switch(v___x_4028_)
{
case 1:
{
lean_object* v_dateformat_4029_; lean_object* v_symbols_4030_; lean_object* v___x_4031_; 
v_dateformat_4029_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4029_);
lean_dec_ref(v_config_3810_);
v_symbols_4030_ = lean_ctor_get(v_dateformat_4029_, 1);
lean_inc_ref(v_symbols_4030_);
lean_dec_ref(v_dateformat_4029_);
v___x_4031_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_4030_, v_a_3812_);
return v___x_4031_;
}
case 2:
{
lean_object* v_dateformat_4032_; lean_object* v_symbols_4033_; lean_object* v___x_4034_; 
v_dateformat_4032_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4032_);
lean_dec_ref(v_config_3810_);
v_symbols_4033_ = lean_ctor_get(v_dateformat_4032_, 1);
lean_inc_ref(v_symbols_4033_);
lean_dec_ref(v_dateformat_4032_);
v___x_4034_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_4033_, v_a_3812_);
return v___x_4034_;
}
default: 
{
lean_object* v_dateformat_4035_; lean_object* v_symbols_4036_; lean_object* v___x_4037_; 
v_dateformat_4035_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4035_);
lean_dec_ref(v_config_3810_);
v_symbols_4036_ = lean_ctor_get(v_dateformat_4035_, 1);
lean_inc_ref(v_symbols_4036_);
lean_dec_ref(v_dateformat_4035_);
v___x_4037_ = l_Std_Time_parseMonthShort(v_symbols_4036_, v_a_3812_);
return v___x_4037_;
}
}
}
}
case 6:
{
lean_object* v_presentation_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_dec_ref(v_config_3810_);
v_presentation_4038_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4038_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4039_ = lean_unsigned_to_nat(1u);
v___x_4040_ = lean_unsigned_to_nat(31u);
v___x_4041_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4041_, 0, v_presentation_4038_);
v___x_4042_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4039_, v___x_4040_, v___x_4041_, v_a_3812_);
return v___x_4042_;
}
case 7:
{
lean_object* v_presentation_4043_; 
v_presentation_4043_ = lean_ctor_get(v_x_3811_, 0);
lean_inc_ref(v_presentation_4043_);
lean_dec_ref_known(v_x_3811_, 1);
if (lean_obj_tag(v_presentation_4043_) == 0)
{
lean_object* v_val_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
lean_dec_ref(v_config_3810_);
v_val_4044_ = lean_ctor_get(v_presentation_4043_, 0);
lean_inc(v_val_4044_);
lean_dec_ref_known(v_presentation_4043_, 1);
v___x_4045_ = lean_unsigned_to_nat(1u);
v___x_4046_ = lean_unsigned_to_nat(4u);
v___x_4047_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4047_, 0, v_val_4044_);
v___x_4048_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4045_, v___x_4046_, v___x_4047_, v_a_3812_);
return v___x_4048_;
}
else
{
lean_object* v_val_4049_; uint8_t v___x_4050_; 
v_val_4049_ = lean_ctor_get(v_presentation_4043_, 0);
lean_inc(v_val_4049_);
lean_dec_ref_known(v_presentation_4043_, 1);
v___x_4050_ = lean_unbox(v_val_4049_);
lean_dec(v_val_4049_);
switch(v___x_4050_)
{
case 0:
{
lean_object* v_dateformat_4051_; lean_object* v_symbols_4052_; lean_object* v___x_4053_; 
v_dateformat_4051_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4051_);
lean_dec_ref(v_config_3810_);
v_symbols_4052_ = lean_ctor_get(v_dateformat_4051_, 1);
lean_inc_ref(v_symbols_4052_);
lean_dec_ref(v_dateformat_4051_);
v___x_4053_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4052_, v_a_3812_);
return v___x_4053_;
}
case 1:
{
lean_object* v_dateformat_4054_; lean_object* v_symbols_4055_; lean_object* v___x_4056_; 
v_dateformat_4054_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4054_);
lean_dec_ref(v_config_3810_);
v_symbols_4055_ = lean_ctor_get(v_dateformat_4054_, 1);
lean_inc_ref(v_symbols_4055_);
lean_dec_ref(v_dateformat_4054_);
v___x_4056_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4055_, v_a_3812_);
return v___x_4056_;
}
default: 
{
v___y_3814_ = v_a_3812_;
goto v___jp_3813_;
}
}
}
}
case 8:
{
lean_object* v_presentation_4057_; 
v_presentation_4057_ = lean_ctor_get(v_x_3811_, 0);
lean_inc_ref(v_presentation_4057_);
lean_dec_ref_known(v_x_3811_, 1);
if (lean_obj_tag(v_presentation_4057_) == 0)
{
lean_object* v_val_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
lean_dec_ref(v_config_3810_);
v_val_4058_ = lean_ctor_get(v_presentation_4057_, 0);
lean_inc(v_val_4058_);
lean_dec_ref_known(v_presentation_4057_, 1);
v___x_4059_ = lean_unsigned_to_nat(1u);
v___x_4060_ = lean_unsigned_to_nat(4u);
v___x_4061_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4061_, 0, v_val_4058_);
v___x_4062_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4059_, v___x_4060_, v___x_4061_, v_a_3812_);
return v___x_4062_;
}
else
{
lean_object* v_val_4063_; uint8_t v___x_4064_; 
v_val_4063_ = lean_ctor_get(v_presentation_4057_, 0);
lean_inc(v_val_4063_);
lean_dec_ref_known(v_presentation_4057_, 1);
v___x_4064_ = lean_unbox(v_val_4063_);
lean_dec(v_val_4063_);
switch(v___x_4064_)
{
case 0:
{
lean_object* v_dateformat_4065_; lean_object* v_symbols_4066_; lean_object* v___x_4067_; 
v_dateformat_4065_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4065_);
lean_dec_ref(v_config_3810_);
v_symbols_4066_ = lean_ctor_get(v_dateformat_4065_, 1);
lean_inc_ref(v_symbols_4066_);
lean_dec_ref(v_dateformat_4065_);
v___x_4067_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4066_, v_a_3812_);
return v___x_4067_;
}
case 1:
{
lean_object* v_dateformat_4068_; lean_object* v_symbols_4069_; lean_object* v___x_4070_; 
v_dateformat_4068_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4068_);
lean_dec_ref(v_config_3810_);
v_symbols_4069_ = lean_ctor_get(v_dateformat_4068_, 1);
lean_inc_ref(v_symbols_4069_);
lean_dec_ref(v_dateformat_4068_);
v___x_4070_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4069_, v_a_3812_);
return v___x_4070_;
}
default: 
{
v___y_3819_ = v_a_3812_;
goto v___jp_3818_;
}
}
}
}
case 9:
{
lean_object* v_presentation_4071_; 
lean_dec_ref(v_config_3810_);
v_presentation_4071_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4071_);
lean_dec_ref_known(v_x_3811_, 1);
switch(lean_obj_tag(v_presentation_4071_))
{
case 0:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_4073_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4072_, v_a_3812_);
return v___x_4073_;
}
case 1:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = lean_unsigned_to_nat(2u);
v___x_4075_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_4074_, v_a_3812_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_pos_4076_; lean_object* v_res_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4087_; 
v_pos_4076_ = lean_ctor_get(v___x_4075_, 0);
v_res_4077_ = lean_ctor_get(v___x_4075_, 1);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4079_ = v___x_4075_;
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_res_4077_);
lean_inc(v_pos_4076_);
lean_dec(v___x_4075_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4085_; 
v___x_4081_ = lean_nat_to_int(v_res_4077_);
v___x_4082_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_4083_ = lean_int_add(v___x_4082_, v___x_4081_);
lean_dec(v___x_4081_);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 1, v___x_4083_);
v___x_4085_ = v___x_4079_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_pos_4076_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v___x_4083_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
else
{
lean_object* v_pos_4088_; lean_object* v_err_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
v_pos_4088_ = lean_ctor_get(v___x_4075_, 0);
v_err_4089_ = lean_ctor_get(v___x_4075_, 1);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4075_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_err_4089_);
lean_inc(v_pos_4088_);
lean_dec(v___x_4075_);
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
case 2:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4097_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_4098_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4097_, v_a_3812_);
return v___x_4098_;
}
default: 
{
lean_object* v_num_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_num_4099_ = lean_ctor_get(v_presentation_4071_, 0);
lean_inc(v_num_4099_);
lean_dec_ref_known(v_presentation_4071_, 1);
v___x_4100_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_4100_, 0, v_num_4099_);
v___x_4101_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4100_, v_a_3812_);
return v___x_4101_;
}
}
}
case 10:
{
lean_object* v_presentation_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
lean_dec_ref(v_config_3810_);
v_presentation_4102_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4102_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4103_ = lean_unsigned_to_nat(1u);
v___x_4104_ = lean_unsigned_to_nat(53u);
v___x_4105_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4105_, 0, v_presentation_4102_);
v___x_4106_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4103_, v___x_4104_, v___x_4105_, v_a_3812_);
return v___x_4106_;
}
case 11:
{
lean_object* v_presentation_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_dec_ref(v_config_3810_);
v_presentation_4107_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4107_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4108_ = lean_unsigned_to_nat(1u);
v___x_4109_ = lean_unsigned_to_nat(6u);
v___x_4110_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4110_, 0, v_presentation_4107_);
v___x_4111_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4108_, v___x_4109_, v___x_4110_, v_a_3812_);
return v___x_4111_;
}
case 12:
{
uint8_t v_presentation_4112_; 
v_presentation_4112_ = lean_ctor_get_uint8(v_x_3811_, 0);
lean_dec_ref_known(v_x_3811_, 0);
switch(v_presentation_4112_)
{
case 1:
{
lean_object* v_dateformat_4113_; lean_object* v_symbols_4114_; lean_object* v___x_4115_; 
v_dateformat_4113_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4113_);
lean_dec_ref(v_config_3810_);
v_symbols_4114_ = lean_ctor_get(v_dateformat_4113_, 1);
lean_inc_ref(v_symbols_4114_);
lean_dec_ref(v_dateformat_4113_);
v___x_4115_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4114_, v_a_3812_);
return v___x_4115_;
}
case 2:
{
lean_object* v_dateformat_4116_; lean_object* v_symbols_4117_; lean_object* v___x_4118_; 
v_dateformat_4116_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4116_);
lean_dec_ref(v_config_3810_);
v_symbols_4117_ = lean_ctor_get(v_dateformat_4116_, 1);
lean_inc_ref(v_symbols_4117_);
lean_dec_ref(v_dateformat_4116_);
v___x_4118_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4117_, v_a_3812_);
return v___x_4118_;
}
default: 
{
lean_object* v_dateformat_4119_; lean_object* v_symbols_4120_; lean_object* v___x_4121_; 
v_dateformat_4119_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4119_);
lean_dec_ref(v_config_3810_);
v_symbols_4120_ = lean_ctor_get(v_dateformat_4119_, 1);
lean_inc_ref(v_symbols_4120_);
lean_dec_ref(v_dateformat_4119_);
v___x_4121_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4120_, v_a_3812_);
return v___x_4121_;
}
}
}
case 13:
{
lean_object* v_presentation_4122_; 
v_presentation_4122_ = lean_ctor_get(v_x_3811_, 0);
lean_inc_ref(v_presentation_4122_);
lean_dec_ref_known(v_x_3811_, 1);
if (lean_obj_tag(v_presentation_4122_) == 0)
{
lean_object* v_val_4123_; lean_object* v___x_4124_; 
v_val_4123_ = lean_ctor_get(v_presentation_4122_, 0);
lean_inc(v_val_4123_);
lean_dec_ref_known(v_presentation_4122_, 1);
v___x_4124_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4123_, v_a_3812_);
lean_dec(v_val_4123_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_pos_4125_; lean_object* v_res_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4162_; 
v_pos_4125_ = lean_ctor_get(v___x_4124_, 0);
v_res_4126_ = lean_ctor_get(v___x_4124_, 1);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4128_ = v___x_4124_;
v_isShared_4129_ = v_isSharedCheck_4162_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_res_4126_);
lean_inc(v_pos_4125_);
lean_dec(v___x_4124_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4162_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; uint8_t v___x_4131_; lean_object* v___x_4132_; uint8_t v___y_4134_; 
v___x_4130_ = lean_unsigned_to_nat(1u);
v___x_4131_ = lean_nat_dec_le(v___x_4130_, v_res_4126_);
v___x_4132_ = lean_unsigned_to_nat(7u);
if (v___x_4131_ == 0)
{
v___y_4134_ = v___x_4131_;
goto v___jp_4133_;
}
else
{
uint8_t v___x_4161_; 
v___x_4161_ = lean_nat_dec_le(v_res_4126_, v___x_4132_);
v___y_4134_ = v___x_4161_;
goto v___jp_4133_;
}
v___jp_4133_:
{
if (v___y_4134_ == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4137_; 
lean_dec(v_res_4126_);
lean_dec_ref(v_config_3810_);
v___x_4135_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4129_ == 0)
{
lean_ctor_set_tag(v___x_4128_, 1);
lean_ctor_set(v___x_4128_, 1, v___x_4135_);
v___x_4137_ = v___x_4128_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_pos_4125_);
lean_ctor_set(v_reuseFailAlloc_4138_, 1, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
else
{
lean_object* v_dateformat_4139_; uint8_t v_firstDayOfWeek_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v_range_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4159_; 
v_dateformat_4139_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4139_);
lean_dec_ref(v_config_3810_);
v_firstDayOfWeek_4140_ = lean_ctor_get_uint8(v_dateformat_4139_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4139_);
v___x_4141_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4140_);
v___x_4142_ = lean_nat_to_int(v_res_4126_);
v___x_4143_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4144_ = lean_int_sub(v___x_4142_, v___x_4143_);
lean_dec(v___x_4142_);
v___x_4145_ = lean_int_add(v___x_4144_, v___x_4141_);
lean_dec(v___x_4141_);
lean_dec(v___x_4144_);
v___x_4146_ = lean_int_sub(v___x_4145_, v___x_4143_);
lean_dec(v___x_4145_);
v___x_4147_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4148_ = lean_int_emod(v___x_4146_, v___x_4147_);
lean_dec(v___x_4146_);
v___x_4149_ = lean_int_add(v___x_4148_, v___x_4143_);
lean_dec(v___x_4148_);
v_range_4150_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4151_ = lean_int_sub(v___x_4149_, v___x_4143_);
lean_dec(v___x_4149_);
v___x_4152_ = lean_int_emod(v___x_4151_, v_range_4150_);
lean_dec(v___x_4151_);
v___x_4153_ = lean_int_add(v___x_4152_, v_range_4150_);
lean_dec(v___x_4152_);
v___x_4154_ = lean_int_emod(v___x_4153_, v_range_4150_);
lean_dec(v___x_4153_);
v___x_4155_ = lean_int_add(v___x_4154_, v___x_4143_);
lean_dec(v___x_4154_);
v___x_4156_ = l_Std_Time_Weekday_ofOrdinal(v___x_4155_);
lean_dec(v___x_4155_);
v___x_4157_ = lean_box(v___x_4156_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 1, v___x_4157_);
v___x_4159_ = v___x_4128_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_pos_4125_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v___x_4157_);
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
}
else
{
lean_object* v_pos_4163_; lean_object* v_err_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec_ref(v_config_3810_);
v_pos_4163_ = lean_ctor_get(v___x_4124_, 0);
v_err_4164_ = lean_ctor_get(v___x_4124_, 1);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4124_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_err_4164_);
lean_inc(v_pos_4163_);
lean_dec(v___x_4124_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_pos_4163_);
lean_ctor_set(v_reuseFailAlloc_4170_, 1, v_err_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
else
{
lean_object* v_val_4172_; uint8_t v___x_4173_; 
v_val_4172_ = lean_ctor_get(v_presentation_4122_, 0);
lean_inc(v_val_4172_);
lean_dec_ref_known(v_presentation_4122_, 1);
v___x_4173_ = lean_unbox(v_val_4172_);
lean_dec(v_val_4172_);
switch(v___x_4173_)
{
case 0:
{
lean_object* v_dateformat_4174_; lean_object* v_symbols_4175_; lean_object* v___x_4176_; 
v_dateformat_4174_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4174_);
lean_dec_ref(v_config_3810_);
v_symbols_4175_ = lean_ctor_get(v_dateformat_4174_, 1);
lean_inc_ref(v_symbols_4175_);
lean_dec_ref(v_dateformat_4174_);
v___x_4176_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4175_, v_a_3812_);
return v___x_4176_;
}
case 1:
{
lean_object* v_dateformat_4177_; lean_object* v_symbols_4178_; lean_object* v___x_4179_; 
v_dateformat_4177_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4177_);
lean_dec_ref(v_config_3810_);
v_symbols_4178_ = lean_ctor_get(v_dateformat_4177_, 1);
lean_inc_ref(v_symbols_4178_);
lean_dec_ref(v_dateformat_4177_);
v___x_4179_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4178_, v_a_3812_);
return v___x_4179_;
}
case 2:
{
lean_object* v_dateformat_4180_; lean_object* v_symbols_4181_; lean_object* v___x_4182_; 
v_dateformat_4180_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4180_);
lean_dec_ref(v_config_3810_);
v_symbols_4181_ = lean_ctor_get(v_dateformat_4180_, 1);
lean_inc_ref(v_symbols_4181_);
lean_dec_ref(v_dateformat_4180_);
v___x_4182_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4181_, v_a_3812_);
return v___x_4182_;
}
default: 
{
lean_object* v_dateformat_4183_; lean_object* v_symbols_4184_; lean_object* v___x_4185_; 
v_dateformat_4183_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4183_);
lean_dec_ref(v_config_3810_);
v_symbols_4184_ = lean_ctor_get(v_dateformat_4183_, 1);
lean_inc_ref(v_symbols_4184_);
lean_dec_ref(v_dateformat_4183_);
v___x_4185_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4184_, v_a_3812_);
return v___x_4185_;
}
}
}
}
case 14:
{
lean_object* v_presentation_4186_; 
v_presentation_4186_ = lean_ctor_get(v_x_3811_, 0);
lean_inc_ref(v_presentation_4186_);
lean_dec_ref_known(v_x_3811_, 1);
if (lean_obj_tag(v_presentation_4186_) == 0)
{
lean_object* v_val_4187_; lean_object* v___x_4188_; 
v_val_4187_ = lean_ctor_get(v_presentation_4186_, 0);
lean_inc(v_val_4187_);
lean_dec_ref_known(v_presentation_4186_, 1);
v___x_4188_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4187_, v_a_3812_);
lean_dec(v_val_4187_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_pos_4189_; lean_object* v_res_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4226_; 
v_pos_4189_ = lean_ctor_get(v___x_4188_, 0);
v_res_4190_ = lean_ctor_get(v___x_4188_, 1);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4192_ = v___x_4188_;
v_isShared_4193_ = v_isSharedCheck_4226_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_res_4190_);
lean_inc(v_pos_4189_);
lean_dec(v___x_4188_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4226_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4194_; uint8_t v___x_4195_; lean_object* v___x_4196_; uint8_t v___y_4198_; 
v___x_4194_ = lean_unsigned_to_nat(1u);
v___x_4195_ = lean_nat_dec_le(v___x_4194_, v_res_4190_);
v___x_4196_ = lean_unsigned_to_nat(7u);
if (v___x_4195_ == 0)
{
v___y_4198_ = v___x_4195_;
goto v___jp_4197_;
}
else
{
uint8_t v___x_4225_; 
v___x_4225_ = lean_nat_dec_le(v_res_4190_, v___x_4196_);
v___y_4198_ = v___x_4225_;
goto v___jp_4197_;
}
v___jp_4197_:
{
if (v___y_4198_ == 0)
{
lean_object* v___x_4199_; lean_object* v___x_4201_; 
lean_dec(v_res_4190_);
lean_dec_ref(v_config_3810_);
v___x_4199_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4193_ == 0)
{
lean_ctor_set_tag(v___x_4192_, 1);
lean_ctor_set(v___x_4192_, 1, v___x_4199_);
v___x_4201_ = v___x_4192_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_pos_4189_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v___x_4199_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
else
{
lean_object* v_dateformat_4203_; uint8_t v_firstDayOfWeek_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v_range_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4223_; 
v_dateformat_4203_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4203_);
lean_dec_ref(v_config_3810_);
v_firstDayOfWeek_4204_ = lean_ctor_get_uint8(v_dateformat_4203_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4203_);
v___x_4205_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4204_);
v___x_4206_ = lean_nat_to_int(v_res_4190_);
v___x_4207_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4208_ = lean_int_sub(v___x_4206_, v___x_4207_);
lean_dec(v___x_4206_);
v___x_4209_ = lean_int_add(v___x_4208_, v___x_4205_);
lean_dec(v___x_4205_);
lean_dec(v___x_4208_);
v___x_4210_ = lean_int_sub(v___x_4209_, v___x_4207_);
lean_dec(v___x_4209_);
v___x_4211_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4212_ = lean_int_emod(v___x_4210_, v___x_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_int_add(v___x_4212_, v___x_4207_);
lean_dec(v___x_4212_);
v_range_4214_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4215_ = lean_int_sub(v___x_4213_, v___x_4207_);
lean_dec(v___x_4213_);
v___x_4216_ = lean_int_emod(v___x_4215_, v_range_4214_);
lean_dec(v___x_4215_);
v___x_4217_ = lean_int_add(v___x_4216_, v_range_4214_);
lean_dec(v___x_4216_);
v___x_4218_ = lean_int_emod(v___x_4217_, v_range_4214_);
lean_dec(v___x_4217_);
v___x_4219_ = lean_int_add(v___x_4218_, v___x_4207_);
lean_dec(v___x_4218_);
v___x_4220_ = l_Std_Time_Weekday_ofOrdinal(v___x_4219_);
lean_dec(v___x_4219_);
v___x_4221_ = lean_box(v___x_4220_);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 1, v___x_4221_);
v___x_4223_ = v___x_4192_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_pos_4189_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
}
else
{
lean_object* v_pos_4227_; lean_object* v_err_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_dec_ref(v_config_3810_);
v_pos_4227_ = lean_ctor_get(v___x_4188_, 0);
v_err_4228_ = lean_ctor_get(v___x_4188_, 1);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4188_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_err_4228_);
lean_inc(v_pos_4227_);
lean_dec(v___x_4188_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_pos_4227_);
lean_ctor_set(v_reuseFailAlloc_4234_, 1, v_err_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
else
{
lean_object* v_val_4236_; uint8_t v___x_4237_; 
v_val_4236_ = lean_ctor_get(v_presentation_4186_, 0);
lean_inc(v_val_4236_);
lean_dec_ref_known(v_presentation_4186_, 1);
v___x_4237_ = lean_unbox(v_val_4236_);
lean_dec(v_val_4236_);
switch(v___x_4237_)
{
case 0:
{
lean_object* v_dateformat_4238_; lean_object* v_symbols_4239_; lean_object* v___x_4240_; 
v_dateformat_4238_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4238_);
lean_dec_ref(v_config_3810_);
v_symbols_4239_ = lean_ctor_get(v_dateformat_4238_, 1);
lean_inc_ref(v_symbols_4239_);
lean_dec_ref(v_dateformat_4238_);
v___x_4240_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4239_, v_a_3812_);
return v___x_4240_;
}
case 1:
{
lean_object* v_dateformat_4241_; lean_object* v_symbols_4242_; lean_object* v___x_4243_; 
v_dateformat_4241_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4241_);
lean_dec_ref(v_config_3810_);
v_symbols_4242_ = lean_ctor_get(v_dateformat_4241_, 1);
lean_inc_ref(v_symbols_4242_);
lean_dec_ref(v_dateformat_4241_);
v___x_4243_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4242_, v_a_3812_);
return v___x_4243_;
}
case 2:
{
lean_object* v_dateformat_4244_; lean_object* v_symbols_4245_; lean_object* v___x_4246_; 
v_dateformat_4244_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4244_);
lean_dec_ref(v_config_3810_);
v_symbols_4245_ = lean_ctor_get(v_dateformat_4244_, 1);
lean_inc_ref(v_symbols_4245_);
lean_dec_ref(v_dateformat_4244_);
v___x_4246_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4245_, v_a_3812_);
return v___x_4246_;
}
default: 
{
lean_object* v_dateformat_4247_; lean_object* v_symbols_4248_; lean_object* v___x_4249_; 
v_dateformat_4247_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4247_);
lean_dec_ref(v_config_3810_);
v_symbols_4248_ = lean_ctor_get(v_dateformat_4247_, 1);
lean_inc_ref(v_symbols_4248_);
lean_dec_ref(v_dateformat_4247_);
v___x_4249_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4248_, v_a_3812_);
return v___x_4249_;
}
}
}
}
case 15:
{
lean_object* v_presentation_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
lean_dec_ref(v_config_3810_);
v_presentation_4250_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4250_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4251_ = lean_unsigned_to_nat(1u);
v___x_4252_ = lean_unsigned_to_nat(5u);
v___x_4253_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4253_, 0, v_presentation_4250_);
v___x_4254_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4251_, v___x_4252_, v___x_4253_, v_a_3812_);
return v___x_4254_;
}
case 16:
{
uint8_t v_presentation_4255_; 
v_presentation_4255_ = lean_ctor_get_uint8(v_x_3811_, 0);
lean_dec_ref_known(v_x_3811_, 0);
switch(v_presentation_4255_)
{
case 1:
{
lean_object* v_dateformat_4256_; lean_object* v_symbols_4257_; lean_object* v___x_4258_; 
v_dateformat_4256_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4256_);
lean_dec_ref(v_config_3810_);
v_symbols_4257_ = lean_ctor_get(v_dateformat_4256_, 1);
lean_inc_ref(v_symbols_4257_);
lean_dec_ref(v_dateformat_4256_);
v___x_4258_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(v_symbols_4257_, v_a_3812_);
return v___x_4258_;
}
case 2:
{
lean_object* v_dateformat_4259_; lean_object* v_symbols_4260_; lean_object* v___x_4261_; 
v_dateformat_4259_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4259_);
lean_dec_ref(v_config_3810_);
v_symbols_4260_ = lean_ctor_get(v_dateformat_4259_, 1);
lean_inc_ref(v_symbols_4260_);
lean_dec_ref(v_dateformat_4259_);
v___x_4261_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(v_symbols_4260_, v_a_3812_);
return v___x_4261_;
}
default: 
{
lean_object* v_dateformat_4262_; lean_object* v_symbols_4263_; lean_object* v___x_4264_; 
v_dateformat_4262_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4262_);
lean_dec_ref(v_config_3810_);
v_symbols_4263_ = lean_ctor_get(v_dateformat_4262_, 1);
lean_inc_ref(v_symbols_4263_);
lean_dec_ref(v_dateformat_4262_);
v___x_4264_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(v_symbols_4263_, v_a_3812_);
return v___x_4264_;
}
}
}
case 17:
{
uint8_t v_presentation_4265_; 
v_presentation_4265_ = lean_ctor_get_uint8(v_x_3811_, 0);
lean_dec_ref_known(v_x_3811_, 0);
switch(v_presentation_4265_)
{
case 1:
{
lean_object* v_dateformat_4266_; lean_object* v_symbols_4267_; lean_object* v_dayPeriodLong_4268_; lean_object* v___x_4269_; 
v_dateformat_4266_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4266_);
lean_dec_ref(v_config_3810_);
v_symbols_4267_ = lean_ctor_get(v_dateformat_4266_, 1);
lean_inc_ref(v_symbols_4267_);
lean_dec_ref(v_dateformat_4266_);
v_dayPeriodLong_4268_ = lean_ctor_get(v_symbols_4267_, 20);
lean_inc_ref(v_dayPeriodLong_4268_);
lean_dec_ref(v_symbols_4267_);
v___x_4269_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodLong_4268_, v_a_3812_);
return v___x_4269_;
}
case 2:
{
lean_object* v_dateformat_4270_; lean_object* v_symbols_4271_; lean_object* v_dayPeriodNarrow_4272_; lean_object* v___x_4273_; 
v_dateformat_4270_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4270_);
lean_dec_ref(v_config_3810_);
v_symbols_4271_ = lean_ctor_get(v_dateformat_4270_, 1);
lean_inc_ref(v_symbols_4271_);
lean_dec_ref(v_dateformat_4270_);
v_dayPeriodNarrow_4272_ = lean_ctor_get(v_symbols_4271_, 21);
lean_inc_ref(v_dayPeriodNarrow_4272_);
lean_dec_ref(v_symbols_4271_);
v___x_4273_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodNarrow_4272_, v_a_3812_);
return v___x_4273_;
}
default: 
{
lean_object* v_dateformat_4274_; lean_object* v_symbols_4275_; lean_object* v_dayPeriodShort_4276_; lean_object* v___x_4277_; 
v_dateformat_4274_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4274_);
lean_dec_ref(v_config_3810_);
v_symbols_4275_ = lean_ctor_get(v_dateformat_4274_, 1);
lean_inc_ref(v_symbols_4275_);
lean_dec_ref(v_dateformat_4274_);
v_dayPeriodShort_4276_ = lean_ctor_get(v_symbols_4275_, 19);
lean_inc_ref(v_dayPeriodShort_4276_);
lean_dec_ref(v_symbols_4275_);
v___x_4277_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodShort_4276_, v_a_3812_);
return v___x_4277_;
}
}
}
case 18:
{
uint8_t v_presentation_4278_; 
v_presentation_4278_ = lean_ctor_get_uint8(v_x_3811_, 0);
lean_dec_ref_known(v_x_3811_, 0);
switch(v_presentation_4278_)
{
case 1:
{
lean_object* v_dateformat_4279_; lean_object* v_symbols_4280_; lean_object* v_extendedDayPeriodLong_4281_; lean_object* v___x_4282_; 
v_dateformat_4279_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4279_);
lean_dec_ref(v_config_3810_);
v_symbols_4280_ = lean_ctor_get(v_dateformat_4279_, 1);
lean_inc_ref(v_symbols_4280_);
lean_dec_ref(v_dateformat_4279_);
v_extendedDayPeriodLong_4281_ = lean_ctor_get(v_symbols_4280_, 23);
lean_inc_ref(v_extendedDayPeriodLong_4281_);
lean_dec_ref(v_symbols_4280_);
v___x_4282_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodLong_4281_, v_a_3812_);
lean_dec_ref(v_extendedDayPeriodLong_4281_);
return v___x_4282_;
}
case 2:
{
lean_object* v_dateformat_4283_; lean_object* v_symbols_4284_; lean_object* v_extendedDayPeriodNarrow_4285_; lean_object* v___x_4286_; 
v_dateformat_4283_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4283_);
lean_dec_ref(v_config_3810_);
v_symbols_4284_ = lean_ctor_get(v_dateformat_4283_, 1);
lean_inc_ref(v_symbols_4284_);
lean_dec_ref(v_dateformat_4283_);
v_extendedDayPeriodNarrow_4285_ = lean_ctor_get(v_symbols_4284_, 24);
lean_inc_ref(v_extendedDayPeriodNarrow_4285_);
lean_dec_ref(v_symbols_4284_);
v___x_4286_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodNarrow_4285_, v_a_3812_);
lean_dec_ref(v_extendedDayPeriodNarrow_4285_);
return v___x_4286_;
}
default: 
{
lean_object* v_dateformat_4287_; lean_object* v_symbols_4288_; lean_object* v_extendedDayPeriodShort_4289_; lean_object* v___x_4290_; 
v_dateformat_4287_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_4287_);
lean_dec_ref(v_config_3810_);
v_symbols_4288_ = lean_ctor_get(v_dateformat_4287_, 1);
lean_inc_ref(v_symbols_4288_);
lean_dec_ref(v_dateformat_4287_);
v_extendedDayPeriodShort_4289_ = lean_ctor_get(v_symbols_4288_, 22);
lean_inc_ref(v_extendedDayPeriodShort_4289_);
lean_dec_ref(v_symbols_4288_);
v___x_4290_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodShort_4289_, v_a_3812_);
lean_dec_ref(v_extendedDayPeriodShort_4289_);
return v___x_4290_;
}
}
}
case 19:
{
lean_object* v_presentation_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
lean_dec_ref(v_config_3810_);
v_presentation_4291_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4291_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4292_ = lean_unsigned_to_nat(1u);
v___x_4293_ = lean_unsigned_to_nat(12u);
v___x_4294_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4294_, 0, v_presentation_4291_);
v___x_4295_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4292_, v___x_4293_, v___x_4294_, v_a_3812_);
return v___x_4295_;
}
case 20:
{
lean_object* v_presentation_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
lean_dec_ref(v_config_3810_);
v_presentation_4296_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4296_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = lean_unsigned_to_nat(11u);
v___x_4299_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4299_, 0, v_presentation_4296_);
v___x_4300_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4297_, v___x_4298_, v___x_4299_, v_a_3812_);
return v___x_4300_;
}
case 21:
{
lean_object* v_presentation_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
lean_dec_ref(v_config_3810_);
v_presentation_4301_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4301_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4302_ = lean_unsigned_to_nat(1u);
v___x_4303_ = lean_unsigned_to_nat(24u);
v___x_4304_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4304_, 0, v_presentation_4301_);
v___x_4305_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4302_, v___x_4303_, v___x_4304_, v_a_3812_);
return v___x_4305_;
}
case 22:
{
lean_object* v_presentation_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
lean_dec_ref(v_config_3810_);
v_presentation_4306_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4306_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4307_ = lean_unsigned_to_nat(0u);
v___x_4308_ = lean_unsigned_to_nat(23u);
v___x_4309_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4309_, 0, v_presentation_4306_);
v___x_4310_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4307_, v___x_4308_, v___x_4309_, v_a_3812_);
return v___x_4310_;
}
case 23:
{
lean_object* v_presentation_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
lean_dec_ref(v_config_3810_);
v_presentation_4311_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4311_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4312_ = lean_unsigned_to_nat(0u);
v___x_4313_ = lean_unsigned_to_nat(59u);
v___x_4314_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4314_, 0, v_presentation_4311_);
v___x_4315_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4312_, v___x_4313_, v___x_4314_, v_a_3812_);
return v___x_4315_;
}
case 24:
{
uint8_t v_allowLeapSeconds_4316_; 
v_allowLeapSeconds_4316_ = lean_ctor_get_uint8(v_config_3810_, sizeof(void*)*1);
lean_dec_ref(v_config_3810_);
if (v_allowLeapSeconds_4316_ == 0)
{
lean_object* v_presentation_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v_presentation_4317_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4317_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4318_ = lean_unsigned_to_nat(0u);
v___x_4319_ = lean_unsigned_to_nat(59u);
v___x_4320_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4320_, 0, v_presentation_4317_);
v___x_4321_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4318_, v___x_4319_, v___x_4320_, v_a_3812_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_pos_4322_; lean_object* v_res_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
v_pos_4322_ = lean_ctor_get(v___x_4321_, 0);
v_res_4323_ = lean_ctor_get(v___x_4321_, 1);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4321_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_res_4323_);
lean_inc(v_pos_4322_);
lean_dec(v___x_4321_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_pos_4322_);
lean_ctor_set(v_reuseFailAlloc_4329_, 1, v_res_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
else
{
return v___x_4321_;
}
}
else
{
lean_object* v_presentation_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v_presentation_4331_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4331_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4332_ = lean_unsigned_to_nat(0u);
v___x_4333_ = lean_unsigned_to_nat(60u);
v___x_4334_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4334_, 0, v_presentation_4331_);
v___x_4335_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4332_, v___x_4333_, v___x_4334_, v_a_3812_);
return v___x_4335_;
}
}
case 25:
{
lean_object* v_presentation_4336_; 
lean_dec_ref(v_config_3810_);
v_presentation_4336_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4336_);
lean_dec_ref_known(v_x_3811_, 1);
if (lean_obj_tag(v_presentation_4336_) == 0)
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4337_ = lean_unsigned_to_nat(0u);
v___x_4338_ = lean_unsigned_to_nat(999999999u);
v___x_4339_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7));
v___x_4340_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4337_, v___x_4338_, v___x_4339_, v_a_3812_);
return v___x_4340_;
}
else
{
lean_object* v_digits_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_digits_4341_ = lean_ctor_get(v_presentation_4336_, 0);
lean_inc(v_digits_4341_);
lean_dec_ref_known(v_presentation_4336_, 1);
v___x_4342_ = lean_unsigned_to_nat(0u);
v___x_4343_ = lean_unsigned_to_nat(999999999u);
v___x_4344_ = lean_unsigned_to_nat(9u);
v___x_4345_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed), 3, 2);
lean_closure_set(v___x_4345_, 0, v_digits_4341_);
lean_closure_set(v___x_4345_, 1, v___x_4344_);
v___x_4346_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4342_, v___x_4343_, v___x_4345_, v_a_3812_);
return v___x_4346_;
}
}
case 26:
{
lean_object* v_presentation_4347_; lean_object* v___x_4348_; 
lean_dec_ref(v_config_3810_);
v_presentation_4347_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4347_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4348_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4347_, v_a_3812_);
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
case 27:
{
lean_object* v_presentation_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
lean_dec_ref(v_config_3810_);
v_presentation_4368_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4368_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4369_ = lean_unsigned_to_nat(0u);
v___x_4370_ = lean_unsigned_to_nat(999999999u);
v___x_4371_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4371_, 0, v_presentation_4368_);
v___x_4372_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4369_, v___x_4370_, v___x_4371_, v_a_3812_);
return v___x_4372_;
}
case 28:
{
lean_object* v_presentation_4373_; lean_object* v___x_4374_; 
lean_dec_ref(v_config_3810_);
v_presentation_4373_ = lean_ctor_get(v_x_3811_, 0);
lean_inc(v_presentation_4373_);
lean_dec_ref_known(v_x_3811_, 1);
v___x_4374_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4373_, v_a_3812_);
lean_dec(v_presentation_4373_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_pos_4375_; lean_object* v_res_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4384_; 
v_pos_4375_ = lean_ctor_get(v___x_4374_, 0);
v_res_4376_ = lean_ctor_get(v___x_4374_, 1);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4378_ = v___x_4374_;
v_isShared_4379_ = v_isSharedCheck_4384_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_res_4376_);
lean_inc(v_pos_4375_);
lean_dec(v___x_4374_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4384_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; lean_object* v___x_4382_; 
v___x_4380_ = lean_nat_to_int(v_res_4376_);
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
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_pos_4375_);
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
lean_object* v_pos_4385_; lean_object* v_err_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v_pos_4385_ = lean_ctor_get(v___x_4374_, 0);
v_err_4386_ = lean_ctor_get(v___x_4374_, 1);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4374_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_err_4386_);
lean_inc(v_pos_4385_);
lean_dec(v___x_4374_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_pos_4385_);
lean_ctor_set(v_reuseFailAlloc_4392_, 1, v_err_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
case 29:
{
uint8_t v_presentation_4394_; 
lean_dec_ref(v_config_3810_);
v_presentation_4394_ = lean_ctor_get_uint8(v_x_3811_, 0);
lean_dec_ref_known(v_x_3811_, 0);
if (v_presentation_4394_ == 0)
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4395_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
v___x_4396_ = l_Std_Internal_Parsec_String_pstring(v___x_4395_, v_a_3812_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_pos_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
v_pos_4397_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; 
v_unused_4405_ = lean_ctor_get(v___x_4396_, 1);
lean_dec(v_unused_4405_);
v___x_4399_ = v___x_4396_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_pos_4397_);
lean_dec(v___x_4396_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 1, v___x_4395_);
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_pos_4397_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v___x_4395_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
else
{
return v___x_4396_;
}
}
else
{
lean_object* v___x_4406_; 
v___x_4406_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3812_);
return v___x_4406_;
}
}
case 32:
{
uint8_t v_presentation_4407_; 
lean_dec_ref(v_config_3810_);
v_presentation_4407_ = lean_ctor_get_uint8(v_x_3811_, 0);
lean_dec_ref_known(v_x_3811_, 0);
if (v_presentation_4407_ == 0)
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4409_ = l_Std_Internal_Parsec_String_pstring(v___x_4408_, v_a_3812_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_pos_4410_; uint8_t v___x_4411_; uint8_t v___x_4412_; uint8_t v___x_4413_; lean_object* v___x_4414_; 
v_pos_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_pos_4410_);
lean_dec_ref_known(v___x_4409_, 2);
v___x_4411_ = 2;
v___x_4412_ = 1;
v___x_4413_ = 1;
v___x_4414_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4411_, v___x_4412_, v___x_4413_, v_pos_4410_);
return v___x_4414_;
}
else
{
lean_object* v_pos_4415_; lean_object* v_err_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
v_pos_4415_ = lean_ctor_get(v___x_4409_, 0);
v_err_4416_ = lean_ctor_get(v___x_4409_, 1);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4409_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_err_4416_);
lean_inc(v_pos_4415_);
lean_dec(v___x_4409_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_pos_4415_);
lean_ctor_set(v_reuseFailAlloc_4422_, 1, v_err_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
else
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4424_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4425_ = l_Std_Internal_Parsec_String_pstring(v___x_4424_, v_a_3812_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_pos_4426_; uint8_t v___x_4427_; uint8_t v___x_4428_; uint8_t v___x_4429_; lean_object* v___x_4430_; 
v_pos_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_pos_4426_);
lean_dec_ref_known(v___x_4425_, 2);
v___x_4427_ = 0;
v___x_4428_ = 2;
v___x_4429_ = 1;
v___x_4430_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4427_, v___x_4428_, v___x_4429_, v_pos_4426_);
return v___x_4430_;
}
else
{
lean_object* v_pos_4431_; lean_object* v_err_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
v_pos_4431_ = lean_ctor_get(v___x_4425_, 0);
v_err_4432_ = lean_ctor_get(v___x_4425_, 1);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4425_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_err_4432_);
lean_inc(v_pos_4431_);
lean_dec(v___x_4425_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_pos_4431_);
lean_ctor_set(v_reuseFailAlloc_4438_, 1, v_err_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
}
case 33:
{
uint8_t v_presentation_4440_; 
lean_dec_ref(v_config_3810_);
v_presentation_4440_ = lean_ctor_get_uint8(v_x_3811_, 0);
lean_dec_ref_known(v_x_3811_, 0);
switch(v_presentation_4440_)
{
case 0:
{
uint8_t v___x_4441_; uint8_t v___x_4442_; uint8_t v___x_4443_; lean_object* v___x_4444_; 
v___x_4441_ = 2;
v___x_4442_ = 1;
v___x_4443_ = 0;
lean_inc_ref(v_a_3812_);
v___x_4444_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4441_, v___x_4442_, v___x_4443_, v_a_3812_);
v___y_3824_ = v___x_4444_;
goto v___jp_3823_;
}
case 1:
{
uint8_t v___x_4445_; uint8_t v___x_4446_; uint8_t v___x_4447_; lean_object* v___x_4448_; 
v___x_4445_ = 0;
v___x_4446_ = 1;
v___x_4447_ = 0;
lean_inc_ref(v_a_3812_);
v___x_4448_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4445_, v___x_4446_, v___x_4447_, v_a_3812_);
v___y_3824_ = v___x_4448_;
goto v___jp_3823_;
}
case 2:
{
uint8_t v___x_4449_; uint8_t v___x_4450_; uint8_t v___x_4451_; lean_object* v___x_4452_; 
v___x_4449_ = 0;
v___x_4450_ = 1;
v___x_4451_ = 1;
lean_inc_ref(v_a_3812_);
v___x_4452_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4449_, v___x_4450_, v___x_4451_, v_a_3812_);
v___y_3824_ = v___x_4452_;
goto v___jp_3823_;
}
case 3:
{
uint8_t v___x_4453_; uint8_t v___x_4454_; uint8_t v___x_4455_; lean_object* v___x_4456_; 
v___x_4453_ = 0;
v___x_4454_ = 2;
v___x_4455_ = 0;
lean_inc_ref(v_a_3812_);
v___x_4456_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4453_, v___x_4454_, v___x_4455_, v_a_3812_);
v___y_3824_ = v___x_4456_;
goto v___jp_3823_;
}
default: 
{
uint8_t v___x_4457_; uint8_t v___x_4458_; uint8_t v___x_4459_; lean_object* v___x_4460_; 
v___x_4457_ = 0;
v___x_4458_ = 2;
v___x_4459_ = 1;
lean_inc_ref(v_a_3812_);
v___x_4460_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4457_, v___x_4458_, v___x_4459_, v_a_3812_);
v___y_3824_ = v___x_4460_;
goto v___jp_3823_;
}
}
}
case 34:
{
uint8_t v_presentation_4461_; 
lean_dec_ref(v_config_3810_);
v_presentation_4461_ = lean_ctor_get_uint8(v_x_3811_, 0);
lean_dec_ref_known(v_x_3811_, 0);
switch(v_presentation_4461_)
{
case 0:
{
uint8_t v___x_4462_; uint8_t v___x_4463_; uint8_t v___x_4464_; lean_object* v___x_4465_; 
v___x_4462_ = 2;
v___x_4463_ = 1;
v___x_4464_ = 0;
v___x_4465_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4462_, v___x_4463_, v___x_4464_, v_a_3812_);
return v___x_4465_;
}
case 1:
{
uint8_t v___x_4466_; uint8_t v___x_4467_; uint8_t v___x_4468_; lean_object* v___x_4469_; 
v___x_4466_ = 0;
v___x_4467_ = 1;
v___x_4468_ = 0;
v___x_4469_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4466_, v___x_4467_, v___x_4468_, v_a_3812_);
return v___x_4469_;
}
case 2:
{
uint8_t v___x_4470_; uint8_t v___x_4471_; uint8_t v___x_4472_; lean_object* v___x_4473_; 
v___x_4470_ = 0;
v___x_4471_ = 2;
v___x_4472_ = 1;
v___x_4473_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4470_, v___x_4471_, v___x_4472_, v_a_3812_);
return v___x_4473_;
}
case 3:
{
uint8_t v___x_4474_; uint8_t v___x_4475_; uint8_t v___x_4476_; lean_object* v___x_4477_; 
v___x_4474_ = 0;
v___x_4475_ = 2;
v___x_4476_ = 0;
v___x_4477_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4474_, v___x_4475_, v___x_4476_, v_a_3812_);
return v___x_4477_;
}
default: 
{
uint8_t v___x_4478_; uint8_t v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = 0;
v___x_4479_ = 1;
v___x_4480_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4478_, v___x_4478_, v___x_4479_, v_a_3812_);
return v___x_4480_;
}
}
}
case 35:
{
uint8_t v_presentation_4481_; 
lean_dec_ref(v_config_3810_);
v_presentation_4481_ = lean_ctor_get_uint8(v_x_3811_, 0);
lean_dec_ref_known(v_x_3811_, 0);
switch(v_presentation_4481_)
{
case 0:
{
uint8_t v___x_4482_; uint8_t v___x_4483_; uint8_t v___x_4484_; lean_object* v___x_4485_; 
v___x_4482_ = 0;
v___x_4483_ = 1;
v___x_4484_ = 0;
v___x_4485_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4482_, v___x_4483_, v___x_4484_, v_a_3812_);
return v___x_4485_;
}
case 1:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4486_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4487_ = l_Std_Internal_Parsec_String_pstring(v___x_4486_, v_a_3812_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_pos_4488_; uint8_t v___x_4489_; uint8_t v___x_4490_; uint8_t v___x_4491_; lean_object* v___x_4492_; 
v_pos_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc_n(v_pos_4488_, 2);
lean_dec_ref_known(v___x_4487_, 2);
v___x_4489_ = 0;
v___x_4490_ = 1;
v___x_4491_ = 1;
v___x_4492_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4489_, v___x_4490_, v___x_4491_, v_pos_4488_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_dec(v_pos_4488_);
return v___x_4492_;
}
else
{
lean_object* v_pos_4493_; lean_object* v_snd_4494_; lean_object* v_snd_4495_; uint8_t v_decide_4496_; 
v_pos_4493_ = lean_ctor_get(v___x_4492_, 0);
v_snd_4494_ = lean_ctor_get(v_pos_4488_, 1);
lean_inc(v_snd_4494_);
lean_dec(v_pos_4488_);
v_snd_4495_ = lean_ctor_get(v_pos_4493_, 1);
v_decide_4496_ = lean_nat_dec_eq(v_snd_4494_, v_snd_4495_);
lean_dec(v_snd_4494_);
if (v_decide_4496_ == 0)
{
return v___x_4492_;
}
else
{
lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4504_; 
lean_inc(v_pos_4493_);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4504_ == 0)
{
lean_object* v_unused_4505_; lean_object* v_unused_4506_; 
v_unused_4505_ = lean_ctor_get(v___x_4492_, 1);
lean_dec(v_unused_4505_);
v_unused_4506_ = lean_ctor_get(v___x_4492_, 0);
lean_dec(v_unused_4506_);
v___x_4498_ = v___x_4492_;
v_isShared_4499_ = v_isSharedCheck_4504_;
goto v_resetjp_4497_;
}
else
{
lean_dec(v___x_4492_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4504_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4500_; lean_object* v___x_4502_; 
v___x_4500_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4499_ == 0)
{
lean_ctor_set_tag(v___x_4498_, 0);
lean_ctor_set(v___x_4498_, 1, v___x_4500_);
v___x_4502_ = v___x_4498_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_pos_4493_);
lean_ctor_set(v_reuseFailAlloc_4503_, 1, v___x_4500_);
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
else
{
lean_object* v_pos_4507_; lean_object* v_err_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
v_pos_4507_ = lean_ctor_get(v___x_4487_, 0);
v_err_4508_ = lean_ctor_get(v___x_4487_, 1);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4487_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_err_4508_);
lean_inc(v_pos_4507_);
lean_dec(v___x_4487_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_pos_4507_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_err_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
default: 
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
lean_inc_ref(v_a_3812_);
v___x_4517_ = l_Std_Internal_Parsec_String_pstring(v___x_4516_, v_a_3812_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_pos_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4526_; 
lean_dec_ref(v_a_3812_);
v_pos_4518_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4526_ == 0)
{
lean_object* v_unused_4527_; 
v_unused_4527_ = lean_ctor_get(v___x_4517_, 1);
lean_dec(v_unused_4527_);
v___x_4520_ = v___x_4517_;
v_isShared_4521_ = v_isSharedCheck_4526_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_pos_4518_);
lean_dec(v___x_4517_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4526_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4522_; lean_object* v___x_4524_; 
v___x_4522_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4521_ == 0)
{
lean_ctor_set(v___x_4520_, 1, v___x_4522_);
v___x_4524_ = v___x_4520_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_pos_4518_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v___x_4522_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
else
{
lean_object* v_pos_4528_; lean_object* v_err_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4542_; 
v_pos_4528_ = lean_ctor_get(v___x_4517_, 0);
v_err_4529_ = lean_ctor_get(v___x_4517_, 1);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4531_ = v___x_4517_;
v_isShared_4532_ = v_isSharedCheck_4542_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_err_4529_);
lean_inc(v_pos_4528_);
lean_dec(v___x_4517_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4542_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v_snd_4533_; lean_object* v_snd_4534_; uint8_t v_decide_4535_; 
v_snd_4533_ = lean_ctor_get(v_a_3812_, 1);
lean_inc(v_snd_4533_);
lean_dec_ref(v_a_3812_);
v_snd_4534_ = lean_ctor_get(v_pos_4528_, 1);
v_decide_4535_ = lean_nat_dec_eq(v_snd_4533_, v_snd_4534_);
lean_dec(v_snd_4533_);
if (v_decide_4535_ == 0)
{
lean_object* v___x_4537_; 
if (v_isShared_4532_ == 0)
{
v___x_4537_ = v___x_4531_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_pos_4528_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v_err_4529_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
else
{
uint8_t v___x_4539_; uint8_t v___x_4540_; lean_object* v___x_4541_; 
lean_del_object(v___x_4531_);
lean_dec(v_err_4529_);
v___x_4539_ = 0;
v___x_4540_ = 2;
v___x_4541_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4539_, v___x_4540_, v_decide_4535_, v_pos_4528_);
return v___x_4541_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_4543_; 
lean_dec_ref(v_x_3811_);
lean_dec_ref(v_config_3810_);
v___x_4543_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3812_);
return v___x_4543_;
}
}
v___jp_3813_:
{
lean_object* v_dateformat_3815_; lean_object* v_symbols_3816_; lean_object* v___x_3817_; 
v_dateformat_3815_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_3815_);
lean_dec_ref(v_config_3810_);
v_symbols_3816_ = lean_ctor_get(v_dateformat_3815_, 1);
lean_inc_ref(v_symbols_3816_);
lean_dec_ref(v_dateformat_3815_);
v___x_3817_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_3816_, v___y_3814_);
return v___x_3817_;
}
v___jp_3818_:
{
lean_object* v_dateformat_3820_; lean_object* v_symbols_3821_; lean_object* v___x_3822_; 
v_dateformat_3820_ = lean_ctor_get(v_config_3810_, 0);
lean_inc_ref(v_dateformat_3820_);
lean_dec_ref(v_config_3810_);
v_symbols_3821_ = lean_ctor_get(v_dateformat_3820_, 1);
lean_inc_ref(v_symbols_3821_);
lean_dec_ref(v_dateformat_3820_);
v___x_3822_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_3821_, v___y_3819_);
return v___x_3822_;
}
v___jp_3823_:
{
if (lean_obj_tag(v___y_3824_) == 0)
{
lean_dec_ref(v_a_3812_);
return v___y_3824_;
}
else
{
lean_object* v_pos_3825_; lean_object* v_snd_3826_; lean_object* v_snd_3827_; uint8_t v_decide_3828_; 
v_pos_3825_ = lean_ctor_get(v___y_3824_, 0);
v_snd_3826_ = lean_ctor_get(v_a_3812_, 1);
lean_inc(v_snd_3826_);
lean_dec_ref(v_a_3812_);
v_snd_3827_ = lean_ctor_get(v_pos_3825_, 1);
v_decide_3828_ = lean_nat_dec_eq(v_snd_3826_, v_snd_3827_);
lean_dec(v_snd_3826_);
if (v_decide_3828_ == 0)
{
return v___y_3824_;
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_inc(v_pos_3825_);
lean_dec_ref_known(v___y_3824_, 2);
v___x_3829_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
v___x_3830_ = l_Std_Internal_Parsec_String_pstring(v___x_3829_, v_pos_3825_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_pos_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3839_; 
v_pos_3831_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v___x_3830_, 1);
lean_dec(v_unused_3840_);
v___x_3833_ = v___x_3830_;
v_isShared_3834_ = v_isSharedCheck_3839_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_pos_3831_);
lean_dec(v___x_3830_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3839_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3835_; lean_object* v___x_3837_; 
v___x_3835_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 1, v___x_3835_);
v___x_3837_ = v___x_3833_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_pos_3831_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
else
{
lean_object* v_pos_3841_; lean_object* v_err_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
v_pos_3841_ = lean_ctor_get(v___x_3830_, 0);
v_err_3842_ = lean_ctor_get(v___x_3830_, 1);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3830_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_err_3842_);
lean_inc(v_pos_3841_);
lean_dec(v___x_3830_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_pos_3841_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_err_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(lean_object* v_dateformat_4544_, lean_object* v_date_4545_, lean_object* v_part_4546_){
_start:
{
if (lean_obj_tag(v_part_4546_) == 0)
{
lean_object* v_val_4547_; 
lean_dec_ref(v_date_4545_);
v_val_4547_ = lean_ctor_get(v_part_4546_, 0);
lean_inc_ref(v_val_4547_);
lean_dec_ref_known(v_part_4546_, 1);
return v_val_4547_;
}
else
{
lean_object* v_modifier_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v_modifier_4548_ = lean_ctor_get(v_part_4546_, 0);
lean_inc_ref(v_modifier_4548_);
lean_dec_ref_known(v_part_4546_, 1);
v___x_4549_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_4548_, v_dateformat_4544_, v_date_4545_);
v___x_4550_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_4544_, v_modifier_4548_, v___x_4549_);
return v___x_4550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate___boxed(lean_object* v_dateformat_4551_, lean_object* v_date_4552_, lean_object* v_part_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_4551_, v_date_4552_, v_part_4553_);
lean_dec_ref(v_dateformat_4551_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter___redArg(lean_object* v_x_4555_, lean_object* v_h__1_4556_, lean_object* v_h__2_4557_, lean_object* v_h__3_4558_){
_start:
{
if (lean_obj_tag(v_x_4555_) == 0)
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
lean_dec(v_h__2_4557_);
lean_dec(v_h__1_4556_);
v___x_4559_ = lean_box(0);
v___x_4560_ = lean_apply_1(v_h__3_4558_, v___x_4559_);
return v___x_4560_;
}
else
{
lean_object* v_head_4561_; 
lean_dec(v_h__3_4558_);
v_head_4561_ = lean_ctor_get(v_x_4555_, 0);
lean_inc(v_head_4561_);
if (lean_obj_tag(v_head_4561_) == 0)
{
lean_object* v_tail_4562_; lean_object* v_val_4563_; lean_object* v___x_4564_; 
lean_dec(v_h__1_4556_);
v_tail_4562_ = lean_ctor_get(v_x_4555_, 1);
lean_inc(v_tail_4562_);
lean_dec_ref_known(v_x_4555_, 2);
v_val_4563_ = lean_ctor_get(v_head_4561_, 0);
lean_inc_ref(v_val_4563_);
lean_dec_ref_known(v_head_4561_, 1);
v___x_4564_ = lean_apply_2(v_h__2_4557_, v_val_4563_, v_tail_4562_);
return v___x_4564_;
}
else
{
lean_object* v_tail_4565_; lean_object* v_modifier_4566_; lean_object* v___x_4567_; 
lean_dec(v_h__2_4557_);
v_tail_4565_ = lean_ctor_get(v_x_4555_, 1);
lean_inc(v_tail_4565_);
lean_dec_ref_known(v_x_4555_, 2);
v_modifier_4566_ = lean_ctor_get(v_head_4561_, 0);
lean_inc_ref(v_modifier_4566_);
lean_dec_ref_known(v_head_4561_, 1);
v___x_4567_ = lean_apply_2(v_h__1_4556_, v_modifier_4566_, v_tail_4565_);
return v___x_4567_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter(lean_object* v_motive_4568_, lean_object* v_x_4569_, lean_object* v_h__1_4570_, lean_object* v_h__2_4571_, lean_object* v_h__3_4572_){
_start:
{
if (lean_obj_tag(v_x_4569_) == 0)
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
lean_dec(v_h__2_4571_);
lean_dec(v_h__1_4570_);
v___x_4573_ = lean_box(0);
v___x_4574_ = lean_apply_1(v_h__3_4572_, v___x_4573_);
return v___x_4574_;
}
else
{
lean_object* v_head_4575_; 
lean_dec(v_h__3_4572_);
v_head_4575_ = lean_ctor_get(v_x_4569_, 0);
lean_inc(v_head_4575_);
if (lean_obj_tag(v_head_4575_) == 0)
{
lean_object* v_tail_4576_; lean_object* v_val_4577_; lean_object* v___x_4578_; 
lean_dec(v_h__1_4570_);
v_tail_4576_ = lean_ctor_get(v_x_4569_, 1);
lean_inc(v_tail_4576_);
lean_dec_ref_known(v_x_4569_, 2);
v_val_4577_ = lean_ctor_get(v_head_4575_, 0);
lean_inc_ref(v_val_4577_);
lean_dec_ref_known(v_head_4575_, 1);
v___x_4578_ = lean_apply_2(v_h__2_4571_, v_val_4577_, v_tail_4576_);
return v___x_4578_;
}
else
{
lean_object* v_tail_4579_; lean_object* v_modifier_4580_; lean_object* v___x_4581_; 
lean_dec(v_h__2_4571_);
v_tail_4579_ = lean_ctor_get(v_x_4569_, 1);
lean_inc(v_tail_4579_);
lean_dec_ref_known(v_x_4569_, 2);
v_modifier_4580_ = lean_ctor_get(v_head_4575_, 0);
lean_inc_ref(v_modifier_4580_);
lean_dec_ref_known(v_head_4575_, 1);
v___x_4581_ = lean_apply_2(v_h__1_4570_, v_modifier_4580_, v_tail_4579_);
return v___x_4581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object* v_date_4582_, lean_object* v_modifier_4583_, lean_object* v_data_4584_){
_start:
{
switch(lean_obj_tag(v_modifier_4583_))
{
case 0:
{
lean_object* v_y_4585_; lean_object* v_u_4586_; lean_object* v_Y_4587_; lean_object* v_D_4588_; lean_object* v_M_4589_; lean_object* v_L_4590_; lean_object* v_d_4591_; lean_object* v_Q_4592_; lean_object* v_q_4593_; lean_object* v_w_4594_; lean_object* v_W_4595_; lean_object* v_E_4596_; lean_object* v_e_4597_; lean_object* v_c_4598_; lean_object* v_F_4599_; lean_object* v_a_4600_; lean_object* v_b_4601_; lean_object* v_B_4602_; lean_object* v_h_4603_; lean_object* v_K_4604_; lean_object* v_k_4605_; lean_object* v_H_4606_; lean_object* v_m_4607_; lean_object* v_s_4608_; lean_object* v_S_4609_; lean_object* v_A_4610_; lean_object* v_n_4611_; lean_object* v_N_4612_; lean_object* v_V_4613_; lean_object* v_z_4614_; lean_object* v_zabbrev_4615_; lean_object* v_v_4616_; lean_object* v_O_4617_; lean_object* v_X_4618_; lean_object* v_x_4619_; lean_object* v_Z_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4628_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_y_4585_ = lean_ctor_get(v_date_4582_, 1);
v_u_4586_ = lean_ctor_get(v_date_4582_, 2);
v_Y_4587_ = lean_ctor_get(v_date_4582_, 3);
v_D_4588_ = lean_ctor_get(v_date_4582_, 4);
v_M_4589_ = lean_ctor_get(v_date_4582_, 5);
v_L_4590_ = lean_ctor_get(v_date_4582_, 6);
v_d_4591_ = lean_ctor_get(v_date_4582_, 7);
v_Q_4592_ = lean_ctor_get(v_date_4582_, 8);
v_q_4593_ = lean_ctor_get(v_date_4582_, 9);
v_w_4594_ = lean_ctor_get(v_date_4582_, 10);
v_W_4595_ = lean_ctor_get(v_date_4582_, 11);
v_E_4596_ = lean_ctor_get(v_date_4582_, 12);
v_e_4597_ = lean_ctor_get(v_date_4582_, 13);
v_c_4598_ = lean_ctor_get(v_date_4582_, 14);
v_F_4599_ = lean_ctor_get(v_date_4582_, 15);
v_a_4600_ = lean_ctor_get(v_date_4582_, 16);
v_b_4601_ = lean_ctor_get(v_date_4582_, 17);
v_B_4602_ = lean_ctor_get(v_date_4582_, 18);
v_h_4603_ = lean_ctor_get(v_date_4582_, 19);
v_K_4604_ = lean_ctor_get(v_date_4582_, 20);
v_k_4605_ = lean_ctor_get(v_date_4582_, 21);
v_H_4606_ = lean_ctor_get(v_date_4582_, 22);
v_m_4607_ = lean_ctor_get(v_date_4582_, 23);
v_s_4608_ = lean_ctor_get(v_date_4582_, 24);
v_S_4609_ = lean_ctor_get(v_date_4582_, 25);
v_A_4610_ = lean_ctor_get(v_date_4582_, 26);
v_n_4611_ = lean_ctor_get(v_date_4582_, 27);
v_N_4612_ = lean_ctor_get(v_date_4582_, 28);
v_V_4613_ = lean_ctor_get(v_date_4582_, 29);
v_z_4614_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_4615_ = lean_ctor_get(v_date_4582_, 31);
v_v_4616_ = lean_ctor_get(v_date_4582_, 32);
v_O_4617_ = lean_ctor_get(v_date_4582_, 33);
v_X_4618_ = lean_ctor_get(v_date_4582_, 34);
v_x_4619_ = lean_ctor_get(v_date_4582_, 35);
v_Z_4620_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_4628_ == 0)
{
lean_object* v_unused_4629_; 
v_unused_4629_ = lean_ctor_get(v_date_4582_, 0);
lean_dec(v_unused_4629_);
v___x_4622_ = v_date_4582_;
v_isShared_4623_ = v_isSharedCheck_4628_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_Z_4620_);
lean_inc(v_x_4619_);
lean_inc(v_X_4618_);
lean_inc(v_O_4617_);
lean_inc(v_v_4616_);
lean_inc(v_zabbrev_4615_);
lean_inc(v_z_4614_);
lean_inc(v_V_4613_);
lean_inc(v_N_4612_);
lean_inc(v_n_4611_);
lean_inc(v_A_4610_);
lean_inc(v_S_4609_);
lean_inc(v_s_4608_);
lean_inc(v_m_4607_);
lean_inc(v_H_4606_);
lean_inc(v_k_4605_);
lean_inc(v_K_4604_);
lean_inc(v_h_4603_);
lean_inc(v_B_4602_);
lean_inc(v_b_4601_);
lean_inc(v_a_4600_);
lean_inc(v_F_4599_);
lean_inc(v_c_4598_);
lean_inc(v_e_4597_);
lean_inc(v_E_4596_);
lean_inc(v_W_4595_);
lean_inc(v_w_4594_);
lean_inc(v_q_4593_);
lean_inc(v_Q_4592_);
lean_inc(v_d_4591_);
lean_inc(v_L_4590_);
lean_inc(v_M_4589_);
lean_inc(v_D_4588_);
lean_inc(v_Y_4587_);
lean_inc(v_u_4586_);
lean_inc(v_y_4585_);
lean_dec(v_date_4582_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4628_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4624_; lean_object* v___x_4626_; 
v___x_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4624_, 0, v_data_4584_);
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 0, v___x_4624_);
v___x_4626_ = v___x_4622_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4627_, 1, v_y_4585_);
lean_ctor_set(v_reuseFailAlloc_4627_, 2, v_u_4586_);
lean_ctor_set(v_reuseFailAlloc_4627_, 3, v_Y_4587_);
lean_ctor_set(v_reuseFailAlloc_4627_, 4, v_D_4588_);
lean_ctor_set(v_reuseFailAlloc_4627_, 5, v_M_4589_);
lean_ctor_set(v_reuseFailAlloc_4627_, 6, v_L_4590_);
lean_ctor_set(v_reuseFailAlloc_4627_, 7, v_d_4591_);
lean_ctor_set(v_reuseFailAlloc_4627_, 8, v_Q_4592_);
lean_ctor_set(v_reuseFailAlloc_4627_, 9, v_q_4593_);
lean_ctor_set(v_reuseFailAlloc_4627_, 10, v_w_4594_);
lean_ctor_set(v_reuseFailAlloc_4627_, 11, v_W_4595_);
lean_ctor_set(v_reuseFailAlloc_4627_, 12, v_E_4596_);
lean_ctor_set(v_reuseFailAlloc_4627_, 13, v_e_4597_);
lean_ctor_set(v_reuseFailAlloc_4627_, 14, v_c_4598_);
lean_ctor_set(v_reuseFailAlloc_4627_, 15, v_F_4599_);
lean_ctor_set(v_reuseFailAlloc_4627_, 16, v_a_4600_);
lean_ctor_set(v_reuseFailAlloc_4627_, 17, v_b_4601_);
lean_ctor_set(v_reuseFailAlloc_4627_, 18, v_B_4602_);
lean_ctor_set(v_reuseFailAlloc_4627_, 19, v_h_4603_);
lean_ctor_set(v_reuseFailAlloc_4627_, 20, v_K_4604_);
lean_ctor_set(v_reuseFailAlloc_4627_, 21, v_k_4605_);
lean_ctor_set(v_reuseFailAlloc_4627_, 22, v_H_4606_);
lean_ctor_set(v_reuseFailAlloc_4627_, 23, v_m_4607_);
lean_ctor_set(v_reuseFailAlloc_4627_, 24, v_s_4608_);
lean_ctor_set(v_reuseFailAlloc_4627_, 25, v_S_4609_);
lean_ctor_set(v_reuseFailAlloc_4627_, 26, v_A_4610_);
lean_ctor_set(v_reuseFailAlloc_4627_, 27, v_n_4611_);
lean_ctor_set(v_reuseFailAlloc_4627_, 28, v_N_4612_);
lean_ctor_set(v_reuseFailAlloc_4627_, 29, v_V_4613_);
lean_ctor_set(v_reuseFailAlloc_4627_, 30, v_z_4614_);
lean_ctor_set(v_reuseFailAlloc_4627_, 31, v_zabbrev_4615_);
lean_ctor_set(v_reuseFailAlloc_4627_, 32, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4627_, 33, v_O_4617_);
lean_ctor_set(v_reuseFailAlloc_4627_, 34, v_X_4618_);
lean_ctor_set(v_reuseFailAlloc_4627_, 35, v_x_4619_);
lean_ctor_set(v_reuseFailAlloc_4627_, 36, v_Z_4620_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
case 1:
{
lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4680_; 
v_isSharedCheck_4680_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_4680_ == 0)
{
lean_object* v_unused_4681_; 
v_unused_4681_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_4681_);
v___x_4631_ = v_modifier_4583_;
v_isShared_4632_ = v_isSharedCheck_4680_;
goto v_resetjp_4630_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4680_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v_G_4633_; lean_object* v_y_4634_; lean_object* v_Y_4635_; lean_object* v_D_4636_; lean_object* v_M_4637_; lean_object* v_L_4638_; lean_object* v_d_4639_; lean_object* v_Q_4640_; lean_object* v_q_4641_; lean_object* v_w_4642_; lean_object* v_W_4643_; lean_object* v_E_4644_; lean_object* v_e_4645_; lean_object* v_c_4646_; lean_object* v_F_4647_; lean_object* v_a_4648_; lean_object* v_b_4649_; lean_object* v_B_4650_; lean_object* v_h_4651_; lean_object* v_K_4652_; lean_object* v_k_4653_; lean_object* v_H_4654_; lean_object* v_m_4655_; lean_object* v_s_4656_; lean_object* v_S_4657_; lean_object* v_A_4658_; lean_object* v_n_4659_; lean_object* v_N_4660_; lean_object* v_V_4661_; lean_object* v_z_4662_; lean_object* v_zabbrev_4663_; lean_object* v_v_4664_; lean_object* v_O_4665_; lean_object* v_X_4666_; lean_object* v_x_4667_; lean_object* v_Z_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4678_; 
v_G_4633_ = lean_ctor_get(v_date_4582_, 0);
v_y_4634_ = lean_ctor_get(v_date_4582_, 1);
v_Y_4635_ = lean_ctor_get(v_date_4582_, 3);
v_D_4636_ = lean_ctor_get(v_date_4582_, 4);
v_M_4637_ = lean_ctor_get(v_date_4582_, 5);
v_L_4638_ = lean_ctor_get(v_date_4582_, 6);
v_d_4639_ = lean_ctor_get(v_date_4582_, 7);
v_Q_4640_ = lean_ctor_get(v_date_4582_, 8);
v_q_4641_ = lean_ctor_get(v_date_4582_, 9);
v_w_4642_ = lean_ctor_get(v_date_4582_, 10);
v_W_4643_ = lean_ctor_get(v_date_4582_, 11);
v_E_4644_ = lean_ctor_get(v_date_4582_, 12);
v_e_4645_ = lean_ctor_get(v_date_4582_, 13);
v_c_4646_ = lean_ctor_get(v_date_4582_, 14);
v_F_4647_ = lean_ctor_get(v_date_4582_, 15);
v_a_4648_ = lean_ctor_get(v_date_4582_, 16);
v_b_4649_ = lean_ctor_get(v_date_4582_, 17);
v_B_4650_ = lean_ctor_get(v_date_4582_, 18);
v_h_4651_ = lean_ctor_get(v_date_4582_, 19);
v_K_4652_ = lean_ctor_get(v_date_4582_, 20);
v_k_4653_ = lean_ctor_get(v_date_4582_, 21);
v_H_4654_ = lean_ctor_get(v_date_4582_, 22);
v_m_4655_ = lean_ctor_get(v_date_4582_, 23);
v_s_4656_ = lean_ctor_get(v_date_4582_, 24);
v_S_4657_ = lean_ctor_get(v_date_4582_, 25);
v_A_4658_ = lean_ctor_get(v_date_4582_, 26);
v_n_4659_ = lean_ctor_get(v_date_4582_, 27);
v_N_4660_ = lean_ctor_get(v_date_4582_, 28);
v_V_4661_ = lean_ctor_get(v_date_4582_, 29);
v_z_4662_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_4663_ = lean_ctor_get(v_date_4582_, 31);
v_v_4664_ = lean_ctor_get(v_date_4582_, 32);
v_O_4665_ = lean_ctor_get(v_date_4582_, 33);
v_X_4666_ = lean_ctor_get(v_date_4582_, 34);
v_x_4667_ = lean_ctor_get(v_date_4582_, 35);
v_Z_4668_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_4678_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_4678_ == 0)
{
lean_object* v_unused_4679_; 
v_unused_4679_ = lean_ctor_get(v_date_4582_, 2);
lean_dec(v_unused_4679_);
v___x_4670_ = v_date_4582_;
v_isShared_4671_ = v_isSharedCheck_4678_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_Z_4668_);
lean_inc(v_x_4667_);
lean_inc(v_X_4666_);
lean_inc(v_O_4665_);
lean_inc(v_v_4664_);
lean_inc(v_zabbrev_4663_);
lean_inc(v_z_4662_);
lean_inc(v_V_4661_);
lean_inc(v_N_4660_);
lean_inc(v_n_4659_);
lean_inc(v_A_4658_);
lean_inc(v_S_4657_);
lean_inc(v_s_4656_);
lean_inc(v_m_4655_);
lean_inc(v_H_4654_);
lean_inc(v_k_4653_);
lean_inc(v_K_4652_);
lean_inc(v_h_4651_);
lean_inc(v_B_4650_);
lean_inc(v_b_4649_);
lean_inc(v_a_4648_);
lean_inc(v_F_4647_);
lean_inc(v_c_4646_);
lean_inc(v_e_4645_);
lean_inc(v_E_4644_);
lean_inc(v_W_4643_);
lean_inc(v_w_4642_);
lean_inc(v_q_4641_);
lean_inc(v_Q_4640_);
lean_inc(v_d_4639_);
lean_inc(v_L_4638_);
lean_inc(v_M_4637_);
lean_inc(v_D_4636_);
lean_inc(v_Y_4635_);
lean_inc(v_y_4634_);
lean_inc(v_G_4633_);
lean_dec(v_date_4582_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4678_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 0, v_data_4584_);
v___x_4673_ = v___x_4631_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_data_4584_);
v___x_4673_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
lean_object* v___x_4675_; 
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 2, v___x_4673_);
v___x_4675_ = v___x_4670_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_G_4633_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_y_4634_);
lean_ctor_set(v_reuseFailAlloc_4676_, 2, v___x_4673_);
lean_ctor_set(v_reuseFailAlloc_4676_, 3, v_Y_4635_);
lean_ctor_set(v_reuseFailAlloc_4676_, 4, v_D_4636_);
lean_ctor_set(v_reuseFailAlloc_4676_, 5, v_M_4637_);
lean_ctor_set(v_reuseFailAlloc_4676_, 6, v_L_4638_);
lean_ctor_set(v_reuseFailAlloc_4676_, 7, v_d_4639_);
lean_ctor_set(v_reuseFailAlloc_4676_, 8, v_Q_4640_);
lean_ctor_set(v_reuseFailAlloc_4676_, 9, v_q_4641_);
lean_ctor_set(v_reuseFailAlloc_4676_, 10, v_w_4642_);
lean_ctor_set(v_reuseFailAlloc_4676_, 11, v_W_4643_);
lean_ctor_set(v_reuseFailAlloc_4676_, 12, v_E_4644_);
lean_ctor_set(v_reuseFailAlloc_4676_, 13, v_e_4645_);
lean_ctor_set(v_reuseFailAlloc_4676_, 14, v_c_4646_);
lean_ctor_set(v_reuseFailAlloc_4676_, 15, v_F_4647_);
lean_ctor_set(v_reuseFailAlloc_4676_, 16, v_a_4648_);
lean_ctor_set(v_reuseFailAlloc_4676_, 17, v_b_4649_);
lean_ctor_set(v_reuseFailAlloc_4676_, 18, v_B_4650_);
lean_ctor_set(v_reuseFailAlloc_4676_, 19, v_h_4651_);
lean_ctor_set(v_reuseFailAlloc_4676_, 20, v_K_4652_);
lean_ctor_set(v_reuseFailAlloc_4676_, 21, v_k_4653_);
lean_ctor_set(v_reuseFailAlloc_4676_, 22, v_H_4654_);
lean_ctor_set(v_reuseFailAlloc_4676_, 23, v_m_4655_);
lean_ctor_set(v_reuseFailAlloc_4676_, 24, v_s_4656_);
lean_ctor_set(v_reuseFailAlloc_4676_, 25, v_S_4657_);
lean_ctor_set(v_reuseFailAlloc_4676_, 26, v_A_4658_);
lean_ctor_set(v_reuseFailAlloc_4676_, 27, v_n_4659_);
lean_ctor_set(v_reuseFailAlloc_4676_, 28, v_N_4660_);
lean_ctor_set(v_reuseFailAlloc_4676_, 29, v_V_4661_);
lean_ctor_set(v_reuseFailAlloc_4676_, 30, v_z_4662_);
lean_ctor_set(v_reuseFailAlloc_4676_, 31, v_zabbrev_4663_);
lean_ctor_set(v_reuseFailAlloc_4676_, 32, v_v_4664_);
lean_ctor_set(v_reuseFailAlloc_4676_, 33, v_O_4665_);
lean_ctor_set(v_reuseFailAlloc_4676_, 34, v_X_4666_);
lean_ctor_set(v_reuseFailAlloc_4676_, 35, v_x_4667_);
lean_ctor_set(v_reuseFailAlloc_4676_, 36, v_Z_4668_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
}
case 2:
{
lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4732_; 
v_isSharedCheck_4732_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_4732_ == 0)
{
lean_object* v_unused_4733_; 
v_unused_4733_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_4733_);
v___x_4683_ = v_modifier_4583_;
v_isShared_4684_ = v_isSharedCheck_4732_;
goto v_resetjp_4682_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4732_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v_G_4685_; lean_object* v_u_4686_; lean_object* v_Y_4687_; lean_object* v_D_4688_; lean_object* v_M_4689_; lean_object* v_L_4690_; lean_object* v_d_4691_; lean_object* v_Q_4692_; lean_object* v_q_4693_; lean_object* v_w_4694_; lean_object* v_W_4695_; lean_object* v_E_4696_; lean_object* v_e_4697_; lean_object* v_c_4698_; lean_object* v_F_4699_; lean_object* v_a_4700_; lean_object* v_b_4701_; lean_object* v_B_4702_; lean_object* v_h_4703_; lean_object* v_K_4704_; lean_object* v_k_4705_; lean_object* v_H_4706_; lean_object* v_m_4707_; lean_object* v_s_4708_; lean_object* v_S_4709_; lean_object* v_A_4710_; lean_object* v_n_4711_; lean_object* v_N_4712_; lean_object* v_V_4713_; lean_object* v_z_4714_; lean_object* v_zabbrev_4715_; lean_object* v_v_4716_; lean_object* v_O_4717_; lean_object* v_X_4718_; lean_object* v_x_4719_; lean_object* v_Z_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4730_; 
v_G_4685_ = lean_ctor_get(v_date_4582_, 0);
v_u_4686_ = lean_ctor_get(v_date_4582_, 2);
v_Y_4687_ = lean_ctor_get(v_date_4582_, 3);
v_D_4688_ = lean_ctor_get(v_date_4582_, 4);
v_M_4689_ = lean_ctor_get(v_date_4582_, 5);
v_L_4690_ = lean_ctor_get(v_date_4582_, 6);
v_d_4691_ = lean_ctor_get(v_date_4582_, 7);
v_Q_4692_ = lean_ctor_get(v_date_4582_, 8);
v_q_4693_ = lean_ctor_get(v_date_4582_, 9);
v_w_4694_ = lean_ctor_get(v_date_4582_, 10);
v_W_4695_ = lean_ctor_get(v_date_4582_, 11);
v_E_4696_ = lean_ctor_get(v_date_4582_, 12);
v_e_4697_ = lean_ctor_get(v_date_4582_, 13);
v_c_4698_ = lean_ctor_get(v_date_4582_, 14);
v_F_4699_ = lean_ctor_get(v_date_4582_, 15);
v_a_4700_ = lean_ctor_get(v_date_4582_, 16);
v_b_4701_ = lean_ctor_get(v_date_4582_, 17);
v_B_4702_ = lean_ctor_get(v_date_4582_, 18);
v_h_4703_ = lean_ctor_get(v_date_4582_, 19);
v_K_4704_ = lean_ctor_get(v_date_4582_, 20);
v_k_4705_ = lean_ctor_get(v_date_4582_, 21);
v_H_4706_ = lean_ctor_get(v_date_4582_, 22);
v_m_4707_ = lean_ctor_get(v_date_4582_, 23);
v_s_4708_ = lean_ctor_get(v_date_4582_, 24);
v_S_4709_ = lean_ctor_get(v_date_4582_, 25);
v_A_4710_ = lean_ctor_get(v_date_4582_, 26);
v_n_4711_ = lean_ctor_get(v_date_4582_, 27);
v_N_4712_ = lean_ctor_get(v_date_4582_, 28);
v_V_4713_ = lean_ctor_get(v_date_4582_, 29);
v_z_4714_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_4715_ = lean_ctor_get(v_date_4582_, 31);
v_v_4716_ = lean_ctor_get(v_date_4582_, 32);
v_O_4717_ = lean_ctor_get(v_date_4582_, 33);
v_X_4718_ = lean_ctor_get(v_date_4582_, 34);
v_x_4719_ = lean_ctor_get(v_date_4582_, 35);
v_Z_4720_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_4730_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_4730_ == 0)
{
lean_object* v_unused_4731_; 
v_unused_4731_ = lean_ctor_get(v_date_4582_, 1);
lean_dec(v_unused_4731_);
v___x_4722_ = v_date_4582_;
v_isShared_4723_ = v_isSharedCheck_4730_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_Z_4720_);
lean_inc(v_x_4719_);
lean_inc(v_X_4718_);
lean_inc(v_O_4717_);
lean_inc(v_v_4716_);
lean_inc(v_zabbrev_4715_);
lean_inc(v_z_4714_);
lean_inc(v_V_4713_);
lean_inc(v_N_4712_);
lean_inc(v_n_4711_);
lean_inc(v_A_4710_);
lean_inc(v_S_4709_);
lean_inc(v_s_4708_);
lean_inc(v_m_4707_);
lean_inc(v_H_4706_);
lean_inc(v_k_4705_);
lean_inc(v_K_4704_);
lean_inc(v_h_4703_);
lean_inc(v_B_4702_);
lean_inc(v_b_4701_);
lean_inc(v_a_4700_);
lean_inc(v_F_4699_);
lean_inc(v_c_4698_);
lean_inc(v_e_4697_);
lean_inc(v_E_4696_);
lean_inc(v_W_4695_);
lean_inc(v_w_4694_);
lean_inc(v_q_4693_);
lean_inc(v_Q_4692_);
lean_inc(v_d_4691_);
lean_inc(v_L_4690_);
lean_inc(v_M_4689_);
lean_inc(v_D_4688_);
lean_inc(v_Y_4687_);
lean_inc(v_u_4686_);
lean_inc(v_G_4685_);
lean_dec(v_date_4582_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4730_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4684_ == 0)
{
lean_ctor_set_tag(v___x_4683_, 1);
lean_ctor_set(v___x_4683_, 0, v_data_4584_);
v___x_4725_ = v___x_4683_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_data_4584_);
v___x_4725_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4727_; 
if (v_isShared_4723_ == 0)
{
lean_ctor_set(v___x_4722_, 1, v___x_4725_);
v___x_4727_ = v___x_4722_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_G_4685_);
lean_ctor_set(v_reuseFailAlloc_4728_, 1, v___x_4725_);
lean_ctor_set(v_reuseFailAlloc_4728_, 2, v_u_4686_);
lean_ctor_set(v_reuseFailAlloc_4728_, 3, v_Y_4687_);
lean_ctor_set(v_reuseFailAlloc_4728_, 4, v_D_4688_);
lean_ctor_set(v_reuseFailAlloc_4728_, 5, v_M_4689_);
lean_ctor_set(v_reuseFailAlloc_4728_, 6, v_L_4690_);
lean_ctor_set(v_reuseFailAlloc_4728_, 7, v_d_4691_);
lean_ctor_set(v_reuseFailAlloc_4728_, 8, v_Q_4692_);
lean_ctor_set(v_reuseFailAlloc_4728_, 9, v_q_4693_);
lean_ctor_set(v_reuseFailAlloc_4728_, 10, v_w_4694_);
lean_ctor_set(v_reuseFailAlloc_4728_, 11, v_W_4695_);
lean_ctor_set(v_reuseFailAlloc_4728_, 12, v_E_4696_);
lean_ctor_set(v_reuseFailAlloc_4728_, 13, v_e_4697_);
lean_ctor_set(v_reuseFailAlloc_4728_, 14, v_c_4698_);
lean_ctor_set(v_reuseFailAlloc_4728_, 15, v_F_4699_);
lean_ctor_set(v_reuseFailAlloc_4728_, 16, v_a_4700_);
lean_ctor_set(v_reuseFailAlloc_4728_, 17, v_b_4701_);
lean_ctor_set(v_reuseFailAlloc_4728_, 18, v_B_4702_);
lean_ctor_set(v_reuseFailAlloc_4728_, 19, v_h_4703_);
lean_ctor_set(v_reuseFailAlloc_4728_, 20, v_K_4704_);
lean_ctor_set(v_reuseFailAlloc_4728_, 21, v_k_4705_);
lean_ctor_set(v_reuseFailAlloc_4728_, 22, v_H_4706_);
lean_ctor_set(v_reuseFailAlloc_4728_, 23, v_m_4707_);
lean_ctor_set(v_reuseFailAlloc_4728_, 24, v_s_4708_);
lean_ctor_set(v_reuseFailAlloc_4728_, 25, v_S_4709_);
lean_ctor_set(v_reuseFailAlloc_4728_, 26, v_A_4710_);
lean_ctor_set(v_reuseFailAlloc_4728_, 27, v_n_4711_);
lean_ctor_set(v_reuseFailAlloc_4728_, 28, v_N_4712_);
lean_ctor_set(v_reuseFailAlloc_4728_, 29, v_V_4713_);
lean_ctor_set(v_reuseFailAlloc_4728_, 30, v_z_4714_);
lean_ctor_set(v_reuseFailAlloc_4728_, 31, v_zabbrev_4715_);
lean_ctor_set(v_reuseFailAlloc_4728_, 32, v_v_4716_);
lean_ctor_set(v_reuseFailAlloc_4728_, 33, v_O_4717_);
lean_ctor_set(v_reuseFailAlloc_4728_, 34, v_X_4718_);
lean_ctor_set(v_reuseFailAlloc_4728_, 35, v_x_4719_);
lean_ctor_set(v_reuseFailAlloc_4728_, 36, v_Z_4720_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
}
case 3:
{
lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4784_; 
v_isSharedCheck_4784_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_4784_ == 0)
{
lean_object* v_unused_4785_; 
v_unused_4785_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_4785_);
v___x_4735_ = v_modifier_4583_;
v_isShared_4736_ = v_isSharedCheck_4784_;
goto v_resetjp_4734_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4784_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v_G_4737_; lean_object* v_y_4738_; lean_object* v_u_4739_; lean_object* v_Y_4740_; lean_object* v_M_4741_; lean_object* v_L_4742_; lean_object* v_d_4743_; lean_object* v_Q_4744_; lean_object* v_q_4745_; lean_object* v_w_4746_; lean_object* v_W_4747_; lean_object* v_E_4748_; lean_object* v_e_4749_; lean_object* v_c_4750_; lean_object* v_F_4751_; lean_object* v_a_4752_; lean_object* v_b_4753_; lean_object* v_B_4754_; lean_object* v_h_4755_; lean_object* v_K_4756_; lean_object* v_k_4757_; lean_object* v_H_4758_; lean_object* v_m_4759_; lean_object* v_s_4760_; lean_object* v_S_4761_; lean_object* v_A_4762_; lean_object* v_n_4763_; lean_object* v_N_4764_; lean_object* v_V_4765_; lean_object* v_z_4766_; lean_object* v_zabbrev_4767_; lean_object* v_v_4768_; lean_object* v_O_4769_; lean_object* v_X_4770_; lean_object* v_x_4771_; lean_object* v_Z_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4782_; 
v_G_4737_ = lean_ctor_get(v_date_4582_, 0);
v_y_4738_ = lean_ctor_get(v_date_4582_, 1);
v_u_4739_ = lean_ctor_get(v_date_4582_, 2);
v_Y_4740_ = lean_ctor_get(v_date_4582_, 3);
v_M_4741_ = lean_ctor_get(v_date_4582_, 5);
v_L_4742_ = lean_ctor_get(v_date_4582_, 6);
v_d_4743_ = lean_ctor_get(v_date_4582_, 7);
v_Q_4744_ = lean_ctor_get(v_date_4582_, 8);
v_q_4745_ = lean_ctor_get(v_date_4582_, 9);
v_w_4746_ = lean_ctor_get(v_date_4582_, 10);
v_W_4747_ = lean_ctor_get(v_date_4582_, 11);
v_E_4748_ = lean_ctor_get(v_date_4582_, 12);
v_e_4749_ = lean_ctor_get(v_date_4582_, 13);
v_c_4750_ = lean_ctor_get(v_date_4582_, 14);
v_F_4751_ = lean_ctor_get(v_date_4582_, 15);
v_a_4752_ = lean_ctor_get(v_date_4582_, 16);
v_b_4753_ = lean_ctor_get(v_date_4582_, 17);
v_B_4754_ = lean_ctor_get(v_date_4582_, 18);
v_h_4755_ = lean_ctor_get(v_date_4582_, 19);
v_K_4756_ = lean_ctor_get(v_date_4582_, 20);
v_k_4757_ = lean_ctor_get(v_date_4582_, 21);
v_H_4758_ = lean_ctor_get(v_date_4582_, 22);
v_m_4759_ = lean_ctor_get(v_date_4582_, 23);
v_s_4760_ = lean_ctor_get(v_date_4582_, 24);
v_S_4761_ = lean_ctor_get(v_date_4582_, 25);
v_A_4762_ = lean_ctor_get(v_date_4582_, 26);
v_n_4763_ = lean_ctor_get(v_date_4582_, 27);
v_N_4764_ = lean_ctor_get(v_date_4582_, 28);
v_V_4765_ = lean_ctor_get(v_date_4582_, 29);
v_z_4766_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_4767_ = lean_ctor_get(v_date_4582_, 31);
v_v_4768_ = lean_ctor_get(v_date_4582_, 32);
v_O_4769_ = lean_ctor_get(v_date_4582_, 33);
v_X_4770_ = lean_ctor_get(v_date_4582_, 34);
v_x_4771_ = lean_ctor_get(v_date_4582_, 35);
v_Z_4772_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_4782_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_4782_ == 0)
{
lean_object* v_unused_4783_; 
v_unused_4783_ = lean_ctor_get(v_date_4582_, 4);
lean_dec(v_unused_4783_);
v___x_4774_ = v_date_4582_;
v_isShared_4775_ = v_isSharedCheck_4782_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_Z_4772_);
lean_inc(v_x_4771_);
lean_inc(v_X_4770_);
lean_inc(v_O_4769_);
lean_inc(v_v_4768_);
lean_inc(v_zabbrev_4767_);
lean_inc(v_z_4766_);
lean_inc(v_V_4765_);
lean_inc(v_N_4764_);
lean_inc(v_n_4763_);
lean_inc(v_A_4762_);
lean_inc(v_S_4761_);
lean_inc(v_s_4760_);
lean_inc(v_m_4759_);
lean_inc(v_H_4758_);
lean_inc(v_k_4757_);
lean_inc(v_K_4756_);
lean_inc(v_h_4755_);
lean_inc(v_B_4754_);
lean_inc(v_b_4753_);
lean_inc(v_a_4752_);
lean_inc(v_F_4751_);
lean_inc(v_c_4750_);
lean_inc(v_e_4749_);
lean_inc(v_E_4748_);
lean_inc(v_W_4747_);
lean_inc(v_w_4746_);
lean_inc(v_q_4745_);
lean_inc(v_Q_4744_);
lean_inc(v_d_4743_);
lean_inc(v_L_4742_);
lean_inc(v_M_4741_);
lean_inc(v_Y_4740_);
lean_inc(v_u_4739_);
lean_inc(v_y_4738_);
lean_inc(v_G_4737_);
lean_dec(v_date_4582_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4782_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4777_; 
if (v_isShared_4736_ == 0)
{
lean_ctor_set_tag(v___x_4735_, 1);
lean_ctor_set(v___x_4735_, 0, v_data_4584_);
v___x_4777_ = v___x_4735_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_data_4584_);
v___x_4777_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
lean_object* v___x_4779_; 
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 4, v___x_4777_);
v___x_4779_ = v___x_4774_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_G_4737_);
lean_ctor_set(v_reuseFailAlloc_4780_, 1, v_y_4738_);
lean_ctor_set(v_reuseFailAlloc_4780_, 2, v_u_4739_);
lean_ctor_set(v_reuseFailAlloc_4780_, 3, v_Y_4740_);
lean_ctor_set(v_reuseFailAlloc_4780_, 4, v___x_4777_);
lean_ctor_set(v_reuseFailAlloc_4780_, 5, v_M_4741_);
lean_ctor_set(v_reuseFailAlloc_4780_, 6, v_L_4742_);
lean_ctor_set(v_reuseFailAlloc_4780_, 7, v_d_4743_);
lean_ctor_set(v_reuseFailAlloc_4780_, 8, v_Q_4744_);
lean_ctor_set(v_reuseFailAlloc_4780_, 9, v_q_4745_);
lean_ctor_set(v_reuseFailAlloc_4780_, 10, v_w_4746_);
lean_ctor_set(v_reuseFailAlloc_4780_, 11, v_W_4747_);
lean_ctor_set(v_reuseFailAlloc_4780_, 12, v_E_4748_);
lean_ctor_set(v_reuseFailAlloc_4780_, 13, v_e_4749_);
lean_ctor_set(v_reuseFailAlloc_4780_, 14, v_c_4750_);
lean_ctor_set(v_reuseFailAlloc_4780_, 15, v_F_4751_);
lean_ctor_set(v_reuseFailAlloc_4780_, 16, v_a_4752_);
lean_ctor_set(v_reuseFailAlloc_4780_, 17, v_b_4753_);
lean_ctor_set(v_reuseFailAlloc_4780_, 18, v_B_4754_);
lean_ctor_set(v_reuseFailAlloc_4780_, 19, v_h_4755_);
lean_ctor_set(v_reuseFailAlloc_4780_, 20, v_K_4756_);
lean_ctor_set(v_reuseFailAlloc_4780_, 21, v_k_4757_);
lean_ctor_set(v_reuseFailAlloc_4780_, 22, v_H_4758_);
lean_ctor_set(v_reuseFailAlloc_4780_, 23, v_m_4759_);
lean_ctor_set(v_reuseFailAlloc_4780_, 24, v_s_4760_);
lean_ctor_set(v_reuseFailAlloc_4780_, 25, v_S_4761_);
lean_ctor_set(v_reuseFailAlloc_4780_, 26, v_A_4762_);
lean_ctor_set(v_reuseFailAlloc_4780_, 27, v_n_4763_);
lean_ctor_set(v_reuseFailAlloc_4780_, 28, v_N_4764_);
lean_ctor_set(v_reuseFailAlloc_4780_, 29, v_V_4765_);
lean_ctor_set(v_reuseFailAlloc_4780_, 30, v_z_4766_);
lean_ctor_set(v_reuseFailAlloc_4780_, 31, v_zabbrev_4767_);
lean_ctor_set(v_reuseFailAlloc_4780_, 32, v_v_4768_);
lean_ctor_set(v_reuseFailAlloc_4780_, 33, v_O_4769_);
lean_ctor_set(v_reuseFailAlloc_4780_, 34, v_X_4770_);
lean_ctor_set(v_reuseFailAlloc_4780_, 35, v_x_4771_);
lean_ctor_set(v_reuseFailAlloc_4780_, 36, v_Z_4772_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
}
case 4:
{
lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4836_; 
v_isSharedCheck_4836_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_4836_ == 0)
{
lean_object* v_unused_4837_; 
v_unused_4837_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_4837_);
v___x_4787_ = v_modifier_4583_;
v_isShared_4788_ = v_isSharedCheck_4836_;
goto v_resetjp_4786_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4836_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v_G_4789_; lean_object* v_y_4790_; lean_object* v_u_4791_; lean_object* v_Y_4792_; lean_object* v_D_4793_; lean_object* v_L_4794_; lean_object* v_d_4795_; lean_object* v_Q_4796_; lean_object* v_q_4797_; lean_object* v_w_4798_; lean_object* v_W_4799_; lean_object* v_E_4800_; lean_object* v_e_4801_; lean_object* v_c_4802_; lean_object* v_F_4803_; lean_object* v_a_4804_; lean_object* v_b_4805_; lean_object* v_B_4806_; lean_object* v_h_4807_; lean_object* v_K_4808_; lean_object* v_k_4809_; lean_object* v_H_4810_; lean_object* v_m_4811_; lean_object* v_s_4812_; lean_object* v_S_4813_; lean_object* v_A_4814_; lean_object* v_n_4815_; lean_object* v_N_4816_; lean_object* v_V_4817_; lean_object* v_z_4818_; lean_object* v_zabbrev_4819_; lean_object* v_v_4820_; lean_object* v_O_4821_; lean_object* v_X_4822_; lean_object* v_x_4823_; lean_object* v_Z_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4834_; 
v_G_4789_ = lean_ctor_get(v_date_4582_, 0);
v_y_4790_ = lean_ctor_get(v_date_4582_, 1);
v_u_4791_ = lean_ctor_get(v_date_4582_, 2);
v_Y_4792_ = lean_ctor_get(v_date_4582_, 3);
v_D_4793_ = lean_ctor_get(v_date_4582_, 4);
v_L_4794_ = lean_ctor_get(v_date_4582_, 6);
v_d_4795_ = lean_ctor_get(v_date_4582_, 7);
v_Q_4796_ = lean_ctor_get(v_date_4582_, 8);
v_q_4797_ = lean_ctor_get(v_date_4582_, 9);
v_w_4798_ = lean_ctor_get(v_date_4582_, 10);
v_W_4799_ = lean_ctor_get(v_date_4582_, 11);
v_E_4800_ = lean_ctor_get(v_date_4582_, 12);
v_e_4801_ = lean_ctor_get(v_date_4582_, 13);
v_c_4802_ = lean_ctor_get(v_date_4582_, 14);
v_F_4803_ = lean_ctor_get(v_date_4582_, 15);
v_a_4804_ = lean_ctor_get(v_date_4582_, 16);
v_b_4805_ = lean_ctor_get(v_date_4582_, 17);
v_B_4806_ = lean_ctor_get(v_date_4582_, 18);
v_h_4807_ = lean_ctor_get(v_date_4582_, 19);
v_K_4808_ = lean_ctor_get(v_date_4582_, 20);
v_k_4809_ = lean_ctor_get(v_date_4582_, 21);
v_H_4810_ = lean_ctor_get(v_date_4582_, 22);
v_m_4811_ = lean_ctor_get(v_date_4582_, 23);
v_s_4812_ = lean_ctor_get(v_date_4582_, 24);
v_S_4813_ = lean_ctor_get(v_date_4582_, 25);
v_A_4814_ = lean_ctor_get(v_date_4582_, 26);
v_n_4815_ = lean_ctor_get(v_date_4582_, 27);
v_N_4816_ = lean_ctor_get(v_date_4582_, 28);
v_V_4817_ = lean_ctor_get(v_date_4582_, 29);
v_z_4818_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_4819_ = lean_ctor_get(v_date_4582_, 31);
v_v_4820_ = lean_ctor_get(v_date_4582_, 32);
v_O_4821_ = lean_ctor_get(v_date_4582_, 33);
v_X_4822_ = lean_ctor_get(v_date_4582_, 34);
v_x_4823_ = lean_ctor_get(v_date_4582_, 35);
v_Z_4824_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_4834_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_4834_ == 0)
{
lean_object* v_unused_4835_; 
v_unused_4835_ = lean_ctor_get(v_date_4582_, 5);
lean_dec(v_unused_4835_);
v___x_4826_ = v_date_4582_;
v_isShared_4827_ = v_isSharedCheck_4834_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_Z_4824_);
lean_inc(v_x_4823_);
lean_inc(v_X_4822_);
lean_inc(v_O_4821_);
lean_inc(v_v_4820_);
lean_inc(v_zabbrev_4819_);
lean_inc(v_z_4818_);
lean_inc(v_V_4817_);
lean_inc(v_N_4816_);
lean_inc(v_n_4815_);
lean_inc(v_A_4814_);
lean_inc(v_S_4813_);
lean_inc(v_s_4812_);
lean_inc(v_m_4811_);
lean_inc(v_H_4810_);
lean_inc(v_k_4809_);
lean_inc(v_K_4808_);
lean_inc(v_h_4807_);
lean_inc(v_B_4806_);
lean_inc(v_b_4805_);
lean_inc(v_a_4804_);
lean_inc(v_F_4803_);
lean_inc(v_c_4802_);
lean_inc(v_e_4801_);
lean_inc(v_E_4800_);
lean_inc(v_W_4799_);
lean_inc(v_w_4798_);
lean_inc(v_q_4797_);
lean_inc(v_Q_4796_);
lean_inc(v_d_4795_);
lean_inc(v_L_4794_);
lean_inc(v_D_4793_);
lean_inc(v_Y_4792_);
lean_inc(v_u_4791_);
lean_inc(v_y_4790_);
lean_inc(v_G_4789_);
lean_dec(v_date_4582_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4834_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4788_ == 0)
{
lean_ctor_set_tag(v___x_4787_, 1);
lean_ctor_set(v___x_4787_, 0, v_data_4584_);
v___x_4829_ = v___x_4787_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_data_4584_);
v___x_4829_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4831_; 
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 5, v___x_4829_);
v___x_4831_ = v___x_4826_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_G_4789_);
lean_ctor_set(v_reuseFailAlloc_4832_, 1, v_y_4790_);
lean_ctor_set(v_reuseFailAlloc_4832_, 2, v_u_4791_);
lean_ctor_set(v_reuseFailAlloc_4832_, 3, v_Y_4792_);
lean_ctor_set(v_reuseFailAlloc_4832_, 4, v_D_4793_);
lean_ctor_set(v_reuseFailAlloc_4832_, 5, v___x_4829_);
lean_ctor_set(v_reuseFailAlloc_4832_, 6, v_L_4794_);
lean_ctor_set(v_reuseFailAlloc_4832_, 7, v_d_4795_);
lean_ctor_set(v_reuseFailAlloc_4832_, 8, v_Q_4796_);
lean_ctor_set(v_reuseFailAlloc_4832_, 9, v_q_4797_);
lean_ctor_set(v_reuseFailAlloc_4832_, 10, v_w_4798_);
lean_ctor_set(v_reuseFailAlloc_4832_, 11, v_W_4799_);
lean_ctor_set(v_reuseFailAlloc_4832_, 12, v_E_4800_);
lean_ctor_set(v_reuseFailAlloc_4832_, 13, v_e_4801_);
lean_ctor_set(v_reuseFailAlloc_4832_, 14, v_c_4802_);
lean_ctor_set(v_reuseFailAlloc_4832_, 15, v_F_4803_);
lean_ctor_set(v_reuseFailAlloc_4832_, 16, v_a_4804_);
lean_ctor_set(v_reuseFailAlloc_4832_, 17, v_b_4805_);
lean_ctor_set(v_reuseFailAlloc_4832_, 18, v_B_4806_);
lean_ctor_set(v_reuseFailAlloc_4832_, 19, v_h_4807_);
lean_ctor_set(v_reuseFailAlloc_4832_, 20, v_K_4808_);
lean_ctor_set(v_reuseFailAlloc_4832_, 21, v_k_4809_);
lean_ctor_set(v_reuseFailAlloc_4832_, 22, v_H_4810_);
lean_ctor_set(v_reuseFailAlloc_4832_, 23, v_m_4811_);
lean_ctor_set(v_reuseFailAlloc_4832_, 24, v_s_4812_);
lean_ctor_set(v_reuseFailAlloc_4832_, 25, v_S_4813_);
lean_ctor_set(v_reuseFailAlloc_4832_, 26, v_A_4814_);
lean_ctor_set(v_reuseFailAlloc_4832_, 27, v_n_4815_);
lean_ctor_set(v_reuseFailAlloc_4832_, 28, v_N_4816_);
lean_ctor_set(v_reuseFailAlloc_4832_, 29, v_V_4817_);
lean_ctor_set(v_reuseFailAlloc_4832_, 30, v_z_4818_);
lean_ctor_set(v_reuseFailAlloc_4832_, 31, v_zabbrev_4819_);
lean_ctor_set(v_reuseFailAlloc_4832_, 32, v_v_4820_);
lean_ctor_set(v_reuseFailAlloc_4832_, 33, v_O_4821_);
lean_ctor_set(v_reuseFailAlloc_4832_, 34, v_X_4822_);
lean_ctor_set(v_reuseFailAlloc_4832_, 35, v_x_4823_);
lean_ctor_set(v_reuseFailAlloc_4832_, 36, v_Z_4824_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
}
case 5:
{
lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4888_; 
v_isSharedCheck_4888_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_4888_ == 0)
{
lean_object* v_unused_4889_; 
v_unused_4889_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_4889_);
v___x_4839_ = v_modifier_4583_;
v_isShared_4840_ = v_isSharedCheck_4888_;
goto v_resetjp_4838_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4888_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v_G_4841_; lean_object* v_y_4842_; lean_object* v_u_4843_; lean_object* v_Y_4844_; lean_object* v_D_4845_; lean_object* v_M_4846_; lean_object* v_d_4847_; lean_object* v_Q_4848_; lean_object* v_q_4849_; lean_object* v_w_4850_; lean_object* v_W_4851_; lean_object* v_E_4852_; lean_object* v_e_4853_; lean_object* v_c_4854_; lean_object* v_F_4855_; lean_object* v_a_4856_; lean_object* v_b_4857_; lean_object* v_B_4858_; lean_object* v_h_4859_; lean_object* v_K_4860_; lean_object* v_k_4861_; lean_object* v_H_4862_; lean_object* v_m_4863_; lean_object* v_s_4864_; lean_object* v_S_4865_; lean_object* v_A_4866_; lean_object* v_n_4867_; lean_object* v_N_4868_; lean_object* v_V_4869_; lean_object* v_z_4870_; lean_object* v_zabbrev_4871_; lean_object* v_v_4872_; lean_object* v_O_4873_; lean_object* v_X_4874_; lean_object* v_x_4875_; lean_object* v_Z_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4886_; 
v_G_4841_ = lean_ctor_get(v_date_4582_, 0);
v_y_4842_ = lean_ctor_get(v_date_4582_, 1);
v_u_4843_ = lean_ctor_get(v_date_4582_, 2);
v_Y_4844_ = lean_ctor_get(v_date_4582_, 3);
v_D_4845_ = lean_ctor_get(v_date_4582_, 4);
v_M_4846_ = lean_ctor_get(v_date_4582_, 5);
v_d_4847_ = lean_ctor_get(v_date_4582_, 7);
v_Q_4848_ = lean_ctor_get(v_date_4582_, 8);
v_q_4849_ = lean_ctor_get(v_date_4582_, 9);
v_w_4850_ = lean_ctor_get(v_date_4582_, 10);
v_W_4851_ = lean_ctor_get(v_date_4582_, 11);
v_E_4852_ = lean_ctor_get(v_date_4582_, 12);
v_e_4853_ = lean_ctor_get(v_date_4582_, 13);
v_c_4854_ = lean_ctor_get(v_date_4582_, 14);
v_F_4855_ = lean_ctor_get(v_date_4582_, 15);
v_a_4856_ = lean_ctor_get(v_date_4582_, 16);
v_b_4857_ = lean_ctor_get(v_date_4582_, 17);
v_B_4858_ = lean_ctor_get(v_date_4582_, 18);
v_h_4859_ = lean_ctor_get(v_date_4582_, 19);
v_K_4860_ = lean_ctor_get(v_date_4582_, 20);
v_k_4861_ = lean_ctor_get(v_date_4582_, 21);
v_H_4862_ = lean_ctor_get(v_date_4582_, 22);
v_m_4863_ = lean_ctor_get(v_date_4582_, 23);
v_s_4864_ = lean_ctor_get(v_date_4582_, 24);
v_S_4865_ = lean_ctor_get(v_date_4582_, 25);
v_A_4866_ = lean_ctor_get(v_date_4582_, 26);
v_n_4867_ = lean_ctor_get(v_date_4582_, 27);
v_N_4868_ = lean_ctor_get(v_date_4582_, 28);
v_V_4869_ = lean_ctor_get(v_date_4582_, 29);
v_z_4870_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_4871_ = lean_ctor_get(v_date_4582_, 31);
v_v_4872_ = lean_ctor_get(v_date_4582_, 32);
v_O_4873_ = lean_ctor_get(v_date_4582_, 33);
v_X_4874_ = lean_ctor_get(v_date_4582_, 34);
v_x_4875_ = lean_ctor_get(v_date_4582_, 35);
v_Z_4876_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_4886_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_4886_ == 0)
{
lean_object* v_unused_4887_; 
v_unused_4887_ = lean_ctor_get(v_date_4582_, 6);
lean_dec(v_unused_4887_);
v___x_4878_ = v_date_4582_;
v_isShared_4879_ = v_isSharedCheck_4886_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_Z_4876_);
lean_inc(v_x_4875_);
lean_inc(v_X_4874_);
lean_inc(v_O_4873_);
lean_inc(v_v_4872_);
lean_inc(v_zabbrev_4871_);
lean_inc(v_z_4870_);
lean_inc(v_V_4869_);
lean_inc(v_N_4868_);
lean_inc(v_n_4867_);
lean_inc(v_A_4866_);
lean_inc(v_S_4865_);
lean_inc(v_s_4864_);
lean_inc(v_m_4863_);
lean_inc(v_H_4862_);
lean_inc(v_k_4861_);
lean_inc(v_K_4860_);
lean_inc(v_h_4859_);
lean_inc(v_B_4858_);
lean_inc(v_b_4857_);
lean_inc(v_a_4856_);
lean_inc(v_F_4855_);
lean_inc(v_c_4854_);
lean_inc(v_e_4853_);
lean_inc(v_E_4852_);
lean_inc(v_W_4851_);
lean_inc(v_w_4850_);
lean_inc(v_q_4849_);
lean_inc(v_Q_4848_);
lean_inc(v_d_4847_);
lean_inc(v_M_4846_);
lean_inc(v_D_4845_);
lean_inc(v_Y_4844_);
lean_inc(v_u_4843_);
lean_inc(v_y_4842_);
lean_inc(v_G_4841_);
lean_dec(v_date_4582_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4886_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4840_ == 0)
{
lean_ctor_set_tag(v___x_4839_, 1);
lean_ctor_set(v___x_4839_, 0, v_data_4584_);
v___x_4881_ = v___x_4839_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_data_4584_);
v___x_4881_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
lean_object* v___x_4883_; 
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 6, v___x_4881_);
v___x_4883_ = v___x_4878_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_G_4841_);
lean_ctor_set(v_reuseFailAlloc_4884_, 1, v_y_4842_);
lean_ctor_set(v_reuseFailAlloc_4884_, 2, v_u_4843_);
lean_ctor_set(v_reuseFailAlloc_4884_, 3, v_Y_4844_);
lean_ctor_set(v_reuseFailAlloc_4884_, 4, v_D_4845_);
lean_ctor_set(v_reuseFailAlloc_4884_, 5, v_M_4846_);
lean_ctor_set(v_reuseFailAlloc_4884_, 6, v___x_4881_);
lean_ctor_set(v_reuseFailAlloc_4884_, 7, v_d_4847_);
lean_ctor_set(v_reuseFailAlloc_4884_, 8, v_Q_4848_);
lean_ctor_set(v_reuseFailAlloc_4884_, 9, v_q_4849_);
lean_ctor_set(v_reuseFailAlloc_4884_, 10, v_w_4850_);
lean_ctor_set(v_reuseFailAlloc_4884_, 11, v_W_4851_);
lean_ctor_set(v_reuseFailAlloc_4884_, 12, v_E_4852_);
lean_ctor_set(v_reuseFailAlloc_4884_, 13, v_e_4853_);
lean_ctor_set(v_reuseFailAlloc_4884_, 14, v_c_4854_);
lean_ctor_set(v_reuseFailAlloc_4884_, 15, v_F_4855_);
lean_ctor_set(v_reuseFailAlloc_4884_, 16, v_a_4856_);
lean_ctor_set(v_reuseFailAlloc_4884_, 17, v_b_4857_);
lean_ctor_set(v_reuseFailAlloc_4884_, 18, v_B_4858_);
lean_ctor_set(v_reuseFailAlloc_4884_, 19, v_h_4859_);
lean_ctor_set(v_reuseFailAlloc_4884_, 20, v_K_4860_);
lean_ctor_set(v_reuseFailAlloc_4884_, 21, v_k_4861_);
lean_ctor_set(v_reuseFailAlloc_4884_, 22, v_H_4862_);
lean_ctor_set(v_reuseFailAlloc_4884_, 23, v_m_4863_);
lean_ctor_set(v_reuseFailAlloc_4884_, 24, v_s_4864_);
lean_ctor_set(v_reuseFailAlloc_4884_, 25, v_S_4865_);
lean_ctor_set(v_reuseFailAlloc_4884_, 26, v_A_4866_);
lean_ctor_set(v_reuseFailAlloc_4884_, 27, v_n_4867_);
lean_ctor_set(v_reuseFailAlloc_4884_, 28, v_N_4868_);
lean_ctor_set(v_reuseFailAlloc_4884_, 29, v_V_4869_);
lean_ctor_set(v_reuseFailAlloc_4884_, 30, v_z_4870_);
lean_ctor_set(v_reuseFailAlloc_4884_, 31, v_zabbrev_4871_);
lean_ctor_set(v_reuseFailAlloc_4884_, 32, v_v_4872_);
lean_ctor_set(v_reuseFailAlloc_4884_, 33, v_O_4873_);
lean_ctor_set(v_reuseFailAlloc_4884_, 34, v_X_4874_);
lean_ctor_set(v_reuseFailAlloc_4884_, 35, v_x_4875_);
lean_ctor_set(v_reuseFailAlloc_4884_, 36, v_Z_4876_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
}
}
case 6:
{
lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4940_; 
v_isSharedCheck_4940_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_4940_ == 0)
{
lean_object* v_unused_4941_; 
v_unused_4941_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_4941_);
v___x_4891_ = v_modifier_4583_;
v_isShared_4892_ = v_isSharedCheck_4940_;
goto v_resetjp_4890_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4940_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v_G_4893_; lean_object* v_y_4894_; lean_object* v_u_4895_; lean_object* v_Y_4896_; lean_object* v_D_4897_; lean_object* v_M_4898_; lean_object* v_L_4899_; lean_object* v_Q_4900_; lean_object* v_q_4901_; lean_object* v_w_4902_; lean_object* v_W_4903_; lean_object* v_E_4904_; lean_object* v_e_4905_; lean_object* v_c_4906_; lean_object* v_F_4907_; lean_object* v_a_4908_; lean_object* v_b_4909_; lean_object* v_B_4910_; lean_object* v_h_4911_; lean_object* v_K_4912_; lean_object* v_k_4913_; lean_object* v_H_4914_; lean_object* v_m_4915_; lean_object* v_s_4916_; lean_object* v_S_4917_; lean_object* v_A_4918_; lean_object* v_n_4919_; lean_object* v_N_4920_; lean_object* v_V_4921_; lean_object* v_z_4922_; lean_object* v_zabbrev_4923_; lean_object* v_v_4924_; lean_object* v_O_4925_; lean_object* v_X_4926_; lean_object* v_x_4927_; lean_object* v_Z_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4938_; 
v_G_4893_ = lean_ctor_get(v_date_4582_, 0);
v_y_4894_ = lean_ctor_get(v_date_4582_, 1);
v_u_4895_ = lean_ctor_get(v_date_4582_, 2);
v_Y_4896_ = lean_ctor_get(v_date_4582_, 3);
v_D_4897_ = lean_ctor_get(v_date_4582_, 4);
v_M_4898_ = lean_ctor_get(v_date_4582_, 5);
v_L_4899_ = lean_ctor_get(v_date_4582_, 6);
v_Q_4900_ = lean_ctor_get(v_date_4582_, 8);
v_q_4901_ = lean_ctor_get(v_date_4582_, 9);
v_w_4902_ = lean_ctor_get(v_date_4582_, 10);
v_W_4903_ = lean_ctor_get(v_date_4582_, 11);
v_E_4904_ = lean_ctor_get(v_date_4582_, 12);
v_e_4905_ = lean_ctor_get(v_date_4582_, 13);
v_c_4906_ = lean_ctor_get(v_date_4582_, 14);
v_F_4907_ = lean_ctor_get(v_date_4582_, 15);
v_a_4908_ = lean_ctor_get(v_date_4582_, 16);
v_b_4909_ = lean_ctor_get(v_date_4582_, 17);
v_B_4910_ = lean_ctor_get(v_date_4582_, 18);
v_h_4911_ = lean_ctor_get(v_date_4582_, 19);
v_K_4912_ = lean_ctor_get(v_date_4582_, 20);
v_k_4913_ = lean_ctor_get(v_date_4582_, 21);
v_H_4914_ = lean_ctor_get(v_date_4582_, 22);
v_m_4915_ = lean_ctor_get(v_date_4582_, 23);
v_s_4916_ = lean_ctor_get(v_date_4582_, 24);
v_S_4917_ = lean_ctor_get(v_date_4582_, 25);
v_A_4918_ = lean_ctor_get(v_date_4582_, 26);
v_n_4919_ = lean_ctor_get(v_date_4582_, 27);
v_N_4920_ = lean_ctor_get(v_date_4582_, 28);
v_V_4921_ = lean_ctor_get(v_date_4582_, 29);
v_z_4922_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_4923_ = lean_ctor_get(v_date_4582_, 31);
v_v_4924_ = lean_ctor_get(v_date_4582_, 32);
v_O_4925_ = lean_ctor_get(v_date_4582_, 33);
v_X_4926_ = lean_ctor_get(v_date_4582_, 34);
v_x_4927_ = lean_ctor_get(v_date_4582_, 35);
v_Z_4928_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_4938_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_4938_ == 0)
{
lean_object* v_unused_4939_; 
v_unused_4939_ = lean_ctor_get(v_date_4582_, 7);
lean_dec(v_unused_4939_);
v___x_4930_ = v_date_4582_;
v_isShared_4931_ = v_isSharedCheck_4938_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_Z_4928_);
lean_inc(v_x_4927_);
lean_inc(v_X_4926_);
lean_inc(v_O_4925_);
lean_inc(v_v_4924_);
lean_inc(v_zabbrev_4923_);
lean_inc(v_z_4922_);
lean_inc(v_V_4921_);
lean_inc(v_N_4920_);
lean_inc(v_n_4919_);
lean_inc(v_A_4918_);
lean_inc(v_S_4917_);
lean_inc(v_s_4916_);
lean_inc(v_m_4915_);
lean_inc(v_H_4914_);
lean_inc(v_k_4913_);
lean_inc(v_K_4912_);
lean_inc(v_h_4911_);
lean_inc(v_B_4910_);
lean_inc(v_b_4909_);
lean_inc(v_a_4908_);
lean_inc(v_F_4907_);
lean_inc(v_c_4906_);
lean_inc(v_e_4905_);
lean_inc(v_E_4904_);
lean_inc(v_W_4903_);
lean_inc(v_w_4902_);
lean_inc(v_q_4901_);
lean_inc(v_Q_4900_);
lean_inc(v_L_4899_);
lean_inc(v_M_4898_);
lean_inc(v_D_4897_);
lean_inc(v_Y_4896_);
lean_inc(v_u_4895_);
lean_inc(v_y_4894_);
lean_inc(v_G_4893_);
lean_dec(v_date_4582_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4938_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4892_ == 0)
{
lean_ctor_set_tag(v___x_4891_, 1);
lean_ctor_set(v___x_4891_, 0, v_data_4584_);
v___x_4933_ = v___x_4891_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_data_4584_);
v___x_4933_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
lean_object* v___x_4935_; 
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 7, v___x_4933_);
v___x_4935_ = v___x_4930_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_G_4893_);
lean_ctor_set(v_reuseFailAlloc_4936_, 1, v_y_4894_);
lean_ctor_set(v_reuseFailAlloc_4936_, 2, v_u_4895_);
lean_ctor_set(v_reuseFailAlloc_4936_, 3, v_Y_4896_);
lean_ctor_set(v_reuseFailAlloc_4936_, 4, v_D_4897_);
lean_ctor_set(v_reuseFailAlloc_4936_, 5, v_M_4898_);
lean_ctor_set(v_reuseFailAlloc_4936_, 6, v_L_4899_);
lean_ctor_set(v_reuseFailAlloc_4936_, 7, v___x_4933_);
lean_ctor_set(v_reuseFailAlloc_4936_, 8, v_Q_4900_);
lean_ctor_set(v_reuseFailAlloc_4936_, 9, v_q_4901_);
lean_ctor_set(v_reuseFailAlloc_4936_, 10, v_w_4902_);
lean_ctor_set(v_reuseFailAlloc_4936_, 11, v_W_4903_);
lean_ctor_set(v_reuseFailAlloc_4936_, 12, v_E_4904_);
lean_ctor_set(v_reuseFailAlloc_4936_, 13, v_e_4905_);
lean_ctor_set(v_reuseFailAlloc_4936_, 14, v_c_4906_);
lean_ctor_set(v_reuseFailAlloc_4936_, 15, v_F_4907_);
lean_ctor_set(v_reuseFailAlloc_4936_, 16, v_a_4908_);
lean_ctor_set(v_reuseFailAlloc_4936_, 17, v_b_4909_);
lean_ctor_set(v_reuseFailAlloc_4936_, 18, v_B_4910_);
lean_ctor_set(v_reuseFailAlloc_4936_, 19, v_h_4911_);
lean_ctor_set(v_reuseFailAlloc_4936_, 20, v_K_4912_);
lean_ctor_set(v_reuseFailAlloc_4936_, 21, v_k_4913_);
lean_ctor_set(v_reuseFailAlloc_4936_, 22, v_H_4914_);
lean_ctor_set(v_reuseFailAlloc_4936_, 23, v_m_4915_);
lean_ctor_set(v_reuseFailAlloc_4936_, 24, v_s_4916_);
lean_ctor_set(v_reuseFailAlloc_4936_, 25, v_S_4917_);
lean_ctor_set(v_reuseFailAlloc_4936_, 26, v_A_4918_);
lean_ctor_set(v_reuseFailAlloc_4936_, 27, v_n_4919_);
lean_ctor_set(v_reuseFailAlloc_4936_, 28, v_N_4920_);
lean_ctor_set(v_reuseFailAlloc_4936_, 29, v_V_4921_);
lean_ctor_set(v_reuseFailAlloc_4936_, 30, v_z_4922_);
lean_ctor_set(v_reuseFailAlloc_4936_, 31, v_zabbrev_4923_);
lean_ctor_set(v_reuseFailAlloc_4936_, 32, v_v_4924_);
lean_ctor_set(v_reuseFailAlloc_4936_, 33, v_O_4925_);
lean_ctor_set(v_reuseFailAlloc_4936_, 34, v_X_4926_);
lean_ctor_set(v_reuseFailAlloc_4936_, 35, v_x_4927_);
lean_ctor_set(v_reuseFailAlloc_4936_, 36, v_Z_4928_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
}
case 7:
{
lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4992_; 
v_isSharedCheck_4992_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_4992_ == 0)
{
lean_object* v_unused_4993_; 
v_unused_4993_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_4993_);
v___x_4943_ = v_modifier_4583_;
v_isShared_4944_ = v_isSharedCheck_4992_;
goto v_resetjp_4942_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4992_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v_G_4945_; lean_object* v_y_4946_; lean_object* v_u_4947_; lean_object* v_Y_4948_; lean_object* v_D_4949_; lean_object* v_M_4950_; lean_object* v_L_4951_; lean_object* v_d_4952_; lean_object* v_q_4953_; lean_object* v_w_4954_; lean_object* v_W_4955_; lean_object* v_E_4956_; lean_object* v_e_4957_; lean_object* v_c_4958_; lean_object* v_F_4959_; lean_object* v_a_4960_; lean_object* v_b_4961_; lean_object* v_B_4962_; lean_object* v_h_4963_; lean_object* v_K_4964_; lean_object* v_k_4965_; lean_object* v_H_4966_; lean_object* v_m_4967_; lean_object* v_s_4968_; lean_object* v_S_4969_; lean_object* v_A_4970_; lean_object* v_n_4971_; lean_object* v_N_4972_; lean_object* v_V_4973_; lean_object* v_z_4974_; lean_object* v_zabbrev_4975_; lean_object* v_v_4976_; lean_object* v_O_4977_; lean_object* v_X_4978_; lean_object* v_x_4979_; lean_object* v_Z_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4990_; 
v_G_4945_ = lean_ctor_get(v_date_4582_, 0);
v_y_4946_ = lean_ctor_get(v_date_4582_, 1);
v_u_4947_ = lean_ctor_get(v_date_4582_, 2);
v_Y_4948_ = lean_ctor_get(v_date_4582_, 3);
v_D_4949_ = lean_ctor_get(v_date_4582_, 4);
v_M_4950_ = lean_ctor_get(v_date_4582_, 5);
v_L_4951_ = lean_ctor_get(v_date_4582_, 6);
v_d_4952_ = lean_ctor_get(v_date_4582_, 7);
v_q_4953_ = lean_ctor_get(v_date_4582_, 9);
v_w_4954_ = lean_ctor_get(v_date_4582_, 10);
v_W_4955_ = lean_ctor_get(v_date_4582_, 11);
v_E_4956_ = lean_ctor_get(v_date_4582_, 12);
v_e_4957_ = lean_ctor_get(v_date_4582_, 13);
v_c_4958_ = lean_ctor_get(v_date_4582_, 14);
v_F_4959_ = lean_ctor_get(v_date_4582_, 15);
v_a_4960_ = lean_ctor_get(v_date_4582_, 16);
v_b_4961_ = lean_ctor_get(v_date_4582_, 17);
v_B_4962_ = lean_ctor_get(v_date_4582_, 18);
v_h_4963_ = lean_ctor_get(v_date_4582_, 19);
v_K_4964_ = lean_ctor_get(v_date_4582_, 20);
v_k_4965_ = lean_ctor_get(v_date_4582_, 21);
v_H_4966_ = lean_ctor_get(v_date_4582_, 22);
v_m_4967_ = lean_ctor_get(v_date_4582_, 23);
v_s_4968_ = lean_ctor_get(v_date_4582_, 24);
v_S_4969_ = lean_ctor_get(v_date_4582_, 25);
v_A_4970_ = lean_ctor_get(v_date_4582_, 26);
v_n_4971_ = lean_ctor_get(v_date_4582_, 27);
v_N_4972_ = lean_ctor_get(v_date_4582_, 28);
v_V_4973_ = lean_ctor_get(v_date_4582_, 29);
v_z_4974_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_4975_ = lean_ctor_get(v_date_4582_, 31);
v_v_4976_ = lean_ctor_get(v_date_4582_, 32);
v_O_4977_ = lean_ctor_get(v_date_4582_, 33);
v_X_4978_ = lean_ctor_get(v_date_4582_, 34);
v_x_4979_ = lean_ctor_get(v_date_4582_, 35);
v_Z_4980_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_4990_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_4990_ == 0)
{
lean_object* v_unused_4991_; 
v_unused_4991_ = lean_ctor_get(v_date_4582_, 8);
lean_dec(v_unused_4991_);
v___x_4982_ = v_date_4582_;
v_isShared_4983_ = v_isSharedCheck_4990_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_Z_4980_);
lean_inc(v_x_4979_);
lean_inc(v_X_4978_);
lean_inc(v_O_4977_);
lean_inc(v_v_4976_);
lean_inc(v_zabbrev_4975_);
lean_inc(v_z_4974_);
lean_inc(v_V_4973_);
lean_inc(v_N_4972_);
lean_inc(v_n_4971_);
lean_inc(v_A_4970_);
lean_inc(v_S_4969_);
lean_inc(v_s_4968_);
lean_inc(v_m_4967_);
lean_inc(v_H_4966_);
lean_inc(v_k_4965_);
lean_inc(v_K_4964_);
lean_inc(v_h_4963_);
lean_inc(v_B_4962_);
lean_inc(v_b_4961_);
lean_inc(v_a_4960_);
lean_inc(v_F_4959_);
lean_inc(v_c_4958_);
lean_inc(v_e_4957_);
lean_inc(v_E_4956_);
lean_inc(v_W_4955_);
lean_inc(v_w_4954_);
lean_inc(v_q_4953_);
lean_inc(v_d_4952_);
lean_inc(v_L_4951_);
lean_inc(v_M_4950_);
lean_inc(v_D_4949_);
lean_inc(v_Y_4948_);
lean_inc(v_u_4947_);
lean_inc(v_y_4946_);
lean_inc(v_G_4945_);
lean_dec(v_date_4582_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4990_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4985_; 
if (v_isShared_4944_ == 0)
{
lean_ctor_set_tag(v___x_4943_, 1);
lean_ctor_set(v___x_4943_, 0, v_data_4584_);
v___x_4985_ = v___x_4943_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_data_4584_);
v___x_4985_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
lean_object* v___x_4987_; 
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 8, v___x_4985_);
v___x_4987_ = v___x_4982_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_G_4945_);
lean_ctor_set(v_reuseFailAlloc_4988_, 1, v_y_4946_);
lean_ctor_set(v_reuseFailAlloc_4988_, 2, v_u_4947_);
lean_ctor_set(v_reuseFailAlloc_4988_, 3, v_Y_4948_);
lean_ctor_set(v_reuseFailAlloc_4988_, 4, v_D_4949_);
lean_ctor_set(v_reuseFailAlloc_4988_, 5, v_M_4950_);
lean_ctor_set(v_reuseFailAlloc_4988_, 6, v_L_4951_);
lean_ctor_set(v_reuseFailAlloc_4988_, 7, v_d_4952_);
lean_ctor_set(v_reuseFailAlloc_4988_, 8, v___x_4985_);
lean_ctor_set(v_reuseFailAlloc_4988_, 9, v_q_4953_);
lean_ctor_set(v_reuseFailAlloc_4988_, 10, v_w_4954_);
lean_ctor_set(v_reuseFailAlloc_4988_, 11, v_W_4955_);
lean_ctor_set(v_reuseFailAlloc_4988_, 12, v_E_4956_);
lean_ctor_set(v_reuseFailAlloc_4988_, 13, v_e_4957_);
lean_ctor_set(v_reuseFailAlloc_4988_, 14, v_c_4958_);
lean_ctor_set(v_reuseFailAlloc_4988_, 15, v_F_4959_);
lean_ctor_set(v_reuseFailAlloc_4988_, 16, v_a_4960_);
lean_ctor_set(v_reuseFailAlloc_4988_, 17, v_b_4961_);
lean_ctor_set(v_reuseFailAlloc_4988_, 18, v_B_4962_);
lean_ctor_set(v_reuseFailAlloc_4988_, 19, v_h_4963_);
lean_ctor_set(v_reuseFailAlloc_4988_, 20, v_K_4964_);
lean_ctor_set(v_reuseFailAlloc_4988_, 21, v_k_4965_);
lean_ctor_set(v_reuseFailAlloc_4988_, 22, v_H_4966_);
lean_ctor_set(v_reuseFailAlloc_4988_, 23, v_m_4967_);
lean_ctor_set(v_reuseFailAlloc_4988_, 24, v_s_4968_);
lean_ctor_set(v_reuseFailAlloc_4988_, 25, v_S_4969_);
lean_ctor_set(v_reuseFailAlloc_4988_, 26, v_A_4970_);
lean_ctor_set(v_reuseFailAlloc_4988_, 27, v_n_4971_);
lean_ctor_set(v_reuseFailAlloc_4988_, 28, v_N_4972_);
lean_ctor_set(v_reuseFailAlloc_4988_, 29, v_V_4973_);
lean_ctor_set(v_reuseFailAlloc_4988_, 30, v_z_4974_);
lean_ctor_set(v_reuseFailAlloc_4988_, 31, v_zabbrev_4975_);
lean_ctor_set(v_reuseFailAlloc_4988_, 32, v_v_4976_);
lean_ctor_set(v_reuseFailAlloc_4988_, 33, v_O_4977_);
lean_ctor_set(v_reuseFailAlloc_4988_, 34, v_X_4978_);
lean_ctor_set(v_reuseFailAlloc_4988_, 35, v_x_4979_);
lean_ctor_set(v_reuseFailAlloc_4988_, 36, v_Z_4980_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
}
}
}
case 8:
{
lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5044_; 
v_isSharedCheck_5044_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5044_ == 0)
{
lean_object* v_unused_5045_; 
v_unused_5045_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5045_);
v___x_4995_ = v_modifier_4583_;
v_isShared_4996_ = v_isSharedCheck_5044_;
goto v_resetjp_4994_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5044_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v_G_4997_; lean_object* v_y_4998_; lean_object* v_u_4999_; lean_object* v_Y_5000_; lean_object* v_D_5001_; lean_object* v_M_5002_; lean_object* v_L_5003_; lean_object* v_d_5004_; lean_object* v_Q_5005_; lean_object* v_w_5006_; lean_object* v_W_5007_; lean_object* v_E_5008_; lean_object* v_e_5009_; lean_object* v_c_5010_; lean_object* v_F_5011_; lean_object* v_a_5012_; lean_object* v_b_5013_; lean_object* v_B_5014_; lean_object* v_h_5015_; lean_object* v_K_5016_; lean_object* v_k_5017_; lean_object* v_H_5018_; lean_object* v_m_5019_; lean_object* v_s_5020_; lean_object* v_S_5021_; lean_object* v_A_5022_; lean_object* v_n_5023_; lean_object* v_N_5024_; lean_object* v_V_5025_; lean_object* v_z_5026_; lean_object* v_zabbrev_5027_; lean_object* v_v_5028_; lean_object* v_O_5029_; lean_object* v_X_5030_; lean_object* v_x_5031_; lean_object* v_Z_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5042_; 
v_G_4997_ = lean_ctor_get(v_date_4582_, 0);
v_y_4998_ = lean_ctor_get(v_date_4582_, 1);
v_u_4999_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5000_ = lean_ctor_get(v_date_4582_, 3);
v_D_5001_ = lean_ctor_get(v_date_4582_, 4);
v_M_5002_ = lean_ctor_get(v_date_4582_, 5);
v_L_5003_ = lean_ctor_get(v_date_4582_, 6);
v_d_5004_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5005_ = lean_ctor_get(v_date_4582_, 8);
v_w_5006_ = lean_ctor_get(v_date_4582_, 10);
v_W_5007_ = lean_ctor_get(v_date_4582_, 11);
v_E_5008_ = lean_ctor_get(v_date_4582_, 12);
v_e_5009_ = lean_ctor_get(v_date_4582_, 13);
v_c_5010_ = lean_ctor_get(v_date_4582_, 14);
v_F_5011_ = lean_ctor_get(v_date_4582_, 15);
v_a_5012_ = lean_ctor_get(v_date_4582_, 16);
v_b_5013_ = lean_ctor_get(v_date_4582_, 17);
v_B_5014_ = lean_ctor_get(v_date_4582_, 18);
v_h_5015_ = lean_ctor_get(v_date_4582_, 19);
v_K_5016_ = lean_ctor_get(v_date_4582_, 20);
v_k_5017_ = lean_ctor_get(v_date_4582_, 21);
v_H_5018_ = lean_ctor_get(v_date_4582_, 22);
v_m_5019_ = lean_ctor_get(v_date_4582_, 23);
v_s_5020_ = lean_ctor_get(v_date_4582_, 24);
v_S_5021_ = lean_ctor_get(v_date_4582_, 25);
v_A_5022_ = lean_ctor_get(v_date_4582_, 26);
v_n_5023_ = lean_ctor_get(v_date_4582_, 27);
v_N_5024_ = lean_ctor_get(v_date_4582_, 28);
v_V_5025_ = lean_ctor_get(v_date_4582_, 29);
v_z_5026_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5027_ = lean_ctor_get(v_date_4582_, 31);
v_v_5028_ = lean_ctor_get(v_date_4582_, 32);
v_O_5029_ = lean_ctor_get(v_date_4582_, 33);
v_X_5030_ = lean_ctor_get(v_date_4582_, 34);
v_x_5031_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5032_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5042_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5042_ == 0)
{
lean_object* v_unused_5043_; 
v_unused_5043_ = lean_ctor_get(v_date_4582_, 9);
lean_dec(v_unused_5043_);
v___x_5034_ = v_date_4582_;
v_isShared_5035_ = v_isSharedCheck_5042_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_Z_5032_);
lean_inc(v_x_5031_);
lean_inc(v_X_5030_);
lean_inc(v_O_5029_);
lean_inc(v_v_5028_);
lean_inc(v_zabbrev_5027_);
lean_inc(v_z_5026_);
lean_inc(v_V_5025_);
lean_inc(v_N_5024_);
lean_inc(v_n_5023_);
lean_inc(v_A_5022_);
lean_inc(v_S_5021_);
lean_inc(v_s_5020_);
lean_inc(v_m_5019_);
lean_inc(v_H_5018_);
lean_inc(v_k_5017_);
lean_inc(v_K_5016_);
lean_inc(v_h_5015_);
lean_inc(v_B_5014_);
lean_inc(v_b_5013_);
lean_inc(v_a_5012_);
lean_inc(v_F_5011_);
lean_inc(v_c_5010_);
lean_inc(v_e_5009_);
lean_inc(v_E_5008_);
lean_inc(v_W_5007_);
lean_inc(v_w_5006_);
lean_inc(v_Q_5005_);
lean_inc(v_d_5004_);
lean_inc(v_L_5003_);
lean_inc(v_M_5002_);
lean_inc(v_D_5001_);
lean_inc(v_Y_5000_);
lean_inc(v_u_4999_);
lean_inc(v_y_4998_);
lean_inc(v_G_4997_);
lean_dec(v_date_4582_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5042_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
if (v_isShared_4996_ == 0)
{
lean_ctor_set_tag(v___x_4995_, 1);
lean_ctor_set(v___x_4995_, 0, v_data_4584_);
v___x_5037_ = v___x_4995_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_data_4584_);
v___x_5037_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
lean_object* v___x_5039_; 
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 9, v___x_5037_);
v___x_5039_ = v___x_5034_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_G_4997_);
lean_ctor_set(v_reuseFailAlloc_5040_, 1, v_y_4998_);
lean_ctor_set(v_reuseFailAlloc_5040_, 2, v_u_4999_);
lean_ctor_set(v_reuseFailAlloc_5040_, 3, v_Y_5000_);
lean_ctor_set(v_reuseFailAlloc_5040_, 4, v_D_5001_);
lean_ctor_set(v_reuseFailAlloc_5040_, 5, v_M_5002_);
lean_ctor_set(v_reuseFailAlloc_5040_, 6, v_L_5003_);
lean_ctor_set(v_reuseFailAlloc_5040_, 7, v_d_5004_);
lean_ctor_set(v_reuseFailAlloc_5040_, 8, v_Q_5005_);
lean_ctor_set(v_reuseFailAlloc_5040_, 9, v___x_5037_);
lean_ctor_set(v_reuseFailAlloc_5040_, 10, v_w_5006_);
lean_ctor_set(v_reuseFailAlloc_5040_, 11, v_W_5007_);
lean_ctor_set(v_reuseFailAlloc_5040_, 12, v_E_5008_);
lean_ctor_set(v_reuseFailAlloc_5040_, 13, v_e_5009_);
lean_ctor_set(v_reuseFailAlloc_5040_, 14, v_c_5010_);
lean_ctor_set(v_reuseFailAlloc_5040_, 15, v_F_5011_);
lean_ctor_set(v_reuseFailAlloc_5040_, 16, v_a_5012_);
lean_ctor_set(v_reuseFailAlloc_5040_, 17, v_b_5013_);
lean_ctor_set(v_reuseFailAlloc_5040_, 18, v_B_5014_);
lean_ctor_set(v_reuseFailAlloc_5040_, 19, v_h_5015_);
lean_ctor_set(v_reuseFailAlloc_5040_, 20, v_K_5016_);
lean_ctor_set(v_reuseFailAlloc_5040_, 21, v_k_5017_);
lean_ctor_set(v_reuseFailAlloc_5040_, 22, v_H_5018_);
lean_ctor_set(v_reuseFailAlloc_5040_, 23, v_m_5019_);
lean_ctor_set(v_reuseFailAlloc_5040_, 24, v_s_5020_);
lean_ctor_set(v_reuseFailAlloc_5040_, 25, v_S_5021_);
lean_ctor_set(v_reuseFailAlloc_5040_, 26, v_A_5022_);
lean_ctor_set(v_reuseFailAlloc_5040_, 27, v_n_5023_);
lean_ctor_set(v_reuseFailAlloc_5040_, 28, v_N_5024_);
lean_ctor_set(v_reuseFailAlloc_5040_, 29, v_V_5025_);
lean_ctor_set(v_reuseFailAlloc_5040_, 30, v_z_5026_);
lean_ctor_set(v_reuseFailAlloc_5040_, 31, v_zabbrev_5027_);
lean_ctor_set(v_reuseFailAlloc_5040_, 32, v_v_5028_);
lean_ctor_set(v_reuseFailAlloc_5040_, 33, v_O_5029_);
lean_ctor_set(v_reuseFailAlloc_5040_, 34, v_X_5030_);
lean_ctor_set(v_reuseFailAlloc_5040_, 35, v_x_5031_);
lean_ctor_set(v_reuseFailAlloc_5040_, 36, v_Z_5032_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
}
}
case 9:
{
lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5096_; 
v_isSharedCheck_5096_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5096_ == 0)
{
lean_object* v_unused_5097_; 
v_unused_5097_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5097_);
v___x_5047_ = v_modifier_4583_;
v_isShared_5048_ = v_isSharedCheck_5096_;
goto v_resetjp_5046_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5096_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v_G_5049_; lean_object* v_y_5050_; lean_object* v_u_5051_; lean_object* v_D_5052_; lean_object* v_M_5053_; lean_object* v_L_5054_; lean_object* v_d_5055_; lean_object* v_Q_5056_; lean_object* v_q_5057_; lean_object* v_w_5058_; lean_object* v_W_5059_; lean_object* v_E_5060_; lean_object* v_e_5061_; lean_object* v_c_5062_; lean_object* v_F_5063_; lean_object* v_a_5064_; lean_object* v_b_5065_; lean_object* v_B_5066_; lean_object* v_h_5067_; lean_object* v_K_5068_; lean_object* v_k_5069_; lean_object* v_H_5070_; lean_object* v_m_5071_; lean_object* v_s_5072_; lean_object* v_S_5073_; lean_object* v_A_5074_; lean_object* v_n_5075_; lean_object* v_N_5076_; lean_object* v_V_5077_; lean_object* v_z_5078_; lean_object* v_zabbrev_5079_; lean_object* v_v_5080_; lean_object* v_O_5081_; lean_object* v_X_5082_; lean_object* v_x_5083_; lean_object* v_Z_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5094_; 
v_G_5049_ = lean_ctor_get(v_date_4582_, 0);
v_y_5050_ = lean_ctor_get(v_date_4582_, 1);
v_u_5051_ = lean_ctor_get(v_date_4582_, 2);
v_D_5052_ = lean_ctor_get(v_date_4582_, 4);
v_M_5053_ = lean_ctor_get(v_date_4582_, 5);
v_L_5054_ = lean_ctor_get(v_date_4582_, 6);
v_d_5055_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5056_ = lean_ctor_get(v_date_4582_, 8);
v_q_5057_ = lean_ctor_get(v_date_4582_, 9);
v_w_5058_ = lean_ctor_get(v_date_4582_, 10);
v_W_5059_ = lean_ctor_get(v_date_4582_, 11);
v_E_5060_ = lean_ctor_get(v_date_4582_, 12);
v_e_5061_ = lean_ctor_get(v_date_4582_, 13);
v_c_5062_ = lean_ctor_get(v_date_4582_, 14);
v_F_5063_ = lean_ctor_get(v_date_4582_, 15);
v_a_5064_ = lean_ctor_get(v_date_4582_, 16);
v_b_5065_ = lean_ctor_get(v_date_4582_, 17);
v_B_5066_ = lean_ctor_get(v_date_4582_, 18);
v_h_5067_ = lean_ctor_get(v_date_4582_, 19);
v_K_5068_ = lean_ctor_get(v_date_4582_, 20);
v_k_5069_ = lean_ctor_get(v_date_4582_, 21);
v_H_5070_ = lean_ctor_get(v_date_4582_, 22);
v_m_5071_ = lean_ctor_get(v_date_4582_, 23);
v_s_5072_ = lean_ctor_get(v_date_4582_, 24);
v_S_5073_ = lean_ctor_get(v_date_4582_, 25);
v_A_5074_ = lean_ctor_get(v_date_4582_, 26);
v_n_5075_ = lean_ctor_get(v_date_4582_, 27);
v_N_5076_ = lean_ctor_get(v_date_4582_, 28);
v_V_5077_ = lean_ctor_get(v_date_4582_, 29);
v_z_5078_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5079_ = lean_ctor_get(v_date_4582_, 31);
v_v_5080_ = lean_ctor_get(v_date_4582_, 32);
v_O_5081_ = lean_ctor_get(v_date_4582_, 33);
v_X_5082_ = lean_ctor_get(v_date_4582_, 34);
v_x_5083_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5084_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5094_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5094_ == 0)
{
lean_object* v_unused_5095_; 
v_unused_5095_ = lean_ctor_get(v_date_4582_, 3);
lean_dec(v_unused_5095_);
v___x_5086_ = v_date_4582_;
v_isShared_5087_ = v_isSharedCheck_5094_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_Z_5084_);
lean_inc(v_x_5083_);
lean_inc(v_X_5082_);
lean_inc(v_O_5081_);
lean_inc(v_v_5080_);
lean_inc(v_zabbrev_5079_);
lean_inc(v_z_5078_);
lean_inc(v_V_5077_);
lean_inc(v_N_5076_);
lean_inc(v_n_5075_);
lean_inc(v_A_5074_);
lean_inc(v_S_5073_);
lean_inc(v_s_5072_);
lean_inc(v_m_5071_);
lean_inc(v_H_5070_);
lean_inc(v_k_5069_);
lean_inc(v_K_5068_);
lean_inc(v_h_5067_);
lean_inc(v_B_5066_);
lean_inc(v_b_5065_);
lean_inc(v_a_5064_);
lean_inc(v_F_5063_);
lean_inc(v_c_5062_);
lean_inc(v_e_5061_);
lean_inc(v_E_5060_);
lean_inc(v_W_5059_);
lean_inc(v_w_5058_);
lean_inc(v_q_5057_);
lean_inc(v_Q_5056_);
lean_inc(v_d_5055_);
lean_inc(v_L_5054_);
lean_inc(v_M_5053_);
lean_inc(v_D_5052_);
lean_inc(v_u_5051_);
lean_inc(v_y_5050_);
lean_inc(v_G_5049_);
lean_dec(v_date_4582_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5094_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5089_; 
if (v_isShared_5048_ == 0)
{
lean_ctor_set_tag(v___x_5047_, 1);
lean_ctor_set(v___x_5047_, 0, v_data_4584_);
v___x_5089_ = v___x_5047_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_data_4584_);
v___x_5089_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
lean_object* v___x_5091_; 
if (v_isShared_5087_ == 0)
{
lean_ctor_set(v___x_5086_, 3, v___x_5089_);
v___x_5091_ = v___x_5086_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_G_5049_);
lean_ctor_set(v_reuseFailAlloc_5092_, 1, v_y_5050_);
lean_ctor_set(v_reuseFailAlloc_5092_, 2, v_u_5051_);
lean_ctor_set(v_reuseFailAlloc_5092_, 3, v___x_5089_);
lean_ctor_set(v_reuseFailAlloc_5092_, 4, v_D_5052_);
lean_ctor_set(v_reuseFailAlloc_5092_, 5, v_M_5053_);
lean_ctor_set(v_reuseFailAlloc_5092_, 6, v_L_5054_);
lean_ctor_set(v_reuseFailAlloc_5092_, 7, v_d_5055_);
lean_ctor_set(v_reuseFailAlloc_5092_, 8, v_Q_5056_);
lean_ctor_set(v_reuseFailAlloc_5092_, 9, v_q_5057_);
lean_ctor_set(v_reuseFailAlloc_5092_, 10, v_w_5058_);
lean_ctor_set(v_reuseFailAlloc_5092_, 11, v_W_5059_);
lean_ctor_set(v_reuseFailAlloc_5092_, 12, v_E_5060_);
lean_ctor_set(v_reuseFailAlloc_5092_, 13, v_e_5061_);
lean_ctor_set(v_reuseFailAlloc_5092_, 14, v_c_5062_);
lean_ctor_set(v_reuseFailAlloc_5092_, 15, v_F_5063_);
lean_ctor_set(v_reuseFailAlloc_5092_, 16, v_a_5064_);
lean_ctor_set(v_reuseFailAlloc_5092_, 17, v_b_5065_);
lean_ctor_set(v_reuseFailAlloc_5092_, 18, v_B_5066_);
lean_ctor_set(v_reuseFailAlloc_5092_, 19, v_h_5067_);
lean_ctor_set(v_reuseFailAlloc_5092_, 20, v_K_5068_);
lean_ctor_set(v_reuseFailAlloc_5092_, 21, v_k_5069_);
lean_ctor_set(v_reuseFailAlloc_5092_, 22, v_H_5070_);
lean_ctor_set(v_reuseFailAlloc_5092_, 23, v_m_5071_);
lean_ctor_set(v_reuseFailAlloc_5092_, 24, v_s_5072_);
lean_ctor_set(v_reuseFailAlloc_5092_, 25, v_S_5073_);
lean_ctor_set(v_reuseFailAlloc_5092_, 26, v_A_5074_);
lean_ctor_set(v_reuseFailAlloc_5092_, 27, v_n_5075_);
lean_ctor_set(v_reuseFailAlloc_5092_, 28, v_N_5076_);
lean_ctor_set(v_reuseFailAlloc_5092_, 29, v_V_5077_);
lean_ctor_set(v_reuseFailAlloc_5092_, 30, v_z_5078_);
lean_ctor_set(v_reuseFailAlloc_5092_, 31, v_zabbrev_5079_);
lean_ctor_set(v_reuseFailAlloc_5092_, 32, v_v_5080_);
lean_ctor_set(v_reuseFailAlloc_5092_, 33, v_O_5081_);
lean_ctor_set(v_reuseFailAlloc_5092_, 34, v_X_5082_);
lean_ctor_set(v_reuseFailAlloc_5092_, 35, v_x_5083_);
lean_ctor_set(v_reuseFailAlloc_5092_, 36, v_Z_5084_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
}
case 10:
{
lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5148_; 
v_isSharedCheck_5148_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5148_ == 0)
{
lean_object* v_unused_5149_; 
v_unused_5149_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5149_);
v___x_5099_ = v_modifier_4583_;
v_isShared_5100_ = v_isSharedCheck_5148_;
goto v_resetjp_5098_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5148_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v_G_5101_; lean_object* v_y_5102_; lean_object* v_u_5103_; lean_object* v_Y_5104_; lean_object* v_D_5105_; lean_object* v_M_5106_; lean_object* v_L_5107_; lean_object* v_d_5108_; lean_object* v_Q_5109_; lean_object* v_q_5110_; lean_object* v_W_5111_; lean_object* v_E_5112_; lean_object* v_e_5113_; lean_object* v_c_5114_; lean_object* v_F_5115_; lean_object* v_a_5116_; lean_object* v_b_5117_; lean_object* v_B_5118_; lean_object* v_h_5119_; lean_object* v_K_5120_; lean_object* v_k_5121_; lean_object* v_H_5122_; lean_object* v_m_5123_; lean_object* v_s_5124_; lean_object* v_S_5125_; lean_object* v_A_5126_; lean_object* v_n_5127_; lean_object* v_N_5128_; lean_object* v_V_5129_; lean_object* v_z_5130_; lean_object* v_zabbrev_5131_; lean_object* v_v_5132_; lean_object* v_O_5133_; lean_object* v_X_5134_; lean_object* v_x_5135_; lean_object* v_Z_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5146_; 
v_G_5101_ = lean_ctor_get(v_date_4582_, 0);
v_y_5102_ = lean_ctor_get(v_date_4582_, 1);
v_u_5103_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5104_ = lean_ctor_get(v_date_4582_, 3);
v_D_5105_ = lean_ctor_get(v_date_4582_, 4);
v_M_5106_ = lean_ctor_get(v_date_4582_, 5);
v_L_5107_ = lean_ctor_get(v_date_4582_, 6);
v_d_5108_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5109_ = lean_ctor_get(v_date_4582_, 8);
v_q_5110_ = lean_ctor_get(v_date_4582_, 9);
v_W_5111_ = lean_ctor_get(v_date_4582_, 11);
v_E_5112_ = lean_ctor_get(v_date_4582_, 12);
v_e_5113_ = lean_ctor_get(v_date_4582_, 13);
v_c_5114_ = lean_ctor_get(v_date_4582_, 14);
v_F_5115_ = lean_ctor_get(v_date_4582_, 15);
v_a_5116_ = lean_ctor_get(v_date_4582_, 16);
v_b_5117_ = lean_ctor_get(v_date_4582_, 17);
v_B_5118_ = lean_ctor_get(v_date_4582_, 18);
v_h_5119_ = lean_ctor_get(v_date_4582_, 19);
v_K_5120_ = lean_ctor_get(v_date_4582_, 20);
v_k_5121_ = lean_ctor_get(v_date_4582_, 21);
v_H_5122_ = lean_ctor_get(v_date_4582_, 22);
v_m_5123_ = lean_ctor_get(v_date_4582_, 23);
v_s_5124_ = lean_ctor_get(v_date_4582_, 24);
v_S_5125_ = lean_ctor_get(v_date_4582_, 25);
v_A_5126_ = lean_ctor_get(v_date_4582_, 26);
v_n_5127_ = lean_ctor_get(v_date_4582_, 27);
v_N_5128_ = lean_ctor_get(v_date_4582_, 28);
v_V_5129_ = lean_ctor_get(v_date_4582_, 29);
v_z_5130_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5131_ = lean_ctor_get(v_date_4582_, 31);
v_v_5132_ = lean_ctor_get(v_date_4582_, 32);
v_O_5133_ = lean_ctor_get(v_date_4582_, 33);
v_X_5134_ = lean_ctor_get(v_date_4582_, 34);
v_x_5135_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5136_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5146_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5146_ == 0)
{
lean_object* v_unused_5147_; 
v_unused_5147_ = lean_ctor_get(v_date_4582_, 10);
lean_dec(v_unused_5147_);
v___x_5138_ = v_date_4582_;
v_isShared_5139_ = v_isSharedCheck_5146_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_Z_5136_);
lean_inc(v_x_5135_);
lean_inc(v_X_5134_);
lean_inc(v_O_5133_);
lean_inc(v_v_5132_);
lean_inc(v_zabbrev_5131_);
lean_inc(v_z_5130_);
lean_inc(v_V_5129_);
lean_inc(v_N_5128_);
lean_inc(v_n_5127_);
lean_inc(v_A_5126_);
lean_inc(v_S_5125_);
lean_inc(v_s_5124_);
lean_inc(v_m_5123_);
lean_inc(v_H_5122_);
lean_inc(v_k_5121_);
lean_inc(v_K_5120_);
lean_inc(v_h_5119_);
lean_inc(v_B_5118_);
lean_inc(v_b_5117_);
lean_inc(v_a_5116_);
lean_inc(v_F_5115_);
lean_inc(v_c_5114_);
lean_inc(v_e_5113_);
lean_inc(v_E_5112_);
lean_inc(v_W_5111_);
lean_inc(v_q_5110_);
lean_inc(v_Q_5109_);
lean_inc(v_d_5108_);
lean_inc(v_L_5107_);
lean_inc(v_M_5106_);
lean_inc(v_D_5105_);
lean_inc(v_Y_5104_);
lean_inc(v_u_5103_);
lean_inc(v_y_5102_);
lean_inc(v_G_5101_);
lean_dec(v_date_4582_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5146_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5100_ == 0)
{
lean_ctor_set_tag(v___x_5099_, 1);
lean_ctor_set(v___x_5099_, 0, v_data_4584_);
v___x_5141_ = v___x_5099_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_data_4584_);
v___x_5141_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
lean_object* v___x_5143_; 
if (v_isShared_5139_ == 0)
{
lean_ctor_set(v___x_5138_, 10, v___x_5141_);
v___x_5143_ = v___x_5138_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_G_5101_);
lean_ctor_set(v_reuseFailAlloc_5144_, 1, v_y_5102_);
lean_ctor_set(v_reuseFailAlloc_5144_, 2, v_u_5103_);
lean_ctor_set(v_reuseFailAlloc_5144_, 3, v_Y_5104_);
lean_ctor_set(v_reuseFailAlloc_5144_, 4, v_D_5105_);
lean_ctor_set(v_reuseFailAlloc_5144_, 5, v_M_5106_);
lean_ctor_set(v_reuseFailAlloc_5144_, 6, v_L_5107_);
lean_ctor_set(v_reuseFailAlloc_5144_, 7, v_d_5108_);
lean_ctor_set(v_reuseFailAlloc_5144_, 8, v_Q_5109_);
lean_ctor_set(v_reuseFailAlloc_5144_, 9, v_q_5110_);
lean_ctor_set(v_reuseFailAlloc_5144_, 10, v___x_5141_);
lean_ctor_set(v_reuseFailAlloc_5144_, 11, v_W_5111_);
lean_ctor_set(v_reuseFailAlloc_5144_, 12, v_E_5112_);
lean_ctor_set(v_reuseFailAlloc_5144_, 13, v_e_5113_);
lean_ctor_set(v_reuseFailAlloc_5144_, 14, v_c_5114_);
lean_ctor_set(v_reuseFailAlloc_5144_, 15, v_F_5115_);
lean_ctor_set(v_reuseFailAlloc_5144_, 16, v_a_5116_);
lean_ctor_set(v_reuseFailAlloc_5144_, 17, v_b_5117_);
lean_ctor_set(v_reuseFailAlloc_5144_, 18, v_B_5118_);
lean_ctor_set(v_reuseFailAlloc_5144_, 19, v_h_5119_);
lean_ctor_set(v_reuseFailAlloc_5144_, 20, v_K_5120_);
lean_ctor_set(v_reuseFailAlloc_5144_, 21, v_k_5121_);
lean_ctor_set(v_reuseFailAlloc_5144_, 22, v_H_5122_);
lean_ctor_set(v_reuseFailAlloc_5144_, 23, v_m_5123_);
lean_ctor_set(v_reuseFailAlloc_5144_, 24, v_s_5124_);
lean_ctor_set(v_reuseFailAlloc_5144_, 25, v_S_5125_);
lean_ctor_set(v_reuseFailAlloc_5144_, 26, v_A_5126_);
lean_ctor_set(v_reuseFailAlloc_5144_, 27, v_n_5127_);
lean_ctor_set(v_reuseFailAlloc_5144_, 28, v_N_5128_);
lean_ctor_set(v_reuseFailAlloc_5144_, 29, v_V_5129_);
lean_ctor_set(v_reuseFailAlloc_5144_, 30, v_z_5130_);
lean_ctor_set(v_reuseFailAlloc_5144_, 31, v_zabbrev_5131_);
lean_ctor_set(v_reuseFailAlloc_5144_, 32, v_v_5132_);
lean_ctor_set(v_reuseFailAlloc_5144_, 33, v_O_5133_);
lean_ctor_set(v_reuseFailAlloc_5144_, 34, v_X_5134_);
lean_ctor_set(v_reuseFailAlloc_5144_, 35, v_x_5135_);
lean_ctor_set(v_reuseFailAlloc_5144_, 36, v_Z_5136_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
}
case 11:
{
lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5200_; 
v_isSharedCheck_5200_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5200_ == 0)
{
lean_object* v_unused_5201_; 
v_unused_5201_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5201_);
v___x_5151_ = v_modifier_4583_;
v_isShared_5152_ = v_isSharedCheck_5200_;
goto v_resetjp_5150_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5200_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v_G_5153_; lean_object* v_y_5154_; lean_object* v_u_5155_; lean_object* v_Y_5156_; lean_object* v_D_5157_; lean_object* v_M_5158_; lean_object* v_L_5159_; lean_object* v_d_5160_; lean_object* v_Q_5161_; lean_object* v_q_5162_; lean_object* v_w_5163_; lean_object* v_E_5164_; lean_object* v_e_5165_; lean_object* v_c_5166_; lean_object* v_F_5167_; lean_object* v_a_5168_; lean_object* v_b_5169_; lean_object* v_B_5170_; lean_object* v_h_5171_; lean_object* v_K_5172_; lean_object* v_k_5173_; lean_object* v_H_5174_; lean_object* v_m_5175_; lean_object* v_s_5176_; lean_object* v_S_5177_; lean_object* v_A_5178_; lean_object* v_n_5179_; lean_object* v_N_5180_; lean_object* v_V_5181_; lean_object* v_z_5182_; lean_object* v_zabbrev_5183_; lean_object* v_v_5184_; lean_object* v_O_5185_; lean_object* v_X_5186_; lean_object* v_x_5187_; lean_object* v_Z_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5198_; 
v_G_5153_ = lean_ctor_get(v_date_4582_, 0);
v_y_5154_ = lean_ctor_get(v_date_4582_, 1);
v_u_5155_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5156_ = lean_ctor_get(v_date_4582_, 3);
v_D_5157_ = lean_ctor_get(v_date_4582_, 4);
v_M_5158_ = lean_ctor_get(v_date_4582_, 5);
v_L_5159_ = lean_ctor_get(v_date_4582_, 6);
v_d_5160_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5161_ = lean_ctor_get(v_date_4582_, 8);
v_q_5162_ = lean_ctor_get(v_date_4582_, 9);
v_w_5163_ = lean_ctor_get(v_date_4582_, 10);
v_E_5164_ = lean_ctor_get(v_date_4582_, 12);
v_e_5165_ = lean_ctor_get(v_date_4582_, 13);
v_c_5166_ = lean_ctor_get(v_date_4582_, 14);
v_F_5167_ = lean_ctor_get(v_date_4582_, 15);
v_a_5168_ = lean_ctor_get(v_date_4582_, 16);
v_b_5169_ = lean_ctor_get(v_date_4582_, 17);
v_B_5170_ = lean_ctor_get(v_date_4582_, 18);
v_h_5171_ = lean_ctor_get(v_date_4582_, 19);
v_K_5172_ = lean_ctor_get(v_date_4582_, 20);
v_k_5173_ = lean_ctor_get(v_date_4582_, 21);
v_H_5174_ = lean_ctor_get(v_date_4582_, 22);
v_m_5175_ = lean_ctor_get(v_date_4582_, 23);
v_s_5176_ = lean_ctor_get(v_date_4582_, 24);
v_S_5177_ = lean_ctor_get(v_date_4582_, 25);
v_A_5178_ = lean_ctor_get(v_date_4582_, 26);
v_n_5179_ = lean_ctor_get(v_date_4582_, 27);
v_N_5180_ = lean_ctor_get(v_date_4582_, 28);
v_V_5181_ = lean_ctor_get(v_date_4582_, 29);
v_z_5182_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5183_ = lean_ctor_get(v_date_4582_, 31);
v_v_5184_ = lean_ctor_get(v_date_4582_, 32);
v_O_5185_ = lean_ctor_get(v_date_4582_, 33);
v_X_5186_ = lean_ctor_get(v_date_4582_, 34);
v_x_5187_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5188_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5198_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5198_ == 0)
{
lean_object* v_unused_5199_; 
v_unused_5199_ = lean_ctor_get(v_date_4582_, 11);
lean_dec(v_unused_5199_);
v___x_5190_ = v_date_4582_;
v_isShared_5191_ = v_isSharedCheck_5198_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_Z_5188_);
lean_inc(v_x_5187_);
lean_inc(v_X_5186_);
lean_inc(v_O_5185_);
lean_inc(v_v_5184_);
lean_inc(v_zabbrev_5183_);
lean_inc(v_z_5182_);
lean_inc(v_V_5181_);
lean_inc(v_N_5180_);
lean_inc(v_n_5179_);
lean_inc(v_A_5178_);
lean_inc(v_S_5177_);
lean_inc(v_s_5176_);
lean_inc(v_m_5175_);
lean_inc(v_H_5174_);
lean_inc(v_k_5173_);
lean_inc(v_K_5172_);
lean_inc(v_h_5171_);
lean_inc(v_B_5170_);
lean_inc(v_b_5169_);
lean_inc(v_a_5168_);
lean_inc(v_F_5167_);
lean_inc(v_c_5166_);
lean_inc(v_e_5165_);
lean_inc(v_E_5164_);
lean_inc(v_w_5163_);
lean_inc(v_q_5162_);
lean_inc(v_Q_5161_);
lean_inc(v_d_5160_);
lean_inc(v_L_5159_);
lean_inc(v_M_5158_);
lean_inc(v_D_5157_);
lean_inc(v_Y_5156_);
lean_inc(v_u_5155_);
lean_inc(v_y_5154_);
lean_inc(v_G_5153_);
lean_dec(v_date_4582_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5198_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5152_ == 0)
{
lean_ctor_set_tag(v___x_5151_, 1);
lean_ctor_set(v___x_5151_, 0, v_data_4584_);
v___x_5193_ = v___x_5151_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v_data_4584_);
v___x_5193_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
lean_object* v___x_5195_; 
if (v_isShared_5191_ == 0)
{
lean_ctor_set(v___x_5190_, 11, v___x_5193_);
v___x_5195_ = v___x_5190_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_G_5153_);
lean_ctor_set(v_reuseFailAlloc_5196_, 1, v_y_5154_);
lean_ctor_set(v_reuseFailAlloc_5196_, 2, v_u_5155_);
lean_ctor_set(v_reuseFailAlloc_5196_, 3, v_Y_5156_);
lean_ctor_set(v_reuseFailAlloc_5196_, 4, v_D_5157_);
lean_ctor_set(v_reuseFailAlloc_5196_, 5, v_M_5158_);
lean_ctor_set(v_reuseFailAlloc_5196_, 6, v_L_5159_);
lean_ctor_set(v_reuseFailAlloc_5196_, 7, v_d_5160_);
lean_ctor_set(v_reuseFailAlloc_5196_, 8, v_Q_5161_);
lean_ctor_set(v_reuseFailAlloc_5196_, 9, v_q_5162_);
lean_ctor_set(v_reuseFailAlloc_5196_, 10, v_w_5163_);
lean_ctor_set(v_reuseFailAlloc_5196_, 11, v___x_5193_);
lean_ctor_set(v_reuseFailAlloc_5196_, 12, v_E_5164_);
lean_ctor_set(v_reuseFailAlloc_5196_, 13, v_e_5165_);
lean_ctor_set(v_reuseFailAlloc_5196_, 14, v_c_5166_);
lean_ctor_set(v_reuseFailAlloc_5196_, 15, v_F_5167_);
lean_ctor_set(v_reuseFailAlloc_5196_, 16, v_a_5168_);
lean_ctor_set(v_reuseFailAlloc_5196_, 17, v_b_5169_);
lean_ctor_set(v_reuseFailAlloc_5196_, 18, v_B_5170_);
lean_ctor_set(v_reuseFailAlloc_5196_, 19, v_h_5171_);
lean_ctor_set(v_reuseFailAlloc_5196_, 20, v_K_5172_);
lean_ctor_set(v_reuseFailAlloc_5196_, 21, v_k_5173_);
lean_ctor_set(v_reuseFailAlloc_5196_, 22, v_H_5174_);
lean_ctor_set(v_reuseFailAlloc_5196_, 23, v_m_5175_);
lean_ctor_set(v_reuseFailAlloc_5196_, 24, v_s_5176_);
lean_ctor_set(v_reuseFailAlloc_5196_, 25, v_S_5177_);
lean_ctor_set(v_reuseFailAlloc_5196_, 26, v_A_5178_);
lean_ctor_set(v_reuseFailAlloc_5196_, 27, v_n_5179_);
lean_ctor_set(v_reuseFailAlloc_5196_, 28, v_N_5180_);
lean_ctor_set(v_reuseFailAlloc_5196_, 29, v_V_5181_);
lean_ctor_set(v_reuseFailAlloc_5196_, 30, v_z_5182_);
lean_ctor_set(v_reuseFailAlloc_5196_, 31, v_zabbrev_5183_);
lean_ctor_set(v_reuseFailAlloc_5196_, 32, v_v_5184_);
lean_ctor_set(v_reuseFailAlloc_5196_, 33, v_O_5185_);
lean_ctor_set(v_reuseFailAlloc_5196_, 34, v_X_5186_);
lean_ctor_set(v_reuseFailAlloc_5196_, 35, v_x_5187_);
lean_ctor_set(v_reuseFailAlloc_5196_, 36, v_Z_5188_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
}
case 12:
{
lean_object* v_G_5202_; lean_object* v_y_5203_; lean_object* v_u_5204_; lean_object* v_Y_5205_; lean_object* v_D_5206_; lean_object* v_M_5207_; lean_object* v_L_5208_; lean_object* v_d_5209_; lean_object* v_Q_5210_; lean_object* v_q_5211_; lean_object* v_w_5212_; lean_object* v_W_5213_; lean_object* v_e_5214_; lean_object* v_c_5215_; lean_object* v_F_5216_; lean_object* v_a_5217_; lean_object* v_b_5218_; lean_object* v_B_5219_; lean_object* v_h_5220_; lean_object* v_K_5221_; lean_object* v_k_5222_; lean_object* v_H_5223_; lean_object* v_m_5224_; lean_object* v_s_5225_; lean_object* v_S_5226_; lean_object* v_A_5227_; lean_object* v_n_5228_; lean_object* v_N_5229_; lean_object* v_V_5230_; lean_object* v_z_5231_; lean_object* v_zabbrev_5232_; lean_object* v_v_5233_; lean_object* v_O_5234_; lean_object* v_X_5235_; lean_object* v_x_5236_; lean_object* v_Z_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5245_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_G_5202_ = lean_ctor_get(v_date_4582_, 0);
v_y_5203_ = lean_ctor_get(v_date_4582_, 1);
v_u_5204_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5205_ = lean_ctor_get(v_date_4582_, 3);
v_D_5206_ = lean_ctor_get(v_date_4582_, 4);
v_M_5207_ = lean_ctor_get(v_date_4582_, 5);
v_L_5208_ = lean_ctor_get(v_date_4582_, 6);
v_d_5209_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5210_ = lean_ctor_get(v_date_4582_, 8);
v_q_5211_ = lean_ctor_get(v_date_4582_, 9);
v_w_5212_ = lean_ctor_get(v_date_4582_, 10);
v_W_5213_ = lean_ctor_get(v_date_4582_, 11);
v_e_5214_ = lean_ctor_get(v_date_4582_, 13);
v_c_5215_ = lean_ctor_get(v_date_4582_, 14);
v_F_5216_ = lean_ctor_get(v_date_4582_, 15);
v_a_5217_ = lean_ctor_get(v_date_4582_, 16);
v_b_5218_ = lean_ctor_get(v_date_4582_, 17);
v_B_5219_ = lean_ctor_get(v_date_4582_, 18);
v_h_5220_ = lean_ctor_get(v_date_4582_, 19);
v_K_5221_ = lean_ctor_get(v_date_4582_, 20);
v_k_5222_ = lean_ctor_get(v_date_4582_, 21);
v_H_5223_ = lean_ctor_get(v_date_4582_, 22);
v_m_5224_ = lean_ctor_get(v_date_4582_, 23);
v_s_5225_ = lean_ctor_get(v_date_4582_, 24);
v_S_5226_ = lean_ctor_get(v_date_4582_, 25);
v_A_5227_ = lean_ctor_get(v_date_4582_, 26);
v_n_5228_ = lean_ctor_get(v_date_4582_, 27);
v_N_5229_ = lean_ctor_get(v_date_4582_, 28);
v_V_5230_ = lean_ctor_get(v_date_4582_, 29);
v_z_5231_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5232_ = lean_ctor_get(v_date_4582_, 31);
v_v_5233_ = lean_ctor_get(v_date_4582_, 32);
v_O_5234_ = lean_ctor_get(v_date_4582_, 33);
v_X_5235_ = lean_ctor_get(v_date_4582_, 34);
v_x_5236_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5237_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5245_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5245_ == 0)
{
lean_object* v_unused_5246_; 
v_unused_5246_ = lean_ctor_get(v_date_4582_, 12);
lean_dec(v_unused_5246_);
v___x_5239_ = v_date_4582_;
v_isShared_5240_ = v_isSharedCheck_5245_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_Z_5237_);
lean_inc(v_x_5236_);
lean_inc(v_X_5235_);
lean_inc(v_O_5234_);
lean_inc(v_v_5233_);
lean_inc(v_zabbrev_5232_);
lean_inc(v_z_5231_);
lean_inc(v_V_5230_);
lean_inc(v_N_5229_);
lean_inc(v_n_5228_);
lean_inc(v_A_5227_);
lean_inc(v_S_5226_);
lean_inc(v_s_5225_);
lean_inc(v_m_5224_);
lean_inc(v_H_5223_);
lean_inc(v_k_5222_);
lean_inc(v_K_5221_);
lean_inc(v_h_5220_);
lean_inc(v_B_5219_);
lean_inc(v_b_5218_);
lean_inc(v_a_5217_);
lean_inc(v_F_5216_);
lean_inc(v_c_5215_);
lean_inc(v_e_5214_);
lean_inc(v_W_5213_);
lean_inc(v_w_5212_);
lean_inc(v_q_5211_);
lean_inc(v_Q_5210_);
lean_inc(v_d_5209_);
lean_inc(v_L_5208_);
lean_inc(v_M_5207_);
lean_inc(v_D_5206_);
lean_inc(v_Y_5205_);
lean_inc(v_u_5204_);
lean_inc(v_y_5203_);
lean_inc(v_G_5202_);
lean_dec(v_date_4582_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5245_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5241_; lean_object* v___x_5243_; 
v___x_5241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5241_, 0, v_data_4584_);
if (v_isShared_5240_ == 0)
{
lean_ctor_set(v___x_5239_, 12, v___x_5241_);
v___x_5243_ = v___x_5239_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_G_5202_);
lean_ctor_set(v_reuseFailAlloc_5244_, 1, v_y_5203_);
lean_ctor_set(v_reuseFailAlloc_5244_, 2, v_u_5204_);
lean_ctor_set(v_reuseFailAlloc_5244_, 3, v_Y_5205_);
lean_ctor_set(v_reuseFailAlloc_5244_, 4, v_D_5206_);
lean_ctor_set(v_reuseFailAlloc_5244_, 5, v_M_5207_);
lean_ctor_set(v_reuseFailAlloc_5244_, 6, v_L_5208_);
lean_ctor_set(v_reuseFailAlloc_5244_, 7, v_d_5209_);
lean_ctor_set(v_reuseFailAlloc_5244_, 8, v_Q_5210_);
lean_ctor_set(v_reuseFailAlloc_5244_, 9, v_q_5211_);
lean_ctor_set(v_reuseFailAlloc_5244_, 10, v_w_5212_);
lean_ctor_set(v_reuseFailAlloc_5244_, 11, v_W_5213_);
lean_ctor_set(v_reuseFailAlloc_5244_, 12, v___x_5241_);
lean_ctor_set(v_reuseFailAlloc_5244_, 13, v_e_5214_);
lean_ctor_set(v_reuseFailAlloc_5244_, 14, v_c_5215_);
lean_ctor_set(v_reuseFailAlloc_5244_, 15, v_F_5216_);
lean_ctor_set(v_reuseFailAlloc_5244_, 16, v_a_5217_);
lean_ctor_set(v_reuseFailAlloc_5244_, 17, v_b_5218_);
lean_ctor_set(v_reuseFailAlloc_5244_, 18, v_B_5219_);
lean_ctor_set(v_reuseFailAlloc_5244_, 19, v_h_5220_);
lean_ctor_set(v_reuseFailAlloc_5244_, 20, v_K_5221_);
lean_ctor_set(v_reuseFailAlloc_5244_, 21, v_k_5222_);
lean_ctor_set(v_reuseFailAlloc_5244_, 22, v_H_5223_);
lean_ctor_set(v_reuseFailAlloc_5244_, 23, v_m_5224_);
lean_ctor_set(v_reuseFailAlloc_5244_, 24, v_s_5225_);
lean_ctor_set(v_reuseFailAlloc_5244_, 25, v_S_5226_);
lean_ctor_set(v_reuseFailAlloc_5244_, 26, v_A_5227_);
lean_ctor_set(v_reuseFailAlloc_5244_, 27, v_n_5228_);
lean_ctor_set(v_reuseFailAlloc_5244_, 28, v_N_5229_);
lean_ctor_set(v_reuseFailAlloc_5244_, 29, v_V_5230_);
lean_ctor_set(v_reuseFailAlloc_5244_, 30, v_z_5231_);
lean_ctor_set(v_reuseFailAlloc_5244_, 31, v_zabbrev_5232_);
lean_ctor_set(v_reuseFailAlloc_5244_, 32, v_v_5233_);
lean_ctor_set(v_reuseFailAlloc_5244_, 33, v_O_5234_);
lean_ctor_set(v_reuseFailAlloc_5244_, 34, v_X_5235_);
lean_ctor_set(v_reuseFailAlloc_5244_, 35, v_x_5236_);
lean_ctor_set(v_reuseFailAlloc_5244_, 36, v_Z_5237_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
case 13:
{
lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5297_; 
v_isSharedCheck_5297_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5297_ == 0)
{
lean_object* v_unused_5298_; 
v_unused_5298_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5298_);
v___x_5248_ = v_modifier_4583_;
v_isShared_5249_ = v_isSharedCheck_5297_;
goto v_resetjp_5247_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5297_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v_G_5250_; lean_object* v_y_5251_; lean_object* v_u_5252_; lean_object* v_Y_5253_; lean_object* v_D_5254_; lean_object* v_M_5255_; lean_object* v_L_5256_; lean_object* v_d_5257_; lean_object* v_Q_5258_; lean_object* v_q_5259_; lean_object* v_w_5260_; lean_object* v_W_5261_; lean_object* v_E_5262_; lean_object* v_c_5263_; lean_object* v_F_5264_; lean_object* v_a_5265_; lean_object* v_b_5266_; lean_object* v_B_5267_; lean_object* v_h_5268_; lean_object* v_K_5269_; lean_object* v_k_5270_; lean_object* v_H_5271_; lean_object* v_m_5272_; lean_object* v_s_5273_; lean_object* v_S_5274_; lean_object* v_A_5275_; lean_object* v_n_5276_; lean_object* v_N_5277_; lean_object* v_V_5278_; lean_object* v_z_5279_; lean_object* v_zabbrev_5280_; lean_object* v_v_5281_; lean_object* v_O_5282_; lean_object* v_X_5283_; lean_object* v_x_5284_; lean_object* v_Z_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5295_; 
v_G_5250_ = lean_ctor_get(v_date_4582_, 0);
v_y_5251_ = lean_ctor_get(v_date_4582_, 1);
v_u_5252_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5253_ = lean_ctor_get(v_date_4582_, 3);
v_D_5254_ = lean_ctor_get(v_date_4582_, 4);
v_M_5255_ = lean_ctor_get(v_date_4582_, 5);
v_L_5256_ = lean_ctor_get(v_date_4582_, 6);
v_d_5257_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5258_ = lean_ctor_get(v_date_4582_, 8);
v_q_5259_ = lean_ctor_get(v_date_4582_, 9);
v_w_5260_ = lean_ctor_get(v_date_4582_, 10);
v_W_5261_ = lean_ctor_get(v_date_4582_, 11);
v_E_5262_ = lean_ctor_get(v_date_4582_, 12);
v_c_5263_ = lean_ctor_get(v_date_4582_, 14);
v_F_5264_ = lean_ctor_get(v_date_4582_, 15);
v_a_5265_ = lean_ctor_get(v_date_4582_, 16);
v_b_5266_ = lean_ctor_get(v_date_4582_, 17);
v_B_5267_ = lean_ctor_get(v_date_4582_, 18);
v_h_5268_ = lean_ctor_get(v_date_4582_, 19);
v_K_5269_ = lean_ctor_get(v_date_4582_, 20);
v_k_5270_ = lean_ctor_get(v_date_4582_, 21);
v_H_5271_ = lean_ctor_get(v_date_4582_, 22);
v_m_5272_ = lean_ctor_get(v_date_4582_, 23);
v_s_5273_ = lean_ctor_get(v_date_4582_, 24);
v_S_5274_ = lean_ctor_get(v_date_4582_, 25);
v_A_5275_ = lean_ctor_get(v_date_4582_, 26);
v_n_5276_ = lean_ctor_get(v_date_4582_, 27);
v_N_5277_ = lean_ctor_get(v_date_4582_, 28);
v_V_5278_ = lean_ctor_get(v_date_4582_, 29);
v_z_5279_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5280_ = lean_ctor_get(v_date_4582_, 31);
v_v_5281_ = lean_ctor_get(v_date_4582_, 32);
v_O_5282_ = lean_ctor_get(v_date_4582_, 33);
v_X_5283_ = lean_ctor_get(v_date_4582_, 34);
v_x_5284_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5285_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5295_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5295_ == 0)
{
lean_object* v_unused_5296_; 
v_unused_5296_ = lean_ctor_get(v_date_4582_, 13);
lean_dec(v_unused_5296_);
v___x_5287_ = v_date_4582_;
v_isShared_5288_ = v_isSharedCheck_5295_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_Z_5285_);
lean_inc(v_x_5284_);
lean_inc(v_X_5283_);
lean_inc(v_O_5282_);
lean_inc(v_v_5281_);
lean_inc(v_zabbrev_5280_);
lean_inc(v_z_5279_);
lean_inc(v_V_5278_);
lean_inc(v_N_5277_);
lean_inc(v_n_5276_);
lean_inc(v_A_5275_);
lean_inc(v_S_5274_);
lean_inc(v_s_5273_);
lean_inc(v_m_5272_);
lean_inc(v_H_5271_);
lean_inc(v_k_5270_);
lean_inc(v_K_5269_);
lean_inc(v_h_5268_);
lean_inc(v_B_5267_);
lean_inc(v_b_5266_);
lean_inc(v_a_5265_);
lean_inc(v_F_5264_);
lean_inc(v_c_5263_);
lean_inc(v_E_5262_);
lean_inc(v_W_5261_);
lean_inc(v_w_5260_);
lean_inc(v_q_5259_);
lean_inc(v_Q_5258_);
lean_inc(v_d_5257_);
lean_inc(v_L_5256_);
lean_inc(v_M_5255_);
lean_inc(v_D_5254_);
lean_inc(v_Y_5253_);
lean_inc(v_u_5252_);
lean_inc(v_y_5251_);
lean_inc(v_G_5250_);
lean_dec(v_date_4582_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5295_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5249_ == 0)
{
lean_ctor_set_tag(v___x_5248_, 1);
lean_ctor_set(v___x_5248_, 0, v_data_4584_);
v___x_5290_ = v___x_5248_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_data_4584_);
v___x_5290_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
lean_object* v___x_5292_; 
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 13, v___x_5290_);
v___x_5292_ = v___x_5287_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_G_5250_);
lean_ctor_set(v_reuseFailAlloc_5293_, 1, v_y_5251_);
lean_ctor_set(v_reuseFailAlloc_5293_, 2, v_u_5252_);
lean_ctor_set(v_reuseFailAlloc_5293_, 3, v_Y_5253_);
lean_ctor_set(v_reuseFailAlloc_5293_, 4, v_D_5254_);
lean_ctor_set(v_reuseFailAlloc_5293_, 5, v_M_5255_);
lean_ctor_set(v_reuseFailAlloc_5293_, 6, v_L_5256_);
lean_ctor_set(v_reuseFailAlloc_5293_, 7, v_d_5257_);
lean_ctor_set(v_reuseFailAlloc_5293_, 8, v_Q_5258_);
lean_ctor_set(v_reuseFailAlloc_5293_, 9, v_q_5259_);
lean_ctor_set(v_reuseFailAlloc_5293_, 10, v_w_5260_);
lean_ctor_set(v_reuseFailAlloc_5293_, 11, v_W_5261_);
lean_ctor_set(v_reuseFailAlloc_5293_, 12, v_E_5262_);
lean_ctor_set(v_reuseFailAlloc_5293_, 13, v___x_5290_);
lean_ctor_set(v_reuseFailAlloc_5293_, 14, v_c_5263_);
lean_ctor_set(v_reuseFailAlloc_5293_, 15, v_F_5264_);
lean_ctor_set(v_reuseFailAlloc_5293_, 16, v_a_5265_);
lean_ctor_set(v_reuseFailAlloc_5293_, 17, v_b_5266_);
lean_ctor_set(v_reuseFailAlloc_5293_, 18, v_B_5267_);
lean_ctor_set(v_reuseFailAlloc_5293_, 19, v_h_5268_);
lean_ctor_set(v_reuseFailAlloc_5293_, 20, v_K_5269_);
lean_ctor_set(v_reuseFailAlloc_5293_, 21, v_k_5270_);
lean_ctor_set(v_reuseFailAlloc_5293_, 22, v_H_5271_);
lean_ctor_set(v_reuseFailAlloc_5293_, 23, v_m_5272_);
lean_ctor_set(v_reuseFailAlloc_5293_, 24, v_s_5273_);
lean_ctor_set(v_reuseFailAlloc_5293_, 25, v_S_5274_);
lean_ctor_set(v_reuseFailAlloc_5293_, 26, v_A_5275_);
lean_ctor_set(v_reuseFailAlloc_5293_, 27, v_n_5276_);
lean_ctor_set(v_reuseFailAlloc_5293_, 28, v_N_5277_);
lean_ctor_set(v_reuseFailAlloc_5293_, 29, v_V_5278_);
lean_ctor_set(v_reuseFailAlloc_5293_, 30, v_z_5279_);
lean_ctor_set(v_reuseFailAlloc_5293_, 31, v_zabbrev_5280_);
lean_ctor_set(v_reuseFailAlloc_5293_, 32, v_v_5281_);
lean_ctor_set(v_reuseFailAlloc_5293_, 33, v_O_5282_);
lean_ctor_set(v_reuseFailAlloc_5293_, 34, v_X_5283_);
lean_ctor_set(v_reuseFailAlloc_5293_, 35, v_x_5284_);
lean_ctor_set(v_reuseFailAlloc_5293_, 36, v_Z_5285_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
}
case 14:
{
lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5349_; 
v_isSharedCheck_5349_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5349_ == 0)
{
lean_object* v_unused_5350_; 
v_unused_5350_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5350_);
v___x_5300_ = v_modifier_4583_;
v_isShared_5301_ = v_isSharedCheck_5349_;
goto v_resetjp_5299_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5349_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v_G_5302_; lean_object* v_y_5303_; lean_object* v_u_5304_; lean_object* v_Y_5305_; lean_object* v_D_5306_; lean_object* v_M_5307_; lean_object* v_L_5308_; lean_object* v_d_5309_; lean_object* v_Q_5310_; lean_object* v_q_5311_; lean_object* v_w_5312_; lean_object* v_W_5313_; lean_object* v_E_5314_; lean_object* v_e_5315_; lean_object* v_F_5316_; lean_object* v_a_5317_; lean_object* v_b_5318_; lean_object* v_B_5319_; lean_object* v_h_5320_; lean_object* v_K_5321_; lean_object* v_k_5322_; lean_object* v_H_5323_; lean_object* v_m_5324_; lean_object* v_s_5325_; lean_object* v_S_5326_; lean_object* v_A_5327_; lean_object* v_n_5328_; lean_object* v_N_5329_; lean_object* v_V_5330_; lean_object* v_z_5331_; lean_object* v_zabbrev_5332_; lean_object* v_v_5333_; lean_object* v_O_5334_; lean_object* v_X_5335_; lean_object* v_x_5336_; lean_object* v_Z_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5347_; 
v_G_5302_ = lean_ctor_get(v_date_4582_, 0);
v_y_5303_ = lean_ctor_get(v_date_4582_, 1);
v_u_5304_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5305_ = lean_ctor_get(v_date_4582_, 3);
v_D_5306_ = lean_ctor_get(v_date_4582_, 4);
v_M_5307_ = lean_ctor_get(v_date_4582_, 5);
v_L_5308_ = lean_ctor_get(v_date_4582_, 6);
v_d_5309_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5310_ = lean_ctor_get(v_date_4582_, 8);
v_q_5311_ = lean_ctor_get(v_date_4582_, 9);
v_w_5312_ = lean_ctor_get(v_date_4582_, 10);
v_W_5313_ = lean_ctor_get(v_date_4582_, 11);
v_E_5314_ = lean_ctor_get(v_date_4582_, 12);
v_e_5315_ = lean_ctor_get(v_date_4582_, 13);
v_F_5316_ = lean_ctor_get(v_date_4582_, 15);
v_a_5317_ = lean_ctor_get(v_date_4582_, 16);
v_b_5318_ = lean_ctor_get(v_date_4582_, 17);
v_B_5319_ = lean_ctor_get(v_date_4582_, 18);
v_h_5320_ = lean_ctor_get(v_date_4582_, 19);
v_K_5321_ = lean_ctor_get(v_date_4582_, 20);
v_k_5322_ = lean_ctor_get(v_date_4582_, 21);
v_H_5323_ = lean_ctor_get(v_date_4582_, 22);
v_m_5324_ = lean_ctor_get(v_date_4582_, 23);
v_s_5325_ = lean_ctor_get(v_date_4582_, 24);
v_S_5326_ = lean_ctor_get(v_date_4582_, 25);
v_A_5327_ = lean_ctor_get(v_date_4582_, 26);
v_n_5328_ = lean_ctor_get(v_date_4582_, 27);
v_N_5329_ = lean_ctor_get(v_date_4582_, 28);
v_V_5330_ = lean_ctor_get(v_date_4582_, 29);
v_z_5331_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5332_ = lean_ctor_get(v_date_4582_, 31);
v_v_5333_ = lean_ctor_get(v_date_4582_, 32);
v_O_5334_ = lean_ctor_get(v_date_4582_, 33);
v_X_5335_ = lean_ctor_get(v_date_4582_, 34);
v_x_5336_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5337_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5347_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5347_ == 0)
{
lean_object* v_unused_5348_; 
v_unused_5348_ = lean_ctor_get(v_date_4582_, 14);
lean_dec(v_unused_5348_);
v___x_5339_ = v_date_4582_;
v_isShared_5340_ = v_isSharedCheck_5347_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_Z_5337_);
lean_inc(v_x_5336_);
lean_inc(v_X_5335_);
lean_inc(v_O_5334_);
lean_inc(v_v_5333_);
lean_inc(v_zabbrev_5332_);
lean_inc(v_z_5331_);
lean_inc(v_V_5330_);
lean_inc(v_N_5329_);
lean_inc(v_n_5328_);
lean_inc(v_A_5327_);
lean_inc(v_S_5326_);
lean_inc(v_s_5325_);
lean_inc(v_m_5324_);
lean_inc(v_H_5323_);
lean_inc(v_k_5322_);
lean_inc(v_K_5321_);
lean_inc(v_h_5320_);
lean_inc(v_B_5319_);
lean_inc(v_b_5318_);
lean_inc(v_a_5317_);
lean_inc(v_F_5316_);
lean_inc(v_e_5315_);
lean_inc(v_E_5314_);
lean_inc(v_W_5313_);
lean_inc(v_w_5312_);
lean_inc(v_q_5311_);
lean_inc(v_Q_5310_);
lean_inc(v_d_5309_);
lean_inc(v_L_5308_);
lean_inc(v_M_5307_);
lean_inc(v_D_5306_);
lean_inc(v_Y_5305_);
lean_inc(v_u_5304_);
lean_inc(v_y_5303_);
lean_inc(v_G_5302_);
lean_dec(v_date_4582_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5347_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v___x_5342_; 
if (v_isShared_5301_ == 0)
{
lean_ctor_set_tag(v___x_5300_, 1);
lean_ctor_set(v___x_5300_, 0, v_data_4584_);
v___x_5342_ = v___x_5300_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_data_4584_);
v___x_5342_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
lean_object* v___x_5344_; 
if (v_isShared_5340_ == 0)
{
lean_ctor_set(v___x_5339_, 14, v___x_5342_);
v___x_5344_ = v___x_5339_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_G_5302_);
lean_ctor_set(v_reuseFailAlloc_5345_, 1, v_y_5303_);
lean_ctor_set(v_reuseFailAlloc_5345_, 2, v_u_5304_);
lean_ctor_set(v_reuseFailAlloc_5345_, 3, v_Y_5305_);
lean_ctor_set(v_reuseFailAlloc_5345_, 4, v_D_5306_);
lean_ctor_set(v_reuseFailAlloc_5345_, 5, v_M_5307_);
lean_ctor_set(v_reuseFailAlloc_5345_, 6, v_L_5308_);
lean_ctor_set(v_reuseFailAlloc_5345_, 7, v_d_5309_);
lean_ctor_set(v_reuseFailAlloc_5345_, 8, v_Q_5310_);
lean_ctor_set(v_reuseFailAlloc_5345_, 9, v_q_5311_);
lean_ctor_set(v_reuseFailAlloc_5345_, 10, v_w_5312_);
lean_ctor_set(v_reuseFailAlloc_5345_, 11, v_W_5313_);
lean_ctor_set(v_reuseFailAlloc_5345_, 12, v_E_5314_);
lean_ctor_set(v_reuseFailAlloc_5345_, 13, v_e_5315_);
lean_ctor_set(v_reuseFailAlloc_5345_, 14, v___x_5342_);
lean_ctor_set(v_reuseFailAlloc_5345_, 15, v_F_5316_);
lean_ctor_set(v_reuseFailAlloc_5345_, 16, v_a_5317_);
lean_ctor_set(v_reuseFailAlloc_5345_, 17, v_b_5318_);
lean_ctor_set(v_reuseFailAlloc_5345_, 18, v_B_5319_);
lean_ctor_set(v_reuseFailAlloc_5345_, 19, v_h_5320_);
lean_ctor_set(v_reuseFailAlloc_5345_, 20, v_K_5321_);
lean_ctor_set(v_reuseFailAlloc_5345_, 21, v_k_5322_);
lean_ctor_set(v_reuseFailAlloc_5345_, 22, v_H_5323_);
lean_ctor_set(v_reuseFailAlloc_5345_, 23, v_m_5324_);
lean_ctor_set(v_reuseFailAlloc_5345_, 24, v_s_5325_);
lean_ctor_set(v_reuseFailAlloc_5345_, 25, v_S_5326_);
lean_ctor_set(v_reuseFailAlloc_5345_, 26, v_A_5327_);
lean_ctor_set(v_reuseFailAlloc_5345_, 27, v_n_5328_);
lean_ctor_set(v_reuseFailAlloc_5345_, 28, v_N_5329_);
lean_ctor_set(v_reuseFailAlloc_5345_, 29, v_V_5330_);
lean_ctor_set(v_reuseFailAlloc_5345_, 30, v_z_5331_);
lean_ctor_set(v_reuseFailAlloc_5345_, 31, v_zabbrev_5332_);
lean_ctor_set(v_reuseFailAlloc_5345_, 32, v_v_5333_);
lean_ctor_set(v_reuseFailAlloc_5345_, 33, v_O_5334_);
lean_ctor_set(v_reuseFailAlloc_5345_, 34, v_X_5335_);
lean_ctor_set(v_reuseFailAlloc_5345_, 35, v_x_5336_);
lean_ctor_set(v_reuseFailAlloc_5345_, 36, v_Z_5337_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
}
}
case 15:
{
lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5401_; 
v_isSharedCheck_5401_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5401_ == 0)
{
lean_object* v_unused_5402_; 
v_unused_5402_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5402_);
v___x_5352_ = v_modifier_4583_;
v_isShared_5353_ = v_isSharedCheck_5401_;
goto v_resetjp_5351_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5401_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v_G_5354_; lean_object* v_y_5355_; lean_object* v_u_5356_; lean_object* v_Y_5357_; lean_object* v_D_5358_; lean_object* v_M_5359_; lean_object* v_L_5360_; lean_object* v_d_5361_; lean_object* v_Q_5362_; lean_object* v_q_5363_; lean_object* v_w_5364_; lean_object* v_W_5365_; lean_object* v_E_5366_; lean_object* v_e_5367_; lean_object* v_c_5368_; lean_object* v_a_5369_; lean_object* v_b_5370_; lean_object* v_B_5371_; lean_object* v_h_5372_; lean_object* v_K_5373_; lean_object* v_k_5374_; lean_object* v_H_5375_; lean_object* v_m_5376_; lean_object* v_s_5377_; lean_object* v_S_5378_; lean_object* v_A_5379_; lean_object* v_n_5380_; lean_object* v_N_5381_; lean_object* v_V_5382_; lean_object* v_z_5383_; lean_object* v_zabbrev_5384_; lean_object* v_v_5385_; lean_object* v_O_5386_; lean_object* v_X_5387_; lean_object* v_x_5388_; lean_object* v_Z_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5399_; 
v_G_5354_ = lean_ctor_get(v_date_4582_, 0);
v_y_5355_ = lean_ctor_get(v_date_4582_, 1);
v_u_5356_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5357_ = lean_ctor_get(v_date_4582_, 3);
v_D_5358_ = lean_ctor_get(v_date_4582_, 4);
v_M_5359_ = lean_ctor_get(v_date_4582_, 5);
v_L_5360_ = lean_ctor_get(v_date_4582_, 6);
v_d_5361_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5362_ = lean_ctor_get(v_date_4582_, 8);
v_q_5363_ = lean_ctor_get(v_date_4582_, 9);
v_w_5364_ = lean_ctor_get(v_date_4582_, 10);
v_W_5365_ = lean_ctor_get(v_date_4582_, 11);
v_E_5366_ = lean_ctor_get(v_date_4582_, 12);
v_e_5367_ = lean_ctor_get(v_date_4582_, 13);
v_c_5368_ = lean_ctor_get(v_date_4582_, 14);
v_a_5369_ = lean_ctor_get(v_date_4582_, 16);
v_b_5370_ = lean_ctor_get(v_date_4582_, 17);
v_B_5371_ = lean_ctor_get(v_date_4582_, 18);
v_h_5372_ = lean_ctor_get(v_date_4582_, 19);
v_K_5373_ = lean_ctor_get(v_date_4582_, 20);
v_k_5374_ = lean_ctor_get(v_date_4582_, 21);
v_H_5375_ = lean_ctor_get(v_date_4582_, 22);
v_m_5376_ = lean_ctor_get(v_date_4582_, 23);
v_s_5377_ = lean_ctor_get(v_date_4582_, 24);
v_S_5378_ = lean_ctor_get(v_date_4582_, 25);
v_A_5379_ = lean_ctor_get(v_date_4582_, 26);
v_n_5380_ = lean_ctor_get(v_date_4582_, 27);
v_N_5381_ = lean_ctor_get(v_date_4582_, 28);
v_V_5382_ = lean_ctor_get(v_date_4582_, 29);
v_z_5383_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5384_ = lean_ctor_get(v_date_4582_, 31);
v_v_5385_ = lean_ctor_get(v_date_4582_, 32);
v_O_5386_ = lean_ctor_get(v_date_4582_, 33);
v_X_5387_ = lean_ctor_get(v_date_4582_, 34);
v_x_5388_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5389_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5399_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5399_ == 0)
{
lean_object* v_unused_5400_; 
v_unused_5400_ = lean_ctor_get(v_date_4582_, 15);
lean_dec(v_unused_5400_);
v___x_5391_ = v_date_4582_;
v_isShared_5392_ = v_isSharedCheck_5399_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_Z_5389_);
lean_inc(v_x_5388_);
lean_inc(v_X_5387_);
lean_inc(v_O_5386_);
lean_inc(v_v_5385_);
lean_inc(v_zabbrev_5384_);
lean_inc(v_z_5383_);
lean_inc(v_V_5382_);
lean_inc(v_N_5381_);
lean_inc(v_n_5380_);
lean_inc(v_A_5379_);
lean_inc(v_S_5378_);
lean_inc(v_s_5377_);
lean_inc(v_m_5376_);
lean_inc(v_H_5375_);
lean_inc(v_k_5374_);
lean_inc(v_K_5373_);
lean_inc(v_h_5372_);
lean_inc(v_B_5371_);
lean_inc(v_b_5370_);
lean_inc(v_a_5369_);
lean_inc(v_c_5368_);
lean_inc(v_e_5367_);
lean_inc(v_E_5366_);
lean_inc(v_W_5365_);
lean_inc(v_w_5364_);
lean_inc(v_q_5363_);
lean_inc(v_Q_5362_);
lean_inc(v_d_5361_);
lean_inc(v_L_5360_);
lean_inc(v_M_5359_);
lean_inc(v_D_5358_);
lean_inc(v_Y_5357_);
lean_inc(v_u_5356_);
lean_inc(v_y_5355_);
lean_inc(v_G_5354_);
lean_dec(v_date_4582_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5399_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v___x_5394_; 
if (v_isShared_5353_ == 0)
{
lean_ctor_set_tag(v___x_5352_, 1);
lean_ctor_set(v___x_5352_, 0, v_data_4584_);
v___x_5394_ = v___x_5352_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v_data_4584_);
v___x_5394_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
lean_object* v___x_5396_; 
if (v_isShared_5392_ == 0)
{
lean_ctor_set(v___x_5391_, 15, v___x_5394_);
v___x_5396_ = v___x_5391_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_G_5354_);
lean_ctor_set(v_reuseFailAlloc_5397_, 1, v_y_5355_);
lean_ctor_set(v_reuseFailAlloc_5397_, 2, v_u_5356_);
lean_ctor_set(v_reuseFailAlloc_5397_, 3, v_Y_5357_);
lean_ctor_set(v_reuseFailAlloc_5397_, 4, v_D_5358_);
lean_ctor_set(v_reuseFailAlloc_5397_, 5, v_M_5359_);
lean_ctor_set(v_reuseFailAlloc_5397_, 6, v_L_5360_);
lean_ctor_set(v_reuseFailAlloc_5397_, 7, v_d_5361_);
lean_ctor_set(v_reuseFailAlloc_5397_, 8, v_Q_5362_);
lean_ctor_set(v_reuseFailAlloc_5397_, 9, v_q_5363_);
lean_ctor_set(v_reuseFailAlloc_5397_, 10, v_w_5364_);
lean_ctor_set(v_reuseFailAlloc_5397_, 11, v_W_5365_);
lean_ctor_set(v_reuseFailAlloc_5397_, 12, v_E_5366_);
lean_ctor_set(v_reuseFailAlloc_5397_, 13, v_e_5367_);
lean_ctor_set(v_reuseFailAlloc_5397_, 14, v_c_5368_);
lean_ctor_set(v_reuseFailAlloc_5397_, 15, v___x_5394_);
lean_ctor_set(v_reuseFailAlloc_5397_, 16, v_a_5369_);
lean_ctor_set(v_reuseFailAlloc_5397_, 17, v_b_5370_);
lean_ctor_set(v_reuseFailAlloc_5397_, 18, v_B_5371_);
lean_ctor_set(v_reuseFailAlloc_5397_, 19, v_h_5372_);
lean_ctor_set(v_reuseFailAlloc_5397_, 20, v_K_5373_);
lean_ctor_set(v_reuseFailAlloc_5397_, 21, v_k_5374_);
lean_ctor_set(v_reuseFailAlloc_5397_, 22, v_H_5375_);
lean_ctor_set(v_reuseFailAlloc_5397_, 23, v_m_5376_);
lean_ctor_set(v_reuseFailAlloc_5397_, 24, v_s_5377_);
lean_ctor_set(v_reuseFailAlloc_5397_, 25, v_S_5378_);
lean_ctor_set(v_reuseFailAlloc_5397_, 26, v_A_5379_);
lean_ctor_set(v_reuseFailAlloc_5397_, 27, v_n_5380_);
lean_ctor_set(v_reuseFailAlloc_5397_, 28, v_N_5381_);
lean_ctor_set(v_reuseFailAlloc_5397_, 29, v_V_5382_);
lean_ctor_set(v_reuseFailAlloc_5397_, 30, v_z_5383_);
lean_ctor_set(v_reuseFailAlloc_5397_, 31, v_zabbrev_5384_);
lean_ctor_set(v_reuseFailAlloc_5397_, 32, v_v_5385_);
lean_ctor_set(v_reuseFailAlloc_5397_, 33, v_O_5386_);
lean_ctor_set(v_reuseFailAlloc_5397_, 34, v_X_5387_);
lean_ctor_set(v_reuseFailAlloc_5397_, 35, v_x_5388_);
lean_ctor_set(v_reuseFailAlloc_5397_, 36, v_Z_5389_);
v___x_5396_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
return v___x_5396_;
}
}
}
}
}
case 16:
{
lean_object* v_G_5403_; lean_object* v_y_5404_; lean_object* v_u_5405_; lean_object* v_Y_5406_; lean_object* v_D_5407_; lean_object* v_M_5408_; lean_object* v_L_5409_; lean_object* v_d_5410_; lean_object* v_Q_5411_; lean_object* v_q_5412_; lean_object* v_w_5413_; lean_object* v_W_5414_; lean_object* v_E_5415_; lean_object* v_e_5416_; lean_object* v_c_5417_; lean_object* v_F_5418_; lean_object* v_b_5419_; lean_object* v_B_5420_; lean_object* v_h_5421_; lean_object* v_K_5422_; lean_object* v_k_5423_; lean_object* v_H_5424_; lean_object* v_m_5425_; lean_object* v_s_5426_; lean_object* v_S_5427_; lean_object* v_A_5428_; lean_object* v_n_5429_; lean_object* v_N_5430_; lean_object* v_V_5431_; lean_object* v_z_5432_; lean_object* v_zabbrev_5433_; lean_object* v_v_5434_; lean_object* v_O_5435_; lean_object* v_X_5436_; lean_object* v_x_5437_; lean_object* v_Z_5438_; lean_object* v___x_5440_; uint8_t v_isShared_5441_; uint8_t v_isSharedCheck_5446_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_G_5403_ = lean_ctor_get(v_date_4582_, 0);
v_y_5404_ = lean_ctor_get(v_date_4582_, 1);
v_u_5405_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5406_ = lean_ctor_get(v_date_4582_, 3);
v_D_5407_ = lean_ctor_get(v_date_4582_, 4);
v_M_5408_ = lean_ctor_get(v_date_4582_, 5);
v_L_5409_ = lean_ctor_get(v_date_4582_, 6);
v_d_5410_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5411_ = lean_ctor_get(v_date_4582_, 8);
v_q_5412_ = lean_ctor_get(v_date_4582_, 9);
v_w_5413_ = lean_ctor_get(v_date_4582_, 10);
v_W_5414_ = lean_ctor_get(v_date_4582_, 11);
v_E_5415_ = lean_ctor_get(v_date_4582_, 12);
v_e_5416_ = lean_ctor_get(v_date_4582_, 13);
v_c_5417_ = lean_ctor_get(v_date_4582_, 14);
v_F_5418_ = lean_ctor_get(v_date_4582_, 15);
v_b_5419_ = lean_ctor_get(v_date_4582_, 17);
v_B_5420_ = lean_ctor_get(v_date_4582_, 18);
v_h_5421_ = lean_ctor_get(v_date_4582_, 19);
v_K_5422_ = lean_ctor_get(v_date_4582_, 20);
v_k_5423_ = lean_ctor_get(v_date_4582_, 21);
v_H_5424_ = lean_ctor_get(v_date_4582_, 22);
v_m_5425_ = lean_ctor_get(v_date_4582_, 23);
v_s_5426_ = lean_ctor_get(v_date_4582_, 24);
v_S_5427_ = lean_ctor_get(v_date_4582_, 25);
v_A_5428_ = lean_ctor_get(v_date_4582_, 26);
v_n_5429_ = lean_ctor_get(v_date_4582_, 27);
v_N_5430_ = lean_ctor_get(v_date_4582_, 28);
v_V_5431_ = lean_ctor_get(v_date_4582_, 29);
v_z_5432_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5433_ = lean_ctor_get(v_date_4582_, 31);
v_v_5434_ = lean_ctor_get(v_date_4582_, 32);
v_O_5435_ = lean_ctor_get(v_date_4582_, 33);
v_X_5436_ = lean_ctor_get(v_date_4582_, 34);
v_x_5437_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5438_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5446_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5446_ == 0)
{
lean_object* v_unused_5447_; 
v_unused_5447_ = lean_ctor_get(v_date_4582_, 16);
lean_dec(v_unused_5447_);
v___x_5440_ = v_date_4582_;
v_isShared_5441_ = v_isSharedCheck_5446_;
goto v_resetjp_5439_;
}
else
{
lean_inc(v_Z_5438_);
lean_inc(v_x_5437_);
lean_inc(v_X_5436_);
lean_inc(v_O_5435_);
lean_inc(v_v_5434_);
lean_inc(v_zabbrev_5433_);
lean_inc(v_z_5432_);
lean_inc(v_V_5431_);
lean_inc(v_N_5430_);
lean_inc(v_n_5429_);
lean_inc(v_A_5428_);
lean_inc(v_S_5427_);
lean_inc(v_s_5426_);
lean_inc(v_m_5425_);
lean_inc(v_H_5424_);
lean_inc(v_k_5423_);
lean_inc(v_K_5422_);
lean_inc(v_h_5421_);
lean_inc(v_B_5420_);
lean_inc(v_b_5419_);
lean_inc(v_F_5418_);
lean_inc(v_c_5417_);
lean_inc(v_e_5416_);
lean_inc(v_E_5415_);
lean_inc(v_W_5414_);
lean_inc(v_w_5413_);
lean_inc(v_q_5412_);
lean_inc(v_Q_5411_);
lean_inc(v_d_5410_);
lean_inc(v_L_5409_);
lean_inc(v_M_5408_);
lean_inc(v_D_5407_);
lean_inc(v_Y_5406_);
lean_inc(v_u_5405_);
lean_inc(v_y_5404_);
lean_inc(v_G_5403_);
lean_dec(v_date_4582_);
v___x_5440_ = lean_box(0);
v_isShared_5441_ = v_isSharedCheck_5446_;
goto v_resetjp_5439_;
}
v_resetjp_5439_:
{
lean_object* v___x_5442_; lean_object* v___x_5444_; 
v___x_5442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5442_, 0, v_data_4584_);
if (v_isShared_5441_ == 0)
{
lean_ctor_set(v___x_5440_, 16, v___x_5442_);
v___x_5444_ = v___x_5440_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_G_5403_);
lean_ctor_set(v_reuseFailAlloc_5445_, 1, v_y_5404_);
lean_ctor_set(v_reuseFailAlloc_5445_, 2, v_u_5405_);
lean_ctor_set(v_reuseFailAlloc_5445_, 3, v_Y_5406_);
lean_ctor_set(v_reuseFailAlloc_5445_, 4, v_D_5407_);
lean_ctor_set(v_reuseFailAlloc_5445_, 5, v_M_5408_);
lean_ctor_set(v_reuseFailAlloc_5445_, 6, v_L_5409_);
lean_ctor_set(v_reuseFailAlloc_5445_, 7, v_d_5410_);
lean_ctor_set(v_reuseFailAlloc_5445_, 8, v_Q_5411_);
lean_ctor_set(v_reuseFailAlloc_5445_, 9, v_q_5412_);
lean_ctor_set(v_reuseFailAlloc_5445_, 10, v_w_5413_);
lean_ctor_set(v_reuseFailAlloc_5445_, 11, v_W_5414_);
lean_ctor_set(v_reuseFailAlloc_5445_, 12, v_E_5415_);
lean_ctor_set(v_reuseFailAlloc_5445_, 13, v_e_5416_);
lean_ctor_set(v_reuseFailAlloc_5445_, 14, v_c_5417_);
lean_ctor_set(v_reuseFailAlloc_5445_, 15, v_F_5418_);
lean_ctor_set(v_reuseFailAlloc_5445_, 16, v___x_5442_);
lean_ctor_set(v_reuseFailAlloc_5445_, 17, v_b_5419_);
lean_ctor_set(v_reuseFailAlloc_5445_, 18, v_B_5420_);
lean_ctor_set(v_reuseFailAlloc_5445_, 19, v_h_5421_);
lean_ctor_set(v_reuseFailAlloc_5445_, 20, v_K_5422_);
lean_ctor_set(v_reuseFailAlloc_5445_, 21, v_k_5423_);
lean_ctor_set(v_reuseFailAlloc_5445_, 22, v_H_5424_);
lean_ctor_set(v_reuseFailAlloc_5445_, 23, v_m_5425_);
lean_ctor_set(v_reuseFailAlloc_5445_, 24, v_s_5426_);
lean_ctor_set(v_reuseFailAlloc_5445_, 25, v_S_5427_);
lean_ctor_set(v_reuseFailAlloc_5445_, 26, v_A_5428_);
lean_ctor_set(v_reuseFailAlloc_5445_, 27, v_n_5429_);
lean_ctor_set(v_reuseFailAlloc_5445_, 28, v_N_5430_);
lean_ctor_set(v_reuseFailAlloc_5445_, 29, v_V_5431_);
lean_ctor_set(v_reuseFailAlloc_5445_, 30, v_z_5432_);
lean_ctor_set(v_reuseFailAlloc_5445_, 31, v_zabbrev_5433_);
lean_ctor_set(v_reuseFailAlloc_5445_, 32, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5445_, 33, v_O_5435_);
lean_ctor_set(v_reuseFailAlloc_5445_, 34, v_X_5436_);
lean_ctor_set(v_reuseFailAlloc_5445_, 35, v_x_5437_);
lean_ctor_set(v_reuseFailAlloc_5445_, 36, v_Z_5438_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
case 17:
{
lean_object* v_G_5448_; lean_object* v_y_5449_; lean_object* v_u_5450_; lean_object* v_Y_5451_; lean_object* v_D_5452_; lean_object* v_M_5453_; lean_object* v_L_5454_; lean_object* v_d_5455_; lean_object* v_Q_5456_; lean_object* v_q_5457_; lean_object* v_w_5458_; lean_object* v_W_5459_; lean_object* v_E_5460_; lean_object* v_e_5461_; lean_object* v_c_5462_; lean_object* v_F_5463_; lean_object* v_a_5464_; lean_object* v_B_5465_; lean_object* v_h_5466_; lean_object* v_K_5467_; lean_object* v_k_5468_; lean_object* v_H_5469_; lean_object* v_m_5470_; lean_object* v_s_5471_; lean_object* v_S_5472_; lean_object* v_A_5473_; lean_object* v_n_5474_; lean_object* v_N_5475_; lean_object* v_V_5476_; lean_object* v_z_5477_; lean_object* v_zabbrev_5478_; lean_object* v_v_5479_; lean_object* v_O_5480_; lean_object* v_X_5481_; lean_object* v_x_5482_; lean_object* v_Z_5483_; lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5491_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_G_5448_ = lean_ctor_get(v_date_4582_, 0);
v_y_5449_ = lean_ctor_get(v_date_4582_, 1);
v_u_5450_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5451_ = lean_ctor_get(v_date_4582_, 3);
v_D_5452_ = lean_ctor_get(v_date_4582_, 4);
v_M_5453_ = lean_ctor_get(v_date_4582_, 5);
v_L_5454_ = lean_ctor_get(v_date_4582_, 6);
v_d_5455_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5456_ = lean_ctor_get(v_date_4582_, 8);
v_q_5457_ = lean_ctor_get(v_date_4582_, 9);
v_w_5458_ = lean_ctor_get(v_date_4582_, 10);
v_W_5459_ = lean_ctor_get(v_date_4582_, 11);
v_E_5460_ = lean_ctor_get(v_date_4582_, 12);
v_e_5461_ = lean_ctor_get(v_date_4582_, 13);
v_c_5462_ = lean_ctor_get(v_date_4582_, 14);
v_F_5463_ = lean_ctor_get(v_date_4582_, 15);
v_a_5464_ = lean_ctor_get(v_date_4582_, 16);
v_B_5465_ = lean_ctor_get(v_date_4582_, 18);
v_h_5466_ = lean_ctor_get(v_date_4582_, 19);
v_K_5467_ = lean_ctor_get(v_date_4582_, 20);
v_k_5468_ = lean_ctor_get(v_date_4582_, 21);
v_H_5469_ = lean_ctor_get(v_date_4582_, 22);
v_m_5470_ = lean_ctor_get(v_date_4582_, 23);
v_s_5471_ = lean_ctor_get(v_date_4582_, 24);
v_S_5472_ = lean_ctor_get(v_date_4582_, 25);
v_A_5473_ = lean_ctor_get(v_date_4582_, 26);
v_n_5474_ = lean_ctor_get(v_date_4582_, 27);
v_N_5475_ = lean_ctor_get(v_date_4582_, 28);
v_V_5476_ = lean_ctor_get(v_date_4582_, 29);
v_z_5477_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5478_ = lean_ctor_get(v_date_4582_, 31);
v_v_5479_ = lean_ctor_get(v_date_4582_, 32);
v_O_5480_ = lean_ctor_get(v_date_4582_, 33);
v_X_5481_ = lean_ctor_get(v_date_4582_, 34);
v_x_5482_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5483_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5491_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5491_ == 0)
{
lean_object* v_unused_5492_; 
v_unused_5492_ = lean_ctor_get(v_date_4582_, 17);
lean_dec(v_unused_5492_);
v___x_5485_ = v_date_4582_;
v_isShared_5486_ = v_isSharedCheck_5491_;
goto v_resetjp_5484_;
}
else
{
lean_inc(v_Z_5483_);
lean_inc(v_x_5482_);
lean_inc(v_X_5481_);
lean_inc(v_O_5480_);
lean_inc(v_v_5479_);
lean_inc(v_zabbrev_5478_);
lean_inc(v_z_5477_);
lean_inc(v_V_5476_);
lean_inc(v_N_5475_);
lean_inc(v_n_5474_);
lean_inc(v_A_5473_);
lean_inc(v_S_5472_);
lean_inc(v_s_5471_);
lean_inc(v_m_5470_);
lean_inc(v_H_5469_);
lean_inc(v_k_5468_);
lean_inc(v_K_5467_);
lean_inc(v_h_5466_);
lean_inc(v_B_5465_);
lean_inc(v_a_5464_);
lean_inc(v_F_5463_);
lean_inc(v_c_5462_);
lean_inc(v_e_5461_);
lean_inc(v_E_5460_);
lean_inc(v_W_5459_);
lean_inc(v_w_5458_);
lean_inc(v_q_5457_);
lean_inc(v_Q_5456_);
lean_inc(v_d_5455_);
lean_inc(v_L_5454_);
lean_inc(v_M_5453_);
lean_inc(v_D_5452_);
lean_inc(v_Y_5451_);
lean_inc(v_u_5450_);
lean_inc(v_y_5449_);
lean_inc(v_G_5448_);
lean_dec(v_date_4582_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5491_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5487_; lean_object* v___x_5489_; 
v___x_5487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5487_, 0, v_data_4584_);
if (v_isShared_5486_ == 0)
{
lean_ctor_set(v___x_5485_, 17, v___x_5487_);
v___x_5489_ = v___x_5485_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_G_5448_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v_y_5449_);
lean_ctor_set(v_reuseFailAlloc_5490_, 2, v_u_5450_);
lean_ctor_set(v_reuseFailAlloc_5490_, 3, v_Y_5451_);
lean_ctor_set(v_reuseFailAlloc_5490_, 4, v_D_5452_);
lean_ctor_set(v_reuseFailAlloc_5490_, 5, v_M_5453_);
lean_ctor_set(v_reuseFailAlloc_5490_, 6, v_L_5454_);
lean_ctor_set(v_reuseFailAlloc_5490_, 7, v_d_5455_);
lean_ctor_set(v_reuseFailAlloc_5490_, 8, v_Q_5456_);
lean_ctor_set(v_reuseFailAlloc_5490_, 9, v_q_5457_);
lean_ctor_set(v_reuseFailAlloc_5490_, 10, v_w_5458_);
lean_ctor_set(v_reuseFailAlloc_5490_, 11, v_W_5459_);
lean_ctor_set(v_reuseFailAlloc_5490_, 12, v_E_5460_);
lean_ctor_set(v_reuseFailAlloc_5490_, 13, v_e_5461_);
lean_ctor_set(v_reuseFailAlloc_5490_, 14, v_c_5462_);
lean_ctor_set(v_reuseFailAlloc_5490_, 15, v_F_5463_);
lean_ctor_set(v_reuseFailAlloc_5490_, 16, v_a_5464_);
lean_ctor_set(v_reuseFailAlloc_5490_, 17, v___x_5487_);
lean_ctor_set(v_reuseFailAlloc_5490_, 18, v_B_5465_);
lean_ctor_set(v_reuseFailAlloc_5490_, 19, v_h_5466_);
lean_ctor_set(v_reuseFailAlloc_5490_, 20, v_K_5467_);
lean_ctor_set(v_reuseFailAlloc_5490_, 21, v_k_5468_);
lean_ctor_set(v_reuseFailAlloc_5490_, 22, v_H_5469_);
lean_ctor_set(v_reuseFailAlloc_5490_, 23, v_m_5470_);
lean_ctor_set(v_reuseFailAlloc_5490_, 24, v_s_5471_);
lean_ctor_set(v_reuseFailAlloc_5490_, 25, v_S_5472_);
lean_ctor_set(v_reuseFailAlloc_5490_, 26, v_A_5473_);
lean_ctor_set(v_reuseFailAlloc_5490_, 27, v_n_5474_);
lean_ctor_set(v_reuseFailAlloc_5490_, 28, v_N_5475_);
lean_ctor_set(v_reuseFailAlloc_5490_, 29, v_V_5476_);
lean_ctor_set(v_reuseFailAlloc_5490_, 30, v_z_5477_);
lean_ctor_set(v_reuseFailAlloc_5490_, 31, v_zabbrev_5478_);
lean_ctor_set(v_reuseFailAlloc_5490_, 32, v_v_5479_);
lean_ctor_set(v_reuseFailAlloc_5490_, 33, v_O_5480_);
lean_ctor_set(v_reuseFailAlloc_5490_, 34, v_X_5481_);
lean_ctor_set(v_reuseFailAlloc_5490_, 35, v_x_5482_);
lean_ctor_set(v_reuseFailAlloc_5490_, 36, v_Z_5483_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
return v___x_5489_;
}
}
}
case 18:
{
lean_object* v_G_5493_; lean_object* v_y_5494_; lean_object* v_u_5495_; lean_object* v_Y_5496_; lean_object* v_D_5497_; lean_object* v_M_5498_; lean_object* v_L_5499_; lean_object* v_d_5500_; lean_object* v_Q_5501_; lean_object* v_q_5502_; lean_object* v_w_5503_; lean_object* v_W_5504_; lean_object* v_E_5505_; lean_object* v_e_5506_; lean_object* v_c_5507_; lean_object* v_F_5508_; lean_object* v_a_5509_; lean_object* v_b_5510_; lean_object* v_h_5511_; lean_object* v_K_5512_; lean_object* v_k_5513_; lean_object* v_H_5514_; lean_object* v_m_5515_; lean_object* v_s_5516_; lean_object* v_S_5517_; lean_object* v_A_5518_; lean_object* v_n_5519_; lean_object* v_N_5520_; lean_object* v_V_5521_; lean_object* v_z_5522_; lean_object* v_zabbrev_5523_; lean_object* v_v_5524_; lean_object* v_O_5525_; lean_object* v_X_5526_; lean_object* v_x_5527_; lean_object* v_Z_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5536_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_G_5493_ = lean_ctor_get(v_date_4582_, 0);
v_y_5494_ = lean_ctor_get(v_date_4582_, 1);
v_u_5495_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5496_ = lean_ctor_get(v_date_4582_, 3);
v_D_5497_ = lean_ctor_get(v_date_4582_, 4);
v_M_5498_ = lean_ctor_get(v_date_4582_, 5);
v_L_5499_ = lean_ctor_get(v_date_4582_, 6);
v_d_5500_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5501_ = lean_ctor_get(v_date_4582_, 8);
v_q_5502_ = lean_ctor_get(v_date_4582_, 9);
v_w_5503_ = lean_ctor_get(v_date_4582_, 10);
v_W_5504_ = lean_ctor_get(v_date_4582_, 11);
v_E_5505_ = lean_ctor_get(v_date_4582_, 12);
v_e_5506_ = lean_ctor_get(v_date_4582_, 13);
v_c_5507_ = lean_ctor_get(v_date_4582_, 14);
v_F_5508_ = lean_ctor_get(v_date_4582_, 15);
v_a_5509_ = lean_ctor_get(v_date_4582_, 16);
v_b_5510_ = lean_ctor_get(v_date_4582_, 17);
v_h_5511_ = lean_ctor_get(v_date_4582_, 19);
v_K_5512_ = lean_ctor_get(v_date_4582_, 20);
v_k_5513_ = lean_ctor_get(v_date_4582_, 21);
v_H_5514_ = lean_ctor_get(v_date_4582_, 22);
v_m_5515_ = lean_ctor_get(v_date_4582_, 23);
v_s_5516_ = lean_ctor_get(v_date_4582_, 24);
v_S_5517_ = lean_ctor_get(v_date_4582_, 25);
v_A_5518_ = lean_ctor_get(v_date_4582_, 26);
v_n_5519_ = lean_ctor_get(v_date_4582_, 27);
v_N_5520_ = lean_ctor_get(v_date_4582_, 28);
v_V_5521_ = lean_ctor_get(v_date_4582_, 29);
v_z_5522_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5523_ = lean_ctor_get(v_date_4582_, 31);
v_v_5524_ = lean_ctor_get(v_date_4582_, 32);
v_O_5525_ = lean_ctor_get(v_date_4582_, 33);
v_X_5526_ = lean_ctor_get(v_date_4582_, 34);
v_x_5527_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5528_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5536_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5536_ == 0)
{
lean_object* v_unused_5537_; 
v_unused_5537_ = lean_ctor_get(v_date_4582_, 18);
lean_dec(v_unused_5537_);
v___x_5530_ = v_date_4582_;
v_isShared_5531_ = v_isSharedCheck_5536_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_Z_5528_);
lean_inc(v_x_5527_);
lean_inc(v_X_5526_);
lean_inc(v_O_5525_);
lean_inc(v_v_5524_);
lean_inc(v_zabbrev_5523_);
lean_inc(v_z_5522_);
lean_inc(v_V_5521_);
lean_inc(v_N_5520_);
lean_inc(v_n_5519_);
lean_inc(v_A_5518_);
lean_inc(v_S_5517_);
lean_inc(v_s_5516_);
lean_inc(v_m_5515_);
lean_inc(v_H_5514_);
lean_inc(v_k_5513_);
lean_inc(v_K_5512_);
lean_inc(v_h_5511_);
lean_inc(v_b_5510_);
lean_inc(v_a_5509_);
lean_inc(v_F_5508_);
lean_inc(v_c_5507_);
lean_inc(v_e_5506_);
lean_inc(v_E_5505_);
lean_inc(v_W_5504_);
lean_inc(v_w_5503_);
lean_inc(v_q_5502_);
lean_inc(v_Q_5501_);
lean_inc(v_d_5500_);
lean_inc(v_L_5499_);
lean_inc(v_M_5498_);
lean_inc(v_D_5497_);
lean_inc(v_Y_5496_);
lean_inc(v_u_5495_);
lean_inc(v_y_5494_);
lean_inc(v_G_5493_);
lean_dec(v_date_4582_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5536_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5532_; lean_object* v___x_5534_; 
v___x_5532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5532_, 0, v_data_4584_);
if (v_isShared_5531_ == 0)
{
lean_ctor_set(v___x_5530_, 18, v___x_5532_);
v___x_5534_ = v___x_5530_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5535_; 
v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_G_5493_);
lean_ctor_set(v_reuseFailAlloc_5535_, 1, v_y_5494_);
lean_ctor_set(v_reuseFailAlloc_5535_, 2, v_u_5495_);
lean_ctor_set(v_reuseFailAlloc_5535_, 3, v_Y_5496_);
lean_ctor_set(v_reuseFailAlloc_5535_, 4, v_D_5497_);
lean_ctor_set(v_reuseFailAlloc_5535_, 5, v_M_5498_);
lean_ctor_set(v_reuseFailAlloc_5535_, 6, v_L_5499_);
lean_ctor_set(v_reuseFailAlloc_5535_, 7, v_d_5500_);
lean_ctor_set(v_reuseFailAlloc_5535_, 8, v_Q_5501_);
lean_ctor_set(v_reuseFailAlloc_5535_, 9, v_q_5502_);
lean_ctor_set(v_reuseFailAlloc_5535_, 10, v_w_5503_);
lean_ctor_set(v_reuseFailAlloc_5535_, 11, v_W_5504_);
lean_ctor_set(v_reuseFailAlloc_5535_, 12, v_E_5505_);
lean_ctor_set(v_reuseFailAlloc_5535_, 13, v_e_5506_);
lean_ctor_set(v_reuseFailAlloc_5535_, 14, v_c_5507_);
lean_ctor_set(v_reuseFailAlloc_5535_, 15, v_F_5508_);
lean_ctor_set(v_reuseFailAlloc_5535_, 16, v_a_5509_);
lean_ctor_set(v_reuseFailAlloc_5535_, 17, v_b_5510_);
lean_ctor_set(v_reuseFailAlloc_5535_, 18, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5535_, 19, v_h_5511_);
lean_ctor_set(v_reuseFailAlloc_5535_, 20, v_K_5512_);
lean_ctor_set(v_reuseFailAlloc_5535_, 21, v_k_5513_);
lean_ctor_set(v_reuseFailAlloc_5535_, 22, v_H_5514_);
lean_ctor_set(v_reuseFailAlloc_5535_, 23, v_m_5515_);
lean_ctor_set(v_reuseFailAlloc_5535_, 24, v_s_5516_);
lean_ctor_set(v_reuseFailAlloc_5535_, 25, v_S_5517_);
lean_ctor_set(v_reuseFailAlloc_5535_, 26, v_A_5518_);
lean_ctor_set(v_reuseFailAlloc_5535_, 27, v_n_5519_);
lean_ctor_set(v_reuseFailAlloc_5535_, 28, v_N_5520_);
lean_ctor_set(v_reuseFailAlloc_5535_, 29, v_V_5521_);
lean_ctor_set(v_reuseFailAlloc_5535_, 30, v_z_5522_);
lean_ctor_set(v_reuseFailAlloc_5535_, 31, v_zabbrev_5523_);
lean_ctor_set(v_reuseFailAlloc_5535_, 32, v_v_5524_);
lean_ctor_set(v_reuseFailAlloc_5535_, 33, v_O_5525_);
lean_ctor_set(v_reuseFailAlloc_5535_, 34, v_X_5526_);
lean_ctor_set(v_reuseFailAlloc_5535_, 35, v_x_5527_);
lean_ctor_set(v_reuseFailAlloc_5535_, 36, v_Z_5528_);
v___x_5534_ = v_reuseFailAlloc_5535_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
return v___x_5534_;
}
}
}
case 19:
{
lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5588_; 
v_isSharedCheck_5588_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5588_ == 0)
{
lean_object* v_unused_5589_; 
v_unused_5589_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5589_);
v___x_5539_ = v_modifier_4583_;
v_isShared_5540_ = v_isSharedCheck_5588_;
goto v_resetjp_5538_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5588_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v_G_5541_; lean_object* v_y_5542_; lean_object* v_u_5543_; lean_object* v_Y_5544_; lean_object* v_D_5545_; lean_object* v_M_5546_; lean_object* v_L_5547_; lean_object* v_d_5548_; lean_object* v_Q_5549_; lean_object* v_q_5550_; lean_object* v_w_5551_; lean_object* v_W_5552_; lean_object* v_E_5553_; lean_object* v_e_5554_; lean_object* v_c_5555_; lean_object* v_F_5556_; lean_object* v_a_5557_; lean_object* v_b_5558_; lean_object* v_B_5559_; lean_object* v_K_5560_; lean_object* v_k_5561_; lean_object* v_H_5562_; lean_object* v_m_5563_; lean_object* v_s_5564_; lean_object* v_S_5565_; lean_object* v_A_5566_; lean_object* v_n_5567_; lean_object* v_N_5568_; lean_object* v_V_5569_; lean_object* v_z_5570_; lean_object* v_zabbrev_5571_; lean_object* v_v_5572_; lean_object* v_O_5573_; lean_object* v_X_5574_; lean_object* v_x_5575_; lean_object* v_Z_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5586_; 
v_G_5541_ = lean_ctor_get(v_date_4582_, 0);
v_y_5542_ = lean_ctor_get(v_date_4582_, 1);
v_u_5543_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5544_ = lean_ctor_get(v_date_4582_, 3);
v_D_5545_ = lean_ctor_get(v_date_4582_, 4);
v_M_5546_ = lean_ctor_get(v_date_4582_, 5);
v_L_5547_ = lean_ctor_get(v_date_4582_, 6);
v_d_5548_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5549_ = lean_ctor_get(v_date_4582_, 8);
v_q_5550_ = lean_ctor_get(v_date_4582_, 9);
v_w_5551_ = lean_ctor_get(v_date_4582_, 10);
v_W_5552_ = lean_ctor_get(v_date_4582_, 11);
v_E_5553_ = lean_ctor_get(v_date_4582_, 12);
v_e_5554_ = lean_ctor_get(v_date_4582_, 13);
v_c_5555_ = lean_ctor_get(v_date_4582_, 14);
v_F_5556_ = lean_ctor_get(v_date_4582_, 15);
v_a_5557_ = lean_ctor_get(v_date_4582_, 16);
v_b_5558_ = lean_ctor_get(v_date_4582_, 17);
v_B_5559_ = lean_ctor_get(v_date_4582_, 18);
v_K_5560_ = lean_ctor_get(v_date_4582_, 20);
v_k_5561_ = lean_ctor_get(v_date_4582_, 21);
v_H_5562_ = lean_ctor_get(v_date_4582_, 22);
v_m_5563_ = lean_ctor_get(v_date_4582_, 23);
v_s_5564_ = lean_ctor_get(v_date_4582_, 24);
v_S_5565_ = lean_ctor_get(v_date_4582_, 25);
v_A_5566_ = lean_ctor_get(v_date_4582_, 26);
v_n_5567_ = lean_ctor_get(v_date_4582_, 27);
v_N_5568_ = lean_ctor_get(v_date_4582_, 28);
v_V_5569_ = lean_ctor_get(v_date_4582_, 29);
v_z_5570_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5571_ = lean_ctor_get(v_date_4582_, 31);
v_v_5572_ = lean_ctor_get(v_date_4582_, 32);
v_O_5573_ = lean_ctor_get(v_date_4582_, 33);
v_X_5574_ = lean_ctor_get(v_date_4582_, 34);
v_x_5575_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5576_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5586_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5586_ == 0)
{
lean_object* v_unused_5587_; 
v_unused_5587_ = lean_ctor_get(v_date_4582_, 19);
lean_dec(v_unused_5587_);
v___x_5578_ = v_date_4582_;
v_isShared_5579_ = v_isSharedCheck_5586_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_Z_5576_);
lean_inc(v_x_5575_);
lean_inc(v_X_5574_);
lean_inc(v_O_5573_);
lean_inc(v_v_5572_);
lean_inc(v_zabbrev_5571_);
lean_inc(v_z_5570_);
lean_inc(v_V_5569_);
lean_inc(v_N_5568_);
lean_inc(v_n_5567_);
lean_inc(v_A_5566_);
lean_inc(v_S_5565_);
lean_inc(v_s_5564_);
lean_inc(v_m_5563_);
lean_inc(v_H_5562_);
lean_inc(v_k_5561_);
lean_inc(v_K_5560_);
lean_inc(v_B_5559_);
lean_inc(v_b_5558_);
lean_inc(v_a_5557_);
lean_inc(v_F_5556_);
lean_inc(v_c_5555_);
lean_inc(v_e_5554_);
lean_inc(v_E_5553_);
lean_inc(v_W_5552_);
lean_inc(v_w_5551_);
lean_inc(v_q_5550_);
lean_inc(v_Q_5549_);
lean_inc(v_d_5548_);
lean_inc(v_L_5547_);
lean_inc(v_M_5546_);
lean_inc(v_D_5545_);
lean_inc(v_Y_5544_);
lean_inc(v_u_5543_);
lean_inc(v_y_5542_);
lean_inc(v_G_5541_);
lean_dec(v_date_4582_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5586_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v___x_5581_; 
if (v_isShared_5540_ == 0)
{
lean_ctor_set_tag(v___x_5539_, 1);
lean_ctor_set(v___x_5539_, 0, v_data_4584_);
v___x_5581_ = v___x_5539_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_data_4584_);
v___x_5581_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
lean_object* v___x_5583_; 
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 19, v___x_5581_);
v___x_5583_ = v___x_5578_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_G_5541_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v_y_5542_);
lean_ctor_set(v_reuseFailAlloc_5584_, 2, v_u_5543_);
lean_ctor_set(v_reuseFailAlloc_5584_, 3, v_Y_5544_);
lean_ctor_set(v_reuseFailAlloc_5584_, 4, v_D_5545_);
lean_ctor_set(v_reuseFailAlloc_5584_, 5, v_M_5546_);
lean_ctor_set(v_reuseFailAlloc_5584_, 6, v_L_5547_);
lean_ctor_set(v_reuseFailAlloc_5584_, 7, v_d_5548_);
lean_ctor_set(v_reuseFailAlloc_5584_, 8, v_Q_5549_);
lean_ctor_set(v_reuseFailAlloc_5584_, 9, v_q_5550_);
lean_ctor_set(v_reuseFailAlloc_5584_, 10, v_w_5551_);
lean_ctor_set(v_reuseFailAlloc_5584_, 11, v_W_5552_);
lean_ctor_set(v_reuseFailAlloc_5584_, 12, v_E_5553_);
lean_ctor_set(v_reuseFailAlloc_5584_, 13, v_e_5554_);
lean_ctor_set(v_reuseFailAlloc_5584_, 14, v_c_5555_);
lean_ctor_set(v_reuseFailAlloc_5584_, 15, v_F_5556_);
lean_ctor_set(v_reuseFailAlloc_5584_, 16, v_a_5557_);
lean_ctor_set(v_reuseFailAlloc_5584_, 17, v_b_5558_);
lean_ctor_set(v_reuseFailAlloc_5584_, 18, v_B_5559_);
lean_ctor_set(v_reuseFailAlloc_5584_, 19, v___x_5581_);
lean_ctor_set(v_reuseFailAlloc_5584_, 20, v_K_5560_);
lean_ctor_set(v_reuseFailAlloc_5584_, 21, v_k_5561_);
lean_ctor_set(v_reuseFailAlloc_5584_, 22, v_H_5562_);
lean_ctor_set(v_reuseFailAlloc_5584_, 23, v_m_5563_);
lean_ctor_set(v_reuseFailAlloc_5584_, 24, v_s_5564_);
lean_ctor_set(v_reuseFailAlloc_5584_, 25, v_S_5565_);
lean_ctor_set(v_reuseFailAlloc_5584_, 26, v_A_5566_);
lean_ctor_set(v_reuseFailAlloc_5584_, 27, v_n_5567_);
lean_ctor_set(v_reuseFailAlloc_5584_, 28, v_N_5568_);
lean_ctor_set(v_reuseFailAlloc_5584_, 29, v_V_5569_);
lean_ctor_set(v_reuseFailAlloc_5584_, 30, v_z_5570_);
lean_ctor_set(v_reuseFailAlloc_5584_, 31, v_zabbrev_5571_);
lean_ctor_set(v_reuseFailAlloc_5584_, 32, v_v_5572_);
lean_ctor_set(v_reuseFailAlloc_5584_, 33, v_O_5573_);
lean_ctor_set(v_reuseFailAlloc_5584_, 34, v_X_5574_);
lean_ctor_set(v_reuseFailAlloc_5584_, 35, v_x_5575_);
lean_ctor_set(v_reuseFailAlloc_5584_, 36, v_Z_5576_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
return v___x_5583_;
}
}
}
}
}
case 20:
{
lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5640_; 
v_isSharedCheck_5640_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5640_ == 0)
{
lean_object* v_unused_5641_; 
v_unused_5641_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5641_);
v___x_5591_ = v_modifier_4583_;
v_isShared_5592_ = v_isSharedCheck_5640_;
goto v_resetjp_5590_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5640_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
lean_object* v_G_5593_; lean_object* v_y_5594_; lean_object* v_u_5595_; lean_object* v_Y_5596_; lean_object* v_D_5597_; lean_object* v_M_5598_; lean_object* v_L_5599_; lean_object* v_d_5600_; lean_object* v_Q_5601_; lean_object* v_q_5602_; lean_object* v_w_5603_; lean_object* v_W_5604_; lean_object* v_E_5605_; lean_object* v_e_5606_; lean_object* v_c_5607_; lean_object* v_F_5608_; lean_object* v_a_5609_; lean_object* v_b_5610_; lean_object* v_B_5611_; lean_object* v_h_5612_; lean_object* v_k_5613_; lean_object* v_H_5614_; lean_object* v_m_5615_; lean_object* v_s_5616_; lean_object* v_S_5617_; lean_object* v_A_5618_; lean_object* v_n_5619_; lean_object* v_N_5620_; lean_object* v_V_5621_; lean_object* v_z_5622_; lean_object* v_zabbrev_5623_; lean_object* v_v_5624_; lean_object* v_O_5625_; lean_object* v_X_5626_; lean_object* v_x_5627_; lean_object* v_Z_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5638_; 
v_G_5593_ = lean_ctor_get(v_date_4582_, 0);
v_y_5594_ = lean_ctor_get(v_date_4582_, 1);
v_u_5595_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5596_ = lean_ctor_get(v_date_4582_, 3);
v_D_5597_ = lean_ctor_get(v_date_4582_, 4);
v_M_5598_ = lean_ctor_get(v_date_4582_, 5);
v_L_5599_ = lean_ctor_get(v_date_4582_, 6);
v_d_5600_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5601_ = lean_ctor_get(v_date_4582_, 8);
v_q_5602_ = lean_ctor_get(v_date_4582_, 9);
v_w_5603_ = lean_ctor_get(v_date_4582_, 10);
v_W_5604_ = lean_ctor_get(v_date_4582_, 11);
v_E_5605_ = lean_ctor_get(v_date_4582_, 12);
v_e_5606_ = lean_ctor_get(v_date_4582_, 13);
v_c_5607_ = lean_ctor_get(v_date_4582_, 14);
v_F_5608_ = lean_ctor_get(v_date_4582_, 15);
v_a_5609_ = lean_ctor_get(v_date_4582_, 16);
v_b_5610_ = lean_ctor_get(v_date_4582_, 17);
v_B_5611_ = lean_ctor_get(v_date_4582_, 18);
v_h_5612_ = lean_ctor_get(v_date_4582_, 19);
v_k_5613_ = lean_ctor_get(v_date_4582_, 21);
v_H_5614_ = lean_ctor_get(v_date_4582_, 22);
v_m_5615_ = lean_ctor_get(v_date_4582_, 23);
v_s_5616_ = lean_ctor_get(v_date_4582_, 24);
v_S_5617_ = lean_ctor_get(v_date_4582_, 25);
v_A_5618_ = lean_ctor_get(v_date_4582_, 26);
v_n_5619_ = lean_ctor_get(v_date_4582_, 27);
v_N_5620_ = lean_ctor_get(v_date_4582_, 28);
v_V_5621_ = lean_ctor_get(v_date_4582_, 29);
v_z_5622_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5623_ = lean_ctor_get(v_date_4582_, 31);
v_v_5624_ = lean_ctor_get(v_date_4582_, 32);
v_O_5625_ = lean_ctor_get(v_date_4582_, 33);
v_X_5626_ = lean_ctor_get(v_date_4582_, 34);
v_x_5627_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5628_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5638_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5638_ == 0)
{
lean_object* v_unused_5639_; 
v_unused_5639_ = lean_ctor_get(v_date_4582_, 20);
lean_dec(v_unused_5639_);
v___x_5630_ = v_date_4582_;
v_isShared_5631_ = v_isSharedCheck_5638_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_Z_5628_);
lean_inc(v_x_5627_);
lean_inc(v_X_5626_);
lean_inc(v_O_5625_);
lean_inc(v_v_5624_);
lean_inc(v_zabbrev_5623_);
lean_inc(v_z_5622_);
lean_inc(v_V_5621_);
lean_inc(v_N_5620_);
lean_inc(v_n_5619_);
lean_inc(v_A_5618_);
lean_inc(v_S_5617_);
lean_inc(v_s_5616_);
lean_inc(v_m_5615_);
lean_inc(v_H_5614_);
lean_inc(v_k_5613_);
lean_inc(v_h_5612_);
lean_inc(v_B_5611_);
lean_inc(v_b_5610_);
lean_inc(v_a_5609_);
lean_inc(v_F_5608_);
lean_inc(v_c_5607_);
lean_inc(v_e_5606_);
lean_inc(v_E_5605_);
lean_inc(v_W_5604_);
lean_inc(v_w_5603_);
lean_inc(v_q_5602_);
lean_inc(v_Q_5601_);
lean_inc(v_d_5600_);
lean_inc(v_L_5599_);
lean_inc(v_M_5598_);
lean_inc(v_D_5597_);
lean_inc(v_Y_5596_);
lean_inc(v_u_5595_);
lean_inc(v_y_5594_);
lean_inc(v_G_5593_);
lean_dec(v_date_4582_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5638_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v___x_5633_; 
if (v_isShared_5592_ == 0)
{
lean_ctor_set_tag(v___x_5591_, 1);
lean_ctor_set(v___x_5591_, 0, v_data_4584_);
v___x_5633_ = v___x_5591_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_data_4584_);
v___x_5633_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
lean_object* v___x_5635_; 
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 20, v___x_5633_);
v___x_5635_ = v___x_5630_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v_G_5593_);
lean_ctor_set(v_reuseFailAlloc_5636_, 1, v_y_5594_);
lean_ctor_set(v_reuseFailAlloc_5636_, 2, v_u_5595_);
lean_ctor_set(v_reuseFailAlloc_5636_, 3, v_Y_5596_);
lean_ctor_set(v_reuseFailAlloc_5636_, 4, v_D_5597_);
lean_ctor_set(v_reuseFailAlloc_5636_, 5, v_M_5598_);
lean_ctor_set(v_reuseFailAlloc_5636_, 6, v_L_5599_);
lean_ctor_set(v_reuseFailAlloc_5636_, 7, v_d_5600_);
lean_ctor_set(v_reuseFailAlloc_5636_, 8, v_Q_5601_);
lean_ctor_set(v_reuseFailAlloc_5636_, 9, v_q_5602_);
lean_ctor_set(v_reuseFailAlloc_5636_, 10, v_w_5603_);
lean_ctor_set(v_reuseFailAlloc_5636_, 11, v_W_5604_);
lean_ctor_set(v_reuseFailAlloc_5636_, 12, v_E_5605_);
lean_ctor_set(v_reuseFailAlloc_5636_, 13, v_e_5606_);
lean_ctor_set(v_reuseFailAlloc_5636_, 14, v_c_5607_);
lean_ctor_set(v_reuseFailAlloc_5636_, 15, v_F_5608_);
lean_ctor_set(v_reuseFailAlloc_5636_, 16, v_a_5609_);
lean_ctor_set(v_reuseFailAlloc_5636_, 17, v_b_5610_);
lean_ctor_set(v_reuseFailAlloc_5636_, 18, v_B_5611_);
lean_ctor_set(v_reuseFailAlloc_5636_, 19, v_h_5612_);
lean_ctor_set(v_reuseFailAlloc_5636_, 20, v___x_5633_);
lean_ctor_set(v_reuseFailAlloc_5636_, 21, v_k_5613_);
lean_ctor_set(v_reuseFailAlloc_5636_, 22, v_H_5614_);
lean_ctor_set(v_reuseFailAlloc_5636_, 23, v_m_5615_);
lean_ctor_set(v_reuseFailAlloc_5636_, 24, v_s_5616_);
lean_ctor_set(v_reuseFailAlloc_5636_, 25, v_S_5617_);
lean_ctor_set(v_reuseFailAlloc_5636_, 26, v_A_5618_);
lean_ctor_set(v_reuseFailAlloc_5636_, 27, v_n_5619_);
lean_ctor_set(v_reuseFailAlloc_5636_, 28, v_N_5620_);
lean_ctor_set(v_reuseFailAlloc_5636_, 29, v_V_5621_);
lean_ctor_set(v_reuseFailAlloc_5636_, 30, v_z_5622_);
lean_ctor_set(v_reuseFailAlloc_5636_, 31, v_zabbrev_5623_);
lean_ctor_set(v_reuseFailAlloc_5636_, 32, v_v_5624_);
lean_ctor_set(v_reuseFailAlloc_5636_, 33, v_O_5625_);
lean_ctor_set(v_reuseFailAlloc_5636_, 34, v_X_5626_);
lean_ctor_set(v_reuseFailAlloc_5636_, 35, v_x_5627_);
lean_ctor_set(v_reuseFailAlloc_5636_, 36, v_Z_5628_);
v___x_5635_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
return v___x_5635_;
}
}
}
}
}
case 21:
{
lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5692_; 
v_isSharedCheck_5692_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5692_ == 0)
{
lean_object* v_unused_5693_; 
v_unused_5693_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5693_);
v___x_5643_ = v_modifier_4583_;
v_isShared_5644_ = v_isSharedCheck_5692_;
goto v_resetjp_5642_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5692_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v_G_5645_; lean_object* v_y_5646_; lean_object* v_u_5647_; lean_object* v_Y_5648_; lean_object* v_D_5649_; lean_object* v_M_5650_; lean_object* v_L_5651_; lean_object* v_d_5652_; lean_object* v_Q_5653_; lean_object* v_q_5654_; lean_object* v_w_5655_; lean_object* v_W_5656_; lean_object* v_E_5657_; lean_object* v_e_5658_; lean_object* v_c_5659_; lean_object* v_F_5660_; lean_object* v_a_5661_; lean_object* v_b_5662_; lean_object* v_B_5663_; lean_object* v_h_5664_; lean_object* v_K_5665_; lean_object* v_H_5666_; lean_object* v_m_5667_; lean_object* v_s_5668_; lean_object* v_S_5669_; lean_object* v_A_5670_; lean_object* v_n_5671_; lean_object* v_N_5672_; lean_object* v_V_5673_; lean_object* v_z_5674_; lean_object* v_zabbrev_5675_; lean_object* v_v_5676_; lean_object* v_O_5677_; lean_object* v_X_5678_; lean_object* v_x_5679_; lean_object* v_Z_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5690_; 
v_G_5645_ = lean_ctor_get(v_date_4582_, 0);
v_y_5646_ = lean_ctor_get(v_date_4582_, 1);
v_u_5647_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5648_ = lean_ctor_get(v_date_4582_, 3);
v_D_5649_ = lean_ctor_get(v_date_4582_, 4);
v_M_5650_ = lean_ctor_get(v_date_4582_, 5);
v_L_5651_ = lean_ctor_get(v_date_4582_, 6);
v_d_5652_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5653_ = lean_ctor_get(v_date_4582_, 8);
v_q_5654_ = lean_ctor_get(v_date_4582_, 9);
v_w_5655_ = lean_ctor_get(v_date_4582_, 10);
v_W_5656_ = lean_ctor_get(v_date_4582_, 11);
v_E_5657_ = lean_ctor_get(v_date_4582_, 12);
v_e_5658_ = lean_ctor_get(v_date_4582_, 13);
v_c_5659_ = lean_ctor_get(v_date_4582_, 14);
v_F_5660_ = lean_ctor_get(v_date_4582_, 15);
v_a_5661_ = lean_ctor_get(v_date_4582_, 16);
v_b_5662_ = lean_ctor_get(v_date_4582_, 17);
v_B_5663_ = lean_ctor_get(v_date_4582_, 18);
v_h_5664_ = lean_ctor_get(v_date_4582_, 19);
v_K_5665_ = lean_ctor_get(v_date_4582_, 20);
v_H_5666_ = lean_ctor_get(v_date_4582_, 22);
v_m_5667_ = lean_ctor_get(v_date_4582_, 23);
v_s_5668_ = lean_ctor_get(v_date_4582_, 24);
v_S_5669_ = lean_ctor_get(v_date_4582_, 25);
v_A_5670_ = lean_ctor_get(v_date_4582_, 26);
v_n_5671_ = lean_ctor_get(v_date_4582_, 27);
v_N_5672_ = lean_ctor_get(v_date_4582_, 28);
v_V_5673_ = lean_ctor_get(v_date_4582_, 29);
v_z_5674_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5675_ = lean_ctor_get(v_date_4582_, 31);
v_v_5676_ = lean_ctor_get(v_date_4582_, 32);
v_O_5677_ = lean_ctor_get(v_date_4582_, 33);
v_X_5678_ = lean_ctor_get(v_date_4582_, 34);
v_x_5679_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5680_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5690_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5690_ == 0)
{
lean_object* v_unused_5691_; 
v_unused_5691_ = lean_ctor_get(v_date_4582_, 21);
lean_dec(v_unused_5691_);
v___x_5682_ = v_date_4582_;
v_isShared_5683_ = v_isSharedCheck_5690_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_Z_5680_);
lean_inc(v_x_5679_);
lean_inc(v_X_5678_);
lean_inc(v_O_5677_);
lean_inc(v_v_5676_);
lean_inc(v_zabbrev_5675_);
lean_inc(v_z_5674_);
lean_inc(v_V_5673_);
lean_inc(v_N_5672_);
lean_inc(v_n_5671_);
lean_inc(v_A_5670_);
lean_inc(v_S_5669_);
lean_inc(v_s_5668_);
lean_inc(v_m_5667_);
lean_inc(v_H_5666_);
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
lean_dec(v_date_4582_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5690_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
lean_object* v___x_5685_; 
if (v_isShared_5644_ == 0)
{
lean_ctor_set_tag(v___x_5643_, 1);
lean_ctor_set(v___x_5643_, 0, v_data_4584_);
v___x_5685_ = v___x_5643_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_data_4584_);
v___x_5685_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
lean_object* v___x_5687_; 
if (v_isShared_5683_ == 0)
{
lean_ctor_set(v___x_5682_, 21, v___x_5685_);
v___x_5687_ = v___x_5682_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v_G_5645_);
lean_ctor_set(v_reuseFailAlloc_5688_, 1, v_y_5646_);
lean_ctor_set(v_reuseFailAlloc_5688_, 2, v_u_5647_);
lean_ctor_set(v_reuseFailAlloc_5688_, 3, v_Y_5648_);
lean_ctor_set(v_reuseFailAlloc_5688_, 4, v_D_5649_);
lean_ctor_set(v_reuseFailAlloc_5688_, 5, v_M_5650_);
lean_ctor_set(v_reuseFailAlloc_5688_, 6, v_L_5651_);
lean_ctor_set(v_reuseFailAlloc_5688_, 7, v_d_5652_);
lean_ctor_set(v_reuseFailAlloc_5688_, 8, v_Q_5653_);
lean_ctor_set(v_reuseFailAlloc_5688_, 9, v_q_5654_);
lean_ctor_set(v_reuseFailAlloc_5688_, 10, v_w_5655_);
lean_ctor_set(v_reuseFailAlloc_5688_, 11, v_W_5656_);
lean_ctor_set(v_reuseFailAlloc_5688_, 12, v_E_5657_);
lean_ctor_set(v_reuseFailAlloc_5688_, 13, v_e_5658_);
lean_ctor_set(v_reuseFailAlloc_5688_, 14, v_c_5659_);
lean_ctor_set(v_reuseFailAlloc_5688_, 15, v_F_5660_);
lean_ctor_set(v_reuseFailAlloc_5688_, 16, v_a_5661_);
lean_ctor_set(v_reuseFailAlloc_5688_, 17, v_b_5662_);
lean_ctor_set(v_reuseFailAlloc_5688_, 18, v_B_5663_);
lean_ctor_set(v_reuseFailAlloc_5688_, 19, v_h_5664_);
lean_ctor_set(v_reuseFailAlloc_5688_, 20, v_K_5665_);
lean_ctor_set(v_reuseFailAlloc_5688_, 21, v___x_5685_);
lean_ctor_set(v_reuseFailAlloc_5688_, 22, v_H_5666_);
lean_ctor_set(v_reuseFailAlloc_5688_, 23, v_m_5667_);
lean_ctor_set(v_reuseFailAlloc_5688_, 24, v_s_5668_);
lean_ctor_set(v_reuseFailAlloc_5688_, 25, v_S_5669_);
lean_ctor_set(v_reuseFailAlloc_5688_, 26, v_A_5670_);
lean_ctor_set(v_reuseFailAlloc_5688_, 27, v_n_5671_);
lean_ctor_set(v_reuseFailAlloc_5688_, 28, v_N_5672_);
lean_ctor_set(v_reuseFailAlloc_5688_, 29, v_V_5673_);
lean_ctor_set(v_reuseFailAlloc_5688_, 30, v_z_5674_);
lean_ctor_set(v_reuseFailAlloc_5688_, 31, v_zabbrev_5675_);
lean_ctor_set(v_reuseFailAlloc_5688_, 32, v_v_5676_);
lean_ctor_set(v_reuseFailAlloc_5688_, 33, v_O_5677_);
lean_ctor_set(v_reuseFailAlloc_5688_, 34, v_X_5678_);
lean_ctor_set(v_reuseFailAlloc_5688_, 35, v_x_5679_);
lean_ctor_set(v_reuseFailAlloc_5688_, 36, v_Z_5680_);
v___x_5687_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
return v___x_5687_;
}
}
}
}
}
case 22:
{
lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5744_; 
v_isSharedCheck_5744_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5744_ == 0)
{
lean_object* v_unused_5745_; 
v_unused_5745_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5745_);
v___x_5695_ = v_modifier_4583_;
v_isShared_5696_ = v_isSharedCheck_5744_;
goto v_resetjp_5694_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5695_ = lean_box(0);
v_isShared_5696_ = v_isSharedCheck_5744_;
goto v_resetjp_5694_;
}
v_resetjp_5694_:
{
lean_object* v_G_5697_; lean_object* v_y_5698_; lean_object* v_u_5699_; lean_object* v_Y_5700_; lean_object* v_D_5701_; lean_object* v_M_5702_; lean_object* v_L_5703_; lean_object* v_d_5704_; lean_object* v_Q_5705_; lean_object* v_q_5706_; lean_object* v_w_5707_; lean_object* v_W_5708_; lean_object* v_E_5709_; lean_object* v_e_5710_; lean_object* v_c_5711_; lean_object* v_F_5712_; lean_object* v_a_5713_; lean_object* v_b_5714_; lean_object* v_B_5715_; lean_object* v_h_5716_; lean_object* v_K_5717_; lean_object* v_k_5718_; lean_object* v_m_5719_; lean_object* v_s_5720_; lean_object* v_S_5721_; lean_object* v_A_5722_; lean_object* v_n_5723_; lean_object* v_N_5724_; lean_object* v_V_5725_; lean_object* v_z_5726_; lean_object* v_zabbrev_5727_; lean_object* v_v_5728_; lean_object* v_O_5729_; lean_object* v_X_5730_; lean_object* v_x_5731_; lean_object* v_Z_5732_; lean_object* v___x_5734_; uint8_t v_isShared_5735_; uint8_t v_isSharedCheck_5742_; 
v_G_5697_ = lean_ctor_get(v_date_4582_, 0);
v_y_5698_ = lean_ctor_get(v_date_4582_, 1);
v_u_5699_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5700_ = lean_ctor_get(v_date_4582_, 3);
v_D_5701_ = lean_ctor_get(v_date_4582_, 4);
v_M_5702_ = lean_ctor_get(v_date_4582_, 5);
v_L_5703_ = lean_ctor_get(v_date_4582_, 6);
v_d_5704_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5705_ = lean_ctor_get(v_date_4582_, 8);
v_q_5706_ = lean_ctor_get(v_date_4582_, 9);
v_w_5707_ = lean_ctor_get(v_date_4582_, 10);
v_W_5708_ = lean_ctor_get(v_date_4582_, 11);
v_E_5709_ = lean_ctor_get(v_date_4582_, 12);
v_e_5710_ = lean_ctor_get(v_date_4582_, 13);
v_c_5711_ = lean_ctor_get(v_date_4582_, 14);
v_F_5712_ = lean_ctor_get(v_date_4582_, 15);
v_a_5713_ = lean_ctor_get(v_date_4582_, 16);
v_b_5714_ = lean_ctor_get(v_date_4582_, 17);
v_B_5715_ = lean_ctor_get(v_date_4582_, 18);
v_h_5716_ = lean_ctor_get(v_date_4582_, 19);
v_K_5717_ = lean_ctor_get(v_date_4582_, 20);
v_k_5718_ = lean_ctor_get(v_date_4582_, 21);
v_m_5719_ = lean_ctor_get(v_date_4582_, 23);
v_s_5720_ = lean_ctor_get(v_date_4582_, 24);
v_S_5721_ = lean_ctor_get(v_date_4582_, 25);
v_A_5722_ = lean_ctor_get(v_date_4582_, 26);
v_n_5723_ = lean_ctor_get(v_date_4582_, 27);
v_N_5724_ = lean_ctor_get(v_date_4582_, 28);
v_V_5725_ = lean_ctor_get(v_date_4582_, 29);
v_z_5726_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5727_ = lean_ctor_get(v_date_4582_, 31);
v_v_5728_ = lean_ctor_get(v_date_4582_, 32);
v_O_5729_ = lean_ctor_get(v_date_4582_, 33);
v_X_5730_ = lean_ctor_get(v_date_4582_, 34);
v_x_5731_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5732_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5742_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5742_ == 0)
{
lean_object* v_unused_5743_; 
v_unused_5743_ = lean_ctor_get(v_date_4582_, 22);
lean_dec(v_unused_5743_);
v___x_5734_ = v_date_4582_;
v_isShared_5735_ = v_isSharedCheck_5742_;
goto v_resetjp_5733_;
}
else
{
lean_inc(v_Z_5732_);
lean_inc(v_x_5731_);
lean_inc(v_X_5730_);
lean_inc(v_O_5729_);
lean_inc(v_v_5728_);
lean_inc(v_zabbrev_5727_);
lean_inc(v_z_5726_);
lean_inc(v_V_5725_);
lean_inc(v_N_5724_);
lean_inc(v_n_5723_);
lean_inc(v_A_5722_);
lean_inc(v_S_5721_);
lean_inc(v_s_5720_);
lean_inc(v_m_5719_);
lean_inc(v_k_5718_);
lean_inc(v_K_5717_);
lean_inc(v_h_5716_);
lean_inc(v_B_5715_);
lean_inc(v_b_5714_);
lean_inc(v_a_5713_);
lean_inc(v_F_5712_);
lean_inc(v_c_5711_);
lean_inc(v_e_5710_);
lean_inc(v_E_5709_);
lean_inc(v_W_5708_);
lean_inc(v_w_5707_);
lean_inc(v_q_5706_);
lean_inc(v_Q_5705_);
lean_inc(v_d_5704_);
lean_inc(v_L_5703_);
lean_inc(v_M_5702_);
lean_inc(v_D_5701_);
lean_inc(v_Y_5700_);
lean_inc(v_u_5699_);
lean_inc(v_y_5698_);
lean_inc(v_G_5697_);
lean_dec(v_date_4582_);
v___x_5734_ = lean_box(0);
v_isShared_5735_ = v_isSharedCheck_5742_;
goto v_resetjp_5733_;
}
v_resetjp_5733_:
{
lean_object* v___x_5737_; 
if (v_isShared_5696_ == 0)
{
lean_ctor_set_tag(v___x_5695_, 1);
lean_ctor_set(v___x_5695_, 0, v_data_4584_);
v___x_5737_ = v___x_5695_;
goto v_reusejp_5736_;
}
else
{
lean_object* v_reuseFailAlloc_5741_; 
v_reuseFailAlloc_5741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5741_, 0, v_data_4584_);
v___x_5737_ = v_reuseFailAlloc_5741_;
goto v_reusejp_5736_;
}
v_reusejp_5736_:
{
lean_object* v___x_5739_; 
if (v_isShared_5735_ == 0)
{
lean_ctor_set(v___x_5734_, 22, v___x_5737_);
v___x_5739_ = v___x_5734_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v_G_5697_);
lean_ctor_set(v_reuseFailAlloc_5740_, 1, v_y_5698_);
lean_ctor_set(v_reuseFailAlloc_5740_, 2, v_u_5699_);
lean_ctor_set(v_reuseFailAlloc_5740_, 3, v_Y_5700_);
lean_ctor_set(v_reuseFailAlloc_5740_, 4, v_D_5701_);
lean_ctor_set(v_reuseFailAlloc_5740_, 5, v_M_5702_);
lean_ctor_set(v_reuseFailAlloc_5740_, 6, v_L_5703_);
lean_ctor_set(v_reuseFailAlloc_5740_, 7, v_d_5704_);
lean_ctor_set(v_reuseFailAlloc_5740_, 8, v_Q_5705_);
lean_ctor_set(v_reuseFailAlloc_5740_, 9, v_q_5706_);
lean_ctor_set(v_reuseFailAlloc_5740_, 10, v_w_5707_);
lean_ctor_set(v_reuseFailAlloc_5740_, 11, v_W_5708_);
lean_ctor_set(v_reuseFailAlloc_5740_, 12, v_E_5709_);
lean_ctor_set(v_reuseFailAlloc_5740_, 13, v_e_5710_);
lean_ctor_set(v_reuseFailAlloc_5740_, 14, v_c_5711_);
lean_ctor_set(v_reuseFailAlloc_5740_, 15, v_F_5712_);
lean_ctor_set(v_reuseFailAlloc_5740_, 16, v_a_5713_);
lean_ctor_set(v_reuseFailAlloc_5740_, 17, v_b_5714_);
lean_ctor_set(v_reuseFailAlloc_5740_, 18, v_B_5715_);
lean_ctor_set(v_reuseFailAlloc_5740_, 19, v_h_5716_);
lean_ctor_set(v_reuseFailAlloc_5740_, 20, v_K_5717_);
lean_ctor_set(v_reuseFailAlloc_5740_, 21, v_k_5718_);
lean_ctor_set(v_reuseFailAlloc_5740_, 22, v___x_5737_);
lean_ctor_set(v_reuseFailAlloc_5740_, 23, v_m_5719_);
lean_ctor_set(v_reuseFailAlloc_5740_, 24, v_s_5720_);
lean_ctor_set(v_reuseFailAlloc_5740_, 25, v_S_5721_);
lean_ctor_set(v_reuseFailAlloc_5740_, 26, v_A_5722_);
lean_ctor_set(v_reuseFailAlloc_5740_, 27, v_n_5723_);
lean_ctor_set(v_reuseFailAlloc_5740_, 28, v_N_5724_);
lean_ctor_set(v_reuseFailAlloc_5740_, 29, v_V_5725_);
lean_ctor_set(v_reuseFailAlloc_5740_, 30, v_z_5726_);
lean_ctor_set(v_reuseFailAlloc_5740_, 31, v_zabbrev_5727_);
lean_ctor_set(v_reuseFailAlloc_5740_, 32, v_v_5728_);
lean_ctor_set(v_reuseFailAlloc_5740_, 33, v_O_5729_);
lean_ctor_set(v_reuseFailAlloc_5740_, 34, v_X_5730_);
lean_ctor_set(v_reuseFailAlloc_5740_, 35, v_x_5731_);
lean_ctor_set(v_reuseFailAlloc_5740_, 36, v_Z_5732_);
v___x_5739_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
return v___x_5739_;
}
}
}
}
}
case 23:
{
lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5796_; 
v_isSharedCheck_5796_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5796_ == 0)
{
lean_object* v_unused_5797_; 
v_unused_5797_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5797_);
v___x_5747_ = v_modifier_4583_;
v_isShared_5748_ = v_isSharedCheck_5796_;
goto v_resetjp_5746_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5796_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v_G_5749_; lean_object* v_y_5750_; lean_object* v_u_5751_; lean_object* v_Y_5752_; lean_object* v_D_5753_; lean_object* v_M_5754_; lean_object* v_L_5755_; lean_object* v_d_5756_; lean_object* v_Q_5757_; lean_object* v_q_5758_; lean_object* v_w_5759_; lean_object* v_W_5760_; lean_object* v_E_5761_; lean_object* v_e_5762_; lean_object* v_c_5763_; lean_object* v_F_5764_; lean_object* v_a_5765_; lean_object* v_b_5766_; lean_object* v_B_5767_; lean_object* v_h_5768_; lean_object* v_K_5769_; lean_object* v_k_5770_; lean_object* v_H_5771_; lean_object* v_s_5772_; lean_object* v_S_5773_; lean_object* v_A_5774_; lean_object* v_n_5775_; lean_object* v_N_5776_; lean_object* v_V_5777_; lean_object* v_z_5778_; lean_object* v_zabbrev_5779_; lean_object* v_v_5780_; lean_object* v_O_5781_; lean_object* v_X_5782_; lean_object* v_x_5783_; lean_object* v_Z_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5794_; 
v_G_5749_ = lean_ctor_get(v_date_4582_, 0);
v_y_5750_ = lean_ctor_get(v_date_4582_, 1);
v_u_5751_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5752_ = lean_ctor_get(v_date_4582_, 3);
v_D_5753_ = lean_ctor_get(v_date_4582_, 4);
v_M_5754_ = lean_ctor_get(v_date_4582_, 5);
v_L_5755_ = lean_ctor_get(v_date_4582_, 6);
v_d_5756_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5757_ = lean_ctor_get(v_date_4582_, 8);
v_q_5758_ = lean_ctor_get(v_date_4582_, 9);
v_w_5759_ = lean_ctor_get(v_date_4582_, 10);
v_W_5760_ = lean_ctor_get(v_date_4582_, 11);
v_E_5761_ = lean_ctor_get(v_date_4582_, 12);
v_e_5762_ = lean_ctor_get(v_date_4582_, 13);
v_c_5763_ = lean_ctor_get(v_date_4582_, 14);
v_F_5764_ = lean_ctor_get(v_date_4582_, 15);
v_a_5765_ = lean_ctor_get(v_date_4582_, 16);
v_b_5766_ = lean_ctor_get(v_date_4582_, 17);
v_B_5767_ = lean_ctor_get(v_date_4582_, 18);
v_h_5768_ = lean_ctor_get(v_date_4582_, 19);
v_K_5769_ = lean_ctor_get(v_date_4582_, 20);
v_k_5770_ = lean_ctor_get(v_date_4582_, 21);
v_H_5771_ = lean_ctor_get(v_date_4582_, 22);
v_s_5772_ = lean_ctor_get(v_date_4582_, 24);
v_S_5773_ = lean_ctor_get(v_date_4582_, 25);
v_A_5774_ = lean_ctor_get(v_date_4582_, 26);
v_n_5775_ = lean_ctor_get(v_date_4582_, 27);
v_N_5776_ = lean_ctor_get(v_date_4582_, 28);
v_V_5777_ = lean_ctor_get(v_date_4582_, 29);
v_z_5778_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5779_ = lean_ctor_get(v_date_4582_, 31);
v_v_5780_ = lean_ctor_get(v_date_4582_, 32);
v_O_5781_ = lean_ctor_get(v_date_4582_, 33);
v_X_5782_ = lean_ctor_get(v_date_4582_, 34);
v_x_5783_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5784_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5794_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5794_ == 0)
{
lean_object* v_unused_5795_; 
v_unused_5795_ = lean_ctor_get(v_date_4582_, 23);
lean_dec(v_unused_5795_);
v___x_5786_ = v_date_4582_;
v_isShared_5787_ = v_isSharedCheck_5794_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_Z_5784_);
lean_inc(v_x_5783_);
lean_inc(v_X_5782_);
lean_inc(v_O_5781_);
lean_inc(v_v_5780_);
lean_inc(v_zabbrev_5779_);
lean_inc(v_z_5778_);
lean_inc(v_V_5777_);
lean_inc(v_N_5776_);
lean_inc(v_n_5775_);
lean_inc(v_A_5774_);
lean_inc(v_S_5773_);
lean_inc(v_s_5772_);
lean_inc(v_H_5771_);
lean_inc(v_k_5770_);
lean_inc(v_K_5769_);
lean_inc(v_h_5768_);
lean_inc(v_B_5767_);
lean_inc(v_b_5766_);
lean_inc(v_a_5765_);
lean_inc(v_F_5764_);
lean_inc(v_c_5763_);
lean_inc(v_e_5762_);
lean_inc(v_E_5761_);
lean_inc(v_W_5760_);
lean_inc(v_w_5759_);
lean_inc(v_q_5758_);
lean_inc(v_Q_5757_);
lean_inc(v_d_5756_);
lean_inc(v_L_5755_);
lean_inc(v_M_5754_);
lean_inc(v_D_5753_);
lean_inc(v_Y_5752_);
lean_inc(v_u_5751_);
lean_inc(v_y_5750_);
lean_inc(v_G_5749_);
lean_dec(v_date_4582_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5794_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v___x_5789_; 
if (v_isShared_5748_ == 0)
{
lean_ctor_set_tag(v___x_5747_, 1);
lean_ctor_set(v___x_5747_, 0, v_data_4584_);
v___x_5789_ = v___x_5747_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5793_; 
v_reuseFailAlloc_5793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5793_, 0, v_data_4584_);
v___x_5789_ = v_reuseFailAlloc_5793_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
lean_object* v___x_5791_; 
if (v_isShared_5787_ == 0)
{
lean_ctor_set(v___x_5786_, 23, v___x_5789_);
v___x_5791_ = v___x_5786_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_G_5749_);
lean_ctor_set(v_reuseFailAlloc_5792_, 1, v_y_5750_);
lean_ctor_set(v_reuseFailAlloc_5792_, 2, v_u_5751_);
lean_ctor_set(v_reuseFailAlloc_5792_, 3, v_Y_5752_);
lean_ctor_set(v_reuseFailAlloc_5792_, 4, v_D_5753_);
lean_ctor_set(v_reuseFailAlloc_5792_, 5, v_M_5754_);
lean_ctor_set(v_reuseFailAlloc_5792_, 6, v_L_5755_);
lean_ctor_set(v_reuseFailAlloc_5792_, 7, v_d_5756_);
lean_ctor_set(v_reuseFailAlloc_5792_, 8, v_Q_5757_);
lean_ctor_set(v_reuseFailAlloc_5792_, 9, v_q_5758_);
lean_ctor_set(v_reuseFailAlloc_5792_, 10, v_w_5759_);
lean_ctor_set(v_reuseFailAlloc_5792_, 11, v_W_5760_);
lean_ctor_set(v_reuseFailAlloc_5792_, 12, v_E_5761_);
lean_ctor_set(v_reuseFailAlloc_5792_, 13, v_e_5762_);
lean_ctor_set(v_reuseFailAlloc_5792_, 14, v_c_5763_);
lean_ctor_set(v_reuseFailAlloc_5792_, 15, v_F_5764_);
lean_ctor_set(v_reuseFailAlloc_5792_, 16, v_a_5765_);
lean_ctor_set(v_reuseFailAlloc_5792_, 17, v_b_5766_);
lean_ctor_set(v_reuseFailAlloc_5792_, 18, v_B_5767_);
lean_ctor_set(v_reuseFailAlloc_5792_, 19, v_h_5768_);
lean_ctor_set(v_reuseFailAlloc_5792_, 20, v_K_5769_);
lean_ctor_set(v_reuseFailAlloc_5792_, 21, v_k_5770_);
lean_ctor_set(v_reuseFailAlloc_5792_, 22, v_H_5771_);
lean_ctor_set(v_reuseFailAlloc_5792_, 23, v___x_5789_);
lean_ctor_set(v_reuseFailAlloc_5792_, 24, v_s_5772_);
lean_ctor_set(v_reuseFailAlloc_5792_, 25, v_S_5773_);
lean_ctor_set(v_reuseFailAlloc_5792_, 26, v_A_5774_);
lean_ctor_set(v_reuseFailAlloc_5792_, 27, v_n_5775_);
lean_ctor_set(v_reuseFailAlloc_5792_, 28, v_N_5776_);
lean_ctor_set(v_reuseFailAlloc_5792_, 29, v_V_5777_);
lean_ctor_set(v_reuseFailAlloc_5792_, 30, v_z_5778_);
lean_ctor_set(v_reuseFailAlloc_5792_, 31, v_zabbrev_5779_);
lean_ctor_set(v_reuseFailAlloc_5792_, 32, v_v_5780_);
lean_ctor_set(v_reuseFailAlloc_5792_, 33, v_O_5781_);
lean_ctor_set(v_reuseFailAlloc_5792_, 34, v_X_5782_);
lean_ctor_set(v_reuseFailAlloc_5792_, 35, v_x_5783_);
lean_ctor_set(v_reuseFailAlloc_5792_, 36, v_Z_5784_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
}
}
case 24:
{
lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5848_; 
v_isSharedCheck_5848_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5848_ == 0)
{
lean_object* v_unused_5849_; 
v_unused_5849_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5849_);
v___x_5799_ = v_modifier_4583_;
v_isShared_5800_ = v_isSharedCheck_5848_;
goto v_resetjp_5798_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5848_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v_G_5801_; lean_object* v_y_5802_; lean_object* v_u_5803_; lean_object* v_Y_5804_; lean_object* v_D_5805_; lean_object* v_M_5806_; lean_object* v_L_5807_; lean_object* v_d_5808_; lean_object* v_Q_5809_; lean_object* v_q_5810_; lean_object* v_w_5811_; lean_object* v_W_5812_; lean_object* v_E_5813_; lean_object* v_e_5814_; lean_object* v_c_5815_; lean_object* v_F_5816_; lean_object* v_a_5817_; lean_object* v_b_5818_; lean_object* v_B_5819_; lean_object* v_h_5820_; lean_object* v_K_5821_; lean_object* v_k_5822_; lean_object* v_H_5823_; lean_object* v_m_5824_; lean_object* v_S_5825_; lean_object* v_A_5826_; lean_object* v_n_5827_; lean_object* v_N_5828_; lean_object* v_V_5829_; lean_object* v_z_5830_; lean_object* v_zabbrev_5831_; lean_object* v_v_5832_; lean_object* v_O_5833_; lean_object* v_X_5834_; lean_object* v_x_5835_; lean_object* v_Z_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5846_; 
v_G_5801_ = lean_ctor_get(v_date_4582_, 0);
v_y_5802_ = lean_ctor_get(v_date_4582_, 1);
v_u_5803_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5804_ = lean_ctor_get(v_date_4582_, 3);
v_D_5805_ = lean_ctor_get(v_date_4582_, 4);
v_M_5806_ = lean_ctor_get(v_date_4582_, 5);
v_L_5807_ = lean_ctor_get(v_date_4582_, 6);
v_d_5808_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5809_ = lean_ctor_get(v_date_4582_, 8);
v_q_5810_ = lean_ctor_get(v_date_4582_, 9);
v_w_5811_ = lean_ctor_get(v_date_4582_, 10);
v_W_5812_ = lean_ctor_get(v_date_4582_, 11);
v_E_5813_ = lean_ctor_get(v_date_4582_, 12);
v_e_5814_ = lean_ctor_get(v_date_4582_, 13);
v_c_5815_ = lean_ctor_get(v_date_4582_, 14);
v_F_5816_ = lean_ctor_get(v_date_4582_, 15);
v_a_5817_ = lean_ctor_get(v_date_4582_, 16);
v_b_5818_ = lean_ctor_get(v_date_4582_, 17);
v_B_5819_ = lean_ctor_get(v_date_4582_, 18);
v_h_5820_ = lean_ctor_get(v_date_4582_, 19);
v_K_5821_ = lean_ctor_get(v_date_4582_, 20);
v_k_5822_ = lean_ctor_get(v_date_4582_, 21);
v_H_5823_ = lean_ctor_get(v_date_4582_, 22);
v_m_5824_ = lean_ctor_get(v_date_4582_, 23);
v_S_5825_ = lean_ctor_get(v_date_4582_, 25);
v_A_5826_ = lean_ctor_get(v_date_4582_, 26);
v_n_5827_ = lean_ctor_get(v_date_4582_, 27);
v_N_5828_ = lean_ctor_get(v_date_4582_, 28);
v_V_5829_ = lean_ctor_get(v_date_4582_, 29);
v_z_5830_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5831_ = lean_ctor_get(v_date_4582_, 31);
v_v_5832_ = lean_ctor_get(v_date_4582_, 32);
v_O_5833_ = lean_ctor_get(v_date_4582_, 33);
v_X_5834_ = lean_ctor_get(v_date_4582_, 34);
v_x_5835_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5836_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5846_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5846_ == 0)
{
lean_object* v_unused_5847_; 
v_unused_5847_ = lean_ctor_get(v_date_4582_, 24);
lean_dec(v_unused_5847_);
v___x_5838_ = v_date_4582_;
v_isShared_5839_ = v_isSharedCheck_5846_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_Z_5836_);
lean_inc(v_x_5835_);
lean_inc(v_X_5834_);
lean_inc(v_O_5833_);
lean_inc(v_v_5832_);
lean_inc(v_zabbrev_5831_);
lean_inc(v_z_5830_);
lean_inc(v_V_5829_);
lean_inc(v_N_5828_);
lean_inc(v_n_5827_);
lean_inc(v_A_5826_);
lean_inc(v_S_5825_);
lean_inc(v_m_5824_);
lean_inc(v_H_5823_);
lean_inc(v_k_5822_);
lean_inc(v_K_5821_);
lean_inc(v_h_5820_);
lean_inc(v_B_5819_);
lean_inc(v_b_5818_);
lean_inc(v_a_5817_);
lean_inc(v_F_5816_);
lean_inc(v_c_5815_);
lean_inc(v_e_5814_);
lean_inc(v_E_5813_);
lean_inc(v_W_5812_);
lean_inc(v_w_5811_);
lean_inc(v_q_5810_);
lean_inc(v_Q_5809_);
lean_inc(v_d_5808_);
lean_inc(v_L_5807_);
lean_inc(v_M_5806_);
lean_inc(v_D_5805_);
lean_inc(v_Y_5804_);
lean_inc(v_u_5803_);
lean_inc(v_y_5802_);
lean_inc(v_G_5801_);
lean_dec(v_date_4582_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5846_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___x_5841_; 
if (v_isShared_5800_ == 0)
{
lean_ctor_set_tag(v___x_5799_, 1);
lean_ctor_set(v___x_5799_, 0, v_data_4584_);
v___x_5841_ = v___x_5799_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v_data_4584_);
v___x_5841_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
lean_object* v___x_5843_; 
if (v_isShared_5839_ == 0)
{
lean_ctor_set(v___x_5838_, 24, v___x_5841_);
v___x_5843_ = v___x_5838_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v_G_5801_);
lean_ctor_set(v_reuseFailAlloc_5844_, 1, v_y_5802_);
lean_ctor_set(v_reuseFailAlloc_5844_, 2, v_u_5803_);
lean_ctor_set(v_reuseFailAlloc_5844_, 3, v_Y_5804_);
lean_ctor_set(v_reuseFailAlloc_5844_, 4, v_D_5805_);
lean_ctor_set(v_reuseFailAlloc_5844_, 5, v_M_5806_);
lean_ctor_set(v_reuseFailAlloc_5844_, 6, v_L_5807_);
lean_ctor_set(v_reuseFailAlloc_5844_, 7, v_d_5808_);
lean_ctor_set(v_reuseFailAlloc_5844_, 8, v_Q_5809_);
lean_ctor_set(v_reuseFailAlloc_5844_, 9, v_q_5810_);
lean_ctor_set(v_reuseFailAlloc_5844_, 10, v_w_5811_);
lean_ctor_set(v_reuseFailAlloc_5844_, 11, v_W_5812_);
lean_ctor_set(v_reuseFailAlloc_5844_, 12, v_E_5813_);
lean_ctor_set(v_reuseFailAlloc_5844_, 13, v_e_5814_);
lean_ctor_set(v_reuseFailAlloc_5844_, 14, v_c_5815_);
lean_ctor_set(v_reuseFailAlloc_5844_, 15, v_F_5816_);
lean_ctor_set(v_reuseFailAlloc_5844_, 16, v_a_5817_);
lean_ctor_set(v_reuseFailAlloc_5844_, 17, v_b_5818_);
lean_ctor_set(v_reuseFailAlloc_5844_, 18, v_B_5819_);
lean_ctor_set(v_reuseFailAlloc_5844_, 19, v_h_5820_);
lean_ctor_set(v_reuseFailAlloc_5844_, 20, v_K_5821_);
lean_ctor_set(v_reuseFailAlloc_5844_, 21, v_k_5822_);
lean_ctor_set(v_reuseFailAlloc_5844_, 22, v_H_5823_);
lean_ctor_set(v_reuseFailAlloc_5844_, 23, v_m_5824_);
lean_ctor_set(v_reuseFailAlloc_5844_, 24, v___x_5841_);
lean_ctor_set(v_reuseFailAlloc_5844_, 25, v_S_5825_);
lean_ctor_set(v_reuseFailAlloc_5844_, 26, v_A_5826_);
lean_ctor_set(v_reuseFailAlloc_5844_, 27, v_n_5827_);
lean_ctor_set(v_reuseFailAlloc_5844_, 28, v_N_5828_);
lean_ctor_set(v_reuseFailAlloc_5844_, 29, v_V_5829_);
lean_ctor_set(v_reuseFailAlloc_5844_, 30, v_z_5830_);
lean_ctor_set(v_reuseFailAlloc_5844_, 31, v_zabbrev_5831_);
lean_ctor_set(v_reuseFailAlloc_5844_, 32, v_v_5832_);
lean_ctor_set(v_reuseFailAlloc_5844_, 33, v_O_5833_);
lean_ctor_set(v_reuseFailAlloc_5844_, 34, v_X_5834_);
lean_ctor_set(v_reuseFailAlloc_5844_, 35, v_x_5835_);
lean_ctor_set(v_reuseFailAlloc_5844_, 36, v_Z_5836_);
v___x_5843_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
return v___x_5843_;
}
}
}
}
}
case 25:
{
lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5900_; 
v_isSharedCheck_5900_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5900_ == 0)
{
lean_object* v_unused_5901_; 
v_unused_5901_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5901_);
v___x_5851_ = v_modifier_4583_;
v_isShared_5852_ = v_isSharedCheck_5900_;
goto v_resetjp_5850_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5900_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
lean_object* v_G_5853_; lean_object* v_y_5854_; lean_object* v_u_5855_; lean_object* v_Y_5856_; lean_object* v_D_5857_; lean_object* v_M_5858_; lean_object* v_L_5859_; lean_object* v_d_5860_; lean_object* v_Q_5861_; lean_object* v_q_5862_; lean_object* v_w_5863_; lean_object* v_W_5864_; lean_object* v_E_5865_; lean_object* v_e_5866_; lean_object* v_c_5867_; lean_object* v_F_5868_; lean_object* v_a_5869_; lean_object* v_b_5870_; lean_object* v_B_5871_; lean_object* v_h_5872_; lean_object* v_K_5873_; lean_object* v_k_5874_; lean_object* v_H_5875_; lean_object* v_m_5876_; lean_object* v_s_5877_; lean_object* v_A_5878_; lean_object* v_n_5879_; lean_object* v_N_5880_; lean_object* v_V_5881_; lean_object* v_z_5882_; lean_object* v_zabbrev_5883_; lean_object* v_v_5884_; lean_object* v_O_5885_; lean_object* v_X_5886_; lean_object* v_x_5887_; lean_object* v_Z_5888_; lean_object* v___x_5890_; uint8_t v_isShared_5891_; uint8_t v_isSharedCheck_5898_; 
v_G_5853_ = lean_ctor_get(v_date_4582_, 0);
v_y_5854_ = lean_ctor_get(v_date_4582_, 1);
v_u_5855_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5856_ = lean_ctor_get(v_date_4582_, 3);
v_D_5857_ = lean_ctor_get(v_date_4582_, 4);
v_M_5858_ = lean_ctor_get(v_date_4582_, 5);
v_L_5859_ = lean_ctor_get(v_date_4582_, 6);
v_d_5860_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5861_ = lean_ctor_get(v_date_4582_, 8);
v_q_5862_ = lean_ctor_get(v_date_4582_, 9);
v_w_5863_ = lean_ctor_get(v_date_4582_, 10);
v_W_5864_ = lean_ctor_get(v_date_4582_, 11);
v_E_5865_ = lean_ctor_get(v_date_4582_, 12);
v_e_5866_ = lean_ctor_get(v_date_4582_, 13);
v_c_5867_ = lean_ctor_get(v_date_4582_, 14);
v_F_5868_ = lean_ctor_get(v_date_4582_, 15);
v_a_5869_ = lean_ctor_get(v_date_4582_, 16);
v_b_5870_ = lean_ctor_get(v_date_4582_, 17);
v_B_5871_ = lean_ctor_get(v_date_4582_, 18);
v_h_5872_ = lean_ctor_get(v_date_4582_, 19);
v_K_5873_ = lean_ctor_get(v_date_4582_, 20);
v_k_5874_ = lean_ctor_get(v_date_4582_, 21);
v_H_5875_ = lean_ctor_get(v_date_4582_, 22);
v_m_5876_ = lean_ctor_get(v_date_4582_, 23);
v_s_5877_ = lean_ctor_get(v_date_4582_, 24);
v_A_5878_ = lean_ctor_get(v_date_4582_, 26);
v_n_5879_ = lean_ctor_get(v_date_4582_, 27);
v_N_5880_ = lean_ctor_get(v_date_4582_, 28);
v_V_5881_ = lean_ctor_get(v_date_4582_, 29);
v_z_5882_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5883_ = lean_ctor_get(v_date_4582_, 31);
v_v_5884_ = lean_ctor_get(v_date_4582_, 32);
v_O_5885_ = lean_ctor_get(v_date_4582_, 33);
v_X_5886_ = lean_ctor_get(v_date_4582_, 34);
v_x_5887_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5888_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5898_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5898_ == 0)
{
lean_object* v_unused_5899_; 
v_unused_5899_ = lean_ctor_get(v_date_4582_, 25);
lean_dec(v_unused_5899_);
v___x_5890_ = v_date_4582_;
v_isShared_5891_ = v_isSharedCheck_5898_;
goto v_resetjp_5889_;
}
else
{
lean_inc(v_Z_5888_);
lean_inc(v_x_5887_);
lean_inc(v_X_5886_);
lean_inc(v_O_5885_);
lean_inc(v_v_5884_);
lean_inc(v_zabbrev_5883_);
lean_inc(v_z_5882_);
lean_inc(v_V_5881_);
lean_inc(v_N_5880_);
lean_inc(v_n_5879_);
lean_inc(v_A_5878_);
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
lean_dec(v_date_4582_);
v___x_5890_ = lean_box(0);
v_isShared_5891_ = v_isSharedCheck_5898_;
goto v_resetjp_5889_;
}
v_resetjp_5889_:
{
lean_object* v___x_5893_; 
if (v_isShared_5852_ == 0)
{
lean_ctor_set_tag(v___x_5851_, 1);
lean_ctor_set(v___x_5851_, 0, v_data_4584_);
v___x_5893_ = v___x_5851_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_5897_; 
v_reuseFailAlloc_5897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_data_4584_);
v___x_5893_ = v_reuseFailAlloc_5897_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
lean_object* v___x_5895_; 
if (v_isShared_5891_ == 0)
{
lean_ctor_set(v___x_5890_, 25, v___x_5893_);
v___x_5895_ = v___x_5890_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5896_; 
v_reuseFailAlloc_5896_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5896_, 0, v_G_5853_);
lean_ctor_set(v_reuseFailAlloc_5896_, 1, v_y_5854_);
lean_ctor_set(v_reuseFailAlloc_5896_, 2, v_u_5855_);
lean_ctor_set(v_reuseFailAlloc_5896_, 3, v_Y_5856_);
lean_ctor_set(v_reuseFailAlloc_5896_, 4, v_D_5857_);
lean_ctor_set(v_reuseFailAlloc_5896_, 5, v_M_5858_);
lean_ctor_set(v_reuseFailAlloc_5896_, 6, v_L_5859_);
lean_ctor_set(v_reuseFailAlloc_5896_, 7, v_d_5860_);
lean_ctor_set(v_reuseFailAlloc_5896_, 8, v_Q_5861_);
lean_ctor_set(v_reuseFailAlloc_5896_, 9, v_q_5862_);
lean_ctor_set(v_reuseFailAlloc_5896_, 10, v_w_5863_);
lean_ctor_set(v_reuseFailAlloc_5896_, 11, v_W_5864_);
lean_ctor_set(v_reuseFailAlloc_5896_, 12, v_E_5865_);
lean_ctor_set(v_reuseFailAlloc_5896_, 13, v_e_5866_);
lean_ctor_set(v_reuseFailAlloc_5896_, 14, v_c_5867_);
lean_ctor_set(v_reuseFailAlloc_5896_, 15, v_F_5868_);
lean_ctor_set(v_reuseFailAlloc_5896_, 16, v_a_5869_);
lean_ctor_set(v_reuseFailAlloc_5896_, 17, v_b_5870_);
lean_ctor_set(v_reuseFailAlloc_5896_, 18, v_B_5871_);
lean_ctor_set(v_reuseFailAlloc_5896_, 19, v_h_5872_);
lean_ctor_set(v_reuseFailAlloc_5896_, 20, v_K_5873_);
lean_ctor_set(v_reuseFailAlloc_5896_, 21, v_k_5874_);
lean_ctor_set(v_reuseFailAlloc_5896_, 22, v_H_5875_);
lean_ctor_set(v_reuseFailAlloc_5896_, 23, v_m_5876_);
lean_ctor_set(v_reuseFailAlloc_5896_, 24, v_s_5877_);
lean_ctor_set(v_reuseFailAlloc_5896_, 25, v___x_5893_);
lean_ctor_set(v_reuseFailAlloc_5896_, 26, v_A_5878_);
lean_ctor_set(v_reuseFailAlloc_5896_, 27, v_n_5879_);
lean_ctor_set(v_reuseFailAlloc_5896_, 28, v_N_5880_);
lean_ctor_set(v_reuseFailAlloc_5896_, 29, v_V_5881_);
lean_ctor_set(v_reuseFailAlloc_5896_, 30, v_z_5882_);
lean_ctor_set(v_reuseFailAlloc_5896_, 31, v_zabbrev_5883_);
lean_ctor_set(v_reuseFailAlloc_5896_, 32, v_v_5884_);
lean_ctor_set(v_reuseFailAlloc_5896_, 33, v_O_5885_);
lean_ctor_set(v_reuseFailAlloc_5896_, 34, v_X_5886_);
lean_ctor_set(v_reuseFailAlloc_5896_, 35, v_x_5887_);
lean_ctor_set(v_reuseFailAlloc_5896_, 36, v_Z_5888_);
v___x_5895_ = v_reuseFailAlloc_5896_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
return v___x_5895_;
}
}
}
}
}
case 26:
{
lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5952_; 
v_isSharedCheck_5952_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_5952_ == 0)
{
lean_object* v_unused_5953_; 
v_unused_5953_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_5953_);
v___x_5903_ = v_modifier_4583_;
v_isShared_5904_ = v_isSharedCheck_5952_;
goto v_resetjp_5902_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5903_ = lean_box(0);
v_isShared_5904_ = v_isSharedCheck_5952_;
goto v_resetjp_5902_;
}
v_resetjp_5902_:
{
lean_object* v_G_5905_; lean_object* v_y_5906_; lean_object* v_u_5907_; lean_object* v_Y_5908_; lean_object* v_D_5909_; lean_object* v_M_5910_; lean_object* v_L_5911_; lean_object* v_d_5912_; lean_object* v_Q_5913_; lean_object* v_q_5914_; lean_object* v_w_5915_; lean_object* v_W_5916_; lean_object* v_E_5917_; lean_object* v_e_5918_; lean_object* v_c_5919_; lean_object* v_F_5920_; lean_object* v_a_5921_; lean_object* v_b_5922_; lean_object* v_B_5923_; lean_object* v_h_5924_; lean_object* v_K_5925_; lean_object* v_k_5926_; lean_object* v_H_5927_; lean_object* v_m_5928_; lean_object* v_s_5929_; lean_object* v_S_5930_; lean_object* v_n_5931_; lean_object* v_N_5932_; lean_object* v_V_5933_; lean_object* v_z_5934_; lean_object* v_zabbrev_5935_; lean_object* v_v_5936_; lean_object* v_O_5937_; lean_object* v_X_5938_; lean_object* v_x_5939_; lean_object* v_Z_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5950_; 
v_G_5905_ = lean_ctor_get(v_date_4582_, 0);
v_y_5906_ = lean_ctor_get(v_date_4582_, 1);
v_u_5907_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5908_ = lean_ctor_get(v_date_4582_, 3);
v_D_5909_ = lean_ctor_get(v_date_4582_, 4);
v_M_5910_ = lean_ctor_get(v_date_4582_, 5);
v_L_5911_ = lean_ctor_get(v_date_4582_, 6);
v_d_5912_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5913_ = lean_ctor_get(v_date_4582_, 8);
v_q_5914_ = lean_ctor_get(v_date_4582_, 9);
v_w_5915_ = lean_ctor_get(v_date_4582_, 10);
v_W_5916_ = lean_ctor_get(v_date_4582_, 11);
v_E_5917_ = lean_ctor_get(v_date_4582_, 12);
v_e_5918_ = lean_ctor_get(v_date_4582_, 13);
v_c_5919_ = lean_ctor_get(v_date_4582_, 14);
v_F_5920_ = lean_ctor_get(v_date_4582_, 15);
v_a_5921_ = lean_ctor_get(v_date_4582_, 16);
v_b_5922_ = lean_ctor_get(v_date_4582_, 17);
v_B_5923_ = lean_ctor_get(v_date_4582_, 18);
v_h_5924_ = lean_ctor_get(v_date_4582_, 19);
v_K_5925_ = lean_ctor_get(v_date_4582_, 20);
v_k_5926_ = lean_ctor_get(v_date_4582_, 21);
v_H_5927_ = lean_ctor_get(v_date_4582_, 22);
v_m_5928_ = lean_ctor_get(v_date_4582_, 23);
v_s_5929_ = lean_ctor_get(v_date_4582_, 24);
v_S_5930_ = lean_ctor_get(v_date_4582_, 25);
v_n_5931_ = lean_ctor_get(v_date_4582_, 27);
v_N_5932_ = lean_ctor_get(v_date_4582_, 28);
v_V_5933_ = lean_ctor_get(v_date_4582_, 29);
v_z_5934_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5935_ = lean_ctor_get(v_date_4582_, 31);
v_v_5936_ = lean_ctor_get(v_date_4582_, 32);
v_O_5937_ = lean_ctor_get(v_date_4582_, 33);
v_X_5938_ = lean_ctor_get(v_date_4582_, 34);
v_x_5939_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5940_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_5950_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_5950_ == 0)
{
lean_object* v_unused_5951_; 
v_unused_5951_ = lean_ctor_get(v_date_4582_, 26);
lean_dec(v_unused_5951_);
v___x_5942_ = v_date_4582_;
v_isShared_5943_ = v_isSharedCheck_5950_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_Z_5940_);
lean_inc(v_x_5939_);
lean_inc(v_X_5938_);
lean_inc(v_O_5937_);
lean_inc(v_v_5936_);
lean_inc(v_zabbrev_5935_);
lean_inc(v_z_5934_);
lean_inc(v_V_5933_);
lean_inc(v_N_5932_);
lean_inc(v_n_5931_);
lean_inc(v_S_5930_);
lean_inc(v_s_5929_);
lean_inc(v_m_5928_);
lean_inc(v_H_5927_);
lean_inc(v_k_5926_);
lean_inc(v_K_5925_);
lean_inc(v_h_5924_);
lean_inc(v_B_5923_);
lean_inc(v_b_5922_);
lean_inc(v_a_5921_);
lean_inc(v_F_5920_);
lean_inc(v_c_5919_);
lean_inc(v_e_5918_);
lean_inc(v_E_5917_);
lean_inc(v_W_5916_);
lean_inc(v_w_5915_);
lean_inc(v_q_5914_);
lean_inc(v_Q_5913_);
lean_inc(v_d_5912_);
lean_inc(v_L_5911_);
lean_inc(v_M_5910_);
lean_inc(v_D_5909_);
lean_inc(v_Y_5908_);
lean_inc(v_u_5907_);
lean_inc(v_y_5906_);
lean_inc(v_G_5905_);
lean_dec(v_date_4582_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5950_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v___x_5945_; 
if (v_isShared_5904_ == 0)
{
lean_ctor_set_tag(v___x_5903_, 1);
lean_ctor_set(v___x_5903_, 0, v_data_4584_);
v___x_5945_ = v___x_5903_;
goto v_reusejp_5944_;
}
else
{
lean_object* v_reuseFailAlloc_5949_; 
v_reuseFailAlloc_5949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5949_, 0, v_data_4584_);
v___x_5945_ = v_reuseFailAlloc_5949_;
goto v_reusejp_5944_;
}
v_reusejp_5944_:
{
lean_object* v___x_5947_; 
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 26, v___x_5945_);
v___x_5947_ = v___x_5942_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5948_; 
v_reuseFailAlloc_5948_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5948_, 0, v_G_5905_);
lean_ctor_set(v_reuseFailAlloc_5948_, 1, v_y_5906_);
lean_ctor_set(v_reuseFailAlloc_5948_, 2, v_u_5907_);
lean_ctor_set(v_reuseFailAlloc_5948_, 3, v_Y_5908_);
lean_ctor_set(v_reuseFailAlloc_5948_, 4, v_D_5909_);
lean_ctor_set(v_reuseFailAlloc_5948_, 5, v_M_5910_);
lean_ctor_set(v_reuseFailAlloc_5948_, 6, v_L_5911_);
lean_ctor_set(v_reuseFailAlloc_5948_, 7, v_d_5912_);
lean_ctor_set(v_reuseFailAlloc_5948_, 8, v_Q_5913_);
lean_ctor_set(v_reuseFailAlloc_5948_, 9, v_q_5914_);
lean_ctor_set(v_reuseFailAlloc_5948_, 10, v_w_5915_);
lean_ctor_set(v_reuseFailAlloc_5948_, 11, v_W_5916_);
lean_ctor_set(v_reuseFailAlloc_5948_, 12, v_E_5917_);
lean_ctor_set(v_reuseFailAlloc_5948_, 13, v_e_5918_);
lean_ctor_set(v_reuseFailAlloc_5948_, 14, v_c_5919_);
lean_ctor_set(v_reuseFailAlloc_5948_, 15, v_F_5920_);
lean_ctor_set(v_reuseFailAlloc_5948_, 16, v_a_5921_);
lean_ctor_set(v_reuseFailAlloc_5948_, 17, v_b_5922_);
lean_ctor_set(v_reuseFailAlloc_5948_, 18, v_B_5923_);
lean_ctor_set(v_reuseFailAlloc_5948_, 19, v_h_5924_);
lean_ctor_set(v_reuseFailAlloc_5948_, 20, v_K_5925_);
lean_ctor_set(v_reuseFailAlloc_5948_, 21, v_k_5926_);
lean_ctor_set(v_reuseFailAlloc_5948_, 22, v_H_5927_);
lean_ctor_set(v_reuseFailAlloc_5948_, 23, v_m_5928_);
lean_ctor_set(v_reuseFailAlloc_5948_, 24, v_s_5929_);
lean_ctor_set(v_reuseFailAlloc_5948_, 25, v_S_5930_);
lean_ctor_set(v_reuseFailAlloc_5948_, 26, v___x_5945_);
lean_ctor_set(v_reuseFailAlloc_5948_, 27, v_n_5931_);
lean_ctor_set(v_reuseFailAlloc_5948_, 28, v_N_5932_);
lean_ctor_set(v_reuseFailAlloc_5948_, 29, v_V_5933_);
lean_ctor_set(v_reuseFailAlloc_5948_, 30, v_z_5934_);
lean_ctor_set(v_reuseFailAlloc_5948_, 31, v_zabbrev_5935_);
lean_ctor_set(v_reuseFailAlloc_5948_, 32, v_v_5936_);
lean_ctor_set(v_reuseFailAlloc_5948_, 33, v_O_5937_);
lean_ctor_set(v_reuseFailAlloc_5948_, 34, v_X_5938_);
lean_ctor_set(v_reuseFailAlloc_5948_, 35, v_x_5939_);
lean_ctor_set(v_reuseFailAlloc_5948_, 36, v_Z_5940_);
v___x_5947_ = v_reuseFailAlloc_5948_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
return v___x_5947_;
}
}
}
}
}
case 27:
{
lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_6004_; 
v_isSharedCheck_6004_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_6004_ == 0)
{
lean_object* v_unused_6005_; 
v_unused_6005_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_6005_);
v___x_5955_ = v_modifier_4583_;
v_isShared_5956_ = v_isSharedCheck_6004_;
goto v_resetjp_5954_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_5955_ = lean_box(0);
v_isShared_5956_ = v_isSharedCheck_6004_;
goto v_resetjp_5954_;
}
v_resetjp_5954_:
{
lean_object* v_G_5957_; lean_object* v_y_5958_; lean_object* v_u_5959_; lean_object* v_Y_5960_; lean_object* v_D_5961_; lean_object* v_M_5962_; lean_object* v_L_5963_; lean_object* v_d_5964_; lean_object* v_Q_5965_; lean_object* v_q_5966_; lean_object* v_w_5967_; lean_object* v_W_5968_; lean_object* v_E_5969_; lean_object* v_e_5970_; lean_object* v_c_5971_; lean_object* v_F_5972_; lean_object* v_a_5973_; lean_object* v_b_5974_; lean_object* v_B_5975_; lean_object* v_h_5976_; lean_object* v_K_5977_; lean_object* v_k_5978_; lean_object* v_H_5979_; lean_object* v_m_5980_; lean_object* v_s_5981_; lean_object* v_S_5982_; lean_object* v_A_5983_; lean_object* v_N_5984_; lean_object* v_V_5985_; lean_object* v_z_5986_; lean_object* v_zabbrev_5987_; lean_object* v_v_5988_; lean_object* v_O_5989_; lean_object* v_X_5990_; lean_object* v_x_5991_; lean_object* v_Z_5992_; lean_object* v___x_5994_; uint8_t v_isShared_5995_; uint8_t v_isSharedCheck_6002_; 
v_G_5957_ = lean_ctor_get(v_date_4582_, 0);
v_y_5958_ = lean_ctor_get(v_date_4582_, 1);
v_u_5959_ = lean_ctor_get(v_date_4582_, 2);
v_Y_5960_ = lean_ctor_get(v_date_4582_, 3);
v_D_5961_ = lean_ctor_get(v_date_4582_, 4);
v_M_5962_ = lean_ctor_get(v_date_4582_, 5);
v_L_5963_ = lean_ctor_get(v_date_4582_, 6);
v_d_5964_ = lean_ctor_get(v_date_4582_, 7);
v_Q_5965_ = lean_ctor_get(v_date_4582_, 8);
v_q_5966_ = lean_ctor_get(v_date_4582_, 9);
v_w_5967_ = lean_ctor_get(v_date_4582_, 10);
v_W_5968_ = lean_ctor_get(v_date_4582_, 11);
v_E_5969_ = lean_ctor_get(v_date_4582_, 12);
v_e_5970_ = lean_ctor_get(v_date_4582_, 13);
v_c_5971_ = lean_ctor_get(v_date_4582_, 14);
v_F_5972_ = lean_ctor_get(v_date_4582_, 15);
v_a_5973_ = lean_ctor_get(v_date_4582_, 16);
v_b_5974_ = lean_ctor_get(v_date_4582_, 17);
v_B_5975_ = lean_ctor_get(v_date_4582_, 18);
v_h_5976_ = lean_ctor_get(v_date_4582_, 19);
v_K_5977_ = lean_ctor_get(v_date_4582_, 20);
v_k_5978_ = lean_ctor_get(v_date_4582_, 21);
v_H_5979_ = lean_ctor_get(v_date_4582_, 22);
v_m_5980_ = lean_ctor_get(v_date_4582_, 23);
v_s_5981_ = lean_ctor_get(v_date_4582_, 24);
v_S_5982_ = lean_ctor_get(v_date_4582_, 25);
v_A_5983_ = lean_ctor_get(v_date_4582_, 26);
v_N_5984_ = lean_ctor_get(v_date_4582_, 28);
v_V_5985_ = lean_ctor_get(v_date_4582_, 29);
v_z_5986_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_5987_ = lean_ctor_get(v_date_4582_, 31);
v_v_5988_ = lean_ctor_get(v_date_4582_, 32);
v_O_5989_ = lean_ctor_get(v_date_4582_, 33);
v_X_5990_ = lean_ctor_get(v_date_4582_, 34);
v_x_5991_ = lean_ctor_get(v_date_4582_, 35);
v_Z_5992_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_6002_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_6002_ == 0)
{
lean_object* v_unused_6003_; 
v_unused_6003_ = lean_ctor_get(v_date_4582_, 27);
lean_dec(v_unused_6003_);
v___x_5994_ = v_date_4582_;
v_isShared_5995_ = v_isSharedCheck_6002_;
goto v_resetjp_5993_;
}
else
{
lean_inc(v_Z_5992_);
lean_inc(v_x_5991_);
lean_inc(v_X_5990_);
lean_inc(v_O_5989_);
lean_inc(v_v_5988_);
lean_inc(v_zabbrev_5987_);
lean_inc(v_z_5986_);
lean_inc(v_V_5985_);
lean_inc(v_N_5984_);
lean_inc(v_A_5983_);
lean_inc(v_S_5982_);
lean_inc(v_s_5981_);
lean_inc(v_m_5980_);
lean_inc(v_H_5979_);
lean_inc(v_k_5978_);
lean_inc(v_K_5977_);
lean_inc(v_h_5976_);
lean_inc(v_B_5975_);
lean_inc(v_b_5974_);
lean_inc(v_a_5973_);
lean_inc(v_F_5972_);
lean_inc(v_c_5971_);
lean_inc(v_e_5970_);
lean_inc(v_E_5969_);
lean_inc(v_W_5968_);
lean_inc(v_w_5967_);
lean_inc(v_q_5966_);
lean_inc(v_Q_5965_);
lean_inc(v_d_5964_);
lean_inc(v_L_5963_);
lean_inc(v_M_5962_);
lean_inc(v_D_5961_);
lean_inc(v_Y_5960_);
lean_inc(v_u_5959_);
lean_inc(v_y_5958_);
lean_inc(v_G_5957_);
lean_dec(v_date_4582_);
v___x_5994_ = lean_box(0);
v_isShared_5995_ = v_isSharedCheck_6002_;
goto v_resetjp_5993_;
}
v_resetjp_5993_:
{
lean_object* v___x_5997_; 
if (v_isShared_5956_ == 0)
{
lean_ctor_set_tag(v___x_5955_, 1);
lean_ctor_set(v___x_5955_, 0, v_data_4584_);
v___x_5997_ = v___x_5955_;
goto v_reusejp_5996_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v_data_4584_);
v___x_5997_ = v_reuseFailAlloc_6001_;
goto v_reusejp_5996_;
}
v_reusejp_5996_:
{
lean_object* v___x_5999_; 
if (v_isShared_5995_ == 0)
{
lean_ctor_set(v___x_5994_, 27, v___x_5997_);
v___x_5999_ = v___x_5994_;
goto v_reusejp_5998_;
}
else
{
lean_object* v_reuseFailAlloc_6000_; 
v_reuseFailAlloc_6000_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6000_, 0, v_G_5957_);
lean_ctor_set(v_reuseFailAlloc_6000_, 1, v_y_5958_);
lean_ctor_set(v_reuseFailAlloc_6000_, 2, v_u_5959_);
lean_ctor_set(v_reuseFailAlloc_6000_, 3, v_Y_5960_);
lean_ctor_set(v_reuseFailAlloc_6000_, 4, v_D_5961_);
lean_ctor_set(v_reuseFailAlloc_6000_, 5, v_M_5962_);
lean_ctor_set(v_reuseFailAlloc_6000_, 6, v_L_5963_);
lean_ctor_set(v_reuseFailAlloc_6000_, 7, v_d_5964_);
lean_ctor_set(v_reuseFailAlloc_6000_, 8, v_Q_5965_);
lean_ctor_set(v_reuseFailAlloc_6000_, 9, v_q_5966_);
lean_ctor_set(v_reuseFailAlloc_6000_, 10, v_w_5967_);
lean_ctor_set(v_reuseFailAlloc_6000_, 11, v_W_5968_);
lean_ctor_set(v_reuseFailAlloc_6000_, 12, v_E_5969_);
lean_ctor_set(v_reuseFailAlloc_6000_, 13, v_e_5970_);
lean_ctor_set(v_reuseFailAlloc_6000_, 14, v_c_5971_);
lean_ctor_set(v_reuseFailAlloc_6000_, 15, v_F_5972_);
lean_ctor_set(v_reuseFailAlloc_6000_, 16, v_a_5973_);
lean_ctor_set(v_reuseFailAlloc_6000_, 17, v_b_5974_);
lean_ctor_set(v_reuseFailAlloc_6000_, 18, v_B_5975_);
lean_ctor_set(v_reuseFailAlloc_6000_, 19, v_h_5976_);
lean_ctor_set(v_reuseFailAlloc_6000_, 20, v_K_5977_);
lean_ctor_set(v_reuseFailAlloc_6000_, 21, v_k_5978_);
lean_ctor_set(v_reuseFailAlloc_6000_, 22, v_H_5979_);
lean_ctor_set(v_reuseFailAlloc_6000_, 23, v_m_5980_);
lean_ctor_set(v_reuseFailAlloc_6000_, 24, v_s_5981_);
lean_ctor_set(v_reuseFailAlloc_6000_, 25, v_S_5982_);
lean_ctor_set(v_reuseFailAlloc_6000_, 26, v_A_5983_);
lean_ctor_set(v_reuseFailAlloc_6000_, 27, v___x_5997_);
lean_ctor_set(v_reuseFailAlloc_6000_, 28, v_N_5984_);
lean_ctor_set(v_reuseFailAlloc_6000_, 29, v_V_5985_);
lean_ctor_set(v_reuseFailAlloc_6000_, 30, v_z_5986_);
lean_ctor_set(v_reuseFailAlloc_6000_, 31, v_zabbrev_5987_);
lean_ctor_set(v_reuseFailAlloc_6000_, 32, v_v_5988_);
lean_ctor_set(v_reuseFailAlloc_6000_, 33, v_O_5989_);
lean_ctor_set(v_reuseFailAlloc_6000_, 34, v_X_5990_);
lean_ctor_set(v_reuseFailAlloc_6000_, 35, v_x_5991_);
lean_ctor_set(v_reuseFailAlloc_6000_, 36, v_Z_5992_);
v___x_5999_ = v_reuseFailAlloc_6000_;
goto v_reusejp_5998_;
}
v_reusejp_5998_:
{
return v___x_5999_;
}
}
}
}
}
case 28:
{
lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6056_; 
v_isSharedCheck_6056_ = !lean_is_exclusive(v_modifier_4583_);
if (v_isSharedCheck_6056_ == 0)
{
lean_object* v_unused_6057_; 
v_unused_6057_ = lean_ctor_get(v_modifier_4583_, 0);
lean_dec(v_unused_6057_);
v___x_6007_ = v_modifier_4583_;
v_isShared_6008_ = v_isSharedCheck_6056_;
goto v_resetjp_6006_;
}
else
{
lean_dec(v_modifier_4583_);
v___x_6007_ = lean_box(0);
v_isShared_6008_ = v_isSharedCheck_6056_;
goto v_resetjp_6006_;
}
v_resetjp_6006_:
{
lean_object* v_G_6009_; lean_object* v_y_6010_; lean_object* v_u_6011_; lean_object* v_Y_6012_; lean_object* v_D_6013_; lean_object* v_M_6014_; lean_object* v_L_6015_; lean_object* v_d_6016_; lean_object* v_Q_6017_; lean_object* v_q_6018_; lean_object* v_w_6019_; lean_object* v_W_6020_; lean_object* v_E_6021_; lean_object* v_e_6022_; lean_object* v_c_6023_; lean_object* v_F_6024_; lean_object* v_a_6025_; lean_object* v_b_6026_; lean_object* v_B_6027_; lean_object* v_h_6028_; lean_object* v_K_6029_; lean_object* v_k_6030_; lean_object* v_H_6031_; lean_object* v_m_6032_; lean_object* v_s_6033_; lean_object* v_S_6034_; lean_object* v_A_6035_; lean_object* v_n_6036_; lean_object* v_V_6037_; lean_object* v_z_6038_; lean_object* v_zabbrev_6039_; lean_object* v_v_6040_; lean_object* v_O_6041_; lean_object* v_X_6042_; lean_object* v_x_6043_; lean_object* v_Z_6044_; lean_object* v___x_6046_; uint8_t v_isShared_6047_; uint8_t v_isSharedCheck_6054_; 
v_G_6009_ = lean_ctor_get(v_date_4582_, 0);
v_y_6010_ = lean_ctor_get(v_date_4582_, 1);
v_u_6011_ = lean_ctor_get(v_date_4582_, 2);
v_Y_6012_ = lean_ctor_get(v_date_4582_, 3);
v_D_6013_ = lean_ctor_get(v_date_4582_, 4);
v_M_6014_ = lean_ctor_get(v_date_4582_, 5);
v_L_6015_ = lean_ctor_get(v_date_4582_, 6);
v_d_6016_ = lean_ctor_get(v_date_4582_, 7);
v_Q_6017_ = lean_ctor_get(v_date_4582_, 8);
v_q_6018_ = lean_ctor_get(v_date_4582_, 9);
v_w_6019_ = lean_ctor_get(v_date_4582_, 10);
v_W_6020_ = lean_ctor_get(v_date_4582_, 11);
v_E_6021_ = lean_ctor_get(v_date_4582_, 12);
v_e_6022_ = lean_ctor_get(v_date_4582_, 13);
v_c_6023_ = lean_ctor_get(v_date_4582_, 14);
v_F_6024_ = lean_ctor_get(v_date_4582_, 15);
v_a_6025_ = lean_ctor_get(v_date_4582_, 16);
v_b_6026_ = lean_ctor_get(v_date_4582_, 17);
v_B_6027_ = lean_ctor_get(v_date_4582_, 18);
v_h_6028_ = lean_ctor_get(v_date_4582_, 19);
v_K_6029_ = lean_ctor_get(v_date_4582_, 20);
v_k_6030_ = lean_ctor_get(v_date_4582_, 21);
v_H_6031_ = lean_ctor_get(v_date_4582_, 22);
v_m_6032_ = lean_ctor_get(v_date_4582_, 23);
v_s_6033_ = lean_ctor_get(v_date_4582_, 24);
v_S_6034_ = lean_ctor_get(v_date_4582_, 25);
v_A_6035_ = lean_ctor_get(v_date_4582_, 26);
v_n_6036_ = lean_ctor_get(v_date_4582_, 27);
v_V_6037_ = lean_ctor_get(v_date_4582_, 29);
v_z_6038_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_6039_ = lean_ctor_get(v_date_4582_, 31);
v_v_6040_ = lean_ctor_get(v_date_4582_, 32);
v_O_6041_ = lean_ctor_get(v_date_4582_, 33);
v_X_6042_ = lean_ctor_get(v_date_4582_, 34);
v_x_6043_ = lean_ctor_get(v_date_4582_, 35);
v_Z_6044_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_6054_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_6054_ == 0)
{
lean_object* v_unused_6055_; 
v_unused_6055_ = lean_ctor_get(v_date_4582_, 28);
lean_dec(v_unused_6055_);
v___x_6046_ = v_date_4582_;
v_isShared_6047_ = v_isSharedCheck_6054_;
goto v_resetjp_6045_;
}
else
{
lean_inc(v_Z_6044_);
lean_inc(v_x_6043_);
lean_inc(v_X_6042_);
lean_inc(v_O_6041_);
lean_inc(v_v_6040_);
lean_inc(v_zabbrev_6039_);
lean_inc(v_z_6038_);
lean_inc(v_V_6037_);
lean_inc(v_n_6036_);
lean_inc(v_A_6035_);
lean_inc(v_S_6034_);
lean_inc(v_s_6033_);
lean_inc(v_m_6032_);
lean_inc(v_H_6031_);
lean_inc(v_k_6030_);
lean_inc(v_K_6029_);
lean_inc(v_h_6028_);
lean_inc(v_B_6027_);
lean_inc(v_b_6026_);
lean_inc(v_a_6025_);
lean_inc(v_F_6024_);
lean_inc(v_c_6023_);
lean_inc(v_e_6022_);
lean_inc(v_E_6021_);
lean_inc(v_W_6020_);
lean_inc(v_w_6019_);
lean_inc(v_q_6018_);
lean_inc(v_Q_6017_);
lean_inc(v_d_6016_);
lean_inc(v_L_6015_);
lean_inc(v_M_6014_);
lean_inc(v_D_6013_);
lean_inc(v_Y_6012_);
lean_inc(v_u_6011_);
lean_inc(v_y_6010_);
lean_inc(v_G_6009_);
lean_dec(v_date_4582_);
v___x_6046_ = lean_box(0);
v_isShared_6047_ = v_isSharedCheck_6054_;
goto v_resetjp_6045_;
}
v_resetjp_6045_:
{
lean_object* v___x_6049_; 
if (v_isShared_6008_ == 0)
{
lean_ctor_set_tag(v___x_6007_, 1);
lean_ctor_set(v___x_6007_, 0, v_data_4584_);
v___x_6049_ = v___x_6007_;
goto v_reusejp_6048_;
}
else
{
lean_object* v_reuseFailAlloc_6053_; 
v_reuseFailAlloc_6053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6053_, 0, v_data_4584_);
v___x_6049_ = v_reuseFailAlloc_6053_;
goto v_reusejp_6048_;
}
v_reusejp_6048_:
{
lean_object* v___x_6051_; 
if (v_isShared_6047_ == 0)
{
lean_ctor_set(v___x_6046_, 28, v___x_6049_);
v___x_6051_ = v___x_6046_;
goto v_reusejp_6050_;
}
else
{
lean_object* v_reuseFailAlloc_6052_; 
v_reuseFailAlloc_6052_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_G_6009_);
lean_ctor_set(v_reuseFailAlloc_6052_, 1, v_y_6010_);
lean_ctor_set(v_reuseFailAlloc_6052_, 2, v_u_6011_);
lean_ctor_set(v_reuseFailAlloc_6052_, 3, v_Y_6012_);
lean_ctor_set(v_reuseFailAlloc_6052_, 4, v_D_6013_);
lean_ctor_set(v_reuseFailAlloc_6052_, 5, v_M_6014_);
lean_ctor_set(v_reuseFailAlloc_6052_, 6, v_L_6015_);
lean_ctor_set(v_reuseFailAlloc_6052_, 7, v_d_6016_);
lean_ctor_set(v_reuseFailAlloc_6052_, 8, v_Q_6017_);
lean_ctor_set(v_reuseFailAlloc_6052_, 9, v_q_6018_);
lean_ctor_set(v_reuseFailAlloc_6052_, 10, v_w_6019_);
lean_ctor_set(v_reuseFailAlloc_6052_, 11, v_W_6020_);
lean_ctor_set(v_reuseFailAlloc_6052_, 12, v_E_6021_);
lean_ctor_set(v_reuseFailAlloc_6052_, 13, v_e_6022_);
lean_ctor_set(v_reuseFailAlloc_6052_, 14, v_c_6023_);
lean_ctor_set(v_reuseFailAlloc_6052_, 15, v_F_6024_);
lean_ctor_set(v_reuseFailAlloc_6052_, 16, v_a_6025_);
lean_ctor_set(v_reuseFailAlloc_6052_, 17, v_b_6026_);
lean_ctor_set(v_reuseFailAlloc_6052_, 18, v_B_6027_);
lean_ctor_set(v_reuseFailAlloc_6052_, 19, v_h_6028_);
lean_ctor_set(v_reuseFailAlloc_6052_, 20, v_K_6029_);
lean_ctor_set(v_reuseFailAlloc_6052_, 21, v_k_6030_);
lean_ctor_set(v_reuseFailAlloc_6052_, 22, v_H_6031_);
lean_ctor_set(v_reuseFailAlloc_6052_, 23, v_m_6032_);
lean_ctor_set(v_reuseFailAlloc_6052_, 24, v_s_6033_);
lean_ctor_set(v_reuseFailAlloc_6052_, 25, v_S_6034_);
lean_ctor_set(v_reuseFailAlloc_6052_, 26, v_A_6035_);
lean_ctor_set(v_reuseFailAlloc_6052_, 27, v_n_6036_);
lean_ctor_set(v_reuseFailAlloc_6052_, 28, v___x_6049_);
lean_ctor_set(v_reuseFailAlloc_6052_, 29, v_V_6037_);
lean_ctor_set(v_reuseFailAlloc_6052_, 30, v_z_6038_);
lean_ctor_set(v_reuseFailAlloc_6052_, 31, v_zabbrev_6039_);
lean_ctor_set(v_reuseFailAlloc_6052_, 32, v_v_6040_);
lean_ctor_set(v_reuseFailAlloc_6052_, 33, v_O_6041_);
lean_ctor_set(v_reuseFailAlloc_6052_, 34, v_X_6042_);
lean_ctor_set(v_reuseFailAlloc_6052_, 35, v_x_6043_);
lean_ctor_set(v_reuseFailAlloc_6052_, 36, v_Z_6044_);
v___x_6051_ = v_reuseFailAlloc_6052_;
goto v_reusejp_6050_;
}
v_reusejp_6050_:
{
return v___x_6051_;
}
}
}
}
}
case 29:
{
lean_object* v_G_6058_; lean_object* v_y_6059_; lean_object* v_u_6060_; lean_object* v_Y_6061_; lean_object* v_D_6062_; lean_object* v_M_6063_; lean_object* v_L_6064_; lean_object* v_d_6065_; lean_object* v_Q_6066_; lean_object* v_q_6067_; lean_object* v_w_6068_; lean_object* v_W_6069_; lean_object* v_E_6070_; lean_object* v_e_6071_; lean_object* v_c_6072_; lean_object* v_F_6073_; lean_object* v_a_6074_; lean_object* v_b_6075_; lean_object* v_B_6076_; lean_object* v_h_6077_; lean_object* v_K_6078_; lean_object* v_k_6079_; lean_object* v_H_6080_; lean_object* v_m_6081_; lean_object* v_s_6082_; lean_object* v_S_6083_; lean_object* v_A_6084_; lean_object* v_n_6085_; lean_object* v_N_6086_; lean_object* v_z_6087_; lean_object* v_zabbrev_6088_; lean_object* v_v_6089_; lean_object* v_O_6090_; lean_object* v_X_6091_; lean_object* v_x_6092_; lean_object* v_Z_6093_; lean_object* v___x_6095_; uint8_t v_isShared_6096_; uint8_t v_isSharedCheck_6101_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_G_6058_ = lean_ctor_get(v_date_4582_, 0);
v_y_6059_ = lean_ctor_get(v_date_4582_, 1);
v_u_6060_ = lean_ctor_get(v_date_4582_, 2);
v_Y_6061_ = lean_ctor_get(v_date_4582_, 3);
v_D_6062_ = lean_ctor_get(v_date_4582_, 4);
v_M_6063_ = lean_ctor_get(v_date_4582_, 5);
v_L_6064_ = lean_ctor_get(v_date_4582_, 6);
v_d_6065_ = lean_ctor_get(v_date_4582_, 7);
v_Q_6066_ = lean_ctor_get(v_date_4582_, 8);
v_q_6067_ = lean_ctor_get(v_date_4582_, 9);
v_w_6068_ = lean_ctor_get(v_date_4582_, 10);
v_W_6069_ = lean_ctor_get(v_date_4582_, 11);
v_E_6070_ = lean_ctor_get(v_date_4582_, 12);
v_e_6071_ = lean_ctor_get(v_date_4582_, 13);
v_c_6072_ = lean_ctor_get(v_date_4582_, 14);
v_F_6073_ = lean_ctor_get(v_date_4582_, 15);
v_a_6074_ = lean_ctor_get(v_date_4582_, 16);
v_b_6075_ = lean_ctor_get(v_date_4582_, 17);
v_B_6076_ = lean_ctor_get(v_date_4582_, 18);
v_h_6077_ = lean_ctor_get(v_date_4582_, 19);
v_K_6078_ = lean_ctor_get(v_date_4582_, 20);
v_k_6079_ = lean_ctor_get(v_date_4582_, 21);
v_H_6080_ = lean_ctor_get(v_date_4582_, 22);
v_m_6081_ = lean_ctor_get(v_date_4582_, 23);
v_s_6082_ = lean_ctor_get(v_date_4582_, 24);
v_S_6083_ = lean_ctor_get(v_date_4582_, 25);
v_A_6084_ = lean_ctor_get(v_date_4582_, 26);
v_n_6085_ = lean_ctor_get(v_date_4582_, 27);
v_N_6086_ = lean_ctor_get(v_date_4582_, 28);
v_z_6087_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_6088_ = lean_ctor_get(v_date_4582_, 31);
v_v_6089_ = lean_ctor_get(v_date_4582_, 32);
v_O_6090_ = lean_ctor_get(v_date_4582_, 33);
v_X_6091_ = lean_ctor_get(v_date_4582_, 34);
v_x_6092_ = lean_ctor_get(v_date_4582_, 35);
v_Z_6093_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_6101_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_6101_ == 0)
{
lean_object* v_unused_6102_; 
v_unused_6102_ = lean_ctor_get(v_date_4582_, 29);
lean_dec(v_unused_6102_);
v___x_6095_ = v_date_4582_;
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
lean_inc(v_z_6087_);
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
lean_dec(v_date_4582_);
v___x_6095_ = lean_box(0);
v_isShared_6096_ = v_isSharedCheck_6101_;
goto v_resetjp_6094_;
}
v_resetjp_6094_:
{
lean_object* v___x_6097_; lean_object* v___x_6099_; 
v___x_6097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6097_, 0, v_data_4584_);
if (v_isShared_6096_ == 0)
{
lean_ctor_set(v___x_6095_, 29, v___x_6097_);
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
lean_ctor_set(v_reuseFailAlloc_6100_, 29, v___x_6097_);
lean_ctor_set(v_reuseFailAlloc_6100_, 30, v_z_6087_);
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
case 30:
{
uint8_t v_presentation_6103_; 
v_presentation_6103_ = lean_ctor_get_uint8(v_modifier_4583_, 0);
lean_dec_ref_known(v_modifier_4583_, 0);
if (v_presentation_6103_ == 0)
{
lean_object* v_G_6104_; lean_object* v_y_6105_; lean_object* v_u_6106_; lean_object* v_Y_6107_; lean_object* v_D_6108_; lean_object* v_M_6109_; lean_object* v_L_6110_; lean_object* v_d_6111_; lean_object* v_Q_6112_; lean_object* v_q_6113_; lean_object* v_w_6114_; lean_object* v_W_6115_; lean_object* v_E_6116_; lean_object* v_e_6117_; lean_object* v_c_6118_; lean_object* v_F_6119_; lean_object* v_a_6120_; lean_object* v_b_6121_; lean_object* v_B_6122_; lean_object* v_h_6123_; lean_object* v_K_6124_; lean_object* v_k_6125_; lean_object* v_H_6126_; lean_object* v_m_6127_; lean_object* v_s_6128_; lean_object* v_S_6129_; lean_object* v_A_6130_; lean_object* v_n_6131_; lean_object* v_N_6132_; lean_object* v_V_6133_; lean_object* v_z_6134_; lean_object* v_v_6135_; lean_object* v_O_6136_; lean_object* v_X_6137_; lean_object* v_x_6138_; lean_object* v_Z_6139_; lean_object* v___x_6141_; uint8_t v_isShared_6142_; uint8_t v_isSharedCheck_6147_; 
v_G_6104_ = lean_ctor_get(v_date_4582_, 0);
v_y_6105_ = lean_ctor_get(v_date_4582_, 1);
v_u_6106_ = lean_ctor_get(v_date_4582_, 2);
v_Y_6107_ = lean_ctor_get(v_date_4582_, 3);
v_D_6108_ = lean_ctor_get(v_date_4582_, 4);
v_M_6109_ = lean_ctor_get(v_date_4582_, 5);
v_L_6110_ = lean_ctor_get(v_date_4582_, 6);
v_d_6111_ = lean_ctor_get(v_date_4582_, 7);
v_Q_6112_ = lean_ctor_get(v_date_4582_, 8);
v_q_6113_ = lean_ctor_get(v_date_4582_, 9);
v_w_6114_ = lean_ctor_get(v_date_4582_, 10);
v_W_6115_ = lean_ctor_get(v_date_4582_, 11);
v_E_6116_ = lean_ctor_get(v_date_4582_, 12);
v_e_6117_ = lean_ctor_get(v_date_4582_, 13);
v_c_6118_ = lean_ctor_get(v_date_4582_, 14);
v_F_6119_ = lean_ctor_get(v_date_4582_, 15);
v_a_6120_ = lean_ctor_get(v_date_4582_, 16);
v_b_6121_ = lean_ctor_get(v_date_4582_, 17);
v_B_6122_ = lean_ctor_get(v_date_4582_, 18);
v_h_6123_ = lean_ctor_get(v_date_4582_, 19);
v_K_6124_ = lean_ctor_get(v_date_4582_, 20);
v_k_6125_ = lean_ctor_get(v_date_4582_, 21);
v_H_6126_ = lean_ctor_get(v_date_4582_, 22);
v_m_6127_ = lean_ctor_get(v_date_4582_, 23);
v_s_6128_ = lean_ctor_get(v_date_4582_, 24);
v_S_6129_ = lean_ctor_get(v_date_4582_, 25);
v_A_6130_ = lean_ctor_get(v_date_4582_, 26);
v_n_6131_ = lean_ctor_get(v_date_4582_, 27);
v_N_6132_ = lean_ctor_get(v_date_4582_, 28);
v_V_6133_ = lean_ctor_get(v_date_4582_, 29);
v_z_6134_ = lean_ctor_get(v_date_4582_, 30);
v_v_6135_ = lean_ctor_get(v_date_4582_, 32);
v_O_6136_ = lean_ctor_get(v_date_4582_, 33);
v_X_6137_ = lean_ctor_get(v_date_4582_, 34);
v_x_6138_ = lean_ctor_get(v_date_4582_, 35);
v_Z_6139_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_6147_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_6147_ == 0)
{
lean_object* v_unused_6148_; 
v_unused_6148_ = lean_ctor_get(v_date_4582_, 31);
lean_dec(v_unused_6148_);
v___x_6141_ = v_date_4582_;
v_isShared_6142_ = v_isSharedCheck_6147_;
goto v_resetjp_6140_;
}
else
{
lean_inc(v_Z_6139_);
lean_inc(v_x_6138_);
lean_inc(v_X_6137_);
lean_inc(v_O_6136_);
lean_inc(v_v_6135_);
lean_inc(v_z_6134_);
lean_inc(v_V_6133_);
lean_inc(v_N_6132_);
lean_inc(v_n_6131_);
lean_inc(v_A_6130_);
lean_inc(v_S_6129_);
lean_inc(v_s_6128_);
lean_inc(v_m_6127_);
lean_inc(v_H_6126_);
lean_inc(v_k_6125_);
lean_inc(v_K_6124_);
lean_inc(v_h_6123_);
lean_inc(v_B_6122_);
lean_inc(v_b_6121_);
lean_inc(v_a_6120_);
lean_inc(v_F_6119_);
lean_inc(v_c_6118_);
lean_inc(v_e_6117_);
lean_inc(v_E_6116_);
lean_inc(v_W_6115_);
lean_inc(v_w_6114_);
lean_inc(v_q_6113_);
lean_inc(v_Q_6112_);
lean_inc(v_d_6111_);
lean_inc(v_L_6110_);
lean_inc(v_M_6109_);
lean_inc(v_D_6108_);
lean_inc(v_Y_6107_);
lean_inc(v_u_6106_);
lean_inc(v_y_6105_);
lean_inc(v_G_6104_);
lean_dec(v_date_4582_);
v___x_6141_ = lean_box(0);
v_isShared_6142_ = v_isSharedCheck_6147_;
goto v_resetjp_6140_;
}
v_resetjp_6140_:
{
lean_object* v___x_6143_; lean_object* v___x_6145_; 
v___x_6143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6143_, 0, v_data_4584_);
if (v_isShared_6142_ == 0)
{
lean_ctor_set(v___x_6141_, 31, v___x_6143_);
v___x_6145_ = v___x_6141_;
goto v_reusejp_6144_;
}
else
{
lean_object* v_reuseFailAlloc_6146_; 
v_reuseFailAlloc_6146_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6146_, 0, v_G_6104_);
lean_ctor_set(v_reuseFailAlloc_6146_, 1, v_y_6105_);
lean_ctor_set(v_reuseFailAlloc_6146_, 2, v_u_6106_);
lean_ctor_set(v_reuseFailAlloc_6146_, 3, v_Y_6107_);
lean_ctor_set(v_reuseFailAlloc_6146_, 4, v_D_6108_);
lean_ctor_set(v_reuseFailAlloc_6146_, 5, v_M_6109_);
lean_ctor_set(v_reuseFailAlloc_6146_, 6, v_L_6110_);
lean_ctor_set(v_reuseFailAlloc_6146_, 7, v_d_6111_);
lean_ctor_set(v_reuseFailAlloc_6146_, 8, v_Q_6112_);
lean_ctor_set(v_reuseFailAlloc_6146_, 9, v_q_6113_);
lean_ctor_set(v_reuseFailAlloc_6146_, 10, v_w_6114_);
lean_ctor_set(v_reuseFailAlloc_6146_, 11, v_W_6115_);
lean_ctor_set(v_reuseFailAlloc_6146_, 12, v_E_6116_);
lean_ctor_set(v_reuseFailAlloc_6146_, 13, v_e_6117_);
lean_ctor_set(v_reuseFailAlloc_6146_, 14, v_c_6118_);
lean_ctor_set(v_reuseFailAlloc_6146_, 15, v_F_6119_);
lean_ctor_set(v_reuseFailAlloc_6146_, 16, v_a_6120_);
lean_ctor_set(v_reuseFailAlloc_6146_, 17, v_b_6121_);
lean_ctor_set(v_reuseFailAlloc_6146_, 18, v_B_6122_);
lean_ctor_set(v_reuseFailAlloc_6146_, 19, v_h_6123_);
lean_ctor_set(v_reuseFailAlloc_6146_, 20, v_K_6124_);
lean_ctor_set(v_reuseFailAlloc_6146_, 21, v_k_6125_);
lean_ctor_set(v_reuseFailAlloc_6146_, 22, v_H_6126_);
lean_ctor_set(v_reuseFailAlloc_6146_, 23, v_m_6127_);
lean_ctor_set(v_reuseFailAlloc_6146_, 24, v_s_6128_);
lean_ctor_set(v_reuseFailAlloc_6146_, 25, v_S_6129_);
lean_ctor_set(v_reuseFailAlloc_6146_, 26, v_A_6130_);
lean_ctor_set(v_reuseFailAlloc_6146_, 27, v_n_6131_);
lean_ctor_set(v_reuseFailAlloc_6146_, 28, v_N_6132_);
lean_ctor_set(v_reuseFailAlloc_6146_, 29, v_V_6133_);
lean_ctor_set(v_reuseFailAlloc_6146_, 30, v_z_6134_);
lean_ctor_set(v_reuseFailAlloc_6146_, 31, v___x_6143_);
lean_ctor_set(v_reuseFailAlloc_6146_, 32, v_v_6135_);
lean_ctor_set(v_reuseFailAlloc_6146_, 33, v_O_6136_);
lean_ctor_set(v_reuseFailAlloc_6146_, 34, v_X_6137_);
lean_ctor_set(v_reuseFailAlloc_6146_, 35, v_x_6138_);
lean_ctor_set(v_reuseFailAlloc_6146_, 36, v_Z_6139_);
v___x_6145_ = v_reuseFailAlloc_6146_;
goto v_reusejp_6144_;
}
v_reusejp_6144_:
{
return v___x_6145_;
}
}
}
else
{
lean_object* v_G_6149_; lean_object* v_y_6150_; lean_object* v_u_6151_; lean_object* v_Y_6152_; lean_object* v_D_6153_; lean_object* v_M_6154_; lean_object* v_L_6155_; lean_object* v_d_6156_; lean_object* v_Q_6157_; lean_object* v_q_6158_; lean_object* v_w_6159_; lean_object* v_W_6160_; lean_object* v_E_6161_; lean_object* v_e_6162_; lean_object* v_c_6163_; lean_object* v_F_6164_; lean_object* v_a_6165_; lean_object* v_b_6166_; lean_object* v_B_6167_; lean_object* v_h_6168_; lean_object* v_K_6169_; lean_object* v_k_6170_; lean_object* v_H_6171_; lean_object* v_m_6172_; lean_object* v_s_6173_; lean_object* v_S_6174_; lean_object* v_A_6175_; lean_object* v_n_6176_; lean_object* v_N_6177_; lean_object* v_V_6178_; lean_object* v_zabbrev_6179_; lean_object* v_v_6180_; lean_object* v_O_6181_; lean_object* v_X_6182_; lean_object* v_x_6183_; lean_object* v_Z_6184_; lean_object* v___x_6186_; uint8_t v_isShared_6187_; uint8_t v_isSharedCheck_6192_; 
v_G_6149_ = lean_ctor_get(v_date_4582_, 0);
v_y_6150_ = lean_ctor_get(v_date_4582_, 1);
v_u_6151_ = lean_ctor_get(v_date_4582_, 2);
v_Y_6152_ = lean_ctor_get(v_date_4582_, 3);
v_D_6153_ = lean_ctor_get(v_date_4582_, 4);
v_M_6154_ = lean_ctor_get(v_date_4582_, 5);
v_L_6155_ = lean_ctor_get(v_date_4582_, 6);
v_d_6156_ = lean_ctor_get(v_date_4582_, 7);
v_Q_6157_ = lean_ctor_get(v_date_4582_, 8);
v_q_6158_ = lean_ctor_get(v_date_4582_, 9);
v_w_6159_ = lean_ctor_get(v_date_4582_, 10);
v_W_6160_ = lean_ctor_get(v_date_4582_, 11);
v_E_6161_ = lean_ctor_get(v_date_4582_, 12);
v_e_6162_ = lean_ctor_get(v_date_4582_, 13);
v_c_6163_ = lean_ctor_get(v_date_4582_, 14);
v_F_6164_ = lean_ctor_get(v_date_4582_, 15);
v_a_6165_ = lean_ctor_get(v_date_4582_, 16);
v_b_6166_ = lean_ctor_get(v_date_4582_, 17);
v_B_6167_ = lean_ctor_get(v_date_4582_, 18);
v_h_6168_ = lean_ctor_get(v_date_4582_, 19);
v_K_6169_ = lean_ctor_get(v_date_4582_, 20);
v_k_6170_ = lean_ctor_get(v_date_4582_, 21);
v_H_6171_ = lean_ctor_get(v_date_4582_, 22);
v_m_6172_ = lean_ctor_get(v_date_4582_, 23);
v_s_6173_ = lean_ctor_get(v_date_4582_, 24);
v_S_6174_ = lean_ctor_get(v_date_4582_, 25);
v_A_6175_ = lean_ctor_get(v_date_4582_, 26);
v_n_6176_ = lean_ctor_get(v_date_4582_, 27);
v_N_6177_ = lean_ctor_get(v_date_4582_, 28);
v_V_6178_ = lean_ctor_get(v_date_4582_, 29);
v_zabbrev_6179_ = lean_ctor_get(v_date_4582_, 31);
v_v_6180_ = lean_ctor_get(v_date_4582_, 32);
v_O_6181_ = lean_ctor_get(v_date_4582_, 33);
v_X_6182_ = lean_ctor_get(v_date_4582_, 34);
v_x_6183_ = lean_ctor_get(v_date_4582_, 35);
v_Z_6184_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_6192_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_6192_ == 0)
{
lean_object* v_unused_6193_; 
v_unused_6193_ = lean_ctor_get(v_date_4582_, 30);
lean_dec(v_unused_6193_);
v___x_6186_ = v_date_4582_;
v_isShared_6187_ = v_isSharedCheck_6192_;
goto v_resetjp_6185_;
}
else
{
lean_inc(v_Z_6184_);
lean_inc(v_x_6183_);
lean_inc(v_X_6182_);
lean_inc(v_O_6181_);
lean_inc(v_v_6180_);
lean_inc(v_zabbrev_6179_);
lean_inc(v_V_6178_);
lean_inc(v_N_6177_);
lean_inc(v_n_6176_);
lean_inc(v_A_6175_);
lean_inc(v_S_6174_);
lean_inc(v_s_6173_);
lean_inc(v_m_6172_);
lean_inc(v_H_6171_);
lean_inc(v_k_6170_);
lean_inc(v_K_6169_);
lean_inc(v_h_6168_);
lean_inc(v_B_6167_);
lean_inc(v_b_6166_);
lean_inc(v_a_6165_);
lean_inc(v_F_6164_);
lean_inc(v_c_6163_);
lean_inc(v_e_6162_);
lean_inc(v_E_6161_);
lean_inc(v_W_6160_);
lean_inc(v_w_6159_);
lean_inc(v_q_6158_);
lean_inc(v_Q_6157_);
lean_inc(v_d_6156_);
lean_inc(v_L_6155_);
lean_inc(v_M_6154_);
lean_inc(v_D_6153_);
lean_inc(v_Y_6152_);
lean_inc(v_u_6151_);
lean_inc(v_y_6150_);
lean_inc(v_G_6149_);
lean_dec(v_date_4582_);
v___x_6186_ = lean_box(0);
v_isShared_6187_ = v_isSharedCheck_6192_;
goto v_resetjp_6185_;
}
v_resetjp_6185_:
{
lean_object* v___x_6188_; lean_object* v___x_6190_; 
v___x_6188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6188_, 0, v_data_4584_);
if (v_isShared_6187_ == 0)
{
lean_ctor_set(v___x_6186_, 30, v___x_6188_);
v___x_6190_ = v___x_6186_;
goto v_reusejp_6189_;
}
else
{
lean_object* v_reuseFailAlloc_6191_; 
v_reuseFailAlloc_6191_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6191_, 0, v_G_6149_);
lean_ctor_set(v_reuseFailAlloc_6191_, 1, v_y_6150_);
lean_ctor_set(v_reuseFailAlloc_6191_, 2, v_u_6151_);
lean_ctor_set(v_reuseFailAlloc_6191_, 3, v_Y_6152_);
lean_ctor_set(v_reuseFailAlloc_6191_, 4, v_D_6153_);
lean_ctor_set(v_reuseFailAlloc_6191_, 5, v_M_6154_);
lean_ctor_set(v_reuseFailAlloc_6191_, 6, v_L_6155_);
lean_ctor_set(v_reuseFailAlloc_6191_, 7, v_d_6156_);
lean_ctor_set(v_reuseFailAlloc_6191_, 8, v_Q_6157_);
lean_ctor_set(v_reuseFailAlloc_6191_, 9, v_q_6158_);
lean_ctor_set(v_reuseFailAlloc_6191_, 10, v_w_6159_);
lean_ctor_set(v_reuseFailAlloc_6191_, 11, v_W_6160_);
lean_ctor_set(v_reuseFailAlloc_6191_, 12, v_E_6161_);
lean_ctor_set(v_reuseFailAlloc_6191_, 13, v_e_6162_);
lean_ctor_set(v_reuseFailAlloc_6191_, 14, v_c_6163_);
lean_ctor_set(v_reuseFailAlloc_6191_, 15, v_F_6164_);
lean_ctor_set(v_reuseFailAlloc_6191_, 16, v_a_6165_);
lean_ctor_set(v_reuseFailAlloc_6191_, 17, v_b_6166_);
lean_ctor_set(v_reuseFailAlloc_6191_, 18, v_B_6167_);
lean_ctor_set(v_reuseFailAlloc_6191_, 19, v_h_6168_);
lean_ctor_set(v_reuseFailAlloc_6191_, 20, v_K_6169_);
lean_ctor_set(v_reuseFailAlloc_6191_, 21, v_k_6170_);
lean_ctor_set(v_reuseFailAlloc_6191_, 22, v_H_6171_);
lean_ctor_set(v_reuseFailAlloc_6191_, 23, v_m_6172_);
lean_ctor_set(v_reuseFailAlloc_6191_, 24, v_s_6173_);
lean_ctor_set(v_reuseFailAlloc_6191_, 25, v_S_6174_);
lean_ctor_set(v_reuseFailAlloc_6191_, 26, v_A_6175_);
lean_ctor_set(v_reuseFailAlloc_6191_, 27, v_n_6176_);
lean_ctor_set(v_reuseFailAlloc_6191_, 28, v_N_6177_);
lean_ctor_set(v_reuseFailAlloc_6191_, 29, v_V_6178_);
lean_ctor_set(v_reuseFailAlloc_6191_, 30, v___x_6188_);
lean_ctor_set(v_reuseFailAlloc_6191_, 31, v_zabbrev_6179_);
lean_ctor_set(v_reuseFailAlloc_6191_, 32, v_v_6180_);
lean_ctor_set(v_reuseFailAlloc_6191_, 33, v_O_6181_);
lean_ctor_set(v_reuseFailAlloc_6191_, 34, v_X_6182_);
lean_ctor_set(v_reuseFailAlloc_6191_, 35, v_x_6183_);
lean_ctor_set(v_reuseFailAlloc_6191_, 36, v_Z_6184_);
v___x_6190_ = v_reuseFailAlloc_6191_;
goto v_reusejp_6189_;
}
v_reusejp_6189_:
{
return v___x_6190_;
}
}
}
}
case 31:
{
lean_object* v_G_6194_; lean_object* v_y_6195_; lean_object* v_u_6196_; lean_object* v_Y_6197_; lean_object* v_D_6198_; lean_object* v_M_6199_; lean_object* v_L_6200_; lean_object* v_d_6201_; lean_object* v_Q_6202_; lean_object* v_q_6203_; lean_object* v_w_6204_; lean_object* v_W_6205_; lean_object* v_E_6206_; lean_object* v_e_6207_; lean_object* v_c_6208_; lean_object* v_F_6209_; lean_object* v_a_6210_; lean_object* v_b_6211_; lean_object* v_B_6212_; lean_object* v_h_6213_; lean_object* v_K_6214_; lean_object* v_k_6215_; lean_object* v_H_6216_; lean_object* v_m_6217_; lean_object* v_s_6218_; lean_object* v_S_6219_; lean_object* v_A_6220_; lean_object* v_n_6221_; lean_object* v_N_6222_; lean_object* v_V_6223_; lean_object* v_z_6224_; lean_object* v_zabbrev_6225_; lean_object* v_O_6226_; lean_object* v_X_6227_; lean_object* v_x_6228_; lean_object* v_Z_6229_; lean_object* v___x_6231_; uint8_t v_isShared_6232_; uint8_t v_isSharedCheck_6237_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_G_6194_ = lean_ctor_get(v_date_4582_, 0);
v_y_6195_ = lean_ctor_get(v_date_4582_, 1);
v_u_6196_ = lean_ctor_get(v_date_4582_, 2);
v_Y_6197_ = lean_ctor_get(v_date_4582_, 3);
v_D_6198_ = lean_ctor_get(v_date_4582_, 4);
v_M_6199_ = lean_ctor_get(v_date_4582_, 5);
v_L_6200_ = lean_ctor_get(v_date_4582_, 6);
v_d_6201_ = lean_ctor_get(v_date_4582_, 7);
v_Q_6202_ = lean_ctor_get(v_date_4582_, 8);
v_q_6203_ = lean_ctor_get(v_date_4582_, 9);
v_w_6204_ = lean_ctor_get(v_date_4582_, 10);
v_W_6205_ = lean_ctor_get(v_date_4582_, 11);
v_E_6206_ = lean_ctor_get(v_date_4582_, 12);
v_e_6207_ = lean_ctor_get(v_date_4582_, 13);
v_c_6208_ = lean_ctor_get(v_date_4582_, 14);
v_F_6209_ = lean_ctor_get(v_date_4582_, 15);
v_a_6210_ = lean_ctor_get(v_date_4582_, 16);
v_b_6211_ = lean_ctor_get(v_date_4582_, 17);
v_B_6212_ = lean_ctor_get(v_date_4582_, 18);
v_h_6213_ = lean_ctor_get(v_date_4582_, 19);
v_K_6214_ = lean_ctor_get(v_date_4582_, 20);
v_k_6215_ = lean_ctor_get(v_date_4582_, 21);
v_H_6216_ = lean_ctor_get(v_date_4582_, 22);
v_m_6217_ = lean_ctor_get(v_date_4582_, 23);
v_s_6218_ = lean_ctor_get(v_date_4582_, 24);
v_S_6219_ = lean_ctor_get(v_date_4582_, 25);
v_A_6220_ = lean_ctor_get(v_date_4582_, 26);
v_n_6221_ = lean_ctor_get(v_date_4582_, 27);
v_N_6222_ = lean_ctor_get(v_date_4582_, 28);
v_V_6223_ = lean_ctor_get(v_date_4582_, 29);
v_z_6224_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_6225_ = lean_ctor_get(v_date_4582_, 31);
v_O_6226_ = lean_ctor_get(v_date_4582_, 33);
v_X_6227_ = lean_ctor_get(v_date_4582_, 34);
v_x_6228_ = lean_ctor_get(v_date_4582_, 35);
v_Z_6229_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_6237_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_6237_ == 0)
{
lean_object* v_unused_6238_; 
v_unused_6238_ = lean_ctor_get(v_date_4582_, 32);
lean_dec(v_unused_6238_);
v___x_6231_ = v_date_4582_;
v_isShared_6232_ = v_isSharedCheck_6237_;
goto v_resetjp_6230_;
}
else
{
lean_inc(v_Z_6229_);
lean_inc(v_x_6228_);
lean_inc(v_X_6227_);
lean_inc(v_O_6226_);
lean_inc(v_zabbrev_6225_);
lean_inc(v_z_6224_);
lean_inc(v_V_6223_);
lean_inc(v_N_6222_);
lean_inc(v_n_6221_);
lean_inc(v_A_6220_);
lean_inc(v_S_6219_);
lean_inc(v_s_6218_);
lean_inc(v_m_6217_);
lean_inc(v_H_6216_);
lean_inc(v_k_6215_);
lean_inc(v_K_6214_);
lean_inc(v_h_6213_);
lean_inc(v_B_6212_);
lean_inc(v_b_6211_);
lean_inc(v_a_6210_);
lean_inc(v_F_6209_);
lean_inc(v_c_6208_);
lean_inc(v_e_6207_);
lean_inc(v_E_6206_);
lean_inc(v_W_6205_);
lean_inc(v_w_6204_);
lean_inc(v_q_6203_);
lean_inc(v_Q_6202_);
lean_inc(v_d_6201_);
lean_inc(v_L_6200_);
lean_inc(v_M_6199_);
lean_inc(v_D_6198_);
lean_inc(v_Y_6197_);
lean_inc(v_u_6196_);
lean_inc(v_y_6195_);
lean_inc(v_G_6194_);
lean_dec(v_date_4582_);
v___x_6231_ = lean_box(0);
v_isShared_6232_ = v_isSharedCheck_6237_;
goto v_resetjp_6230_;
}
v_resetjp_6230_:
{
lean_object* v___x_6233_; lean_object* v___x_6235_; 
v___x_6233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6233_, 0, v_data_4584_);
if (v_isShared_6232_ == 0)
{
lean_ctor_set(v___x_6231_, 32, v___x_6233_);
v___x_6235_ = v___x_6231_;
goto v_reusejp_6234_;
}
else
{
lean_object* v_reuseFailAlloc_6236_; 
v_reuseFailAlloc_6236_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6236_, 0, v_G_6194_);
lean_ctor_set(v_reuseFailAlloc_6236_, 1, v_y_6195_);
lean_ctor_set(v_reuseFailAlloc_6236_, 2, v_u_6196_);
lean_ctor_set(v_reuseFailAlloc_6236_, 3, v_Y_6197_);
lean_ctor_set(v_reuseFailAlloc_6236_, 4, v_D_6198_);
lean_ctor_set(v_reuseFailAlloc_6236_, 5, v_M_6199_);
lean_ctor_set(v_reuseFailAlloc_6236_, 6, v_L_6200_);
lean_ctor_set(v_reuseFailAlloc_6236_, 7, v_d_6201_);
lean_ctor_set(v_reuseFailAlloc_6236_, 8, v_Q_6202_);
lean_ctor_set(v_reuseFailAlloc_6236_, 9, v_q_6203_);
lean_ctor_set(v_reuseFailAlloc_6236_, 10, v_w_6204_);
lean_ctor_set(v_reuseFailAlloc_6236_, 11, v_W_6205_);
lean_ctor_set(v_reuseFailAlloc_6236_, 12, v_E_6206_);
lean_ctor_set(v_reuseFailAlloc_6236_, 13, v_e_6207_);
lean_ctor_set(v_reuseFailAlloc_6236_, 14, v_c_6208_);
lean_ctor_set(v_reuseFailAlloc_6236_, 15, v_F_6209_);
lean_ctor_set(v_reuseFailAlloc_6236_, 16, v_a_6210_);
lean_ctor_set(v_reuseFailAlloc_6236_, 17, v_b_6211_);
lean_ctor_set(v_reuseFailAlloc_6236_, 18, v_B_6212_);
lean_ctor_set(v_reuseFailAlloc_6236_, 19, v_h_6213_);
lean_ctor_set(v_reuseFailAlloc_6236_, 20, v_K_6214_);
lean_ctor_set(v_reuseFailAlloc_6236_, 21, v_k_6215_);
lean_ctor_set(v_reuseFailAlloc_6236_, 22, v_H_6216_);
lean_ctor_set(v_reuseFailAlloc_6236_, 23, v_m_6217_);
lean_ctor_set(v_reuseFailAlloc_6236_, 24, v_s_6218_);
lean_ctor_set(v_reuseFailAlloc_6236_, 25, v_S_6219_);
lean_ctor_set(v_reuseFailAlloc_6236_, 26, v_A_6220_);
lean_ctor_set(v_reuseFailAlloc_6236_, 27, v_n_6221_);
lean_ctor_set(v_reuseFailAlloc_6236_, 28, v_N_6222_);
lean_ctor_set(v_reuseFailAlloc_6236_, 29, v_V_6223_);
lean_ctor_set(v_reuseFailAlloc_6236_, 30, v_z_6224_);
lean_ctor_set(v_reuseFailAlloc_6236_, 31, v_zabbrev_6225_);
lean_ctor_set(v_reuseFailAlloc_6236_, 32, v___x_6233_);
lean_ctor_set(v_reuseFailAlloc_6236_, 33, v_O_6226_);
lean_ctor_set(v_reuseFailAlloc_6236_, 34, v_X_6227_);
lean_ctor_set(v_reuseFailAlloc_6236_, 35, v_x_6228_);
lean_ctor_set(v_reuseFailAlloc_6236_, 36, v_Z_6229_);
v___x_6235_ = v_reuseFailAlloc_6236_;
goto v_reusejp_6234_;
}
v_reusejp_6234_:
{
return v___x_6235_;
}
}
}
case 32:
{
lean_object* v_G_6239_; lean_object* v_y_6240_; lean_object* v_u_6241_; lean_object* v_Y_6242_; lean_object* v_D_6243_; lean_object* v_M_6244_; lean_object* v_L_6245_; lean_object* v_d_6246_; lean_object* v_Q_6247_; lean_object* v_q_6248_; lean_object* v_w_6249_; lean_object* v_W_6250_; lean_object* v_E_6251_; lean_object* v_e_6252_; lean_object* v_c_6253_; lean_object* v_F_6254_; lean_object* v_a_6255_; lean_object* v_b_6256_; lean_object* v_B_6257_; lean_object* v_h_6258_; lean_object* v_K_6259_; lean_object* v_k_6260_; lean_object* v_H_6261_; lean_object* v_m_6262_; lean_object* v_s_6263_; lean_object* v_S_6264_; lean_object* v_A_6265_; lean_object* v_n_6266_; lean_object* v_N_6267_; lean_object* v_V_6268_; lean_object* v_z_6269_; lean_object* v_zabbrev_6270_; lean_object* v_v_6271_; lean_object* v_X_6272_; lean_object* v_x_6273_; lean_object* v_Z_6274_; lean_object* v___x_6276_; uint8_t v_isShared_6277_; uint8_t v_isSharedCheck_6282_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_G_6239_ = lean_ctor_get(v_date_4582_, 0);
v_y_6240_ = lean_ctor_get(v_date_4582_, 1);
v_u_6241_ = lean_ctor_get(v_date_4582_, 2);
v_Y_6242_ = lean_ctor_get(v_date_4582_, 3);
v_D_6243_ = lean_ctor_get(v_date_4582_, 4);
v_M_6244_ = lean_ctor_get(v_date_4582_, 5);
v_L_6245_ = lean_ctor_get(v_date_4582_, 6);
v_d_6246_ = lean_ctor_get(v_date_4582_, 7);
v_Q_6247_ = lean_ctor_get(v_date_4582_, 8);
v_q_6248_ = lean_ctor_get(v_date_4582_, 9);
v_w_6249_ = lean_ctor_get(v_date_4582_, 10);
v_W_6250_ = lean_ctor_get(v_date_4582_, 11);
v_E_6251_ = lean_ctor_get(v_date_4582_, 12);
v_e_6252_ = lean_ctor_get(v_date_4582_, 13);
v_c_6253_ = lean_ctor_get(v_date_4582_, 14);
v_F_6254_ = lean_ctor_get(v_date_4582_, 15);
v_a_6255_ = lean_ctor_get(v_date_4582_, 16);
v_b_6256_ = lean_ctor_get(v_date_4582_, 17);
v_B_6257_ = lean_ctor_get(v_date_4582_, 18);
v_h_6258_ = lean_ctor_get(v_date_4582_, 19);
v_K_6259_ = lean_ctor_get(v_date_4582_, 20);
v_k_6260_ = lean_ctor_get(v_date_4582_, 21);
v_H_6261_ = lean_ctor_get(v_date_4582_, 22);
v_m_6262_ = lean_ctor_get(v_date_4582_, 23);
v_s_6263_ = lean_ctor_get(v_date_4582_, 24);
v_S_6264_ = lean_ctor_get(v_date_4582_, 25);
v_A_6265_ = lean_ctor_get(v_date_4582_, 26);
v_n_6266_ = lean_ctor_get(v_date_4582_, 27);
v_N_6267_ = lean_ctor_get(v_date_4582_, 28);
v_V_6268_ = lean_ctor_get(v_date_4582_, 29);
v_z_6269_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_6270_ = lean_ctor_get(v_date_4582_, 31);
v_v_6271_ = lean_ctor_get(v_date_4582_, 32);
v_X_6272_ = lean_ctor_get(v_date_4582_, 34);
v_x_6273_ = lean_ctor_get(v_date_4582_, 35);
v_Z_6274_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_6282_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_6282_ == 0)
{
lean_object* v_unused_6283_; 
v_unused_6283_ = lean_ctor_get(v_date_4582_, 33);
lean_dec(v_unused_6283_);
v___x_6276_ = v_date_4582_;
v_isShared_6277_ = v_isSharedCheck_6282_;
goto v_resetjp_6275_;
}
else
{
lean_inc(v_Z_6274_);
lean_inc(v_x_6273_);
lean_inc(v_X_6272_);
lean_inc(v_v_6271_);
lean_inc(v_zabbrev_6270_);
lean_inc(v_z_6269_);
lean_inc(v_V_6268_);
lean_inc(v_N_6267_);
lean_inc(v_n_6266_);
lean_inc(v_A_6265_);
lean_inc(v_S_6264_);
lean_inc(v_s_6263_);
lean_inc(v_m_6262_);
lean_inc(v_H_6261_);
lean_inc(v_k_6260_);
lean_inc(v_K_6259_);
lean_inc(v_h_6258_);
lean_inc(v_B_6257_);
lean_inc(v_b_6256_);
lean_inc(v_a_6255_);
lean_inc(v_F_6254_);
lean_inc(v_c_6253_);
lean_inc(v_e_6252_);
lean_inc(v_E_6251_);
lean_inc(v_W_6250_);
lean_inc(v_w_6249_);
lean_inc(v_q_6248_);
lean_inc(v_Q_6247_);
lean_inc(v_d_6246_);
lean_inc(v_L_6245_);
lean_inc(v_M_6244_);
lean_inc(v_D_6243_);
lean_inc(v_Y_6242_);
lean_inc(v_u_6241_);
lean_inc(v_y_6240_);
lean_inc(v_G_6239_);
lean_dec(v_date_4582_);
v___x_6276_ = lean_box(0);
v_isShared_6277_ = v_isSharedCheck_6282_;
goto v_resetjp_6275_;
}
v_resetjp_6275_:
{
lean_object* v___x_6278_; lean_object* v___x_6280_; 
v___x_6278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6278_, 0, v_data_4584_);
if (v_isShared_6277_ == 0)
{
lean_ctor_set(v___x_6276_, 33, v___x_6278_);
v___x_6280_ = v___x_6276_;
goto v_reusejp_6279_;
}
else
{
lean_object* v_reuseFailAlloc_6281_; 
v_reuseFailAlloc_6281_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6281_, 0, v_G_6239_);
lean_ctor_set(v_reuseFailAlloc_6281_, 1, v_y_6240_);
lean_ctor_set(v_reuseFailAlloc_6281_, 2, v_u_6241_);
lean_ctor_set(v_reuseFailAlloc_6281_, 3, v_Y_6242_);
lean_ctor_set(v_reuseFailAlloc_6281_, 4, v_D_6243_);
lean_ctor_set(v_reuseFailAlloc_6281_, 5, v_M_6244_);
lean_ctor_set(v_reuseFailAlloc_6281_, 6, v_L_6245_);
lean_ctor_set(v_reuseFailAlloc_6281_, 7, v_d_6246_);
lean_ctor_set(v_reuseFailAlloc_6281_, 8, v_Q_6247_);
lean_ctor_set(v_reuseFailAlloc_6281_, 9, v_q_6248_);
lean_ctor_set(v_reuseFailAlloc_6281_, 10, v_w_6249_);
lean_ctor_set(v_reuseFailAlloc_6281_, 11, v_W_6250_);
lean_ctor_set(v_reuseFailAlloc_6281_, 12, v_E_6251_);
lean_ctor_set(v_reuseFailAlloc_6281_, 13, v_e_6252_);
lean_ctor_set(v_reuseFailAlloc_6281_, 14, v_c_6253_);
lean_ctor_set(v_reuseFailAlloc_6281_, 15, v_F_6254_);
lean_ctor_set(v_reuseFailAlloc_6281_, 16, v_a_6255_);
lean_ctor_set(v_reuseFailAlloc_6281_, 17, v_b_6256_);
lean_ctor_set(v_reuseFailAlloc_6281_, 18, v_B_6257_);
lean_ctor_set(v_reuseFailAlloc_6281_, 19, v_h_6258_);
lean_ctor_set(v_reuseFailAlloc_6281_, 20, v_K_6259_);
lean_ctor_set(v_reuseFailAlloc_6281_, 21, v_k_6260_);
lean_ctor_set(v_reuseFailAlloc_6281_, 22, v_H_6261_);
lean_ctor_set(v_reuseFailAlloc_6281_, 23, v_m_6262_);
lean_ctor_set(v_reuseFailAlloc_6281_, 24, v_s_6263_);
lean_ctor_set(v_reuseFailAlloc_6281_, 25, v_S_6264_);
lean_ctor_set(v_reuseFailAlloc_6281_, 26, v_A_6265_);
lean_ctor_set(v_reuseFailAlloc_6281_, 27, v_n_6266_);
lean_ctor_set(v_reuseFailAlloc_6281_, 28, v_N_6267_);
lean_ctor_set(v_reuseFailAlloc_6281_, 29, v_V_6268_);
lean_ctor_set(v_reuseFailAlloc_6281_, 30, v_z_6269_);
lean_ctor_set(v_reuseFailAlloc_6281_, 31, v_zabbrev_6270_);
lean_ctor_set(v_reuseFailAlloc_6281_, 32, v_v_6271_);
lean_ctor_set(v_reuseFailAlloc_6281_, 33, v___x_6278_);
lean_ctor_set(v_reuseFailAlloc_6281_, 34, v_X_6272_);
lean_ctor_set(v_reuseFailAlloc_6281_, 35, v_x_6273_);
lean_ctor_set(v_reuseFailAlloc_6281_, 36, v_Z_6274_);
v___x_6280_ = v_reuseFailAlloc_6281_;
goto v_reusejp_6279_;
}
v_reusejp_6279_:
{
return v___x_6280_;
}
}
}
case 33:
{
lean_object* v_G_6284_; lean_object* v_y_6285_; lean_object* v_u_6286_; lean_object* v_Y_6287_; lean_object* v_D_6288_; lean_object* v_M_6289_; lean_object* v_L_6290_; lean_object* v_d_6291_; lean_object* v_Q_6292_; lean_object* v_q_6293_; lean_object* v_w_6294_; lean_object* v_W_6295_; lean_object* v_E_6296_; lean_object* v_e_6297_; lean_object* v_c_6298_; lean_object* v_F_6299_; lean_object* v_a_6300_; lean_object* v_b_6301_; lean_object* v_B_6302_; lean_object* v_h_6303_; lean_object* v_K_6304_; lean_object* v_k_6305_; lean_object* v_H_6306_; lean_object* v_m_6307_; lean_object* v_s_6308_; lean_object* v_S_6309_; lean_object* v_A_6310_; lean_object* v_n_6311_; lean_object* v_N_6312_; lean_object* v_V_6313_; lean_object* v_z_6314_; lean_object* v_zabbrev_6315_; lean_object* v_v_6316_; lean_object* v_O_6317_; lean_object* v_x_6318_; lean_object* v_Z_6319_; lean_object* v___x_6321_; uint8_t v_isShared_6322_; uint8_t v_isSharedCheck_6327_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_G_6284_ = lean_ctor_get(v_date_4582_, 0);
v_y_6285_ = lean_ctor_get(v_date_4582_, 1);
v_u_6286_ = lean_ctor_get(v_date_4582_, 2);
v_Y_6287_ = lean_ctor_get(v_date_4582_, 3);
v_D_6288_ = lean_ctor_get(v_date_4582_, 4);
v_M_6289_ = lean_ctor_get(v_date_4582_, 5);
v_L_6290_ = lean_ctor_get(v_date_4582_, 6);
v_d_6291_ = lean_ctor_get(v_date_4582_, 7);
v_Q_6292_ = lean_ctor_get(v_date_4582_, 8);
v_q_6293_ = lean_ctor_get(v_date_4582_, 9);
v_w_6294_ = lean_ctor_get(v_date_4582_, 10);
v_W_6295_ = lean_ctor_get(v_date_4582_, 11);
v_E_6296_ = lean_ctor_get(v_date_4582_, 12);
v_e_6297_ = lean_ctor_get(v_date_4582_, 13);
v_c_6298_ = lean_ctor_get(v_date_4582_, 14);
v_F_6299_ = lean_ctor_get(v_date_4582_, 15);
v_a_6300_ = lean_ctor_get(v_date_4582_, 16);
v_b_6301_ = lean_ctor_get(v_date_4582_, 17);
v_B_6302_ = lean_ctor_get(v_date_4582_, 18);
v_h_6303_ = lean_ctor_get(v_date_4582_, 19);
v_K_6304_ = lean_ctor_get(v_date_4582_, 20);
v_k_6305_ = lean_ctor_get(v_date_4582_, 21);
v_H_6306_ = lean_ctor_get(v_date_4582_, 22);
v_m_6307_ = lean_ctor_get(v_date_4582_, 23);
v_s_6308_ = lean_ctor_get(v_date_4582_, 24);
v_S_6309_ = lean_ctor_get(v_date_4582_, 25);
v_A_6310_ = lean_ctor_get(v_date_4582_, 26);
v_n_6311_ = lean_ctor_get(v_date_4582_, 27);
v_N_6312_ = lean_ctor_get(v_date_4582_, 28);
v_V_6313_ = lean_ctor_get(v_date_4582_, 29);
v_z_6314_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_6315_ = lean_ctor_get(v_date_4582_, 31);
v_v_6316_ = lean_ctor_get(v_date_4582_, 32);
v_O_6317_ = lean_ctor_get(v_date_4582_, 33);
v_x_6318_ = lean_ctor_get(v_date_4582_, 35);
v_Z_6319_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_6327_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_6327_ == 0)
{
lean_object* v_unused_6328_; 
v_unused_6328_ = lean_ctor_get(v_date_4582_, 34);
lean_dec(v_unused_6328_);
v___x_6321_ = v_date_4582_;
v_isShared_6322_ = v_isSharedCheck_6327_;
goto v_resetjp_6320_;
}
else
{
lean_inc(v_Z_6319_);
lean_inc(v_x_6318_);
lean_inc(v_O_6317_);
lean_inc(v_v_6316_);
lean_inc(v_zabbrev_6315_);
lean_inc(v_z_6314_);
lean_inc(v_V_6313_);
lean_inc(v_N_6312_);
lean_inc(v_n_6311_);
lean_inc(v_A_6310_);
lean_inc(v_S_6309_);
lean_inc(v_s_6308_);
lean_inc(v_m_6307_);
lean_inc(v_H_6306_);
lean_inc(v_k_6305_);
lean_inc(v_K_6304_);
lean_inc(v_h_6303_);
lean_inc(v_B_6302_);
lean_inc(v_b_6301_);
lean_inc(v_a_6300_);
lean_inc(v_F_6299_);
lean_inc(v_c_6298_);
lean_inc(v_e_6297_);
lean_inc(v_E_6296_);
lean_inc(v_W_6295_);
lean_inc(v_w_6294_);
lean_inc(v_q_6293_);
lean_inc(v_Q_6292_);
lean_inc(v_d_6291_);
lean_inc(v_L_6290_);
lean_inc(v_M_6289_);
lean_inc(v_D_6288_);
lean_inc(v_Y_6287_);
lean_inc(v_u_6286_);
lean_inc(v_y_6285_);
lean_inc(v_G_6284_);
lean_dec(v_date_4582_);
v___x_6321_ = lean_box(0);
v_isShared_6322_ = v_isSharedCheck_6327_;
goto v_resetjp_6320_;
}
v_resetjp_6320_:
{
lean_object* v___x_6323_; lean_object* v___x_6325_; 
v___x_6323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6323_, 0, v_data_4584_);
if (v_isShared_6322_ == 0)
{
lean_ctor_set(v___x_6321_, 34, v___x_6323_);
v___x_6325_ = v___x_6321_;
goto v_reusejp_6324_;
}
else
{
lean_object* v_reuseFailAlloc_6326_; 
v_reuseFailAlloc_6326_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6326_, 0, v_G_6284_);
lean_ctor_set(v_reuseFailAlloc_6326_, 1, v_y_6285_);
lean_ctor_set(v_reuseFailAlloc_6326_, 2, v_u_6286_);
lean_ctor_set(v_reuseFailAlloc_6326_, 3, v_Y_6287_);
lean_ctor_set(v_reuseFailAlloc_6326_, 4, v_D_6288_);
lean_ctor_set(v_reuseFailAlloc_6326_, 5, v_M_6289_);
lean_ctor_set(v_reuseFailAlloc_6326_, 6, v_L_6290_);
lean_ctor_set(v_reuseFailAlloc_6326_, 7, v_d_6291_);
lean_ctor_set(v_reuseFailAlloc_6326_, 8, v_Q_6292_);
lean_ctor_set(v_reuseFailAlloc_6326_, 9, v_q_6293_);
lean_ctor_set(v_reuseFailAlloc_6326_, 10, v_w_6294_);
lean_ctor_set(v_reuseFailAlloc_6326_, 11, v_W_6295_);
lean_ctor_set(v_reuseFailAlloc_6326_, 12, v_E_6296_);
lean_ctor_set(v_reuseFailAlloc_6326_, 13, v_e_6297_);
lean_ctor_set(v_reuseFailAlloc_6326_, 14, v_c_6298_);
lean_ctor_set(v_reuseFailAlloc_6326_, 15, v_F_6299_);
lean_ctor_set(v_reuseFailAlloc_6326_, 16, v_a_6300_);
lean_ctor_set(v_reuseFailAlloc_6326_, 17, v_b_6301_);
lean_ctor_set(v_reuseFailAlloc_6326_, 18, v_B_6302_);
lean_ctor_set(v_reuseFailAlloc_6326_, 19, v_h_6303_);
lean_ctor_set(v_reuseFailAlloc_6326_, 20, v_K_6304_);
lean_ctor_set(v_reuseFailAlloc_6326_, 21, v_k_6305_);
lean_ctor_set(v_reuseFailAlloc_6326_, 22, v_H_6306_);
lean_ctor_set(v_reuseFailAlloc_6326_, 23, v_m_6307_);
lean_ctor_set(v_reuseFailAlloc_6326_, 24, v_s_6308_);
lean_ctor_set(v_reuseFailAlloc_6326_, 25, v_S_6309_);
lean_ctor_set(v_reuseFailAlloc_6326_, 26, v_A_6310_);
lean_ctor_set(v_reuseFailAlloc_6326_, 27, v_n_6311_);
lean_ctor_set(v_reuseFailAlloc_6326_, 28, v_N_6312_);
lean_ctor_set(v_reuseFailAlloc_6326_, 29, v_V_6313_);
lean_ctor_set(v_reuseFailAlloc_6326_, 30, v_z_6314_);
lean_ctor_set(v_reuseFailAlloc_6326_, 31, v_zabbrev_6315_);
lean_ctor_set(v_reuseFailAlloc_6326_, 32, v_v_6316_);
lean_ctor_set(v_reuseFailAlloc_6326_, 33, v_O_6317_);
lean_ctor_set(v_reuseFailAlloc_6326_, 34, v___x_6323_);
lean_ctor_set(v_reuseFailAlloc_6326_, 35, v_x_6318_);
lean_ctor_set(v_reuseFailAlloc_6326_, 36, v_Z_6319_);
v___x_6325_ = v_reuseFailAlloc_6326_;
goto v_reusejp_6324_;
}
v_reusejp_6324_:
{
return v___x_6325_;
}
}
}
case 34:
{
lean_object* v_G_6329_; lean_object* v_y_6330_; lean_object* v_u_6331_; lean_object* v_Y_6332_; lean_object* v_D_6333_; lean_object* v_M_6334_; lean_object* v_L_6335_; lean_object* v_d_6336_; lean_object* v_Q_6337_; lean_object* v_q_6338_; lean_object* v_w_6339_; lean_object* v_W_6340_; lean_object* v_E_6341_; lean_object* v_e_6342_; lean_object* v_c_6343_; lean_object* v_F_6344_; lean_object* v_a_6345_; lean_object* v_b_6346_; lean_object* v_B_6347_; lean_object* v_h_6348_; lean_object* v_K_6349_; lean_object* v_k_6350_; lean_object* v_H_6351_; lean_object* v_m_6352_; lean_object* v_s_6353_; lean_object* v_S_6354_; lean_object* v_A_6355_; lean_object* v_n_6356_; lean_object* v_N_6357_; lean_object* v_V_6358_; lean_object* v_z_6359_; lean_object* v_zabbrev_6360_; lean_object* v_v_6361_; lean_object* v_O_6362_; lean_object* v_X_6363_; lean_object* v_Z_6364_; lean_object* v___x_6366_; uint8_t v_isShared_6367_; uint8_t v_isSharedCheck_6372_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_G_6329_ = lean_ctor_get(v_date_4582_, 0);
v_y_6330_ = lean_ctor_get(v_date_4582_, 1);
v_u_6331_ = lean_ctor_get(v_date_4582_, 2);
v_Y_6332_ = lean_ctor_get(v_date_4582_, 3);
v_D_6333_ = lean_ctor_get(v_date_4582_, 4);
v_M_6334_ = lean_ctor_get(v_date_4582_, 5);
v_L_6335_ = lean_ctor_get(v_date_4582_, 6);
v_d_6336_ = lean_ctor_get(v_date_4582_, 7);
v_Q_6337_ = lean_ctor_get(v_date_4582_, 8);
v_q_6338_ = lean_ctor_get(v_date_4582_, 9);
v_w_6339_ = lean_ctor_get(v_date_4582_, 10);
v_W_6340_ = lean_ctor_get(v_date_4582_, 11);
v_E_6341_ = lean_ctor_get(v_date_4582_, 12);
v_e_6342_ = lean_ctor_get(v_date_4582_, 13);
v_c_6343_ = lean_ctor_get(v_date_4582_, 14);
v_F_6344_ = lean_ctor_get(v_date_4582_, 15);
v_a_6345_ = lean_ctor_get(v_date_4582_, 16);
v_b_6346_ = lean_ctor_get(v_date_4582_, 17);
v_B_6347_ = lean_ctor_get(v_date_4582_, 18);
v_h_6348_ = lean_ctor_get(v_date_4582_, 19);
v_K_6349_ = lean_ctor_get(v_date_4582_, 20);
v_k_6350_ = lean_ctor_get(v_date_4582_, 21);
v_H_6351_ = lean_ctor_get(v_date_4582_, 22);
v_m_6352_ = lean_ctor_get(v_date_4582_, 23);
v_s_6353_ = lean_ctor_get(v_date_4582_, 24);
v_S_6354_ = lean_ctor_get(v_date_4582_, 25);
v_A_6355_ = lean_ctor_get(v_date_4582_, 26);
v_n_6356_ = lean_ctor_get(v_date_4582_, 27);
v_N_6357_ = lean_ctor_get(v_date_4582_, 28);
v_V_6358_ = lean_ctor_get(v_date_4582_, 29);
v_z_6359_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_6360_ = lean_ctor_get(v_date_4582_, 31);
v_v_6361_ = lean_ctor_get(v_date_4582_, 32);
v_O_6362_ = lean_ctor_get(v_date_4582_, 33);
v_X_6363_ = lean_ctor_get(v_date_4582_, 34);
v_Z_6364_ = lean_ctor_get(v_date_4582_, 36);
v_isSharedCheck_6372_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_6372_ == 0)
{
lean_object* v_unused_6373_; 
v_unused_6373_ = lean_ctor_get(v_date_4582_, 35);
lean_dec(v_unused_6373_);
v___x_6366_ = v_date_4582_;
v_isShared_6367_ = v_isSharedCheck_6372_;
goto v_resetjp_6365_;
}
else
{
lean_inc(v_Z_6364_);
lean_inc(v_X_6363_);
lean_inc(v_O_6362_);
lean_inc(v_v_6361_);
lean_inc(v_zabbrev_6360_);
lean_inc(v_z_6359_);
lean_inc(v_V_6358_);
lean_inc(v_N_6357_);
lean_inc(v_n_6356_);
lean_inc(v_A_6355_);
lean_inc(v_S_6354_);
lean_inc(v_s_6353_);
lean_inc(v_m_6352_);
lean_inc(v_H_6351_);
lean_inc(v_k_6350_);
lean_inc(v_K_6349_);
lean_inc(v_h_6348_);
lean_inc(v_B_6347_);
lean_inc(v_b_6346_);
lean_inc(v_a_6345_);
lean_inc(v_F_6344_);
lean_inc(v_c_6343_);
lean_inc(v_e_6342_);
lean_inc(v_E_6341_);
lean_inc(v_W_6340_);
lean_inc(v_w_6339_);
lean_inc(v_q_6338_);
lean_inc(v_Q_6337_);
lean_inc(v_d_6336_);
lean_inc(v_L_6335_);
lean_inc(v_M_6334_);
lean_inc(v_D_6333_);
lean_inc(v_Y_6332_);
lean_inc(v_u_6331_);
lean_inc(v_y_6330_);
lean_inc(v_G_6329_);
lean_dec(v_date_4582_);
v___x_6366_ = lean_box(0);
v_isShared_6367_ = v_isSharedCheck_6372_;
goto v_resetjp_6365_;
}
v_resetjp_6365_:
{
lean_object* v___x_6368_; lean_object* v___x_6370_; 
v___x_6368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6368_, 0, v_data_4584_);
if (v_isShared_6367_ == 0)
{
lean_ctor_set(v___x_6366_, 35, v___x_6368_);
v___x_6370_ = v___x_6366_;
goto v_reusejp_6369_;
}
else
{
lean_object* v_reuseFailAlloc_6371_; 
v_reuseFailAlloc_6371_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6371_, 0, v_G_6329_);
lean_ctor_set(v_reuseFailAlloc_6371_, 1, v_y_6330_);
lean_ctor_set(v_reuseFailAlloc_6371_, 2, v_u_6331_);
lean_ctor_set(v_reuseFailAlloc_6371_, 3, v_Y_6332_);
lean_ctor_set(v_reuseFailAlloc_6371_, 4, v_D_6333_);
lean_ctor_set(v_reuseFailAlloc_6371_, 5, v_M_6334_);
lean_ctor_set(v_reuseFailAlloc_6371_, 6, v_L_6335_);
lean_ctor_set(v_reuseFailAlloc_6371_, 7, v_d_6336_);
lean_ctor_set(v_reuseFailAlloc_6371_, 8, v_Q_6337_);
lean_ctor_set(v_reuseFailAlloc_6371_, 9, v_q_6338_);
lean_ctor_set(v_reuseFailAlloc_6371_, 10, v_w_6339_);
lean_ctor_set(v_reuseFailAlloc_6371_, 11, v_W_6340_);
lean_ctor_set(v_reuseFailAlloc_6371_, 12, v_E_6341_);
lean_ctor_set(v_reuseFailAlloc_6371_, 13, v_e_6342_);
lean_ctor_set(v_reuseFailAlloc_6371_, 14, v_c_6343_);
lean_ctor_set(v_reuseFailAlloc_6371_, 15, v_F_6344_);
lean_ctor_set(v_reuseFailAlloc_6371_, 16, v_a_6345_);
lean_ctor_set(v_reuseFailAlloc_6371_, 17, v_b_6346_);
lean_ctor_set(v_reuseFailAlloc_6371_, 18, v_B_6347_);
lean_ctor_set(v_reuseFailAlloc_6371_, 19, v_h_6348_);
lean_ctor_set(v_reuseFailAlloc_6371_, 20, v_K_6349_);
lean_ctor_set(v_reuseFailAlloc_6371_, 21, v_k_6350_);
lean_ctor_set(v_reuseFailAlloc_6371_, 22, v_H_6351_);
lean_ctor_set(v_reuseFailAlloc_6371_, 23, v_m_6352_);
lean_ctor_set(v_reuseFailAlloc_6371_, 24, v_s_6353_);
lean_ctor_set(v_reuseFailAlloc_6371_, 25, v_S_6354_);
lean_ctor_set(v_reuseFailAlloc_6371_, 26, v_A_6355_);
lean_ctor_set(v_reuseFailAlloc_6371_, 27, v_n_6356_);
lean_ctor_set(v_reuseFailAlloc_6371_, 28, v_N_6357_);
lean_ctor_set(v_reuseFailAlloc_6371_, 29, v_V_6358_);
lean_ctor_set(v_reuseFailAlloc_6371_, 30, v_z_6359_);
lean_ctor_set(v_reuseFailAlloc_6371_, 31, v_zabbrev_6360_);
lean_ctor_set(v_reuseFailAlloc_6371_, 32, v_v_6361_);
lean_ctor_set(v_reuseFailAlloc_6371_, 33, v_O_6362_);
lean_ctor_set(v_reuseFailAlloc_6371_, 34, v_X_6363_);
lean_ctor_set(v_reuseFailAlloc_6371_, 35, v___x_6368_);
lean_ctor_set(v_reuseFailAlloc_6371_, 36, v_Z_6364_);
v___x_6370_ = v_reuseFailAlloc_6371_;
goto v_reusejp_6369_;
}
v_reusejp_6369_:
{
return v___x_6370_;
}
}
}
default: 
{
lean_object* v_G_6374_; lean_object* v_y_6375_; lean_object* v_u_6376_; lean_object* v_Y_6377_; lean_object* v_D_6378_; lean_object* v_M_6379_; lean_object* v_L_6380_; lean_object* v_d_6381_; lean_object* v_Q_6382_; lean_object* v_q_6383_; lean_object* v_w_6384_; lean_object* v_W_6385_; lean_object* v_E_6386_; lean_object* v_e_6387_; lean_object* v_c_6388_; lean_object* v_F_6389_; lean_object* v_a_6390_; lean_object* v_b_6391_; lean_object* v_B_6392_; lean_object* v_h_6393_; lean_object* v_K_6394_; lean_object* v_k_6395_; lean_object* v_H_6396_; lean_object* v_m_6397_; lean_object* v_s_6398_; lean_object* v_S_6399_; lean_object* v_A_6400_; lean_object* v_n_6401_; lean_object* v_N_6402_; lean_object* v_V_6403_; lean_object* v_z_6404_; lean_object* v_zabbrev_6405_; lean_object* v_v_6406_; lean_object* v_O_6407_; lean_object* v_X_6408_; lean_object* v_x_6409_; lean_object* v___x_6411_; uint8_t v_isShared_6412_; uint8_t v_isSharedCheck_6417_; 
lean_dec_ref_known(v_modifier_4583_, 0);
v_G_6374_ = lean_ctor_get(v_date_4582_, 0);
v_y_6375_ = lean_ctor_get(v_date_4582_, 1);
v_u_6376_ = lean_ctor_get(v_date_4582_, 2);
v_Y_6377_ = lean_ctor_get(v_date_4582_, 3);
v_D_6378_ = lean_ctor_get(v_date_4582_, 4);
v_M_6379_ = lean_ctor_get(v_date_4582_, 5);
v_L_6380_ = lean_ctor_get(v_date_4582_, 6);
v_d_6381_ = lean_ctor_get(v_date_4582_, 7);
v_Q_6382_ = lean_ctor_get(v_date_4582_, 8);
v_q_6383_ = lean_ctor_get(v_date_4582_, 9);
v_w_6384_ = lean_ctor_get(v_date_4582_, 10);
v_W_6385_ = lean_ctor_get(v_date_4582_, 11);
v_E_6386_ = lean_ctor_get(v_date_4582_, 12);
v_e_6387_ = lean_ctor_get(v_date_4582_, 13);
v_c_6388_ = lean_ctor_get(v_date_4582_, 14);
v_F_6389_ = lean_ctor_get(v_date_4582_, 15);
v_a_6390_ = lean_ctor_get(v_date_4582_, 16);
v_b_6391_ = lean_ctor_get(v_date_4582_, 17);
v_B_6392_ = lean_ctor_get(v_date_4582_, 18);
v_h_6393_ = lean_ctor_get(v_date_4582_, 19);
v_K_6394_ = lean_ctor_get(v_date_4582_, 20);
v_k_6395_ = lean_ctor_get(v_date_4582_, 21);
v_H_6396_ = lean_ctor_get(v_date_4582_, 22);
v_m_6397_ = lean_ctor_get(v_date_4582_, 23);
v_s_6398_ = lean_ctor_get(v_date_4582_, 24);
v_S_6399_ = lean_ctor_get(v_date_4582_, 25);
v_A_6400_ = lean_ctor_get(v_date_4582_, 26);
v_n_6401_ = lean_ctor_get(v_date_4582_, 27);
v_N_6402_ = lean_ctor_get(v_date_4582_, 28);
v_V_6403_ = lean_ctor_get(v_date_4582_, 29);
v_z_6404_ = lean_ctor_get(v_date_4582_, 30);
v_zabbrev_6405_ = lean_ctor_get(v_date_4582_, 31);
v_v_6406_ = lean_ctor_get(v_date_4582_, 32);
v_O_6407_ = lean_ctor_get(v_date_4582_, 33);
v_X_6408_ = lean_ctor_get(v_date_4582_, 34);
v_x_6409_ = lean_ctor_get(v_date_4582_, 35);
v_isSharedCheck_6417_ = !lean_is_exclusive(v_date_4582_);
if (v_isSharedCheck_6417_ == 0)
{
lean_object* v_unused_6418_; 
v_unused_6418_ = lean_ctor_get(v_date_4582_, 36);
lean_dec(v_unused_6418_);
v___x_6411_ = v_date_4582_;
v_isShared_6412_ = v_isSharedCheck_6417_;
goto v_resetjp_6410_;
}
else
{
lean_inc(v_x_6409_);
lean_inc(v_X_6408_);
lean_inc(v_O_6407_);
lean_inc(v_v_6406_);
lean_inc(v_zabbrev_6405_);
lean_inc(v_z_6404_);
lean_inc(v_V_6403_);
lean_inc(v_N_6402_);
lean_inc(v_n_6401_);
lean_inc(v_A_6400_);
lean_inc(v_S_6399_);
lean_inc(v_s_6398_);
lean_inc(v_m_6397_);
lean_inc(v_H_6396_);
lean_inc(v_k_6395_);
lean_inc(v_K_6394_);
lean_inc(v_h_6393_);
lean_inc(v_B_6392_);
lean_inc(v_b_6391_);
lean_inc(v_a_6390_);
lean_inc(v_F_6389_);
lean_inc(v_c_6388_);
lean_inc(v_e_6387_);
lean_inc(v_E_6386_);
lean_inc(v_W_6385_);
lean_inc(v_w_6384_);
lean_inc(v_q_6383_);
lean_inc(v_Q_6382_);
lean_inc(v_d_6381_);
lean_inc(v_L_6380_);
lean_inc(v_M_6379_);
lean_inc(v_D_6378_);
lean_inc(v_Y_6377_);
lean_inc(v_u_6376_);
lean_inc(v_y_6375_);
lean_inc(v_G_6374_);
lean_dec(v_date_4582_);
v___x_6411_ = lean_box(0);
v_isShared_6412_ = v_isSharedCheck_6417_;
goto v_resetjp_6410_;
}
v_resetjp_6410_:
{
lean_object* v___x_6413_; lean_object* v___x_6415_; 
v___x_6413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6413_, 0, v_data_4584_);
if (v_isShared_6412_ == 0)
{
lean_ctor_set(v___x_6411_, 36, v___x_6413_);
v___x_6415_ = v___x_6411_;
goto v_reusejp_6414_;
}
else
{
lean_object* v_reuseFailAlloc_6416_; 
v_reuseFailAlloc_6416_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6416_, 0, v_G_6374_);
lean_ctor_set(v_reuseFailAlloc_6416_, 1, v_y_6375_);
lean_ctor_set(v_reuseFailAlloc_6416_, 2, v_u_6376_);
lean_ctor_set(v_reuseFailAlloc_6416_, 3, v_Y_6377_);
lean_ctor_set(v_reuseFailAlloc_6416_, 4, v_D_6378_);
lean_ctor_set(v_reuseFailAlloc_6416_, 5, v_M_6379_);
lean_ctor_set(v_reuseFailAlloc_6416_, 6, v_L_6380_);
lean_ctor_set(v_reuseFailAlloc_6416_, 7, v_d_6381_);
lean_ctor_set(v_reuseFailAlloc_6416_, 8, v_Q_6382_);
lean_ctor_set(v_reuseFailAlloc_6416_, 9, v_q_6383_);
lean_ctor_set(v_reuseFailAlloc_6416_, 10, v_w_6384_);
lean_ctor_set(v_reuseFailAlloc_6416_, 11, v_W_6385_);
lean_ctor_set(v_reuseFailAlloc_6416_, 12, v_E_6386_);
lean_ctor_set(v_reuseFailAlloc_6416_, 13, v_e_6387_);
lean_ctor_set(v_reuseFailAlloc_6416_, 14, v_c_6388_);
lean_ctor_set(v_reuseFailAlloc_6416_, 15, v_F_6389_);
lean_ctor_set(v_reuseFailAlloc_6416_, 16, v_a_6390_);
lean_ctor_set(v_reuseFailAlloc_6416_, 17, v_b_6391_);
lean_ctor_set(v_reuseFailAlloc_6416_, 18, v_B_6392_);
lean_ctor_set(v_reuseFailAlloc_6416_, 19, v_h_6393_);
lean_ctor_set(v_reuseFailAlloc_6416_, 20, v_K_6394_);
lean_ctor_set(v_reuseFailAlloc_6416_, 21, v_k_6395_);
lean_ctor_set(v_reuseFailAlloc_6416_, 22, v_H_6396_);
lean_ctor_set(v_reuseFailAlloc_6416_, 23, v_m_6397_);
lean_ctor_set(v_reuseFailAlloc_6416_, 24, v_s_6398_);
lean_ctor_set(v_reuseFailAlloc_6416_, 25, v_S_6399_);
lean_ctor_set(v_reuseFailAlloc_6416_, 26, v_A_6400_);
lean_ctor_set(v_reuseFailAlloc_6416_, 27, v_n_6401_);
lean_ctor_set(v_reuseFailAlloc_6416_, 28, v_N_6402_);
lean_ctor_set(v_reuseFailAlloc_6416_, 29, v_V_6403_);
lean_ctor_set(v_reuseFailAlloc_6416_, 30, v_z_6404_);
lean_ctor_set(v_reuseFailAlloc_6416_, 31, v_zabbrev_6405_);
lean_ctor_set(v_reuseFailAlloc_6416_, 32, v_v_6406_);
lean_ctor_set(v_reuseFailAlloc_6416_, 33, v_O_6407_);
lean_ctor_set(v_reuseFailAlloc_6416_, 34, v_X_6408_);
lean_ctor_set(v_reuseFailAlloc_6416_, 35, v_x_6409_);
lean_ctor_set(v_reuseFailAlloc_6416_, 36, v___x_6413_);
v___x_6415_ = v_reuseFailAlloc_6416_;
goto v_reusejp_6414_;
}
v_reusejp_6414_:
{
return v___x_6415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object* v_year_6419_, uint8_t v_x_6420_){
_start:
{
if (v_x_6420_ == 0)
{
lean_object* v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; 
v___x_6421_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6422_ = lean_int_add(v_year_6419_, v___x_6421_);
v___x_6423_ = lean_int_neg(v___x_6422_);
lean_dec(v___x_6422_);
return v___x_6423_;
}
else
{
lean_inc(v_year_6419_);
return v_year_6419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object* v_year_6424_, lean_object* v_x_6425_){
_start:
{
uint8_t v_x_42__boxed_6426_; lean_object* v_res_6427_; 
v_x_42__boxed_6426_ = lean_unbox(v_x_6425_);
v_res_6427_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6424_, v_x_42__boxed_6426_);
lean_dec(v_year_6424_);
return v_res_6427_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t v_x_6428_){
_start:
{
switch(v_x_6428_)
{
case 1:
{
uint8_t v___x_6429_; 
v___x_6429_ = 1;
return v___x_6429_;
}
case 2:
{
uint8_t v___x_6430_; 
v___x_6430_ = 1;
return v___x_6430_;
}
default: 
{
uint8_t v___x_6431_; 
v___x_6431_ = 0;
return v___x_6431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object* v_x_6432_){
_start:
{
uint8_t v_x_28__boxed_6433_; uint8_t v_res_6434_; lean_object* v_r_6435_; 
v_x_28__boxed_6433_ = lean_unbox(v_x_6432_);
v_res_6434_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_28__boxed_6433_);
v_r_6435_ = lean_box(v_res_6434_);
return v_r_6435_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(uint8_t v_x_6436_){
_start:
{
switch(v_x_6436_)
{
case 3:
{
uint8_t v___x_6437_; 
v___x_6437_ = 1;
return v___x_6437_;
}
case 4:
{
uint8_t v___x_6438_; 
v___x_6438_ = 1;
return v___x_6438_;
}
case 5:
{
uint8_t v___x_6439_; 
v___x_6439_ = 1;
return v___x_6439_;
}
default: 
{
uint8_t v___x_6440_; 
v___x_6440_ = 0;
return v___x_6440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object* v_x_6441_){
_start:
{
uint8_t v_x_38__boxed_6442_; uint8_t v_res_6443_; lean_object* v_r_6444_; 
v_x_38__boxed_6442_ = lean_unbox(v_x_6441_);
v_res_6443_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_x_38__boxed_6442_);
v_r_6444_ = lean_box(v_res_6443_);
return v_r_6444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object* v_val_6445_, lean_object* v_x_6446_){
_start:
{
lean_inc_ref(v_val_6445_);
return v_val_6445_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object* v_val_6447_, lean_object* v_x_6448_){
_start:
{
lean_object* v_res_6449_; 
v_res_6449_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v_val_6447_, v_x_6448_);
lean_dec_ref(v_val_6447_);
return v_res_6449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object* v___y_6450_, lean_object* v_00___6451_){
_start:
{
uint8_t v___x_6452_; lean_object* v___x_6453_; 
v___x_6452_ = 1;
v___x_6453_ = l_Std_Time_TimeZone_Offset_toIsoString(v___y_6450_, v___x_6452_);
return v___x_6453_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1(void){
_start:
{
lean_object* v___x_6456_; lean_object* v___x_6457_; 
v___x_6456_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6457_ = lean_int_neg(v___x_6456_);
return v___x_6457_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2(void){
_start:
{
lean_object* v___x_6458_; lean_object* v___x_6459_; 
v___x_6458_ = lean_unsigned_to_nat(1000000u);
v___x_6459_ = lean_nat_to_int(v___x_6458_);
return v___x_6459_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3(void){
_start:
{
lean_object* v___x_6460_; uint8_t v___x_6461_; lean_object* v___x_6462_; 
v___x_6460_ = lean_unsigned_to_nat(0u);
v___x_6461_ = 1;
v___x_6462_ = l_Std_Time_Second_instOfNatOrdinal(v___x_6461_, v___x_6460_);
return v___x_6462_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4(void){
_start:
{
lean_object* v___x_6463_; lean_object* v___x_6464_; lean_object* v___x_6465_; 
v___x_6463_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3);
v___x_6464_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6465_ = lean_int_add(v___x_6464_, v___x_6463_);
return v___x_6465_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5(void){
_start:
{
lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; 
v___x_6466_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6467_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4);
v___x_6468_ = lean_int_sub(v___x_6467_, v___x_6466_);
return v___x_6468_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6(void){
_start:
{
lean_object* v___x_6469_; lean_object* v___x_6470_; lean_object* v_range_6471_; 
v___x_6469_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6470_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v_range_6471_ = lean_int_add(v___x_6470_, v___x_6469_);
return v_range_6471_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7(void){
_start:
{
lean_object* v___x_6472_; lean_object* v___x_6473_; 
v___x_6472_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6473_ = lean_int_sub(v___x_6472_, v___x_6472_);
return v___x_6473_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8(void){
_start:
{
lean_object* v_range_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; 
v_range_6474_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6475_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7);
v___x_6476_ = lean_int_emod(v___x_6475_, v_range_6474_);
return v___x_6476_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9(void){
_start:
{
lean_object* v_range_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; 
v_range_6477_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6478_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6479_ = lean_int_add(v___x_6478_, v_range_6477_);
return v___x_6479_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10(void){
_start:
{
lean_object* v_range_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; 
v_range_6480_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6481_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9);
v___x_6482_ = lean_int_emod(v___x_6481_, v_range_6480_);
return v___x_6482_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11(void){
_start:
{
lean_object* v___x_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; 
v___x_6483_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6484_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10);
v___x_6485_ = lean_int_add(v___x_6484_, v___x_6483_);
return v___x_6485_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12(void){
_start:
{
lean_object* v___x_6486_; lean_object* v___x_6487_; 
v___x_6486_ = lean_unsigned_to_nat(30u);
v___x_6487_ = lean_nat_to_int(v___x_6486_);
return v___x_6487_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13(void){
_start:
{
lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; 
v___x_6488_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12);
v___x_6489_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6490_ = lean_int_add(v___x_6489_, v___x_6488_);
return v___x_6490_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14(void){
_start:
{
lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; 
v___x_6491_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6492_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13);
v___x_6493_ = lean_int_sub(v___x_6492_, v___x_6491_);
return v___x_6493_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15(void){
_start:
{
lean_object* v___x_6494_; lean_object* v___x_6495_; lean_object* v_range_6496_; 
v___x_6494_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6495_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14);
v_range_6496_ = lean_int_add(v___x_6495_, v___x_6494_);
return v_range_6496_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16(void){
_start:
{
lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; 
v___x_6497_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6498_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6499_ = lean_int_sub(v___x_6498_, v___x_6497_);
return v___x_6499_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17(void){
_start:
{
lean_object* v_range_6500_; lean_object* v___x_6501_; lean_object* v___x_6502_; 
v_range_6500_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6501_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6502_ = lean_int_emod(v___x_6501_, v_range_6500_);
return v___x_6502_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18(void){
_start:
{
lean_object* v_range_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; 
v_range_6503_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6504_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6505_ = lean_int_add(v___x_6504_, v_range_6503_);
return v___x_6505_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19(void){
_start:
{
lean_object* v_range_6506_; lean_object* v___x_6507_; lean_object* v___x_6508_; 
v_range_6506_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6507_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6508_ = lean_int_emod(v___x_6507_, v_range_6506_);
return v___x_6508_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20(void){
_start:
{
lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; 
v___x_6509_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6510_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19);
v___x_6511_ = lean_int_add(v___x_6510_, v___x_6509_);
return v___x_6511_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21(void){
_start:
{
lean_object* v___x_6512_; lean_object* v___x_6513_; 
v___x_6512_ = lean_unsigned_to_nat(11u);
v___x_6513_ = lean_nat_to_int(v___x_6512_);
return v___x_6513_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22(void){
_start:
{
lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; 
v___x_6514_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21);
v___x_6515_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6516_ = lean_int_add(v___x_6515_, v___x_6514_);
return v___x_6516_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23(void){
_start:
{
lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; 
v___x_6517_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6518_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22);
v___x_6519_ = lean_int_sub(v___x_6518_, v___x_6517_);
return v___x_6519_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24(void){
_start:
{
lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v_range_6522_; 
v___x_6520_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6521_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23);
v_range_6522_ = lean_int_add(v___x_6521_, v___x_6520_);
return v_range_6522_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25(void){
_start:
{
lean_object* v_range_6523_; lean_object* v___x_6524_; lean_object* v___x_6525_; 
v_range_6523_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6524_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6525_ = lean_int_emod(v___x_6524_, v_range_6523_);
return v___x_6525_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26(void){
_start:
{
lean_object* v_range_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; 
v_range_6526_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6527_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25);
v___x_6528_ = lean_int_add(v___x_6527_, v_range_6526_);
return v___x_6528_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27(void){
_start:
{
lean_object* v_range_6529_; lean_object* v___x_6530_; lean_object* v___x_6531_; 
v_range_6529_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6530_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6531_ = lean_int_emod(v___x_6530_, v_range_6529_);
return v___x_6531_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28(void){
_start:
{
lean_object* v___x_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; 
v___x_6532_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6533_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27);
v___x_6534_ = lean_int_add(v___x_6533_, v___x_6532_);
return v___x_6534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object* v_builder_6535_, lean_object* v_aw_6536_){
_start:
{
lean_object* v___y_6538_; lean_object* v___y_6539_; lean_object* v___y_6578_; lean_object* v___y_6579_; lean_object* v___y_6582_; lean_object* v___y_6583_; lean_object* v___y_6584_; lean_object* v___y_6585_; lean_object* v___y_6586_; uint8_t v___y_6587_; lean_object* v___y_6595_; uint8_t v___y_6596_; lean_object* v___y_6597_; lean_object* v___y_6598_; lean_object* v___y_6599_; lean_object* v___y_6600_; uint8_t v___y_6601_; lean_object* v___y_6603_; lean_object* v___y_6604_; lean_object* v___y_6605_; lean_object* v___y_6606_; lean_object* v___y_6607_; lean_object* v_G_6619_; lean_object* v_y_6620_; lean_object* v_u_6621_; lean_object* v_Y_6622_; lean_object* v_M_6623_; lean_object* v_L_6624_; lean_object* v_d_6625_; lean_object* v_a_6626_; lean_object* v_b_6627_; lean_object* v_B_6628_; lean_object* v_h_6629_; lean_object* v_K_6630_; lean_object* v_k_6631_; lean_object* v_H_6632_; lean_object* v_m_6633_; lean_object* v_s_6634_; lean_object* v_S_6635_; lean_object* v_A_6636_; lean_object* v_n_6637_; lean_object* v_N_6638_; lean_object* v_V_6639_; lean_object* v_z_6640_; lean_object* v_zabbrev_6641_; lean_object* v_v_6642_; lean_object* v_O_6643_; lean_object* v_X_6644_; lean_object* v_x_6645_; lean_object* v_Z_6646_; lean_object* v___y_6648_; lean_object* v___y_6649_; lean_object* v___y_6650_; lean_object* v___y_6651_; lean_object* v___y_6652_; lean_object* v___y_6653_; lean_object* v___y_6654_; lean_object* v___y_6655_; lean_object* v___y_6664_; lean_object* v___y_6665_; lean_object* v___y_6666_; lean_object* v___y_6667_; lean_object* v___y_6668_; lean_object* v___y_6669_; lean_object* v___y_6670_; lean_object* v___y_6675_; lean_object* v___y_6676_; lean_object* v___y_6677_; lean_object* v___y_6678_; lean_object* v___y_6679_; lean_object* v___y_6680_; lean_object* v___y_6684_; lean_object* v___y_6685_; lean_object* v___y_6686_; lean_object* v___y_6687_; lean_object* v___y_6688_; lean_object* v___y_6692_; lean_object* v___y_6693_; lean_object* v___y_6694_; lean_object* v___y_6695_; lean_object* v___y_6703_; lean_object* v___y_6704_; lean_object* v___y_6705_; lean_object* v___y_6706_; uint8_t v_val_6707_; lean_object* v___y_6715_; lean_object* v___y_6716_; lean_object* v___y_6717_; lean_object* v___y_6718_; lean_object* v___y_6728_; lean_object* v___y_6729_; lean_object* v___y_6730_; uint8_t v___y_6731_; lean_object* v___y_6738_; lean_object* v___y_6739_; lean_object* v___y_6740_; lean_object* v___y_6745_; lean_object* v___y_6746_; lean_object* v___y_6750_; lean_object* v___y_6751_; lean_object* v___y_6752_; lean_object* v___y_6759_; lean_object* v___y_6760_; lean_object* v___y_6761_; lean_object* v___y_6766_; 
v_G_6619_ = lean_ctor_get(v_builder_6535_, 0);
lean_inc(v_G_6619_);
v_y_6620_ = lean_ctor_get(v_builder_6535_, 1);
lean_inc(v_y_6620_);
v_u_6621_ = lean_ctor_get(v_builder_6535_, 2);
lean_inc(v_u_6621_);
v_Y_6622_ = lean_ctor_get(v_builder_6535_, 3);
lean_inc(v_Y_6622_);
v_M_6623_ = lean_ctor_get(v_builder_6535_, 5);
lean_inc(v_M_6623_);
v_L_6624_ = lean_ctor_get(v_builder_6535_, 6);
lean_inc(v_L_6624_);
v_d_6625_ = lean_ctor_get(v_builder_6535_, 7);
lean_inc(v_d_6625_);
v_a_6626_ = lean_ctor_get(v_builder_6535_, 16);
lean_inc(v_a_6626_);
v_b_6627_ = lean_ctor_get(v_builder_6535_, 17);
lean_inc(v_b_6627_);
v_B_6628_ = lean_ctor_get(v_builder_6535_, 18);
lean_inc(v_B_6628_);
v_h_6629_ = lean_ctor_get(v_builder_6535_, 19);
lean_inc(v_h_6629_);
v_K_6630_ = lean_ctor_get(v_builder_6535_, 20);
lean_inc(v_K_6630_);
v_k_6631_ = lean_ctor_get(v_builder_6535_, 21);
lean_inc(v_k_6631_);
v_H_6632_ = lean_ctor_get(v_builder_6535_, 22);
lean_inc(v_H_6632_);
v_m_6633_ = lean_ctor_get(v_builder_6535_, 23);
lean_inc(v_m_6633_);
v_s_6634_ = lean_ctor_get(v_builder_6535_, 24);
lean_inc(v_s_6634_);
v_S_6635_ = lean_ctor_get(v_builder_6535_, 25);
lean_inc(v_S_6635_);
v_A_6636_ = lean_ctor_get(v_builder_6535_, 26);
lean_inc(v_A_6636_);
v_n_6637_ = lean_ctor_get(v_builder_6535_, 27);
lean_inc(v_n_6637_);
v_N_6638_ = lean_ctor_get(v_builder_6535_, 28);
lean_inc(v_N_6638_);
v_V_6639_ = lean_ctor_get(v_builder_6535_, 29);
lean_inc(v_V_6639_);
v_z_6640_ = lean_ctor_get(v_builder_6535_, 30);
lean_inc(v_z_6640_);
v_zabbrev_6641_ = lean_ctor_get(v_builder_6535_, 31);
lean_inc(v_zabbrev_6641_);
v_v_6642_ = lean_ctor_get(v_builder_6535_, 32);
lean_inc(v_v_6642_);
v_O_6643_ = lean_ctor_get(v_builder_6535_, 33);
lean_inc(v_O_6643_);
v_X_6644_ = lean_ctor_get(v_builder_6535_, 34);
lean_inc(v_X_6644_);
v_x_6645_ = lean_ctor_get(v_builder_6535_, 35);
lean_inc(v_x_6645_);
v_Z_6646_ = lean_ctor_get(v_builder_6535_, 36);
lean_inc(v_Z_6646_);
lean_dec_ref(v_builder_6535_);
if (lean_obj_tag(v_O_6643_) == 0)
{
if (lean_obj_tag(v_X_6644_) == 0)
{
if (lean_obj_tag(v_x_6645_) == 0)
{
if (lean_obj_tag(v_Z_6646_) == 0)
{
lean_object* v___x_6773_; 
v___x_6773_ = l_Std_Time_TimeZone_Offset_zero;
v___y_6766_ = v___x_6773_;
goto v___jp_6765_;
}
else
{
lean_object* v_val_6774_; 
v_val_6774_ = lean_ctor_get(v_Z_6646_, 0);
lean_inc(v_val_6774_);
lean_dec_ref_known(v_Z_6646_, 1);
v___y_6766_ = v_val_6774_;
goto v___jp_6765_;
}
}
else
{
lean_object* v_val_6775_; 
lean_dec(v_Z_6646_);
v_val_6775_ = lean_ctor_get(v_x_6645_, 0);
lean_inc(v_val_6775_);
lean_dec_ref_known(v_x_6645_, 1);
v___y_6766_ = v_val_6775_;
goto v___jp_6765_;
}
}
else
{
lean_object* v_val_6776_; 
lean_dec(v_Z_6646_);
lean_dec(v_x_6645_);
v_val_6776_ = lean_ctor_get(v_X_6644_, 0);
lean_inc(v_val_6776_);
lean_dec_ref_known(v_X_6644_, 1);
v___y_6766_ = v_val_6776_;
goto v___jp_6765_;
}
}
else
{
lean_object* v_val_6777_; 
lean_dec(v_Z_6646_);
lean_dec(v_x_6645_);
lean_dec(v_X_6644_);
v_val_6777_ = lean_ctor_get(v_O_6643_, 0);
lean_inc(v_val_6777_);
lean_dec_ref_known(v_O_6643_, 1);
v___y_6766_ = v_val_6777_;
goto v___jp_6765_;
}
v___jp_6537_:
{
if (lean_obj_tag(v___y_6538_) == 0)
{
lean_object* v___x_6540_; 
lean_dec_ref(v___y_6539_);
v___x_6540_ = lean_box(0);
return v___x_6540_;
}
else
{
lean_object* v_val_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6576_; 
v_val_6541_ = lean_ctor_get(v___y_6538_, 0);
v_isSharedCheck_6576_ = !lean_is_exclusive(v___y_6538_);
if (v_isSharedCheck_6576_ == 0)
{
v___x_6543_ = v___y_6538_;
v_isShared_6544_ = v_isSharedCheck_6576_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_val_6541_);
lean_dec(v___y_6538_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6576_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
lean_object* v_offset_6545_; lean_object* v_name_6546_; lean_object* v_abbreviation_6547_; uint8_t v_isDST_6548_; uint8_t v___x_6549_; uint8_t v___x_6550_; lean_object* v_ltt_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v_wt_6555_; lean_object* v_ltt_6556_; lean_object* v_tz_6557_; lean_object* v_offset_6558_; lean_object* v_second_6559_; lean_object* v_nano_6560_; lean_object* v___f_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v_nanos_6567_; lean_object* v___x_6568_; lean_object* v_nanos_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; lean_object* v___x_6574_; 
v_offset_6545_ = lean_ctor_get(v___y_6539_, 0);
lean_inc(v_offset_6545_);
v_name_6546_ = lean_ctor_get(v___y_6539_, 1);
lean_inc_ref(v_name_6546_);
v_abbreviation_6547_ = lean_ctor_get(v___y_6539_, 2);
lean_inc_ref(v_abbreviation_6547_);
v_isDST_6548_ = lean_ctor_get_uint8(v___y_6539_, sizeof(void*)*3);
lean_dec_ref(v___y_6539_);
v___x_6549_ = 0;
v___x_6550_ = 1;
v_ltt_6551_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6551_, 0, v_offset_6545_);
lean_ctor_set(v_ltt_6551_, 1, v_abbreviation_6547_);
lean_ctor_set(v_ltt_6551_, 2, v_name_6546_);
lean_ctor_set_uint8(v_ltt_6551_, sizeof(void*)*3, v_isDST_6548_);
lean_ctor_set_uint8(v_ltt_6551_, sizeof(void*)*3 + 1, v___x_6549_);
lean_ctor_set_uint8(v_ltt_6551_, sizeof(void*)*3 + 2, v___x_6550_);
v___x_6552_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6553_ = lean_box(0);
v___x_6554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6554_, 0, v_ltt_6551_);
lean_ctor_set(v___x_6554_, 1, v___x_6552_);
lean_ctor_set(v___x_6554_, 2, v___x_6553_);
lean_inc(v_val_6541_);
v_wt_6555_ = l_Std_Time_PlainDateTime_toWallTime(v_val_6541_);
lean_inc_ref(v___x_6554_);
v_ltt_6556_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_6554_, v_wt_6555_);
v_tz_6557_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_6556_);
lean_dec_ref(v_ltt_6556_);
v_offset_6558_ = lean_ctor_get(v_tz_6557_, 0);
v_second_6559_ = lean_ctor_get(v_wt_6555_, 0);
lean_inc(v_second_6559_);
v_nano_6560_ = lean_ctor_get(v_wt_6555_, 1);
lean_inc(v_nano_6560_);
lean_dec_ref(v_wt_6555_);
v___f_6561_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6561_, 0, v_val_6541_);
v___x_6562_ = lean_mk_thunk(v___f_6561_);
v___x_6563_ = lean_int_neg(v_offset_6558_);
v___x_6564_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1);
v___x_6565_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6566_ = lean_int_mul(v_second_6559_, v___x_6565_);
lean_dec(v_second_6559_);
v_nanos_6567_ = lean_int_add(v___x_6566_, v_nano_6560_);
lean_dec(v_nano_6560_);
lean_dec(v___x_6566_);
v___x_6568_ = lean_int_mul(v___x_6563_, v___x_6565_);
lean_dec(v___x_6563_);
v_nanos_6569_ = lean_int_add(v___x_6568_, v___x_6564_);
lean_dec(v___x_6568_);
v___x_6570_ = lean_int_add(v_nanos_6567_, v_nanos_6569_);
lean_dec(v_nanos_6569_);
lean_dec(v_nanos_6567_);
v___x_6571_ = l_Std_Time_Duration_ofNanoseconds(v___x_6570_);
lean_dec(v___x_6570_);
v___x_6572_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6572_, 0, v___x_6562_);
lean_ctor_set(v___x_6572_, 1, v___x_6571_);
lean_ctor_set(v___x_6572_, 2, v___x_6554_);
lean_ctor_set(v___x_6572_, 3, v_tz_6557_);
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 0, v___x_6572_);
v___x_6574_ = v___x_6543_;
goto v_reusejp_6573_;
}
else
{
lean_object* v_reuseFailAlloc_6575_; 
v_reuseFailAlloc_6575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6575_, 0, v___x_6572_);
v___x_6574_ = v_reuseFailAlloc_6575_;
goto v_reusejp_6573_;
}
v_reusejp_6573_:
{
return v___x_6574_;
}
}
}
}
v___jp_6577_:
{
if (lean_obj_tag(v_aw_6536_) == 0)
{
lean_object* v_a_6580_; 
lean_dec_ref(v___y_6578_);
v_a_6580_ = lean_ctor_get(v_aw_6536_, 0);
lean_inc_ref(v_a_6580_);
lean_dec_ref_known(v_aw_6536_, 1);
v___y_6538_ = v___y_6579_;
v___y_6539_ = v_a_6580_;
goto v___jp_6537_;
}
else
{
v___y_6538_ = v___y_6579_;
v___y_6539_ = v___y_6578_;
goto v___jp_6537_;
}
}
v___jp_6581_:
{
lean_object* v___x_6588_; uint8_t v___x_6589_; 
v___x_6588_ = l_Std_Time_Month_Ordinal_days(v___y_6587_, v___y_6586_);
v___x_6589_ = lean_int_dec_le(v___y_6582_, v___x_6588_);
lean_dec(v___x_6588_);
if (v___x_6589_ == 0)
{
lean_object* v___x_6590_; 
lean_dec(v___y_6586_);
lean_dec(v___y_6585_);
lean_dec_ref(v___y_6584_);
lean_dec(v___y_6582_);
v___x_6590_ = lean_box(0);
v___y_6578_ = v___y_6583_;
v___y_6579_ = v___x_6590_;
goto v___jp_6577_;
}
else
{
lean_object* v_date_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; 
v_date_6591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_date_6591_, 0, v___y_6585_);
lean_ctor_set(v_date_6591_, 1, v___y_6586_);
lean_ctor_set(v_date_6591_, 2, v___y_6582_);
v___x_6592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6592_, 0, v_date_6591_);
lean_ctor_set(v___x_6592_, 1, v___y_6584_);
v___x_6593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6593_, 0, v___x_6592_);
v___y_6578_ = v___y_6583_;
v___y_6579_ = v___x_6593_;
goto v___jp_6577_;
}
}
v___jp_6594_:
{
if (v___y_6596_ == 0)
{
v___y_6582_ = v___y_6595_;
v___y_6583_ = v___y_6597_;
v___y_6584_ = v___y_6598_;
v___y_6585_ = v___y_6600_;
v___y_6586_ = v___y_6599_;
v___y_6587_ = v___y_6596_;
goto v___jp_6581_;
}
else
{
v___y_6582_ = v___y_6595_;
v___y_6583_ = v___y_6597_;
v___y_6584_ = v___y_6598_;
v___y_6585_ = v___y_6600_;
v___y_6586_ = v___y_6599_;
v___y_6587_ = v___y_6601_;
goto v___jp_6581_;
}
}
v___jp_6602_:
{
lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; uint8_t v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; uint8_t v___x_6614_; 
v___x_6608_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_6609_ = lean_int_mod(v___y_6606_, v___x_6608_);
v___x_6610_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6611_ = lean_int_dec_eq(v___x_6609_, v___x_6610_);
lean_dec(v___x_6609_);
v___x_6612_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6613_ = lean_int_mod(v___y_6606_, v___x_6612_);
v___x_6614_ = lean_int_dec_eq(v___x_6613_, v___x_6610_);
lean_dec(v___x_6613_);
if (v___x_6614_ == 0)
{
uint8_t v___x_6615_; 
v___x_6615_ = 1;
v___y_6595_ = v___y_6603_;
v___y_6596_ = v___x_6611_;
v___y_6597_ = v___y_6604_;
v___y_6598_ = v___y_6607_;
v___y_6599_ = v___y_6605_;
v___y_6600_ = v___y_6606_;
v___y_6601_ = v___x_6615_;
goto v___jp_6594_;
}
else
{
lean_object* v___x_6616_; lean_object* v___x_6617_; uint8_t v___x_6618_; 
v___x_6616_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_6617_ = lean_int_mod(v___y_6606_, v___x_6616_);
v___x_6618_ = lean_int_dec_eq(v___x_6617_, v___x_6610_);
lean_dec(v___x_6617_);
v___y_6595_ = v___y_6603_;
v___y_6596_ = v___x_6611_;
v___y_6597_ = v___y_6604_;
v___y_6598_ = v___y_6607_;
v___y_6599_ = v___y_6605_;
v___y_6600_ = v___y_6606_;
v___y_6601_ = v___x_6618_;
goto v___jp_6594_;
}
}
v___jp_6647_:
{
if (lean_obj_tag(v_N_6638_) == 0)
{
if (lean_obj_tag(v_A_6636_) == 0)
{
lean_object* v___x_6656_; 
v___x_6656_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6656_, 0, v___y_6649_);
lean_ctor_set(v___x_6656_, 1, v___y_6650_);
lean_ctor_set(v___x_6656_, 2, v___y_6652_);
lean_ctor_set(v___x_6656_, 3, v___y_6655_);
v___y_6603_ = v___y_6648_;
v___y_6604_ = v___y_6651_;
v___y_6605_ = v___y_6654_;
v___y_6606_ = v___y_6653_;
v___y_6607_ = v___x_6656_;
goto v___jp_6602_;
}
else
{
lean_object* v_val_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; lean_object* v___x_6660_; 
lean_dec(v___y_6655_);
lean_dec(v___y_6652_);
lean_dec(v___y_6650_);
lean_dec(v___y_6649_);
v_val_6657_ = lean_ctor_get(v_A_6636_, 0);
lean_inc(v_val_6657_);
lean_dec_ref_known(v_A_6636_, 1);
v___x_6658_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2);
v___x_6659_ = lean_int_mul(v_val_6657_, v___x_6658_);
lean_dec(v_val_6657_);
v___x_6660_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_6659_);
lean_dec(v___x_6659_);
v___y_6603_ = v___y_6648_;
v___y_6604_ = v___y_6651_;
v___y_6605_ = v___y_6654_;
v___y_6606_ = v___y_6653_;
v___y_6607_ = v___x_6660_;
goto v___jp_6602_;
}
}
else
{
lean_object* v_val_6661_; lean_object* v___x_6662_; 
lean_dec(v___y_6655_);
lean_dec(v___y_6652_);
lean_dec(v___y_6650_);
lean_dec(v___y_6649_);
lean_dec(v_A_6636_);
v_val_6661_ = lean_ctor_get(v_N_6638_, 0);
lean_inc(v_val_6661_);
lean_dec_ref_known(v_N_6638_, 1);
v___x_6662_ = l_Std_Time_PlainTime_ofNanoseconds(v_val_6661_);
lean_dec(v_val_6661_);
v___y_6603_ = v___y_6648_;
v___y_6604_ = v___y_6651_;
v___y_6605_ = v___y_6654_;
v___y_6606_ = v___y_6653_;
v___y_6607_ = v___x_6662_;
goto v___jp_6602_;
}
}
v___jp_6663_:
{
if (lean_obj_tag(v_n_6637_) == 0)
{
if (lean_obj_tag(v_S_6635_) == 0)
{
lean_object* v___x_6671_; 
v___x_6671_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6648_ = v___y_6665_;
v___y_6649_ = v___y_6664_;
v___y_6650_ = v___y_6666_;
v___y_6651_ = v___y_6667_;
v___y_6652_ = v___y_6670_;
v___y_6653_ = v___y_6669_;
v___y_6654_ = v___y_6668_;
v___y_6655_ = v___x_6671_;
goto v___jp_6647_;
}
else
{
lean_object* v_val_6672_; 
v_val_6672_ = lean_ctor_get(v_S_6635_, 0);
lean_inc(v_val_6672_);
lean_dec_ref_known(v_S_6635_, 1);
v___y_6648_ = v___y_6665_;
v___y_6649_ = v___y_6664_;
v___y_6650_ = v___y_6666_;
v___y_6651_ = v___y_6667_;
v___y_6652_ = v___y_6670_;
v___y_6653_ = v___y_6669_;
v___y_6654_ = v___y_6668_;
v___y_6655_ = v_val_6672_;
goto v___jp_6647_;
}
}
else
{
lean_object* v_val_6673_; 
lean_dec(v_S_6635_);
v_val_6673_ = lean_ctor_get(v_n_6637_, 0);
lean_inc(v_val_6673_);
lean_dec_ref_known(v_n_6637_, 1);
v___y_6648_ = v___y_6665_;
v___y_6649_ = v___y_6664_;
v___y_6650_ = v___y_6666_;
v___y_6651_ = v___y_6667_;
v___y_6652_ = v___y_6670_;
v___y_6653_ = v___y_6669_;
v___y_6654_ = v___y_6668_;
v___y_6655_ = v_val_6673_;
goto v___jp_6647_;
}
}
v___jp_6674_:
{
if (lean_obj_tag(v_s_6634_) == 0)
{
lean_object* v___x_6681_; 
v___x_6681_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3);
v___y_6664_ = v___y_6676_;
v___y_6665_ = v___y_6675_;
v___y_6666_ = v___y_6680_;
v___y_6667_ = v___y_6677_;
v___y_6668_ = v___y_6679_;
v___y_6669_ = v___y_6678_;
v___y_6670_ = v___x_6681_;
goto v___jp_6663_;
}
else
{
lean_object* v_val_6682_; 
v_val_6682_ = lean_ctor_get(v_s_6634_, 0);
lean_inc(v_val_6682_);
lean_dec_ref_known(v_s_6634_, 1);
v___y_6664_ = v___y_6676_;
v___y_6665_ = v___y_6675_;
v___y_6666_ = v___y_6680_;
v___y_6667_ = v___y_6677_;
v___y_6668_ = v___y_6679_;
v___y_6669_ = v___y_6678_;
v___y_6670_ = v_val_6682_;
goto v___jp_6663_;
}
}
v___jp_6683_:
{
if (lean_obj_tag(v_m_6633_) == 0)
{
lean_object* v___x_6689_; 
v___x_6689_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11);
v___y_6675_ = v___y_6684_;
v___y_6676_ = v___y_6688_;
v___y_6677_ = v___y_6685_;
v___y_6678_ = v___y_6687_;
v___y_6679_ = v___y_6686_;
v___y_6680_ = v___x_6689_;
goto v___jp_6674_;
}
else
{
lean_object* v_val_6690_; 
v_val_6690_ = lean_ctor_get(v_m_6633_, 0);
lean_inc(v_val_6690_);
lean_dec_ref_known(v_m_6633_, 1);
v___y_6675_ = v___y_6684_;
v___y_6676_ = v___y_6688_;
v___y_6677_ = v___y_6685_;
v___y_6678_ = v___y_6687_;
v___y_6679_ = v___y_6686_;
v___y_6680_ = v_val_6690_;
goto v___jp_6674_;
}
}
v___jp_6691_:
{
if (lean_obj_tag(v_k_6631_) == 0)
{
if (lean_obj_tag(v_H_6632_) == 0)
{
lean_object* v___x_6696_; 
v___x_6696_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6684_ = v___y_6692_;
v___y_6685_ = v___y_6693_;
v___y_6686_ = v___y_6695_;
v___y_6687_ = v___y_6694_;
v___y_6688_ = v___x_6696_;
goto v___jp_6683_;
}
else
{
lean_object* v_val_6697_; 
v_val_6697_ = lean_ctor_get(v_H_6632_, 0);
lean_inc(v_val_6697_);
lean_dec_ref_known(v_H_6632_, 1);
v___y_6684_ = v___y_6692_;
v___y_6685_ = v___y_6693_;
v___y_6686_ = v___y_6695_;
v___y_6687_ = v___y_6694_;
v___y_6688_ = v_val_6697_;
goto v___jp_6683_;
}
}
else
{
if (lean_obj_tag(v_H_6632_) == 0)
{
lean_object* v_val_6698_; lean_object* v___x_6699_; lean_object* v___x_6700_; 
v_val_6698_ = lean_ctor_get(v_k_6631_, 0);
lean_inc(v_val_6698_);
lean_dec_ref_known(v_k_6631_, 1);
v___x_6699_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_6700_ = lean_int_add(v_val_6698_, v___x_6699_);
lean_dec(v_val_6698_);
v___y_6684_ = v___y_6692_;
v___y_6685_ = v___y_6693_;
v___y_6686_ = v___y_6695_;
v___y_6687_ = v___y_6694_;
v___y_6688_ = v___x_6700_;
goto v___jp_6683_;
}
else
{
lean_object* v_val_6701_; 
lean_dec_ref_known(v_k_6631_, 1);
v_val_6701_ = lean_ctor_get(v_H_6632_, 0);
lean_inc(v_val_6701_);
lean_dec_ref_known(v_H_6632_, 1);
v___y_6684_ = v___y_6692_;
v___y_6685_ = v___y_6693_;
v___y_6686_ = v___y_6695_;
v___y_6687_ = v___y_6694_;
v___y_6688_ = v_val_6701_;
goto v___jp_6683_;
}
}
}
v___jp_6702_:
{
if (lean_obj_tag(v_h_6629_) == 0)
{
if (lean_obj_tag(v_K_6630_) == 0)
{
v___y_6692_ = v___y_6703_;
v___y_6693_ = v___y_6704_;
v___y_6694_ = v___y_6706_;
v___y_6695_ = v___y_6705_;
goto v___jp_6691_;
}
else
{
lean_object* v_val_6708_; lean_object* v___x_6709_; lean_object* v___x_6710_; lean_object* v___x_6711_; 
lean_dec(v_H_6632_);
lean_dec(v_k_6631_);
v_val_6708_ = lean_ctor_get(v_K_6630_, 0);
lean_inc(v_val_6708_);
lean_dec_ref_known(v_K_6630_, 1);
v___x_6709_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6710_ = lean_int_add(v_val_6708_, v___x_6709_);
lean_dec(v_val_6708_);
v___x_6711_ = l_Std_Time_HourMarker_toAbsolute(v_val_6707_, v___x_6710_);
lean_dec(v___x_6710_);
v___y_6684_ = v___y_6703_;
v___y_6685_ = v___y_6704_;
v___y_6686_ = v___y_6705_;
v___y_6687_ = v___y_6706_;
v___y_6688_ = v___x_6711_;
goto v___jp_6683_;
}
}
else
{
lean_object* v_val_6712_; lean_object* v___x_6713_; 
lean_dec(v_H_6632_);
lean_dec(v_k_6631_);
lean_dec(v_K_6630_);
v_val_6712_ = lean_ctor_get(v_h_6629_, 0);
lean_inc(v_val_6712_);
lean_dec_ref_known(v_h_6629_, 1);
v___x_6713_ = l_Std_Time_HourMarker_toAbsolute(v_val_6707_, v_val_6712_);
lean_dec(v_val_6712_);
v___y_6684_ = v___y_6703_;
v___y_6685_ = v___y_6704_;
v___y_6686_ = v___y_6705_;
v___y_6687_ = v___y_6706_;
v___y_6688_ = v___x_6713_;
goto v___jp_6683_;
}
}
v___jp_6714_:
{
if (lean_obj_tag(v_a_6626_) == 0)
{
if (lean_obj_tag(v_b_6627_) == 0)
{
if (lean_obj_tag(v_B_6628_) == 0)
{
lean_dec(v_K_6630_);
lean_dec(v_h_6629_);
v___y_6692_ = v___y_6715_;
v___y_6693_ = v___y_6716_;
v___y_6694_ = v___y_6718_;
v___y_6695_ = v___y_6717_;
goto v___jp_6691_;
}
else
{
lean_object* v_val_6719_; uint8_t v___x_6720_; uint8_t v___x_6721_; 
v_val_6719_ = lean_ctor_get(v_B_6628_, 0);
lean_inc(v_val_6719_);
lean_dec_ref_known(v_B_6628_, 1);
v___x_6720_ = lean_unbox(v_val_6719_);
lean_dec(v_val_6719_);
v___x_6721_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v___x_6720_);
v___y_6703_ = v___y_6715_;
v___y_6704_ = v___y_6716_;
v___y_6705_ = v___y_6717_;
v___y_6706_ = v___y_6718_;
v_val_6707_ = v___x_6721_;
goto v___jp_6702_;
}
}
else
{
lean_object* v_val_6722_; uint8_t v___x_6723_; uint8_t v___x_6724_; 
lean_dec(v_B_6628_);
v_val_6722_ = lean_ctor_get(v_b_6627_, 0);
lean_inc(v_val_6722_);
lean_dec_ref_known(v_b_6627_, 1);
v___x_6723_ = lean_unbox(v_val_6722_);
lean_dec(v_val_6722_);
v___x_6724_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v___x_6723_);
v___y_6703_ = v___y_6715_;
v___y_6704_ = v___y_6716_;
v___y_6705_ = v___y_6717_;
v___y_6706_ = v___y_6718_;
v_val_6707_ = v___x_6724_;
goto v___jp_6702_;
}
}
else
{
lean_object* v_val_6725_; uint8_t v___x_6726_; 
lean_dec(v_B_6628_);
lean_dec(v_b_6627_);
v_val_6725_ = lean_ctor_get(v_a_6626_, 0);
lean_inc(v_val_6725_);
lean_dec_ref_known(v_a_6626_, 1);
v___x_6726_ = lean_unbox(v_val_6725_);
lean_dec(v_val_6725_);
v___y_6703_ = v___y_6715_;
v___y_6704_ = v___y_6716_;
v___y_6705_ = v___y_6717_;
v___y_6706_ = v___y_6718_;
v_val_6707_ = v___x_6726_;
goto v___jp_6702_;
}
}
v___jp_6727_:
{
if (lean_obj_tag(v_u_6621_) == 0)
{
if (lean_obj_tag(v_y_6620_) == 0)
{
if (lean_obj_tag(v_Y_6622_) == 0)
{
lean_object* v___x_6732_; 
v___x_6732_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6715_ = v___y_6728_;
v___y_6716_ = v___y_6729_;
v___y_6717_ = v___y_6730_;
v___y_6718_ = v___x_6732_;
goto v___jp_6714_;
}
else
{
lean_object* v_val_6733_; 
v_val_6733_ = lean_ctor_get(v_Y_6622_, 0);
lean_inc(v_val_6733_);
lean_dec_ref_known(v_Y_6622_, 1);
v___y_6715_ = v___y_6728_;
v___y_6716_ = v___y_6729_;
v___y_6717_ = v___y_6730_;
v___y_6718_ = v_val_6733_;
goto v___jp_6714_;
}
}
else
{
lean_object* v_val_6734_; lean_object* v___x_6735_; 
lean_dec(v_Y_6622_);
v_val_6734_ = lean_ctor_get(v_y_6620_, 0);
lean_inc(v_val_6734_);
lean_dec_ref_known(v_y_6620_, 1);
v___x_6735_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6734_, v___y_6731_);
lean_dec(v_val_6734_);
v___y_6715_ = v___y_6728_;
v___y_6716_ = v___y_6729_;
v___y_6717_ = v___y_6730_;
v___y_6718_ = v___x_6735_;
goto v___jp_6714_;
}
}
else
{
lean_object* v_val_6736_; 
lean_dec(v_Y_6622_);
lean_dec(v_y_6620_);
v_val_6736_ = lean_ctor_get(v_u_6621_, 0);
lean_inc(v_val_6736_);
lean_dec_ref_known(v_u_6621_, 1);
v___y_6715_ = v___y_6728_;
v___y_6716_ = v___y_6729_;
v___y_6717_ = v___y_6730_;
v___y_6718_ = v_val_6736_;
goto v___jp_6714_;
}
}
v___jp_6737_:
{
if (lean_obj_tag(v_G_6619_) == 0)
{
uint8_t v___x_6741_; 
v___x_6741_ = 1;
v___y_6728_ = v___y_6740_;
v___y_6729_ = v___y_6738_;
v___y_6730_ = v___y_6739_;
v___y_6731_ = v___x_6741_;
goto v___jp_6727_;
}
else
{
lean_object* v_val_6742_; uint8_t v___x_6743_; 
v_val_6742_ = lean_ctor_get(v_G_6619_, 0);
lean_inc(v_val_6742_);
lean_dec_ref_known(v_G_6619_, 1);
v___x_6743_ = lean_unbox(v_val_6742_);
lean_dec(v_val_6742_);
v___y_6728_ = v___y_6740_;
v___y_6729_ = v___y_6738_;
v___y_6730_ = v___y_6739_;
v___y_6731_ = v___x_6743_;
goto v___jp_6727_;
}
}
v___jp_6744_:
{
if (lean_obj_tag(v_d_6625_) == 0)
{
lean_object* v___x_6747_; 
v___x_6747_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20);
v___y_6738_ = v___y_6745_;
v___y_6739_ = v___y_6746_;
v___y_6740_ = v___x_6747_;
goto v___jp_6737_;
}
else
{
lean_object* v_val_6748_; 
v_val_6748_ = lean_ctor_get(v_d_6625_, 0);
lean_inc(v_val_6748_);
lean_dec_ref_known(v_d_6625_, 1);
v___y_6738_ = v___y_6745_;
v___y_6739_ = v___y_6746_;
v___y_6740_ = v_val_6748_;
goto v___jp_6737_;
}
}
v___jp_6749_:
{
uint8_t v___x_6753_; lean_object* v_tz_6754_; 
v___x_6753_ = 0;
v_tz_6754_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tz_6754_, 0, v___y_6750_);
lean_ctor_set(v_tz_6754_, 1, v___y_6751_);
lean_ctor_set(v_tz_6754_, 2, v___y_6752_);
lean_ctor_set_uint8(v_tz_6754_, sizeof(void*)*3, v___x_6753_);
if (lean_obj_tag(v_M_6623_) == 0)
{
if (lean_obj_tag(v_L_6624_) == 0)
{
lean_object* v___x_6755_; 
v___x_6755_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28);
v___y_6745_ = v_tz_6754_;
v___y_6746_ = v___x_6755_;
goto v___jp_6744_;
}
else
{
lean_object* v_val_6756_; 
v_val_6756_ = lean_ctor_get(v_L_6624_, 0);
lean_inc(v_val_6756_);
lean_dec_ref_known(v_L_6624_, 1);
v___y_6745_ = v_tz_6754_;
v___y_6746_ = v_val_6756_;
goto v___jp_6744_;
}
}
else
{
lean_object* v_val_6757_; 
lean_dec(v_L_6624_);
v_val_6757_ = lean_ctor_get(v_M_6623_, 0);
lean_inc(v_val_6757_);
lean_dec_ref_known(v_M_6623_, 1);
v___y_6745_ = v_tz_6754_;
v___y_6746_ = v_val_6757_;
goto v___jp_6744_;
}
}
v___jp_6758_:
{
if (lean_obj_tag(v_zabbrev_6641_) == 0)
{
lean_object* v___x_6762_; lean_object* v___x_6763_; 
v___x_6762_ = lean_box(0);
v___x_6763_ = lean_apply_1(v___y_6759_, v___x_6762_);
v___y_6750_ = v___y_6760_;
v___y_6751_ = v___y_6761_;
v___y_6752_ = v___x_6763_;
goto v___jp_6749_;
}
else
{
lean_object* v_val_6764_; 
lean_dec_ref(v___y_6759_);
v_val_6764_ = lean_ctor_get(v_zabbrev_6641_, 0);
lean_inc(v_val_6764_);
lean_dec_ref_known(v_zabbrev_6641_, 1);
v___y_6750_ = v___y_6760_;
v___y_6751_ = v___y_6761_;
v___y_6752_ = v_val_6764_;
goto v___jp_6749_;
}
}
v___jp_6765_:
{
lean_object* v___f_6767_; 
lean_inc(v___y_6766_);
v___f_6767_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1), 2, 1);
lean_closure_set(v___f_6767_, 0, v___y_6766_);
if (lean_obj_tag(v_V_6639_) == 0)
{
if (lean_obj_tag(v_v_6642_) == 0)
{
if (lean_obj_tag(v_z_6640_) == 0)
{
lean_object* v___x_6768_; lean_object* v___x_6769_; 
v___x_6768_ = lean_box(0);
lean_inc(v___y_6766_);
v___x_6769_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(v___y_6766_, v___x_6768_);
v___y_6759_ = v___f_6767_;
v___y_6760_ = v___y_6766_;
v___y_6761_ = v___x_6769_;
goto v___jp_6758_;
}
else
{
lean_object* v_val_6770_; 
v_val_6770_ = lean_ctor_get(v_z_6640_, 0);
lean_inc(v_val_6770_);
lean_dec_ref_known(v_z_6640_, 1);
v___y_6759_ = v___f_6767_;
v___y_6760_ = v___y_6766_;
v___y_6761_ = v_val_6770_;
goto v___jp_6758_;
}
}
else
{
lean_object* v_val_6771_; 
lean_dec(v_z_6640_);
v_val_6771_ = lean_ctor_get(v_v_6642_, 0);
lean_inc(v_val_6771_);
lean_dec_ref_known(v_v_6642_, 1);
v___y_6759_ = v___f_6767_;
v___y_6760_ = v___y_6766_;
v___y_6761_ = v_val_6771_;
goto v___jp_6758_;
}
}
else
{
lean_object* v_val_6772_; 
lean_dec(v_v_6642_);
lean_dec(v_z_6640_);
v_val_6772_ = lean_ctor_get(v_V_6639_, 0);
lean_inc(v_val_6772_);
lean_dec_ref_known(v_V_6639_, 1);
v___y_6759_ = v___f_6767_;
v___y_6760_ = v___y_6766_;
v___y_6761_ = v_val_6772_;
goto v___jp_6758_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object* v_date_6778_, lean_object* v_config_6779_, lean_object* v_mod_6780_, lean_object* v_a_6781_){
_start:
{
if (lean_obj_tag(v_mod_6780_) == 0)
{
lean_object* v_val_6782_; lean_object* v___x_6783_; 
lean_dec_ref(v_config_6779_);
v_val_6782_ = lean_ctor_get(v_mod_6780_, 0);
lean_inc_ref(v_val_6782_);
lean_dec_ref_known(v_mod_6780_, 1);
v___x_6783_ = l_Std_Internal_Parsec_String_pstring(v_val_6782_, v_a_6781_);
if (lean_obj_tag(v___x_6783_) == 0)
{
lean_object* v_pos_6784_; lean_object* v___x_6786_; uint8_t v_isShared_6787_; uint8_t v_isSharedCheck_6791_; 
v_pos_6784_ = lean_ctor_get(v___x_6783_, 0);
v_isSharedCheck_6791_ = !lean_is_exclusive(v___x_6783_);
if (v_isSharedCheck_6791_ == 0)
{
lean_object* v_unused_6792_; 
v_unused_6792_ = lean_ctor_get(v___x_6783_, 1);
lean_dec(v_unused_6792_);
v___x_6786_ = v___x_6783_;
v_isShared_6787_ = v_isSharedCheck_6791_;
goto v_resetjp_6785_;
}
else
{
lean_inc(v_pos_6784_);
lean_dec(v___x_6783_);
v___x_6786_ = lean_box(0);
v_isShared_6787_ = v_isSharedCheck_6791_;
goto v_resetjp_6785_;
}
v_resetjp_6785_:
{
lean_object* v___x_6789_; 
if (v_isShared_6787_ == 0)
{
lean_ctor_set(v___x_6786_, 1, v_date_6778_);
v___x_6789_ = v___x_6786_;
goto v_reusejp_6788_;
}
else
{
lean_object* v_reuseFailAlloc_6790_; 
v_reuseFailAlloc_6790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6790_, 0, v_pos_6784_);
lean_ctor_set(v_reuseFailAlloc_6790_, 1, v_date_6778_);
v___x_6789_ = v_reuseFailAlloc_6790_;
goto v_reusejp_6788_;
}
v_reusejp_6788_:
{
return v___x_6789_;
}
}
}
else
{
lean_object* v_pos_6793_; lean_object* v_err_6794_; lean_object* v___x_6796_; uint8_t v_isShared_6797_; uint8_t v_isSharedCheck_6801_; 
lean_dec_ref(v_date_6778_);
v_pos_6793_ = lean_ctor_get(v___x_6783_, 0);
v_err_6794_ = lean_ctor_get(v___x_6783_, 1);
v_isSharedCheck_6801_ = !lean_is_exclusive(v___x_6783_);
if (v_isSharedCheck_6801_ == 0)
{
v___x_6796_ = v___x_6783_;
v_isShared_6797_ = v_isSharedCheck_6801_;
goto v_resetjp_6795_;
}
else
{
lean_inc(v_err_6794_);
lean_inc(v_pos_6793_);
lean_dec(v___x_6783_);
v___x_6796_ = lean_box(0);
v_isShared_6797_ = v_isSharedCheck_6801_;
goto v_resetjp_6795_;
}
v_resetjp_6795_:
{
lean_object* v___x_6799_; 
if (v_isShared_6797_ == 0)
{
v___x_6799_ = v___x_6796_;
goto v_reusejp_6798_;
}
else
{
lean_object* v_reuseFailAlloc_6800_; 
v_reuseFailAlloc_6800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6800_, 0, v_pos_6793_);
lean_ctor_set(v_reuseFailAlloc_6800_, 1, v_err_6794_);
v___x_6799_ = v_reuseFailAlloc_6800_;
goto v_reusejp_6798_;
}
v_reusejp_6798_:
{
return v___x_6799_;
}
}
}
}
else
{
lean_object* v_modifier_6802_; lean_object* v___x_6803_; 
v_modifier_6802_ = lean_ctor_get(v_mod_6780_, 0);
lean_inc_ref_n(v_modifier_6802_, 2);
lean_dec_ref_known(v_mod_6780_, 1);
v___x_6803_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6779_, v_modifier_6802_, v_a_6781_);
if (lean_obj_tag(v___x_6803_) == 0)
{
lean_object* v_pos_6804_; lean_object* v_res_6805_; lean_object* v___x_6807_; uint8_t v_isShared_6808_; uint8_t v_isSharedCheck_6813_; 
v_pos_6804_ = lean_ctor_get(v___x_6803_, 0);
v_res_6805_ = lean_ctor_get(v___x_6803_, 1);
v_isSharedCheck_6813_ = !lean_is_exclusive(v___x_6803_);
if (v_isSharedCheck_6813_ == 0)
{
v___x_6807_ = v___x_6803_;
v_isShared_6808_ = v_isSharedCheck_6813_;
goto v_resetjp_6806_;
}
else
{
lean_inc(v_res_6805_);
lean_inc(v_pos_6804_);
lean_dec(v___x_6803_);
v___x_6807_ = lean_box(0);
v_isShared_6808_ = v_isSharedCheck_6813_;
goto v_resetjp_6806_;
}
v_resetjp_6806_:
{
lean_object* v___x_6809_; lean_object* v___x_6811_; 
v___x_6809_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(v_date_6778_, v_modifier_6802_, v_res_6805_);
if (v_isShared_6808_ == 0)
{
lean_ctor_set(v___x_6807_, 1, v___x_6809_);
v___x_6811_ = v___x_6807_;
goto v_reusejp_6810_;
}
else
{
lean_object* v_reuseFailAlloc_6812_; 
v_reuseFailAlloc_6812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6812_, 0, v_pos_6804_);
lean_ctor_set(v_reuseFailAlloc_6812_, 1, v___x_6809_);
v___x_6811_ = v_reuseFailAlloc_6812_;
goto v_reusejp_6810_;
}
v_reusejp_6810_:
{
return v___x_6811_;
}
}
}
else
{
lean_object* v_pos_6814_; lean_object* v_err_6815_; lean_object* v___x_6817_; uint8_t v_isShared_6818_; uint8_t v_isSharedCheck_6822_; 
lean_dec_ref(v_modifier_6802_);
lean_dec_ref(v_date_6778_);
v_pos_6814_ = lean_ctor_get(v___x_6803_, 0);
v_err_6815_ = lean_ctor_get(v___x_6803_, 1);
v_isSharedCheck_6822_ = !lean_is_exclusive(v___x_6803_);
if (v_isSharedCheck_6822_ == 0)
{
v___x_6817_ = v___x_6803_;
v_isShared_6818_ = v_isSharedCheck_6822_;
goto v_resetjp_6816_;
}
else
{
lean_inc(v_err_6815_);
lean_inc(v_pos_6814_);
lean_dec(v___x_6803_);
v___x_6817_ = lean_box(0);
v_isShared_6818_ = v_isSharedCheck_6822_;
goto v_resetjp_6816_;
}
v_resetjp_6816_:
{
lean_object* v___x_6820_; 
if (v_isShared_6818_ == 0)
{
v___x_6820_ = v___x_6817_;
goto v_reusejp_6819_;
}
else
{
lean_object* v_reuseFailAlloc_6821_; 
v_reuseFailAlloc_6821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6821_, 0, v_pos_6814_);
lean_ctor_set(v_reuseFailAlloc_6821_, 1, v_err_6815_);
v___x_6820_ = v_reuseFailAlloc_6821_;
goto v_reusejp_6819_;
}
v_reusejp_6819_:
{
return v___x_6820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object* v_input_6823_, lean_object* v_config_6824_){
_start:
{
lean_object* v___x_6825_; lean_object* v___x_6826_; 
v___x_6825_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6826_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6825_, v_input_6823_);
if (lean_obj_tag(v___x_6826_) == 0)
{
lean_object* v_a_6827_; lean_object* v___x_6829_; uint8_t v_isShared_6830_; uint8_t v_isSharedCheck_6834_; 
lean_dec_ref(v_config_6824_);
v_a_6827_ = lean_ctor_get(v___x_6826_, 0);
v_isSharedCheck_6834_ = !lean_is_exclusive(v___x_6826_);
if (v_isSharedCheck_6834_ == 0)
{
v___x_6829_ = v___x_6826_;
v_isShared_6830_ = v_isSharedCheck_6834_;
goto v_resetjp_6828_;
}
else
{
lean_inc(v_a_6827_);
lean_dec(v___x_6826_);
v___x_6829_ = lean_box(0);
v_isShared_6830_ = v_isSharedCheck_6834_;
goto v_resetjp_6828_;
}
v_resetjp_6828_:
{
lean_object* v___x_6832_; 
if (v_isShared_6830_ == 0)
{
v___x_6832_ = v___x_6829_;
goto v_reusejp_6831_;
}
else
{
lean_object* v_reuseFailAlloc_6833_; 
v_reuseFailAlloc_6833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6833_, 0, v_a_6827_);
v___x_6832_ = v_reuseFailAlloc_6833_;
goto v_reusejp_6831_;
}
v_reusejp_6831_:
{
return v___x_6832_;
}
}
}
else
{
lean_object* v_a_6835_; lean_object* v___x_6837_; uint8_t v_isShared_6838_; uint8_t v_isSharedCheck_6843_; 
v_a_6835_ = lean_ctor_get(v___x_6826_, 0);
v_isSharedCheck_6843_ = !lean_is_exclusive(v___x_6826_);
if (v_isSharedCheck_6843_ == 0)
{
v___x_6837_ = v___x_6826_;
v_isShared_6838_ = v_isSharedCheck_6843_;
goto v_resetjp_6836_;
}
else
{
lean_inc(v_a_6835_);
lean_dec(v___x_6826_);
v___x_6837_ = lean_box(0);
v_isShared_6838_ = v_isSharedCheck_6843_;
goto v_resetjp_6836_;
}
v_resetjp_6836_:
{
lean_object* v___x_6839_; lean_object* v___x_6841_; 
v___x_6839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6839_, 0, v_config_6824_);
lean_ctor_set(v___x_6839_, 1, v_a_6835_);
if (v_isShared_6838_ == 0)
{
lean_ctor_set(v___x_6837_, 0, v___x_6839_);
v___x_6841_ = v___x_6837_;
goto v_reusejp_6840_;
}
else
{
lean_object* v_reuseFailAlloc_6842_; 
v_reuseFailAlloc_6842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6842_, 0, v___x_6839_);
v___x_6841_ = v_reuseFailAlloc_6842_;
goto v_reusejp_6840_;
}
v_reusejp_6840_:
{
return v___x_6841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object* v_tz_6844_, lean_object* v_input_6845_, lean_object* v_config_6846_){
_start:
{
lean_object* v___x_6847_; 
v___x_6847_ = l_Std_Time_GenericFormat_spec___redArg(v_input_6845_, v_config_6846_);
return v___x_6847_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object* v_tz_6848_, lean_object* v_input_6849_, lean_object* v_config_6850_){
_start:
{
lean_object* v_res_6851_; 
v_res_6851_ = l_Std_Time_GenericFormat_spec(v_tz_6848_, v_input_6849_, v_config_6850_);
lean_dec(v_tz_6848_);
return v_res_6851_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(lean_object* v_msg_6852_){
_start:
{
lean_object* v___x_6853_; lean_object* v___x_6854_; 
v___x_6853_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
v___x_6854_ = lean_panic_fn_borrowed(v___x_6853_, v_msg_6852_);
return v___x_6854_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object* v_tz_6855_, lean_object* v_msg_6856_){
_start:
{
lean_object* v___x_6857_; 
v___x_6857_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v_msg_6856_);
return v___x_6857_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object* v_tz_6858_, lean_object* v_msg_6859_){
_start:
{
lean_object* v_res_6860_; 
v_res_6860_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6858_, v_msg_6859_);
lean_dec(v_tz_6858_);
return v_res_6860_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object* v_tz_6863_, lean_object* v_input_6864_, lean_object* v_config_6865_){
_start:
{
lean_object* v___x_6866_; lean_object* v___x_6867_; 
v___x_6866_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6867_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6866_, v_input_6864_);
if (lean_obj_tag(v___x_6867_) == 0)
{
lean_object* v_a_6868_; lean_object* v___x_6869_; lean_object* v___x_6870_; lean_object* v___x_6871_; lean_object* v___x_6872_; lean_object* v___x_6873_; lean_object* v___x_6874_; 
lean_dec_ref(v_config_6865_);
v_a_6868_ = lean_ctor_get(v___x_6867_, 0);
lean_inc(v_a_6868_);
lean_dec_ref_known(v___x_6867_, 1);
v___x_6869_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6870_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__1));
v___x_6871_ = lean_unsigned_to_nat(1071u);
v___x_6872_ = lean_unsigned_to_nat(18u);
v___x_6873_ = l_mkPanicMessageWithDecl(v___x_6869_, v___x_6870_, v___x_6871_, v___x_6872_, v_a_6868_);
lean_dec(v_a_6868_);
v___x_6874_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v___x_6873_);
return v___x_6874_;
}
else
{
lean_object* v_a_6875_; lean_object* v___x_6876_; 
v_a_6875_ = lean_ctor_get(v___x_6867_, 0);
lean_inc(v_a_6875_);
lean_dec_ref_known(v___x_6867_, 1);
v___x_6876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6876_, 0, v_config_6865_);
lean_ctor_set(v___x_6876_, 1, v_a_6875_);
return v___x_6876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object* v_tz_6877_, lean_object* v_input_6878_, lean_object* v_config_6879_){
_start:
{
lean_object* v_res_6880_; 
v_res_6880_ = l_Std_Time_GenericFormat_spec_x21(v_tz_6877_, v_input_6878_, v_config_6879_);
lean_dec(v_tz_6877_);
return v_res_6880_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(lean_object* v_x_6881_, lean_object* v_x_6882_){
_start:
{
if (lean_obj_tag(v_x_6882_) == 0)
{
return v_x_6881_;
}
else
{
lean_object* v_head_6883_; lean_object* v_tail_6884_; lean_object* v___x_6885_; 
v_head_6883_ = lean_ctor_get(v_x_6882_, 0);
v_tail_6884_ = lean_ctor_get(v_x_6882_, 1);
v___x_6885_ = lean_string_append(v_x_6881_, v_head_6883_);
v_x_6881_ = v___x_6885_;
v_x_6882_ = v_tail_6884_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1___boxed(lean_object* v_x_6887_, lean_object* v_x_6888_){
_start:
{
lean_object* v_res_6889_; 
v_res_6889_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v_x_6887_, v_x_6888_);
lean_dec(v_x_6888_);
return v_res_6889_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(lean_object* v_tz_6890_, lean_object* v_timestamp_6891_, lean_object* v___x_6892_, lean_object* v_x_6893_){
_start:
{
lean_object* v_offset_6894_; lean_object* v_second_6895_; lean_object* v_nano_6896_; lean_object* v___x_6897_; lean_object* v___x_6898_; lean_object* v___x_6899_; lean_object* v_nanos_6900_; lean_object* v___x_6901_; lean_object* v_nanos_6902_; lean_object* v___x_6903_; lean_object* v___x_6904_; lean_object* v___x_6905_; 
v_offset_6894_ = lean_ctor_get(v_tz_6890_, 0);
v_second_6895_ = lean_ctor_get(v_timestamp_6891_, 0);
v_nano_6896_ = lean_ctor_get(v_timestamp_6891_, 1);
v___x_6897_ = lean_nat_to_int(v___x_6892_);
v___x_6898_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6899_ = lean_int_mul(v_second_6895_, v___x_6898_);
v_nanos_6900_ = lean_int_add(v___x_6899_, v_nano_6896_);
lean_dec(v___x_6899_);
v___x_6901_ = lean_int_mul(v_offset_6894_, v___x_6898_);
v_nanos_6902_ = lean_int_add(v___x_6901_, v___x_6897_);
lean_dec(v___x_6897_);
lean_dec(v___x_6901_);
v___x_6903_ = lean_int_add(v_nanos_6900_, v_nanos_6902_);
lean_dec(v_nanos_6902_);
lean_dec(v_nanos_6900_);
v___x_6904_ = l_Std_Time_Duration_ofNanoseconds(v___x_6903_);
lean_dec(v___x_6903_);
v___x_6905_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_6904_);
return v___x_6905_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed(lean_object* v_tz_6906_, lean_object* v_timestamp_6907_, lean_object* v___x_6908_, lean_object* v_x_6909_){
_start:
{
lean_object* v_res_6910_; 
v_res_6910_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(v_tz_6906_, v_timestamp_6907_, v___x_6908_, v_x_6909_);
lean_dec_ref(v_timestamp_6907_);
lean_dec_ref(v_tz_6906_);
return v_res_6910_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(lean_object* v_aw_6911_, lean_object* v_date_6912_, lean_object* v_dateformat_6913_, lean_object* v_a_6914_, lean_object* v_a_6915_){
_start:
{
if (lean_obj_tag(v_a_6914_) == 0)
{
lean_object* v___x_6916_; 
lean_dec_ref(v_date_6912_);
v___x_6916_ = l_List_reverse___redArg(v_a_6915_);
return v___x_6916_;
}
else
{
lean_object* v_head_6917_; lean_object* v_tail_6918_; lean_object* v___x_6920_; uint8_t v_isShared_6921_; uint8_t v_isSharedCheck_6947_; 
v_head_6917_ = lean_ctor_get(v_a_6914_, 0);
v_tail_6918_ = lean_ctor_get(v_a_6914_, 1);
v_isSharedCheck_6947_ = !lean_is_exclusive(v_a_6914_);
if (v_isSharedCheck_6947_ == 0)
{
v___x_6920_ = v_a_6914_;
v_isShared_6921_ = v_isSharedCheck_6947_;
goto v_resetjp_6919_;
}
else
{
lean_inc(v_tail_6918_);
lean_inc(v_head_6917_);
lean_dec(v_a_6914_);
v___x_6920_ = lean_box(0);
v_isShared_6921_ = v_isSharedCheck_6947_;
goto v_resetjp_6919_;
}
v_resetjp_6919_:
{
lean_object* v___y_6923_; 
if (lean_obj_tag(v_aw_6911_) == 0)
{
lean_object* v_a_6928_; lean_object* v_offset_6929_; lean_object* v_name_6930_; lean_object* v_abbreviation_6931_; uint8_t v_isDST_6932_; lean_object* v_timestamp_6933_; uint8_t v___x_6934_; uint8_t v___x_6935_; lean_object* v_ltt_6936_; lean_object* v___x_6937_; lean_object* v___x_6938_; lean_object* v___x_6939_; lean_object* v___x_6940_; lean_object* v_tz_6941_; lean_object* v___f_6942_; lean_object* v___x_6943_; lean_object* v___x_6944_; lean_object* v___x_6945_; 
v_a_6928_ = lean_ctor_get(v_aw_6911_, 0);
v_offset_6929_ = lean_ctor_get(v_a_6928_, 0);
v_name_6930_ = lean_ctor_get(v_a_6928_, 1);
v_abbreviation_6931_ = lean_ctor_get(v_a_6928_, 2);
v_isDST_6932_ = lean_ctor_get_uint8(v_a_6928_, sizeof(void*)*3);
v_timestamp_6933_ = lean_ctor_get(v_date_6912_, 1);
v___x_6934_ = 0;
v___x_6935_ = 1;
lean_inc_ref(v_name_6930_);
lean_inc_ref(v_abbreviation_6931_);
lean_inc(v_offset_6929_);
v_ltt_6936_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6936_, 0, v_offset_6929_);
lean_ctor_set(v_ltt_6936_, 1, v_abbreviation_6931_);
lean_ctor_set(v_ltt_6936_, 2, v_name_6930_);
lean_ctor_set_uint8(v_ltt_6936_, sizeof(void*)*3, v_isDST_6932_);
lean_ctor_set_uint8(v_ltt_6936_, sizeof(void*)*3 + 1, v___x_6934_);
lean_ctor_set_uint8(v_ltt_6936_, sizeof(void*)*3 + 2, v___x_6935_);
v___x_6937_ = lean_unsigned_to_nat(0u);
v___x_6938_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6939_ = lean_box(0);
v___x_6940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6940_, 0, v_ltt_6936_);
lean_ctor_set(v___x_6940_, 1, v___x_6938_);
lean_ctor_set(v___x_6940_, 2, v___x_6939_);
lean_inc_ref(v___x_6940_);
v_tz_6941_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_6940_, v_timestamp_6933_);
lean_inc_ref_n(v_timestamp_6933_, 2);
lean_inc_ref(v_tz_6941_);
v___f_6942_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_6942_, 0, v_tz_6941_);
lean_closure_set(v___f_6942_, 1, v_timestamp_6933_);
lean_closure_set(v___f_6942_, 2, v___x_6937_);
v___x_6943_ = lean_mk_thunk(v___f_6942_);
v___x_6944_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6944_, 0, v___x_6943_);
lean_ctor_set(v___x_6944_, 1, v_timestamp_6933_);
lean_ctor_set(v___x_6944_, 2, v___x_6940_);
lean_ctor_set(v___x_6944_, 3, v_tz_6941_);
v___x_6945_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6913_, v___x_6944_, v_head_6917_);
v___y_6923_ = v___x_6945_;
goto v___jp_6922_;
}
else
{
lean_object* v___x_6946_; 
lean_inc_ref(v_date_6912_);
v___x_6946_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6913_, v_date_6912_, v_head_6917_);
v___y_6923_ = v___x_6946_;
goto v___jp_6922_;
}
v___jp_6922_:
{
lean_object* v___x_6925_; 
if (v_isShared_6921_ == 0)
{
lean_ctor_set(v___x_6920_, 1, v_a_6915_);
lean_ctor_set(v___x_6920_, 0, v___y_6923_);
v___x_6925_ = v___x_6920_;
goto v_reusejp_6924_;
}
else
{
lean_object* v_reuseFailAlloc_6927_; 
v_reuseFailAlloc_6927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6927_, 0, v___y_6923_);
lean_ctor_set(v_reuseFailAlloc_6927_, 1, v_a_6915_);
v___x_6925_ = v_reuseFailAlloc_6927_;
goto v_reusejp_6924_;
}
v_reusejp_6924_:
{
v_a_6914_ = v_tail_6918_;
v_a_6915_ = v___x_6925_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0___boxed(lean_object* v_aw_6948_, lean_object* v_date_6949_, lean_object* v_dateformat_6950_, lean_object* v_a_6951_, lean_object* v_a_6952_){
_start:
{
lean_object* v_res_6953_; 
v_res_6953_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(v_aw_6948_, v_date_6949_, v_dateformat_6950_, v_a_6951_, v_a_6952_);
lean_dec_ref(v_dateformat_6950_);
lean_dec(v_aw_6948_);
return v_res_6953_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(lean_object* v_aw_6954_, lean_object* v_date_6955_, lean_object* v_dateformat_6956_, lean_object* v_a_6957_, lean_object* v_a_6958_){
_start:
{
if (lean_obj_tag(v_a_6957_) == 0)
{
lean_object* v___x_6959_; 
lean_dec_ref(v_date_6955_);
v___x_6959_ = l_List_reverse___redArg(v_a_6958_);
return v___x_6959_;
}
else
{
lean_object* v_head_6960_; lean_object* v_tail_6961_; lean_object* v___x_6963_; uint8_t v_isShared_6964_; uint8_t v_isSharedCheck_6990_; 
v_head_6960_ = lean_ctor_get(v_a_6957_, 0);
v_tail_6961_ = lean_ctor_get(v_a_6957_, 1);
v_isSharedCheck_6990_ = !lean_is_exclusive(v_a_6957_);
if (v_isSharedCheck_6990_ == 0)
{
v___x_6963_ = v_a_6957_;
v_isShared_6964_ = v_isSharedCheck_6990_;
goto v_resetjp_6962_;
}
else
{
lean_inc(v_tail_6961_);
lean_inc(v_head_6960_);
lean_dec(v_a_6957_);
v___x_6963_ = lean_box(0);
v_isShared_6964_ = v_isSharedCheck_6990_;
goto v_resetjp_6962_;
}
v_resetjp_6962_:
{
lean_object* v___y_6966_; 
if (lean_obj_tag(v_aw_6954_) == 0)
{
lean_object* v_a_6971_; lean_object* v_offset_6972_; lean_object* v_name_6973_; lean_object* v_abbreviation_6974_; uint8_t v_isDST_6975_; lean_object* v_timestamp_6976_; uint8_t v___x_6977_; uint8_t v___x_6978_; lean_object* v_ltt_6979_; lean_object* v___x_6980_; lean_object* v___x_6981_; lean_object* v___x_6982_; lean_object* v___x_6983_; lean_object* v_tz_6984_; lean_object* v___f_6985_; lean_object* v___x_6986_; lean_object* v___x_6987_; lean_object* v___x_6988_; 
v_a_6971_ = lean_ctor_get(v_aw_6954_, 0);
v_offset_6972_ = lean_ctor_get(v_a_6971_, 0);
v_name_6973_ = lean_ctor_get(v_a_6971_, 1);
v_abbreviation_6974_ = lean_ctor_get(v_a_6971_, 2);
v_isDST_6975_ = lean_ctor_get_uint8(v_a_6971_, sizeof(void*)*3);
v_timestamp_6976_ = lean_ctor_get(v_date_6955_, 1);
v___x_6977_ = 0;
v___x_6978_ = 1;
lean_inc_ref(v_name_6973_);
lean_inc_ref(v_abbreviation_6974_);
lean_inc(v_offset_6972_);
v_ltt_6979_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6979_, 0, v_offset_6972_);
lean_ctor_set(v_ltt_6979_, 1, v_abbreviation_6974_);
lean_ctor_set(v_ltt_6979_, 2, v_name_6973_);
lean_ctor_set_uint8(v_ltt_6979_, sizeof(void*)*3, v_isDST_6975_);
lean_ctor_set_uint8(v_ltt_6979_, sizeof(void*)*3 + 1, v___x_6977_);
lean_ctor_set_uint8(v_ltt_6979_, sizeof(void*)*3 + 2, v___x_6978_);
v___x_6980_ = lean_unsigned_to_nat(0u);
v___x_6981_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6982_ = lean_box(0);
v___x_6983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6983_, 0, v_ltt_6979_);
lean_ctor_set(v___x_6983_, 1, v___x_6981_);
lean_ctor_set(v___x_6983_, 2, v___x_6982_);
lean_inc_ref(v___x_6983_);
v_tz_6984_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_6983_, v_timestamp_6976_);
lean_inc_ref_n(v_timestamp_6976_, 2);
lean_inc_ref(v_tz_6984_);
v___f_6985_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_6985_, 0, v_tz_6984_);
lean_closure_set(v___f_6985_, 1, v_timestamp_6976_);
lean_closure_set(v___f_6985_, 2, v___x_6980_);
v___x_6986_ = lean_mk_thunk(v___f_6985_);
v___x_6987_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6987_, 0, v___x_6986_);
lean_ctor_set(v___x_6987_, 1, v_timestamp_6976_);
lean_ctor_set(v___x_6987_, 2, v___x_6983_);
lean_ctor_set(v___x_6987_, 3, v_tz_6984_);
v___x_6988_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6956_, v___x_6987_, v_head_6960_);
v___y_6966_ = v___x_6988_;
goto v___jp_6965_;
}
else
{
lean_object* v___x_6989_; 
lean_inc_ref(v_date_6955_);
v___x_6989_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6956_, v_date_6955_, v_head_6960_);
v___y_6966_ = v___x_6989_;
goto v___jp_6965_;
}
v___jp_6965_:
{
lean_object* v___x_6968_; 
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 1, v_a_6958_);
lean_ctor_set(v___x_6963_, 0, v___y_6966_);
v___x_6968_ = v___x_6963_;
goto v_reusejp_6967_;
}
else
{
lean_object* v_reuseFailAlloc_6970_; 
v_reuseFailAlloc_6970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6970_, 0, v___y_6966_);
lean_ctor_set(v_reuseFailAlloc_6970_, 1, v_a_6958_);
v___x_6968_ = v_reuseFailAlloc_6970_;
goto v_reusejp_6967_;
}
v_reusejp_6967_:
{
lean_object* v___x_6969_; 
v___x_6969_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(v_aw_6954_, v_date_6955_, v_dateformat_6956_, v_tail_6961_, v___x_6968_);
return v___x_6969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___boxed(lean_object* v_aw_6991_, lean_object* v_date_6992_, lean_object* v_dateformat_6993_, lean_object* v_a_6994_, lean_object* v_a_6995_){
_start:
{
lean_object* v_res_6996_; 
v_res_6996_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6991_, v_date_6992_, v_dateformat_6993_, v_a_6994_, v_a_6995_);
lean_dec_ref(v_dateformat_6993_);
lean_dec(v_aw_6991_);
return v_res_6996_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object* v_aw_6997_, lean_object* v_format_6998_, lean_object* v_date_6999_){
_start:
{
lean_object* v_config_7000_; lean_object* v_string_7001_; lean_object* v_dateformat_7002_; lean_object* v___x_7003_; lean_object* v___x_7004_; lean_object* v___x_7005_; lean_object* v___x_7006_; 
v_config_7000_ = lean_ctor_get(v_format_6998_, 0);
lean_inc_ref(v_config_7000_);
v_string_7001_ = lean_ctor_get(v_format_6998_, 1);
lean_inc(v_string_7001_);
lean_dec_ref(v_format_6998_);
v_dateformat_7002_ = lean_ctor_get(v_config_7000_, 0);
lean_inc_ref(v_dateformat_7002_);
lean_dec_ref(v_config_7000_);
v___x_7003_ = lean_box(0);
v___x_7004_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6997_, v_date_6999_, v_dateformat_7002_, v_string_7001_, v___x_7003_);
lean_dec_ref(v_dateformat_7002_);
v___x_7005_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7006_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v___x_7005_, v___x_7004_);
lean_dec(v___x_7004_);
return v___x_7006_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object* v_aw_7007_, lean_object* v_format_7008_, lean_object* v_date_7009_){
_start:
{
lean_object* v_res_7010_; 
v_res_7010_ = l_Std_Time_GenericFormat_format(v_aw_7007_, v_format_7008_, v_date_7009_);
lean_dec(v_aw_7007_);
return v_res_7010_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object* v_config_7014_, lean_object* v_aw_7015_, lean_object* v_builder_7016_, lean_object* v_x_7017_, lean_object* v_a_7018_){
_start:
{
if (lean_obj_tag(v_x_7017_) == 0)
{
lean_object* v___x_7019_; 
lean_dec_ref(v_config_7014_);
v___x_7019_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_7016_, v_aw_7015_);
if (lean_obj_tag(v___x_7019_) == 0)
{
lean_object* v___x_7020_; lean_object* v___x_7021_; 
v___x_7020_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1));
v___x_7021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7021_, 0, v_a_7018_);
lean_ctor_set(v___x_7021_, 1, v___x_7020_);
return v___x_7021_;
}
else
{
lean_object* v_val_7022_; lean_object* v___x_7023_; 
v_val_7022_ = lean_ctor_get(v___x_7019_, 0);
lean_inc(v_val_7022_);
lean_dec_ref_known(v___x_7019_, 1);
v___x_7023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7023_, 0, v_a_7018_);
lean_ctor_set(v___x_7023_, 1, v_val_7022_);
return v___x_7023_;
}
}
else
{
lean_object* v_head_7024_; lean_object* v_tail_7025_; lean_object* v___x_7026_; 
v_head_7024_ = lean_ctor_get(v_x_7017_, 0);
lean_inc(v_head_7024_);
v_tail_7025_ = lean_ctor_get(v_x_7017_, 1);
lean_inc(v_tail_7025_);
lean_dec_ref_known(v_x_7017_, 2);
lean_inc_ref(v_config_7014_);
v___x_7026_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(v_builder_7016_, v_config_7014_, v_head_7024_, v_a_7018_);
if (lean_obj_tag(v___x_7026_) == 0)
{
lean_object* v_pos_7027_; lean_object* v_res_7028_; 
v_pos_7027_ = lean_ctor_get(v___x_7026_, 0);
lean_inc(v_pos_7027_);
v_res_7028_ = lean_ctor_get(v___x_7026_, 1);
lean_inc(v_res_7028_);
lean_dec_ref_known(v___x_7026_, 2);
v_builder_7016_ = v_res_7028_;
v_x_7017_ = v_tail_7025_;
v_a_7018_ = v_pos_7027_;
goto _start;
}
else
{
lean_object* v_pos_7030_; lean_object* v_err_7031_; lean_object* v___x_7033_; uint8_t v_isShared_7034_; uint8_t v_isSharedCheck_7038_; 
lean_dec(v_tail_7025_);
lean_dec(v_aw_7015_);
lean_dec_ref(v_config_7014_);
v_pos_7030_ = lean_ctor_get(v___x_7026_, 0);
v_err_7031_ = lean_ctor_get(v___x_7026_, 1);
v_isSharedCheck_7038_ = !lean_is_exclusive(v___x_7026_);
if (v_isSharedCheck_7038_ == 0)
{
v___x_7033_ = v___x_7026_;
v_isShared_7034_ = v_isSharedCheck_7038_;
goto v_resetjp_7032_;
}
else
{
lean_inc(v_err_7031_);
lean_inc(v_pos_7030_);
lean_dec(v___x_7026_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object* v_format_7041_, lean_object* v_config_7042_, lean_object* v_aw_7043_, lean_object* v_a_7044_){
_start:
{
lean_object* v___x_7045_; lean_object* v___x_7046_; 
v___x_7045_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0));
v___x_7046_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(v_config_7042_, v_aw_7043_, v___x_7045_, v_format_7041_, v_a_7044_);
return v___x_7046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object* v_config_7050_, lean_object* v_format_7051_, lean_object* v_func_7052_, lean_object* v_a_7053_){
_start:
{
if (lean_obj_tag(v_format_7051_) == 0)
{
lean_dec_ref(v_config_7050_);
if (lean_obj_tag(v_func_7052_) == 0)
{
lean_object* v___x_7054_; lean_object* v___x_7055_; 
v___x_7054_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1));
v___x_7055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7055_, 0, v_a_7053_);
lean_ctor_set(v___x_7055_, 1, v___x_7054_);
return v___x_7055_;
}
else
{
lean_object* v_val_7056_; lean_object* v_fst_7057_; lean_object* v_snd_7058_; lean_object* v___x_7059_; uint8_t v_decide_7060_; 
v_val_7056_ = lean_ctor_get(v_func_7052_, 0);
lean_inc(v_val_7056_);
lean_dec_ref_known(v_func_7052_, 1);
v_fst_7057_ = lean_ctor_get(v_a_7053_, 0);
v_snd_7058_ = lean_ctor_get(v_a_7053_, 1);
v___x_7059_ = lean_string_utf8_byte_size(v_fst_7057_);
v_decide_7060_ = lean_nat_dec_eq(v_snd_7058_, v___x_7059_);
if (v_decide_7060_ == 0)
{
lean_object* v___x_7061_; lean_object* v___x_7062_; 
lean_dec(v_val_7056_);
v___x_7061_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
v___x_7062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7062_, 0, v_a_7053_);
lean_ctor_set(v___x_7062_, 1, v___x_7061_);
return v___x_7062_;
}
else
{
lean_object* v___x_7063_; 
v___x_7063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7063_, 0, v_a_7053_);
lean_ctor_set(v___x_7063_, 1, v_val_7056_);
return v___x_7063_;
}
}
}
else
{
lean_object* v_head_7064_; 
v_head_7064_ = lean_ctor_get(v_format_7051_, 0);
lean_inc(v_head_7064_);
if (lean_obj_tag(v_head_7064_) == 0)
{
lean_object* v_tail_7065_; lean_object* v_val_7066_; lean_object* v___x_7067_; 
v_tail_7065_ = lean_ctor_get(v_format_7051_, 1);
lean_inc(v_tail_7065_);
lean_dec_ref_known(v_format_7051_, 2);
v_val_7066_ = lean_ctor_get(v_head_7064_, 0);
lean_inc_ref(v_val_7066_);
lean_dec_ref_known(v_head_7064_, 1);
v___x_7067_ = l_Std_Internal_Parsec_String_pstring(v_val_7066_, v_a_7053_);
if (lean_obj_tag(v___x_7067_) == 0)
{
lean_object* v_pos_7068_; 
v_pos_7068_ = lean_ctor_get(v___x_7067_, 0);
lean_inc(v_pos_7068_);
lean_dec_ref_known(v___x_7067_, 2);
v_format_7051_ = v_tail_7065_;
v_a_7053_ = v_pos_7068_;
goto _start;
}
else
{
lean_object* v_pos_7070_; lean_object* v_err_7071_; lean_object* v___x_7073_; uint8_t v_isShared_7074_; uint8_t v_isSharedCheck_7078_; 
lean_dec(v_tail_7065_);
lean_dec(v_func_7052_);
lean_dec_ref(v_config_7050_);
v_pos_7070_ = lean_ctor_get(v___x_7067_, 0);
v_err_7071_ = lean_ctor_get(v___x_7067_, 1);
v_isSharedCheck_7078_ = !lean_is_exclusive(v___x_7067_);
if (v_isSharedCheck_7078_ == 0)
{
v___x_7073_ = v___x_7067_;
v_isShared_7074_ = v_isSharedCheck_7078_;
goto v_resetjp_7072_;
}
else
{
lean_inc(v_err_7071_);
lean_inc(v_pos_7070_);
lean_dec(v___x_7067_);
v___x_7073_ = lean_box(0);
v_isShared_7074_ = v_isSharedCheck_7078_;
goto v_resetjp_7072_;
}
v_resetjp_7072_:
{
lean_object* v___x_7076_; 
if (v_isShared_7074_ == 0)
{
v___x_7076_ = v___x_7073_;
goto v_reusejp_7075_;
}
else
{
lean_object* v_reuseFailAlloc_7077_; 
v_reuseFailAlloc_7077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7077_, 0, v_pos_7070_);
lean_ctor_set(v_reuseFailAlloc_7077_, 1, v_err_7071_);
v___x_7076_ = v_reuseFailAlloc_7077_;
goto v_reusejp_7075_;
}
v_reusejp_7075_:
{
return v___x_7076_;
}
}
}
}
else
{
lean_object* v_tail_7079_; lean_object* v_modifier_7080_; lean_object* v___x_7081_; 
v_tail_7079_ = lean_ctor_get(v_format_7051_, 1);
lean_inc(v_tail_7079_);
lean_dec_ref_known(v_format_7051_, 2);
v_modifier_7080_ = lean_ctor_get(v_head_7064_, 0);
lean_inc_ref(v_modifier_7080_);
lean_dec_ref_known(v_head_7064_, 1);
lean_inc_ref(v_config_7050_);
v___x_7081_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_7050_, v_modifier_7080_, v_a_7053_);
if (lean_obj_tag(v___x_7081_) == 0)
{
lean_object* v_pos_7082_; lean_object* v_res_7083_; lean_object* v___x_7084_; 
v_pos_7082_ = lean_ctor_get(v___x_7081_, 0);
lean_inc(v_pos_7082_);
v_res_7083_ = lean_ctor_get(v___x_7081_, 1);
lean_inc(v_res_7083_);
lean_dec_ref_known(v___x_7081_, 2);
v___x_7084_ = lean_apply_1(v_func_7052_, v_res_7083_);
v_format_7051_ = v_tail_7079_;
v_func_7052_ = v___x_7084_;
v_a_7053_ = v_pos_7082_;
goto _start;
}
else
{
lean_object* v_pos_7086_; lean_object* v_err_7087_; lean_object* v___x_7089_; uint8_t v_isShared_7090_; uint8_t v_isSharedCheck_7094_; 
lean_dec(v_tail_7079_);
lean_dec(v_func_7052_);
lean_dec_ref(v_config_7050_);
v_pos_7086_ = lean_ctor_get(v___x_7081_, 0);
v_err_7087_ = lean_ctor_get(v___x_7081_, 1);
v_isSharedCheck_7094_ = !lean_is_exclusive(v___x_7081_);
if (v_isSharedCheck_7094_ == 0)
{
v___x_7089_ = v___x_7081_;
v_isShared_7090_ = v_isSharedCheck_7094_;
goto v_resetjp_7088_;
}
else
{
lean_inc(v_err_7087_);
lean_inc(v_pos_7086_);
lean_dec(v___x_7081_);
v___x_7089_ = lean_box(0);
v_isShared_7090_ = v_isSharedCheck_7094_;
goto v_resetjp_7088_;
}
v_resetjp_7088_:
{
lean_object* v___x_7092_; 
if (v_isShared_7090_ == 0)
{
v___x_7092_ = v___x_7089_;
goto v_reusejp_7091_;
}
else
{
lean_object* v_reuseFailAlloc_7093_; 
v_reuseFailAlloc_7093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7093_, 0, v_pos_7086_);
lean_ctor_set(v_reuseFailAlloc_7093_, 1, v_err_7087_);
v___x_7092_ = v_reuseFailAlloc_7093_;
goto v_reusejp_7091_;
}
v_reusejp_7091_:
{
return v___x_7092_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object* v_00_u03b1_7095_, lean_object* v_config_7096_, lean_object* v_format_7097_, lean_object* v_func_7098_, lean_object* v_a_7099_){
_start:
{
lean_object* v___x_7100_; 
v___x_7100_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7096_, v_format_7097_, v_func_7098_, v_a_7099_);
return v___x_7100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object* v_format_7101_, lean_object* v_config_7102_, lean_object* v_func_7103_, lean_object* v_a_7104_){
_start:
{
lean_object* v___x_7105_; 
v___x_7105_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7102_, v_format_7101_, v_func_7103_, v_a_7104_);
return v___x_7105_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object* v_00_u03b1_7106_, lean_object* v_format_7107_, lean_object* v_config_7108_, lean_object* v_func_7109_, lean_object* v_a_7110_){
_start:
{
lean_object* v___x_7111_; 
v___x_7111_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7108_, v_format_7107_, v_func_7109_, v_a_7110_);
return v___x_7111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object* v_string_7112_, lean_object* v_config_7113_, lean_object* v_aw_7114_, lean_object* v___y_7115_){
_start:
{
lean_object* v___x_7116_; 
v___x_7116_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(v_string_7112_, v_config_7113_, v_aw_7114_, v___y_7115_);
if (lean_obj_tag(v___x_7116_) == 0)
{
lean_object* v_pos_7117_; lean_object* v_fst_7118_; lean_object* v_snd_7119_; lean_object* v___x_7120_; uint8_t v_decide_7121_; 
v_pos_7117_ = lean_ctor_get(v___x_7116_, 0);
v_fst_7118_ = lean_ctor_get(v_pos_7117_, 0);
v_snd_7119_ = lean_ctor_get(v_pos_7117_, 1);
v___x_7120_ = lean_string_utf8_byte_size(v_fst_7118_);
v_decide_7121_ = lean_nat_dec_eq(v_snd_7119_, v___x_7120_);
if (v_decide_7121_ == 0)
{
lean_object* v___x_7123_; uint8_t v_isShared_7124_; uint8_t v_isSharedCheck_7129_; 
lean_inc(v_pos_7117_);
v_isSharedCheck_7129_ = !lean_is_exclusive(v___x_7116_);
if (v_isSharedCheck_7129_ == 0)
{
lean_object* v_unused_7130_; lean_object* v_unused_7131_; 
v_unused_7130_ = lean_ctor_get(v___x_7116_, 1);
lean_dec(v_unused_7130_);
v_unused_7131_ = lean_ctor_get(v___x_7116_, 0);
lean_dec(v_unused_7131_);
v___x_7123_ = v___x_7116_;
v_isShared_7124_ = v_isSharedCheck_7129_;
goto v_resetjp_7122_;
}
else
{
lean_dec(v___x_7116_);
v___x_7123_ = lean_box(0);
v_isShared_7124_ = v_isSharedCheck_7129_;
goto v_resetjp_7122_;
}
v_resetjp_7122_:
{
lean_object* v___x_7125_; lean_object* v___x_7127_; 
v___x_7125_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_7124_ == 0)
{
lean_ctor_set_tag(v___x_7123_, 1);
lean_ctor_set(v___x_7123_, 1, v___x_7125_);
v___x_7127_ = v___x_7123_;
goto v_reusejp_7126_;
}
else
{
lean_object* v_reuseFailAlloc_7128_; 
v_reuseFailAlloc_7128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7128_, 0, v_pos_7117_);
lean_ctor_set(v_reuseFailAlloc_7128_, 1, v___x_7125_);
v___x_7127_ = v_reuseFailAlloc_7128_;
goto v_reusejp_7126_;
}
v_reusejp_7126_:
{
return v___x_7127_;
}
}
}
else
{
return v___x_7116_;
}
}
else
{
return v___x_7116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object* v_aw_7132_, lean_object* v_format_7133_, lean_object* v_input_7134_){
_start:
{
lean_object* v_config_7135_; lean_object* v_string_7136_; lean_object* v___f_7137_; lean_object* v___x_7138_; 
v_config_7135_ = lean_ctor_get(v_format_7133_, 0);
lean_inc_ref(v_config_7135_);
v_string_7136_ = lean_ctor_get(v_format_7133_, 1);
lean_inc(v_string_7136_);
lean_dec_ref(v_format_7133_);
v___f_7137_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parse___lam__0), 4, 3);
lean_closure_set(v___f_7137_, 0, v_string_7136_);
lean_closure_set(v___f_7137_, 1, v_config_7135_);
lean_closure_set(v___f_7137_, 2, v_aw_7132_);
v___x_7138_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7137_, v_input_7134_);
return v___x_7138_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object* v_msg_7139_){
_start:
{
lean_object* v___x_7140_; lean_object* v___x_7141_; 
v___x_7140_ = l_Std_Time_instInhabitedDateTime;
v___x_7141_ = lean_panic_fn_borrowed(v___x_7140_, v_msg_7139_);
return v___x_7141_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object* v_aw_7143_, lean_object* v_format_7144_, lean_object* v_input_7145_){
_start:
{
lean_object* v___x_7146_; 
v___x_7146_ = l_Std_Time_GenericFormat_parse(v_aw_7143_, v_format_7144_, v_input_7145_);
if (lean_obj_tag(v___x_7146_) == 0)
{
lean_object* v_a_7147_; lean_object* v___x_7148_; lean_object* v___x_7149_; lean_object* v___x_7150_; lean_object* v___x_7151_; lean_object* v___x_7152_; lean_object* v___x_7153_; 
v_a_7147_ = lean_ctor_get(v___x_7146_, 0);
lean_inc(v_a_7147_);
lean_dec_ref_known(v___x_7146_, 1);
v___x_7148_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7149_ = ((lean_object*)(l_Std_Time_GenericFormat_parse_x21___closed__0));
v___x_7150_ = lean_unsigned_to_nat(1124u);
v___x_7151_ = lean_unsigned_to_nat(18u);
v___x_7152_ = l_mkPanicMessageWithDecl(v___x_7148_, v___x_7149_, v___x_7150_, v___x_7151_, v_a_7147_);
lean_dec(v_a_7147_);
v___x_7153_ = l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(v___x_7152_);
return v___x_7153_;
}
else
{
lean_object* v_a_7154_; 
v_a_7154_ = lean_ctor_get(v___x_7146_, 0);
lean_inc(v_a_7154_);
lean_dec_ref_known(v___x_7146_, 1);
return v_a_7154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object* v_config_7155_, lean_object* v_string_7156_, lean_object* v_builder_7157_, lean_object* v___y_7158_){
_start:
{
lean_object* v___x_7159_; 
v___x_7159_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7155_, v_string_7156_, v_builder_7157_, v___y_7158_);
return v___x_7159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object* v_format_7160_, lean_object* v_builder_7161_, lean_object* v_input_7162_){
_start:
{
lean_object* v_config_7163_; lean_object* v_string_7164_; lean_object* v___f_7165_; lean_object* v___x_7166_; 
v_config_7163_ = lean_ctor_get(v_format_7160_, 0);
lean_inc_ref(v_config_7163_);
v_string_7164_ = lean_ctor_get(v_format_7160_, 1);
lean_inc(v_string_7164_);
lean_dec_ref(v_format_7160_);
v___f_7165_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0), 4, 3);
lean_closure_set(v___f_7165_, 0, v_config_7163_);
lean_closure_set(v___f_7165_, 1, v_string_7164_);
lean_closure_set(v___f_7165_, 2, v_builder_7161_);
v___x_7166_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7165_, v_input_7162_);
return v___x_7166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object* v_aw_7167_, lean_object* v_00_u03b1_7168_, lean_object* v_format_7169_, lean_object* v_builder_7170_, lean_object* v_input_7171_){
_start:
{
lean_object* v___x_7172_; 
v___x_7172_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7169_, v_builder_7170_, v_input_7171_);
return v___x_7172_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object* v_aw_7173_, lean_object* v_00_u03b1_7174_, lean_object* v_format_7175_, lean_object* v_builder_7176_, lean_object* v_input_7177_){
_start:
{
lean_object* v_res_7178_; 
v_res_7178_ = l_Std_Time_GenericFormat_parseBuilder(v_aw_7173_, v_00_u03b1_7174_, v_format_7175_, v_builder_7176_, v_input_7177_);
lean_dec(v_aw_7173_);
return v_res_7178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object* v_inst_7180_, lean_object* v_format_7181_, lean_object* v_builder_7182_, lean_object* v_input_7183_){
_start:
{
lean_object* v___x_7184_; 
v___x_7184_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7181_, v_builder_7182_, v_input_7183_);
if (lean_obj_tag(v___x_7184_) == 0)
{
lean_object* v_a_7185_; lean_object* v___x_7186_; lean_object* v___x_7187_; lean_object* v___x_7188_; lean_object* v___x_7189_; lean_object* v___x_7190_; lean_object* v___x_7191_; 
v_a_7185_ = lean_ctor_get(v___x_7184_, 0);
lean_inc(v_a_7185_);
lean_dec_ref_known(v___x_7184_, 1);
v___x_7186_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7187_ = ((lean_object*)(l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0));
v___x_7188_ = lean_unsigned_to_nat(1138u);
v___x_7189_ = lean_unsigned_to_nat(18u);
v___x_7190_ = l_mkPanicMessageWithDecl(v___x_7186_, v___x_7187_, v___x_7188_, v___x_7189_, v_a_7185_);
lean_dec(v_a_7185_);
v___x_7191_ = l_panic___redArg(v_inst_7180_, v___x_7190_);
return v___x_7191_;
}
else
{
lean_object* v_a_7192_; 
v_a_7192_ = lean_ctor_get(v___x_7184_, 0);
lean_inc(v_a_7192_);
lean_dec_ref_known(v___x_7184_, 1);
return v_a_7192_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object* v_inst_7193_, lean_object* v_format_7194_, lean_object* v_builder_7195_, lean_object* v_input_7196_){
_start:
{
lean_object* v_res_7197_; 
v_res_7197_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7193_, v_format_7194_, v_builder_7195_, v_input_7196_);
lean_dec(v_inst_7193_);
return v_res_7197_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object* v_00_u03b1_7198_, lean_object* v_aw_7199_, lean_object* v_inst_7200_, lean_object* v_format_7201_, lean_object* v_builder_7202_, lean_object* v_input_7203_){
_start:
{
lean_object* v___x_7204_; 
v___x_7204_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7200_, v_format_7201_, v_builder_7202_, v_input_7203_);
return v___x_7204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object* v_00_u03b1_7205_, lean_object* v_aw_7206_, lean_object* v_inst_7207_, lean_object* v_format_7208_, lean_object* v_builder_7209_, lean_object* v_input_7210_){
_start:
{
lean_object* v_res_7211_; 
v_res_7211_ = l_Std_Time_GenericFormat_parseBuilder_x21(v_00_u03b1_7205_, v_aw_7206_, v_inst_7207_, v_format_7208_, v_builder_7209_, v_input_7210_);
lean_dec(v_inst_7207_);
lean_dec(v_aw_7206_);
return v_res_7211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object* v_getInfo_7212_, lean_object* v_dateformat_7213_, lean_object* v_data_7214_, lean_object* v_format_7215_){
_start:
{
if (lean_obj_tag(v_format_7215_) == 0)
{
lean_object* v___x_7216_; 
lean_dec_ref(v_getInfo_7212_);
v___x_7216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7216_, 0, v_data_7214_);
return v___x_7216_;
}
else
{
lean_object* v_head_7217_; 
v_head_7217_ = lean_ctor_get(v_format_7215_, 0);
lean_inc(v_head_7217_);
if (lean_obj_tag(v_head_7217_) == 0)
{
lean_object* v_tail_7218_; lean_object* v_val_7219_; lean_object* v___x_7220_; 
v_tail_7218_ = lean_ctor_get(v_format_7215_, 1);
lean_inc(v_tail_7218_);
lean_dec_ref_known(v_format_7215_, 2);
v_val_7219_ = lean_ctor_get(v_head_7217_, 0);
lean_inc_ref(v_val_7219_);
lean_dec_ref_known(v_head_7217_, 1);
v___x_7220_ = lean_string_append(v_data_7214_, v_val_7219_);
lean_dec_ref(v_val_7219_);
v_data_7214_ = v___x_7220_;
v_format_7215_ = v_tail_7218_;
goto _start;
}
else
{
lean_object* v_tail_7222_; lean_object* v_modifier_7223_; lean_object* v___x_7224_; 
v_tail_7222_ = lean_ctor_get(v_format_7215_, 1);
lean_inc(v_tail_7222_);
lean_dec_ref_known(v_format_7215_, 2);
v_modifier_7223_ = lean_ctor_get(v_head_7217_, 0);
lean_inc_ref_n(v_modifier_7223_, 2);
lean_dec_ref_known(v_head_7217_, 1);
lean_inc_ref(v_getInfo_7212_);
v___x_7224_ = lean_apply_1(v_getInfo_7212_, v_modifier_7223_);
if (lean_obj_tag(v___x_7224_) == 0)
{
lean_object* v___x_7225_; 
lean_dec_ref(v_modifier_7223_);
lean_dec(v_tail_7222_);
lean_dec_ref(v_data_7214_);
lean_dec_ref(v_getInfo_7212_);
v___x_7225_ = lean_box(0);
return v___x_7225_;
}
else
{
lean_object* v_val_7226_; lean_object* v___x_7227_; lean_object* v___x_7228_; 
v_val_7226_ = lean_ctor_get(v___x_7224_, 0);
lean_inc(v_val_7226_);
lean_dec_ref_known(v___x_7224_, 1);
v___x_7227_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7213_, v_modifier_7223_, v_val_7226_);
v___x_7228_ = lean_string_append(v_data_7214_, v___x_7227_);
lean_dec_ref(v___x_7227_);
v_data_7214_ = v___x_7228_;
v_format_7215_ = v_tail_7222_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go___boxed(lean_object* v_getInfo_7230_, lean_object* v_dateformat_7231_, lean_object* v_data_7232_, lean_object* v_format_7233_){
_start:
{
lean_object* v_res_7234_; 
v_res_7234_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7230_, v_dateformat_7231_, v_data_7232_, v_format_7233_);
lean_dec_ref(v_dateformat_7231_);
return v_res_7234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object* v_format_7235_, lean_object* v_getInfo_7236_){
_start:
{
lean_object* v_config_7237_; lean_object* v_string_7238_; lean_object* v_dateformat_7239_; lean_object* v___x_7240_; lean_object* v___x_7241_; 
v_config_7237_ = lean_ctor_get(v_format_7235_, 0);
lean_inc_ref(v_config_7237_);
v_string_7238_ = lean_ctor_get(v_format_7235_, 1);
lean_inc(v_string_7238_);
lean_dec_ref(v_format_7235_);
v_dateformat_7239_ = lean_ctor_get(v_config_7237_, 0);
lean_inc_ref(v_dateformat_7239_);
lean_dec_ref(v_config_7237_);
v___x_7240_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7241_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7236_, v_dateformat_7239_, v___x_7240_, v_string_7238_);
lean_dec_ref(v_dateformat_7239_);
return v___x_7241_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object* v_aw_7242_, lean_object* v_format_7243_, lean_object* v_getInfo_7244_){
_start:
{
lean_object* v___x_7245_; 
v___x_7245_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7243_, v_getInfo_7244_);
return v___x_7245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object* v_aw_7246_, lean_object* v_format_7247_, lean_object* v_getInfo_7248_){
_start:
{
lean_object* v_res_7249_; 
v_res_7249_ = l_Std_Time_GenericFormat_formatGeneric(v_aw_7246_, v_format_7247_, v_getInfo_7248_);
lean_dec(v_aw_7246_);
return v_res_7249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object* v_dateformat_7250_, lean_object* v_data_7251_, lean_object* v_format_7252_){
_start:
{
if (lean_obj_tag(v_format_7252_) == 0)
{
lean_dec_ref(v_dateformat_7250_);
return v_data_7251_;
}
else
{
lean_object* v_head_7253_; 
v_head_7253_ = lean_ctor_get(v_format_7252_, 0);
lean_inc(v_head_7253_);
if (lean_obj_tag(v_head_7253_) == 0)
{
lean_object* v_tail_7254_; lean_object* v_val_7255_; lean_object* v___x_7256_; 
v_tail_7254_ = lean_ctor_get(v_format_7252_, 1);
lean_inc(v_tail_7254_);
lean_dec_ref_known(v_format_7252_, 2);
v_val_7255_ = lean_ctor_get(v_head_7253_, 0);
lean_inc_ref(v_val_7255_);
lean_dec_ref_known(v_head_7253_, 1);
v___x_7256_ = lean_string_append(v_data_7251_, v_val_7255_);
lean_dec_ref(v_val_7255_);
v_data_7251_ = v___x_7256_;
v_format_7252_ = v_tail_7254_;
goto _start;
}
else
{
lean_object* v_tail_7258_; lean_object* v_modifier_7259_; lean_object* v___f_7260_; 
v_tail_7258_ = lean_ctor_get(v_format_7252_, 1);
lean_inc(v_tail_7258_);
lean_dec_ref_known(v_format_7252_, 2);
v_modifier_7259_ = lean_ctor_get(v_head_7253_, 0);
lean_inc_ref(v_modifier_7259_);
lean_dec_ref_known(v_head_7253_, 1);
v___f_7260_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0), 5, 4);
lean_closure_set(v___f_7260_, 0, v_dateformat_7250_);
lean_closure_set(v___f_7260_, 1, v_modifier_7259_);
lean_closure_set(v___f_7260_, 2, v_data_7251_);
lean_closure_set(v___f_7260_, 3, v_tail_7258_);
return v___f_7260_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object* v_dateformat_7261_, lean_object* v_modifier_7262_, lean_object* v_data_7263_, lean_object* v_tail_7264_, lean_object* v___y_7265_){
_start:
{
lean_object* v___x_7266_; lean_object* v___x_7267_; lean_object* v___x_7268_; 
v___x_7266_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7261_, v_modifier_7262_, v___y_7265_);
v___x_7267_ = lean_string_append(v_data_7263_, v___x_7266_);
lean_dec_ref(v___x_7266_);
v___x_7268_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7261_, v___x_7267_, v_tail_7264_);
return v___x_7268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object* v_format_7269_){
_start:
{
lean_object* v_config_7270_; lean_object* v_string_7271_; lean_object* v_dateformat_7272_; lean_object* v___x_7273_; lean_object* v___x_7274_; 
v_config_7270_ = lean_ctor_get(v_format_7269_, 0);
lean_inc_ref(v_config_7270_);
v_string_7271_ = lean_ctor_get(v_format_7269_, 1);
lean_inc(v_string_7271_);
lean_dec_ref(v_format_7269_);
v_dateformat_7272_ = lean_ctor_get(v_config_7270_, 0);
lean_inc_ref(v_dateformat_7272_);
lean_dec_ref(v_config_7270_);
v___x_7273_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7274_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7272_, v___x_7273_, v_string_7271_);
return v___x_7274_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object* v_aw_7275_, lean_object* v_format_7276_){
_start:
{
lean_object* v___x_7277_; 
v___x_7277_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v_format_7276_);
return v___x_7277_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object* v_aw_7278_, lean_object* v_format_7279_){
_start:
{
lean_object* v_res_7280_; 
v_res_7280_ = l_Std_Time_GenericFormat_formatBuilder(v_aw_7278_, v_format_7279_);
lean_dec(v_aw_7278_);
return v_res_7280_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instFormatGenericFormatFormatTypeString(lean_object* v_aw_7281_){
_start:
{
lean_object* v___x_7282_; lean_object* v___x_7283_; lean_object* v___x_7284_; 
lean_inc(v_aw_7281_);
v___x_7282_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_formatBuilder___boxed), 2, 1);
lean_closure_set(v___x_7282_, 0, v_aw_7281_);
v___x_7283_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___boxed), 5, 1);
lean_closure_set(v___x_7283_, 0, v_aw_7281_);
v___x_7284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7284_, 0, v___x_7282_);
lean_ctor_set(v___x_7284_, 1, v___x_7283_);
return v___x_7284_;
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
