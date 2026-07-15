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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_toCtorIdx___boxed(lean_object*);
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
v___x_867_ = lean_string_utf8_extract(v_numStr_856_, v___x_866_, v___x_857_);
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
v___x_896_ = lean_string_utf8_extract(v_numStr_885_, v___x_892_, v___x_895_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_toCtorIdx(uint8_t v_x_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_toCtorIdx___boxed(lean_object* v_x_1171_){
_start:
{
uint8_t v_x_4__boxed_1172_; lean_object* v_res_1173_; 
v_x_4__boxed_1172_ = lean_unbox(v_x_1171_);
v_res_1173_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_toCtorIdx(v_x_4__boxed_1172_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(lean_object* v_k_1174_){
_start:
{
lean_inc(v_k_1174_);
return v_k_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg___boxed(lean_object* v_k_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(v_k_1175_);
lean_dec(v_k_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_object* v_motive_1177_, lean_object* v_ctorIdx_1178_, uint8_t v_t_1179_, lean_object* v_h_1180_, lean_object* v_k_1181_){
_start:
{
lean_inc(v_k_1181_);
return v_k_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___boxed(lean_object* v_motive_1182_, lean_object* v_ctorIdx_1183_, lean_object* v_t_1184_, lean_object* v_h_1185_, lean_object* v_k_1186_){
_start:
{
uint8_t v_t_boxed_1187_; lean_object* v_res_1188_; 
v_t_boxed_1187_ = lean_unbox(v_t_1184_);
v_res_1188_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(v_motive_1182_, v_ctorIdx_1183_, v_t_boxed_1187_, v_h_1185_, v_k_1186_);
lean_dec(v_k_1186_);
lean_dec(v_ctorIdx_1183_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(lean_object* v_yes_1189_){
_start:
{
lean_inc(v_yes_1189_);
return v_yes_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg___boxed(lean_object* v_yes_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(v_yes_1190_);
lean_dec(v_yes_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_object* v_motive_1192_, uint8_t v_t_1193_, lean_object* v_h_1194_, lean_object* v_yes_1195_){
_start:
{
lean_inc(v_yes_1195_);
return v_yes_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___boxed(lean_object* v_motive_1196_, lean_object* v_t_1197_, lean_object* v_h_1198_, lean_object* v_yes_1199_){
_start:
{
uint8_t v_t_boxed_1200_; lean_object* v_res_1201_; 
v_t_boxed_1200_ = lean_unbox(v_t_1197_);
v_res_1201_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(v_motive_1196_, v_t_boxed_1200_, v_h_1198_, v_yes_1199_);
lean_dec(v_yes_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(lean_object* v_no_1202_){
_start:
{
lean_inc(v_no_1202_);
return v_no_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg___boxed(lean_object* v_no_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(v_no_1203_);
lean_dec(v_no_1203_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_object* v_motive_1205_, uint8_t v_t_1206_, lean_object* v_h_1207_, lean_object* v_no_1208_){
_start:
{
lean_inc(v_no_1208_);
return v_no_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___boxed(lean_object* v_motive_1209_, lean_object* v_t_1210_, lean_object* v_h_1211_, lean_object* v_no_1212_){
_start:
{
uint8_t v_t_boxed_1213_; lean_object* v_res_1214_; 
v_t_boxed_1213_ = lean_unbox(v_t_1210_);
v_res_1214_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(v_motive_1209_, v_t_boxed_1213_, v_h_1211_, v_no_1212_);
lean_dec(v_no_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(lean_object* v_optional_1215_){
_start:
{
lean_inc(v_optional_1215_);
return v_optional_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg___boxed(lean_object* v_optional_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(v_optional_1216_);
lean_dec(v_optional_1216_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_object* v_motive_1218_, uint8_t v_t_1219_, lean_object* v_h_1220_, lean_object* v_optional_1221_){
_start:
{
lean_inc(v_optional_1221_);
return v_optional_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___boxed(lean_object* v_motive_1222_, lean_object* v_t_1223_, lean_object* v_h_1224_, lean_object* v_optional_1225_){
_start:
{
uint8_t v_t_boxed_1226_; lean_object* v_res_1227_; 
v_t_boxed_1226_ = lean_unbox(v_t_1223_);
v_res_1227_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(v_motive_1222_, v_t_boxed_1226_, v_h_1224_, v_optional_1225_);
lean_dec(v_optional_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(uint8_t v_x_1228_, uint8_t v_y_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_x_1228_);
v___x_1231_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_y_1229_);
v___x_1232_ = lean_nat_dec_eq(v___x_1230_, v___x_1231_);
lean_dec(v___x_1231_);
lean_dec(v___x_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq___boxed(lean_object* v_x_1233_, lean_object* v_y_1234_){
_start:
{
uint8_t v_x_17__boxed_1235_; uint8_t v_y_18__boxed_1236_; uint8_t v_res_1237_; lean_object* v_r_1238_; 
v_x_17__boxed_1235_ = lean_unbox(v_x_1233_);
v_y_18__boxed_1236_ = lean_unbox(v_y_1234_);
v_res_1237_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_x_17__boxed_1235_, v_y_18__boxed_1236_);
v_r_1238_ = lean_box(v_res_1237_);
return v_r_1238_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__1(lean_object* v_a_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Rat_ofInt(v_a_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(1000000000u);
v___x_1245_ = lean_nat_to_int(v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(lean_object* v_offset_1246_, uint8_t v_withMinutes_1247_, uint8_t v_withSeconds_1248_, uint8_t v_colon_1249_, uint8_t v_padHour_1250_){
_start:
{
uint32_t v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1263_; uint32_t v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; uint32_t v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1274_; uint8_t v___y_1276_; lean_object* v___y_1277_; uint32_t v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; uint8_t v___y_1288_; uint32_t v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; uint8_t v___y_1300_; lean_object* v___y_1301_; uint32_t v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; uint8_t v___y_1308_; uint32_t v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; uint8_t v___y_1313_; uint32_t v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v_fst_1329_; lean_object* v_snd_1330_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1342_ = lean_int_dec_le(v___x_1341_, v_offset_1246_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1344_ = lean_int_neg(v_offset_1246_);
lean_dec(v_offset_1246_);
v_fst_1329_ = v___x_1343_;
v_snd_1330_ = v___x_1344_;
goto v___jp_1328_;
}
else
{
lean_object* v___x_1345_; 
v___x_1345_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1329_ = v___x_1345_;
v_snd_1330_ = v_offset_1246_;
goto v___jp_1328_;
}
v___jp_1251_:
{
lean_object* v_second_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_second_1257_ = lean_ctor_get(v___y_1253_, 2);
lean_inc(v_second_1257_);
lean_dec_ref(v___y_1253_);
v___x_1258_ = lean_string_append(v___y_1255_, v___y_1256_);
v___x_1259_ = l_Int_repr(v_second_1257_);
lean_dec(v_second_1257_);
v___x_1260_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1254_, v___y_1252_, v___x_1259_);
v___x_1261_ = lean_string_append(v___x_1258_, v___x_1260_);
lean_dec_ref(v___x_1260_);
return v___x_1261_;
}
v___jp_1262_:
{
if (v_colon_1249_ == 0)
{
lean_object* v___x_1267_; 
v___x_1267_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___y_1252_ = v___y_1264_;
v___y_1253_ = v___y_1263_;
v___y_1254_ = v___y_1265_;
v___y_1255_ = v___y_1266_;
v___y_1256_ = v___x_1267_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1268_; 
v___x_1268_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1252_ = v___y_1264_;
v___y_1253_ = v___y_1263_;
v___y_1254_ = v___y_1265_;
v___y_1255_ = v___y_1266_;
v___y_1256_ = v___x_1268_;
goto v___jp_1251_;
}
}
v___jp_1269_:
{
if (v___y_1274_ == 0)
{
lean_dec_ref(v___y_1271_);
return v___y_1273_;
}
else
{
v___y_1263_ = v___y_1271_;
v___y_1264_ = v___y_1270_;
v___y_1265_ = v___y_1272_;
v___y_1266_ = v___y_1273_;
goto v___jp_1262_;
}
}
v___jp_1275_:
{
uint8_t v___x_1281_; 
v___x_1281_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1248_, v___y_1276_);
if (v___x_1281_ == 0)
{
uint8_t v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = 2;
v___x_1283_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1248_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_dec_ref(v___y_1277_);
return v___y_1280_;
}
else
{
lean_object* v_second_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_second_1284_ = lean_ctor_get(v___y_1277_, 2);
v___x_1285_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1286_ = lean_int_dec_eq(v_second_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
v___y_1270_ = v___y_1278_;
v___y_1271_ = v___y_1277_;
v___y_1272_ = v___y_1279_;
v___y_1273_ = v___y_1280_;
v___y_1274_ = v___x_1283_;
goto v___jp_1269_;
}
else
{
v___y_1270_ = v___y_1278_;
v___y_1271_ = v___y_1277_;
v___y_1272_ = v___y_1279_;
v___y_1273_ = v___y_1280_;
v___y_1274_ = v___x_1281_;
goto v___jp_1269_;
}
}
}
else
{
v___y_1263_ = v___y_1277_;
v___y_1264_ = v___y_1278_;
v___y_1265_ = v___y_1279_;
v___y_1266_ = v___y_1280_;
goto v___jp_1262_;
}
}
v___jp_1287_:
{
lean_object* v_minute_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_minute_1294_ = lean_ctor_get(v___y_1290_, 1);
v___x_1295_ = lean_string_append(v___y_1292_, v___y_1293_);
v___x_1296_ = l_Int_repr(v_minute_1294_);
v___x_1297_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1291_, v___y_1289_, v___x_1296_);
v___x_1298_ = lean_string_append(v___x_1295_, v___x_1297_);
lean_dec_ref(v___x_1297_);
v___y_1276_ = v___y_1288_;
v___y_1277_ = v___y_1290_;
v___y_1278_ = v___y_1289_;
v___y_1279_ = v___y_1291_;
v___y_1280_ = v___x_1298_;
goto v___jp_1275_;
}
v___jp_1299_:
{
if (v_colon_1249_ == 0)
{
lean_object* v___x_1305_; 
v___x_1305_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___y_1288_ = v___y_1300_;
v___y_1289_ = v___y_1302_;
v___y_1290_ = v___y_1301_;
v___y_1291_ = v___y_1304_;
v___y_1292_ = v___y_1303_;
v___y_1293_ = v___x_1305_;
goto v___jp_1287_;
}
else
{
lean_object* v___x_1306_; 
v___x_1306_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1288_ = v___y_1300_;
v___y_1289_ = v___y_1302_;
v___y_1290_ = v___y_1301_;
v___y_1291_ = v___y_1304_;
v___y_1292_ = v___y_1303_;
v___y_1293_ = v___x_1306_;
goto v___jp_1287_;
}
}
v___jp_1307_:
{
if (v___y_1313_ == 0)
{
v___y_1276_ = v___y_1308_;
v___y_1277_ = v___y_1310_;
v___y_1278_ = v___y_1309_;
v___y_1279_ = v___y_1311_;
v___y_1280_ = v___y_1312_;
goto v___jp_1275_;
}
else
{
v___y_1300_ = v___y_1308_;
v___y_1301_ = v___y_1310_;
v___y_1302_ = v___y_1309_;
v___y_1303_ = v___y_1312_;
v___y_1304_ = v___y_1311_;
goto v___jp_1299_;
}
}
v___jp_1314_:
{
lean_object* v_data_1320_; uint8_t v___x_1321_; uint8_t v___x_1322_; 
lean_inc_ref(v___y_1318_);
v_data_1320_ = lean_string_append(v___y_1318_, v___y_1319_);
lean_dec_ref(v___y_1319_);
v___x_1321_ = 0;
v___x_1322_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1247_, v___x_1321_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = 2;
v___x_1324_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1247_, v___x_1323_);
if (v___x_1324_ == 0)
{
v___y_1276_ = v___x_1321_;
v___y_1277_ = v___y_1316_;
v___y_1278_ = v___y_1315_;
v___y_1279_ = v___y_1317_;
v___y_1280_ = v_data_1320_;
goto v___jp_1275_;
}
else
{
lean_object* v_minute_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_minute_1325_ = lean_ctor_get(v___y_1316_, 1);
v___x_1326_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1327_ = lean_int_dec_eq(v_minute_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
v___y_1308_ = v___x_1321_;
v___y_1309_ = v___y_1315_;
v___y_1310_ = v___y_1316_;
v___y_1311_ = v___y_1317_;
v___y_1312_ = v_data_1320_;
v___y_1313_ = v___x_1324_;
goto v___jp_1307_;
}
else
{
v___y_1308_ = v___x_1321_;
v___y_1309_ = v___y_1315_;
v___y_1310_ = v___y_1316_;
v___y_1311_ = v___y_1317_;
v___y_1312_ = v_data_1320_;
v___y_1313_ = v___x_1322_;
goto v___jp_1307_;
}
}
}
else
{
v___y_1300_ = v___x_1321_;
v___y_1301_ = v___y_1316_;
v___y_1302_ = v___y_1315_;
v___y_1303_ = v_data_1320_;
v___y_1304_ = v___y_1317_;
goto v___jp_1299_;
}
}
v___jp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_time_1333_; lean_object* v___x_1334_; uint32_t v___x_1335_; 
v___x_1331_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1332_ = lean_int_mul(v_snd_1330_, v___x_1331_);
lean_dec(v_snd_1330_);
v_time_1333_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1332_);
lean_dec(v___x_1332_);
v___x_1334_ = lean_unsigned_to_nat(2u);
v___x_1335_ = 48;
if (v_padHour_1250_ == 0)
{
lean_object* v_hour_1336_; lean_object* v___x_1337_; 
v_hour_1336_ = lean_ctor_get(v_time_1333_, 0);
lean_inc(v_hour_1336_);
v___x_1337_ = l_Int_repr(v_hour_1336_);
lean_dec(v_hour_1336_);
v___y_1315_ = v___x_1335_;
v___y_1316_ = v_time_1333_;
v___y_1317_ = v___x_1334_;
v___y_1318_ = v_fst_1329_;
v___y_1319_ = v___x_1337_;
goto v___jp_1314_;
}
else
{
lean_object* v_hour_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_hour_1338_ = lean_ctor_get(v_time_1333_, 0);
lean_inc(v_hour_1338_);
v___x_1339_ = l_Int_repr(v_hour_1338_);
lean_dec(v_hour_1338_);
v___x_1340_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1334_, v___x_1335_, v___x_1339_);
v___y_1315_ = v___x_1335_;
v___y_1316_ = v_time_1333_;
v___y_1317_ = v___x_1334_;
v___y_1318_ = v_fst_1329_;
v___y_1319_ = v___x_1340_;
goto v___jp_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___boxed(lean_object* v_offset_1346_, lean_object* v_withMinutes_1347_, lean_object* v_withSeconds_1348_, lean_object* v_colon_1349_, lean_object* v_padHour_1350_){
_start:
{
uint8_t v_withMinutes_boxed_1351_; uint8_t v_withSeconds_boxed_1352_; uint8_t v_colon_boxed_1353_; uint8_t v_padHour_boxed_1354_; lean_object* v_res_1355_; 
v_withMinutes_boxed_1351_ = lean_unbox(v_withMinutes_1347_);
v_withSeconds_boxed_1352_ = lean_unbox(v_withSeconds_1348_);
v_colon_boxed_1353_ = lean_unbox(v_colon_1349_);
v_padHour_boxed_1354_ = lean_unbox(v_padHour_1350_);
v_res_1355_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1346_, v_withMinutes_boxed_1351_, v_withSeconds_boxed_1352_, v_colon_boxed_1353_, v_padHour_boxed_1354_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0_spec__0(lean_object* v_a_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_nat_to_int(v_a_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(lean_object* v_a_1358_){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_nat_to_int(v_a_1358_);
v___x_1360_ = l_Rat_ofInt(v___x_1359_);
return v___x_1360_;
}
}
static lean_object* _init_l_Std_Time_classifyDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_unsigned_to_nat(12u);
v___x_1362_ = lean_nat_to_int(v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod(lean_object* v_hour_1363_, lean_object* v_minute_1364_, lean_object* v_second_1365_){
_start:
{
lean_object* v___y_1367_; lean_object* v___x_1371_; uint8_t v___x_1378_; 
v___x_1371_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1378_ = lean_int_dec_eq(v_hour_1363_, v___x_1371_);
if (v___x_1378_ == 0)
{
goto v___jp_1372_;
}
else
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_int_dec_eq(v_minute_1364_, v___x_1371_);
if (v___x_1379_ == 0)
{
goto v___jp_1372_;
}
else
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_int_dec_eq(v_second_1365_, v___x_1371_);
if (v___x_1380_ == 0)
{
goto v___jp_1372_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = 3;
return v___x_1381_;
}
}
}
v___jp_1366_:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_int_dec_lt(v_hour_1363_, v___y_1367_);
if (v___x_1368_ == 0)
{
uint8_t v___x_1369_; 
v___x_1369_ = 1;
return v___x_1369_;
}
else
{
uint8_t v___x_1370_; 
v___x_1370_ = 0;
return v___x_1370_;
}
}
v___jp_1372_:
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1374_ = lean_int_dec_eq(v_hour_1363_, v___x_1373_);
if (v___x_1374_ == 0)
{
v___y_1367_ = v___x_1373_;
goto v___jp_1366_;
}
else
{
uint8_t v___x_1375_; 
v___x_1375_ = lean_int_dec_eq(v_minute_1364_, v___x_1371_);
if (v___x_1375_ == 0)
{
v___y_1367_ = v___x_1373_;
goto v___jp_1366_;
}
else
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_int_dec_eq(v_second_1365_, v___x_1371_);
if (v___x_1376_ == 0)
{
v___y_1367_ = v___x_1373_;
goto v___jp_1366_;
}
else
{
uint8_t v___x_1377_; 
v___x_1377_ = 2;
return v___x_1377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___boxed(lean_object* v_hour_1382_, lean_object* v_minute_1383_, lean_object* v_second_1384_){
_start:
{
uint8_t v_res_1385_; lean_object* v_r_1386_; 
v_res_1385_ = l_Std_Time_classifyDayPeriod(v_hour_1382_, v_minute_1383_, v_second_1384_);
lean_dec(v_second_1384_);
lean_dec(v_minute_1383_);
lean_dec(v_hour_1382_);
v_r_1386_ = lean_box(v_res_1385_);
return v_r_1386_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_unsigned_to_nat(6u);
v___x_1388_ = lean_nat_to_int(v___x_1387_);
return v___x_1388_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__1(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_unsigned_to_nat(18u);
v___x_1390_ = lean_nat_to_int(v___x_1389_);
return v___x_1390_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__2(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_unsigned_to_nat(21u);
v___x_1392_ = lean_nat_to_int(v___x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object* v_hour_1393_, lean_object* v_minute_1394_, lean_object* v_second_1395_){
_start:
{
lean_object* v___y_1397_; lean_object* v___x_1410_; uint8_t v___x_1417_; 
v___x_1410_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1417_ = lean_int_dec_eq(v_hour_1393_, v___x_1410_);
if (v___x_1417_ == 0)
{
goto v___jp_1411_;
}
else
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_int_dec_eq(v_minute_1394_, v___x_1410_);
if (v___x_1418_ == 0)
{
goto v___jp_1411_;
}
else
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_int_dec_eq(v_second_1395_, v___x_1410_);
if (v___x_1419_ == 0)
{
goto v___jp_1411_;
}
else
{
uint8_t v___x_1420_; 
v___x_1420_ = 0;
return v___x_1420_;
}
}
}
v___jp_1396_:
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_1399_ = lean_int_dec_lt(v_hour_1393_, v___x_1398_);
if (v___x_1399_ == 0)
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_int_dec_lt(v_hour_1393_, v___y_1397_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1401_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__1, &l_Std_Time_classifyExtendedDayPeriod___closed__1_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__1);
v___x_1402_ = lean_int_dec_lt(v_hour_1393_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__2, &l_Std_Time_classifyExtendedDayPeriod___closed__2_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__2);
v___x_1404_ = lean_int_dec_lt(v_hour_1393_, v___x_1403_);
if (v___x_1404_ == 0)
{
uint8_t v___x_1405_; 
v___x_1405_ = 1;
return v___x_1405_;
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = 5;
return v___x_1406_;
}
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = 4;
return v___x_1407_;
}
}
else
{
uint8_t v___x_1408_; 
v___x_1408_ = 2;
return v___x_1408_;
}
}
else
{
uint8_t v___x_1409_; 
v___x_1409_ = 1;
return v___x_1409_;
}
}
v___jp_1411_:
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1413_ = lean_int_dec_eq(v_hour_1393_, v___x_1412_);
if (v___x_1413_ == 0)
{
v___y_1397_ = v___x_1412_;
goto v___jp_1396_;
}
else
{
uint8_t v___x_1414_; 
v___x_1414_ = lean_int_dec_eq(v_minute_1394_, v___x_1410_);
if (v___x_1414_ == 0)
{
v___y_1397_ = v___x_1412_;
goto v___jp_1396_;
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_int_dec_eq(v_second_1395_, v___x_1410_);
if (v___x_1415_ == 0)
{
v___y_1397_ = v___x_1412_;
goto v___jp_1396_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = 3;
return v___x_1416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyExtendedDayPeriod___boxed(lean_object* v_hour_1421_, lean_object* v_minute_1422_, lean_object* v_second_1423_){
_start:
{
uint8_t v_res_1424_; lean_object* v_r_1425_; 
v_res_1424_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1421_, v_minute_1422_, v_second_1423_);
lean_dec(v_second_1423_);
lean_dec(v_minute_1422_);
lean_dec(v_hour_1421_);
v_r_1425_ = lean_box(v_res_1424_);
return v_r_1425_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_unsigned_to_nat(100u);
v___x_1427_ = lean_nat_to_int(v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_unsigned_to_nat(7u);
v___x_1429_ = lean_nat_to_int(v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object* v_dateformat_1433_, lean_object* v_modifier_1434_, lean_object* v_data_1435_){
_start:
{
switch(lean_obj_tag(v_modifier_1434_))
{
case 0:
{
uint8_t v_presentation_1436_; 
v_presentation_1436_ = lean_ctor_get_uint8(v_modifier_1434_, 0);
lean_dec_ref_known(v_modifier_1434_, 0);
switch(v_presentation_1436_)
{
case 1:
{
lean_object* v_symbols_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; 
v_symbols_1437_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1438_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1439_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1437_, v___x_1438_);
return v___x_1439_;
}
case 2:
{
lean_object* v_symbols_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; 
v_symbols_1440_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1441_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1442_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1440_, v___x_1441_);
return v___x_1442_;
}
default: 
{
lean_object* v_symbols_1443_; uint8_t v___x_1444_; lean_object* v___x_1445_; 
v_symbols_1443_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1444_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1445_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1443_, v___x_1444_);
return v___x_1445_;
}
}
}
case 1:
{
lean_object* v_presentation_1446_; 
v_presentation_1446_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1446_);
lean_dec_ref_known(v_modifier_1434_, 1);
switch(lean_obj_tag(v_presentation_1446_))
{
case 0:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = 0;
v___x_1449_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1447_, v_data_1435_, v___x_1448_);
return v___x_1449_;
}
case 1:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1450_ = lean_unsigned_to_nat(2u);
v___x_1451_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1452_ = lean_int_emod(v_data_1435_, v___x_1451_);
lean_dec(v_data_1435_);
v___x_1453_ = 0;
v___x_1454_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1450_, v___x_1452_, v___x_1453_);
return v___x_1454_;
}
case 2:
{
lean_object* v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_unsigned_to_nat(4u);
v___x_1456_ = 0;
v___x_1457_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1455_, v_data_1435_, v___x_1456_);
return v___x_1457_;
}
default: 
{
lean_object* v_num_1458_; uint8_t v___x_1459_; lean_object* v___x_1460_; 
v_num_1458_ = lean_ctor_get(v_presentation_1446_, 0);
lean_inc(v_num_1458_);
lean_dec_ref_known(v_presentation_1446_, 1);
v___x_1459_ = 0;
v___x_1460_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1458_, v_data_1435_, v___x_1459_);
lean_dec(v_num_1458_);
return v___x_1460_;
}
}
}
case 2:
{
lean_object* v_presentation_1461_; lean_object* v___x_1462_; lean_object* v___y_1464_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_presentation_1461_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1461_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1479_ = lean_int_dec_le(v_data_1435_, v___x_1478_);
if (v___x_1479_ == 0)
{
v___y_1464_ = v_data_1435_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = lean_int_neg(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1481_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1482_ = lean_int_add(v___x_1480_, v___x_1481_);
lean_dec(v___x_1480_);
v___y_1464_ = v___x_1482_;
goto v___jp_1463_;
}
v___jp_1463_:
{
switch(lean_obj_tag(v_presentation_1461_))
{
case 0:
{
uint8_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = 0;
v___x_1466_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1462_, v___y_1464_, v___x_1465_);
return v___x_1466_;
}
case 1:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1467_ = lean_unsigned_to_nat(2u);
v___x_1468_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1469_ = lean_int_emod(v___y_1464_, v___x_1468_);
lean_dec(v___y_1464_);
v___x_1470_ = 0;
v___x_1471_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1467_, v___x_1469_, v___x_1470_);
return v___x_1471_;
}
case 2:
{
lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = lean_unsigned_to_nat(4u);
v___x_1473_ = 0;
v___x_1474_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1472_, v___y_1464_, v___x_1473_);
return v___x_1474_;
}
default: 
{
lean_object* v_num_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; 
v_num_1475_ = lean_ctor_get(v_presentation_1461_, 0);
lean_inc(v_num_1475_);
lean_dec_ref_known(v_presentation_1461_, 1);
v___x_1476_ = 0;
v___x_1477_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1475_, v___y_1464_, v___x_1476_);
lean_dec(v_num_1475_);
return v___x_1477_;
}
}
}
}
case 3:
{
lean_object* v_presentation_1483_; lean_object* v_snd_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; 
v_presentation_1483_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1483_);
lean_dec_ref_known(v_modifier_1434_, 1);
v_snd_1484_ = lean_ctor_get(v_data_1435_, 1);
lean_inc(v_snd_1484_);
lean_dec(v_data_1435_);
v___x_1485_ = 0;
v___x_1486_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1483_, v_snd_1484_, v___x_1485_);
lean_dec(v_presentation_1483_);
return v___x_1486_;
}
case 4:
{
lean_object* v_presentation_1487_; 
v_presentation_1487_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc_ref(v_presentation_1487_);
lean_dec_ref_known(v_modifier_1434_, 1);
if (lean_obj_tag(v_presentation_1487_) == 0)
{
lean_object* v_val_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; 
v_val_1488_ = lean_ctor_get(v_presentation_1487_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v_presentation_1487_, 1);
v___x_1489_ = 0;
v___x_1490_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1488_, v_data_1435_, v___x_1489_);
lean_dec(v_val_1488_);
return v___x_1490_;
}
else
{
lean_object* v_val_1491_; uint8_t v___x_1492_; 
v_val_1491_ = lean_ctor_get(v_presentation_1487_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v_presentation_1487_, 1);
v___x_1492_ = lean_unbox(v_val_1491_);
lean_dec(v_val_1491_);
switch(v___x_1492_)
{
case 1:
{
lean_object* v_symbols_1493_; lean_object* v___x_1494_; 
v_symbols_1493_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1494_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1493_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1494_;
}
case 2:
{
lean_object* v_symbols_1495_; lean_object* v___x_1496_; 
v_symbols_1495_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1496_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1495_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1496_;
}
default: 
{
lean_object* v_symbols_1497_; lean_object* v___x_1498_; 
v_symbols_1497_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1498_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1497_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1498_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1499_; 
v_presentation_1499_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc_ref(v_presentation_1499_);
lean_dec_ref_known(v_modifier_1434_, 1);
if (lean_obj_tag(v_presentation_1499_) == 0)
{
lean_object* v_val_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; 
v_val_1500_ = lean_ctor_get(v_presentation_1499_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v_presentation_1499_, 1);
v___x_1501_ = 0;
v___x_1502_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1500_, v_data_1435_, v___x_1501_);
lean_dec(v_val_1500_);
return v___x_1502_;
}
else
{
lean_object* v_val_1503_; uint8_t v___x_1504_; 
v_val_1503_ = lean_ctor_get(v_presentation_1499_, 0);
lean_inc(v_val_1503_);
lean_dec_ref_known(v_presentation_1499_, 1);
v___x_1504_ = lean_unbox(v_val_1503_);
lean_dec(v_val_1503_);
switch(v___x_1504_)
{
case 1:
{
lean_object* v_symbols_1505_; lean_object* v___x_1506_; 
v_symbols_1505_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1506_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1505_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1506_;
}
case 2:
{
lean_object* v_symbols_1507_; lean_object* v___x_1508_; 
v_symbols_1507_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1508_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1507_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1508_;
}
default: 
{
lean_object* v_symbols_1509_; lean_object* v___x_1510_; 
v_symbols_1509_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1510_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1509_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1510_;
}
}
}
}
case 6:
{
lean_object* v_presentation_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; 
v_presentation_1511_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1511_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1512_ = 0;
v___x_1513_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1511_, v_data_1435_, v___x_1512_);
lean_dec(v_presentation_1511_);
return v___x_1513_;
}
case 7:
{
lean_object* v_presentation_1514_; 
v_presentation_1514_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc_ref(v_presentation_1514_);
lean_dec_ref_known(v_modifier_1434_, 1);
if (lean_obj_tag(v_presentation_1514_) == 0)
{
lean_object* v_val_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; 
v_val_1515_ = lean_ctor_get(v_presentation_1514_, 0);
lean_inc(v_val_1515_);
lean_dec_ref_known(v_presentation_1514_, 1);
v___x_1516_ = 0;
v___x_1517_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1515_, v_data_1435_, v___x_1516_);
lean_dec(v_val_1515_);
return v___x_1517_;
}
else
{
lean_object* v_val_1518_; uint8_t v___x_1519_; 
v_val_1518_ = lean_ctor_get(v_presentation_1514_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v_presentation_1514_, 1);
v___x_1519_ = lean_unbox(v_val_1518_);
lean_dec(v_val_1518_);
switch(v___x_1519_)
{
case 0:
{
lean_object* v_symbols_1520_; lean_object* v___x_1521_; 
v_symbols_1520_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1521_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1520_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1521_;
}
case 1:
{
lean_object* v_symbols_1522_; lean_object* v___x_1523_; 
v_symbols_1522_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1523_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1522_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1523_;
}
case 2:
{
lean_object* v_symbols_1524_; lean_object* v___x_1525_; 
v_symbols_1524_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1525_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1524_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1525_;
}
default: 
{
lean_object* v___x_1526_; 
v___x_1526_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1526_;
}
}
}
}
case 8:
{
lean_object* v_presentation_1527_; 
v_presentation_1527_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc_ref(v_presentation_1527_);
lean_dec_ref_known(v_modifier_1434_, 1);
if (lean_obj_tag(v_presentation_1527_) == 0)
{
lean_object* v_val_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; 
v_val_1528_ = lean_ctor_get(v_presentation_1527_, 0);
lean_inc(v_val_1528_);
lean_dec_ref_known(v_presentation_1527_, 1);
v___x_1529_ = 0;
v___x_1530_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1528_, v_data_1435_, v___x_1529_);
lean_dec(v_val_1528_);
return v___x_1530_;
}
else
{
lean_object* v_val_1531_; uint8_t v___x_1532_; 
v_val_1531_ = lean_ctor_get(v_presentation_1527_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v_presentation_1527_, 1);
v___x_1532_ = lean_unbox(v_val_1531_);
lean_dec(v_val_1531_);
switch(v___x_1532_)
{
case 0:
{
lean_object* v_symbols_1533_; lean_object* v___x_1534_; 
v_symbols_1533_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1534_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1533_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1534_;
}
case 1:
{
lean_object* v_symbols_1535_; lean_object* v___x_1536_; 
v_symbols_1535_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1536_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1535_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1536_;
}
case 2:
{
lean_object* v_symbols_1537_; lean_object* v___x_1538_; 
v_symbols_1537_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1538_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1537_, v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1538_;
}
default: 
{
lean_object* v___x_1539_; 
v___x_1539_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1435_);
lean_dec(v_data_1435_);
return v___x_1539_;
}
}
}
}
case 9:
{
lean_object* v_presentation_1540_; lean_object* v___x_1541_; lean_object* v___y_1543_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_presentation_1540_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1540_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1558_ = lean_int_dec_le(v_data_1435_, v___x_1557_);
if (v___x_1558_ == 0)
{
v___y_1543_ = v_data_1435_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = lean_int_neg(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1560_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1561_ = lean_int_add(v___x_1559_, v___x_1560_);
lean_dec(v___x_1559_);
v___y_1543_ = v___x_1561_;
goto v___jp_1542_;
}
v___jp_1542_:
{
switch(lean_obj_tag(v_presentation_1540_))
{
case 0:
{
uint8_t v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = 0;
v___x_1545_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1541_, v___y_1543_, v___x_1544_);
return v___x_1545_;
}
case 1:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; 
v___x_1546_ = lean_unsigned_to_nat(2u);
v___x_1547_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1548_ = lean_int_emod(v___y_1543_, v___x_1547_);
lean_dec(v___y_1543_);
v___x_1549_ = 0;
v___x_1550_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1546_, v___x_1548_, v___x_1549_);
return v___x_1550_;
}
case 2:
{
lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = lean_unsigned_to_nat(4u);
v___x_1552_ = 0;
v___x_1553_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1551_, v___y_1543_, v___x_1552_);
return v___x_1553_;
}
default: 
{
lean_object* v_num_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
v_num_1554_ = lean_ctor_get(v_presentation_1540_, 0);
lean_inc(v_num_1554_);
lean_dec_ref_known(v_presentation_1540_, 1);
v___x_1555_ = 0;
v___x_1556_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1554_, v___y_1543_, v___x_1555_);
lean_dec(v_num_1554_);
return v___x_1556_;
}
}
}
}
case 10:
{
lean_object* v_presentation_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; 
v_presentation_1562_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1562_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1563_ = 0;
v___x_1564_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1562_, v_data_1435_, v___x_1563_);
lean_dec(v_presentation_1562_);
return v___x_1564_;
}
case 11:
{
lean_object* v_presentation_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; 
v_presentation_1565_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1565_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1566_ = 0;
v___x_1567_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1565_, v_data_1435_, v___x_1566_);
lean_dec(v_presentation_1565_);
return v___x_1567_;
}
case 12:
{
uint8_t v_presentation_1568_; 
v_presentation_1568_ = lean_ctor_get_uint8(v_modifier_1434_, 0);
lean_dec_ref_known(v_modifier_1434_, 0);
switch(v_presentation_1568_)
{
case 0:
{
lean_object* v_symbols_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; 
v_symbols_1569_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1570_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1571_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1569_, v___x_1570_);
return v___x_1571_;
}
case 1:
{
lean_object* v_symbols_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; 
v_symbols_1572_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1573_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1574_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1572_, v___x_1573_);
return v___x_1574_;
}
case 2:
{
lean_object* v_symbols_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; 
v_symbols_1575_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1576_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1577_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1575_, v___x_1576_);
return v___x_1577_;
}
default: 
{
lean_object* v_symbols_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; 
v_symbols_1578_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1579_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1580_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1578_, v___x_1579_);
return v___x_1580_;
}
}
}
case 13:
{
lean_object* v_presentation_1581_; 
v_presentation_1581_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc_ref(v_presentation_1581_);
lean_dec_ref_known(v_modifier_1434_, 1);
if (lean_obj_tag(v_presentation_1581_) == 0)
{
lean_object* v_val_1582_; uint8_t v_firstDayOfWeek_1583_; lean_object* v_firstOrd_1584_; uint8_t v___x_1585_; lean_object* v_dayOrd_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; 
v_val_1582_ = lean_ctor_get(v_presentation_1581_, 0);
lean_inc(v_val_1582_);
lean_dec_ref_known(v_presentation_1581_, 1);
v_firstDayOfWeek_1583_ = lean_ctor_get_uint8(v_dateformat_1433_, sizeof(void*)*2);
v_firstOrd_1584_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1583_);
v___x_1585_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v_dayOrd_1586_ = l_Std_Time_Weekday_toOrdinal(v___x_1585_);
v___x_1587_ = lean_int_sub(v_dayOrd_1586_, v_firstOrd_1584_);
lean_dec(v_firstOrd_1584_);
lean_dec(v_dayOrd_1586_);
v___x_1588_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1589_ = lean_int_add(v___x_1587_, v___x_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_int_emod(v___x_1589_, v___x_1588_);
lean_dec(v___x_1589_);
v___x_1591_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1592_ = lean_int_add(v___x_1590_, v___x_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = 0;
v___x_1594_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1582_, v___x_1592_, v___x_1593_);
lean_dec(v_val_1582_);
return v___x_1594_;
}
else
{
lean_object* v_val_1595_; uint8_t v___x_1596_; 
v_val_1595_ = lean_ctor_get(v_presentation_1581_, 0);
lean_inc(v_val_1595_);
lean_dec_ref_known(v_presentation_1581_, 1);
v___x_1596_ = lean_unbox(v_val_1595_);
lean_dec(v_val_1595_);
switch(v___x_1596_)
{
case 0:
{
lean_object* v_symbols_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; 
v_symbols_1597_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1598_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1599_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1597_, v___x_1598_);
return v___x_1599_;
}
case 1:
{
lean_object* v_symbols_1600_; uint8_t v___x_1601_; lean_object* v___x_1602_; 
v_symbols_1600_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1601_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1602_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1600_, v___x_1601_);
return v___x_1602_;
}
case 2:
{
lean_object* v_symbols_1603_; uint8_t v___x_1604_; lean_object* v___x_1605_; 
v_symbols_1603_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1604_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1605_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1603_, v___x_1604_);
return v___x_1605_;
}
default: 
{
lean_object* v_symbols_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; 
v_symbols_1606_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1607_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1608_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1606_, v___x_1607_);
return v___x_1608_;
}
}
}
}
case 14:
{
lean_object* v_presentation_1609_; 
v_presentation_1609_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc_ref(v_presentation_1609_);
lean_dec_ref_known(v_modifier_1434_, 1);
if (lean_obj_tag(v_presentation_1609_) == 0)
{
lean_object* v_val_1610_; uint8_t v_firstDayOfWeek_1611_; lean_object* v_firstOrd_1612_; uint8_t v___x_1613_; lean_object* v_dayOrd_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; 
v_val_1610_ = lean_ctor_get(v_presentation_1609_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v_presentation_1609_, 1);
v_firstDayOfWeek_1611_ = lean_ctor_get_uint8(v_dateformat_1433_, sizeof(void*)*2);
v_firstOrd_1612_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1611_);
v___x_1613_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v_dayOrd_1614_ = l_Std_Time_Weekday_toOrdinal(v___x_1613_);
v___x_1615_ = lean_int_sub(v_dayOrd_1614_, v_firstOrd_1612_);
lean_dec(v_firstOrd_1612_);
lean_dec(v_dayOrd_1614_);
v___x_1616_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1617_ = lean_int_add(v___x_1615_, v___x_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_int_emod(v___x_1617_, v___x_1616_);
lean_dec(v___x_1617_);
v___x_1619_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1620_ = lean_int_add(v___x_1618_, v___x_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = 0;
v___x_1622_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1610_, v___x_1620_, v___x_1621_);
lean_dec(v_val_1610_);
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; uint8_t v___x_1624_; 
v_val_1623_ = lean_ctor_get(v_presentation_1609_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v_presentation_1609_, 1);
v___x_1624_ = lean_unbox(v_val_1623_);
lean_dec(v_val_1623_);
switch(v___x_1624_)
{
case 0:
{
lean_object* v_symbols_1625_; uint8_t v___x_1626_; lean_object* v___x_1627_; 
v_symbols_1625_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1626_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1627_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1625_, v___x_1626_);
return v___x_1627_;
}
case 1:
{
lean_object* v_symbols_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; 
v_symbols_1628_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1629_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1630_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1628_, v___x_1629_);
return v___x_1630_;
}
case 2:
{
lean_object* v_symbols_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; 
v_symbols_1631_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1632_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1633_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1631_, v___x_1632_);
return v___x_1633_;
}
default: 
{
lean_object* v_symbols_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; 
v_symbols_1634_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1635_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1636_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1634_, v___x_1635_);
return v___x_1636_;
}
}
}
}
case 15:
{
lean_object* v_presentation_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; 
v_presentation_1637_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1637_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1638_ = 0;
v___x_1639_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1637_, v_data_1435_, v___x_1638_);
lean_dec(v_presentation_1637_);
return v___x_1639_;
}
case 16:
{
uint8_t v_presentation_1640_; 
v_presentation_1640_ = lean_ctor_get_uint8(v_modifier_1434_, 0);
lean_dec_ref_known(v_modifier_1434_, 0);
if (v_presentation_1640_ == 2)
{
lean_object* v_symbols_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; 
v_symbols_1641_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1642_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1643_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1641_, v___x_1642_);
return v___x_1643_;
}
else
{
lean_object* v_symbols_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; 
v_symbols_1644_ = lean_ctor_get(v_dateformat_1433_, 1);
v___x_1645_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1646_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1644_, v___x_1645_);
return v___x_1646_;
}
}
case 17:
{
uint8_t v_presentation_1647_; 
v_presentation_1647_ = lean_ctor_get_uint8(v_modifier_1434_, 0);
lean_dec_ref_known(v_modifier_1434_, 0);
switch(v_presentation_1647_)
{
case 1:
{
lean_object* v_symbols_1648_; lean_object* v_dayPeriodLong_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; 
v_symbols_1648_ = lean_ctor_get(v_dateformat_1433_, 1);
v_dayPeriodLong_1649_ = lean_ctor_get(v_symbols_1648_, 20);
v___x_1650_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1651_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodLong_1649_, v___x_1650_);
return v___x_1651_;
}
case 2:
{
lean_object* v_symbols_1652_; lean_object* v_dayPeriodNarrow_1653_; uint8_t v___x_1654_; lean_object* v___x_1655_; 
v_symbols_1652_ = lean_ctor_get(v_dateformat_1433_, 1);
v_dayPeriodNarrow_1653_ = lean_ctor_get(v_symbols_1652_, 21);
v___x_1654_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1655_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodNarrow_1653_, v___x_1654_);
return v___x_1655_;
}
default: 
{
lean_object* v_symbols_1656_; lean_object* v_dayPeriodShort_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; 
v_symbols_1656_ = lean_ctor_get(v_dateformat_1433_, 1);
v_dayPeriodShort_1657_ = lean_ctor_get(v_symbols_1656_, 19);
v___x_1658_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1659_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodShort_1657_, v___x_1658_);
return v___x_1659_;
}
}
}
case 18:
{
uint8_t v_presentation_1660_; 
v_presentation_1660_ = lean_ctor_get_uint8(v_modifier_1434_, 0);
lean_dec_ref_known(v_modifier_1434_, 0);
switch(v_presentation_1660_)
{
case 1:
{
lean_object* v_symbols_1661_; lean_object* v_extendedDayPeriodLong_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; 
v_symbols_1661_ = lean_ctor_get(v_dateformat_1433_, 1);
v_extendedDayPeriodLong_1662_ = lean_ctor_get(v_symbols_1661_, 23);
v___x_1663_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1664_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodLong_1662_, v___x_1663_);
return v___x_1664_;
}
case 2:
{
lean_object* v_symbols_1665_; lean_object* v_extendedDayPeriodNarrow_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; 
v_symbols_1665_ = lean_ctor_get(v_dateformat_1433_, 1);
v_extendedDayPeriodNarrow_1666_ = lean_ctor_get(v_symbols_1665_, 24);
v___x_1667_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1668_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodNarrow_1666_, v___x_1667_);
return v___x_1668_;
}
default: 
{
lean_object* v_symbols_1669_; lean_object* v_extendedDayPeriodShort_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; 
v_symbols_1669_ = lean_ctor_get(v_dateformat_1433_, 1);
v_extendedDayPeriodShort_1670_ = lean_ctor_get(v_symbols_1669_, 22);
v___x_1671_ = lean_unbox(v_data_1435_);
lean_dec(v_data_1435_);
v___x_1672_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodShort_1670_, v___x_1671_);
return v___x_1672_;
}
}
}
case 19:
{
lean_object* v_presentation_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; 
v_presentation_1673_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1673_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1674_ = 0;
v___x_1675_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1673_, v_data_1435_, v___x_1674_);
lean_dec(v_presentation_1673_);
return v___x_1675_;
}
case 20:
{
lean_object* v_presentation_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; 
v_presentation_1676_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1676_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1677_ = 0;
v___x_1678_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1676_, v_data_1435_, v___x_1677_);
lean_dec(v_presentation_1676_);
return v___x_1678_;
}
case 21:
{
lean_object* v_presentation_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; 
v_presentation_1679_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1679_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1680_ = 0;
v___x_1681_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1679_, v_data_1435_, v___x_1680_);
lean_dec(v_presentation_1679_);
return v___x_1681_;
}
case 22:
{
lean_object* v_presentation_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; 
v_presentation_1682_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1682_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1683_ = 0;
v___x_1684_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1682_, v_data_1435_, v___x_1683_);
lean_dec(v_presentation_1682_);
return v___x_1684_;
}
case 23:
{
lean_object* v_presentation_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; 
v_presentation_1685_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1685_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1686_ = 0;
v___x_1687_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1685_, v_data_1435_, v___x_1686_);
lean_dec(v_presentation_1685_);
return v___x_1687_;
}
case 24:
{
lean_object* v_presentation_1688_; uint8_t v___x_1689_; lean_object* v___x_1690_; 
v_presentation_1688_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1688_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1689_ = 0;
v___x_1690_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1688_, v_data_1435_, v___x_1689_);
lean_dec(v_presentation_1688_);
return v___x_1690_;
}
case 25:
{
lean_object* v_presentation_1691_; 
v_presentation_1691_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1691_);
lean_dec_ref_known(v_modifier_1434_, 1);
if (lean_obj_tag(v_presentation_1691_) == 0)
{
lean_object* v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_unsigned_to_nat(9u);
v___x_1693_ = 0;
v___x_1694_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1692_, v_data_1435_, v___x_1693_);
return v___x_1694_;
}
else
{
lean_object* v_digits_1695_; lean_object* v___x_1696_; uint32_t v___x_1697_; lean_object* v___x_1698_; lean_object* v_s_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_digits_1695_ = lean_ctor_get(v_presentation_1691_, 0);
lean_inc(v_digits_1695_);
lean_dec_ref_known(v_presentation_1691_, 1);
v___x_1696_ = lean_unsigned_to_nat(9u);
v___x_1697_ = 48;
v___x_1698_ = l_Int_repr(v_data_1435_);
lean_dec(v_data_1435_);
v_s_1699_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1696_, v___x_1697_, v___x_1698_);
v___x_1700_ = lean_unsigned_to_nat(0u);
v___x_1701_ = lean_string_utf8_byte_size(v_s_1699_);
lean_inc_ref(v_s_1699_);
v___x_1702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1702_, 0, v_s_1699_);
lean_ctor_set(v___x_1702_, 1, v___x_1700_);
lean_ctor_set(v___x_1702_, 2, v___x_1701_);
v___x_1703_ = l_String_Slice_Pos_nextn(v___x_1702_, v___x_1700_, v_digits_1695_);
lean_dec_ref_known(v___x_1702_, 3);
v___x_1704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1704_, 0, v_s_1699_);
lean_ctor_set(v___x_1704_, 1, v___x_1700_);
lean_ctor_set(v___x_1704_, 2, v___x_1703_);
v___x_1705_ = l_String_Slice_toString(v___x_1704_);
lean_dec_ref_known(v___x_1704_, 3);
return v___x_1705_;
}
}
case 26:
{
lean_object* v_presentation_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; 
v_presentation_1706_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1706_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1707_ = 0;
v___x_1708_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1706_, v_data_1435_, v___x_1707_);
lean_dec(v_presentation_1706_);
return v___x_1708_;
}
case 27:
{
lean_object* v_presentation_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; 
v_presentation_1709_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1709_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1710_ = 0;
v___x_1711_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1709_, v_data_1435_, v___x_1710_);
lean_dec(v_presentation_1709_);
return v___x_1711_;
}
case 28:
{
lean_object* v_presentation_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; 
v_presentation_1712_ = lean_ctor_get(v_modifier_1434_, 0);
lean_inc(v_presentation_1712_);
lean_dec_ref_known(v_modifier_1434_, 1);
v___x_1713_ = 0;
v___x_1714_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1712_, v_data_1435_, v___x_1713_);
lean_dec(v_presentation_1712_);
return v___x_1714_;
}
case 29:
{
uint8_t v_presentation_1715_; 
v_presentation_1715_ = lean_ctor_get_uint8(v_modifier_1434_, 0);
lean_dec_ref_known(v_modifier_1434_, 0);
if (v_presentation_1715_ == 0)
{
lean_object* v___x_1716_; 
lean_dec(v_data_1435_);
v___x_1716_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1716_;
}
else
{
return v_data_1435_;
}
}
case 32:
{
uint8_t v_presentation_1717_; 
v_presentation_1717_ = lean_ctor_get_uint8(v_modifier_1434_, 0);
lean_dec_ref_known(v_modifier_1434_, 0);
if (v_presentation_1717_ == 0)
{
lean_object* v_fst_1719_; lean_object* v_snd_1720_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1744_ = lean_int_dec_eq(v_data_1435_, v___x_1743_);
if (v___x_1744_ == 0)
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_int_dec_le(v___x_1743_, v_data_1435_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1747_ = lean_int_neg(v_data_1435_);
lean_dec(v_data_1435_);
v_fst_1719_ = v___x_1746_;
v_snd_1720_ = v___x_1747_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1719_ = v___x_1748_;
v_snd_1720_ = v_data_1435_;
goto v___jp_1718_;
}
}
else
{
lean_object* v___x_1749_; 
lean_dec(v_data_1435_);
v___x_1749_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1749_;
}
v___jp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v_t_1723_; lean_object* v_hour_1724_; lean_object* v_minute_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1721_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1722_ = lean_int_mul(v_snd_1720_, v___x_1721_);
lean_dec(v_snd_1720_);
v_t_1723_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1722_);
lean_dec(v___x_1722_);
v_hour_1724_ = lean_ctor_get(v_t_1723_, 0);
lean_inc(v_hour_1724_);
v_minute_1725_ = lean_ctor_get(v_t_1723_, 1);
lean_inc(v_minute_1725_);
lean_dec_ref(v_t_1723_);
v___x_1726_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1727_ = lean_int_dec_eq(v_minute_1725_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; uint32_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1728_ = lean_unsigned_to_nat(2u);
v___x_1729_ = 48;
v___x_1730_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1731_ = lean_string_append(v___x_1730_, v_fst_1719_);
v___x_1732_ = l_Int_repr(v_hour_1724_);
lean_dec(v_hour_1724_);
v___x_1733_ = lean_string_append(v___x_1731_, v___x_1732_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___x_1735_ = lean_string_append(v___x_1733_, v___x_1734_);
v___x_1736_ = l_Int_repr(v_minute_1725_);
lean_dec(v_minute_1725_);
v___x_1737_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1728_, v___x_1729_, v___x_1736_);
v___x_1738_ = lean_string_append(v___x_1735_, v___x_1737_);
lean_dec_ref(v___x_1737_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec(v_minute_1725_);
v___x_1739_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1740_ = lean_string_append(v___x_1739_, v_fst_1719_);
v___x_1741_ = l_Int_repr(v_hour_1724_);
lean_dec(v_hour_1724_);
v___x_1742_ = lean_string_append(v___x_1740_, v___x_1741_);
lean_dec_ref(v___x_1741_);
return v___x_1742_;
}
}
}
else
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1751_ = lean_int_dec_eq(v_data_1435_, v___x_1750_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1752_ = 1;
v___x_1753_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1754_ = 0;
v___x_1755_ = 1;
v___x_1756_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1754_, v___x_1755_, v___x_1752_, v___x_1752_);
v___x_1757_ = lean_string_append(v___x_1753_, v___x_1756_);
lean_dec_ref(v___x_1756_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; 
lean_dec(v_data_1435_);
v___x_1758_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1758_;
}
}
}
case 33:
{
uint8_t v_presentation_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v_presentation_1759_ = lean_ctor_get_uint8(v_modifier_1434_, 0);
lean_dec_ref_known(v_modifier_1434_, 0);
v___x_1760_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1761_ = lean_int_dec_eq(v_data_1435_, v___x_1760_);
if (v___x_1761_ == 0)
{
uint8_t v___x_1762_; 
v___x_1762_ = 1;
switch(v_presentation_1759_)
{
case 0:
{
uint8_t v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = 2;
v___x_1764_ = 1;
v___x_1765_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1763_, v___x_1764_, v___x_1761_, v___x_1762_);
return v___x_1765_;
}
case 1:
{
uint8_t v___x_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = 0;
v___x_1767_ = 1;
v___x_1768_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1766_, v___x_1767_, v___x_1761_, v___x_1762_);
return v___x_1768_;
}
case 2:
{
uint8_t v___x_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = 0;
v___x_1770_ = 1;
v___x_1771_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1769_, v___x_1770_, v___x_1762_, v___x_1762_);
return v___x_1771_;
}
case 3:
{
uint8_t v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = 0;
v___x_1773_ = 2;
v___x_1774_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1772_, v___x_1773_, v___x_1761_, v___x_1762_);
return v___x_1774_;
}
default: 
{
uint8_t v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = 0;
v___x_1776_ = 2;
v___x_1777_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1775_, v___x_1776_, v___x_1762_, v___x_1762_);
return v___x_1777_;
}
}
}
else
{
lean_object* v___x_1778_; 
lean_dec(v_data_1435_);
v___x_1778_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1778_;
}
}
case 34:
{
uint8_t v_presentation_1779_; 
v_presentation_1779_ = lean_ctor_get_uint8(v_modifier_1434_, 0);
lean_dec_ref_known(v_modifier_1434_, 0);
switch(v_presentation_1779_)
{
case 0:
{
uint8_t v___x_1780_; uint8_t v___x_1781_; uint8_t v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; 
v___x_1780_ = 2;
v___x_1781_ = 1;
v___x_1782_ = 0;
v___x_1783_ = 1;
v___x_1784_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1780_, v___x_1781_, v___x_1782_, v___x_1783_);
return v___x_1784_;
}
case 1:
{
uint8_t v___x_1785_; uint8_t v___x_1786_; uint8_t v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; 
v___x_1785_ = 0;
v___x_1786_ = 1;
v___x_1787_ = 0;
v___x_1788_ = 1;
v___x_1789_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1785_, v___x_1786_, v___x_1787_, v___x_1788_);
return v___x_1789_;
}
case 2:
{
uint8_t v___x_1790_; uint8_t v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1790_ = 0;
v___x_1791_ = 1;
v___x_1792_ = 1;
v___x_1793_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1790_, v___x_1791_, v___x_1792_, v___x_1792_);
return v___x_1793_;
}
case 3:
{
uint8_t v___x_1794_; uint8_t v___x_1795_; uint8_t v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; 
v___x_1794_ = 0;
v___x_1795_ = 2;
v___x_1796_ = 0;
v___x_1797_ = 1;
v___x_1798_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1794_, v___x_1795_, v___x_1796_, v___x_1797_);
return v___x_1798_;
}
default: 
{
uint8_t v___x_1799_; uint8_t v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1799_ = 0;
v___x_1800_ = 2;
v___x_1801_ = 1;
v___x_1802_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1799_, v___x_1800_, v___x_1801_, v___x_1801_);
return v___x_1802_;
}
}
}
case 35:
{
uint8_t v_presentation_1803_; 
v_presentation_1803_ = lean_ctor_get_uint8(v_modifier_1434_, 0);
lean_dec_ref_known(v_modifier_1434_, 0);
switch(v_presentation_1803_)
{
case 0:
{
uint8_t v___x_1804_; uint8_t v___x_1805_; uint8_t v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; 
v___x_1804_ = 0;
v___x_1805_ = 2;
v___x_1806_ = 0;
v___x_1807_ = 1;
v___x_1808_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1804_, v___x_1805_, v___x_1806_, v___x_1807_);
return v___x_1808_;
}
case 1:
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1810_ = lean_int_dec_eq(v_data_1435_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; uint8_t v___x_1812_; uint8_t v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1811_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1812_ = 0;
v___x_1813_ = 1;
v___x_1814_ = 1;
v___x_1815_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1812_, v___x_1813_, v___x_1814_, v___x_1814_);
v___x_1816_ = lean_string_append(v___x_1811_, v___x_1815_);
lean_dec_ref(v___x_1815_);
return v___x_1816_;
}
else
{
lean_object* v___x_1817_; 
lean_dec(v_data_1435_);
v___x_1817_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1817_;
}
}
default: 
{
lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1819_ = lean_int_dec_eq(v_data_1435_, v___x_1818_);
if (v___x_1819_ == 0)
{
uint8_t v___x_1820_; uint8_t v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1820_ = 1;
v___x_1821_ = 0;
v___x_1822_ = 2;
v___x_1823_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1435_, v___x_1821_, v___x_1822_, v___x_1820_, v___x_1820_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; 
lean_dec(v_data_1435_);
v___x_1824_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1824_;
}
}
}
}
default: 
{
lean_dec_ref(v_modifier_1434_);
return v_data_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___boxed(lean_object* v_dateformat_1825_, lean_object* v_modifier_1826_, lean_object* v_data_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_1825_, v_modifier_1826_, v_data_1827_);
lean_dec_ref(v_dateformat_1825_);
return v_res_1828_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_unsigned_to_nat(400u);
v___x_1830_ = lean_nat_to_int(v___x_1829_);
return v___x_1830_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = lean_unsigned_to_nat(4u);
v___x_1832_ = lean_nat_to_int(v___x_1831_);
return v___x_1832_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1834_ = lean_string_utf8_byte_size(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1836_ = lean_string_utf8_byte_size(v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(lean_object* v_modifier_1837_, lean_object* v_dateformat_1838_, lean_object* v_date_1839_){
_start:
{
uint8_t v___y_1841_; lean_object* v_month_1842_; lean_object* v_day_1843_; uint8_t v___y_1844_; uint8_t v___y_1850_; lean_object* v_month_1851_; lean_object* v_day_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; uint8_t v_firstDayOfWeek_1858_; lean_object* v_minimalDaysInFirstWeek_1859_; lean_object* v_date_1860_; lean_object* v_timezone_1861_; uint8_t v___y_1880_; 
v_firstDayOfWeek_1858_ = lean_ctor_get_uint8(v_dateformat_1838_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1859_ = lean_ctor_get(v_dateformat_1838_, 0);
v_date_1860_ = lean_ctor_get(v_date_1839_, 0);
v_timezone_1861_ = lean_ctor_get(v_date_1839_, 3);
switch(lean_obj_tag(v_modifier_1837_))
{
case 0:
{
lean_object* v___x_1893_; lean_object* v_date_1894_; lean_object* v_year_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1893_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc_ref(v_date_1894_);
lean_dec(v___x_1893_);
v_year_1895_ = lean_ctor_get(v_date_1894_, 0);
lean_inc(v_year_1895_);
lean_dec_ref(v_date_1894_);
v___x_1896_ = l_Std_Time_Year_Offset_era(v_year_1895_);
lean_dec(v_year_1895_);
v___x_1897_ = lean_box(v___x_1896_);
return v___x_1897_;
}
case 1:
{
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
goto v___jp_1875_;
}
case 2:
{
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
goto v___jp_1875_;
}
case 3:
{
lean_object* v___x_1898_; lean_object* v_date_1899_; lean_object* v_year_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1908_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1898_ = lean_thunk_get_own(v_date_1860_);
v_date_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc_ref(v_date_1899_);
lean_dec(v___x_1898_);
v_year_1900_ = lean_ctor_get(v_date_1899_, 0);
lean_inc(v_year_1900_);
lean_dec_ref(v_date_1899_);
v___x_1901_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1902_ = lean_int_mod(v_year_1900_, v___x_1901_);
v___x_1903_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1908_ = lean_int_dec_eq(v___x_1902_, v___x_1903_);
lean_dec(v___x_1902_);
if (v___x_1908_ == 0)
{
lean_dec(v_year_1900_);
v___y_1880_ = v___x_1908_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1909_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1910_ = lean_int_mod(v_year_1900_, v___x_1909_);
v___x_1911_ = lean_int_dec_eq(v___x_1910_, v___x_1903_);
lean_dec(v___x_1910_);
if (v___x_1911_ == 0)
{
if (v___x_1908_ == 0)
{
goto v___jp_1904_;
}
else
{
lean_dec(v_year_1900_);
v___y_1880_ = v___x_1908_;
goto v___jp_1879_;
}
}
else
{
goto v___jp_1904_;
}
}
v___jp_1904_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1905_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1906_ = lean_int_mod(v_year_1900_, v___x_1905_);
lean_dec(v_year_1900_);
v___x_1907_ = lean_int_dec_eq(v___x_1906_, v___x_1903_);
lean_dec(v___x_1906_);
v___y_1880_ = v___x_1907_;
goto v___jp_1879_;
}
}
case 4:
{
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
goto v___jp_1871_;
}
case 5:
{
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
goto v___jp_1871_;
}
case 6:
{
lean_object* v___x_1912_; lean_object* v_date_1913_; lean_object* v_day_1914_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1912_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc_ref(v_date_1913_);
lean_dec(v___x_1912_);
v_day_1914_ = lean_ctor_get(v_date_1913_, 2);
lean_inc(v_day_1914_);
lean_dec_ref(v_date_1913_);
return v_day_1914_;
}
case 7:
{
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
goto v___jp_1867_;
}
case 8:
{
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
goto v___jp_1867_;
}
case 9:
{
lean_object* v___x_1915_; lean_object* v_date_1916_; lean_object* v___x_1917_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1915_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_date_1916_);
lean_dec(v___x_1915_);
v___x_1917_ = l_Std_Time_PlainDate_weekYear(v_date_1916_, v_firstDayOfWeek_1858_, v_minimalDaysInFirstWeek_1859_);
return v___x_1917_;
}
case 10:
{
lean_object* v___x_1918_; lean_object* v_date_1919_; lean_object* v___x_1920_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1918_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc_ref(v_date_1919_);
lean_dec(v___x_1918_);
v___x_1920_ = l_Std_Time_PlainDate_weekOfYear(v_date_1919_, v_firstDayOfWeek_1858_, v_minimalDaysInFirstWeek_1859_);
return v___x_1920_;
}
case 11:
{
lean_object* v___x_1921_; lean_object* v_date_1922_; lean_object* v___x_1923_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1921_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc_ref(v_date_1922_);
lean_dec(v___x_1921_);
v___x_1923_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1922_, v_firstDayOfWeek_1858_);
return v___x_1923_;
}
case 12:
{
lean_object* v___x_1924_; lean_object* v_date_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1924_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc_ref(v_date_1925_);
lean_dec(v___x_1924_);
v___x_1926_ = l_Std_Time_PlainDate_weekday(v_date_1925_);
v___x_1927_ = lean_box(v___x_1926_);
return v___x_1927_;
}
case 13:
{
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
goto v___jp_1862_;
}
case 14:
{
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
goto v___jp_1862_;
}
case 15:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_1839_);
lean_dec_ref(v_date_1839_);
return v___x_1928_;
}
case 16:
{
lean_object* v___x_1929_; lean_object* v_time_1930_; lean_object* v_hour_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1929_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1930_ = lean_ctor_get(v___x_1929_, 1);
lean_inc_ref(v_time_1930_);
lean_dec(v___x_1929_);
v_hour_1931_ = lean_ctor_get(v_time_1930_, 0);
lean_inc(v_hour_1931_);
lean_dec_ref(v_time_1930_);
v___x_1932_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1931_);
lean_dec(v_hour_1931_);
v___x_1933_ = lean_box(v___x_1932_);
return v___x_1933_;
}
case 17:
{
lean_object* v___x_1934_; lean_object* v_time_1935_; lean_object* v_hour_1936_; lean_object* v_minute_1937_; lean_object* v_second_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1934_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
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
v___x_1939_ = l_Std_Time_classifyDayPeriod(v_hour_1936_, v_minute_1937_, v_second_1938_);
lean_dec(v_second_1938_);
lean_dec(v_minute_1937_);
lean_dec(v_hour_1936_);
v___x_1940_ = lean_box(v___x_1939_);
return v___x_1940_;
}
case 18:
{
lean_object* v___x_1941_; lean_object* v_time_1942_; lean_object* v_hour_1943_; lean_object* v_minute_1944_; lean_object* v_second_1945_; uint8_t v___x_1946_; lean_object* v___x_1947_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1941_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1942_ = lean_ctor_get(v___x_1941_, 1);
lean_inc_ref(v_time_1942_);
lean_dec(v___x_1941_);
v_hour_1943_ = lean_ctor_get(v_time_1942_, 0);
lean_inc(v_hour_1943_);
v_minute_1944_ = lean_ctor_get(v_time_1942_, 1);
lean_inc(v_minute_1944_);
v_second_1945_ = lean_ctor_get(v_time_1942_, 2);
lean_inc(v_second_1945_);
lean_dec_ref(v_time_1942_);
v___x_1946_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1943_, v_minute_1944_, v_second_1945_);
lean_dec(v_second_1945_);
lean_dec(v_minute_1944_);
lean_dec(v_hour_1943_);
v___x_1947_ = lean_box(v___x_1946_);
return v___x_1947_;
}
case 19:
{
lean_object* v___x_1948_; lean_object* v_time_1949_; lean_object* v_hour_1950_; lean_object* v___x_1951_; lean_object* v_fst_1952_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1948_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1949_ = lean_ctor_get(v___x_1948_, 1);
lean_inc_ref(v_time_1949_);
lean_dec(v___x_1948_);
v_hour_1950_ = lean_ctor_get(v_time_1949_, 0);
lean_inc(v_hour_1950_);
lean_dec_ref(v_time_1949_);
v___x_1951_ = l_Std_Time_HourMarker_toRelative(v_hour_1950_);
v_fst_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_fst_1952_);
lean_dec_ref(v___x_1951_);
return v_fst_1952_;
}
case 20:
{
lean_object* v___x_1953_; lean_object* v_time_1954_; lean_object* v_hour_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1953_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1954_ = lean_ctor_get(v___x_1953_, 1);
lean_inc_ref(v_time_1954_);
lean_dec(v___x_1953_);
v_hour_1955_ = lean_ctor_get(v_time_1954_, 0);
lean_inc(v_hour_1955_);
lean_dec_ref(v_time_1954_);
v___x_1956_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1957_ = lean_int_emod(v_hour_1955_, v___x_1956_);
lean_dec(v_hour_1955_);
return v___x_1957_;
}
case 21:
{
lean_object* v___x_1958_; lean_object* v_time_1959_; lean_object* v_hour_1960_; lean_object* v___x_1961_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1958_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1959_ = lean_ctor_get(v___x_1958_, 1);
lean_inc_ref(v_time_1959_);
lean_dec(v___x_1958_);
v_hour_1960_ = lean_ctor_get(v_time_1959_, 0);
lean_inc(v_hour_1960_);
lean_dec_ref(v_time_1959_);
v___x_1961_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1960_);
lean_dec(v_hour_1960_);
return v___x_1961_;
}
case 22:
{
lean_object* v___x_1962_; lean_object* v_time_1963_; lean_object* v_hour_1964_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1962_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1963_ = lean_ctor_get(v___x_1962_, 1);
lean_inc_ref(v_time_1963_);
lean_dec(v___x_1962_);
v_hour_1964_ = lean_ctor_get(v_time_1963_, 0);
lean_inc(v_hour_1964_);
lean_dec_ref(v_time_1963_);
return v_hour_1964_;
}
case 23:
{
lean_object* v___x_1965_; lean_object* v_time_1966_; lean_object* v_minute_1967_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1965_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1966_ = lean_ctor_get(v___x_1965_, 1);
lean_inc_ref(v_time_1966_);
lean_dec(v___x_1965_);
v_minute_1967_ = lean_ctor_get(v_time_1966_, 1);
lean_inc(v_minute_1967_);
lean_dec_ref(v_time_1966_);
return v_minute_1967_;
}
case 24:
{
lean_object* v___x_1968_; lean_object* v_time_1969_; lean_object* v_second_1970_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1968_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1969_ = lean_ctor_get(v___x_1968_, 1);
lean_inc_ref(v_time_1969_);
lean_dec(v___x_1968_);
v_second_1970_ = lean_ctor_get(v_time_1969_, 2);
lean_inc(v_second_1970_);
lean_dec_ref(v_time_1969_);
return v_second_1970_;
}
case 25:
{
lean_object* v___x_1971_; lean_object* v_time_1972_; lean_object* v_nanosecond_1973_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1971_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1972_ = lean_ctor_get(v___x_1971_, 1);
lean_inc_ref(v_time_1972_);
lean_dec(v___x_1971_);
v_nanosecond_1973_ = lean_ctor_get(v_time_1972_, 3);
lean_inc(v_nanosecond_1973_);
lean_dec_ref(v_time_1972_);
return v_nanosecond_1973_;
}
case 26:
{
lean_object* v___x_1974_; lean_object* v_time_1975_; lean_object* v___x_1976_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1974_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1975_ = lean_ctor_get(v___x_1974_, 1);
lean_inc_ref(v_time_1975_);
lean_dec(v___x_1974_);
v___x_1976_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1975_);
lean_dec_ref(v_time_1975_);
return v___x_1976_;
}
case 27:
{
lean_object* v___x_1977_; lean_object* v_time_1978_; lean_object* v_nanosecond_1979_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1977_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1978_ = lean_ctor_get(v___x_1977_, 1);
lean_inc_ref(v_time_1978_);
lean_dec(v___x_1977_);
v_nanosecond_1979_ = lean_ctor_get(v_time_1978_, 3);
lean_inc(v_nanosecond_1979_);
lean_dec_ref(v_time_1978_);
return v_nanosecond_1979_;
}
case 28:
{
lean_object* v___x_1980_; lean_object* v_time_1981_; lean_object* v___x_1982_; 
lean_inc_ref(v_date_1860_);
lean_dec_ref(v_date_1839_);
v___x_1980_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_time_1981_ = lean_ctor_get(v___x_1980_, 1);
lean_inc_ref(v_time_1981_);
lean_dec(v___x_1980_);
v___x_1982_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1981_);
lean_dec_ref(v_time_1981_);
return v___x_1982_;
}
case 29:
{
uint8_t v_presentation_1983_; 
lean_inc_ref(v_timezone_1861_);
lean_dec_ref(v_date_1839_);
v_presentation_1983_ = lean_ctor_get_uint8(v_modifier_1837_, 0);
if (v_presentation_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_dec_ref(v_timezone_1861_);
v___x_1984_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1984_;
}
else
{
lean_object* v_offset_1985_; lean_object* v_name_1986_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v_offset_1985_ = lean_ctor_get(v_timezone_1861_, 0);
lean_inc(v_offset_1985_);
v_name_1986_ = lean_ctor_get(v_timezone_1861_, 1);
lean_inc_ref(v_name_1986_);
lean_dec_ref(v_timezone_1861_);
v___x_2001_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2002_ = lean_string_utf8_byte_size(v_name_1986_);
v___x_2003_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2004_ = lean_nat_dec_le(v___x_2003_, v___x_2002_);
if (v___x_2004_ == 0)
{
goto v___jp_1994_;
}
else
{
lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = lean_string_memcmp(v_name_1986_, v___x_2001_, v___x_2005_, v___x_2005_, v___x_2003_);
if (v___x_2006_ == 0)
{
goto v___jp_1994_;
}
else
{
lean_dec_ref(v_name_1986_);
goto v___jp_1987_;
}
}
v___jp_1987_:
{
uint8_t v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1988_ = 1;
v___x_1989_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1990_ = 0;
v___x_1991_ = 1;
v___x_1992_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1985_, v___x_1990_, v___x_1991_, v___x_1988_, v___x_1988_);
v___x_1993_ = lean_string_append(v___x_1989_, v___x_1992_);
lean_dec_ref(v___x_1992_);
return v___x_1993_;
}
v___jp_1994_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1995_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1996_ = lean_string_utf8_byte_size(v_name_1986_);
v___x_1997_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_1998_ = lean_nat_dec_le(v___x_1997_, v___x_1996_);
if (v___x_1998_ == 0)
{
lean_dec(v_offset_1985_);
return v_name_1986_;
}
else
{
lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = lean_unsigned_to_nat(0u);
v___x_2000_ = lean_string_memcmp(v_name_1986_, v___x_1995_, v___x_1999_, v___x_1999_, v___x_1997_);
if (v___x_2000_ == 0)
{
lean_dec(v_offset_1985_);
return v_name_1986_;
}
else
{
lean_dec_ref(v_name_1986_);
goto v___jp_1987_;
}
}
}
}
}
case 30:
{
uint8_t v_presentation_2007_; 
lean_inc_ref(v_timezone_1861_);
lean_dec_ref(v_date_1839_);
v_presentation_2007_ = lean_ctor_get_uint8(v_modifier_1837_, 0);
if (v_presentation_2007_ == 0)
{
lean_object* v_offset_2008_; lean_object* v_abbreviation_2009_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_offset_2008_ = lean_ctor_get(v_timezone_1861_, 0);
lean_inc(v_offset_2008_);
v_abbreviation_2009_ = lean_ctor_get(v_timezone_1861_, 2);
lean_inc_ref(v_abbreviation_2009_);
lean_dec_ref(v_timezone_1861_);
v___x_2024_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2025_ = lean_string_utf8_byte_size(v_abbreviation_2009_);
v___x_2026_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2027_ = lean_nat_dec_le(v___x_2026_, v___x_2025_);
if (v___x_2027_ == 0)
{
goto v___jp_2017_;
}
else
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = lean_string_memcmp(v_abbreviation_2009_, v___x_2024_, v___x_2028_, v___x_2028_, v___x_2026_);
if (v___x_2029_ == 0)
{
goto v___jp_2017_;
}
else
{
lean_dec_ref(v_abbreviation_2009_);
goto v___jp_2010_;
}
}
v___jp_2010_:
{
uint8_t v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2011_ = 1;
v___x_2012_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2013_ = 0;
v___x_2014_ = 1;
v___x_2015_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2008_, v___x_2013_, v___x_2014_, v___x_2011_, v___x_2011_);
v___x_2016_ = lean_string_append(v___x_2012_, v___x_2015_);
lean_dec_ref(v___x_2015_);
return v___x_2016_;
}
v___jp_2017_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2018_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2019_ = lean_string_utf8_byte_size(v_abbreviation_2009_);
v___x_2020_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2021_ = lean_nat_dec_le(v___x_2020_, v___x_2019_);
if (v___x_2021_ == 0)
{
lean_dec(v_offset_2008_);
return v_abbreviation_2009_;
}
else
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = lean_unsigned_to_nat(0u);
v___x_2023_ = lean_string_memcmp(v_abbreviation_2009_, v___x_2018_, v___x_2022_, v___x_2022_, v___x_2020_);
if (v___x_2023_ == 0)
{
lean_dec(v_offset_2008_);
return v_abbreviation_2009_;
}
else
{
lean_dec_ref(v_abbreviation_2009_);
goto v___jp_2010_;
}
}
}
}
else
{
lean_object* v_offset_2030_; lean_object* v_name_2031_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_offset_2030_ = lean_ctor_get(v_timezone_1861_, 0);
lean_inc(v_offset_2030_);
v_name_2031_ = lean_ctor_get(v_timezone_1861_, 1);
lean_inc_ref(v_name_2031_);
lean_dec_ref(v_timezone_1861_);
v___x_2046_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2047_ = lean_string_utf8_byte_size(v_name_2031_);
v___x_2048_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2049_ = lean_nat_dec_le(v___x_2048_, v___x_2047_);
if (v___x_2049_ == 0)
{
goto v___jp_2039_;
}
else
{
lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = lean_string_memcmp(v_name_2031_, v___x_2046_, v___x_2050_, v___x_2050_, v___x_2048_);
if (v___x_2051_ == 0)
{
goto v___jp_2039_;
}
else
{
lean_dec_ref(v_name_2031_);
goto v___jp_2032_;
}
}
v___jp_2032_:
{
uint8_t v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; uint8_t v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2033_ = 1;
v___x_2034_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2035_ = 0;
v___x_2036_ = 1;
v___x_2037_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2030_, v___x_2035_, v___x_2036_, v___x_2033_, v___x_2033_);
v___x_2038_ = lean_string_append(v___x_2034_, v___x_2037_);
lean_dec_ref(v___x_2037_);
return v___x_2038_;
}
v___jp_2039_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2040_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2041_ = lean_string_utf8_byte_size(v_name_2031_);
v___x_2042_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2043_ = lean_nat_dec_le(v___x_2042_, v___x_2041_);
if (v___x_2043_ == 0)
{
lean_dec(v_offset_2030_);
return v_name_2031_;
}
else
{
lean_object* v___x_2044_; uint8_t v___x_2045_; 
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = lean_string_memcmp(v_name_2031_, v___x_2040_, v___x_2044_, v___x_2044_, v___x_2042_);
if (v___x_2045_ == 0)
{
lean_dec(v_offset_2030_);
return v_name_2031_;
}
else
{
lean_dec_ref(v_name_2031_);
goto v___jp_2032_;
}
}
}
}
}
case 31:
{
uint8_t v_presentation_2052_; 
lean_inc_ref(v_timezone_1861_);
lean_dec_ref(v_date_1839_);
v_presentation_2052_ = lean_ctor_get_uint8(v_modifier_1837_, 0);
if (v_presentation_2052_ == 0)
{
lean_object* v_offset_2053_; lean_object* v_abbreviation_2054_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v_offset_2053_ = lean_ctor_get(v_timezone_1861_, 0);
lean_inc(v_offset_2053_);
v_abbreviation_2054_ = lean_ctor_get(v_timezone_1861_, 2);
lean_inc_ref(v_abbreviation_2054_);
lean_dec_ref(v_timezone_1861_);
v___x_2069_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2070_ = lean_string_utf8_byte_size(v_abbreviation_2054_);
v___x_2071_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2072_ = lean_nat_dec_le(v___x_2071_, v___x_2070_);
if (v___x_2072_ == 0)
{
goto v___jp_2062_;
}
else
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = lean_string_memcmp(v_abbreviation_2054_, v___x_2069_, v___x_2073_, v___x_2073_, v___x_2071_);
if (v___x_2074_ == 0)
{
goto v___jp_2062_;
}
else
{
lean_dec_ref(v_abbreviation_2054_);
goto v___jp_2055_;
}
}
v___jp_2055_:
{
uint8_t v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2056_ = 1;
v___x_2057_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2058_ = 0;
v___x_2059_ = 1;
v___x_2060_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2053_, v___x_2058_, v___x_2059_, v___x_2056_, v___x_2056_);
v___x_2061_ = lean_string_append(v___x_2057_, v___x_2060_);
lean_dec_ref(v___x_2060_);
return v___x_2061_;
}
v___jp_2062_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2063_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2064_ = lean_string_utf8_byte_size(v_abbreviation_2054_);
v___x_2065_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2066_ = lean_nat_dec_le(v___x_2065_, v___x_2064_);
if (v___x_2066_ == 0)
{
lean_dec(v_offset_2053_);
return v_abbreviation_2054_;
}
else
{
lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = lean_string_memcmp(v_abbreviation_2054_, v___x_2063_, v___x_2067_, v___x_2067_, v___x_2065_);
if (v___x_2068_ == 0)
{
lean_dec(v_offset_2053_);
return v_abbreviation_2054_;
}
else
{
lean_dec_ref(v_abbreviation_2054_);
goto v___jp_2055_;
}
}
}
}
else
{
lean_object* v_offset_2075_; lean_object* v_name_2076_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_offset_2075_ = lean_ctor_get(v_timezone_1861_, 0);
lean_inc(v_offset_2075_);
v_name_2076_ = lean_ctor_get(v_timezone_1861_, 1);
lean_inc_ref(v_name_2076_);
lean_dec_ref(v_timezone_1861_);
v___x_2091_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2092_ = lean_string_utf8_byte_size(v_name_2076_);
v___x_2093_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2094_ = lean_nat_dec_le(v___x_2093_, v___x_2092_);
if (v___x_2094_ == 0)
{
goto v___jp_2084_;
}
else
{
lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_string_memcmp(v_name_2076_, v___x_2091_, v___x_2095_, v___x_2095_, v___x_2093_);
if (v___x_2096_ == 0)
{
goto v___jp_2084_;
}
else
{
lean_dec_ref(v_name_2076_);
goto v___jp_2077_;
}
}
v___jp_2077_:
{
uint8_t v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; uint8_t v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2078_ = 1;
v___x_2079_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2080_ = 0;
v___x_2081_ = 1;
v___x_2082_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2075_, v___x_2080_, v___x_2081_, v___x_2078_, v___x_2078_);
v___x_2083_ = lean_string_append(v___x_2079_, v___x_2082_);
lean_dec_ref(v___x_2082_);
return v___x_2083_;
}
v___jp_2084_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2085_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2086_ = lean_string_utf8_byte_size(v_name_2076_);
v___x_2087_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2088_ = lean_nat_dec_le(v___x_2087_, v___x_2086_);
if (v___x_2088_ == 0)
{
lean_dec(v_offset_2075_);
return v_name_2076_;
}
else
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_string_memcmp(v_name_2076_, v___x_2085_, v___x_2089_, v___x_2089_, v___x_2087_);
if (v___x_2090_ == 0)
{
lean_dec(v_offset_2075_);
return v_name_2076_;
}
else
{
lean_dec_ref(v_name_2076_);
goto v___jp_2077_;
}
}
}
}
}
default: 
{
lean_object* v_offset_2097_; 
lean_inc_ref(v_timezone_1861_);
lean_dec_ref(v_date_1839_);
v_offset_2097_ = lean_ctor_get(v_timezone_1861_, 0);
lean_inc(v_offset_2097_);
lean_dec_ref(v_timezone_1861_);
return v_offset_2097_;
}
}
v___jp_1840_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_month_1842_);
lean_ctor_set(v___x_1845_, 1, v_day_1843_);
v___x_1846_ = l_Std_Time_ValidDate_dayOfYear(v___y_1844_, v___x_1845_);
lean_dec_ref_known(v___x_1845_, 2);
v___x_1847_ = lean_box(v___y_1841_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v___x_1846_);
return v___x_1848_;
}
v___jp_1849_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1855_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1856_ = lean_int_mod(v___y_1854_, v___x_1855_);
lean_dec(v___y_1854_);
v___x_1857_ = lean_int_dec_eq(v___x_1856_, v___y_1853_);
lean_dec(v___x_1856_);
v___y_1841_ = v___y_1850_;
v_month_1842_ = v_month_1851_;
v_day_1843_ = v_day_1852_;
v___y_1844_ = v___x_1857_;
goto v___jp_1840_;
}
v___jp_1862_:
{
lean_object* v___x_1863_; lean_object* v_date_1864_; uint8_t v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc_ref(v_date_1864_);
lean_dec(v___x_1863_);
v___x_1865_ = l_Std_Time_PlainDate_weekday(v_date_1864_);
v___x_1866_ = lean_box(v___x_1865_);
return v___x_1866_;
}
v___jp_1867_:
{
lean_object* v___x_1868_; lean_object* v_date_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc_ref(v_date_1869_);
lean_dec(v___x_1868_);
v___x_1870_ = l_Std_Time_PlainDate_quarter(v_date_1869_);
lean_dec_ref(v_date_1869_);
return v___x_1870_;
}
v___jp_1871_:
{
lean_object* v___x_1872_; lean_object* v_date_1873_; lean_object* v_month_1874_; 
v___x_1872_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc_ref(v_date_1873_);
lean_dec(v___x_1872_);
v_month_1874_ = lean_ctor_get(v_date_1873_, 1);
lean_inc(v_month_1874_);
lean_dec_ref(v_date_1873_);
return v_month_1874_;
}
v___jp_1875_:
{
lean_object* v___x_1876_; lean_object* v_date_1877_; lean_object* v_year_1878_; 
v___x_1876_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc_ref(v_date_1877_);
lean_dec(v___x_1876_);
v_year_1878_ = lean_ctor_get(v_date_1877_, 0);
lean_inc(v_year_1878_);
lean_dec_ref(v_date_1877_);
return v_year_1878_;
}
v___jp_1879_:
{
lean_object* v___x_1881_; lean_object* v_date_1882_; lean_object* v_year_1883_; lean_object* v_month_1884_; lean_object* v_day_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1881_ = lean_thunk_get_own(v_date_1860_);
lean_dec_ref(v_date_1860_);
v_date_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc_ref(v_date_1882_);
lean_dec(v___x_1881_);
v_year_1883_ = lean_ctor_get(v_date_1882_, 0);
lean_inc(v_year_1883_);
v_month_1884_ = lean_ctor_get(v_date_1882_, 1);
lean_inc(v_month_1884_);
v_day_1885_ = lean_ctor_get(v_date_1882_, 2);
lean_inc(v_day_1885_);
lean_dec_ref(v_date_1882_);
v___x_1886_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1887_ = lean_int_mod(v_year_1883_, v___x_1886_);
v___x_1888_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1889_ = lean_int_dec_eq(v___x_1887_, v___x_1888_);
lean_dec(v___x_1887_);
if (v___x_1889_ == 0)
{
lean_dec(v_year_1883_);
v___y_1841_ = v___y_1880_;
v_month_1842_ = v_month_1884_;
v_day_1843_ = v_day_1885_;
v___y_1844_ = v___x_1889_;
goto v___jp_1840_;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1890_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1891_ = lean_int_mod(v_year_1883_, v___x_1890_);
v___x_1892_ = lean_int_dec_eq(v___x_1891_, v___x_1888_);
lean_dec(v___x_1891_);
if (v___x_1892_ == 0)
{
if (v___x_1889_ == 0)
{
v___y_1850_ = v___y_1880_;
v_month_1851_ = v_month_1884_;
v_day_1852_ = v_day_1885_;
v___y_1853_ = v___x_1888_;
v___y_1854_ = v_year_1883_;
goto v___jp_1849_;
}
else
{
lean_dec(v_year_1883_);
v___y_1841_ = v___y_1880_;
v_month_1842_ = v_month_1884_;
v_day_1843_ = v_day_1885_;
v___y_1844_ = v___x_1889_;
goto v___jp_1840_;
}
}
else
{
v___y_1850_ = v___y_1880_;
v_month_1851_ = v_month_1884_;
v_day_1852_ = v_day_1885_;
v___y_1853_ = v___x_1888_;
v___y_1854_ = v_year_1883_;
goto v___jp_1849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___boxed(lean_object* v_modifier_2098_, lean_object* v_dateformat_2099_, lean_object* v_date_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_2098_, v_dateformat_2099_, v_date_2100_);
lean_dec_ref(v_dateformat_2099_);
lean_dec_ref(v_modifier_2098_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0(lean_object* v___x_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
v___x_2105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___y_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0(lean_object* v___x_2106_, lean_object* v_b_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___x_2111_; 
v_fst_2109_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_fst_2109_);
v_snd_2110_ = lean_ctor_get(v___x_2106_, 1);
lean_inc(v_snd_2110_);
lean_dec_ref(v___x_2106_);
lean_inc_ref(v___y_2108_);
v___x_2111_ = lean_apply_1(v_b_2107_, v___y_2108_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec_ref(v___y_2108_);
return v___x_2111_;
}
else
{
lean_object* v_pos_2112_; lean_object* v_snd_2113_; lean_object* v_snd_2114_; uint8_t v___x_2115_; 
v_pos_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_pos_2112_);
v_snd_2113_ = lean_ctor_get(v___y_2108_, 1);
lean_inc(v_snd_2113_);
lean_dec_ref(v___y_2108_);
v_snd_2114_ = lean_ctor_get(v_pos_2112_, 1);
v___x_2115_ = lean_nat_dec_eq(v_snd_2113_, v_snd_2114_);
lean_dec(v_snd_2113_);
if (v___x_2115_ == 0)
{
lean_dec(v_pos_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
return v___x_2111_;
}
else
{
lean_object* v___x_2116_; 
lean_dec_ref_known(v___x_2111_, 2);
v___x_2116_ = l_Std_Internal_Parsec_String_pstring(v_fst_2109_, v_pos_2112_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_pos_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
v_pos_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; 
v_unused_2125_ = lean_ctor_get(v___x_2116_, 1);
lean_dec(v_unused_2125_);
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_pos_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v_snd_2110_);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_pos_2117_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_snd_2110_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
else
{
lean_object* v_pos_2126_; lean_object* v_err_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_snd_2110_);
v_pos_2126_ = lean_ctor_get(v___x_2116_, 0);
v_err_2127_ = lean_ctor_get(v___x_2116_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2116_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_err_2127_);
lean_inc(v_pos_2126_);
lean_dec(v___x_2116_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_pos_2126_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_err_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(lean_object* v_as_2135_, size_t v_i_2136_, size_t v_stop_2137_, lean_object* v_b_2138_, lean_object* v___y_2139_){
_start:
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_usize_dec_eq(v_i_2136_, v_stop_2137_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___f_2142_; size_t v___x_2143_; size_t v___x_2144_; 
v___x_2141_ = lean_array_uget_borrowed(v_as_2135_, v_i_2136_);
lean_inc(v___x_2141_);
v___f_2142_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2142_, 0, v___x_2141_);
lean_closure_set(v___f_2142_, 1, v_b_2138_);
v___x_2143_ = ((size_t)1ULL);
v___x_2144_ = lean_usize_add(v_i_2136_, v___x_2143_);
v_i_2136_ = v___x_2144_;
v_b_2138_ = v___f_2142_;
goto _start;
}
else
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_apply_1(v_b_2138_, v___y_2139_);
return v___x_2146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___boxed(lean_object* v_as_2147_, lean_object* v_i_2148_, lean_object* v_stop_2149_, lean_object* v_b_2150_, lean_object* v___y_2151_){
_start:
{
size_t v_i_boxed_2152_; size_t v_stop_boxed_2153_; lean_object* v_res_2154_; 
v_i_boxed_2152_ = lean_unbox_usize(v_i_2148_);
lean_dec(v_i_2148_);
v_stop_boxed_2153_ = lean_unbox_usize(v_stop_2149_);
lean_dec(v_stop_2149_);
v_res_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2147_, v_i_boxed_2152_, v_stop_boxed_2153_, v_b_2150_, v___y_2151_);
lean_dec_ref(v_as_2147_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(lean_object* v_pairs_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = lean_array_get_size(v_pairs_2160_);
v___x_2164_ = lean_nat_dec_lt(v___x_2162_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2166_, 0, v_a_2161_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
return v___x_2166_;
}
else
{
lean_object* v___f_2167_; uint8_t v___x_2168_; 
v___f_2167_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2));
v___x_2168_ = lean_nat_dec_le(v___x_2163_, v___x_2163_);
if (v___x_2168_ == 0)
{
if (v___x_2164_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2170_, 0, v_a_2161_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
return v___x_2170_;
}
else
{
size_t v___x_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = lean_usize_of_nat(v___x_2163_);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2160_, v___x_2171_, v___x_2172_, v___f_2167_, v_a_2161_);
return v___x_2173_;
}
}
else
{
size_t v___x_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((size_t)0ULL);
v___x_2175_ = lean_usize_of_nat(v___x_2163_);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2160_, v___x_2174_, v___x_2175_, v___f_2167_, v_a_2161_);
return v___x_2176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___boxed(lean_object* v_pairs_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2177_, v_a_2178_);
lean_dec_ref(v_pairs_2177_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(lean_object* v_00_u03b1_2180_, lean_object* v_pairs_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2181_, v_a_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___boxed(lean_object* v_00_u03b1_2184_, lean_object* v_pairs_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(v_00_u03b1_2184_, v_pairs_2185_, v_a_2186_);
lean_dec_ref(v_pairs_2185_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_object* v_00_u03b1_2188_, lean_object* v_as_2189_, size_t v_i_2190_, size_t v_stop_2191_, lean_object* v_b_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2189_, v_i_2190_, v_stop_2191_, v_b_2192_, v___y_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___boxed(lean_object* v_00_u03b1_2195_, lean_object* v_as_2196_, lean_object* v_i_2197_, lean_object* v_stop_2198_, lean_object* v_b_2199_, lean_object* v___y_2200_){
_start:
{
size_t v_i_boxed_2201_; size_t v_stop_boxed_2202_; lean_object* v_res_2203_; 
v_i_boxed_2201_ = lean_unbox_usize(v_i_2197_);
lean_dec(v_i_2197_);
v_stop_boxed_2202_ = lean_unbox_usize(v_stop_2198_);
lean_dec(v_stop_2198_);
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(v_00_u03b1_2195_, v_as_2196_, v_i_boxed_2201_, v_stop_boxed_2202_, v_b_2199_, v___y_2200_);
lean_dec_ref(v_as_2196_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(size_t v_sz_2204_, size_t v_i_2205_, lean_object* v_bs_2206_){
_start:
{
uint8_t v___x_2207_; 
v___x_2207_ = lean_usize_dec_lt(v_i_2205_, v_sz_2204_);
if (v___x_2207_ == 0)
{
return v_bs_2206_;
}
else
{
lean_object* v_v_2208_; lean_object* v___x_2209_; lean_object* v_bs_x27_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; lean_object* v___x_2218_; 
v_v_2208_ = lean_array_uget(v_bs_2206_, v_i_2205_);
v___x_2209_ = lean_unsigned_to_nat(0u);
v_bs_x27_2210_ = lean_array_uset(v_bs_2206_, v_i_2205_, v___x_2209_);
v___x_2211_ = lean_usize_to_nat(v_i_2205_);
v___x_2212_ = lean_nat_to_int(v___x_2211_);
v___x_2213_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2214_ = lean_int_add(v___x_2212_, v___x_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_v_2208_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = ((size_t)1ULL);
v___x_2217_ = lean_usize_add(v_i_2205_, v___x_2216_);
v___x_2218_ = lean_array_uset(v_bs_x27_2210_, v_i_2205_, v___x_2215_);
v_i_2205_ = v___x_2217_;
v_bs_2206_ = v___x_2218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2220_, lean_object* v_i_2221_, lean_object* v_bs_2222_){
_start:
{
size_t v_sz_boxed_2223_; size_t v_i_boxed_2224_; lean_object* v_res_2225_; 
v_sz_boxed_2223_ = lean_unbox_usize(v_sz_2220_);
lean_dec(v_sz_2220_);
v_i_boxed_2224_ = lean_unbox_usize(v_i_2221_);
lean_dec(v_i_2221_);
v_res_2225_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_boxed_2223_, v_i_boxed_2224_, v_bs_2222_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(lean_object* v_as_2226_, size_t v_sz_2227_, size_t v_i_2228_, lean_object* v_bs_2229_){
_start:
{
uint8_t v___x_2230_; 
v___x_2230_ = lean_usize_dec_lt(v_i_2228_, v_sz_2227_);
if (v___x_2230_ == 0)
{
return v_bs_2229_;
}
else
{
lean_object* v_v_2231_; lean_object* v___x_2232_; lean_object* v_bs_x27_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; size_t v___x_2239_; size_t v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v_v_2231_ = lean_array_uget(v_bs_2229_, v_i_2228_);
v___x_2232_ = lean_unsigned_to_nat(0u);
v_bs_x27_2233_ = lean_array_uset(v_bs_2229_, v_i_2228_, v___x_2232_);
v___x_2234_ = lean_usize_to_nat(v_i_2228_);
v___x_2235_ = lean_nat_to_int(v___x_2234_);
v___x_2236_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2237_ = lean_int_add(v___x_2235_, v___x_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_v_2231_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = ((size_t)1ULL);
v___x_2240_ = lean_usize_add(v_i_2228_, v___x_2239_);
v___x_2241_ = lean_array_uset(v_bs_x27_2233_, v_i_2228_, v___x_2238_);
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2227_, v___x_2240_, v___x_2241_);
return v___x_2242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0___boxed(lean_object* v_as_2243_, lean_object* v_sz_2244_, lean_object* v_i_2245_, lean_object* v_bs_2246_){
_start:
{
size_t v_sz_boxed_2247_; size_t v_i_boxed_2248_; lean_object* v_res_2249_; 
v_sz_boxed_2247_ = lean_unbox_usize(v_sz_2244_);
lean_dec(v_sz_2244_);
v_i_boxed_2248_ = lean_unbox_usize(v_i_2245_);
lean_dec(v_i_2245_);
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_as_2243_, v_sz_boxed_2247_, v_i_boxed_2248_, v_bs_2246_);
lean_dec_ref(v_as_2243_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(lean_object* v_arr_2250_){
_start:
{
size_t v_sz_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
v_sz_2251_ = lean_array_size(v_arr_2250_);
v___x_2252_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2250_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2250_, v_sz_2251_, v___x_2252_, v_arr_2250_);
lean_dec_ref(v_arr_2250_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(lean_object* v_as_2254_, size_t v_sz_2255_, size_t v_i_2256_, lean_object* v_bs_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2255_, v_i_2256_, v_bs_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___boxed(lean_object* v_as_2259_, lean_object* v_sz_2260_, lean_object* v_i_2261_, lean_object* v_bs_2262_){
_start:
{
size_t v_sz_boxed_2263_; size_t v_i_boxed_2264_; lean_object* v_res_2265_; 
v_sz_boxed_2263_ = lean_unbox_usize(v_sz_2260_);
lean_dec(v_sz_2260_);
v_i_boxed_2264_ = lean_unbox_usize(v_i_2261_);
lean_dec(v_i_2261_);
v_res_2265_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(v_as_2259_, v_sz_boxed_2263_, v_i_boxed_2264_, v_bs_2262_);
lean_dec_ref(v_as_2259_);
return v_res_2265_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object* v_x_2266_){
_start:
{
lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = lean_nat_dec_eq(v_x_2266_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = lean_unsigned_to_nat(1u);
v___x_2270_ = lean_nat_dec_eq(v_x_2266_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = lean_unsigned_to_nat(2u);
v___x_2272_ = lean_nat_dec_eq(v_x_2266_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(3u);
v___x_2274_ = lean_nat_dec_eq(v_x_2266_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = lean_unsigned_to_nat(4u);
v___x_2276_ = lean_nat_dec_eq(v_x_2266_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = lean_unsigned_to_nat(5u);
v___x_2278_ = lean_nat_dec_eq(v_x_2266_, v___x_2277_);
if (v___x_2278_ == 0)
{
uint8_t v___x_2279_; 
v___x_2279_ = 5;
return v___x_2279_;
}
else
{
uint8_t v___x_2280_; 
v___x_2280_ = 4;
return v___x_2280_;
}
}
else
{
uint8_t v___x_2281_; 
v___x_2281_ = 3;
return v___x_2281_;
}
}
else
{
uint8_t v___x_2282_; 
v___x_2282_ = 2;
return v___x_2282_;
}
}
else
{
uint8_t v___x_2283_; 
v___x_2283_ = 1;
return v___x_2283_;
}
}
else
{
uint8_t v___x_2284_; 
v___x_2284_ = 0;
return v___x_2284_;
}
}
else
{
uint8_t v___x_2285_; 
v___x_2285_ = 6;
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object* v_x_2286_){
_start:
{
uint8_t v_res_2287_; lean_object* v_r_2288_; 
v_res_2287_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_x_2286_);
lean_dec(v_x_2286_);
v_r_2288_ = lean_box(v_res_2287_);
return v_r_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(size_t v_sz_2289_, size_t v_i_2290_, lean_object* v_bs_2291_){
_start:
{
uint8_t v___x_2292_; 
v___x_2292_ = lean_usize_dec_lt(v_i_2290_, v_sz_2289_);
if (v___x_2292_ == 0)
{
return v_bs_2291_;
}
else
{
lean_object* v_v_2293_; lean_object* v___x_2294_; lean_object* v_bs_x27_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; size_t v___x_2303_; size_t v___x_2304_; lean_object* v___x_2305_; 
v_v_2293_ = lean_array_uget(v_bs_2291_, v_i_2290_);
v___x_2294_ = lean_unsigned_to_nat(0u);
v_bs_x27_2295_ = lean_array_uset(v_bs_2291_, v_i_2290_, v___x_2294_);
v___x_2296_ = lean_usize_to_nat(v_i_2290_);
v___x_2297_ = lean_nat_to_int(v___x_2296_);
v___x_2298_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2299_ = lean_int_add(v___x_2297_, v___x_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = l_Std_Time_Weekday_ofOrdinal(v___x_2299_);
lean_dec(v___x_2299_);
v___x_2301_ = lean_box(v___x_2300_);
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v_v_2293_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = ((size_t)1ULL);
v___x_2304_ = lean_usize_add(v_i_2290_, v___x_2303_);
v___x_2305_ = lean_array_uset(v_bs_x27_2295_, v_i_2290_, v___x_2302_);
v_i_2290_ = v___x_2304_;
v_bs_2291_ = v___x_2305_;
goto _start;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(lean_object* v_as_2313_, size_t v_sz_2314_, size_t v_i_2315_, lean_object* v_bs_2316_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0___boxed(lean_object* v_as_2332_, lean_object* v_sz_2333_, lean_object* v_i_2334_, lean_object* v_bs_2335_){
_start:
{
size_t v_sz_boxed_2336_; size_t v_i_boxed_2337_; lean_object* v_res_2338_; 
v_sz_boxed_2336_ = lean_unbox_usize(v_sz_2333_);
lean_dec(v_sz_2333_);
v_i_boxed_2337_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_as_2332_, v_sz_boxed_2336_, v_i_boxed_2337_, v_bs_2335_);
lean_dec_ref(v_as_2332_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(lean_object* v_arr_2339_){
_start:
{
size_t v_sz_2340_; size_t v___x_2341_; lean_object* v___x_2342_; 
v_sz_2340_ = lean_array_size(v_arr_2339_);
v___x_2341_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2339_);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_arr_2339_, v_sz_2340_, v___x_2341_, v_arr_2339_);
lean_dec_ref(v_arr_2339_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(lean_object* v_as_2343_, size_t v_sz_2344_, size_t v_i_2345_, lean_object* v_bs_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2344_, v_i_2345_, v_bs_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___boxed(lean_object* v_as_2348_, lean_object* v_sz_2349_, lean_object* v_i_2350_, lean_object* v_bs_2351_){
_start:
{
size_t v_sz_boxed_2352_; size_t v_i_boxed_2353_; lean_object* v_res_2354_; 
v_sz_boxed_2352_ = lean_unbox_usize(v_sz_2349_);
lean_dec(v_sz_2349_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2350_);
lean_dec(v_i_2350_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(v_as_2348_, v_sz_boxed_2352_, v_i_boxed_2353_, v_bs_2351_);
lean_dec_ref(v_as_2348_);
return v_res_2354_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object* v_x_2355_){
_start:
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = lean_unsigned_to_nat(0u);
v___x_2357_ = lean_nat_dec_eq(v_x_2355_, v___x_2356_);
if (v___x_2357_ == 0)
{
uint8_t v___x_2358_; 
v___x_2358_ = 1;
return v___x_2358_;
}
else
{
uint8_t v___x_2359_; 
v___x_2359_ = 0;
return v___x_2359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object* v_x_2360_){
_start:
{
uint8_t v_res_2361_; lean_object* v_r_2362_; 
v_res_2361_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_x_2360_);
lean_dec(v_x_2360_);
v_r_2362_ = lean_box(v_res_2361_);
return v_r_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(size_t v_sz_2363_, size_t v_i_2364_, lean_object* v_bs_2365_){
_start:
{
uint8_t v___x_2366_; 
v___x_2366_ = lean_usize_dec_lt(v_i_2364_, v_sz_2363_);
if (v___x_2366_ == 0)
{
return v_bs_2365_;
}
else
{
lean_object* v_v_2367_; lean_object* v___x_2368_; lean_object* v_bs_x27_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; size_t v___x_2374_; size_t v___x_2375_; lean_object* v___x_2376_; 
v_v_2367_ = lean_array_uget(v_bs_2365_, v_i_2364_);
v___x_2368_ = lean_unsigned_to_nat(0u);
v_bs_x27_2369_ = lean_array_uset(v_bs_2365_, v_i_2364_, v___x_2368_);
v___x_2370_ = lean_usize_to_nat(v_i_2364_);
v___x_2371_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v___x_2370_);
lean_dec(v___x_2370_);
v___x_2372_ = lean_box(v___x_2371_);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_v_2367_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = ((size_t)1ULL);
v___x_2375_ = lean_usize_add(v_i_2364_, v___x_2374_);
v___x_2376_ = lean_array_uset(v_bs_x27_2369_, v_i_2364_, v___x_2373_);
v_i_2364_ = v___x_2375_;
v_bs_2365_ = v___x_2376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg___boxed(lean_object* v_sz_2378_, lean_object* v_i_2379_, lean_object* v_bs_2380_){
_start:
{
size_t v_sz_boxed_2381_; size_t v_i_boxed_2382_; lean_object* v_res_2383_; 
v_sz_boxed_2381_ = lean_unbox_usize(v_sz_2378_);
lean_dec(v_sz_2378_);
v_i_boxed_2382_ = lean_unbox_usize(v_i_2379_);
lean_dec(v_i_2379_);
v_res_2383_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_boxed_2381_, v_i_boxed_2382_, v_bs_2380_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(lean_object* v_arr_2384_){
_start:
{
size_t v_sz_2385_; size_t v___x_2386_; lean_object* v___x_2387_; 
v_sz_2385_ = lean_array_size(v_arr_2384_);
v___x_2386_ = ((size_t)0ULL);
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2385_, v___x_2386_, v_arr_2384_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(lean_object* v_as_2388_, size_t v_sz_2389_, size_t v_i_2390_, lean_object* v_bs_2391_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2389_, v_i_2390_, v_bs_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___boxed(lean_object* v_as_2393_, lean_object* v_sz_2394_, lean_object* v_i_2395_, lean_object* v_bs_2396_){
_start:
{
size_t v_sz_boxed_2397_; size_t v_i_boxed_2398_; lean_object* v_res_2399_; 
v_sz_boxed_2397_ = lean_unbox_usize(v_sz_2394_);
lean_dec(v_sz_2394_);
v_i_boxed_2398_ = lean_unbox_usize(v_i_2395_);
lean_dec(v_i_2395_);
v_res_2399_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(v_as_2393_, v_sz_boxed_2397_, v_i_boxed_2398_, v_bs_2396_);
lean_dec_ref(v_as_2393_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(lean_object* v_arr_2400_){
_start:
{
size_t v_sz_2401_; size_t v___x_2402_; lean_object* v___x_2403_; 
v_sz_2401_ = lean_array_size(v_arr_2400_);
v___x_2402_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2400_);
v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2400_, v_sz_2401_, v___x_2402_, v_arr_2400_);
lean_dec_ref(v_arr_2400_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(lean_object* v_symbols_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_monthLong_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_monthLong_2406_ = lean_ctor_get(v_symbols_2404_, 0);
lean_inc_ref(v_monthLong_2406_);
lean_dec_ref(v_symbols_2404_);
v___x_2407_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthLong_2406_);
v___x_2408_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2407_, v_a_2405_);
lean_dec_ref(v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object* v_symbols_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_monthShort_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_monthShort_2411_ = lean_ctor_get(v_symbols_2409_, 1);
lean_inc_ref(v_monthShort_2411_);
lean_dec_ref(v_symbols_2409_);
v___x_2412_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthShort_2411_);
v___x_2413_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2412_, v_a_2410_);
lean_dec_ref(v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(lean_object* v_symbols_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_monthNarrow_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_monthNarrow_2416_ = lean_ctor_get(v_symbols_2414_, 2);
lean_inc_ref(v_monthNarrow_2416_);
lean_dec_ref(v_symbols_2414_);
v___x_2417_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthNarrow_2416_);
v___x_2418_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2417_, v_a_2415_);
lean_dec_ref(v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(lean_object* v_symbols_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_weekdayLong_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_weekdayLong_2421_ = lean_ctor_get(v_symbols_2419_, 3);
lean_inc_ref(v_weekdayLong_2421_);
lean_dec_ref(v_symbols_2419_);
v___x_2422_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayLong_2421_);
v___x_2423_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2422_, v_a_2420_);
lean_dec_ref(v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(lean_object* v_symbols_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_weekdayShort_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_weekdayShort_2426_ = lean_ctor_get(v_symbols_2424_, 4);
lean_inc_ref(v_weekdayShort_2426_);
lean_dec_ref(v_symbols_2424_);
v___x_2427_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayShort_2426_);
v___x_2428_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2427_, v_a_2425_);
lean_dec_ref(v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(lean_object* v_symbols_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_weekdayNarrow_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_weekdayNarrow_2431_ = lean_ctor_get(v_symbols_2429_, 5);
lean_inc_ref(v_weekdayNarrow_2431_);
lean_dec_ref(v_symbols_2429_);
v___x_2432_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayNarrow_2431_);
v___x_2433_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2432_, v_a_2430_);
lean_dec_ref(v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(lean_object* v_symbols_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_weekdayTwoLetter_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_weekdayTwoLetter_2436_ = lean_ctor_get(v_symbols_2434_, 6);
lean_inc_ref(v_weekdayTwoLetter_2436_);
lean_dec_ref(v_symbols_2434_);
v___x_2437_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayTwoLetter_2436_);
v___x_2438_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2437_, v_a_2435_);
lean_dec_ref(v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(lean_object* v_symbols_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_eraShort_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_eraShort_2441_ = lean_ctor_get(v_symbols_2439_, 7);
lean_inc_ref(v_eraShort_2441_);
lean_dec_ref(v_symbols_2439_);
v___x_2442_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraShort_2441_);
v___x_2443_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2442_, v_a_2440_);
lean_dec_ref(v___x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(lean_object* v_symbols_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_eraLong_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_eraLong_2446_ = lean_ctor_get(v_symbols_2444_, 8);
lean_inc_ref(v_eraLong_2446_);
lean_dec_ref(v_symbols_2444_);
v___x_2447_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraLong_2446_);
v___x_2448_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2447_, v_a_2445_);
lean_dec_ref(v___x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(lean_object* v_symbols_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v_eraNarrow_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_eraNarrow_2451_ = lean_ctor_get(v_symbols_2449_, 9);
lean_inc_ref(v_eraNarrow_2451_);
lean_dec_ref(v_symbols_2449_);
v___x_2452_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraNarrow_2451_);
v___x_2453_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2452_, v_a_2450_);
lean_dec_ref(v___x_2452_);
return v___x_2453_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_unsigned_to_nat(3u);
v___x_2455_ = lean_nat_to_int(v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber(lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
lean_inc_ref(v_a_2456_);
v___x_2458_ = l_Std_Internal_Parsec_String_pstring(v___x_2457_, v_a_2456_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_pos_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v_a_2456_);
v_pos_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; 
v_unused_2468_ = lean_ctor_get(v___x_2458_, 1);
lean_dec(v_unused_2468_);
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_pos_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2463_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 1, v___x_2463_);
v___x_2465_ = v___x_2461_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_pos_2459_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
else
{
lean_object* v_pos_2469_; lean_object* v_err_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2547_; 
v_pos_2469_ = lean_ctor_get(v___x_2458_, 0);
v_err_2470_ = lean_ctor_get(v___x_2458_, 1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2472_ = v___x_2458_;
v_isShared_2473_ = v_isSharedCheck_2547_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_err_2470_);
lean_inc(v_pos_2469_);
lean_dec(v___x_2458_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2547_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v_snd_2474_; lean_object* v_snd_2475_; uint8_t v___x_2476_; 
v_snd_2474_ = lean_ctor_get(v_a_2456_, 1);
lean_inc(v_snd_2474_);
lean_dec_ref(v_a_2456_);
v_snd_2475_ = lean_ctor_get(v_pos_2469_, 1);
v___x_2476_ = lean_nat_dec_eq(v_snd_2474_, v_snd_2475_);
lean_dec(v_snd_2474_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2478_; 
if (v_isShared_2473_ == 0)
{
v___x_2478_ = v___x_2472_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_pos_2469_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_err_2470_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_inc(v_snd_2475_);
lean_del_object(v___x_2472_);
lean_dec(v_err_2470_);
v___x_2480_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
v___x_2481_ = l_Std_Internal_Parsec_String_pstring(v___x_2480_, v_pos_2469_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_pos_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_snd_2475_);
v_pos_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v___x_2481_, 1);
lean_dec(v_unused_2491_);
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2490_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_pos_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2490_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2486_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v___x_2486_);
v___x_2488_ = v___x_2484_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_pos_2482_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
else
{
lean_object* v_pos_2492_; lean_object* v_err_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2546_; 
v_pos_2492_ = lean_ctor_get(v___x_2481_, 0);
v_err_2493_ = lean_ctor_get(v___x_2481_, 1);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2495_ = v___x_2481_;
v_isShared_2496_ = v_isSharedCheck_2546_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_err_2493_);
lean_inc(v_pos_2492_);
lean_dec(v___x_2481_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2546_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_snd_2497_; uint8_t v___x_2498_; 
v_snd_2497_ = lean_ctor_get(v_pos_2492_, 1);
v___x_2498_ = lean_nat_dec_eq(v_snd_2475_, v_snd_2497_);
lean_dec(v_snd_2475_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2500_; 
if (v_isShared_2496_ == 0)
{
v___x_2500_ = v___x_2495_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_pos_2492_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_err_2493_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_inc(v_snd_2497_);
lean_del_object(v___x_2495_);
lean_dec(v_err_2493_);
v___x_2502_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
v___x_2503_ = l_Std_Internal_Parsec_String_pstring(v___x_2502_, v_pos_2492_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_pos_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_snd_2497_);
v_pos_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2503_, 1);
lean_dec(v_unused_2513_);
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_pos_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2508_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 1, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_pos_2504_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
else
{
lean_object* v_pos_2514_; lean_object* v_err_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2545_; 
v_pos_2514_ = lean_ctor_get(v___x_2503_, 0);
v_err_2515_ = lean_ctor_get(v___x_2503_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2517_ = v___x_2503_;
v_isShared_2518_ = v_isSharedCheck_2545_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_err_2515_);
lean_inc(v_pos_2514_);
lean_dec(v___x_2503_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2545_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v_snd_2519_; uint8_t v___x_2520_; 
v_snd_2519_ = lean_ctor_get(v_pos_2514_, 1);
v___x_2520_ = lean_nat_dec_eq(v_snd_2497_, v_snd_2519_);
lean_dec(v_snd_2497_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2522_; 
if (v_isShared_2518_ == 0)
{
v___x_2522_ = v___x_2517_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_pos_2514_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_err_2515_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_del_object(v___x_2517_);
lean_dec(v_err_2515_);
v___x_2524_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
v___x_2525_ = l_Std_Internal_Parsec_String_pstring(v___x_2524_, v_pos_2514_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_pos_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2534_; 
v_pos_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2525_, 1);
lean_dec(v_unused_2535_);
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2534_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_pos_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2534_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2530_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___x_2530_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_pos_2526_);
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
lean_object* v_pos_2536_; lean_object* v_err_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
v_pos_2536_ = lean_ctor_get(v___x_2525_, 0);
v_err_2537_ = lean_ctor_get(v___x_2525_, 1);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2525_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_err_2537_);
lean_inc(v_pos_2536_);
lean_dec(v___x_2525_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_pos_2536_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_err_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(lean_object* v_symbols_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_quarterLong_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_quarterLong_2550_ = lean_ctor_get(v_symbols_2548_, 11);
lean_inc_ref(v_quarterLong_2550_);
lean_dec_ref(v_symbols_2548_);
v___x_2551_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterLong_2550_);
v___x_2552_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2551_, v_a_2549_);
lean_dec_ref(v___x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(lean_object* v_symbols_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_quarterShort_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_quarterShort_2555_ = lean_ctor_get(v_symbols_2553_, 10);
lean_inc_ref(v_quarterShort_2555_);
lean_dec_ref(v_symbols_2553_);
v___x_2556_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterShort_2555_);
v___x_2557_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2556_, v_a_2554_);
lean_dec_ref(v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(lean_object* v_symbols_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_quarterNarrow_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_quarterNarrow_2560_ = lean_ctor_get(v_symbols_2558_, 12);
lean_inc_ref(v_quarterNarrow_2560_);
lean_dec_ref(v_symbols_2558_);
v___x_2561_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterNarrow_2560_);
v___x_2562_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2561_, v_a_2559_);
lean_dec_ref(v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(lean_object* v_symbols_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_amShort_2565_; lean_object* v_pmShort_2566_; lean_object* v___x_2567_; 
v_amShort_2565_ = lean_ctor_get(v_symbols_2563_, 13);
lean_inc_ref(v_amShort_2565_);
v_pmShort_2566_ = lean_ctor_get(v_symbols_2563_, 14);
lean_inc_ref(v_pmShort_2566_);
lean_dec_ref(v_symbols_2563_);
lean_inc_ref(v_a_2564_);
v___x_2567_ = l_Std_Internal_Parsec_String_pstring(v_amShort_2565_, v_a_2564_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_pos_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref(v_pmShort_2566_);
lean_dec_ref(v_a_2564_);
v_pos_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2567_, 1);
lean_dec(v_unused_2578_);
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2577_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_pos_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2577_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2572_ = 0;
v___x_2573_ = lean_box(v___x_2572_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v___x_2573_);
v___x_2575_ = v___x_2570_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_pos_2568_);
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
lean_object* v_pos_2579_; lean_object* v_err_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2611_; 
v_pos_2579_ = lean_ctor_get(v___x_2567_, 0);
v_err_2580_ = lean_ctor_get(v___x_2567_, 1);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2582_ = v___x_2567_;
v_isShared_2583_ = v_isSharedCheck_2611_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_err_2580_);
lean_inc(v_pos_2579_);
lean_dec(v___x_2567_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2611_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_snd_2584_; lean_object* v_snd_2585_; uint8_t v___x_2586_; 
v_snd_2584_ = lean_ctor_get(v_a_2564_, 1);
lean_inc(v_snd_2584_);
lean_dec_ref(v_a_2564_);
v_snd_2585_ = lean_ctor_get(v_pos_2579_, 1);
v___x_2586_ = lean_nat_dec_eq(v_snd_2584_, v_snd_2585_);
lean_dec(v_snd_2584_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2588_; 
lean_dec_ref(v_pmShort_2566_);
if (v_isShared_2583_ == 0)
{
v___x_2588_ = v___x_2582_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_pos_2579_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_err_2580_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
else
{
lean_object* v___x_2590_; 
lean_del_object(v___x_2582_);
lean_dec(v_err_2580_);
v___x_2590_ = l_Std_Internal_Parsec_String_pstring(v_pmShort_2566_, v_pos_2579_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_pos_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2600_; 
v_pos_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v___x_2590_, 1);
lean_dec(v_unused_2601_);
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2600_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_pos_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2600_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
uint8_t v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2595_ = 1;
v___x_2596_ = lean_box(v___x_2595_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___x_2596_);
v___x_2598_ = v___x_2593_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_pos_2591_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
else
{
lean_object* v_pos_2602_; lean_object* v_err_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
v_pos_2602_ = lean_ctor_get(v___x_2590_, 0);
v_err_2603_ = lean_ctor_get(v___x_2590_, 1);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2590_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_err_2603_);
lean_inc(v_pos_2602_);
lean_dec(v___x_2590_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_pos_2602_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_err_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(lean_object* v_symbols_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v_amLong_2614_; lean_object* v_pmLong_2615_; lean_object* v___x_2616_; 
v_amLong_2614_ = lean_ctor_get(v_symbols_2612_, 15);
lean_inc_ref(v_amLong_2614_);
v_pmLong_2615_ = lean_ctor_get(v_symbols_2612_, 16);
lean_inc_ref(v_pmLong_2615_);
lean_dec_ref(v_symbols_2612_);
lean_inc_ref(v_a_2613_);
v___x_2616_ = l_Std_Internal_Parsec_String_pstring(v_amLong_2614_, v_a_2613_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_pos_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_pmLong_2615_);
lean_dec_ref(v_a_2613_);
v_pos_2617_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v___x_2616_, 1);
lean_dec(v_unused_2627_);
v___x_2619_ = v___x_2616_;
v_isShared_2620_ = v_isSharedCheck_2626_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_pos_2617_);
lean_dec(v___x_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2626_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
uint8_t v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2621_ = 0;
v___x_2622_ = lean_box(v___x_2621_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 1, v___x_2622_);
v___x_2624_ = v___x_2619_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_pos_2617_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
lean_object* v_pos_2628_; lean_object* v_err_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2660_; 
v_pos_2628_ = lean_ctor_get(v___x_2616_, 0);
v_err_2629_ = lean_ctor_get(v___x_2616_, 1);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2631_ = v___x_2616_;
v_isShared_2632_ = v_isSharedCheck_2660_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_err_2629_);
lean_inc(v_pos_2628_);
lean_dec(v___x_2616_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2660_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_snd_2633_; lean_object* v_snd_2634_; uint8_t v___x_2635_; 
v_snd_2633_ = lean_ctor_get(v_a_2613_, 1);
lean_inc(v_snd_2633_);
lean_dec_ref(v_a_2613_);
v_snd_2634_ = lean_ctor_get(v_pos_2628_, 1);
v___x_2635_ = lean_nat_dec_eq(v_snd_2633_, v_snd_2634_);
lean_dec(v_snd_2633_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2637_; 
lean_dec_ref(v_pmLong_2615_);
if (v_isShared_2632_ == 0)
{
v___x_2637_ = v___x_2631_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_pos_2628_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_err_2629_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
else
{
lean_object* v___x_2639_; 
lean_del_object(v___x_2631_);
lean_dec(v_err_2629_);
v___x_2639_ = l_Std_Internal_Parsec_String_pstring(v_pmLong_2615_, v_pos_2628_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_pos_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2649_; 
v_pos_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; 
v_unused_2650_ = lean_ctor_get(v___x_2639_, 1);
lean_dec(v_unused_2650_);
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2649_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_pos_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2649_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
uint8_t v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2644_ = 1;
v___x_2645_ = lean_box(v___x_2644_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 1, v___x_2645_);
v___x_2647_ = v___x_2642_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_pos_2640_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
else
{
lean_object* v_pos_2651_; lean_object* v_err_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_pos_2651_ = lean_ctor_get(v___x_2639_, 0);
v_err_2652_ = lean_ctor_get(v___x_2639_, 1);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2639_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_err_2652_);
lean_inc(v_pos_2651_);
lean_dec(v___x_2639_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_pos_2651_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_err_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(lean_object* v_symbols_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_amNarrow_2663_; lean_object* v_pmNarrow_2664_; lean_object* v___x_2665_; 
v_amNarrow_2663_ = lean_ctor_get(v_symbols_2661_, 17);
lean_inc_ref(v_amNarrow_2663_);
v_pmNarrow_2664_ = lean_ctor_get(v_symbols_2661_, 18);
lean_inc_ref(v_pmNarrow_2664_);
lean_dec_ref(v_symbols_2661_);
lean_inc_ref(v_a_2662_);
v___x_2665_ = l_Std_Internal_Parsec_String_pstring(v_amNarrow_2663_, v_a_2662_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_pos_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2675_; 
lean_dec_ref(v_pmNarrow_2664_);
lean_dec_ref(v_a_2662_);
v_pos_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v___x_2665_, 1);
lean_dec(v_unused_2676_);
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2675_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_pos_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2675_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2670_ = 0;
v___x_2671_ = lean_box(v___x_2670_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___x_2671_);
v___x_2673_ = v___x_2668_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_pos_2666_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
lean_object* v_pos_2677_; lean_object* v_err_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2709_; 
v_pos_2677_ = lean_ctor_get(v___x_2665_, 0);
v_err_2678_ = lean_ctor_get(v___x_2665_, 1);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2680_ = v___x_2665_;
v_isShared_2681_ = v_isSharedCheck_2709_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_err_2678_);
lean_inc(v_pos_2677_);
lean_dec(v___x_2665_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2709_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v_snd_2682_; lean_object* v_snd_2683_; uint8_t v___x_2684_; 
v_snd_2682_ = lean_ctor_get(v_a_2662_, 1);
lean_inc(v_snd_2682_);
lean_dec_ref(v_a_2662_);
v_snd_2683_ = lean_ctor_get(v_pos_2677_, 1);
v___x_2684_ = lean_nat_dec_eq(v_snd_2682_, v_snd_2683_);
lean_dec(v_snd_2682_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2686_; 
lean_dec_ref(v_pmNarrow_2664_);
if (v_isShared_2681_ == 0)
{
v___x_2686_ = v___x_2680_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_pos_2677_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_err_2678_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
else
{
lean_object* v___x_2688_; 
lean_del_object(v___x_2680_);
lean_dec(v_err_2678_);
v___x_2688_ = l_Std_Internal_Parsec_String_pstring(v_pmNarrow_2664_, v_pos_2677_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_pos_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2698_; 
v_pos_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2688_, 1);
lean_dec(v_unused_2699_);
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2698_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_pos_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2698_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
uint8_t v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2693_ = 1;
v___x_2694_ = lean_box(v___x_2693_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 1, v___x_2694_);
v___x_2696_ = v___x_2691_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_pos_2689_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
else
{
lean_object* v_pos_2700_; lean_object* v_err_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
v_pos_2700_ = lean_ctor_get(v___x_2688_, 0);
v_err_2701_ = lean_ctor_get(v___x_2688_, 1);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2688_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_err_2701_);
lean_inc(v_pos_2700_);
lean_dec(v___x_2688_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_pos_2700_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_err_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(lean_object* v_dp_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_am_2712_; lean_object* v_pm_2713_; lean_object* v_noon_2714_; lean_object* v_midnight_2715_; lean_object* v___x_2716_; 
v_am_2712_ = lean_ctor_get(v_dp_2710_, 0);
lean_inc_ref(v_am_2712_);
v_pm_2713_ = lean_ctor_get(v_dp_2710_, 1);
lean_inc_ref(v_pm_2713_);
v_noon_2714_ = lean_ctor_get(v_dp_2710_, 2);
lean_inc_ref(v_noon_2714_);
v_midnight_2715_ = lean_ctor_get(v_dp_2710_, 3);
lean_inc_ref(v_midnight_2715_);
lean_dec_ref(v_dp_2710_);
lean_inc_ref(v_a_2711_);
v___x_2716_ = l_Std_Internal_Parsec_String_pstring(v_midnight_2715_, v_a_2711_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_pos_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2726_; 
lean_dec_ref(v_noon_2714_);
lean_dec_ref(v_pm_2713_);
lean_dec_ref(v_am_2712_);
lean_dec_ref(v_a_2711_);
v_pos_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2726_ == 0)
{
lean_object* v_unused_2727_; 
v_unused_2727_ = lean_ctor_get(v___x_2716_, 1);
lean_dec(v_unused_2727_);
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2726_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_pos_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2726_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2721_ = 3;
v___x_2722_ = lean_box(v___x_2721_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 1, v___x_2722_);
v___x_2724_ = v___x_2719_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_pos_2717_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
else
{
lean_object* v_pos_2728_; lean_object* v_err_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2806_; 
v_pos_2728_ = lean_ctor_get(v___x_2716_, 0);
v_err_2729_ = lean_ctor_get(v___x_2716_, 1);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2731_ = v___x_2716_;
v_isShared_2732_ = v_isSharedCheck_2806_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_err_2729_);
lean_inc(v_pos_2728_);
lean_dec(v___x_2716_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2806_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v_snd_2733_; lean_object* v_snd_2734_; uint8_t v___x_2735_; 
v_snd_2733_ = lean_ctor_get(v_a_2711_, 1);
lean_inc(v_snd_2733_);
lean_dec_ref(v_a_2711_);
v_snd_2734_ = lean_ctor_get(v_pos_2728_, 1);
v___x_2735_ = lean_nat_dec_eq(v_snd_2733_, v_snd_2734_);
lean_dec(v_snd_2733_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2737_; 
lean_dec_ref(v_noon_2714_);
lean_dec_ref(v_pm_2713_);
lean_dec_ref(v_am_2712_);
if (v_isShared_2732_ == 0)
{
v___x_2737_ = v___x_2731_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_pos_2728_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_err_2729_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
else
{
lean_object* v___x_2739_; 
lean_inc(v_snd_2734_);
lean_del_object(v___x_2731_);
lean_dec(v_err_2729_);
v___x_2739_ = l_Std_Internal_Parsec_String_pstring(v_noon_2714_, v_pos_2728_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_pos_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_snd_2734_);
lean_dec_ref(v_pm_2713_);
lean_dec_ref(v_am_2712_);
v_pos_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; 
v_unused_2750_ = lean_ctor_get(v___x_2739_, 1);
lean_dec(v_unused_2750_);
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2749_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_pos_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2749_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
uint8_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2744_ = 2;
v___x_2745_ = lean_box(v___x_2744_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v___x_2745_);
v___x_2747_ = v___x_2742_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_pos_2740_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
else
{
lean_object* v_pos_2751_; lean_object* v_err_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2805_; 
v_pos_2751_ = lean_ctor_get(v___x_2739_, 0);
v_err_2752_ = lean_ctor_get(v___x_2739_, 1);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2754_ = v___x_2739_;
v_isShared_2755_ = v_isSharedCheck_2805_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_err_2752_);
lean_inc(v_pos_2751_);
lean_dec(v___x_2739_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2805_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_snd_2756_; uint8_t v___x_2757_; 
v_snd_2756_ = lean_ctor_get(v_pos_2751_, 1);
v___x_2757_ = lean_nat_dec_eq(v_snd_2734_, v_snd_2756_);
lean_dec(v_snd_2734_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2759_; 
lean_dec_ref(v_pm_2713_);
lean_dec_ref(v_am_2712_);
if (v_isShared_2755_ == 0)
{
v___x_2759_ = v___x_2754_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_pos_2751_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v_err_2752_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
else
{
lean_object* v___x_2761_; 
lean_inc(v_snd_2756_);
lean_del_object(v___x_2754_);
lean_dec(v_err_2752_);
v___x_2761_ = l_Std_Internal_Parsec_String_pstring(v_am_2712_, v_pos_2751_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_pos_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v_snd_2756_);
lean_dec_ref(v_pm_2713_);
v_pos_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2771_ == 0)
{
lean_object* v_unused_2772_; 
v_unused_2772_ = lean_ctor_get(v___x_2761_, 1);
lean_dec(v_unused_2772_);
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2771_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_pos_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2771_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
uint8_t v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2766_ = 0;
v___x_2767_ = lean_box(v___x_2766_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 1, v___x_2767_);
v___x_2769_ = v___x_2764_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_pos_2762_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
else
{
lean_object* v_pos_2773_; lean_object* v_err_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2804_; 
v_pos_2773_ = lean_ctor_get(v___x_2761_, 0);
v_err_2774_ = lean_ctor_get(v___x_2761_, 1);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2776_ = v___x_2761_;
v_isShared_2777_ = v_isSharedCheck_2804_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_err_2774_);
lean_inc(v_pos_2773_);
lean_dec(v___x_2761_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2804_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v_snd_2778_; uint8_t v___x_2779_; 
v_snd_2778_ = lean_ctor_get(v_pos_2773_, 1);
v___x_2779_ = lean_nat_dec_eq(v_snd_2756_, v_snd_2778_);
lean_dec(v_snd_2756_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2781_; 
lean_dec_ref(v_pm_2713_);
if (v_isShared_2777_ == 0)
{
v___x_2781_ = v___x_2776_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_pos_2773_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_err_2774_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
else
{
lean_object* v___x_2783_; 
lean_del_object(v___x_2776_);
lean_dec(v_err_2774_);
v___x_2783_ = l_Std_Internal_Parsec_String_pstring(v_pm_2713_, v_pos_2773_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_pos_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2793_; 
v_pos_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v___x_2783_, 1);
lean_dec(v_unused_2794_);
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2793_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_pos_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2793_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
uint8_t v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2788_ = 1;
v___x_2789_ = lean_box(v___x_2788_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 1, v___x_2789_);
v___x_2791_ = v___x_2786_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_pos_2784_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
else
{
lean_object* v_pos_2795_; lean_object* v_err_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_pos_2795_ = lean_ctor_get(v___x_2783_, 0);
v_err_2796_ = lean_ctor_get(v___x_2783_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2783_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_err_2796_);
lean_inc(v_pos_2795_);
lean_dec(v___x_2783_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_pos_2795_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_err_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(lean_object* v_arr_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v_pairs_2846_; lean_object* v___x_2847_; 
v___x_2809_ = lean_unsigned_to_nat(6u);
v___x_2810_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0);
v___x_2811_ = lean_array_fget_borrowed(v_arr_2807_, v___x_2810_);
v___x_2812_ = 0;
v___x_2813_ = lean_box(v___x_2812_);
lean_inc(v___x_2811_);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2811_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1);
v___x_2816_ = lean_array_fget_borrowed(v_arr_2807_, v___x_2815_);
v___x_2817_ = 1;
v___x_2818_ = lean_box(v___x_2817_);
lean_inc(v___x_2816_);
v___x_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2816_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2);
v___x_2821_ = lean_array_fget_borrowed(v_arr_2807_, v___x_2820_);
v___x_2822_ = 2;
v___x_2823_ = lean_box(v___x_2822_);
lean_inc(v___x_2821_);
v___x_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2821_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3);
v___x_2826_ = lean_array_fget_borrowed(v_arr_2807_, v___x_2825_);
v___x_2827_ = 3;
v___x_2828_ = lean_box(v___x_2827_);
lean_inc(v___x_2826_);
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2826_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4);
v___x_2831_ = lean_array_fget_borrowed(v_arr_2807_, v___x_2830_);
v___x_2832_ = 4;
v___x_2833_ = lean_box(v___x_2832_);
lean_inc(v___x_2831_);
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2831_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5);
v___x_2836_ = lean_array_fget_borrowed(v_arr_2807_, v___x_2835_);
v___x_2837_ = 5;
v___x_2838_ = lean_box(v___x_2837_);
lean_inc(v___x_2836_);
v___x_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2836_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_mk_empty_array_with_capacity(v___x_2809_);
v___x_2841_ = lean_array_push(v___x_2840_, v___x_2814_);
v___x_2842_ = lean_array_push(v___x_2841_, v___x_2819_);
v___x_2843_ = lean_array_push(v___x_2842_, v___x_2824_);
v___x_2844_ = lean_array_push(v___x_2843_, v___x_2829_);
v___x_2845_ = lean_array_push(v___x_2844_, v___x_2834_);
v_pairs_2846_ = lean_array_push(v___x_2845_, v___x_2839_);
v___x_2847_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2846_, v_a_2808_);
lean_dec_ref(v_pairs_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom___boxed(lean_object* v_arr_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_arr_2848_, v_a_2849_);
lean_dec_ref(v_arr_2848_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(lean_object* v_parse_2851_, lean_object* v_size_2852_, lean_object* v_acc_2853_, lean_object* v_count_2854_, lean_object* v_a_2855_){
_start:
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_nat_dec_le(v_size_2852_, v_count_2854_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
lean_inc_ref(v_parse_2851_);
v___x_2857_ = lean_apply_1(v_parse_2851_, v_a_2855_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_pos_2858_; lean_object* v_res_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_pos_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_pos_2858_);
v_res_2859_ = lean_ctor_get(v___x_2857_, 1);
lean_inc(v_res_2859_);
lean_dec_ref_known(v___x_2857_, 2);
v___x_2860_ = lean_array_push(v_acc_2853_, v_res_2859_);
v___x_2861_ = lean_unsigned_to_nat(1u);
v___x_2862_ = lean_nat_add(v_count_2854_, v___x_2861_);
lean_dec(v_count_2854_);
v_acc_2853_ = v___x_2860_;
v_count_2854_ = v___x_2862_;
v_a_2855_ = v_pos_2858_;
goto _start;
}
else
{
lean_object* v_pos_2864_; lean_object* v_err_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_count_2854_);
lean_dec_ref(v_acc_2853_);
lean_dec_ref(v_parse_2851_);
v_pos_2864_ = lean_ctor_get(v___x_2857_, 0);
v_err_2865_ = lean_ctor_get(v___x_2857_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2857_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_err_2865_);
lean_inc(v_pos_2864_);
lean_dec(v___x_2857_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_pos_2864_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_err_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v___x_2873_; 
lean_dec(v_count_2854_);
lean_dec_ref(v_parse_2851_);
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v_a_2855_);
lean_ctor_set(v___x_2873_, 1, v_acc_2853_);
return v___x_2873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg___boxed(lean_object* v_parse_2874_, lean_object* v_size_2875_, lean_object* v_acc_2876_, lean_object* v_count_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2874_, v_size_2875_, v_acc_2876_, v_count_2877_, v_a_2878_);
lean_dec(v_size_2875_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(lean_object* v_00_u03b1_2880_, lean_object* v_parse_2881_, lean_object* v_size_2882_, lean_object* v_acc_2883_, lean_object* v_count_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2881_, v_size_2882_, v_acc_2883_, v_count_2884_, v_a_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___boxed(lean_object* v_00_u03b1_2887_, lean_object* v_parse_2888_, lean_object* v_size_2889_, lean_object* v_acc_2890_, lean_object* v_count_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(v_00_u03b1_2887_, v_parse_2888_, v_size_2889_, v_acc_2890_, v_count_2891_, v_a_2892_);
lean_dec(v_size_2889_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(lean_object* v_parse_2896_, lean_object* v_size_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0));
v___x_2900_ = lean_unsigned_to_nat(12u);
v___x_2901_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2896_, v_size_2897_, v___x_2899_, v___x_2900_, v_a_2898_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___boxed(lean_object* v_parse_2902_, lean_object* v_size_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2902_, v_size_2903_, v_a_2904_);
lean_dec(v_size_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly(lean_object* v_00_u03b1_2906_, lean_object* v_parse_2907_, lean_object* v_size_2908_, lean_object* v_a_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2907_, v_size_2908_, v_a_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___boxed(lean_object* v_00_u03b1_2911_, lean_object* v_parse_2912_, lean_object* v_size_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly(v_00_u03b1_2911_, v_parse_2912_, v_size_2913_, v_a_2914_);
lean_dec(v_size_2913_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object* v_parse_2916_, lean_object* v_size_2917_, lean_object* v_acc_2918_, lean_object* v_count_2919_, lean_object* v_a_2920_){
_start:
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_nat_dec_le(v_size_2917_, v_count_2919_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; 
lean_inc_ref(v_parse_2916_);
v___x_2922_ = lean_apply_1(v_parse_2916_, v_a_2920_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_pos_2923_; lean_object* v_res_2924_; uint32_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_pos_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_pos_2923_);
v_res_2924_ = lean_ctor_get(v___x_2922_, 1);
lean_inc(v_res_2924_);
lean_dec_ref_known(v___x_2922_, 2);
v___x_2925_ = lean_unbox_uint32(v_res_2924_);
lean_dec(v_res_2924_);
v___x_2926_ = lean_string_push(v_acc_2918_, v___x_2925_);
v___x_2927_ = lean_unsigned_to_nat(1u);
v___x_2928_ = lean_nat_add(v_count_2919_, v___x_2927_);
lean_dec(v_count_2919_);
v_acc_2918_ = v___x_2926_;
v_count_2919_ = v___x_2928_;
v_a_2920_ = v_pos_2923_;
goto _start;
}
else
{
lean_object* v_pos_2930_; lean_object* v_err_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v_count_2919_);
lean_dec_ref(v_acc_2918_);
lean_dec_ref(v_parse_2916_);
v_pos_2930_ = lean_ctor_get(v___x_2922_, 0);
v_err_2931_ = lean_ctor_get(v___x_2922_, 1);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2922_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_err_2931_);
lean_inc(v_pos_2930_);
lean_dec(v___x_2922_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_pos_2930_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_err_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
else
{
lean_object* v___x_2939_; 
lean_dec(v_count_2919_);
lean_dec_ref(v_parse_2916_);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2920_);
lean_ctor_set(v___x_2939_, 1, v_acc_2918_);
return v___x_2939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object* v_parse_2940_, lean_object* v_size_2941_, lean_object* v_acc_2942_, lean_object* v_count_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2940_, v_size_2941_, v_acc_2942_, v_count_2943_, v_a_2944_);
lean_dec(v_size_2941_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object* v_parse_2946_, lean_object* v_size_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_2950_ = lean_unsigned_to_nat(0u);
v___x_2951_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2946_, v_size_2947_, v___x_2949_, v___x_2950_, v_a_2948_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object* v_parse_2952_, lean_object* v_size_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v_parse_2952_, v_size_2953_, v_a_2954_);
lean_dec(v_size_2953_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object* v_parser_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_pos_2959_; lean_object* v_res_2960_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
lean_inc_ref(v_a_2957_);
v___x_2993_ = l_Std_Internal_Parsec_String_pstring(v___x_2992_, v_a_2957_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_pos_2994_; lean_object* v_res_2995_; lean_object* v___x_2996_; 
lean_dec_ref(v_a_2957_);
v_pos_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_pos_2994_);
v_res_2995_ = lean_ctor_get(v___x_2993_, 1);
lean_inc(v_res_2995_);
lean_dec_ref_known(v___x_2993_, 2);
v___x_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2996_, 0, v_res_2995_);
v_pos_2959_ = v_pos_2994_;
v_res_2960_ = v___x_2996_;
goto v___jp_2958_;
}
else
{
lean_object* v_pos_2997_; lean_object* v_err_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3009_; 
v_pos_2997_ = lean_ctor_get(v___x_2993_, 0);
v_err_2998_ = lean_ctor_get(v___x_2993_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3000_ = v___x_2993_;
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_err_2998_);
lean_inc(v_pos_2997_);
lean_dec(v___x_2993_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v_snd_3002_; lean_object* v_snd_3003_; uint8_t v___x_3004_; 
v_snd_3002_ = lean_ctor_get(v_a_2957_, 1);
lean_inc(v_snd_3002_);
lean_dec_ref(v_a_2957_);
v_snd_3003_ = lean_ctor_get(v_pos_2997_, 1);
v___x_3004_ = lean_nat_dec_eq(v_snd_3002_, v_snd_3003_);
lean_dec(v_snd_3002_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3006_; 
lean_dec_ref(v_parser_2956_);
if (v_isShared_3001_ == 0)
{
v___x_3006_ = v___x_3000_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_pos_2997_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_err_2998_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
else
{
lean_object* v___x_3008_; 
lean_del_object(v___x_3000_);
lean_dec(v_err_2998_);
v___x_3008_ = lean_box(0);
v_pos_2959_ = v_pos_2997_;
v_res_2960_ = v___x_3008_;
goto v___jp_2958_;
}
}
}
v___jp_2958_:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_apply_1(v_parser_2956_, v_pos_2959_);
if (lean_obj_tag(v___x_2961_) == 0)
{
if (lean_obj_tag(v_res_2960_) == 0)
{
lean_object* v_pos_2962_; lean_object* v_res_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2971_; 
v_pos_2962_ = lean_ctor_get(v___x_2961_, 0);
v_res_2963_ = lean_ctor_get(v___x_2961_, 1);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2965_ = v___x_2961_;
v_isShared_2966_ = v_isSharedCheck_2971_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_res_2963_);
lean_inc(v_pos_2962_);
lean_dec(v___x_2961_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2971_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2967_ = lean_nat_to_int(v_res_2963_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v___x_2967_);
v___x_2969_ = v___x_2965_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_pos_2962_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
else
{
lean_object* v_pos_2972_; lean_object* v_res_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref_known(v_res_2960_, 1);
v_pos_2972_ = lean_ctor_get(v___x_2961_, 0);
v_res_2973_ = lean_ctor_get(v___x_2961_, 1);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2975_ = v___x_2961_;
v_isShared_2976_ = v_isSharedCheck_2982_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_res_2973_);
lean_inc(v_pos_2972_);
lean_dec(v___x_2961_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2982_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2977_ = lean_nat_to_int(v_res_2973_);
v___x_2978_ = lean_int_neg(v___x_2977_);
lean_dec(v___x_2977_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 1, v___x_2978_);
v___x_2980_ = v___x_2975_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_pos_2972_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_pos_2983_; lean_object* v_err_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_res_2960_);
v_pos_2983_ = lean_ctor_get(v___x_2961_, 0);
v_err_2984_ = lean_ctor_get(v___x_2961_, 1);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2961_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_err_2984_);
lean_inc(v_pos_2983_);
lean_dec(v___x_2961_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_pos_2983_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_err_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___lam__0(lean_object* v___y_3010_){
_start:
{
lean_object* v_fst_3011_; lean_object* v_snd_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v_fst_3011_ = lean_ctor_get(v___y_3010_, 0);
v_snd_3012_ = lean_ctor_get(v___y_3010_, 1);
v___x_3013_ = lean_string_utf8_byte_size(v_fst_3011_);
v___x_3014_ = lean_nat_dec_eq(v_snd_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
uint32_t v_c_3015_; lean_object* v___x_3016_; lean_object* v_it_x27_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; uint8_t v___y_3021_; uint32_t v___x_3024_; uint8_t v___x_3025_; 
v_c_3015_ = lean_string_utf8_get_fast(v_fst_3011_, v_snd_3012_);
v___x_3016_ = lean_string_utf8_next_fast(v_fst_3011_, v_snd_3012_);
lean_inc(v_fst_3011_);
v_it_x27_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3017_, 0, v_fst_3011_);
lean_ctor_set(v_it_x27_3017_, 1, v___x_3016_);
v___x_3018_ = lean_box_uint32(v_c_3015_);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v_it_x27_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3024_ = 48;
v___x_3025_ = lean_uint32_dec_le(v___x_3024_, v_c_3015_);
if (v___x_3025_ == 0)
{
v___y_3021_ = v___x_3025_;
goto v___jp_3020_;
}
else
{
uint32_t v___x_3026_; uint8_t v___x_3027_; 
v___x_3026_ = 57;
v___x_3027_ = lean_uint32_dec_le(v_c_3015_, v___x_3026_);
v___y_3021_ = v___x_3027_;
goto v___jp_3020_;
}
v___jp_3020_:
{
if (v___y_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3019_, 2);
v___x_3022_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___y_3010_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
return v___x_3023_;
}
else
{
lean_dec_ref(v___y_3010_);
return v___x_3019_;
}
}
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___y_3010_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
return v___x_3029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object* v_size_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v___f_3033_; lean_object* v___x_3034_; 
v___f_3033_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3034_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3033_, v_size_3031_, v_a_3032_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_pos_3035_; lean_object* v_res_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3047_; 
v_pos_3035_ = lean_ctor_get(v___x_3034_, 0);
v_res_3036_ = lean_ctor_get(v___x_3034_, 1);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3038_ = v___x_3034_;
v_isShared_3039_ = v_isSharedCheck_3047_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_res_3036_);
lean_inc(v_pos_3035_);
lean_dec(v___x_3034_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3047_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = lean_string_utf8_byte_size(v_res_3036_);
v___x_3042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3042_, 0, v_res_3036_);
lean_ctor_set(v___x_3042_, 1, v___x_3040_);
lean_ctor_set(v___x_3042_, 2, v___x_3041_);
v___x_3043_ = l_String_Slice_toNat_x21(v___x_3042_);
lean_dec_ref_known(v___x_3042_, 3);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 1, v___x_3043_);
v___x_3045_ = v___x_3038_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_pos_3035_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
else
{
lean_object* v_pos_3048_; lean_object* v_err_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
v_pos_3048_ = lean_ctor_get(v___x_3034_, 0);
v_err_3049_ = lean_ctor_get(v___x_3034_, 1);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3034_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_err_3049_);
lean_inc(v_pos_3048_);
lean_dec(v___x_3034_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_pos_3048_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_err_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed(lean_object* v_size_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3057_, v_a_3058_);
lean_dec(v_size_3057_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object* v_acc_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_fst_3062_; lean_object* v_snd_3063_; lean_object* v_pos_3065_; lean_object* v_snd_3066_; lean_object* v_err_3067_; lean_object* v___x_3071_; uint8_t v___x_3072_; 
v_fst_3062_ = lean_ctor_get(v_a_3061_, 0);
v_snd_3063_ = lean_ctor_get(v_a_3061_, 1);
lean_inc(v_snd_3063_);
v___x_3071_ = lean_string_utf8_byte_size(v_fst_3062_);
v___x_3072_ = lean_nat_dec_eq(v_snd_3063_, v___x_3071_);
if (v___x_3072_ == 0)
{
uint32_t v_c_3073_; lean_object* v___x_3074_; lean_object* v_it_x27_3075_; uint8_t v___y_3077_; uint32_t v___x_3081_; uint8_t v___x_3082_; 
v_c_3073_ = lean_string_utf8_get_fast(v_fst_3062_, v_snd_3063_);
v___x_3074_ = lean_string_utf8_next_fast(v_fst_3062_, v_snd_3063_);
lean_inc(v_fst_3062_);
v_it_x27_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3075_, 0, v_fst_3062_);
lean_ctor_set(v_it_x27_3075_, 1, v___x_3074_);
v___x_3081_ = 48;
v___x_3082_ = lean_uint32_dec_le(v___x_3081_, v_c_3073_);
if (v___x_3082_ == 0)
{
v___y_3077_ = v___x_3082_;
goto v___jp_3076_;
}
else
{
uint32_t v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = 57;
v___x_3084_ = lean_uint32_dec_le(v_c_3073_, v___x_3083_);
v___y_3077_ = v___x_3084_;
goto v___jp_3076_;
}
v___jp_3076_:
{
if (v___y_3077_ == 0)
{
lean_object* v___x_3078_; 
lean_dec_ref_known(v_it_x27_3075_, 2);
v___x_3078_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3063_);
v_pos_3065_ = v_a_3061_;
v_snd_3066_ = v_snd_3063_;
v_err_3067_ = v___x_3078_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3079_; 
lean_dec(v_snd_3063_);
lean_dec_ref(v_a_3061_);
v___x_3079_ = lean_string_push(v_acc_3060_, v_c_3073_);
v_acc_3060_ = v___x_3079_;
v_a_3061_ = v_it_x27_3075_;
goto _start;
}
}
}
else
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_box(0);
lean_inc(v_snd_3063_);
v_pos_3065_ = v_a_3061_;
v_snd_3066_ = v_snd_3063_;
v_err_3067_ = v___x_3085_;
goto v___jp_3064_;
}
v___jp_3064_:
{
uint8_t v___x_3068_; 
v___x_3068_ = lean_nat_dec_eq(v_snd_3063_, v_snd_3066_);
lean_dec(v_snd_3066_);
lean_dec(v_snd_3063_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; 
lean_dec_ref(v_acc_3060_);
lean_inc(v_err_3067_);
v___x_3069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3069_, 0, v_pos_3065_);
lean_ctor_set(v___x_3069_, 1, v_err_3067_);
return v___x_3069_;
}
else
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v_pos_3065_);
lean_ctor_set(v___x_3070_, 1, v_acc_3060_);
return v___x_3070_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object* v_size_3086_, lean_object* v_a_3087_){
_start:
{
lean_object* v_pos_3089_; lean_object* v_res_3090_; lean_object* v___y_3097_; lean_object* v___f_3109_; lean_object* v___x_3110_; 
v___f_3109_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3110_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3109_, v_size_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_pos_3111_; lean_object* v_res_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v_pos_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_pos_3111_);
v_res_3112_ = lean_ctor_get(v___x_3110_, 1);
lean_inc(v_res_3112_);
lean_dec_ref_known(v___x_3110_, 2);
v___x_3113_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3114_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(v___x_3113_, v_pos_3111_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_pos_3115_; lean_object* v_res_3116_; lean_object* v___x_3117_; 
v_pos_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_pos_3115_);
v_res_3116_ = lean_ctor_get(v___x_3114_, 1);
lean_inc(v_res_3116_);
lean_dec_ref_known(v___x_3114_, 2);
v___x_3117_ = lean_string_append(v_res_3112_, v_res_3116_);
lean_dec(v_res_3116_);
v_pos_3089_ = v_pos_3115_;
v_res_3090_ = v___x_3117_;
goto v___jp_3088_;
}
else
{
lean_dec(v_res_3112_);
v___y_3097_ = v___x_3114_;
goto v___jp_3096_;
}
}
else
{
v___y_3097_ = v___x_3110_;
goto v___jp_3096_;
}
v___jp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3091_ = lean_unsigned_to_nat(0u);
v___x_3092_ = lean_string_utf8_byte_size(v_res_3090_);
v___x_3093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3093_, 0, v_res_3090_);
lean_ctor_set(v___x_3093_, 1, v___x_3091_);
lean_ctor_set(v___x_3093_, 2, v___x_3092_);
v___x_3094_ = l_String_Slice_toNat_x21(v___x_3093_);
lean_dec_ref_known(v___x_3093_, 3);
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v_pos_3089_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
return v___x_3095_;
}
v___jp_3096_:
{
if (lean_obj_tag(v___y_3097_) == 0)
{
lean_object* v_pos_3098_; lean_object* v_res_3099_; 
v_pos_3098_ = lean_ctor_get(v___y_3097_, 0);
lean_inc(v_pos_3098_);
v_res_3099_ = lean_ctor_get(v___y_3097_, 1);
lean_inc(v_res_3099_);
lean_dec_ref_known(v___y_3097_, 2);
v_pos_3089_ = v_pos_3098_;
v_res_3090_ = v_res_3099_;
goto v___jp_3088_;
}
else
{
lean_object* v_pos_3100_; lean_object* v_err_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_pos_3100_ = lean_ctor_get(v___y_3097_, 0);
v_err_3101_ = lean_ctor_get(v___y_3097_, 1);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___y_3097_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___y_3097_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_err_3101_);
lean_inc(v_pos_3100_);
lean_dec(v___y_3097_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_pos_3100_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_err_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object* v_size_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v_size_3118_, v_a_3119_);
lean_dec(v_size_3118_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object* v_size_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3123_ = lean_unsigned_to_nat(1u);
v___x_3124_ = lean_nat_dec_eq(v_size_3121_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
v___x_3125_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3121_, v_a_3122_);
return v___x_3125_;
}
else
{
lean_object* v___x_3126_; 
v___x_3126_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3123_, v_a_3122_);
return v___x_3126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed(lean_object* v_size_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_size_3127_, v_a_3128_);
lean_dec(v_size_3127_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object* v_size_3130_, lean_object* v_pad_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_pos_3134_; lean_object* v_res_3135_; lean_object* v___f_3141_; lean_object* v___x_3142_; 
v___f_3141_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3142_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3141_, v_size_3130_, v_a_3132_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_pos_3143_; lean_object* v_res_3144_; uint32_t v___x_3145_; lean_object* v___x_3146_; 
v_pos_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_pos_3143_);
v_res_3144_ = lean_ctor_get(v___x_3142_, 1);
lean_inc(v_res_3144_);
lean_dec_ref_known(v___x_3142_, 2);
v___x_3145_ = 48;
v___x_3146_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_pad_3131_, v___x_3145_, v_res_3144_);
v_pos_3134_ = v_pos_3143_;
v_res_3135_ = v___x_3146_;
goto v___jp_3133_;
}
else
{
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_pos_3147_; lean_object* v_res_3148_; 
v_pos_3147_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_pos_3147_);
v_res_3148_ = lean_ctor_get(v___x_3142_, 1);
lean_inc(v_res_3148_);
lean_dec_ref_known(v___x_3142_, 2);
v_pos_3134_ = v_pos_3147_;
v_res_3135_ = v_res_3148_;
goto v___jp_3133_;
}
else
{
lean_object* v_pos_3149_; lean_object* v_err_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
v_pos_3149_ = lean_ctor_get(v___x_3142_, 0);
v_err_3150_ = lean_ctor_get(v___x_3142_, 1);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3142_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_err_3150_);
lean_inc(v_pos_3149_);
lean_dec(v___x_3142_);
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
v___jp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3136_ = lean_unsigned_to_nat(0u);
v___x_3137_ = lean_string_utf8_byte_size(v_res_3135_);
v___x_3138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3138_, 0, v_res_3135_);
lean_ctor_set(v___x_3138_, 1, v___x_3136_);
lean_ctor_set(v___x_3138_, 2, v___x_3137_);
v___x_3139_ = l_String_Slice_toNat_x21(v___x_3138_);
lean_dec_ref_known(v___x_3138_, 3);
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v_pos_3134_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
return v___x_3140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object* v_size_3158_, lean_object* v_pad_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(v_size_3158_, v_pad_3159_, v_a_3160_);
lean_dec(v_pad_3159_);
lean_dec(v_size_3158_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object* v_acc_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v_pos_3165_; uint32_t v_res_3166_; lean_object* v_fst_3169_; lean_object* v_snd_3170_; lean_object* v_pos_3172_; lean_object* v_snd_3173_; lean_object* v_err_3174_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v_fst_3169_ = lean_ctor_get(v_a_3163_, 0);
v_snd_3170_ = lean_ctor_get(v_a_3163_, 1);
lean_inc(v_snd_3170_);
v___x_3178_ = lean_string_utf8_byte_size(v_fst_3169_);
v___x_3179_ = lean_nat_dec_eq(v_snd_3170_, v___x_3178_);
if (v___x_3179_ == 0)
{
uint32_t v_c_3180_; lean_object* v___x_3181_; lean_object* v_it_x27_3182_; uint8_t v___y_3184_; uint8_t v___y_3185_; uint8_t v___y_3194_; uint32_t v___x_3204_; uint8_t v___x_3205_; 
v_c_3180_ = lean_string_utf8_get_fast(v_fst_3169_, v_snd_3170_);
v___x_3181_ = lean_string_utf8_next_fast(v_fst_3169_, v_snd_3170_);
lean_inc(v_fst_3169_);
v_it_x27_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3182_, 0, v_fst_3169_);
lean_ctor_set(v_it_x27_3182_, 1, v___x_3181_);
v___x_3204_ = 65;
v___x_3205_ = lean_uint32_dec_le(v___x_3204_, v_c_3180_);
if (v___x_3205_ == 0)
{
goto v___jp_3199_;
}
else
{
uint32_t v___x_3206_; uint8_t v___x_3207_; 
v___x_3206_ = 90;
v___x_3207_ = lean_uint32_dec_le(v_c_3180_, v___x_3206_);
if (v___x_3207_ == 0)
{
goto v___jp_3199_;
}
else
{
lean_dec(v_snd_3170_);
lean_dec_ref(v_a_3163_);
v_pos_3165_ = v_it_x27_3182_;
v_res_3166_ = v_c_3180_;
goto v___jp_3164_;
}
}
v___jp_3183_:
{
if (v___y_3185_ == 0)
{
uint32_t v___x_3186_; uint8_t v___x_3187_; 
v___x_3186_ = 95;
v___x_3187_ = lean_uint32_dec_eq(v_c_3180_, v___x_3186_);
if (v___x_3187_ == 0)
{
uint32_t v___x_3188_; uint8_t v___x_3189_; 
v___x_3188_ = 45;
v___x_3189_ = lean_uint32_dec_eq(v_c_3180_, v___x_3188_);
if (v___x_3189_ == 0)
{
uint32_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = 47;
v___x_3191_ = lean_uint32_dec_eq(v_c_3180_, v___x_3190_);
if (v___x_3191_ == 0)
{
if (v___y_3184_ == 0)
{
lean_object* v___x_3192_; 
lean_dec_ref_known(v_it_x27_3182_, 2);
v___x_3192_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3170_);
v_pos_3172_ = v_a_3163_;
v_snd_3173_ = v_snd_3170_;
v_err_3174_ = v___x_3192_;
goto v___jp_3171_;
}
else
{
lean_dec(v_snd_3170_);
lean_dec_ref(v_a_3163_);
v_pos_3165_ = v_it_x27_3182_;
v_res_3166_ = v_c_3180_;
goto v___jp_3164_;
}
}
else
{
lean_dec(v_snd_3170_);
lean_dec_ref(v_a_3163_);
v_pos_3165_ = v_it_x27_3182_;
v_res_3166_ = v_c_3180_;
goto v___jp_3164_;
}
}
else
{
lean_dec(v_snd_3170_);
lean_dec_ref(v_a_3163_);
v_pos_3165_ = v_it_x27_3182_;
v_res_3166_ = v_c_3180_;
goto v___jp_3164_;
}
}
else
{
lean_dec(v_snd_3170_);
lean_dec_ref(v_a_3163_);
v_pos_3165_ = v_it_x27_3182_;
v_res_3166_ = v_c_3180_;
goto v___jp_3164_;
}
}
else
{
lean_dec(v_snd_3170_);
lean_dec_ref(v_a_3163_);
v_pos_3165_ = v_it_x27_3182_;
v_res_3166_ = v_c_3180_;
goto v___jp_3164_;
}
}
v___jp_3193_:
{
if (v___y_3194_ == 0)
{
uint32_t v___x_3195_; uint8_t v___x_3196_; 
v___x_3195_ = 48;
v___x_3196_ = lean_uint32_dec_le(v___x_3195_, v_c_3180_);
if (v___x_3196_ == 0)
{
v___y_3184_ = v___y_3194_;
v___y_3185_ = v___x_3196_;
goto v___jp_3183_;
}
else
{
uint32_t v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = 57;
v___x_3198_ = lean_uint32_dec_le(v_c_3180_, v___x_3197_);
v___y_3184_ = v___y_3194_;
v___y_3185_ = v___x_3198_;
goto v___jp_3183_;
}
}
else
{
lean_dec(v_snd_3170_);
lean_dec_ref(v_a_3163_);
v_pos_3165_ = v_it_x27_3182_;
v_res_3166_ = v_c_3180_;
goto v___jp_3164_;
}
}
v___jp_3199_:
{
uint32_t v___x_3200_; uint8_t v___x_3201_; 
v___x_3200_ = 97;
v___x_3201_ = lean_uint32_dec_le(v___x_3200_, v_c_3180_);
if (v___x_3201_ == 0)
{
v___y_3194_ = v___x_3201_;
goto v___jp_3193_;
}
else
{
uint32_t v___x_3202_; uint8_t v___x_3203_; 
v___x_3202_ = 122;
v___x_3203_ = lean_uint32_dec_le(v_c_3180_, v___x_3202_);
v___y_3194_ = v___x_3203_;
goto v___jp_3193_;
}
}
}
else
{
lean_object* v___x_3208_; 
v___x_3208_ = lean_box(0);
lean_inc(v_snd_3170_);
v_pos_3172_ = v_a_3163_;
v_snd_3173_ = v_snd_3170_;
v_err_3174_ = v___x_3208_;
goto v___jp_3171_;
}
v___jp_3164_:
{
lean_object* v___x_3167_; 
v___x_3167_ = lean_string_push(v_acc_3162_, v_res_3166_);
v_acc_3162_ = v___x_3167_;
v_a_3163_ = v_pos_3165_;
goto _start;
}
v___jp_3171_:
{
uint8_t v___x_3175_; 
v___x_3175_ = lean_nat_dec_eq(v_snd_3170_, v_snd_3173_);
lean_dec(v_snd_3173_);
lean_dec(v_snd_3170_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; 
lean_dec_ref(v_acc_3162_);
lean_inc(v_err_3174_);
v___x_3176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3176_, 0, v_pos_3172_);
lean_ctor_set(v___x_3176_, 1, v_err_3174_);
return v___x_3176_;
}
else
{
lean_object* v___x_3177_; 
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_pos_3172_);
lean_ctor_set(v___x_3177_, 1, v_acc_3162_);
return v___x_3177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object* v_acc_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v_pos_3212_; uint32_t v_res_3213_; lean_object* v_fst_3216_; lean_object* v_snd_3217_; lean_object* v_pos_3219_; lean_object* v_snd_3220_; lean_object* v_err_3221_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v_fst_3216_ = lean_ctor_get(v_a_3210_, 0);
v_snd_3217_ = lean_ctor_get(v_a_3210_, 1);
lean_inc(v_snd_3217_);
v___x_3225_ = lean_string_utf8_byte_size(v_fst_3216_);
v___x_3226_ = lean_nat_dec_eq(v_snd_3217_, v___x_3225_);
if (v___x_3226_ == 0)
{
uint32_t v_c_3227_; lean_object* v___x_3228_; lean_object* v_it_x27_3229_; uint8_t v___y_3231_; uint8_t v___y_3232_; uint8_t v___y_3241_; uint32_t v___x_3251_; uint8_t v___x_3252_; 
v_c_3227_ = lean_string_utf8_get_fast(v_fst_3216_, v_snd_3217_);
v___x_3228_ = lean_string_utf8_next_fast(v_fst_3216_, v_snd_3217_);
lean_inc(v_fst_3216_);
v_it_x27_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3229_, 0, v_fst_3216_);
lean_ctor_set(v_it_x27_3229_, 1, v___x_3228_);
v___x_3251_ = 65;
v___x_3252_ = lean_uint32_dec_le(v___x_3251_, v_c_3227_);
if (v___x_3252_ == 0)
{
goto v___jp_3246_;
}
else
{
uint32_t v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = 90;
v___x_3254_ = lean_uint32_dec_le(v_c_3227_, v___x_3253_);
if (v___x_3254_ == 0)
{
goto v___jp_3246_;
}
else
{
lean_dec(v_snd_3217_);
lean_dec_ref(v_a_3210_);
v_pos_3212_ = v_it_x27_3229_;
v_res_3213_ = v_c_3227_;
goto v___jp_3211_;
}
}
v___jp_3230_:
{
if (v___y_3232_ == 0)
{
uint32_t v___x_3233_; uint8_t v___x_3234_; 
v___x_3233_ = 95;
v___x_3234_ = lean_uint32_dec_eq(v_c_3227_, v___x_3233_);
if (v___x_3234_ == 0)
{
uint32_t v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = 45;
v___x_3236_ = lean_uint32_dec_eq(v_c_3227_, v___x_3235_);
if (v___x_3236_ == 0)
{
uint32_t v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = 47;
v___x_3238_ = lean_uint32_dec_eq(v_c_3227_, v___x_3237_);
if (v___x_3238_ == 0)
{
if (v___y_3231_ == 0)
{
lean_object* v___x_3239_; 
lean_dec_ref_known(v_it_x27_3229_, 2);
v___x_3239_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3217_);
v_pos_3219_ = v_a_3210_;
v_snd_3220_ = v_snd_3217_;
v_err_3221_ = v___x_3239_;
goto v___jp_3218_;
}
else
{
lean_dec(v_snd_3217_);
lean_dec_ref(v_a_3210_);
v_pos_3212_ = v_it_x27_3229_;
v_res_3213_ = v_c_3227_;
goto v___jp_3211_;
}
}
else
{
lean_dec(v_snd_3217_);
lean_dec_ref(v_a_3210_);
v_pos_3212_ = v_it_x27_3229_;
v_res_3213_ = v_c_3227_;
goto v___jp_3211_;
}
}
else
{
lean_dec(v_snd_3217_);
lean_dec_ref(v_a_3210_);
v_pos_3212_ = v_it_x27_3229_;
v_res_3213_ = v_c_3227_;
goto v___jp_3211_;
}
}
else
{
lean_dec(v_snd_3217_);
lean_dec_ref(v_a_3210_);
v_pos_3212_ = v_it_x27_3229_;
v_res_3213_ = v_c_3227_;
goto v___jp_3211_;
}
}
else
{
lean_dec(v_snd_3217_);
lean_dec_ref(v_a_3210_);
v_pos_3212_ = v_it_x27_3229_;
v_res_3213_ = v_c_3227_;
goto v___jp_3211_;
}
}
v___jp_3240_:
{
if (v___y_3241_ == 0)
{
uint32_t v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = 48;
v___x_3243_ = lean_uint32_dec_le(v___x_3242_, v_c_3227_);
if (v___x_3243_ == 0)
{
v___y_3231_ = v___y_3241_;
v___y_3232_ = v___x_3243_;
goto v___jp_3230_;
}
else
{
uint32_t v___x_3244_; uint8_t v___x_3245_; 
v___x_3244_ = 57;
v___x_3245_ = lean_uint32_dec_le(v_c_3227_, v___x_3244_);
v___y_3231_ = v___y_3241_;
v___y_3232_ = v___x_3245_;
goto v___jp_3230_;
}
}
else
{
lean_dec(v_snd_3217_);
lean_dec_ref(v_a_3210_);
v_pos_3212_ = v_it_x27_3229_;
v_res_3213_ = v_c_3227_;
goto v___jp_3211_;
}
}
v___jp_3246_:
{
uint32_t v___x_3247_; uint8_t v___x_3248_; 
v___x_3247_ = 97;
v___x_3248_ = lean_uint32_dec_le(v___x_3247_, v_c_3227_);
if (v___x_3248_ == 0)
{
v___y_3241_ = v___x_3248_;
goto v___jp_3240_;
}
else
{
uint32_t v___x_3249_; uint8_t v___x_3250_; 
v___x_3249_ = 122;
v___x_3250_ = lean_uint32_dec_le(v_c_3227_, v___x_3249_);
v___y_3241_ = v___x_3250_;
goto v___jp_3240_;
}
}
}
else
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_box(0);
lean_inc(v_snd_3217_);
v_pos_3219_ = v_a_3210_;
v_snd_3220_ = v_snd_3217_;
v_err_3221_ = v___x_3255_;
goto v___jp_3218_;
}
v___jp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = lean_string_push(v_acc_3209_, v_res_3213_);
v___x_3215_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(v___x_3214_, v_pos_3212_);
return v___x_3215_;
}
v___jp_3218_:
{
uint8_t v___x_3222_; 
v___x_3222_ = lean_nat_dec_eq(v_snd_3217_, v_snd_3220_);
lean_dec(v_snd_3220_);
lean_dec(v_snd_3217_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; 
lean_dec_ref(v_acc_3209_);
lean_inc(v_err_3221_);
v___x_3223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3223_, 0, v_pos_3219_);
lean_ctor_set(v___x_3223_, 1, v_err_3221_);
return v___x_3223_;
}
else
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v_pos_3219_);
lean_ctor_set(v___x_3224_, 1, v_acc_3209_);
return v___x_3224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object* v_a_3256_){
_start:
{
lean_object* v_fst_3257_; lean_object* v_snd_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v_fst_3257_ = lean_ctor_get(v_a_3256_, 0);
v_snd_3258_ = lean_ctor_get(v_a_3256_, 1);
v___x_3259_ = lean_string_utf8_byte_size(v_fst_3257_);
v___x_3260_ = lean_nat_dec_eq(v_snd_3258_, v___x_3259_);
if (v___x_3260_ == 0)
{
uint32_t v_c_3261_; lean_object* v___x_3262_; uint8_t v___y_3269_; uint8_t v___y_3270_; uint8_t v___y_3280_; uint32_t v___x_3290_; uint8_t v___x_3291_; 
v_c_3261_ = lean_string_utf8_get_fast(v_fst_3257_, v_snd_3258_);
v___x_3262_ = lean_string_utf8_next_fast(v_fst_3257_, v_snd_3258_);
v___x_3290_ = 65;
v___x_3291_ = lean_uint32_dec_le(v___x_3290_, v_c_3261_);
if (v___x_3291_ == 0)
{
goto v___jp_3285_;
}
else
{
uint32_t v___x_3292_; uint8_t v___x_3293_; 
v___x_3292_ = 90;
v___x_3293_ = lean_uint32_dec_le(v_c_3261_, v___x_3292_);
if (v___x_3293_ == 0)
{
goto v___jp_3285_;
}
else
{
lean_inc(v_fst_3257_);
lean_dec_ref(v_a_3256_);
goto v___jp_3263_;
}
}
v___jp_3263_:
{
lean_object* v_it_x27_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v_it_x27_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3264_, 0, v_fst_3257_);
lean_ctor_set(v_it_x27_3264_, 1, v___x_3262_);
v___x_3265_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3266_ = lean_string_push(v___x_3265_, v_c_3261_);
v___x_3267_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(v___x_3266_, v_it_x27_3264_);
return v___x_3267_;
}
v___jp_3268_:
{
if (v___y_3270_ == 0)
{
uint32_t v___x_3271_; uint8_t v___x_3272_; 
v___x_3271_ = 95;
v___x_3272_ = lean_uint32_dec_eq(v_c_3261_, v___x_3271_);
if (v___x_3272_ == 0)
{
uint32_t v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = 45;
v___x_3274_ = lean_uint32_dec_eq(v_c_3261_, v___x_3273_);
if (v___x_3274_ == 0)
{
uint32_t v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = 47;
v___x_3276_ = lean_uint32_dec_eq(v_c_3261_, v___x_3275_);
if (v___x_3276_ == 0)
{
if (v___y_3269_ == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3278_, 0, v_a_3256_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
return v___x_3278_;
}
else
{
lean_inc(v_fst_3257_);
lean_dec_ref(v_a_3256_);
goto v___jp_3263_;
}
}
else
{
lean_inc(v_fst_3257_);
lean_dec_ref(v_a_3256_);
goto v___jp_3263_;
}
}
else
{
lean_inc(v_fst_3257_);
lean_dec_ref(v_a_3256_);
goto v___jp_3263_;
}
}
else
{
lean_inc(v_fst_3257_);
lean_dec_ref(v_a_3256_);
goto v___jp_3263_;
}
}
else
{
lean_inc(v_fst_3257_);
lean_dec_ref(v_a_3256_);
goto v___jp_3263_;
}
}
v___jp_3279_:
{
if (v___y_3280_ == 0)
{
uint32_t v___x_3281_; uint8_t v___x_3282_; 
v___x_3281_ = 48;
v___x_3282_ = lean_uint32_dec_le(v___x_3281_, v_c_3261_);
if (v___x_3282_ == 0)
{
v___y_3269_ = v___y_3280_;
v___y_3270_ = v___x_3282_;
goto v___jp_3268_;
}
else
{
uint32_t v___x_3283_; uint8_t v___x_3284_; 
v___x_3283_ = 57;
v___x_3284_ = lean_uint32_dec_le(v_c_3261_, v___x_3283_);
v___y_3269_ = v___y_3280_;
v___y_3270_ = v___x_3284_;
goto v___jp_3268_;
}
}
else
{
lean_inc(v_fst_3257_);
lean_dec_ref(v_a_3256_);
goto v___jp_3263_;
}
}
v___jp_3285_:
{
uint32_t v___x_3286_; uint8_t v___x_3287_; 
v___x_3286_ = 97;
v___x_3287_ = lean_uint32_dec_le(v___x_3286_, v_c_3261_);
if (v___x_3287_ == 0)
{
v___y_3280_ = v___x_3287_;
goto v___jp_3279_;
}
else
{
uint32_t v___x_3288_; uint8_t v___x_3289_; 
v___x_3288_ = 122;
v___x_3289_ = lean_uint32_dec_le(v_c_3261_, v___x_3288_);
v___y_3280_ = v___x_3289_;
goto v___jp_3279_;
}
}
}
else
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = lean_box(0);
v___x_3295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3295_, 0, v_a_3256_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
return v___x_3295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object* v_n_3298_, lean_object* v_m_3299_, lean_object* v_parser_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_apply_1(v_parser_3300_, v_a_3301_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_pos_3303_; lean_object* v_res_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3324_; 
v_pos_3303_ = lean_ctor_get(v___x_3302_, 0);
v_res_3304_ = lean_ctor_get(v___x_3302_, 1);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3306_ = v___x_3302_;
v_isShared_3307_ = v_isSharedCheck_3324_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_res_3304_);
lean_inc(v_pos_3303_);
lean_dec(v___x_3302_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3324_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
uint8_t v___x_3320_; 
v___x_3320_ = lean_nat_dec_le(v_n_3298_, v_res_3304_);
if (v___x_3320_ == 0)
{
lean_dec(v_res_3304_);
goto v___jp_3308_;
}
else
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_nat_dec_le(v_res_3304_, v_m_3299_);
if (v___x_3321_ == 0)
{
lean_dec(v_res_3304_);
goto v___jp_3308_;
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_del_object(v___x_3306_);
lean_dec(v_m_3299_);
lean_dec(v_n_3298_);
v___x_3322_ = lean_nat_to_int(v_res_3304_);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v_pos_3303_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
return v___x_3323_;
}
}
v___jp_3308_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3309_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0));
v___x_3310_ = l_Nat_reprFast(v_n_3298_);
v___x_3311_ = lean_string_append(v___x_3309_, v___x_3310_);
lean_dec_ref(v___x_3310_);
v___x_3312_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1));
v___x_3313_ = lean_string_append(v___x_3311_, v___x_3312_);
v___x_3314_ = l_Nat_reprFast(v_m_3299_);
v___x_3315_ = lean_string_append(v___x_3313_, v___x_3314_);
lean_dec_ref(v___x_3314_);
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set_tag(v___x_3306_, 1);
lean_ctor_set(v___x_3306_, 1, v___x_3316_);
v___x_3318_ = v___x_3306_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_pos_3303_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
else
{
lean_object* v_pos_3325_; lean_object* v_err_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_m_3299_);
lean_dec(v_n_3298_);
v_pos_3325_ = lean_ctor_get(v___x_3302_, 0);
v_err_3326_ = lean_ctor_get(v___x_3302_, 1);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3302_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_err_3326_);
lean_inc(v_pos_3325_);
lean_dec(v___x_3302_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_pos_3325_);
lean_ctor_set(v_reuseFailAlloc_3332_, 1, v_err_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object* v_a_3334_){
_start:
{
lean_object* v_fst_3335_; lean_object* v_snd_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v_fst_3335_ = lean_ctor_get(v_a_3334_, 0);
v_snd_3336_ = lean_ctor_get(v_a_3334_, 1);
v___x_3337_ = lean_string_utf8_byte_size(v_fst_3335_);
v___x_3338_ = lean_nat_dec_eq(v_snd_3336_, v___x_3337_);
if (v___x_3338_ == 0)
{
uint32_t v_c_3339_; lean_object* v___x_3340_; lean_object* v_pos_3342_; lean_object* v_snd_3343_; lean_object* v_err_3344_; lean_object* v_it_x27_3351_; lean_object* v___y_3353_; uint32_t v___y_3354_; uint8_t v___y_3355_; uint8_t v___y_3367_; uint32_t v___x_3387_; uint8_t v___x_3388_; 
v_c_3339_ = lean_string_utf8_get_fast(v_fst_3335_, v_snd_3336_);
v___x_3340_ = lean_string_utf8_next_fast(v_fst_3335_, v_snd_3336_);
lean_inc(v_fst_3335_);
v_it_x27_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3351_, 0, v_fst_3335_);
lean_ctor_set(v_it_x27_3351_, 1, v___x_3340_);
v___x_3387_ = 48;
v___x_3388_ = lean_uint32_dec_le(v___x_3387_, v_c_3339_);
if (v___x_3388_ == 0)
{
v___y_3367_ = v___x_3388_;
goto v___jp_3366_;
}
else
{
uint32_t v___x_3389_; uint8_t v___x_3390_; 
v___x_3389_ = 57;
v___x_3390_ = lean_uint32_dec_le(v_c_3339_, v___x_3389_);
v___y_3367_ = v___x_3390_;
goto v___jp_3366_;
}
v___jp_3341_:
{
uint8_t v___x_3345_; 
v___x_3345_ = lean_nat_dec_eq(v___x_3340_, v_snd_3343_);
lean_dec(v_snd_3343_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; 
lean_inc(v_err_3344_);
v___x_3346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3346_, 0, v_pos_3342_);
lean_ctor_set(v___x_3346_, 1, v_err_3344_);
return v___x_3346_;
}
else
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3347_ = lean_uint32_to_nat(v_c_3339_);
v___x_3348_ = lean_unsigned_to_nat(48u);
v___x_3349_ = lean_nat_sub(v___x_3347_, v___x_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v_pos_3342_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
return v___x_3350_;
}
}
v___jp_3352_:
{
if (v___y_3355_ == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref(v___y_3353_);
v___x_3356_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v_pos_3342_ = v_it_x27_3351_;
v_snd_3343_ = v___x_3340_;
v_err_3344_ = v___x_3356_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_dec_ref_known(v_it_x27_3351_, 2);
v___x_3357_ = lean_uint32_to_nat(v_c_3339_);
v___x_3358_ = lean_unsigned_to_nat(48u);
v___x_3359_ = lean_nat_sub(v___x_3357_, v___x_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_unsigned_to_nat(10u);
v___x_3361_ = lean_nat_mul(v___x_3359_, v___x_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_uint32_to_nat(v___y_3354_);
v___x_3363_ = lean_nat_sub(v___x_3362_, v___x_3358_);
lean_dec(v___x_3362_);
v___x_3364_ = lean_nat_add(v___x_3361_, v___x_3363_);
lean_dec(v___x_3363_);
lean_dec(v___x_3361_);
v___x_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___y_3353_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
return v___x_3365_;
}
}
v___jp_3366_:
{
if (v___y_3367_ == 0)
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec_ref_known(v_it_x27_3351_, 2);
v___x_3368_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3369_, 0, v_a_3334_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
return v___x_3369_;
}
else
{
lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3384_; 
lean_inc(v_fst_3335_);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_a_3334_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; lean_object* v_unused_3386_; 
v_unused_3385_ = lean_ctor_get(v_a_3334_, 1);
lean_dec(v_unused_3385_);
v_unused_3386_ = lean_ctor_get(v_a_3334_, 0);
lean_dec(v_unused_3386_);
v___x_3371_ = v_a_3334_;
v_isShared_3372_ = v_isSharedCheck_3384_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v_a_3334_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3384_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
uint8_t v___x_3373_; 
v___x_3373_ = lean_nat_dec_eq(v___x_3340_, v___x_3337_);
if (v___x_3373_ == 0)
{
uint32_t v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3374_ = lean_string_utf8_get_fast(v_fst_3335_, v___x_3340_);
v___x_3375_ = lean_string_utf8_next_fast(v_fst_3335_, v___x_3340_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 1, v___x_3375_);
v___x_3377_ = v___x_3371_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_fst_3335_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
uint32_t v___x_3378_; uint8_t v___x_3379_; 
v___x_3378_ = 48;
v___x_3379_ = lean_uint32_dec_le(v___x_3378_, v___x_3374_);
if (v___x_3379_ == 0)
{
v___y_3353_ = v___x_3377_;
v___y_3354_ = v___x_3374_;
v___y_3355_ = v___x_3379_;
goto v___jp_3352_;
}
else
{
uint32_t v___x_3380_; uint8_t v___x_3381_; 
v___x_3380_ = 57;
v___x_3381_ = lean_uint32_dec_le(v___x_3374_, v___x_3380_);
v___y_3353_ = v___x_3377_;
v___y_3354_ = v___x_3374_;
v___y_3355_ = v___x_3381_;
goto v___jp_3352_;
}
}
}
else
{
lean_object* v___x_3383_; 
lean_del_object(v___x_3371_);
lean_dec(v_fst_3335_);
v___x_3383_ = lean_box(0);
v_pos_3342_ = v_it_x27_3351_;
v_snd_3343_ = v___x_3340_;
v_err_3344_ = v___x_3383_;
goto v___jp_3341_;
}
}
}
}
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = lean_box(0);
v___x_3392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3392_, 0, v_a_3334_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
return v___x_3392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(lean_object* v_a_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = lean_nat_to_int(v_a_3393_);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___y_3394_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
return v___x_3396_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__0(void){
_start:
{
uint32_t v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = 58;
v___x_3398_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3399_ = lean_string_push(v___x_3398_, v___x_3397_);
return v___x_3399_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__0);
v___x_3401_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3402_ = lean_string_append(v___x_3401_, v___x_3400_);
return v___x_3402_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__2(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3404_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__1);
v___x_3405_ = lean_string_append(v___x_3404_, v___x_3403_);
return v___x_3405_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__2);
v___x_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
return v___x_3407_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = 58;
v___x_3409_ = lean_box_uint32(v___x_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(uint8_t v_withColon_3410_, lean_object* v___y_3411_){
_start:
{
if (v_withColon_3410_ == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed__const__1;
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___y_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
return v___x_3413_;
}
else
{
lean_object* v_fst_3414_; lean_object* v_snd_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
v_fst_3414_ = lean_ctor_get(v___y_3411_, 0);
v_snd_3415_ = lean_ctor_get(v___y_3411_, 1);
v___x_3416_ = lean_string_utf8_byte_size(v_fst_3414_);
v___x_3417_ = lean_nat_dec_eq(v_snd_3415_, v___x_3416_);
if (v___x_3417_ == 0)
{
uint32_t v___x_3418_; uint32_t v_c_3419_; uint8_t v___x_3420_; 
v___x_3418_ = 58;
v_c_3419_ = lean_string_utf8_get_fast(v_fst_3414_, v_snd_3415_);
v___x_3420_ = lean_uint32_dec_eq(v_c_3419_, v___x_3418_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__3);
v___x_3422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___y_3411_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
return v___x_3422_;
}
else
{
lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3432_; 
lean_inc(v_snd_3415_);
lean_inc(v_fst_3414_);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___y_3411_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; lean_object* v_unused_3434_; 
v_unused_3433_ = lean_ctor_get(v___y_3411_, 1);
lean_dec(v_unused_3433_);
v_unused_3434_ = lean_ctor_get(v___y_3411_, 0);
lean_dec(v_unused_3434_);
v___x_3424_ = v___y_3411_;
v_isShared_3425_ = v_isSharedCheck_3432_;
goto v_resetjp_3423_;
}
else
{
lean_dec(v___y_3411_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3432_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v_it_x27_3428_; 
v___x_3426_ = lean_string_utf8_next_fast(v_fst_3414_, v_snd_3415_);
lean_dec(v_snd_3415_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3426_);
v_it_x27_3428_ = v___x_3424_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_fst_3414_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3426_);
v_it_x27_3428_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed__const__1;
v___x_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3430_, 0, v_it_x27_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
return v___x_3430_;
}
}
}
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___y_3411_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
return v___x_3436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed(lean_object* v_withColon_3437_, lean_object* v___y_3438_){
_start:
{
uint8_t v_withColon_boxed_3439_; lean_object* v_res_3440_; 
v_withColon_boxed_3439_ = lean_unbox(v_withColon_3437_);
v_res_3440_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(v_withColon_boxed_3439_, v___y_3438_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object* v___y_3441_, lean_object* v___f_3442_, lean_object* v_n_3443_, uint8_t v_reason_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v_pos_3447_; lean_object* v_err_3448_; 
switch(v_reason_3444_)
{
case 0:
{
lean_object* v___x_3464_; 
v___x_3464_ = lean_apply_1(v___y_3441_, v___y_3445_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_pos_3465_; lean_object* v___x_3466_; 
v_pos_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_pos_3465_);
lean_dec_ref_known(v___x_3464_, 2);
v___x_3466_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3465_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_pos_3467_; lean_object* v_res_3468_; lean_object* v___x_3469_; 
v_pos_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_pos_3467_);
v_res_3468_ = lean_ctor_get(v___x_3466_, 1);
lean_inc(v_res_3468_);
lean_dec_ref_known(v___x_3466_, 2);
v___x_3469_ = lean_apply_2(v___f_3442_, v_res_3468_, v_pos_3467_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_pos_3470_; lean_object* v_res_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3479_; 
v_pos_3470_ = lean_ctor_get(v___x_3469_, 0);
v_res_3471_ = lean_ctor_get(v___x_3469_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3473_ = v___x_3469_;
v_isShared_3474_ = v_isSharedCheck_3479_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_res_3471_);
lean_inc(v_pos_3470_);
lean_dec(v___x_3469_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3479_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3475_, 0, v_res_3471_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 1, v___x_3475_);
v___x_3477_ = v___x_3473_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_pos_3470_);
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
v_pos_3480_ = lean_ctor_get(v___x_3469_, 0);
v_err_3481_ = lean_ctor_get(v___x_3469_, 1);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3469_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_err_3481_);
lean_inc(v_pos_3480_);
lean_dec(v___x_3469_);
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
else
{
lean_object* v_pos_3489_; lean_object* v_err_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec_ref(v___f_3442_);
v_pos_3489_ = lean_ctor_get(v___x_3466_, 0);
v_err_3490_ = lean_ctor_get(v___x_3466_, 1);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3466_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_err_3490_);
lean_inc(v_pos_3489_);
lean_dec(v___x_3466_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_pos_3489_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_err_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
lean_object* v_pos_3498_; lean_object* v_err_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec_ref(v___f_3442_);
v_pos_3498_ = lean_ctor_get(v___x_3464_, 0);
v_err_3499_ = lean_ctor_get(v___x_3464_, 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3464_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_err_3499_);
lean_inc(v_pos_3498_);
lean_dec(v___x_3464_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_pos_3498_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_err_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
case 1:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_dec_ref(v___f_3442_);
lean_dec_ref(v___y_3441_);
v___x_3507_ = lean_box(0);
v___x_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___y_3445_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
return v___x_3508_;
}
default: 
{
lean_object* v___x_3509_; 
lean_inc_ref(v___y_3445_);
v___x_3509_ = lean_apply_1(v___y_3441_, v___y_3445_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_pos_3510_; lean_object* v___x_3511_; 
v_pos_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_pos_3510_);
lean_dec_ref_known(v___x_3509_, 2);
v___x_3511_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3510_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_pos_3512_; lean_object* v_res_3513_; lean_object* v___x_3514_; 
v_pos_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_pos_3512_);
v_res_3513_ = lean_ctor_get(v___x_3511_, 1);
lean_inc(v_res_3513_);
lean_dec_ref_known(v___x_3511_, 2);
v___x_3514_ = lean_apply_2(v___f_3442_, v_res_3513_, v_pos_3512_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_pos_3515_; lean_object* v_res_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3524_; 
lean_dec_ref(v___y_3445_);
v_pos_3515_ = lean_ctor_get(v___x_3514_, 0);
v_res_3516_ = lean_ctor_get(v___x_3514_, 1);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3518_ = v___x_3514_;
v_isShared_3519_ = v_isSharedCheck_3524_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_res_3516_);
lean_inc(v_pos_3515_);
lean_dec(v___x_3514_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3524_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3520_, 0, v_res_3516_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 1, v___x_3520_);
v___x_3522_ = v___x_3518_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_pos_3515_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
else
{
lean_object* v_pos_3525_; lean_object* v_err_3526_; 
v_pos_3525_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_pos_3525_);
v_err_3526_ = lean_ctor_get(v___x_3514_, 1);
lean_inc(v_err_3526_);
lean_dec_ref_known(v___x_3514_, 2);
v_pos_3447_ = v_pos_3525_;
v_err_3448_ = v_err_3526_;
goto v___jp_3446_;
}
}
else
{
lean_object* v_pos_3527_; lean_object* v_err_3528_; 
lean_dec_ref(v___f_3442_);
v_pos_3527_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_pos_3527_);
v_err_3528_ = lean_ctor_get(v___x_3511_, 1);
lean_inc(v_err_3528_);
lean_dec_ref_known(v___x_3511_, 2);
v_pos_3447_ = v_pos_3527_;
v_err_3448_ = v_err_3528_;
goto v___jp_3446_;
}
}
else
{
lean_object* v_pos_3529_; lean_object* v_err_3530_; 
lean_dec_ref(v___f_3442_);
v_pos_3529_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_pos_3529_);
v_err_3530_ = lean_ctor_get(v___x_3509_, 1);
lean_inc(v_err_3530_);
lean_dec_ref_known(v___x_3509_, 2);
v_pos_3447_ = v_pos_3529_;
v_err_3448_ = v_err_3530_;
goto v___jp_3446_;
}
}
}
v___jp_3446_:
{
lean_object* v_snd_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3462_; 
v_snd_3449_ = lean_ctor_get(v___y_3445_, 1);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___y_3445_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; 
v_unused_3463_ = lean_ctor_get(v___y_3445_, 0);
lean_dec(v_unused_3463_);
v___x_3451_ = v___y_3445_;
v_isShared_3452_ = v_isSharedCheck_3462_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_snd_3449_);
lean_dec(v___y_3445_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3462_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v_snd_3453_; uint8_t v___x_3454_; 
v_snd_3453_ = lean_ctor_get(v_pos_3447_, 1);
v___x_3454_ = lean_nat_dec_eq(v_snd_3449_, v_snd_3453_);
lean_dec(v_snd_3449_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3456_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set_tag(v___x_3451_, 1);
lean_ctor_set(v___x_3451_, 1, v_err_3448_);
lean_ctor_set(v___x_3451_, 0, v_pos_3447_);
v___x_3456_ = v___x_3451_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_pos_3447_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_err_3448_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3460_; 
lean_dec(v_err_3448_);
v___x_3458_ = lean_box(0);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 1, v___x_3458_);
lean_ctor_set(v___x_3451_, 0, v_pos_3447_);
v___x_3460_ = v___x_3451_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_pos_3447_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v___x_3458_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object* v___y_3531_, lean_object* v___f_3532_, lean_object* v_n_3533_, lean_object* v_reason_3534_, lean_object* v___y_3535_){
_start:
{
uint8_t v_reason_boxed_3536_; lean_object* v_res_3537_; 
v_reason_boxed_3536_ = lean_unbox(v_reason_3534_);
v_res_3537_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3531_, v___f_3532_, v_n_3533_, v_reason_boxed_3536_, v___y_3535_);
lean_dec_ref(v_n_3533_);
return v_res_3537_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = lean_unsigned_to_nat(3600u);
v___x_3541_ = lean_nat_to_int(v___x_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = lean_unsigned_to_nat(1u);
v___x_3544_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3543_);
return v___x_3544_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5(void){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = lean_unsigned_to_nat(59u);
v___x_3546_ = lean_nat_to_int(v___x_3545_);
return v___x_3546_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = lean_unsigned_to_nat(23u);
v___x_3550_ = lean_nat_to_int(v___x_3549_);
return v___x_3550_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = lean_unsigned_to_nat(60u);
v___x_3552_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3551_);
return v___x_3552_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11(void){
_start:
{
uint32_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = 45;
v___x_3555_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3556_ = lean_string_push(v___x_3555_, v___x_3554_);
return v___x_3556_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11);
v___x_3558_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3559_ = lean_string_append(v___x_3558_, v___x_3557_);
return v___x_3559_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3561_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12);
v___x_3562_ = lean_string_append(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13);
v___x_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
return v___x_3564_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15(void){
_start:
{
uint32_t v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = 43;
v___x_3566_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3567_ = lean_string_push(v___x_3566_, v___x_3565_);
return v___x_3567_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15);
v___x_3569_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3570_ = lean_string_append(v___x_3569_, v___x_3568_);
return v___x_3570_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3571_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3572_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16);
v___x_3573_ = lean_string_append(v___x_3572_, v___x_3571_);
return v___x_3573_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17);
v___x_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t v_withMinutes_3576_, uint8_t v_withSeconds_3577_, uint8_t v_withColon_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3622_; lean_object* v_fst_3625_; lean_object* v_snd_3626_; lean_object* v___f_3627_; lean_object* v___x_3628_; lean_object* v___y_3629_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v_pos_3675_; lean_object* v_res_3676_; lean_object* v_pos_3734_; lean_object* v_fst_3735_; lean_object* v_snd_3736_; lean_object* v_err_3737_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v_fst_3625_ = lean_ctor_get(v_a_3579_, 0);
lean_inc(v_fst_3625_);
v_snd_3626_ = lean_ctor_get(v_a_3579_, 1);
lean_inc(v_snd_3626_);
v___f_3627_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3));
v___x_3628_ = lean_box(v_withColon_3578_);
v___y_3629_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed), 2, 1);
lean_closure_set(v___y_3629_, 0, v___x_3628_);
v___x_3750_ = lean_string_utf8_byte_size(v_fst_3625_);
v___x_3751_ = lean_nat_dec_eq(v_snd_3626_, v___x_3750_);
if (v___x_3751_ == 0)
{
uint32_t v___x_3752_; uint32_t v_c_3753_; uint8_t v___x_3754_; 
v___x_3752_ = 43;
v_c_3753_ = lean_string_utf8_get_fast(v_fst_3625_, v_snd_3626_);
v___x_3754_ = lean_uint32_dec_eq(v_c_3753_, v___x_3752_);
if (v___x_3754_ == 0)
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18);
lean_inc(v_snd_3626_);
v_pos_3734_ = v_a_3579_;
v_fst_3735_ = v_fst_3625_;
v_snd_3736_ = v_snd_3626_;
v_err_3737_ = v___x_3755_;
goto v___jp_3733_;
}
else
{
lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3764_; 
v_isSharedCheck_3764_ = !lean_is_exclusive(v_a_3579_);
if (v_isSharedCheck_3764_ == 0)
{
lean_object* v_unused_3765_; lean_object* v_unused_3766_; 
v_unused_3765_ = lean_ctor_get(v_a_3579_, 1);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_a_3579_, 0);
lean_dec(v_unused_3766_);
v___x_3757_ = v_a_3579_;
v_isShared_3758_ = v_isSharedCheck_3764_;
goto v_resetjp_3756_;
}
else
{
lean_dec(v_a_3579_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3764_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3759_; lean_object* v_it_x27_3761_; 
v___x_3759_ = lean_string_utf8_next_fast(v_fst_3625_, v_snd_3626_);
lean_dec(v_snd_3626_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 1, v___x_3759_);
v_it_x27_3761_ = v___x_3757_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_fst_3625_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v___x_3759_);
v_it_x27_3761_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v_pos_3675_ = v_it_x27_3761_;
v_res_3676_ = v___x_3762_;
goto v___jp_3674_;
}
}
}
}
else
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_box(0);
lean_inc(v_snd_3626_);
v_pos_3734_ = v_a_3579_;
v_fst_3735_ = v_fst_3625_;
v_snd_3736_ = v_snd_3626_;
v_err_3737_ = v___x_3767_;
goto v___jp_3733_;
}
v___jp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3583_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0));
v___x_3584_ = l_Int_repr(v___y_3582_);
lean_dec(v___y_3582_);
v___x_3585_ = lean_string_append(v___x_3583_, v___x_3584_);
lean_dec_ref(v___x_3584_);
v___x_3586_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1));
v___x_3587_ = lean_string_append(v___x_3585_, v___x_3586_);
v___x_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
v___x_3589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___y_3581_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
return v___x_3589_;
}
v___jp_3590_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = lean_int_add(v___y_3591_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec(v___y_3591_);
v___x_3596_ = lean_int_mul(v___x_3595_, v___y_3592_);
lean_dec(v___x_3595_);
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___y_3593_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
return v___x_3597_;
}
v___jp_3598_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3605_ = lean_nat_to_int(v___y_3600_);
v___x_3606_ = lean_int_mul(v___y_3604_, v___x_3605_);
lean_dec(v___x_3605_);
lean_dec(v___y_3604_);
v___x_3607_ = lean_int_add(v___y_3599_, v___x_3606_);
lean_dec(v___x_3606_);
lean_dec(v___y_3599_);
if (lean_obj_tag(v___y_3601_) == 0)
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_3591_ = v___x_3607_;
v___y_3592_ = v___y_3602_;
v___y_3593_ = v___y_3603_;
v___y_3594_ = v___x_3608_;
goto v___jp_3590_;
}
else
{
lean_object* v_val_3609_; 
v_val_3609_ = lean_ctor_get(v___y_3601_, 0);
lean_inc(v_val_3609_);
lean_dec_ref_known(v___y_3601_, 1);
v___y_3591_ = v___x_3607_;
v___y_3592_ = v___y_3602_;
v___y_3593_ = v___y_3603_;
v___y_3594_ = v_val_3609_;
goto v___jp_3590_;
}
}
v___jp_3610_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2);
v___x_3618_ = lean_int_mul(v___y_3615_, v___x_3617_);
lean_dec(v___y_3615_);
if (lean_obj_tag(v___y_3611_) == 0)
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_3599_ = v___x_3618_;
v___y_3600_ = v___y_3612_;
v___y_3601_ = v___y_3613_;
v___y_3602_ = v___y_3614_;
v___y_3603_ = v___y_3616_;
v___y_3604_ = v___x_3619_;
goto v___jp_3598_;
}
else
{
lean_object* v_val_3620_; 
v_val_3620_ = lean_ctor_get(v___y_3611_, 0);
lean_inc(v_val_3620_);
lean_dec_ref_known(v___y_3611_, 1);
v___y_3599_ = v___x_3618_;
v___y_3600_ = v___y_3612_;
v___y_3601_ = v___y_3613_;
v___y_3602_ = v___y_3614_;
v___y_3603_ = v___y_3616_;
v___y_3604_ = v_val_3620_;
goto v___jp_3598_;
}
}
v___jp_3621_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3623_ = lean_box(0);
v___x_3624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___y_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
return v___x_3624_;
}
v___jp_3630_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4);
v___x_3637_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3629_, v___f_3627_, v___x_3636_, v_withSeconds_3577_, v___y_3635_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_res_3638_; 
v_res_3638_ = lean_ctor_get(v___x_3637_, 1);
lean_inc(v_res_3638_);
if (lean_obj_tag(v_res_3638_) == 1)
{
lean_object* v_pos_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3662_; 
v_pos_3639_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3662_ == 0)
{
lean_object* v_unused_3663_; 
v_unused_3663_ = lean_ctor_get(v___x_3637_, 1);
lean_dec(v_unused_3663_);
v___x_3641_ = v___x_3637_;
v_isShared_3642_ = v_isSharedCheck_3662_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_pos_3639_);
lean_dec(v___x_3637_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3662_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v_val_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v_val_3643_ = lean_ctor_get(v_res_3638_, 0);
v___x_3644_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_3645_ = lean_int_dec_lt(v___x_3644_, v_val_3643_);
if (v___x_3645_ == 0)
{
lean_del_object(v___x_3641_);
v___y_3611_ = v___y_3631_;
v___y_3612_ = v___y_3632_;
v___y_3613_ = v_res_3638_;
v___y_3614_ = v___y_3633_;
v___y_3615_ = v___y_3634_;
v___y_3616_ = v_pos_3639_;
goto v___jp_3610_;
}
else
{
lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3660_; 
lean_inc(v_val_3643_);
lean_dec(v___y_3634_);
lean_dec(v___y_3632_);
lean_dec(v___y_3631_);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_res_3638_);
if (v_isSharedCheck_3660_ == 0)
{
lean_object* v_unused_3661_; 
v_unused_3661_ = lean_ctor_get(v_res_3638_, 0);
lean_dec(v_unused_3661_);
v___x_3647_ = v_res_3638_;
v_isShared_3648_ = v_isSharedCheck_3660_;
goto v_resetjp_3646_;
}
else
{
lean_dec(v_res_3638_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3660_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3649_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6));
v___x_3650_ = l_Int_repr(v_val_3643_);
lean_dec(v_val_3643_);
v___x_3651_ = lean_string_append(v___x_3649_, v___x_3650_);
lean_dec_ref(v___x_3650_);
v___x_3652_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3653_ = lean_string_append(v___x_3651_, v___x_3652_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v___x_3653_);
v___x_3655_ = v___x_3647_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3653_);
v___x_3655_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3657_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set_tag(v___x_3641_, 1);
lean_ctor_set(v___x_3641_, 1, v___x_3655_);
v___x_3657_ = v___x_3641_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_pos_3639_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3664_; 
v_pos_3664_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_pos_3664_);
lean_dec_ref_known(v___x_3637_, 2);
v___y_3611_ = v___y_3631_;
v___y_3612_ = v___y_3632_;
v___y_3613_ = v_res_3638_;
v___y_3614_ = v___y_3633_;
v___y_3615_ = v___y_3634_;
v___y_3616_ = v_pos_3664_;
goto v___jp_3610_;
}
}
else
{
lean_object* v_pos_3665_; lean_object* v_err_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v___y_3634_);
lean_dec(v___y_3632_);
lean_dec(v___y_3631_);
v_pos_3665_ = lean_ctor_get(v___x_3637_, 0);
v_err_3666_ = lean_ctor_get(v___x_3637_, 1);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3637_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_err_3666_);
lean_inc(v_pos_3665_);
lean_dec(v___x_3637_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_pos_3665_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_err_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
v___jp_3674_:
{
lean_object* v___x_3677_; 
v___x_3677_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3675_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_pos_3678_; lean_object* v_res_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v_pos_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_pos_3678_);
v_res_3679_ = lean_ctor_get(v___x_3677_, 1);
lean_inc(v_res_3679_);
lean_dec_ref_known(v___x_3677_, 2);
v___x_3680_ = lean_nat_to_int(v_res_3679_);
v___x_3681_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_3682_ = lean_int_dec_lt(v___x_3680_, v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3683_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8);
v___x_3684_ = lean_int_dec_lt(v___x_3683_, v___x_3680_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = lean_unsigned_to_nat(60u);
v___x_3686_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9);
lean_inc_ref(v___y_3629_);
v___x_3687_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3629_, v___f_3627_, v___x_3686_, v_withMinutes_3576_, v_pos_3678_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_res_3688_; 
v_res_3688_ = lean_ctor_get(v___x_3687_, 1);
lean_inc(v_res_3688_);
if (lean_obj_tag(v_res_3688_) == 1)
{
lean_object* v_pos_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3712_; 
v_pos_3689_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3712_ == 0)
{
lean_object* v_unused_3713_; 
v_unused_3713_ = lean_ctor_get(v___x_3687_, 1);
lean_dec(v_unused_3713_);
v___x_3691_ = v___x_3687_;
v_isShared_3692_ = v_isSharedCheck_3712_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_pos_3689_);
lean_dec(v___x_3687_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3712_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v_val_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
v_val_3693_ = lean_ctor_get(v_res_3688_, 0);
v___x_3694_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_3695_ = lean_int_dec_lt(v___x_3694_, v_val_3693_);
if (v___x_3695_ == 0)
{
lean_del_object(v___x_3691_);
v___y_3631_ = v_res_3688_;
v___y_3632_ = v___x_3685_;
v___y_3633_ = v_res_3676_;
v___y_3634_ = v___x_3680_;
v___y_3635_ = v_pos_3689_;
goto v___jp_3630_;
}
else
{
lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3710_; 
lean_inc(v_val_3693_);
lean_dec(v___x_3680_);
lean_dec_ref(v___y_3629_);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_res_3688_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; 
v_unused_3711_ = lean_ctor_get(v_res_3688_, 0);
lean_dec(v_unused_3711_);
v___x_3697_ = v_res_3688_;
v_isShared_3698_ = v_isSharedCheck_3710_;
goto v_resetjp_3696_;
}
else
{
lean_dec(v_res_3688_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3710_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3699_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10));
v___x_3700_ = l_Int_repr(v_val_3693_);
lean_dec(v_val_3693_);
v___x_3701_ = lean_string_append(v___x_3699_, v___x_3700_);
lean_dec_ref(v___x_3700_);
v___x_3702_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3703_ = lean_string_append(v___x_3701_, v___x_3702_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3703_);
v___x_3705_ = v___x_3697_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3707_; 
if (v_isShared_3692_ == 0)
{
lean_ctor_set_tag(v___x_3691_, 1);
lean_ctor_set(v___x_3691_, 1, v___x_3705_);
v___x_3707_ = v___x_3691_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_pos_3689_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3714_; 
v_pos_3714_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_pos_3714_);
lean_dec_ref_known(v___x_3687_, 2);
v___y_3631_ = v_res_3688_;
v___y_3632_ = v___x_3685_;
v___y_3633_ = v_res_3676_;
v___y_3634_ = v___x_3680_;
v___y_3635_ = v_pos_3714_;
goto v___jp_3630_;
}
}
else
{
lean_object* v_pos_3715_; lean_object* v_err_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v___x_3680_);
lean_dec_ref(v___y_3629_);
v_pos_3715_ = lean_ctor_get(v___x_3687_, 0);
v_err_3716_ = lean_ctor_get(v___x_3687_, 1);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3687_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_err_3716_);
lean_inc(v_pos_3715_);
lean_dec(v___x_3687_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_pos_3715_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_err_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_dec_ref(v___y_3629_);
v___y_3581_ = v_pos_3678_;
v___y_3582_ = v___x_3680_;
goto v___jp_3580_;
}
}
else
{
lean_dec_ref(v___y_3629_);
v___y_3581_ = v_pos_3678_;
v___y_3582_ = v___x_3680_;
goto v___jp_3580_;
}
}
else
{
lean_object* v_pos_3724_; lean_object* v_err_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec_ref(v___y_3629_);
v_pos_3724_ = lean_ctor_get(v___x_3677_, 0);
v_err_3725_ = lean_ctor_get(v___x_3677_, 1);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3677_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_err_3725_);
lean_inc(v_pos_3724_);
lean_dec(v___x_3677_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_pos_3724_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_err_3725_);
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
v___jp_3733_:
{
uint8_t v___x_3738_; 
v___x_3738_ = lean_nat_dec_eq(v_snd_3626_, v_snd_3736_);
lean_dec(v_snd_3626_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; 
lean_dec(v_snd_3736_);
lean_dec(v_fst_3735_);
lean_dec_ref(v___y_3629_);
lean_inc(v_err_3737_);
v___x_3739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3739_, 0, v_pos_3734_);
lean_ctor_set(v___x_3739_, 1, v_err_3737_);
return v___x_3739_;
}
else
{
lean_object* v___x_3740_; uint8_t v___x_3741_; 
v___x_3740_ = lean_string_utf8_byte_size(v_fst_3735_);
v___x_3741_ = lean_nat_dec_eq(v_snd_3736_, v___x_3740_);
if (v___x_3741_ == 0)
{
if (v___x_3738_ == 0)
{
lean_dec(v_snd_3736_);
lean_dec(v_fst_3735_);
lean_dec_ref(v___y_3629_);
v___y_3622_ = v_pos_3734_;
goto v___jp_3621_;
}
else
{
uint32_t v___x_3742_; uint32_t v_c_3743_; uint8_t v___x_3744_; 
v___x_3742_ = 45;
v_c_3743_ = lean_string_utf8_get_fast(v_fst_3735_, v_snd_3736_);
v___x_3744_ = lean_uint32_dec_eq(v_c_3743_, v___x_3742_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec(v_snd_3736_);
lean_dec(v_fst_3735_);
lean_dec_ref(v___y_3629_);
v___x_3745_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14);
v___x_3746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3746_, 0, v_pos_3734_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
return v___x_3746_;
}
else
{
lean_object* v___x_3747_; lean_object* v_it_x27_3748_; lean_object* v___x_3749_; 
lean_dec_ref(v_pos_3734_);
v___x_3747_ = lean_string_utf8_next_fast(v_fst_3735_, v_snd_3736_);
lean_dec(v_snd_3736_);
v_it_x27_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3748_, 0, v_fst_3735_);
lean_ctor_set(v_it_x27_3748_, 1, v___x_3747_);
v___x_3749_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v_pos_3675_ = v_it_x27_3748_;
v_res_3676_ = v___x_3749_;
goto v___jp_3674_;
}
}
}
else
{
lean_dec(v_snd_3736_);
lean_dec(v_fst_3735_);
lean_dec_ref(v___y_3629_);
v___y_3622_ = v_pos_3734_;
goto v___jp_3621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object* v_withMinutes_3768_, lean_object* v_withSeconds_3769_, lean_object* v_withColon_3770_, lean_object* v_a_3771_){
_start:
{
uint8_t v_withMinutes_boxed_3772_; uint8_t v_withSeconds_boxed_3773_; uint8_t v_withColon_boxed_3774_; lean_object* v_res_3775_; 
v_withMinutes_boxed_3772_ = lean_unbox(v_withMinutes_3768_);
v_withSeconds_boxed_3773_ = lean_unbox(v_withSeconds_3769_);
v_withColon_boxed_3774_ = lean_unbox(v_withColon_3770_);
v_res_3775_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_withMinutes_boxed_3772_, v_withSeconds_boxed_3773_, v_withColon_boxed_3774_, v_a_3771_);
return v_res_3775_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_unsigned_to_nat(2000u);
v___x_3779_ = lean_nat_to_int(v___x_3778_);
return v___x_3779_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3785_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3786_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3787_ = lean_int_sub(v___x_3786_, v___x_3785_);
return v___x_3787_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6(void){
_start:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v_range_3790_; 
v___x_3788_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3789_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5);
v_range_3790_ = lean_int_add(v___x_3789_, v___x_3788_);
return v_range_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object* v_config_3793_, lean_object* v_x_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v___y_3797_; 
switch(lean_obj_tag(v_x_3794_))
{
case 0:
{
uint8_t v_presentation_3823_; 
v_presentation_3823_ = lean_ctor_get_uint8(v_x_3794_, 0);
lean_dec_ref_known(v_x_3794_, 0);
switch(v_presentation_3823_)
{
case 1:
{
lean_object* v_dateformat_3824_; lean_object* v_symbols_3825_; lean_object* v___x_3826_; 
v_dateformat_3824_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_3824_);
lean_dec_ref(v_config_3793_);
v_symbols_3825_ = lean_ctor_get(v_dateformat_3824_, 1);
lean_inc_ref(v_symbols_3825_);
lean_dec_ref(v_dateformat_3824_);
v___x_3826_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(v_symbols_3825_, v_a_3795_);
return v___x_3826_;
}
case 2:
{
lean_object* v_dateformat_3827_; lean_object* v_symbols_3828_; lean_object* v___x_3829_; 
v_dateformat_3827_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_3827_);
lean_dec_ref(v_config_3793_);
v_symbols_3828_ = lean_ctor_get(v_dateformat_3827_, 1);
lean_inc_ref(v_symbols_3828_);
lean_dec_ref(v_dateformat_3827_);
v___x_3829_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(v_symbols_3828_, v_a_3795_);
return v___x_3829_;
}
default: 
{
lean_object* v_dateformat_3830_; lean_object* v_symbols_3831_; lean_object* v___x_3832_; 
v_dateformat_3830_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_3830_);
lean_dec_ref(v_config_3793_);
v_symbols_3831_ = lean_ctor_get(v_dateformat_3830_, 1);
lean_inc_ref(v_symbols_3831_);
lean_dec_ref(v_dateformat_3830_);
v___x_3832_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(v_symbols_3831_, v_a_3795_);
return v___x_3832_;
}
}
}
case 1:
{
lean_object* v_presentation_3833_; 
lean_dec_ref(v_config_3793_);
v_presentation_3833_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_3833_);
lean_dec_ref_known(v_x_3794_, 1);
switch(lean_obj_tag(v_presentation_3833_))
{
case 0:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_3835_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3834_, v_a_3795_);
return v___x_3835_;
}
case 1:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = lean_unsigned_to_nat(2u);
v___x_3837_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3836_, v_a_3795_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_pos_3838_; lean_object* v_res_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3849_; 
v_pos_3838_ = lean_ctor_get(v___x_3837_, 0);
v_res_3839_ = lean_ctor_get(v___x_3837_, 1);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3841_ = v___x_3837_;
v_isShared_3842_ = v_isSharedCheck_3849_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_res_3839_);
lean_inc(v_pos_3838_);
lean_dec(v___x_3837_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3849_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3843_ = lean_nat_to_int(v_res_3839_);
v___x_3844_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3845_ = lean_int_add(v___x_3844_, v___x_3843_);
lean_dec(v___x_3843_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 1, v___x_3845_);
v___x_3847_ = v___x_3841_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_pos_3838_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
else
{
lean_object* v_pos_3850_; lean_object* v_err_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
v_pos_3850_ = lean_ctor_get(v___x_3837_, 0);
v_err_3851_ = lean_ctor_get(v___x_3837_, 1);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3837_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_err_3851_);
lean_inc(v_pos_3850_);
lean_dec(v___x_3837_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_pos_3850_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v_err_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
case 2:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_3860_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3859_, v_a_3795_);
return v___x_3860_;
}
default: 
{
lean_object* v_num_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v_num_3861_ = lean_ctor_get(v_presentation_3833_, 0);
lean_inc(v_num_3861_);
lean_dec_ref_known(v_presentation_3833_, 1);
v___x_3862_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_3862_, 0, v_num_3861_);
v___x_3863_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3862_, v_a_3795_);
return v___x_3863_;
}
}
}
case 2:
{
lean_object* v_presentation_3864_; 
lean_dec_ref(v_config_3793_);
v_presentation_3864_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_3864_);
lean_dec_ref_known(v_x_3794_, 1);
switch(lean_obj_tag(v_presentation_3864_))
{
case 0:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = lean_unsigned_to_nat(1u);
v___x_3866_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3865_, v_a_3795_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_pos_3867_; lean_object* v_res_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3876_; 
v_pos_3867_ = lean_ctor_get(v___x_3866_, 0);
v_res_3868_ = lean_ctor_get(v___x_3866_, 1);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3870_ = v___x_3866_;
v_isShared_3871_ = v_isSharedCheck_3876_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_res_3868_);
lean_inc(v_pos_3867_);
lean_dec(v___x_3866_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3876_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
v___x_3872_ = lean_nat_to_int(v_res_3868_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v___x_3872_);
v___x_3874_ = v___x_3870_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_pos_3867_);
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
v_pos_3877_ = lean_ctor_get(v___x_3866_, 0);
v_err_3878_ = lean_ctor_get(v___x_3866_, 1);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3866_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_err_3878_);
lean_inc(v_pos_3877_);
lean_dec(v___x_3866_);
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
case 1:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_unsigned_to_nat(2u);
v___x_3887_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3886_, v_a_3795_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_pos_3888_; lean_object* v_res_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3899_; 
v_pos_3888_ = lean_ctor_get(v___x_3887_, 0);
v_res_3889_ = lean_ctor_get(v___x_3887_, 1);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3891_ = v___x_3887_;
v_isShared_3892_ = v_isSharedCheck_3899_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_res_3889_);
lean_inc(v_pos_3888_);
lean_dec(v___x_3887_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3899_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3893_ = lean_nat_to_int(v_res_3889_);
v___x_3894_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3895_ = lean_int_add(v___x_3894_, v___x_3893_);
lean_dec(v___x_3893_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 1, v___x_3895_);
v___x_3897_ = v___x_3891_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_pos_3888_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
else
{
lean_object* v_pos_3900_; lean_object* v_err_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
v_pos_3900_ = lean_ctor_get(v___x_3887_, 0);
v_err_3901_ = lean_ctor_get(v___x_3887_, 1);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3887_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_err_3901_);
lean_inc(v_pos_3900_);
lean_dec(v___x_3887_);
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
case 2:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = lean_unsigned_to_nat(4u);
v___x_3910_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3909_, v_a_3795_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_pos_3911_; lean_object* v_res_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3920_; 
v_pos_3911_ = lean_ctor_get(v___x_3910_, 0);
v_res_3912_ = lean_ctor_get(v___x_3910_, 1);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3914_ = v___x_3910_;
v_isShared_3915_ = v_isSharedCheck_3920_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_res_3912_);
lean_inc(v_pos_3911_);
lean_dec(v___x_3910_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3920_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3918_; 
v___x_3916_ = lean_nat_to_int(v_res_3912_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 1, v___x_3916_);
v___x_3918_ = v___x_3914_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_pos_3911_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
else
{
lean_object* v_pos_3921_; lean_object* v_err_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
v_pos_3921_ = lean_ctor_get(v___x_3910_, 0);
v_err_3922_ = lean_ctor_get(v___x_3910_, 1);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3910_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_err_3922_);
lean_inc(v_pos_3921_);
lean_dec(v___x_3910_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_pos_3921_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_err_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
default: 
{
lean_object* v_num_3930_; lean_object* v___x_3931_; 
v_num_3930_ = lean_ctor_get(v_presentation_3864_, 0);
lean_inc(v_num_3930_);
lean_dec_ref_known(v_presentation_3864_, 1);
v___x_3931_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_num_3930_, v_a_3795_);
lean_dec(v_num_3930_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_pos_3932_; lean_object* v_res_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3941_; 
v_pos_3932_ = lean_ctor_get(v___x_3931_, 0);
v_res_3933_ = lean_ctor_get(v___x_3931_, 1);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3935_ = v___x_3931_;
v_isShared_3936_ = v_isSharedCheck_3941_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_res_3933_);
lean_inc(v_pos_3932_);
lean_dec(v___x_3931_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3941_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3937_ = lean_nat_to_int(v_res_3933_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 1, v___x_3937_);
v___x_3939_ = v___x_3935_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_pos_3932_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
else
{
lean_object* v_pos_3942_; lean_object* v_err_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
v_pos_3942_ = lean_ctor_get(v___x_3931_, 0);
v_err_3943_ = lean_ctor_get(v___x_3931_, 1);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3931_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_err_3943_);
lean_inc(v_pos_3942_);
lean_dec(v___x_3931_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_pos_3942_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v_err_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
}
case 3:
{
lean_object* v_presentation_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
lean_dec_ref(v_config_3793_);
v_presentation_3951_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_3951_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_3952_ = lean_unsigned_to_nat(1u);
v___x_3953_ = lean_unsigned_to_nat(366u);
v___x_3954_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3954_, 0, v_presentation_3951_);
v___x_3955_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3952_, v___x_3953_, v___x_3954_, v_a_3795_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_pos_3956_; lean_object* v_res_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3967_; 
v_pos_3956_ = lean_ctor_get(v___x_3955_, 0);
v_res_3957_ = lean_ctor_get(v___x_3955_, 1);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3959_ = v___x_3955_;
v_isShared_3960_ = v_isSharedCheck_3967_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_res_3957_);
lean_inc(v_pos_3956_);
lean_dec(v___x_3955_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3967_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
uint8_t v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3965_; 
v___x_3961_ = 1;
v___x_3962_ = lean_box(v___x_3961_);
v___x_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
lean_ctor_set(v___x_3963_, 1, v_res_3957_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 1, v___x_3963_);
v___x_3965_ = v___x_3959_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_pos_3956_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
else
{
lean_object* v_pos_3968_; lean_object* v_err_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
v_pos_3968_ = lean_ctor_get(v___x_3955_, 0);
v_err_3969_ = lean_ctor_get(v___x_3955_, 1);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3955_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_err_3969_);
lean_inc(v_pos_3968_);
lean_dec(v___x_3955_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_pos_3968_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v_err_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
case 4:
{
lean_object* v_presentation_3977_; 
v_presentation_3977_ = lean_ctor_get(v_x_3794_, 0);
lean_inc_ref(v_presentation_3977_);
lean_dec_ref_known(v_x_3794_, 1);
if (lean_obj_tag(v_presentation_3977_) == 0)
{
lean_object* v_val_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_dec_ref(v_config_3793_);
v_val_3978_ = lean_ctor_get(v_presentation_3977_, 0);
lean_inc(v_val_3978_);
lean_dec_ref_known(v_presentation_3977_, 1);
v___x_3979_ = lean_unsigned_to_nat(1u);
v___x_3980_ = lean_unsigned_to_nat(12u);
v___x_3981_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3981_, 0, v_val_3978_);
v___x_3982_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3979_, v___x_3980_, v___x_3981_, v_a_3795_);
return v___x_3982_;
}
else
{
lean_object* v_val_3983_; uint8_t v___x_3984_; 
v_val_3983_ = lean_ctor_get(v_presentation_3977_, 0);
lean_inc(v_val_3983_);
lean_dec_ref_known(v_presentation_3977_, 1);
v___x_3984_ = lean_unbox(v_val_3983_);
lean_dec(v_val_3983_);
switch(v___x_3984_)
{
case 1:
{
lean_object* v_dateformat_3985_; lean_object* v_symbols_3986_; lean_object* v___x_3987_; 
v_dateformat_3985_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_3985_);
lean_dec_ref(v_config_3793_);
v_symbols_3986_ = lean_ctor_get(v_dateformat_3985_, 1);
lean_inc_ref(v_symbols_3986_);
lean_dec_ref(v_dateformat_3985_);
v___x_3987_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_3986_, v_a_3795_);
return v___x_3987_;
}
case 2:
{
lean_object* v_dateformat_3988_; lean_object* v_symbols_3989_; lean_object* v___x_3990_; 
v_dateformat_3988_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_3988_);
lean_dec_ref(v_config_3793_);
v_symbols_3989_ = lean_ctor_get(v_dateformat_3988_, 1);
lean_inc_ref(v_symbols_3989_);
lean_dec_ref(v_dateformat_3988_);
v___x_3990_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_3989_, v_a_3795_);
return v___x_3990_;
}
default: 
{
lean_object* v_dateformat_3991_; lean_object* v_symbols_3992_; lean_object* v___x_3993_; 
v_dateformat_3991_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_3991_);
lean_dec_ref(v_config_3793_);
v_symbols_3992_ = lean_ctor_get(v_dateformat_3991_, 1);
lean_inc_ref(v_symbols_3992_);
lean_dec_ref(v_dateformat_3991_);
v___x_3993_ = l_Std_Time_parseMonthShort(v_symbols_3992_, v_a_3795_);
return v___x_3993_;
}
}
}
}
case 5:
{
lean_object* v_presentation_3994_; 
v_presentation_3994_ = lean_ctor_get(v_x_3794_, 0);
lean_inc_ref(v_presentation_3994_);
lean_dec_ref_known(v_x_3794_, 1);
if (lean_obj_tag(v_presentation_3994_) == 0)
{
lean_object* v_val_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
lean_dec_ref(v_config_3793_);
v_val_3995_ = lean_ctor_get(v_presentation_3994_, 0);
lean_inc(v_val_3995_);
lean_dec_ref_known(v_presentation_3994_, 1);
v___x_3996_ = lean_unsigned_to_nat(1u);
v___x_3997_ = lean_unsigned_to_nat(12u);
v___x_3998_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3998_, 0, v_val_3995_);
v___x_3999_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3996_, v___x_3997_, v___x_3998_, v_a_3795_);
return v___x_3999_;
}
else
{
lean_object* v_val_4000_; uint8_t v___x_4001_; 
v_val_4000_ = lean_ctor_get(v_presentation_3994_, 0);
lean_inc(v_val_4000_);
lean_dec_ref_known(v_presentation_3994_, 1);
v___x_4001_ = lean_unbox(v_val_4000_);
lean_dec(v_val_4000_);
switch(v___x_4001_)
{
case 1:
{
lean_object* v_dateformat_4002_; lean_object* v_symbols_4003_; lean_object* v___x_4004_; 
v_dateformat_4002_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4002_);
lean_dec_ref(v_config_3793_);
v_symbols_4003_ = lean_ctor_get(v_dateformat_4002_, 1);
lean_inc_ref(v_symbols_4003_);
lean_dec_ref(v_dateformat_4002_);
v___x_4004_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_4003_, v_a_3795_);
return v___x_4004_;
}
case 2:
{
lean_object* v_dateformat_4005_; lean_object* v_symbols_4006_; lean_object* v___x_4007_; 
v_dateformat_4005_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4005_);
lean_dec_ref(v_config_3793_);
v_symbols_4006_ = lean_ctor_get(v_dateformat_4005_, 1);
lean_inc_ref(v_symbols_4006_);
lean_dec_ref(v_dateformat_4005_);
v___x_4007_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_4006_, v_a_3795_);
return v___x_4007_;
}
default: 
{
lean_object* v_dateformat_4008_; lean_object* v_symbols_4009_; lean_object* v___x_4010_; 
v_dateformat_4008_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4008_);
lean_dec_ref(v_config_3793_);
v_symbols_4009_ = lean_ctor_get(v_dateformat_4008_, 1);
lean_inc_ref(v_symbols_4009_);
lean_dec_ref(v_dateformat_4008_);
v___x_4010_ = l_Std_Time_parseMonthShort(v_symbols_4009_, v_a_3795_);
return v___x_4010_;
}
}
}
}
case 6:
{
lean_object* v_presentation_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_dec_ref(v_config_3793_);
v_presentation_4011_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4011_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4012_ = lean_unsigned_to_nat(1u);
v___x_4013_ = lean_unsigned_to_nat(31u);
v___x_4014_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4014_, 0, v_presentation_4011_);
v___x_4015_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4012_, v___x_4013_, v___x_4014_, v_a_3795_);
return v___x_4015_;
}
case 7:
{
lean_object* v_presentation_4016_; 
v_presentation_4016_ = lean_ctor_get(v_x_3794_, 0);
lean_inc_ref(v_presentation_4016_);
lean_dec_ref_known(v_x_3794_, 1);
if (lean_obj_tag(v_presentation_4016_) == 0)
{
lean_object* v_val_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
lean_dec_ref(v_config_3793_);
v_val_4017_ = lean_ctor_get(v_presentation_4016_, 0);
lean_inc(v_val_4017_);
lean_dec_ref_known(v_presentation_4016_, 1);
v___x_4018_ = lean_unsigned_to_nat(1u);
v___x_4019_ = lean_unsigned_to_nat(4u);
v___x_4020_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4020_, 0, v_val_4017_);
v___x_4021_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4018_, v___x_4019_, v___x_4020_, v_a_3795_);
return v___x_4021_;
}
else
{
lean_object* v_val_4022_; uint8_t v___x_4023_; 
v_val_4022_ = lean_ctor_get(v_presentation_4016_, 0);
lean_inc(v_val_4022_);
lean_dec_ref_known(v_presentation_4016_, 1);
v___x_4023_ = lean_unbox(v_val_4022_);
lean_dec(v_val_4022_);
switch(v___x_4023_)
{
case 0:
{
lean_object* v_dateformat_4024_; lean_object* v_symbols_4025_; lean_object* v___x_4026_; 
v_dateformat_4024_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4024_);
lean_dec_ref(v_config_3793_);
v_symbols_4025_ = lean_ctor_get(v_dateformat_4024_, 1);
lean_inc_ref(v_symbols_4025_);
lean_dec_ref(v_dateformat_4024_);
v___x_4026_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4025_, v_a_3795_);
return v___x_4026_;
}
case 1:
{
lean_object* v_dateformat_4027_; lean_object* v_symbols_4028_; lean_object* v___x_4029_; 
v_dateformat_4027_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4027_);
lean_dec_ref(v_config_3793_);
v_symbols_4028_ = lean_ctor_get(v_dateformat_4027_, 1);
lean_inc_ref(v_symbols_4028_);
lean_dec_ref(v_dateformat_4027_);
v___x_4029_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4028_, v_a_3795_);
return v___x_4029_;
}
default: 
{
lean_object* v_dateformat_4030_; lean_object* v_symbols_4031_; lean_object* v___x_4032_; 
v_dateformat_4030_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4030_);
lean_dec_ref(v_config_3793_);
v_symbols_4031_ = lean_ctor_get(v_dateformat_4030_, 1);
lean_inc_ref(v_symbols_4031_);
lean_dec_ref(v_dateformat_4030_);
v___x_4032_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_4031_, v_a_3795_);
return v___x_4032_;
}
}
}
}
case 8:
{
lean_object* v_presentation_4033_; 
v_presentation_4033_ = lean_ctor_get(v_x_3794_, 0);
lean_inc_ref(v_presentation_4033_);
lean_dec_ref_known(v_x_3794_, 1);
if (lean_obj_tag(v_presentation_4033_) == 0)
{
lean_object* v_val_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
lean_dec_ref(v_config_3793_);
v_val_4034_ = lean_ctor_get(v_presentation_4033_, 0);
lean_inc(v_val_4034_);
lean_dec_ref_known(v_presentation_4033_, 1);
v___x_4035_ = lean_unsigned_to_nat(1u);
v___x_4036_ = lean_unsigned_to_nat(4u);
v___x_4037_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4037_, 0, v_val_4034_);
v___x_4038_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4035_, v___x_4036_, v___x_4037_, v_a_3795_);
return v___x_4038_;
}
else
{
lean_object* v_val_4039_; uint8_t v___x_4040_; 
v_val_4039_ = lean_ctor_get(v_presentation_4033_, 0);
lean_inc(v_val_4039_);
lean_dec_ref_known(v_presentation_4033_, 1);
v___x_4040_ = lean_unbox(v_val_4039_);
lean_dec(v_val_4039_);
switch(v___x_4040_)
{
case 0:
{
lean_object* v_dateformat_4041_; lean_object* v_symbols_4042_; lean_object* v___x_4043_; 
v_dateformat_4041_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4041_);
lean_dec_ref(v_config_3793_);
v_symbols_4042_ = lean_ctor_get(v_dateformat_4041_, 1);
lean_inc_ref(v_symbols_4042_);
lean_dec_ref(v_dateformat_4041_);
v___x_4043_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4042_, v_a_3795_);
return v___x_4043_;
}
case 1:
{
lean_object* v_dateformat_4044_; lean_object* v_symbols_4045_; lean_object* v___x_4046_; 
v_dateformat_4044_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4044_);
lean_dec_ref(v_config_3793_);
v_symbols_4045_ = lean_ctor_get(v_dateformat_4044_, 1);
lean_inc_ref(v_symbols_4045_);
lean_dec_ref(v_dateformat_4044_);
v___x_4046_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4045_, v_a_3795_);
return v___x_4046_;
}
default: 
{
lean_object* v_dateformat_4047_; lean_object* v_symbols_4048_; lean_object* v___x_4049_; 
v_dateformat_4047_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4047_);
lean_dec_ref(v_config_3793_);
v_symbols_4048_ = lean_ctor_get(v_dateformat_4047_, 1);
lean_inc_ref(v_symbols_4048_);
lean_dec_ref(v_dateformat_4047_);
v___x_4049_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_4048_, v_a_3795_);
return v___x_4049_;
}
}
}
}
case 9:
{
lean_object* v_presentation_4050_; 
lean_dec_ref(v_config_3793_);
v_presentation_4050_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4050_);
lean_dec_ref_known(v_x_3794_, 1);
switch(lean_obj_tag(v_presentation_4050_))
{
case 0:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4051_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_4052_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4051_, v_a_3795_);
return v___x_4052_;
}
case 1:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = lean_unsigned_to_nat(2u);
v___x_4054_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_4053_, v_a_3795_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_pos_4055_; lean_object* v_res_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4066_; 
v_pos_4055_ = lean_ctor_get(v___x_4054_, 0);
v_res_4056_ = lean_ctor_get(v___x_4054_, 1);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4058_ = v___x_4054_;
v_isShared_4059_ = v_isSharedCheck_4066_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_res_4056_);
lean_inc(v_pos_4055_);
lean_dec(v___x_4054_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4066_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4064_; 
v___x_4060_ = lean_nat_to_int(v_res_4056_);
v___x_4061_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_4062_ = lean_int_add(v___x_4061_, v___x_4060_);
lean_dec(v___x_4060_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v___x_4062_);
v___x_4064_ = v___x_4058_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_pos_4055_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v___x_4062_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
else
{
lean_object* v_pos_4067_; lean_object* v_err_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
v_pos_4067_ = lean_ctor_get(v___x_4054_, 0);
v_err_4068_ = lean_ctor_get(v___x_4054_, 1);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4054_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_err_4068_);
lean_inc(v_pos_4067_);
lean_dec(v___x_4054_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_pos_4067_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_err_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
case 2:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_4077_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4076_, v_a_3795_);
return v___x_4077_;
}
default: 
{
lean_object* v_num_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v_num_4078_ = lean_ctor_get(v_presentation_4050_, 0);
lean_inc(v_num_4078_);
lean_dec_ref_known(v_presentation_4050_, 1);
v___x_4079_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_4079_, 0, v_num_4078_);
v___x_4080_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4079_, v_a_3795_);
return v___x_4080_;
}
}
}
case 10:
{
lean_object* v_presentation_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
lean_dec_ref(v_config_3793_);
v_presentation_4081_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4081_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4082_ = lean_unsigned_to_nat(1u);
v___x_4083_ = lean_unsigned_to_nat(53u);
v___x_4084_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4084_, 0, v_presentation_4081_);
v___x_4085_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4082_, v___x_4083_, v___x_4084_, v_a_3795_);
return v___x_4085_;
}
case 11:
{
lean_object* v_presentation_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
lean_dec_ref(v_config_3793_);
v_presentation_4086_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4086_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4087_ = lean_unsigned_to_nat(1u);
v___x_4088_ = lean_unsigned_to_nat(6u);
v___x_4089_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4089_, 0, v_presentation_4086_);
v___x_4090_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4087_, v___x_4088_, v___x_4089_, v_a_3795_);
return v___x_4090_;
}
case 12:
{
uint8_t v_presentation_4091_; 
v_presentation_4091_ = lean_ctor_get_uint8(v_x_3794_, 0);
lean_dec_ref_known(v_x_3794_, 0);
switch(v_presentation_4091_)
{
case 1:
{
lean_object* v_dateformat_4092_; lean_object* v_symbols_4093_; lean_object* v___x_4094_; 
v_dateformat_4092_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4092_);
lean_dec_ref(v_config_3793_);
v_symbols_4093_ = lean_ctor_get(v_dateformat_4092_, 1);
lean_inc_ref(v_symbols_4093_);
lean_dec_ref(v_dateformat_4092_);
v___x_4094_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4093_, v_a_3795_);
return v___x_4094_;
}
case 2:
{
lean_object* v_dateformat_4095_; lean_object* v_symbols_4096_; lean_object* v___x_4097_; 
v_dateformat_4095_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4095_);
lean_dec_ref(v_config_3793_);
v_symbols_4096_ = lean_ctor_get(v_dateformat_4095_, 1);
lean_inc_ref(v_symbols_4096_);
lean_dec_ref(v_dateformat_4095_);
v___x_4097_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4096_, v_a_3795_);
return v___x_4097_;
}
default: 
{
lean_object* v_dateformat_4098_; lean_object* v_symbols_4099_; lean_object* v___x_4100_; 
v_dateformat_4098_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4098_);
lean_dec_ref(v_config_3793_);
v_symbols_4099_ = lean_ctor_get(v_dateformat_4098_, 1);
lean_inc_ref(v_symbols_4099_);
lean_dec_ref(v_dateformat_4098_);
v___x_4100_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4099_, v_a_3795_);
return v___x_4100_;
}
}
}
case 13:
{
lean_object* v_presentation_4101_; 
v_presentation_4101_ = lean_ctor_get(v_x_3794_, 0);
lean_inc_ref(v_presentation_4101_);
lean_dec_ref_known(v_x_3794_, 1);
if (lean_obj_tag(v_presentation_4101_) == 0)
{
lean_object* v_val_4102_; lean_object* v___x_4103_; 
v_val_4102_ = lean_ctor_get(v_presentation_4101_, 0);
lean_inc(v_val_4102_);
lean_dec_ref_known(v_presentation_4101_, 1);
v___x_4103_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4102_, v_a_3795_);
lean_dec(v_val_4102_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_pos_4104_; lean_object* v_res_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4141_; 
v_pos_4104_ = lean_ctor_get(v___x_4103_, 0);
v_res_4105_ = lean_ctor_get(v___x_4103_, 1);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4107_ = v___x_4103_;
v_isShared_4108_ = v_isSharedCheck_4141_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_res_4105_);
lean_inc(v_pos_4104_);
lean_dec(v___x_4103_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4141_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
uint8_t v___y_4110_; lean_object* v___x_4137_; uint8_t v___x_4138_; 
v___x_4137_ = lean_unsigned_to_nat(1u);
v___x_4138_ = lean_nat_dec_le(v___x_4137_, v_res_4105_);
if (v___x_4138_ == 0)
{
v___y_4110_ = v___x_4138_;
goto v___jp_4109_;
}
else
{
lean_object* v___x_4139_; uint8_t v___x_4140_; 
v___x_4139_ = lean_unsigned_to_nat(7u);
v___x_4140_ = lean_nat_dec_le(v_res_4105_, v___x_4139_);
v___y_4110_ = v___x_4140_;
goto v___jp_4109_;
}
v___jp_4109_:
{
if (v___y_4110_ == 0)
{
lean_object* v___x_4111_; lean_object* v___x_4113_; 
lean_dec(v_res_4105_);
lean_dec_ref(v_config_3793_);
v___x_4111_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4108_ == 0)
{
lean_ctor_set_tag(v___x_4107_, 1);
lean_ctor_set(v___x_4107_, 1, v___x_4111_);
v___x_4113_ = v___x_4107_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_pos_4104_);
lean_ctor_set(v_reuseFailAlloc_4114_, 1, v___x_4111_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
else
{
lean_object* v_dateformat_4115_; uint8_t v_firstDayOfWeek_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v_range_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4135_; 
v_dateformat_4115_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4115_);
lean_dec_ref(v_config_3793_);
v_firstDayOfWeek_4116_ = lean_ctor_get_uint8(v_dateformat_4115_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4115_);
v___x_4117_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4116_);
v___x_4118_ = lean_nat_to_int(v_res_4105_);
v___x_4119_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4120_ = lean_int_sub(v___x_4118_, v___x_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_int_add(v___x_4120_, v___x_4117_);
lean_dec(v___x_4117_);
lean_dec(v___x_4120_);
v___x_4122_ = lean_int_sub(v___x_4121_, v___x_4119_);
lean_dec(v___x_4121_);
v___x_4123_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4124_ = lean_int_emod(v___x_4122_, v___x_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_int_add(v___x_4124_, v___x_4119_);
lean_dec(v___x_4124_);
v_range_4126_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4127_ = lean_int_sub(v___x_4125_, v___x_4119_);
lean_dec(v___x_4125_);
v___x_4128_ = lean_int_emod(v___x_4127_, v_range_4126_);
lean_dec(v___x_4127_);
v___x_4129_ = lean_int_add(v___x_4128_, v_range_4126_);
lean_dec(v___x_4128_);
v___x_4130_ = lean_int_emod(v___x_4129_, v_range_4126_);
lean_dec(v___x_4129_);
v___x_4131_ = lean_int_add(v___x_4130_, v___x_4119_);
lean_dec(v___x_4130_);
v___x_4132_ = l_Std_Time_Weekday_ofOrdinal(v___x_4131_);
lean_dec(v___x_4131_);
v___x_4133_ = lean_box(v___x_4132_);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 1, v___x_4133_);
v___x_4135_ = v___x_4107_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_pos_4104_);
lean_ctor_set(v_reuseFailAlloc_4136_, 1, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
else
{
lean_object* v_pos_4142_; lean_object* v_err_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_dec_ref(v_config_3793_);
v_pos_4142_ = lean_ctor_get(v___x_4103_, 0);
v_err_4143_ = lean_ctor_get(v___x_4103_, 1);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4103_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_err_4143_);
lean_inc(v_pos_4142_);
lean_dec(v___x_4103_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_pos_4142_);
lean_ctor_set(v_reuseFailAlloc_4149_, 1, v_err_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
else
{
lean_object* v_val_4151_; uint8_t v___x_4152_; 
v_val_4151_ = lean_ctor_get(v_presentation_4101_, 0);
lean_inc(v_val_4151_);
lean_dec_ref_known(v_presentation_4101_, 1);
v___x_4152_ = lean_unbox(v_val_4151_);
lean_dec(v_val_4151_);
switch(v___x_4152_)
{
case 0:
{
lean_object* v_dateformat_4153_; lean_object* v_symbols_4154_; lean_object* v___x_4155_; 
v_dateformat_4153_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4153_);
lean_dec_ref(v_config_3793_);
v_symbols_4154_ = lean_ctor_get(v_dateformat_4153_, 1);
lean_inc_ref(v_symbols_4154_);
lean_dec_ref(v_dateformat_4153_);
v___x_4155_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4154_, v_a_3795_);
return v___x_4155_;
}
case 1:
{
lean_object* v_dateformat_4156_; lean_object* v_symbols_4157_; lean_object* v___x_4158_; 
v_dateformat_4156_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4156_);
lean_dec_ref(v_config_3793_);
v_symbols_4157_ = lean_ctor_get(v_dateformat_4156_, 1);
lean_inc_ref(v_symbols_4157_);
lean_dec_ref(v_dateformat_4156_);
v___x_4158_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4157_, v_a_3795_);
return v___x_4158_;
}
case 2:
{
lean_object* v_dateformat_4159_; lean_object* v_symbols_4160_; lean_object* v___x_4161_; 
v_dateformat_4159_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4159_);
lean_dec_ref(v_config_3793_);
v_symbols_4160_ = lean_ctor_get(v_dateformat_4159_, 1);
lean_inc_ref(v_symbols_4160_);
lean_dec_ref(v_dateformat_4159_);
v___x_4161_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4160_, v_a_3795_);
return v___x_4161_;
}
default: 
{
lean_object* v_dateformat_4162_; lean_object* v_symbols_4163_; lean_object* v___x_4164_; 
v_dateformat_4162_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4162_);
lean_dec_ref(v_config_3793_);
v_symbols_4163_ = lean_ctor_get(v_dateformat_4162_, 1);
lean_inc_ref(v_symbols_4163_);
lean_dec_ref(v_dateformat_4162_);
v___x_4164_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4163_, v_a_3795_);
return v___x_4164_;
}
}
}
}
case 14:
{
lean_object* v_presentation_4165_; 
v_presentation_4165_ = lean_ctor_get(v_x_3794_, 0);
lean_inc_ref(v_presentation_4165_);
lean_dec_ref_known(v_x_3794_, 1);
if (lean_obj_tag(v_presentation_4165_) == 0)
{
lean_object* v_val_4166_; lean_object* v___x_4167_; 
v_val_4166_ = lean_ctor_get(v_presentation_4165_, 0);
lean_inc(v_val_4166_);
lean_dec_ref_known(v_presentation_4165_, 1);
v___x_4167_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4166_, v_a_3795_);
lean_dec(v_val_4166_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_pos_4168_; lean_object* v_res_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4205_; 
v_pos_4168_ = lean_ctor_get(v___x_4167_, 0);
v_res_4169_ = lean_ctor_get(v___x_4167_, 1);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4171_ = v___x_4167_;
v_isShared_4172_ = v_isSharedCheck_4205_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_res_4169_);
lean_inc(v_pos_4168_);
lean_dec(v___x_4167_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4205_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
uint8_t v___y_4174_; lean_object* v___x_4201_; uint8_t v___x_4202_; 
v___x_4201_ = lean_unsigned_to_nat(1u);
v___x_4202_ = lean_nat_dec_le(v___x_4201_, v_res_4169_);
if (v___x_4202_ == 0)
{
v___y_4174_ = v___x_4202_;
goto v___jp_4173_;
}
else
{
lean_object* v___x_4203_; uint8_t v___x_4204_; 
v___x_4203_ = lean_unsigned_to_nat(7u);
v___x_4204_ = lean_nat_dec_le(v_res_4169_, v___x_4203_);
v___y_4174_ = v___x_4204_;
goto v___jp_4173_;
}
v___jp_4173_:
{
if (v___y_4174_ == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4177_; 
lean_dec(v_res_4169_);
lean_dec_ref(v_config_3793_);
v___x_4175_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4172_ == 0)
{
lean_ctor_set_tag(v___x_4171_, 1);
lean_ctor_set(v___x_4171_, 1, v___x_4175_);
v___x_4177_ = v___x_4171_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_pos_4168_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v___x_4175_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
else
{
lean_object* v_dateformat_4179_; uint8_t v_firstDayOfWeek_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v_range_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; uint8_t v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4199_; 
v_dateformat_4179_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4179_);
lean_dec_ref(v_config_3793_);
v_firstDayOfWeek_4180_ = lean_ctor_get_uint8(v_dateformat_4179_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4179_);
v___x_4181_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4180_);
v___x_4182_ = lean_nat_to_int(v_res_4169_);
v___x_4183_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4184_ = lean_int_sub(v___x_4182_, v___x_4183_);
lean_dec(v___x_4182_);
v___x_4185_ = lean_int_add(v___x_4184_, v___x_4181_);
lean_dec(v___x_4181_);
lean_dec(v___x_4184_);
v___x_4186_ = lean_int_sub(v___x_4185_, v___x_4183_);
lean_dec(v___x_4185_);
v___x_4187_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4188_ = lean_int_emod(v___x_4186_, v___x_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = lean_int_add(v___x_4188_, v___x_4183_);
lean_dec(v___x_4188_);
v_range_4190_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4191_ = lean_int_sub(v___x_4189_, v___x_4183_);
lean_dec(v___x_4189_);
v___x_4192_ = lean_int_emod(v___x_4191_, v_range_4190_);
lean_dec(v___x_4191_);
v___x_4193_ = lean_int_add(v___x_4192_, v_range_4190_);
lean_dec(v___x_4192_);
v___x_4194_ = lean_int_emod(v___x_4193_, v_range_4190_);
lean_dec(v___x_4193_);
v___x_4195_ = lean_int_add(v___x_4194_, v___x_4183_);
lean_dec(v___x_4194_);
v___x_4196_ = l_Std_Time_Weekday_ofOrdinal(v___x_4195_);
lean_dec(v___x_4195_);
v___x_4197_ = lean_box(v___x_4196_);
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 1, v___x_4197_);
v___x_4199_ = v___x_4171_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_pos_4168_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v___x_4197_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
else
{
lean_object* v_pos_4206_; lean_object* v_err_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec_ref(v_config_3793_);
v_pos_4206_ = lean_ctor_get(v___x_4167_, 0);
v_err_4207_ = lean_ctor_get(v___x_4167_, 1);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4167_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_err_4207_);
lean_inc(v_pos_4206_);
lean_dec(v___x_4167_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_pos_4206_);
lean_ctor_set(v_reuseFailAlloc_4213_, 1, v_err_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
else
{
lean_object* v_val_4215_; uint8_t v___x_4216_; 
v_val_4215_ = lean_ctor_get(v_presentation_4165_, 0);
lean_inc(v_val_4215_);
lean_dec_ref_known(v_presentation_4165_, 1);
v___x_4216_ = lean_unbox(v_val_4215_);
lean_dec(v_val_4215_);
switch(v___x_4216_)
{
case 0:
{
lean_object* v_dateformat_4217_; lean_object* v_symbols_4218_; lean_object* v___x_4219_; 
v_dateformat_4217_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4217_);
lean_dec_ref(v_config_3793_);
v_symbols_4218_ = lean_ctor_get(v_dateformat_4217_, 1);
lean_inc_ref(v_symbols_4218_);
lean_dec_ref(v_dateformat_4217_);
v___x_4219_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4218_, v_a_3795_);
return v___x_4219_;
}
case 1:
{
lean_object* v_dateformat_4220_; lean_object* v_symbols_4221_; lean_object* v___x_4222_; 
v_dateformat_4220_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4220_);
lean_dec_ref(v_config_3793_);
v_symbols_4221_ = lean_ctor_get(v_dateformat_4220_, 1);
lean_inc_ref(v_symbols_4221_);
lean_dec_ref(v_dateformat_4220_);
v___x_4222_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4221_, v_a_3795_);
return v___x_4222_;
}
case 2:
{
lean_object* v_dateformat_4223_; lean_object* v_symbols_4224_; lean_object* v___x_4225_; 
v_dateformat_4223_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4223_);
lean_dec_ref(v_config_3793_);
v_symbols_4224_ = lean_ctor_get(v_dateformat_4223_, 1);
lean_inc_ref(v_symbols_4224_);
lean_dec_ref(v_dateformat_4223_);
v___x_4225_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4224_, v_a_3795_);
return v___x_4225_;
}
default: 
{
lean_object* v_dateformat_4226_; lean_object* v_symbols_4227_; lean_object* v___x_4228_; 
v_dateformat_4226_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4226_);
lean_dec_ref(v_config_3793_);
v_symbols_4227_ = lean_ctor_get(v_dateformat_4226_, 1);
lean_inc_ref(v_symbols_4227_);
lean_dec_ref(v_dateformat_4226_);
v___x_4228_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4227_, v_a_3795_);
return v___x_4228_;
}
}
}
}
case 15:
{
lean_object* v_presentation_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec_ref(v_config_3793_);
v_presentation_4229_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4229_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4230_ = lean_unsigned_to_nat(1u);
v___x_4231_ = lean_unsigned_to_nat(5u);
v___x_4232_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4232_, 0, v_presentation_4229_);
v___x_4233_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4230_, v___x_4231_, v___x_4232_, v_a_3795_);
return v___x_4233_;
}
case 16:
{
uint8_t v_presentation_4234_; 
v_presentation_4234_ = lean_ctor_get_uint8(v_x_3794_, 0);
lean_dec_ref_known(v_x_3794_, 0);
switch(v_presentation_4234_)
{
case 1:
{
lean_object* v_dateformat_4235_; lean_object* v_symbols_4236_; lean_object* v___x_4237_; 
v_dateformat_4235_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4235_);
lean_dec_ref(v_config_3793_);
v_symbols_4236_ = lean_ctor_get(v_dateformat_4235_, 1);
lean_inc_ref(v_symbols_4236_);
lean_dec_ref(v_dateformat_4235_);
v___x_4237_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(v_symbols_4236_, v_a_3795_);
return v___x_4237_;
}
case 2:
{
lean_object* v_dateformat_4238_; lean_object* v_symbols_4239_; lean_object* v___x_4240_; 
v_dateformat_4238_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4238_);
lean_dec_ref(v_config_3793_);
v_symbols_4239_ = lean_ctor_get(v_dateformat_4238_, 1);
lean_inc_ref(v_symbols_4239_);
lean_dec_ref(v_dateformat_4238_);
v___x_4240_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(v_symbols_4239_, v_a_3795_);
return v___x_4240_;
}
default: 
{
lean_object* v_dateformat_4241_; lean_object* v_symbols_4242_; lean_object* v___x_4243_; 
v_dateformat_4241_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4241_);
lean_dec_ref(v_config_3793_);
v_symbols_4242_ = lean_ctor_get(v_dateformat_4241_, 1);
lean_inc_ref(v_symbols_4242_);
lean_dec_ref(v_dateformat_4241_);
v___x_4243_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(v_symbols_4242_, v_a_3795_);
return v___x_4243_;
}
}
}
case 17:
{
uint8_t v_presentation_4244_; 
v_presentation_4244_ = lean_ctor_get_uint8(v_x_3794_, 0);
lean_dec_ref_known(v_x_3794_, 0);
switch(v_presentation_4244_)
{
case 1:
{
lean_object* v_dateformat_4245_; lean_object* v_symbols_4246_; lean_object* v_dayPeriodLong_4247_; lean_object* v___x_4248_; 
v_dateformat_4245_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4245_);
lean_dec_ref(v_config_3793_);
v_symbols_4246_ = lean_ctor_get(v_dateformat_4245_, 1);
lean_inc_ref(v_symbols_4246_);
lean_dec_ref(v_dateformat_4245_);
v_dayPeriodLong_4247_ = lean_ctor_get(v_symbols_4246_, 20);
lean_inc_ref(v_dayPeriodLong_4247_);
lean_dec_ref(v_symbols_4246_);
v___x_4248_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodLong_4247_, v_a_3795_);
return v___x_4248_;
}
case 2:
{
lean_object* v_dateformat_4249_; lean_object* v_symbols_4250_; lean_object* v_dayPeriodNarrow_4251_; lean_object* v___x_4252_; 
v_dateformat_4249_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4249_);
lean_dec_ref(v_config_3793_);
v_symbols_4250_ = lean_ctor_get(v_dateformat_4249_, 1);
lean_inc_ref(v_symbols_4250_);
lean_dec_ref(v_dateformat_4249_);
v_dayPeriodNarrow_4251_ = lean_ctor_get(v_symbols_4250_, 21);
lean_inc_ref(v_dayPeriodNarrow_4251_);
lean_dec_ref(v_symbols_4250_);
v___x_4252_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodNarrow_4251_, v_a_3795_);
return v___x_4252_;
}
default: 
{
lean_object* v_dateformat_4253_; lean_object* v_symbols_4254_; lean_object* v_dayPeriodShort_4255_; lean_object* v___x_4256_; 
v_dateformat_4253_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4253_);
lean_dec_ref(v_config_3793_);
v_symbols_4254_ = lean_ctor_get(v_dateformat_4253_, 1);
lean_inc_ref(v_symbols_4254_);
lean_dec_ref(v_dateformat_4253_);
v_dayPeriodShort_4255_ = lean_ctor_get(v_symbols_4254_, 19);
lean_inc_ref(v_dayPeriodShort_4255_);
lean_dec_ref(v_symbols_4254_);
v___x_4256_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodShort_4255_, v_a_3795_);
return v___x_4256_;
}
}
}
case 18:
{
uint8_t v_presentation_4257_; 
v_presentation_4257_ = lean_ctor_get_uint8(v_x_3794_, 0);
lean_dec_ref_known(v_x_3794_, 0);
switch(v_presentation_4257_)
{
case 1:
{
lean_object* v_dateformat_4258_; lean_object* v_symbols_4259_; lean_object* v_extendedDayPeriodLong_4260_; lean_object* v___x_4261_; 
v_dateformat_4258_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4258_);
lean_dec_ref(v_config_3793_);
v_symbols_4259_ = lean_ctor_get(v_dateformat_4258_, 1);
lean_inc_ref(v_symbols_4259_);
lean_dec_ref(v_dateformat_4258_);
v_extendedDayPeriodLong_4260_ = lean_ctor_get(v_symbols_4259_, 23);
lean_inc_ref(v_extendedDayPeriodLong_4260_);
lean_dec_ref(v_symbols_4259_);
v___x_4261_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodLong_4260_, v_a_3795_);
lean_dec_ref(v_extendedDayPeriodLong_4260_);
return v___x_4261_;
}
case 2:
{
lean_object* v_dateformat_4262_; lean_object* v_symbols_4263_; lean_object* v_extendedDayPeriodNarrow_4264_; lean_object* v___x_4265_; 
v_dateformat_4262_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4262_);
lean_dec_ref(v_config_3793_);
v_symbols_4263_ = lean_ctor_get(v_dateformat_4262_, 1);
lean_inc_ref(v_symbols_4263_);
lean_dec_ref(v_dateformat_4262_);
v_extendedDayPeriodNarrow_4264_ = lean_ctor_get(v_symbols_4263_, 24);
lean_inc_ref(v_extendedDayPeriodNarrow_4264_);
lean_dec_ref(v_symbols_4263_);
v___x_4265_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodNarrow_4264_, v_a_3795_);
lean_dec_ref(v_extendedDayPeriodNarrow_4264_);
return v___x_4265_;
}
default: 
{
lean_object* v_dateformat_4266_; lean_object* v_symbols_4267_; lean_object* v_extendedDayPeriodShort_4268_; lean_object* v___x_4269_; 
v_dateformat_4266_ = lean_ctor_get(v_config_3793_, 0);
lean_inc_ref(v_dateformat_4266_);
lean_dec_ref(v_config_3793_);
v_symbols_4267_ = lean_ctor_get(v_dateformat_4266_, 1);
lean_inc_ref(v_symbols_4267_);
lean_dec_ref(v_dateformat_4266_);
v_extendedDayPeriodShort_4268_ = lean_ctor_get(v_symbols_4267_, 22);
lean_inc_ref(v_extendedDayPeriodShort_4268_);
lean_dec_ref(v_symbols_4267_);
v___x_4269_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodShort_4268_, v_a_3795_);
lean_dec_ref(v_extendedDayPeriodShort_4268_);
return v___x_4269_;
}
}
}
case 19:
{
lean_object* v_presentation_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
lean_dec_ref(v_config_3793_);
v_presentation_4270_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4270_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4271_ = lean_unsigned_to_nat(1u);
v___x_4272_ = lean_unsigned_to_nat(12u);
v___x_4273_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4273_, 0, v_presentation_4270_);
v___x_4274_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4271_, v___x_4272_, v___x_4273_, v_a_3795_);
return v___x_4274_;
}
case 20:
{
lean_object* v_presentation_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
lean_dec_ref(v_config_3793_);
v_presentation_4275_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4275_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4276_ = lean_unsigned_to_nat(0u);
v___x_4277_ = lean_unsigned_to_nat(11u);
v___x_4278_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4278_, 0, v_presentation_4275_);
v___x_4279_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4276_, v___x_4277_, v___x_4278_, v_a_3795_);
return v___x_4279_;
}
case 21:
{
lean_object* v_presentation_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
lean_dec_ref(v_config_3793_);
v_presentation_4280_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4280_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4281_ = lean_unsigned_to_nat(1u);
v___x_4282_ = lean_unsigned_to_nat(24u);
v___x_4283_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4283_, 0, v_presentation_4280_);
v___x_4284_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4281_, v___x_4282_, v___x_4283_, v_a_3795_);
return v___x_4284_;
}
case 22:
{
lean_object* v_presentation_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
lean_dec_ref(v_config_3793_);
v_presentation_4285_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4285_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4286_ = lean_unsigned_to_nat(0u);
v___x_4287_ = lean_unsigned_to_nat(23u);
v___x_4288_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4288_, 0, v_presentation_4285_);
v___x_4289_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4286_, v___x_4287_, v___x_4288_, v_a_3795_);
return v___x_4289_;
}
case 23:
{
lean_object* v_presentation_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
lean_dec_ref(v_config_3793_);
v_presentation_4290_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4290_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4291_ = lean_unsigned_to_nat(0u);
v___x_4292_ = lean_unsigned_to_nat(59u);
v___x_4293_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4293_, 0, v_presentation_4290_);
v___x_4294_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4291_, v___x_4292_, v___x_4293_, v_a_3795_);
return v___x_4294_;
}
case 24:
{
uint8_t v_allowLeapSeconds_4295_; 
v_allowLeapSeconds_4295_ = lean_ctor_get_uint8(v_config_3793_, sizeof(void*)*1);
lean_dec_ref(v_config_3793_);
if (v_allowLeapSeconds_4295_ == 0)
{
lean_object* v_presentation_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v_presentation_4296_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4296_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = lean_unsigned_to_nat(59u);
v___x_4299_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4299_, 0, v_presentation_4296_);
v___x_4300_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4297_, v___x_4298_, v___x_4299_, v_a_3795_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_pos_4301_; lean_object* v_res_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
v_pos_4301_ = lean_ctor_get(v___x_4300_, 0);
v_res_4302_ = lean_ctor_get(v___x_4300_, 1);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4300_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_res_4302_);
lean_inc(v_pos_4301_);
lean_dec(v___x_4300_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_pos_4301_);
lean_ctor_set(v_reuseFailAlloc_4308_, 1, v_res_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
else
{
return v___x_4300_;
}
}
else
{
lean_object* v_presentation_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v_presentation_4310_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4310_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4311_ = lean_unsigned_to_nat(0u);
v___x_4312_ = lean_unsigned_to_nat(60u);
v___x_4313_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4313_, 0, v_presentation_4310_);
v___x_4314_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4311_, v___x_4312_, v___x_4313_, v_a_3795_);
return v___x_4314_;
}
}
case 25:
{
lean_object* v_presentation_4315_; 
lean_dec_ref(v_config_3793_);
v_presentation_4315_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4315_);
lean_dec_ref_known(v_x_3794_, 1);
if (lean_obj_tag(v_presentation_4315_) == 0)
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4316_ = lean_unsigned_to_nat(0u);
v___x_4317_ = lean_unsigned_to_nat(999999999u);
v___x_4318_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7));
v___x_4319_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4316_, v___x_4317_, v___x_4318_, v_a_3795_);
return v___x_4319_;
}
else
{
lean_object* v_digits_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v_digits_4320_ = lean_ctor_get(v_presentation_4315_, 0);
lean_inc(v_digits_4320_);
lean_dec_ref_known(v_presentation_4315_, 1);
v___x_4321_ = lean_unsigned_to_nat(0u);
v___x_4322_ = lean_unsigned_to_nat(999999999u);
v___x_4323_ = lean_unsigned_to_nat(9u);
v___x_4324_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed), 3, 2);
lean_closure_set(v___x_4324_, 0, v_digits_4320_);
lean_closure_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4321_, v___x_4322_, v___x_4324_, v_a_3795_);
return v___x_4325_;
}
}
case 26:
{
lean_object* v_presentation_4326_; lean_object* v___x_4327_; 
lean_dec_ref(v_config_3793_);
v_presentation_4326_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4326_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4327_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4326_, v_a_3795_);
lean_dec(v_presentation_4326_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_pos_4328_; lean_object* v_res_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4337_; 
v_pos_4328_ = lean_ctor_get(v___x_4327_, 0);
v_res_4329_ = lean_ctor_get(v___x_4327_, 1);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4331_ = v___x_4327_;
v_isShared_4332_ = v_isSharedCheck_4337_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_res_4329_);
lean_inc(v_pos_4328_);
lean_dec(v___x_4327_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4337_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4333_; lean_object* v___x_4335_; 
v___x_4333_ = lean_nat_to_int(v_res_4329_);
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 1, v___x_4333_);
v___x_4335_ = v___x_4331_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_pos_4328_);
lean_ctor_set(v_reuseFailAlloc_4336_, 1, v___x_4333_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
}
else
{
lean_object* v_pos_4338_; lean_object* v_err_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
v_pos_4338_ = lean_ctor_get(v___x_4327_, 0);
v_err_4339_ = lean_ctor_get(v___x_4327_, 1);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4327_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_err_4339_);
lean_inc(v_pos_4338_);
lean_dec(v___x_4327_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_pos_4338_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v_err_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
case 27:
{
lean_object* v_presentation_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
lean_dec_ref(v_config_3793_);
v_presentation_4347_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4347_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4348_ = lean_unsigned_to_nat(0u);
v___x_4349_ = lean_unsigned_to_nat(999999999u);
v___x_4350_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4350_, 0, v_presentation_4347_);
v___x_4351_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4348_, v___x_4349_, v___x_4350_, v_a_3795_);
return v___x_4351_;
}
case 28:
{
lean_object* v_presentation_4352_; lean_object* v___x_4353_; 
lean_dec_ref(v_config_3793_);
v_presentation_4352_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_presentation_4352_);
lean_dec_ref_known(v_x_3794_, 1);
v___x_4353_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4352_, v_a_3795_);
lean_dec(v_presentation_4352_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_pos_4354_; lean_object* v_res_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4363_; 
v_pos_4354_ = lean_ctor_get(v___x_4353_, 0);
v_res_4355_ = lean_ctor_get(v___x_4353_, 1);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4357_ = v___x_4353_;
v_isShared_4358_ = v_isSharedCheck_4363_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_res_4355_);
lean_inc(v_pos_4354_);
lean_dec(v___x_4353_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4363_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v___x_4361_; 
v___x_4359_ = lean_nat_to_int(v_res_4355_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 1, v___x_4359_);
v___x_4361_ = v___x_4357_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_pos_4354_);
lean_ctor_set(v_reuseFailAlloc_4362_, 1, v___x_4359_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
else
{
lean_object* v_pos_4364_; lean_object* v_err_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
v_pos_4364_ = lean_ctor_get(v___x_4353_, 0);
v_err_4365_ = lean_ctor_get(v___x_4353_, 1);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4353_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_err_4365_);
lean_inc(v_pos_4364_);
lean_dec(v___x_4353_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_pos_4364_);
lean_ctor_set(v_reuseFailAlloc_4371_, 1, v_err_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
case 29:
{
uint8_t v_presentation_4373_; 
lean_dec_ref(v_config_3793_);
v_presentation_4373_ = lean_ctor_get_uint8(v_x_3794_, 0);
lean_dec_ref_known(v_x_3794_, 0);
if (v_presentation_4373_ == 0)
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
v___x_4375_ = l_Std_Internal_Parsec_String_pstring(v___x_4374_, v_a_3795_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_pos_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
v_pos_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; 
v_unused_4384_ = lean_ctor_get(v___x_4375_, 1);
lean_dec(v_unused_4384_);
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_pos_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 1, v___x_4374_);
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_pos_4376_);
lean_ctor_set(v_reuseFailAlloc_4382_, 1, v___x_4374_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
else
{
return v___x_4375_;
}
}
else
{
lean_object* v___x_4385_; 
v___x_4385_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3795_);
return v___x_4385_;
}
}
case 32:
{
uint8_t v_presentation_4386_; 
lean_dec_ref(v_config_3793_);
v_presentation_4386_ = lean_ctor_get_uint8(v_x_3794_, 0);
lean_dec_ref_known(v_x_3794_, 0);
if (v_presentation_4386_ == 0)
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4388_ = l_Std_Internal_Parsec_String_pstring(v___x_4387_, v_a_3795_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_pos_4389_; uint8_t v___x_4390_; uint8_t v___x_4391_; uint8_t v___x_4392_; lean_object* v___x_4393_; 
v_pos_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_pos_4389_);
lean_dec_ref_known(v___x_4388_, 2);
v___x_4390_ = 2;
v___x_4391_ = 1;
v___x_4392_ = 1;
v___x_4393_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4390_, v___x_4391_, v___x_4392_, v_pos_4389_);
return v___x_4393_;
}
else
{
lean_object* v_pos_4394_; lean_object* v_err_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
v_pos_4394_ = lean_ctor_get(v___x_4388_, 0);
v_err_4395_ = lean_ctor_get(v___x_4388_, 1);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4388_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_err_4395_);
lean_inc(v_pos_4394_);
lean_dec(v___x_4388_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_pos_4394_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_err_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4404_ = l_Std_Internal_Parsec_String_pstring(v___x_4403_, v_a_3795_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_pos_4405_; uint8_t v___x_4406_; uint8_t v___x_4407_; uint8_t v___x_4408_; lean_object* v___x_4409_; 
v_pos_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_pos_4405_);
lean_dec_ref_known(v___x_4404_, 2);
v___x_4406_ = 0;
v___x_4407_ = 2;
v___x_4408_ = 1;
v___x_4409_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4406_, v___x_4407_, v___x_4408_, v_pos_4405_);
return v___x_4409_;
}
else
{
lean_object* v_pos_4410_; lean_object* v_err_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
v_pos_4410_ = lean_ctor_get(v___x_4404_, 0);
v_err_4411_ = lean_ctor_get(v___x_4404_, 1);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4404_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_err_4411_);
lean_inc(v_pos_4410_);
lean_dec(v___x_4404_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_pos_4410_);
lean_ctor_set(v_reuseFailAlloc_4417_, 1, v_err_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
case 33:
{
uint8_t v_presentation_4419_; 
lean_dec_ref(v_config_3793_);
v_presentation_4419_ = lean_ctor_get_uint8(v_x_3794_, 0);
lean_dec_ref_known(v_x_3794_, 0);
switch(v_presentation_4419_)
{
case 0:
{
uint8_t v___x_4420_; uint8_t v___x_4421_; uint8_t v___x_4422_; lean_object* v___x_4423_; 
v___x_4420_ = 2;
v___x_4421_ = 1;
v___x_4422_ = 0;
lean_inc_ref(v_a_3795_);
v___x_4423_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4420_, v___x_4421_, v___x_4422_, v_a_3795_);
v___y_3797_ = v___x_4423_;
goto v___jp_3796_;
}
case 1:
{
uint8_t v___x_4424_; uint8_t v___x_4425_; uint8_t v___x_4426_; lean_object* v___x_4427_; 
v___x_4424_ = 0;
v___x_4425_ = 1;
v___x_4426_ = 0;
lean_inc_ref(v_a_3795_);
v___x_4427_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4424_, v___x_4425_, v___x_4426_, v_a_3795_);
v___y_3797_ = v___x_4427_;
goto v___jp_3796_;
}
case 2:
{
uint8_t v___x_4428_; uint8_t v___x_4429_; uint8_t v___x_4430_; lean_object* v___x_4431_; 
v___x_4428_ = 0;
v___x_4429_ = 1;
v___x_4430_ = 1;
lean_inc_ref(v_a_3795_);
v___x_4431_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4428_, v___x_4429_, v___x_4430_, v_a_3795_);
v___y_3797_ = v___x_4431_;
goto v___jp_3796_;
}
case 3:
{
uint8_t v___x_4432_; uint8_t v___x_4433_; uint8_t v___x_4434_; lean_object* v___x_4435_; 
v___x_4432_ = 0;
v___x_4433_ = 2;
v___x_4434_ = 0;
lean_inc_ref(v_a_3795_);
v___x_4435_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4432_, v___x_4433_, v___x_4434_, v_a_3795_);
v___y_3797_ = v___x_4435_;
goto v___jp_3796_;
}
default: 
{
uint8_t v___x_4436_; uint8_t v___x_4437_; uint8_t v___x_4438_; lean_object* v___x_4439_; 
v___x_4436_ = 0;
v___x_4437_ = 2;
v___x_4438_ = 1;
lean_inc_ref(v_a_3795_);
v___x_4439_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4436_, v___x_4437_, v___x_4438_, v_a_3795_);
v___y_3797_ = v___x_4439_;
goto v___jp_3796_;
}
}
}
case 34:
{
uint8_t v_presentation_4440_; 
lean_dec_ref(v_config_3793_);
v_presentation_4440_ = lean_ctor_get_uint8(v_x_3794_, 0);
lean_dec_ref_known(v_x_3794_, 0);
switch(v_presentation_4440_)
{
case 0:
{
uint8_t v___x_4441_; uint8_t v___x_4442_; uint8_t v___x_4443_; lean_object* v___x_4444_; 
v___x_4441_ = 2;
v___x_4442_ = 1;
v___x_4443_ = 0;
v___x_4444_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4441_, v___x_4442_, v___x_4443_, v_a_3795_);
return v___x_4444_;
}
case 1:
{
uint8_t v___x_4445_; uint8_t v___x_4446_; uint8_t v___x_4447_; lean_object* v___x_4448_; 
v___x_4445_ = 0;
v___x_4446_ = 1;
v___x_4447_ = 0;
v___x_4448_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4445_, v___x_4446_, v___x_4447_, v_a_3795_);
return v___x_4448_;
}
case 2:
{
uint8_t v___x_4449_; uint8_t v___x_4450_; uint8_t v___x_4451_; lean_object* v___x_4452_; 
v___x_4449_ = 0;
v___x_4450_ = 2;
v___x_4451_ = 1;
v___x_4452_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4449_, v___x_4450_, v___x_4451_, v_a_3795_);
return v___x_4452_;
}
case 3:
{
uint8_t v___x_4453_; uint8_t v___x_4454_; uint8_t v___x_4455_; lean_object* v___x_4456_; 
v___x_4453_ = 0;
v___x_4454_ = 2;
v___x_4455_ = 0;
v___x_4456_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4453_, v___x_4454_, v___x_4455_, v_a_3795_);
return v___x_4456_;
}
default: 
{
uint8_t v___x_4457_; uint8_t v___x_4458_; lean_object* v___x_4459_; 
v___x_4457_ = 0;
v___x_4458_ = 1;
v___x_4459_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4457_, v___x_4457_, v___x_4458_, v_a_3795_);
return v___x_4459_;
}
}
}
case 35:
{
uint8_t v_presentation_4460_; 
lean_dec_ref(v_config_3793_);
v_presentation_4460_ = lean_ctor_get_uint8(v_x_3794_, 0);
lean_dec_ref_known(v_x_3794_, 0);
switch(v_presentation_4460_)
{
case 0:
{
uint8_t v___x_4461_; uint8_t v___x_4462_; uint8_t v___x_4463_; lean_object* v___x_4464_; 
v___x_4461_ = 0;
v___x_4462_ = 1;
v___x_4463_ = 0;
v___x_4464_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4461_, v___x_4462_, v___x_4463_, v_a_3795_);
return v___x_4464_;
}
case 1:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4466_ = l_Std_Internal_Parsec_String_pstring(v___x_4465_, v_a_3795_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_pos_4467_; uint8_t v___x_4468_; uint8_t v___x_4469_; uint8_t v___x_4470_; lean_object* v___x_4471_; 
v_pos_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc_n(v_pos_4467_, 2);
lean_dec_ref_known(v___x_4466_, 2);
v___x_4468_ = 0;
v___x_4469_ = 1;
v___x_4470_ = 1;
v___x_4471_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4468_, v___x_4469_, v___x_4470_, v_pos_4467_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_dec(v_pos_4467_);
return v___x_4471_;
}
else
{
lean_object* v_pos_4472_; lean_object* v_snd_4473_; lean_object* v_snd_4474_; uint8_t v___x_4475_; 
v_pos_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_pos_4472_);
v_snd_4473_ = lean_ctor_get(v_pos_4467_, 1);
lean_inc(v_snd_4473_);
lean_dec(v_pos_4467_);
v_snd_4474_ = lean_ctor_get(v_pos_4472_, 1);
v___x_4475_ = lean_nat_dec_eq(v_snd_4473_, v_snd_4474_);
lean_dec(v_snd_4473_);
if (v___x_4475_ == 0)
{
lean_dec(v_pos_4472_);
return v___x_4471_;
}
else
{
lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4483_; 
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4483_ == 0)
{
lean_object* v_unused_4484_; lean_object* v_unused_4485_; 
v_unused_4484_ = lean_ctor_get(v___x_4471_, 1);
lean_dec(v_unused_4484_);
v_unused_4485_ = lean_ctor_get(v___x_4471_, 0);
lean_dec(v_unused_4485_);
v___x_4477_ = v___x_4471_;
v_isShared_4478_ = v_isSharedCheck_4483_;
goto v_resetjp_4476_;
}
else
{
lean_dec(v___x_4471_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4483_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4479_; lean_object* v___x_4481_; 
v___x_4479_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4478_ == 0)
{
lean_ctor_set_tag(v___x_4477_, 0);
lean_ctor_set(v___x_4477_, 1, v___x_4479_);
v___x_4481_ = v___x_4477_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_pos_4472_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v___x_4479_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
}
else
{
lean_object* v_pos_4486_; lean_object* v_err_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
v_pos_4486_ = lean_ctor_get(v___x_4466_, 0);
v_err_4487_ = lean_ctor_get(v___x_4466_, 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4466_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_err_4487_);
lean_inc(v_pos_4486_);
lean_dec(v___x_4466_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_pos_4486_);
lean_ctor_set(v_reuseFailAlloc_4493_, 1, v_err_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
default: 
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
lean_inc_ref(v_a_3795_);
v___x_4496_ = l_Std_Internal_Parsec_String_pstring(v___x_4495_, v_a_3795_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_pos_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4505_; 
lean_dec_ref(v_a_3795_);
v_pos_4497_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4505_ == 0)
{
lean_object* v_unused_4506_; 
v_unused_4506_ = lean_ctor_get(v___x_4496_, 1);
lean_dec(v_unused_4506_);
v___x_4499_ = v___x_4496_;
v_isShared_4500_ = v_isSharedCheck_4505_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_pos_4497_);
lean_dec(v___x_4496_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4505_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4501_; lean_object* v___x_4503_; 
v___x_4501_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 1, v___x_4501_);
v___x_4503_ = v___x_4499_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_pos_4497_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
else
{
lean_object* v_pos_4507_; lean_object* v_err_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4521_; 
v_pos_4507_ = lean_ctor_get(v___x_4496_, 0);
v_err_4508_ = lean_ctor_get(v___x_4496_, 1);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4510_ = v___x_4496_;
v_isShared_4511_ = v_isSharedCheck_4521_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_err_4508_);
lean_inc(v_pos_4507_);
lean_dec(v___x_4496_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4521_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v_snd_4512_; lean_object* v_snd_4513_; uint8_t v___x_4514_; 
v_snd_4512_ = lean_ctor_get(v_a_3795_, 1);
lean_inc(v_snd_4512_);
lean_dec_ref(v_a_3795_);
v_snd_4513_ = lean_ctor_get(v_pos_4507_, 1);
v___x_4514_ = lean_nat_dec_eq(v_snd_4512_, v_snd_4513_);
lean_dec(v_snd_4512_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4516_; 
if (v_isShared_4511_ == 0)
{
v___x_4516_ = v___x_4510_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_pos_4507_);
lean_ctor_set(v_reuseFailAlloc_4517_, 1, v_err_4508_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
else
{
uint8_t v___x_4518_; uint8_t v___x_4519_; lean_object* v___x_4520_; 
lean_del_object(v___x_4510_);
lean_dec(v_err_4508_);
v___x_4518_ = 0;
v___x_4519_ = 2;
v___x_4520_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4518_, v___x_4519_, v___x_4514_, v_pos_4507_);
return v___x_4520_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_4522_; 
lean_dec_ref(v_x_3794_);
lean_dec_ref(v_config_3793_);
v___x_4522_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3795_);
return v___x_4522_;
}
}
v___jp_3796_:
{
if (lean_obj_tag(v___y_3797_) == 0)
{
lean_dec_ref(v_a_3795_);
return v___y_3797_;
}
else
{
lean_object* v_pos_3798_; lean_object* v_snd_3799_; lean_object* v_snd_3800_; uint8_t v___x_3801_; 
v_pos_3798_ = lean_ctor_get(v___y_3797_, 0);
v_snd_3799_ = lean_ctor_get(v_a_3795_, 1);
lean_inc(v_snd_3799_);
lean_dec_ref(v_a_3795_);
v_snd_3800_ = lean_ctor_get(v_pos_3798_, 1);
v___x_3801_ = lean_nat_dec_eq(v_snd_3799_, v_snd_3800_);
lean_dec(v_snd_3799_);
if (v___x_3801_ == 0)
{
return v___y_3797_;
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
lean_inc(v_pos_3798_);
lean_dec_ref_known(v___y_3797_, 2);
v___x_3802_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
v___x_3803_ = l_Std_Internal_Parsec_String_pstring(v___x_3802_, v_pos_3798_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_pos_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3812_; 
v_pos_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3812_ == 0)
{
lean_object* v_unused_3813_; 
v_unused_3813_ = lean_ctor_get(v___x_3803_, 1);
lean_dec(v_unused_3813_);
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3812_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_pos_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3812_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3808_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
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
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_pos_3804_);
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
lean_object* v_pos_3814_; lean_object* v_err_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
v_pos_3814_ = lean_ctor_get(v___x_3803_, 0);
v_err_3815_ = lean_ctor_get(v___x_3803_, 1);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3803_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_err_3815_);
lean_inc(v_pos_3814_);
lean_dec(v___x_3803_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_pos_3814_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_err_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(lean_object* v_dateformat_4523_, lean_object* v_date_4524_, lean_object* v_part_4525_){
_start:
{
if (lean_obj_tag(v_part_4525_) == 0)
{
lean_object* v_val_4526_; 
lean_dec_ref(v_date_4524_);
v_val_4526_ = lean_ctor_get(v_part_4525_, 0);
lean_inc_ref(v_val_4526_);
lean_dec_ref_known(v_part_4525_, 1);
return v_val_4526_;
}
else
{
lean_object* v_modifier_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v_modifier_4527_ = lean_ctor_get(v_part_4525_, 0);
lean_inc_ref(v_modifier_4527_);
lean_dec_ref_known(v_part_4525_, 1);
v___x_4528_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_4527_, v_dateformat_4523_, v_date_4524_);
v___x_4529_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_4523_, v_modifier_4527_, v___x_4528_);
return v___x_4529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate___boxed(lean_object* v_dateformat_4530_, lean_object* v_date_4531_, lean_object* v_part_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_4530_, v_date_4531_, v_part_4532_);
lean_dec_ref(v_dateformat_4530_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter___redArg(lean_object* v_x_4534_, lean_object* v_h__1_4535_, lean_object* v_h__2_4536_, lean_object* v_h__3_4537_){
_start:
{
if (lean_obj_tag(v_x_4534_) == 0)
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
lean_dec(v_h__2_4536_);
lean_dec(v_h__1_4535_);
v___x_4538_ = lean_box(0);
v___x_4539_ = lean_apply_1(v_h__3_4537_, v___x_4538_);
return v___x_4539_;
}
else
{
lean_object* v_head_4540_; 
lean_dec(v_h__3_4537_);
v_head_4540_ = lean_ctor_get(v_x_4534_, 0);
lean_inc(v_head_4540_);
if (lean_obj_tag(v_head_4540_) == 0)
{
lean_object* v_tail_4541_; lean_object* v_val_4542_; lean_object* v___x_4543_; 
lean_dec(v_h__1_4535_);
v_tail_4541_ = lean_ctor_get(v_x_4534_, 1);
lean_inc(v_tail_4541_);
lean_dec_ref_known(v_x_4534_, 2);
v_val_4542_ = lean_ctor_get(v_head_4540_, 0);
lean_inc_ref(v_val_4542_);
lean_dec_ref_known(v_head_4540_, 1);
v___x_4543_ = lean_apply_2(v_h__2_4536_, v_val_4542_, v_tail_4541_);
return v___x_4543_;
}
else
{
lean_object* v_tail_4544_; lean_object* v_modifier_4545_; lean_object* v___x_4546_; 
lean_dec(v_h__2_4536_);
v_tail_4544_ = lean_ctor_get(v_x_4534_, 1);
lean_inc(v_tail_4544_);
lean_dec_ref_known(v_x_4534_, 2);
v_modifier_4545_ = lean_ctor_get(v_head_4540_, 0);
lean_inc_ref(v_modifier_4545_);
lean_dec_ref_known(v_head_4540_, 1);
v___x_4546_ = lean_apply_2(v_h__1_4535_, v_modifier_4545_, v_tail_4544_);
return v___x_4546_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter(lean_object* v_motive_4547_, lean_object* v_x_4548_, lean_object* v_h__1_4549_, lean_object* v_h__2_4550_, lean_object* v_h__3_4551_){
_start:
{
if (lean_obj_tag(v_x_4548_) == 0)
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
lean_dec(v_h__2_4550_);
lean_dec(v_h__1_4549_);
v___x_4552_ = lean_box(0);
v___x_4553_ = lean_apply_1(v_h__3_4551_, v___x_4552_);
return v___x_4553_;
}
else
{
lean_object* v_head_4554_; 
lean_dec(v_h__3_4551_);
v_head_4554_ = lean_ctor_get(v_x_4548_, 0);
lean_inc(v_head_4554_);
if (lean_obj_tag(v_head_4554_) == 0)
{
lean_object* v_tail_4555_; lean_object* v_val_4556_; lean_object* v___x_4557_; 
lean_dec(v_h__1_4549_);
v_tail_4555_ = lean_ctor_get(v_x_4548_, 1);
lean_inc(v_tail_4555_);
lean_dec_ref_known(v_x_4548_, 2);
v_val_4556_ = lean_ctor_get(v_head_4554_, 0);
lean_inc_ref(v_val_4556_);
lean_dec_ref_known(v_head_4554_, 1);
v___x_4557_ = lean_apply_2(v_h__2_4550_, v_val_4556_, v_tail_4555_);
return v___x_4557_;
}
else
{
lean_object* v_tail_4558_; lean_object* v_modifier_4559_; lean_object* v___x_4560_; 
lean_dec(v_h__2_4550_);
v_tail_4558_ = lean_ctor_get(v_x_4548_, 1);
lean_inc(v_tail_4558_);
lean_dec_ref_known(v_x_4548_, 2);
v_modifier_4559_ = lean_ctor_get(v_head_4554_, 0);
lean_inc_ref(v_modifier_4559_);
lean_dec_ref_known(v_head_4554_, 1);
v___x_4560_ = lean_apply_2(v_h__1_4549_, v_modifier_4559_, v_tail_4558_);
return v___x_4560_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object* v_date_4561_, lean_object* v_modifier_4562_, lean_object* v_data_4563_){
_start:
{
switch(lean_obj_tag(v_modifier_4562_))
{
case 0:
{
lean_object* v_y_4564_; lean_object* v_u_4565_; lean_object* v_Y_4566_; lean_object* v_D_4567_; lean_object* v_M_4568_; lean_object* v_L_4569_; lean_object* v_d_4570_; lean_object* v_Q_4571_; lean_object* v_q_4572_; lean_object* v_w_4573_; lean_object* v_W_4574_; lean_object* v_E_4575_; lean_object* v_e_4576_; lean_object* v_c_4577_; lean_object* v_F_4578_; lean_object* v_a_4579_; lean_object* v_b_4580_; lean_object* v_B_4581_; lean_object* v_h_4582_; lean_object* v_K_4583_; lean_object* v_k_4584_; lean_object* v_H_4585_; lean_object* v_m_4586_; lean_object* v_s_4587_; lean_object* v_S_4588_; lean_object* v_A_4589_; lean_object* v_n_4590_; lean_object* v_N_4591_; lean_object* v_V_4592_; lean_object* v_z_4593_; lean_object* v_zabbrev_4594_; lean_object* v_v_4595_; lean_object* v_O_4596_; lean_object* v_X_4597_; lean_object* v_x_4598_; lean_object* v_Z_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4607_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_y_4564_ = lean_ctor_get(v_date_4561_, 1);
v_u_4565_ = lean_ctor_get(v_date_4561_, 2);
v_Y_4566_ = lean_ctor_get(v_date_4561_, 3);
v_D_4567_ = lean_ctor_get(v_date_4561_, 4);
v_M_4568_ = lean_ctor_get(v_date_4561_, 5);
v_L_4569_ = lean_ctor_get(v_date_4561_, 6);
v_d_4570_ = lean_ctor_get(v_date_4561_, 7);
v_Q_4571_ = lean_ctor_get(v_date_4561_, 8);
v_q_4572_ = lean_ctor_get(v_date_4561_, 9);
v_w_4573_ = lean_ctor_get(v_date_4561_, 10);
v_W_4574_ = lean_ctor_get(v_date_4561_, 11);
v_E_4575_ = lean_ctor_get(v_date_4561_, 12);
v_e_4576_ = lean_ctor_get(v_date_4561_, 13);
v_c_4577_ = lean_ctor_get(v_date_4561_, 14);
v_F_4578_ = lean_ctor_get(v_date_4561_, 15);
v_a_4579_ = lean_ctor_get(v_date_4561_, 16);
v_b_4580_ = lean_ctor_get(v_date_4561_, 17);
v_B_4581_ = lean_ctor_get(v_date_4561_, 18);
v_h_4582_ = lean_ctor_get(v_date_4561_, 19);
v_K_4583_ = lean_ctor_get(v_date_4561_, 20);
v_k_4584_ = lean_ctor_get(v_date_4561_, 21);
v_H_4585_ = lean_ctor_get(v_date_4561_, 22);
v_m_4586_ = lean_ctor_get(v_date_4561_, 23);
v_s_4587_ = lean_ctor_get(v_date_4561_, 24);
v_S_4588_ = lean_ctor_get(v_date_4561_, 25);
v_A_4589_ = lean_ctor_get(v_date_4561_, 26);
v_n_4590_ = lean_ctor_get(v_date_4561_, 27);
v_N_4591_ = lean_ctor_get(v_date_4561_, 28);
v_V_4592_ = lean_ctor_get(v_date_4561_, 29);
v_z_4593_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_4594_ = lean_ctor_get(v_date_4561_, 31);
v_v_4595_ = lean_ctor_get(v_date_4561_, 32);
v_O_4596_ = lean_ctor_get(v_date_4561_, 33);
v_X_4597_ = lean_ctor_get(v_date_4561_, 34);
v_x_4598_ = lean_ctor_get(v_date_4561_, 35);
v_Z_4599_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_4607_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_4607_ == 0)
{
lean_object* v_unused_4608_; 
v_unused_4608_ = lean_ctor_get(v_date_4561_, 0);
lean_dec(v_unused_4608_);
v___x_4601_ = v_date_4561_;
v_isShared_4602_ = v_isSharedCheck_4607_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_Z_4599_);
lean_inc(v_x_4598_);
lean_inc(v_X_4597_);
lean_inc(v_O_4596_);
lean_inc(v_v_4595_);
lean_inc(v_zabbrev_4594_);
lean_inc(v_z_4593_);
lean_inc(v_V_4592_);
lean_inc(v_N_4591_);
lean_inc(v_n_4590_);
lean_inc(v_A_4589_);
lean_inc(v_S_4588_);
lean_inc(v_s_4587_);
lean_inc(v_m_4586_);
lean_inc(v_H_4585_);
lean_inc(v_k_4584_);
lean_inc(v_K_4583_);
lean_inc(v_h_4582_);
lean_inc(v_B_4581_);
lean_inc(v_b_4580_);
lean_inc(v_a_4579_);
lean_inc(v_F_4578_);
lean_inc(v_c_4577_);
lean_inc(v_e_4576_);
lean_inc(v_E_4575_);
lean_inc(v_W_4574_);
lean_inc(v_w_4573_);
lean_inc(v_q_4572_);
lean_inc(v_Q_4571_);
lean_inc(v_d_4570_);
lean_inc(v_L_4569_);
lean_inc(v_M_4568_);
lean_inc(v_D_4567_);
lean_inc(v_Y_4566_);
lean_inc(v_u_4565_);
lean_inc(v_y_4564_);
lean_dec(v_date_4561_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4607_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4603_, 0, v_data_4563_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4603_);
v___x_4605_ = v___x_4601_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
lean_ctor_set(v_reuseFailAlloc_4606_, 1, v_y_4564_);
lean_ctor_set(v_reuseFailAlloc_4606_, 2, v_u_4565_);
lean_ctor_set(v_reuseFailAlloc_4606_, 3, v_Y_4566_);
lean_ctor_set(v_reuseFailAlloc_4606_, 4, v_D_4567_);
lean_ctor_set(v_reuseFailAlloc_4606_, 5, v_M_4568_);
lean_ctor_set(v_reuseFailAlloc_4606_, 6, v_L_4569_);
lean_ctor_set(v_reuseFailAlloc_4606_, 7, v_d_4570_);
lean_ctor_set(v_reuseFailAlloc_4606_, 8, v_Q_4571_);
lean_ctor_set(v_reuseFailAlloc_4606_, 9, v_q_4572_);
lean_ctor_set(v_reuseFailAlloc_4606_, 10, v_w_4573_);
lean_ctor_set(v_reuseFailAlloc_4606_, 11, v_W_4574_);
lean_ctor_set(v_reuseFailAlloc_4606_, 12, v_E_4575_);
lean_ctor_set(v_reuseFailAlloc_4606_, 13, v_e_4576_);
lean_ctor_set(v_reuseFailAlloc_4606_, 14, v_c_4577_);
lean_ctor_set(v_reuseFailAlloc_4606_, 15, v_F_4578_);
lean_ctor_set(v_reuseFailAlloc_4606_, 16, v_a_4579_);
lean_ctor_set(v_reuseFailAlloc_4606_, 17, v_b_4580_);
lean_ctor_set(v_reuseFailAlloc_4606_, 18, v_B_4581_);
lean_ctor_set(v_reuseFailAlloc_4606_, 19, v_h_4582_);
lean_ctor_set(v_reuseFailAlloc_4606_, 20, v_K_4583_);
lean_ctor_set(v_reuseFailAlloc_4606_, 21, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4606_, 22, v_H_4585_);
lean_ctor_set(v_reuseFailAlloc_4606_, 23, v_m_4586_);
lean_ctor_set(v_reuseFailAlloc_4606_, 24, v_s_4587_);
lean_ctor_set(v_reuseFailAlloc_4606_, 25, v_S_4588_);
lean_ctor_set(v_reuseFailAlloc_4606_, 26, v_A_4589_);
lean_ctor_set(v_reuseFailAlloc_4606_, 27, v_n_4590_);
lean_ctor_set(v_reuseFailAlloc_4606_, 28, v_N_4591_);
lean_ctor_set(v_reuseFailAlloc_4606_, 29, v_V_4592_);
lean_ctor_set(v_reuseFailAlloc_4606_, 30, v_z_4593_);
lean_ctor_set(v_reuseFailAlloc_4606_, 31, v_zabbrev_4594_);
lean_ctor_set(v_reuseFailAlloc_4606_, 32, v_v_4595_);
lean_ctor_set(v_reuseFailAlloc_4606_, 33, v_O_4596_);
lean_ctor_set(v_reuseFailAlloc_4606_, 34, v_X_4597_);
lean_ctor_set(v_reuseFailAlloc_4606_, 35, v_x_4598_);
lean_ctor_set(v_reuseFailAlloc_4606_, 36, v_Z_4599_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
case 1:
{
lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4659_; 
v_isSharedCheck_4659_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_4659_ == 0)
{
lean_object* v_unused_4660_; 
v_unused_4660_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_4660_);
v___x_4610_ = v_modifier_4562_;
v_isShared_4611_ = v_isSharedCheck_4659_;
goto v_resetjp_4609_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4659_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v_G_4612_; lean_object* v_y_4613_; lean_object* v_Y_4614_; lean_object* v_D_4615_; lean_object* v_M_4616_; lean_object* v_L_4617_; lean_object* v_d_4618_; lean_object* v_Q_4619_; lean_object* v_q_4620_; lean_object* v_w_4621_; lean_object* v_W_4622_; lean_object* v_E_4623_; lean_object* v_e_4624_; lean_object* v_c_4625_; lean_object* v_F_4626_; lean_object* v_a_4627_; lean_object* v_b_4628_; lean_object* v_B_4629_; lean_object* v_h_4630_; lean_object* v_K_4631_; lean_object* v_k_4632_; lean_object* v_H_4633_; lean_object* v_m_4634_; lean_object* v_s_4635_; lean_object* v_S_4636_; lean_object* v_A_4637_; lean_object* v_n_4638_; lean_object* v_N_4639_; lean_object* v_V_4640_; lean_object* v_z_4641_; lean_object* v_zabbrev_4642_; lean_object* v_v_4643_; lean_object* v_O_4644_; lean_object* v_X_4645_; lean_object* v_x_4646_; lean_object* v_Z_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4657_; 
v_G_4612_ = lean_ctor_get(v_date_4561_, 0);
v_y_4613_ = lean_ctor_get(v_date_4561_, 1);
v_Y_4614_ = lean_ctor_get(v_date_4561_, 3);
v_D_4615_ = lean_ctor_get(v_date_4561_, 4);
v_M_4616_ = lean_ctor_get(v_date_4561_, 5);
v_L_4617_ = lean_ctor_get(v_date_4561_, 6);
v_d_4618_ = lean_ctor_get(v_date_4561_, 7);
v_Q_4619_ = lean_ctor_get(v_date_4561_, 8);
v_q_4620_ = lean_ctor_get(v_date_4561_, 9);
v_w_4621_ = lean_ctor_get(v_date_4561_, 10);
v_W_4622_ = lean_ctor_get(v_date_4561_, 11);
v_E_4623_ = lean_ctor_get(v_date_4561_, 12);
v_e_4624_ = lean_ctor_get(v_date_4561_, 13);
v_c_4625_ = lean_ctor_get(v_date_4561_, 14);
v_F_4626_ = lean_ctor_get(v_date_4561_, 15);
v_a_4627_ = lean_ctor_get(v_date_4561_, 16);
v_b_4628_ = lean_ctor_get(v_date_4561_, 17);
v_B_4629_ = lean_ctor_get(v_date_4561_, 18);
v_h_4630_ = lean_ctor_get(v_date_4561_, 19);
v_K_4631_ = lean_ctor_get(v_date_4561_, 20);
v_k_4632_ = lean_ctor_get(v_date_4561_, 21);
v_H_4633_ = lean_ctor_get(v_date_4561_, 22);
v_m_4634_ = lean_ctor_get(v_date_4561_, 23);
v_s_4635_ = lean_ctor_get(v_date_4561_, 24);
v_S_4636_ = lean_ctor_get(v_date_4561_, 25);
v_A_4637_ = lean_ctor_get(v_date_4561_, 26);
v_n_4638_ = lean_ctor_get(v_date_4561_, 27);
v_N_4639_ = lean_ctor_get(v_date_4561_, 28);
v_V_4640_ = lean_ctor_get(v_date_4561_, 29);
v_z_4641_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_4642_ = lean_ctor_get(v_date_4561_, 31);
v_v_4643_ = lean_ctor_get(v_date_4561_, 32);
v_O_4644_ = lean_ctor_get(v_date_4561_, 33);
v_X_4645_ = lean_ctor_get(v_date_4561_, 34);
v_x_4646_ = lean_ctor_get(v_date_4561_, 35);
v_Z_4647_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_4657_ == 0)
{
lean_object* v_unused_4658_; 
v_unused_4658_ = lean_ctor_get(v_date_4561_, 2);
lean_dec(v_unused_4658_);
v___x_4649_ = v_date_4561_;
v_isShared_4650_ = v_isSharedCheck_4657_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_Z_4647_);
lean_inc(v_x_4646_);
lean_inc(v_X_4645_);
lean_inc(v_O_4644_);
lean_inc(v_v_4643_);
lean_inc(v_zabbrev_4642_);
lean_inc(v_z_4641_);
lean_inc(v_V_4640_);
lean_inc(v_N_4639_);
lean_inc(v_n_4638_);
lean_inc(v_A_4637_);
lean_inc(v_S_4636_);
lean_inc(v_s_4635_);
lean_inc(v_m_4634_);
lean_inc(v_H_4633_);
lean_inc(v_k_4632_);
lean_inc(v_K_4631_);
lean_inc(v_h_4630_);
lean_inc(v_B_4629_);
lean_inc(v_b_4628_);
lean_inc(v_a_4627_);
lean_inc(v_F_4626_);
lean_inc(v_c_4625_);
lean_inc(v_e_4624_);
lean_inc(v_E_4623_);
lean_inc(v_W_4622_);
lean_inc(v_w_4621_);
lean_inc(v_q_4620_);
lean_inc(v_Q_4619_);
lean_inc(v_d_4618_);
lean_inc(v_L_4617_);
lean_inc(v_M_4616_);
lean_inc(v_D_4615_);
lean_inc(v_Y_4614_);
lean_inc(v_y_4613_);
lean_inc(v_G_4612_);
lean_dec(v_date_4561_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4657_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4611_ == 0)
{
lean_ctor_set(v___x_4610_, 0, v_data_4563_);
v___x_4652_ = v___x_4610_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_data_4563_);
v___x_4652_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
lean_object* v___x_4654_; 
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 2, v___x_4652_);
v___x_4654_ = v___x_4649_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_G_4612_);
lean_ctor_set(v_reuseFailAlloc_4655_, 1, v_y_4613_);
lean_ctor_set(v_reuseFailAlloc_4655_, 2, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4655_, 3, v_Y_4614_);
lean_ctor_set(v_reuseFailAlloc_4655_, 4, v_D_4615_);
lean_ctor_set(v_reuseFailAlloc_4655_, 5, v_M_4616_);
lean_ctor_set(v_reuseFailAlloc_4655_, 6, v_L_4617_);
lean_ctor_set(v_reuseFailAlloc_4655_, 7, v_d_4618_);
lean_ctor_set(v_reuseFailAlloc_4655_, 8, v_Q_4619_);
lean_ctor_set(v_reuseFailAlloc_4655_, 9, v_q_4620_);
lean_ctor_set(v_reuseFailAlloc_4655_, 10, v_w_4621_);
lean_ctor_set(v_reuseFailAlloc_4655_, 11, v_W_4622_);
lean_ctor_set(v_reuseFailAlloc_4655_, 12, v_E_4623_);
lean_ctor_set(v_reuseFailAlloc_4655_, 13, v_e_4624_);
lean_ctor_set(v_reuseFailAlloc_4655_, 14, v_c_4625_);
lean_ctor_set(v_reuseFailAlloc_4655_, 15, v_F_4626_);
lean_ctor_set(v_reuseFailAlloc_4655_, 16, v_a_4627_);
lean_ctor_set(v_reuseFailAlloc_4655_, 17, v_b_4628_);
lean_ctor_set(v_reuseFailAlloc_4655_, 18, v_B_4629_);
lean_ctor_set(v_reuseFailAlloc_4655_, 19, v_h_4630_);
lean_ctor_set(v_reuseFailAlloc_4655_, 20, v_K_4631_);
lean_ctor_set(v_reuseFailAlloc_4655_, 21, v_k_4632_);
lean_ctor_set(v_reuseFailAlloc_4655_, 22, v_H_4633_);
lean_ctor_set(v_reuseFailAlloc_4655_, 23, v_m_4634_);
lean_ctor_set(v_reuseFailAlloc_4655_, 24, v_s_4635_);
lean_ctor_set(v_reuseFailAlloc_4655_, 25, v_S_4636_);
lean_ctor_set(v_reuseFailAlloc_4655_, 26, v_A_4637_);
lean_ctor_set(v_reuseFailAlloc_4655_, 27, v_n_4638_);
lean_ctor_set(v_reuseFailAlloc_4655_, 28, v_N_4639_);
lean_ctor_set(v_reuseFailAlloc_4655_, 29, v_V_4640_);
lean_ctor_set(v_reuseFailAlloc_4655_, 30, v_z_4641_);
lean_ctor_set(v_reuseFailAlloc_4655_, 31, v_zabbrev_4642_);
lean_ctor_set(v_reuseFailAlloc_4655_, 32, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4655_, 33, v_O_4644_);
lean_ctor_set(v_reuseFailAlloc_4655_, 34, v_X_4645_);
lean_ctor_set(v_reuseFailAlloc_4655_, 35, v_x_4646_);
lean_ctor_set(v_reuseFailAlloc_4655_, 36, v_Z_4647_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
}
}
}
case 2:
{
lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4711_; 
v_isSharedCheck_4711_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_4711_ == 0)
{
lean_object* v_unused_4712_; 
v_unused_4712_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_4712_);
v___x_4662_ = v_modifier_4562_;
v_isShared_4663_ = v_isSharedCheck_4711_;
goto v_resetjp_4661_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4711_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v_G_4664_; lean_object* v_u_4665_; lean_object* v_Y_4666_; lean_object* v_D_4667_; lean_object* v_M_4668_; lean_object* v_L_4669_; lean_object* v_d_4670_; lean_object* v_Q_4671_; lean_object* v_q_4672_; lean_object* v_w_4673_; lean_object* v_W_4674_; lean_object* v_E_4675_; lean_object* v_e_4676_; lean_object* v_c_4677_; lean_object* v_F_4678_; lean_object* v_a_4679_; lean_object* v_b_4680_; lean_object* v_B_4681_; lean_object* v_h_4682_; lean_object* v_K_4683_; lean_object* v_k_4684_; lean_object* v_H_4685_; lean_object* v_m_4686_; lean_object* v_s_4687_; lean_object* v_S_4688_; lean_object* v_A_4689_; lean_object* v_n_4690_; lean_object* v_N_4691_; lean_object* v_V_4692_; lean_object* v_z_4693_; lean_object* v_zabbrev_4694_; lean_object* v_v_4695_; lean_object* v_O_4696_; lean_object* v_X_4697_; lean_object* v_x_4698_; lean_object* v_Z_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4709_; 
v_G_4664_ = lean_ctor_get(v_date_4561_, 0);
v_u_4665_ = lean_ctor_get(v_date_4561_, 2);
v_Y_4666_ = lean_ctor_get(v_date_4561_, 3);
v_D_4667_ = lean_ctor_get(v_date_4561_, 4);
v_M_4668_ = lean_ctor_get(v_date_4561_, 5);
v_L_4669_ = lean_ctor_get(v_date_4561_, 6);
v_d_4670_ = lean_ctor_get(v_date_4561_, 7);
v_Q_4671_ = lean_ctor_get(v_date_4561_, 8);
v_q_4672_ = lean_ctor_get(v_date_4561_, 9);
v_w_4673_ = lean_ctor_get(v_date_4561_, 10);
v_W_4674_ = lean_ctor_get(v_date_4561_, 11);
v_E_4675_ = lean_ctor_get(v_date_4561_, 12);
v_e_4676_ = lean_ctor_get(v_date_4561_, 13);
v_c_4677_ = lean_ctor_get(v_date_4561_, 14);
v_F_4678_ = lean_ctor_get(v_date_4561_, 15);
v_a_4679_ = lean_ctor_get(v_date_4561_, 16);
v_b_4680_ = lean_ctor_get(v_date_4561_, 17);
v_B_4681_ = lean_ctor_get(v_date_4561_, 18);
v_h_4682_ = lean_ctor_get(v_date_4561_, 19);
v_K_4683_ = lean_ctor_get(v_date_4561_, 20);
v_k_4684_ = lean_ctor_get(v_date_4561_, 21);
v_H_4685_ = lean_ctor_get(v_date_4561_, 22);
v_m_4686_ = lean_ctor_get(v_date_4561_, 23);
v_s_4687_ = lean_ctor_get(v_date_4561_, 24);
v_S_4688_ = lean_ctor_get(v_date_4561_, 25);
v_A_4689_ = lean_ctor_get(v_date_4561_, 26);
v_n_4690_ = lean_ctor_get(v_date_4561_, 27);
v_N_4691_ = lean_ctor_get(v_date_4561_, 28);
v_V_4692_ = lean_ctor_get(v_date_4561_, 29);
v_z_4693_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_4694_ = lean_ctor_get(v_date_4561_, 31);
v_v_4695_ = lean_ctor_get(v_date_4561_, 32);
v_O_4696_ = lean_ctor_get(v_date_4561_, 33);
v_X_4697_ = lean_ctor_get(v_date_4561_, 34);
v_x_4698_ = lean_ctor_get(v_date_4561_, 35);
v_Z_4699_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_4709_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_4709_ == 0)
{
lean_object* v_unused_4710_; 
v_unused_4710_ = lean_ctor_get(v_date_4561_, 1);
lean_dec(v_unused_4710_);
v___x_4701_ = v_date_4561_;
v_isShared_4702_ = v_isSharedCheck_4709_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_Z_4699_);
lean_inc(v_x_4698_);
lean_inc(v_X_4697_);
lean_inc(v_O_4696_);
lean_inc(v_v_4695_);
lean_inc(v_zabbrev_4694_);
lean_inc(v_z_4693_);
lean_inc(v_V_4692_);
lean_inc(v_N_4691_);
lean_inc(v_n_4690_);
lean_inc(v_A_4689_);
lean_inc(v_S_4688_);
lean_inc(v_s_4687_);
lean_inc(v_m_4686_);
lean_inc(v_H_4685_);
lean_inc(v_k_4684_);
lean_inc(v_K_4683_);
lean_inc(v_h_4682_);
lean_inc(v_B_4681_);
lean_inc(v_b_4680_);
lean_inc(v_a_4679_);
lean_inc(v_F_4678_);
lean_inc(v_c_4677_);
lean_inc(v_e_4676_);
lean_inc(v_E_4675_);
lean_inc(v_W_4674_);
lean_inc(v_w_4673_);
lean_inc(v_q_4672_);
lean_inc(v_Q_4671_);
lean_inc(v_d_4670_);
lean_inc(v_L_4669_);
lean_inc(v_M_4668_);
lean_inc(v_D_4667_);
lean_inc(v_Y_4666_);
lean_inc(v_u_4665_);
lean_inc(v_G_4664_);
lean_dec(v_date_4561_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4709_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
if (v_isShared_4663_ == 0)
{
lean_ctor_set_tag(v___x_4662_, 1);
lean_ctor_set(v___x_4662_, 0, v_data_4563_);
v___x_4704_ = v___x_4662_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_data_4563_);
v___x_4704_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
lean_object* v___x_4706_; 
if (v_isShared_4702_ == 0)
{
lean_ctor_set(v___x_4701_, 1, v___x_4704_);
v___x_4706_ = v___x_4701_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_G_4664_);
lean_ctor_set(v_reuseFailAlloc_4707_, 1, v___x_4704_);
lean_ctor_set(v_reuseFailAlloc_4707_, 2, v_u_4665_);
lean_ctor_set(v_reuseFailAlloc_4707_, 3, v_Y_4666_);
lean_ctor_set(v_reuseFailAlloc_4707_, 4, v_D_4667_);
lean_ctor_set(v_reuseFailAlloc_4707_, 5, v_M_4668_);
lean_ctor_set(v_reuseFailAlloc_4707_, 6, v_L_4669_);
lean_ctor_set(v_reuseFailAlloc_4707_, 7, v_d_4670_);
lean_ctor_set(v_reuseFailAlloc_4707_, 8, v_Q_4671_);
lean_ctor_set(v_reuseFailAlloc_4707_, 9, v_q_4672_);
lean_ctor_set(v_reuseFailAlloc_4707_, 10, v_w_4673_);
lean_ctor_set(v_reuseFailAlloc_4707_, 11, v_W_4674_);
lean_ctor_set(v_reuseFailAlloc_4707_, 12, v_E_4675_);
lean_ctor_set(v_reuseFailAlloc_4707_, 13, v_e_4676_);
lean_ctor_set(v_reuseFailAlloc_4707_, 14, v_c_4677_);
lean_ctor_set(v_reuseFailAlloc_4707_, 15, v_F_4678_);
lean_ctor_set(v_reuseFailAlloc_4707_, 16, v_a_4679_);
lean_ctor_set(v_reuseFailAlloc_4707_, 17, v_b_4680_);
lean_ctor_set(v_reuseFailAlloc_4707_, 18, v_B_4681_);
lean_ctor_set(v_reuseFailAlloc_4707_, 19, v_h_4682_);
lean_ctor_set(v_reuseFailAlloc_4707_, 20, v_K_4683_);
lean_ctor_set(v_reuseFailAlloc_4707_, 21, v_k_4684_);
lean_ctor_set(v_reuseFailAlloc_4707_, 22, v_H_4685_);
lean_ctor_set(v_reuseFailAlloc_4707_, 23, v_m_4686_);
lean_ctor_set(v_reuseFailAlloc_4707_, 24, v_s_4687_);
lean_ctor_set(v_reuseFailAlloc_4707_, 25, v_S_4688_);
lean_ctor_set(v_reuseFailAlloc_4707_, 26, v_A_4689_);
lean_ctor_set(v_reuseFailAlloc_4707_, 27, v_n_4690_);
lean_ctor_set(v_reuseFailAlloc_4707_, 28, v_N_4691_);
lean_ctor_set(v_reuseFailAlloc_4707_, 29, v_V_4692_);
lean_ctor_set(v_reuseFailAlloc_4707_, 30, v_z_4693_);
lean_ctor_set(v_reuseFailAlloc_4707_, 31, v_zabbrev_4694_);
lean_ctor_set(v_reuseFailAlloc_4707_, 32, v_v_4695_);
lean_ctor_set(v_reuseFailAlloc_4707_, 33, v_O_4696_);
lean_ctor_set(v_reuseFailAlloc_4707_, 34, v_X_4697_);
lean_ctor_set(v_reuseFailAlloc_4707_, 35, v_x_4698_);
lean_ctor_set(v_reuseFailAlloc_4707_, 36, v_Z_4699_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
}
case 3:
{
lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4763_; 
v_isSharedCheck_4763_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_4763_ == 0)
{
lean_object* v_unused_4764_; 
v_unused_4764_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_4764_);
v___x_4714_ = v_modifier_4562_;
v_isShared_4715_ = v_isSharedCheck_4763_;
goto v_resetjp_4713_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4763_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v_G_4716_; lean_object* v_y_4717_; lean_object* v_u_4718_; lean_object* v_Y_4719_; lean_object* v_M_4720_; lean_object* v_L_4721_; lean_object* v_d_4722_; lean_object* v_Q_4723_; lean_object* v_q_4724_; lean_object* v_w_4725_; lean_object* v_W_4726_; lean_object* v_E_4727_; lean_object* v_e_4728_; lean_object* v_c_4729_; lean_object* v_F_4730_; lean_object* v_a_4731_; lean_object* v_b_4732_; lean_object* v_B_4733_; lean_object* v_h_4734_; lean_object* v_K_4735_; lean_object* v_k_4736_; lean_object* v_H_4737_; lean_object* v_m_4738_; lean_object* v_s_4739_; lean_object* v_S_4740_; lean_object* v_A_4741_; lean_object* v_n_4742_; lean_object* v_N_4743_; lean_object* v_V_4744_; lean_object* v_z_4745_; lean_object* v_zabbrev_4746_; lean_object* v_v_4747_; lean_object* v_O_4748_; lean_object* v_X_4749_; lean_object* v_x_4750_; lean_object* v_Z_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4761_; 
v_G_4716_ = lean_ctor_get(v_date_4561_, 0);
v_y_4717_ = lean_ctor_get(v_date_4561_, 1);
v_u_4718_ = lean_ctor_get(v_date_4561_, 2);
v_Y_4719_ = lean_ctor_get(v_date_4561_, 3);
v_M_4720_ = lean_ctor_get(v_date_4561_, 5);
v_L_4721_ = lean_ctor_get(v_date_4561_, 6);
v_d_4722_ = lean_ctor_get(v_date_4561_, 7);
v_Q_4723_ = lean_ctor_get(v_date_4561_, 8);
v_q_4724_ = lean_ctor_get(v_date_4561_, 9);
v_w_4725_ = lean_ctor_get(v_date_4561_, 10);
v_W_4726_ = lean_ctor_get(v_date_4561_, 11);
v_E_4727_ = lean_ctor_get(v_date_4561_, 12);
v_e_4728_ = lean_ctor_get(v_date_4561_, 13);
v_c_4729_ = lean_ctor_get(v_date_4561_, 14);
v_F_4730_ = lean_ctor_get(v_date_4561_, 15);
v_a_4731_ = lean_ctor_get(v_date_4561_, 16);
v_b_4732_ = lean_ctor_get(v_date_4561_, 17);
v_B_4733_ = lean_ctor_get(v_date_4561_, 18);
v_h_4734_ = lean_ctor_get(v_date_4561_, 19);
v_K_4735_ = lean_ctor_get(v_date_4561_, 20);
v_k_4736_ = lean_ctor_get(v_date_4561_, 21);
v_H_4737_ = lean_ctor_get(v_date_4561_, 22);
v_m_4738_ = lean_ctor_get(v_date_4561_, 23);
v_s_4739_ = lean_ctor_get(v_date_4561_, 24);
v_S_4740_ = lean_ctor_get(v_date_4561_, 25);
v_A_4741_ = lean_ctor_get(v_date_4561_, 26);
v_n_4742_ = lean_ctor_get(v_date_4561_, 27);
v_N_4743_ = lean_ctor_get(v_date_4561_, 28);
v_V_4744_ = lean_ctor_get(v_date_4561_, 29);
v_z_4745_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_4746_ = lean_ctor_get(v_date_4561_, 31);
v_v_4747_ = lean_ctor_get(v_date_4561_, 32);
v_O_4748_ = lean_ctor_get(v_date_4561_, 33);
v_X_4749_ = lean_ctor_get(v_date_4561_, 34);
v_x_4750_ = lean_ctor_get(v_date_4561_, 35);
v_Z_4751_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_4761_ == 0)
{
lean_object* v_unused_4762_; 
v_unused_4762_ = lean_ctor_get(v_date_4561_, 4);
lean_dec(v_unused_4762_);
v___x_4753_ = v_date_4561_;
v_isShared_4754_ = v_isSharedCheck_4761_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_Z_4751_);
lean_inc(v_x_4750_);
lean_inc(v_X_4749_);
lean_inc(v_O_4748_);
lean_inc(v_v_4747_);
lean_inc(v_zabbrev_4746_);
lean_inc(v_z_4745_);
lean_inc(v_V_4744_);
lean_inc(v_N_4743_);
lean_inc(v_n_4742_);
lean_inc(v_A_4741_);
lean_inc(v_S_4740_);
lean_inc(v_s_4739_);
lean_inc(v_m_4738_);
lean_inc(v_H_4737_);
lean_inc(v_k_4736_);
lean_inc(v_K_4735_);
lean_inc(v_h_4734_);
lean_inc(v_B_4733_);
lean_inc(v_b_4732_);
lean_inc(v_a_4731_);
lean_inc(v_F_4730_);
lean_inc(v_c_4729_);
lean_inc(v_e_4728_);
lean_inc(v_E_4727_);
lean_inc(v_W_4726_);
lean_inc(v_w_4725_);
lean_inc(v_q_4724_);
lean_inc(v_Q_4723_);
lean_inc(v_d_4722_);
lean_inc(v_L_4721_);
lean_inc(v_M_4720_);
lean_inc(v_Y_4719_);
lean_inc(v_u_4718_);
lean_inc(v_y_4717_);
lean_inc(v_G_4716_);
lean_dec(v_date_4561_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4761_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4715_ == 0)
{
lean_ctor_set_tag(v___x_4714_, 1);
lean_ctor_set(v___x_4714_, 0, v_data_4563_);
v___x_4756_ = v___x_4714_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_data_4563_);
v___x_4756_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
lean_object* v___x_4758_; 
if (v_isShared_4754_ == 0)
{
lean_ctor_set(v___x_4753_, 4, v___x_4756_);
v___x_4758_ = v___x_4753_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_G_4716_);
lean_ctor_set(v_reuseFailAlloc_4759_, 1, v_y_4717_);
lean_ctor_set(v_reuseFailAlloc_4759_, 2, v_u_4718_);
lean_ctor_set(v_reuseFailAlloc_4759_, 3, v_Y_4719_);
lean_ctor_set(v_reuseFailAlloc_4759_, 4, v___x_4756_);
lean_ctor_set(v_reuseFailAlloc_4759_, 5, v_M_4720_);
lean_ctor_set(v_reuseFailAlloc_4759_, 6, v_L_4721_);
lean_ctor_set(v_reuseFailAlloc_4759_, 7, v_d_4722_);
lean_ctor_set(v_reuseFailAlloc_4759_, 8, v_Q_4723_);
lean_ctor_set(v_reuseFailAlloc_4759_, 9, v_q_4724_);
lean_ctor_set(v_reuseFailAlloc_4759_, 10, v_w_4725_);
lean_ctor_set(v_reuseFailAlloc_4759_, 11, v_W_4726_);
lean_ctor_set(v_reuseFailAlloc_4759_, 12, v_E_4727_);
lean_ctor_set(v_reuseFailAlloc_4759_, 13, v_e_4728_);
lean_ctor_set(v_reuseFailAlloc_4759_, 14, v_c_4729_);
lean_ctor_set(v_reuseFailAlloc_4759_, 15, v_F_4730_);
lean_ctor_set(v_reuseFailAlloc_4759_, 16, v_a_4731_);
lean_ctor_set(v_reuseFailAlloc_4759_, 17, v_b_4732_);
lean_ctor_set(v_reuseFailAlloc_4759_, 18, v_B_4733_);
lean_ctor_set(v_reuseFailAlloc_4759_, 19, v_h_4734_);
lean_ctor_set(v_reuseFailAlloc_4759_, 20, v_K_4735_);
lean_ctor_set(v_reuseFailAlloc_4759_, 21, v_k_4736_);
lean_ctor_set(v_reuseFailAlloc_4759_, 22, v_H_4737_);
lean_ctor_set(v_reuseFailAlloc_4759_, 23, v_m_4738_);
lean_ctor_set(v_reuseFailAlloc_4759_, 24, v_s_4739_);
lean_ctor_set(v_reuseFailAlloc_4759_, 25, v_S_4740_);
lean_ctor_set(v_reuseFailAlloc_4759_, 26, v_A_4741_);
lean_ctor_set(v_reuseFailAlloc_4759_, 27, v_n_4742_);
lean_ctor_set(v_reuseFailAlloc_4759_, 28, v_N_4743_);
lean_ctor_set(v_reuseFailAlloc_4759_, 29, v_V_4744_);
lean_ctor_set(v_reuseFailAlloc_4759_, 30, v_z_4745_);
lean_ctor_set(v_reuseFailAlloc_4759_, 31, v_zabbrev_4746_);
lean_ctor_set(v_reuseFailAlloc_4759_, 32, v_v_4747_);
lean_ctor_set(v_reuseFailAlloc_4759_, 33, v_O_4748_);
lean_ctor_set(v_reuseFailAlloc_4759_, 34, v_X_4749_);
lean_ctor_set(v_reuseFailAlloc_4759_, 35, v_x_4750_);
lean_ctor_set(v_reuseFailAlloc_4759_, 36, v_Z_4751_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
}
case 4:
{
lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4815_; 
v_isSharedCheck_4815_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_4815_ == 0)
{
lean_object* v_unused_4816_; 
v_unused_4816_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_4816_);
v___x_4766_ = v_modifier_4562_;
v_isShared_4767_ = v_isSharedCheck_4815_;
goto v_resetjp_4765_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4815_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v_G_4768_; lean_object* v_y_4769_; lean_object* v_u_4770_; lean_object* v_Y_4771_; lean_object* v_D_4772_; lean_object* v_L_4773_; lean_object* v_d_4774_; lean_object* v_Q_4775_; lean_object* v_q_4776_; lean_object* v_w_4777_; lean_object* v_W_4778_; lean_object* v_E_4779_; lean_object* v_e_4780_; lean_object* v_c_4781_; lean_object* v_F_4782_; lean_object* v_a_4783_; lean_object* v_b_4784_; lean_object* v_B_4785_; lean_object* v_h_4786_; lean_object* v_K_4787_; lean_object* v_k_4788_; lean_object* v_H_4789_; lean_object* v_m_4790_; lean_object* v_s_4791_; lean_object* v_S_4792_; lean_object* v_A_4793_; lean_object* v_n_4794_; lean_object* v_N_4795_; lean_object* v_V_4796_; lean_object* v_z_4797_; lean_object* v_zabbrev_4798_; lean_object* v_v_4799_; lean_object* v_O_4800_; lean_object* v_X_4801_; lean_object* v_x_4802_; lean_object* v_Z_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4813_; 
v_G_4768_ = lean_ctor_get(v_date_4561_, 0);
v_y_4769_ = lean_ctor_get(v_date_4561_, 1);
v_u_4770_ = lean_ctor_get(v_date_4561_, 2);
v_Y_4771_ = lean_ctor_get(v_date_4561_, 3);
v_D_4772_ = lean_ctor_get(v_date_4561_, 4);
v_L_4773_ = lean_ctor_get(v_date_4561_, 6);
v_d_4774_ = lean_ctor_get(v_date_4561_, 7);
v_Q_4775_ = lean_ctor_get(v_date_4561_, 8);
v_q_4776_ = lean_ctor_get(v_date_4561_, 9);
v_w_4777_ = lean_ctor_get(v_date_4561_, 10);
v_W_4778_ = lean_ctor_get(v_date_4561_, 11);
v_E_4779_ = lean_ctor_get(v_date_4561_, 12);
v_e_4780_ = lean_ctor_get(v_date_4561_, 13);
v_c_4781_ = lean_ctor_get(v_date_4561_, 14);
v_F_4782_ = lean_ctor_get(v_date_4561_, 15);
v_a_4783_ = lean_ctor_get(v_date_4561_, 16);
v_b_4784_ = lean_ctor_get(v_date_4561_, 17);
v_B_4785_ = lean_ctor_get(v_date_4561_, 18);
v_h_4786_ = lean_ctor_get(v_date_4561_, 19);
v_K_4787_ = lean_ctor_get(v_date_4561_, 20);
v_k_4788_ = lean_ctor_get(v_date_4561_, 21);
v_H_4789_ = lean_ctor_get(v_date_4561_, 22);
v_m_4790_ = lean_ctor_get(v_date_4561_, 23);
v_s_4791_ = lean_ctor_get(v_date_4561_, 24);
v_S_4792_ = lean_ctor_get(v_date_4561_, 25);
v_A_4793_ = lean_ctor_get(v_date_4561_, 26);
v_n_4794_ = lean_ctor_get(v_date_4561_, 27);
v_N_4795_ = lean_ctor_get(v_date_4561_, 28);
v_V_4796_ = lean_ctor_get(v_date_4561_, 29);
v_z_4797_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_4798_ = lean_ctor_get(v_date_4561_, 31);
v_v_4799_ = lean_ctor_get(v_date_4561_, 32);
v_O_4800_ = lean_ctor_get(v_date_4561_, 33);
v_X_4801_ = lean_ctor_get(v_date_4561_, 34);
v_x_4802_ = lean_ctor_get(v_date_4561_, 35);
v_Z_4803_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_4813_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_4813_ == 0)
{
lean_object* v_unused_4814_; 
v_unused_4814_ = lean_ctor_get(v_date_4561_, 5);
lean_dec(v_unused_4814_);
v___x_4805_ = v_date_4561_;
v_isShared_4806_ = v_isSharedCheck_4813_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_Z_4803_);
lean_inc(v_x_4802_);
lean_inc(v_X_4801_);
lean_inc(v_O_4800_);
lean_inc(v_v_4799_);
lean_inc(v_zabbrev_4798_);
lean_inc(v_z_4797_);
lean_inc(v_V_4796_);
lean_inc(v_N_4795_);
lean_inc(v_n_4794_);
lean_inc(v_A_4793_);
lean_inc(v_S_4792_);
lean_inc(v_s_4791_);
lean_inc(v_m_4790_);
lean_inc(v_H_4789_);
lean_inc(v_k_4788_);
lean_inc(v_K_4787_);
lean_inc(v_h_4786_);
lean_inc(v_B_4785_);
lean_inc(v_b_4784_);
lean_inc(v_a_4783_);
lean_inc(v_F_4782_);
lean_inc(v_c_4781_);
lean_inc(v_e_4780_);
lean_inc(v_E_4779_);
lean_inc(v_W_4778_);
lean_inc(v_w_4777_);
lean_inc(v_q_4776_);
lean_inc(v_Q_4775_);
lean_inc(v_d_4774_);
lean_inc(v_L_4773_);
lean_inc(v_D_4772_);
lean_inc(v_Y_4771_);
lean_inc(v_u_4770_);
lean_inc(v_y_4769_);
lean_inc(v_G_4768_);
lean_dec(v_date_4561_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4813_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4767_ == 0)
{
lean_ctor_set_tag(v___x_4766_, 1);
lean_ctor_set(v___x_4766_, 0, v_data_4563_);
v___x_4808_ = v___x_4766_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_data_4563_);
v___x_4808_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_object* v___x_4810_; 
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 5, v___x_4808_);
v___x_4810_ = v___x_4805_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_G_4768_);
lean_ctor_set(v_reuseFailAlloc_4811_, 1, v_y_4769_);
lean_ctor_set(v_reuseFailAlloc_4811_, 2, v_u_4770_);
lean_ctor_set(v_reuseFailAlloc_4811_, 3, v_Y_4771_);
lean_ctor_set(v_reuseFailAlloc_4811_, 4, v_D_4772_);
lean_ctor_set(v_reuseFailAlloc_4811_, 5, v___x_4808_);
lean_ctor_set(v_reuseFailAlloc_4811_, 6, v_L_4773_);
lean_ctor_set(v_reuseFailAlloc_4811_, 7, v_d_4774_);
lean_ctor_set(v_reuseFailAlloc_4811_, 8, v_Q_4775_);
lean_ctor_set(v_reuseFailAlloc_4811_, 9, v_q_4776_);
lean_ctor_set(v_reuseFailAlloc_4811_, 10, v_w_4777_);
lean_ctor_set(v_reuseFailAlloc_4811_, 11, v_W_4778_);
lean_ctor_set(v_reuseFailAlloc_4811_, 12, v_E_4779_);
lean_ctor_set(v_reuseFailAlloc_4811_, 13, v_e_4780_);
lean_ctor_set(v_reuseFailAlloc_4811_, 14, v_c_4781_);
lean_ctor_set(v_reuseFailAlloc_4811_, 15, v_F_4782_);
lean_ctor_set(v_reuseFailAlloc_4811_, 16, v_a_4783_);
lean_ctor_set(v_reuseFailAlloc_4811_, 17, v_b_4784_);
lean_ctor_set(v_reuseFailAlloc_4811_, 18, v_B_4785_);
lean_ctor_set(v_reuseFailAlloc_4811_, 19, v_h_4786_);
lean_ctor_set(v_reuseFailAlloc_4811_, 20, v_K_4787_);
lean_ctor_set(v_reuseFailAlloc_4811_, 21, v_k_4788_);
lean_ctor_set(v_reuseFailAlloc_4811_, 22, v_H_4789_);
lean_ctor_set(v_reuseFailAlloc_4811_, 23, v_m_4790_);
lean_ctor_set(v_reuseFailAlloc_4811_, 24, v_s_4791_);
lean_ctor_set(v_reuseFailAlloc_4811_, 25, v_S_4792_);
lean_ctor_set(v_reuseFailAlloc_4811_, 26, v_A_4793_);
lean_ctor_set(v_reuseFailAlloc_4811_, 27, v_n_4794_);
lean_ctor_set(v_reuseFailAlloc_4811_, 28, v_N_4795_);
lean_ctor_set(v_reuseFailAlloc_4811_, 29, v_V_4796_);
lean_ctor_set(v_reuseFailAlloc_4811_, 30, v_z_4797_);
lean_ctor_set(v_reuseFailAlloc_4811_, 31, v_zabbrev_4798_);
lean_ctor_set(v_reuseFailAlloc_4811_, 32, v_v_4799_);
lean_ctor_set(v_reuseFailAlloc_4811_, 33, v_O_4800_);
lean_ctor_set(v_reuseFailAlloc_4811_, 34, v_X_4801_);
lean_ctor_set(v_reuseFailAlloc_4811_, 35, v_x_4802_);
lean_ctor_set(v_reuseFailAlloc_4811_, 36, v_Z_4803_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
}
case 5:
{
lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4867_; 
v_isSharedCheck_4867_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_4867_ == 0)
{
lean_object* v_unused_4868_; 
v_unused_4868_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_4868_);
v___x_4818_ = v_modifier_4562_;
v_isShared_4819_ = v_isSharedCheck_4867_;
goto v_resetjp_4817_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4867_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v_G_4820_; lean_object* v_y_4821_; lean_object* v_u_4822_; lean_object* v_Y_4823_; lean_object* v_D_4824_; lean_object* v_M_4825_; lean_object* v_d_4826_; lean_object* v_Q_4827_; lean_object* v_q_4828_; lean_object* v_w_4829_; lean_object* v_W_4830_; lean_object* v_E_4831_; lean_object* v_e_4832_; lean_object* v_c_4833_; lean_object* v_F_4834_; lean_object* v_a_4835_; lean_object* v_b_4836_; lean_object* v_B_4837_; lean_object* v_h_4838_; lean_object* v_K_4839_; lean_object* v_k_4840_; lean_object* v_H_4841_; lean_object* v_m_4842_; lean_object* v_s_4843_; lean_object* v_S_4844_; lean_object* v_A_4845_; lean_object* v_n_4846_; lean_object* v_N_4847_; lean_object* v_V_4848_; lean_object* v_z_4849_; lean_object* v_zabbrev_4850_; lean_object* v_v_4851_; lean_object* v_O_4852_; lean_object* v_X_4853_; lean_object* v_x_4854_; lean_object* v_Z_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4865_; 
v_G_4820_ = lean_ctor_get(v_date_4561_, 0);
v_y_4821_ = lean_ctor_get(v_date_4561_, 1);
v_u_4822_ = lean_ctor_get(v_date_4561_, 2);
v_Y_4823_ = lean_ctor_get(v_date_4561_, 3);
v_D_4824_ = lean_ctor_get(v_date_4561_, 4);
v_M_4825_ = lean_ctor_get(v_date_4561_, 5);
v_d_4826_ = lean_ctor_get(v_date_4561_, 7);
v_Q_4827_ = lean_ctor_get(v_date_4561_, 8);
v_q_4828_ = lean_ctor_get(v_date_4561_, 9);
v_w_4829_ = lean_ctor_get(v_date_4561_, 10);
v_W_4830_ = lean_ctor_get(v_date_4561_, 11);
v_E_4831_ = lean_ctor_get(v_date_4561_, 12);
v_e_4832_ = lean_ctor_get(v_date_4561_, 13);
v_c_4833_ = lean_ctor_get(v_date_4561_, 14);
v_F_4834_ = lean_ctor_get(v_date_4561_, 15);
v_a_4835_ = lean_ctor_get(v_date_4561_, 16);
v_b_4836_ = lean_ctor_get(v_date_4561_, 17);
v_B_4837_ = lean_ctor_get(v_date_4561_, 18);
v_h_4838_ = lean_ctor_get(v_date_4561_, 19);
v_K_4839_ = lean_ctor_get(v_date_4561_, 20);
v_k_4840_ = lean_ctor_get(v_date_4561_, 21);
v_H_4841_ = lean_ctor_get(v_date_4561_, 22);
v_m_4842_ = lean_ctor_get(v_date_4561_, 23);
v_s_4843_ = lean_ctor_get(v_date_4561_, 24);
v_S_4844_ = lean_ctor_get(v_date_4561_, 25);
v_A_4845_ = lean_ctor_get(v_date_4561_, 26);
v_n_4846_ = lean_ctor_get(v_date_4561_, 27);
v_N_4847_ = lean_ctor_get(v_date_4561_, 28);
v_V_4848_ = lean_ctor_get(v_date_4561_, 29);
v_z_4849_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_4850_ = lean_ctor_get(v_date_4561_, 31);
v_v_4851_ = lean_ctor_get(v_date_4561_, 32);
v_O_4852_ = lean_ctor_get(v_date_4561_, 33);
v_X_4853_ = lean_ctor_get(v_date_4561_, 34);
v_x_4854_ = lean_ctor_get(v_date_4561_, 35);
v_Z_4855_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_4865_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_4865_ == 0)
{
lean_object* v_unused_4866_; 
v_unused_4866_ = lean_ctor_get(v_date_4561_, 6);
lean_dec(v_unused_4866_);
v___x_4857_ = v_date_4561_;
v_isShared_4858_ = v_isSharedCheck_4865_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_Z_4855_);
lean_inc(v_x_4854_);
lean_inc(v_X_4853_);
lean_inc(v_O_4852_);
lean_inc(v_v_4851_);
lean_inc(v_zabbrev_4850_);
lean_inc(v_z_4849_);
lean_inc(v_V_4848_);
lean_inc(v_N_4847_);
lean_inc(v_n_4846_);
lean_inc(v_A_4845_);
lean_inc(v_S_4844_);
lean_inc(v_s_4843_);
lean_inc(v_m_4842_);
lean_inc(v_H_4841_);
lean_inc(v_k_4840_);
lean_inc(v_K_4839_);
lean_inc(v_h_4838_);
lean_inc(v_B_4837_);
lean_inc(v_b_4836_);
lean_inc(v_a_4835_);
lean_inc(v_F_4834_);
lean_inc(v_c_4833_);
lean_inc(v_e_4832_);
lean_inc(v_E_4831_);
lean_inc(v_W_4830_);
lean_inc(v_w_4829_);
lean_inc(v_q_4828_);
lean_inc(v_Q_4827_);
lean_inc(v_d_4826_);
lean_inc(v_M_4825_);
lean_inc(v_D_4824_);
lean_inc(v_Y_4823_);
lean_inc(v_u_4822_);
lean_inc(v_y_4821_);
lean_inc(v_G_4820_);
lean_dec(v_date_4561_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4865_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4860_; 
if (v_isShared_4819_ == 0)
{
lean_ctor_set_tag(v___x_4818_, 1);
lean_ctor_set(v___x_4818_, 0, v_data_4563_);
v___x_4860_ = v___x_4818_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_data_4563_);
v___x_4860_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
lean_object* v___x_4862_; 
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 6, v___x_4860_);
v___x_4862_ = v___x_4857_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_G_4820_);
lean_ctor_set(v_reuseFailAlloc_4863_, 1, v_y_4821_);
lean_ctor_set(v_reuseFailAlloc_4863_, 2, v_u_4822_);
lean_ctor_set(v_reuseFailAlloc_4863_, 3, v_Y_4823_);
lean_ctor_set(v_reuseFailAlloc_4863_, 4, v_D_4824_);
lean_ctor_set(v_reuseFailAlloc_4863_, 5, v_M_4825_);
lean_ctor_set(v_reuseFailAlloc_4863_, 6, v___x_4860_);
lean_ctor_set(v_reuseFailAlloc_4863_, 7, v_d_4826_);
lean_ctor_set(v_reuseFailAlloc_4863_, 8, v_Q_4827_);
lean_ctor_set(v_reuseFailAlloc_4863_, 9, v_q_4828_);
lean_ctor_set(v_reuseFailAlloc_4863_, 10, v_w_4829_);
lean_ctor_set(v_reuseFailAlloc_4863_, 11, v_W_4830_);
lean_ctor_set(v_reuseFailAlloc_4863_, 12, v_E_4831_);
lean_ctor_set(v_reuseFailAlloc_4863_, 13, v_e_4832_);
lean_ctor_set(v_reuseFailAlloc_4863_, 14, v_c_4833_);
lean_ctor_set(v_reuseFailAlloc_4863_, 15, v_F_4834_);
lean_ctor_set(v_reuseFailAlloc_4863_, 16, v_a_4835_);
lean_ctor_set(v_reuseFailAlloc_4863_, 17, v_b_4836_);
lean_ctor_set(v_reuseFailAlloc_4863_, 18, v_B_4837_);
lean_ctor_set(v_reuseFailAlloc_4863_, 19, v_h_4838_);
lean_ctor_set(v_reuseFailAlloc_4863_, 20, v_K_4839_);
lean_ctor_set(v_reuseFailAlloc_4863_, 21, v_k_4840_);
lean_ctor_set(v_reuseFailAlloc_4863_, 22, v_H_4841_);
lean_ctor_set(v_reuseFailAlloc_4863_, 23, v_m_4842_);
lean_ctor_set(v_reuseFailAlloc_4863_, 24, v_s_4843_);
lean_ctor_set(v_reuseFailAlloc_4863_, 25, v_S_4844_);
lean_ctor_set(v_reuseFailAlloc_4863_, 26, v_A_4845_);
lean_ctor_set(v_reuseFailAlloc_4863_, 27, v_n_4846_);
lean_ctor_set(v_reuseFailAlloc_4863_, 28, v_N_4847_);
lean_ctor_set(v_reuseFailAlloc_4863_, 29, v_V_4848_);
lean_ctor_set(v_reuseFailAlloc_4863_, 30, v_z_4849_);
lean_ctor_set(v_reuseFailAlloc_4863_, 31, v_zabbrev_4850_);
lean_ctor_set(v_reuseFailAlloc_4863_, 32, v_v_4851_);
lean_ctor_set(v_reuseFailAlloc_4863_, 33, v_O_4852_);
lean_ctor_set(v_reuseFailAlloc_4863_, 34, v_X_4853_);
lean_ctor_set(v_reuseFailAlloc_4863_, 35, v_x_4854_);
lean_ctor_set(v_reuseFailAlloc_4863_, 36, v_Z_4855_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
}
case 6:
{
lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4919_; 
v_isSharedCheck_4919_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_4919_ == 0)
{
lean_object* v_unused_4920_; 
v_unused_4920_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_4920_);
v___x_4870_ = v_modifier_4562_;
v_isShared_4871_ = v_isSharedCheck_4919_;
goto v_resetjp_4869_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4919_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v_G_4872_; lean_object* v_y_4873_; lean_object* v_u_4874_; lean_object* v_Y_4875_; lean_object* v_D_4876_; lean_object* v_M_4877_; lean_object* v_L_4878_; lean_object* v_Q_4879_; lean_object* v_q_4880_; lean_object* v_w_4881_; lean_object* v_W_4882_; lean_object* v_E_4883_; lean_object* v_e_4884_; lean_object* v_c_4885_; lean_object* v_F_4886_; lean_object* v_a_4887_; lean_object* v_b_4888_; lean_object* v_B_4889_; lean_object* v_h_4890_; lean_object* v_K_4891_; lean_object* v_k_4892_; lean_object* v_H_4893_; lean_object* v_m_4894_; lean_object* v_s_4895_; lean_object* v_S_4896_; lean_object* v_A_4897_; lean_object* v_n_4898_; lean_object* v_N_4899_; lean_object* v_V_4900_; lean_object* v_z_4901_; lean_object* v_zabbrev_4902_; lean_object* v_v_4903_; lean_object* v_O_4904_; lean_object* v_X_4905_; lean_object* v_x_4906_; lean_object* v_Z_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4917_; 
v_G_4872_ = lean_ctor_get(v_date_4561_, 0);
v_y_4873_ = lean_ctor_get(v_date_4561_, 1);
v_u_4874_ = lean_ctor_get(v_date_4561_, 2);
v_Y_4875_ = lean_ctor_get(v_date_4561_, 3);
v_D_4876_ = lean_ctor_get(v_date_4561_, 4);
v_M_4877_ = lean_ctor_get(v_date_4561_, 5);
v_L_4878_ = lean_ctor_get(v_date_4561_, 6);
v_Q_4879_ = lean_ctor_get(v_date_4561_, 8);
v_q_4880_ = lean_ctor_get(v_date_4561_, 9);
v_w_4881_ = lean_ctor_get(v_date_4561_, 10);
v_W_4882_ = lean_ctor_get(v_date_4561_, 11);
v_E_4883_ = lean_ctor_get(v_date_4561_, 12);
v_e_4884_ = lean_ctor_get(v_date_4561_, 13);
v_c_4885_ = lean_ctor_get(v_date_4561_, 14);
v_F_4886_ = lean_ctor_get(v_date_4561_, 15);
v_a_4887_ = lean_ctor_get(v_date_4561_, 16);
v_b_4888_ = lean_ctor_get(v_date_4561_, 17);
v_B_4889_ = lean_ctor_get(v_date_4561_, 18);
v_h_4890_ = lean_ctor_get(v_date_4561_, 19);
v_K_4891_ = lean_ctor_get(v_date_4561_, 20);
v_k_4892_ = lean_ctor_get(v_date_4561_, 21);
v_H_4893_ = lean_ctor_get(v_date_4561_, 22);
v_m_4894_ = lean_ctor_get(v_date_4561_, 23);
v_s_4895_ = lean_ctor_get(v_date_4561_, 24);
v_S_4896_ = lean_ctor_get(v_date_4561_, 25);
v_A_4897_ = lean_ctor_get(v_date_4561_, 26);
v_n_4898_ = lean_ctor_get(v_date_4561_, 27);
v_N_4899_ = lean_ctor_get(v_date_4561_, 28);
v_V_4900_ = lean_ctor_get(v_date_4561_, 29);
v_z_4901_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_4902_ = lean_ctor_get(v_date_4561_, 31);
v_v_4903_ = lean_ctor_get(v_date_4561_, 32);
v_O_4904_ = lean_ctor_get(v_date_4561_, 33);
v_X_4905_ = lean_ctor_get(v_date_4561_, 34);
v_x_4906_ = lean_ctor_get(v_date_4561_, 35);
v_Z_4907_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_4917_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_4917_ == 0)
{
lean_object* v_unused_4918_; 
v_unused_4918_ = lean_ctor_get(v_date_4561_, 7);
lean_dec(v_unused_4918_);
v___x_4909_ = v_date_4561_;
v_isShared_4910_ = v_isSharedCheck_4917_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_Z_4907_);
lean_inc(v_x_4906_);
lean_inc(v_X_4905_);
lean_inc(v_O_4904_);
lean_inc(v_v_4903_);
lean_inc(v_zabbrev_4902_);
lean_inc(v_z_4901_);
lean_inc(v_V_4900_);
lean_inc(v_N_4899_);
lean_inc(v_n_4898_);
lean_inc(v_A_4897_);
lean_inc(v_S_4896_);
lean_inc(v_s_4895_);
lean_inc(v_m_4894_);
lean_inc(v_H_4893_);
lean_inc(v_k_4892_);
lean_inc(v_K_4891_);
lean_inc(v_h_4890_);
lean_inc(v_B_4889_);
lean_inc(v_b_4888_);
lean_inc(v_a_4887_);
lean_inc(v_F_4886_);
lean_inc(v_c_4885_);
lean_inc(v_e_4884_);
lean_inc(v_E_4883_);
lean_inc(v_W_4882_);
lean_inc(v_w_4881_);
lean_inc(v_q_4880_);
lean_inc(v_Q_4879_);
lean_inc(v_L_4878_);
lean_inc(v_M_4877_);
lean_inc(v_D_4876_);
lean_inc(v_Y_4875_);
lean_inc(v_u_4874_);
lean_inc(v_y_4873_);
lean_inc(v_G_4872_);
lean_dec(v_date_4561_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4917_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4912_; 
if (v_isShared_4871_ == 0)
{
lean_ctor_set_tag(v___x_4870_, 1);
lean_ctor_set(v___x_4870_, 0, v_data_4563_);
v___x_4912_ = v___x_4870_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_data_4563_);
v___x_4912_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
lean_object* v___x_4914_; 
if (v_isShared_4910_ == 0)
{
lean_ctor_set(v___x_4909_, 7, v___x_4912_);
v___x_4914_ = v___x_4909_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_G_4872_);
lean_ctor_set(v_reuseFailAlloc_4915_, 1, v_y_4873_);
lean_ctor_set(v_reuseFailAlloc_4915_, 2, v_u_4874_);
lean_ctor_set(v_reuseFailAlloc_4915_, 3, v_Y_4875_);
lean_ctor_set(v_reuseFailAlloc_4915_, 4, v_D_4876_);
lean_ctor_set(v_reuseFailAlloc_4915_, 5, v_M_4877_);
lean_ctor_set(v_reuseFailAlloc_4915_, 6, v_L_4878_);
lean_ctor_set(v_reuseFailAlloc_4915_, 7, v___x_4912_);
lean_ctor_set(v_reuseFailAlloc_4915_, 8, v_Q_4879_);
lean_ctor_set(v_reuseFailAlloc_4915_, 9, v_q_4880_);
lean_ctor_set(v_reuseFailAlloc_4915_, 10, v_w_4881_);
lean_ctor_set(v_reuseFailAlloc_4915_, 11, v_W_4882_);
lean_ctor_set(v_reuseFailAlloc_4915_, 12, v_E_4883_);
lean_ctor_set(v_reuseFailAlloc_4915_, 13, v_e_4884_);
lean_ctor_set(v_reuseFailAlloc_4915_, 14, v_c_4885_);
lean_ctor_set(v_reuseFailAlloc_4915_, 15, v_F_4886_);
lean_ctor_set(v_reuseFailAlloc_4915_, 16, v_a_4887_);
lean_ctor_set(v_reuseFailAlloc_4915_, 17, v_b_4888_);
lean_ctor_set(v_reuseFailAlloc_4915_, 18, v_B_4889_);
lean_ctor_set(v_reuseFailAlloc_4915_, 19, v_h_4890_);
lean_ctor_set(v_reuseFailAlloc_4915_, 20, v_K_4891_);
lean_ctor_set(v_reuseFailAlloc_4915_, 21, v_k_4892_);
lean_ctor_set(v_reuseFailAlloc_4915_, 22, v_H_4893_);
lean_ctor_set(v_reuseFailAlloc_4915_, 23, v_m_4894_);
lean_ctor_set(v_reuseFailAlloc_4915_, 24, v_s_4895_);
lean_ctor_set(v_reuseFailAlloc_4915_, 25, v_S_4896_);
lean_ctor_set(v_reuseFailAlloc_4915_, 26, v_A_4897_);
lean_ctor_set(v_reuseFailAlloc_4915_, 27, v_n_4898_);
lean_ctor_set(v_reuseFailAlloc_4915_, 28, v_N_4899_);
lean_ctor_set(v_reuseFailAlloc_4915_, 29, v_V_4900_);
lean_ctor_set(v_reuseFailAlloc_4915_, 30, v_z_4901_);
lean_ctor_set(v_reuseFailAlloc_4915_, 31, v_zabbrev_4902_);
lean_ctor_set(v_reuseFailAlloc_4915_, 32, v_v_4903_);
lean_ctor_set(v_reuseFailAlloc_4915_, 33, v_O_4904_);
lean_ctor_set(v_reuseFailAlloc_4915_, 34, v_X_4905_);
lean_ctor_set(v_reuseFailAlloc_4915_, 35, v_x_4906_);
lean_ctor_set(v_reuseFailAlloc_4915_, 36, v_Z_4907_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
}
}
}
}
}
case 7:
{
lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4971_; 
v_isSharedCheck_4971_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_4971_ == 0)
{
lean_object* v_unused_4972_; 
v_unused_4972_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_4972_);
v___x_4922_ = v_modifier_4562_;
v_isShared_4923_ = v_isSharedCheck_4971_;
goto v_resetjp_4921_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4971_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v_G_4924_; lean_object* v_y_4925_; lean_object* v_u_4926_; lean_object* v_Y_4927_; lean_object* v_D_4928_; lean_object* v_M_4929_; lean_object* v_L_4930_; lean_object* v_d_4931_; lean_object* v_q_4932_; lean_object* v_w_4933_; lean_object* v_W_4934_; lean_object* v_E_4935_; lean_object* v_e_4936_; lean_object* v_c_4937_; lean_object* v_F_4938_; lean_object* v_a_4939_; lean_object* v_b_4940_; lean_object* v_B_4941_; lean_object* v_h_4942_; lean_object* v_K_4943_; lean_object* v_k_4944_; lean_object* v_H_4945_; lean_object* v_m_4946_; lean_object* v_s_4947_; lean_object* v_S_4948_; lean_object* v_A_4949_; lean_object* v_n_4950_; lean_object* v_N_4951_; lean_object* v_V_4952_; lean_object* v_z_4953_; lean_object* v_zabbrev_4954_; lean_object* v_v_4955_; lean_object* v_O_4956_; lean_object* v_X_4957_; lean_object* v_x_4958_; lean_object* v_Z_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4969_; 
v_G_4924_ = lean_ctor_get(v_date_4561_, 0);
v_y_4925_ = lean_ctor_get(v_date_4561_, 1);
v_u_4926_ = lean_ctor_get(v_date_4561_, 2);
v_Y_4927_ = lean_ctor_get(v_date_4561_, 3);
v_D_4928_ = lean_ctor_get(v_date_4561_, 4);
v_M_4929_ = lean_ctor_get(v_date_4561_, 5);
v_L_4930_ = lean_ctor_get(v_date_4561_, 6);
v_d_4931_ = lean_ctor_get(v_date_4561_, 7);
v_q_4932_ = lean_ctor_get(v_date_4561_, 9);
v_w_4933_ = lean_ctor_get(v_date_4561_, 10);
v_W_4934_ = lean_ctor_get(v_date_4561_, 11);
v_E_4935_ = lean_ctor_get(v_date_4561_, 12);
v_e_4936_ = lean_ctor_get(v_date_4561_, 13);
v_c_4937_ = lean_ctor_get(v_date_4561_, 14);
v_F_4938_ = lean_ctor_get(v_date_4561_, 15);
v_a_4939_ = lean_ctor_get(v_date_4561_, 16);
v_b_4940_ = lean_ctor_get(v_date_4561_, 17);
v_B_4941_ = lean_ctor_get(v_date_4561_, 18);
v_h_4942_ = lean_ctor_get(v_date_4561_, 19);
v_K_4943_ = lean_ctor_get(v_date_4561_, 20);
v_k_4944_ = lean_ctor_get(v_date_4561_, 21);
v_H_4945_ = lean_ctor_get(v_date_4561_, 22);
v_m_4946_ = lean_ctor_get(v_date_4561_, 23);
v_s_4947_ = lean_ctor_get(v_date_4561_, 24);
v_S_4948_ = lean_ctor_get(v_date_4561_, 25);
v_A_4949_ = lean_ctor_get(v_date_4561_, 26);
v_n_4950_ = lean_ctor_get(v_date_4561_, 27);
v_N_4951_ = lean_ctor_get(v_date_4561_, 28);
v_V_4952_ = lean_ctor_get(v_date_4561_, 29);
v_z_4953_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_4954_ = lean_ctor_get(v_date_4561_, 31);
v_v_4955_ = lean_ctor_get(v_date_4561_, 32);
v_O_4956_ = lean_ctor_get(v_date_4561_, 33);
v_X_4957_ = lean_ctor_get(v_date_4561_, 34);
v_x_4958_ = lean_ctor_get(v_date_4561_, 35);
v_Z_4959_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_4969_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_4969_ == 0)
{
lean_object* v_unused_4970_; 
v_unused_4970_ = lean_ctor_get(v_date_4561_, 8);
lean_dec(v_unused_4970_);
v___x_4961_ = v_date_4561_;
v_isShared_4962_ = v_isSharedCheck_4969_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_Z_4959_);
lean_inc(v_x_4958_);
lean_inc(v_X_4957_);
lean_inc(v_O_4956_);
lean_inc(v_v_4955_);
lean_inc(v_zabbrev_4954_);
lean_inc(v_z_4953_);
lean_inc(v_V_4952_);
lean_inc(v_N_4951_);
lean_inc(v_n_4950_);
lean_inc(v_A_4949_);
lean_inc(v_S_4948_);
lean_inc(v_s_4947_);
lean_inc(v_m_4946_);
lean_inc(v_H_4945_);
lean_inc(v_k_4944_);
lean_inc(v_K_4943_);
lean_inc(v_h_4942_);
lean_inc(v_B_4941_);
lean_inc(v_b_4940_);
lean_inc(v_a_4939_);
lean_inc(v_F_4938_);
lean_inc(v_c_4937_);
lean_inc(v_e_4936_);
lean_inc(v_E_4935_);
lean_inc(v_W_4934_);
lean_inc(v_w_4933_);
lean_inc(v_q_4932_);
lean_inc(v_d_4931_);
lean_inc(v_L_4930_);
lean_inc(v_M_4929_);
lean_inc(v_D_4928_);
lean_inc(v_Y_4927_);
lean_inc(v_u_4926_);
lean_inc(v_y_4925_);
lean_inc(v_G_4924_);
lean_dec(v_date_4561_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4969_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4923_ == 0)
{
lean_ctor_set_tag(v___x_4922_, 1);
lean_ctor_set(v___x_4922_, 0, v_data_4563_);
v___x_4964_ = v___x_4922_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_data_4563_);
v___x_4964_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
lean_object* v___x_4966_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 8, v___x_4964_);
v___x_4966_ = v___x_4961_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_G_4924_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v_y_4925_);
lean_ctor_set(v_reuseFailAlloc_4967_, 2, v_u_4926_);
lean_ctor_set(v_reuseFailAlloc_4967_, 3, v_Y_4927_);
lean_ctor_set(v_reuseFailAlloc_4967_, 4, v_D_4928_);
lean_ctor_set(v_reuseFailAlloc_4967_, 5, v_M_4929_);
lean_ctor_set(v_reuseFailAlloc_4967_, 6, v_L_4930_);
lean_ctor_set(v_reuseFailAlloc_4967_, 7, v_d_4931_);
lean_ctor_set(v_reuseFailAlloc_4967_, 8, v___x_4964_);
lean_ctor_set(v_reuseFailAlloc_4967_, 9, v_q_4932_);
lean_ctor_set(v_reuseFailAlloc_4967_, 10, v_w_4933_);
lean_ctor_set(v_reuseFailAlloc_4967_, 11, v_W_4934_);
lean_ctor_set(v_reuseFailAlloc_4967_, 12, v_E_4935_);
lean_ctor_set(v_reuseFailAlloc_4967_, 13, v_e_4936_);
lean_ctor_set(v_reuseFailAlloc_4967_, 14, v_c_4937_);
lean_ctor_set(v_reuseFailAlloc_4967_, 15, v_F_4938_);
lean_ctor_set(v_reuseFailAlloc_4967_, 16, v_a_4939_);
lean_ctor_set(v_reuseFailAlloc_4967_, 17, v_b_4940_);
lean_ctor_set(v_reuseFailAlloc_4967_, 18, v_B_4941_);
lean_ctor_set(v_reuseFailAlloc_4967_, 19, v_h_4942_);
lean_ctor_set(v_reuseFailAlloc_4967_, 20, v_K_4943_);
lean_ctor_set(v_reuseFailAlloc_4967_, 21, v_k_4944_);
lean_ctor_set(v_reuseFailAlloc_4967_, 22, v_H_4945_);
lean_ctor_set(v_reuseFailAlloc_4967_, 23, v_m_4946_);
lean_ctor_set(v_reuseFailAlloc_4967_, 24, v_s_4947_);
lean_ctor_set(v_reuseFailAlloc_4967_, 25, v_S_4948_);
lean_ctor_set(v_reuseFailAlloc_4967_, 26, v_A_4949_);
lean_ctor_set(v_reuseFailAlloc_4967_, 27, v_n_4950_);
lean_ctor_set(v_reuseFailAlloc_4967_, 28, v_N_4951_);
lean_ctor_set(v_reuseFailAlloc_4967_, 29, v_V_4952_);
lean_ctor_set(v_reuseFailAlloc_4967_, 30, v_z_4953_);
lean_ctor_set(v_reuseFailAlloc_4967_, 31, v_zabbrev_4954_);
lean_ctor_set(v_reuseFailAlloc_4967_, 32, v_v_4955_);
lean_ctor_set(v_reuseFailAlloc_4967_, 33, v_O_4956_);
lean_ctor_set(v_reuseFailAlloc_4967_, 34, v_X_4957_);
lean_ctor_set(v_reuseFailAlloc_4967_, 35, v_x_4958_);
lean_ctor_set(v_reuseFailAlloc_4967_, 36, v_Z_4959_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
case 8:
{
lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_5023_; 
v_isSharedCheck_5023_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5023_ == 0)
{
lean_object* v_unused_5024_; 
v_unused_5024_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5024_);
v___x_4974_ = v_modifier_4562_;
v_isShared_4975_ = v_isSharedCheck_5023_;
goto v_resetjp_4973_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_5023_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v_G_4976_; lean_object* v_y_4977_; lean_object* v_u_4978_; lean_object* v_Y_4979_; lean_object* v_D_4980_; lean_object* v_M_4981_; lean_object* v_L_4982_; lean_object* v_d_4983_; lean_object* v_Q_4984_; lean_object* v_w_4985_; lean_object* v_W_4986_; lean_object* v_E_4987_; lean_object* v_e_4988_; lean_object* v_c_4989_; lean_object* v_F_4990_; lean_object* v_a_4991_; lean_object* v_b_4992_; lean_object* v_B_4993_; lean_object* v_h_4994_; lean_object* v_K_4995_; lean_object* v_k_4996_; lean_object* v_H_4997_; lean_object* v_m_4998_; lean_object* v_s_4999_; lean_object* v_S_5000_; lean_object* v_A_5001_; lean_object* v_n_5002_; lean_object* v_N_5003_; lean_object* v_V_5004_; lean_object* v_z_5005_; lean_object* v_zabbrev_5006_; lean_object* v_v_5007_; lean_object* v_O_5008_; lean_object* v_X_5009_; lean_object* v_x_5010_; lean_object* v_Z_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5021_; 
v_G_4976_ = lean_ctor_get(v_date_4561_, 0);
v_y_4977_ = lean_ctor_get(v_date_4561_, 1);
v_u_4978_ = lean_ctor_get(v_date_4561_, 2);
v_Y_4979_ = lean_ctor_get(v_date_4561_, 3);
v_D_4980_ = lean_ctor_get(v_date_4561_, 4);
v_M_4981_ = lean_ctor_get(v_date_4561_, 5);
v_L_4982_ = lean_ctor_get(v_date_4561_, 6);
v_d_4983_ = lean_ctor_get(v_date_4561_, 7);
v_Q_4984_ = lean_ctor_get(v_date_4561_, 8);
v_w_4985_ = lean_ctor_get(v_date_4561_, 10);
v_W_4986_ = lean_ctor_get(v_date_4561_, 11);
v_E_4987_ = lean_ctor_get(v_date_4561_, 12);
v_e_4988_ = lean_ctor_get(v_date_4561_, 13);
v_c_4989_ = lean_ctor_get(v_date_4561_, 14);
v_F_4990_ = lean_ctor_get(v_date_4561_, 15);
v_a_4991_ = lean_ctor_get(v_date_4561_, 16);
v_b_4992_ = lean_ctor_get(v_date_4561_, 17);
v_B_4993_ = lean_ctor_get(v_date_4561_, 18);
v_h_4994_ = lean_ctor_get(v_date_4561_, 19);
v_K_4995_ = lean_ctor_get(v_date_4561_, 20);
v_k_4996_ = lean_ctor_get(v_date_4561_, 21);
v_H_4997_ = lean_ctor_get(v_date_4561_, 22);
v_m_4998_ = lean_ctor_get(v_date_4561_, 23);
v_s_4999_ = lean_ctor_get(v_date_4561_, 24);
v_S_5000_ = lean_ctor_get(v_date_4561_, 25);
v_A_5001_ = lean_ctor_get(v_date_4561_, 26);
v_n_5002_ = lean_ctor_get(v_date_4561_, 27);
v_N_5003_ = lean_ctor_get(v_date_4561_, 28);
v_V_5004_ = lean_ctor_get(v_date_4561_, 29);
v_z_5005_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5006_ = lean_ctor_get(v_date_4561_, 31);
v_v_5007_ = lean_ctor_get(v_date_4561_, 32);
v_O_5008_ = lean_ctor_get(v_date_4561_, 33);
v_X_5009_ = lean_ctor_get(v_date_4561_, 34);
v_x_5010_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5011_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5021_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5021_ == 0)
{
lean_object* v_unused_5022_; 
v_unused_5022_ = lean_ctor_get(v_date_4561_, 9);
lean_dec(v_unused_5022_);
v___x_5013_ = v_date_4561_;
v_isShared_5014_ = v_isSharedCheck_5021_;
goto v_resetjp_5012_;
}
else
{
lean_inc(v_Z_5011_);
lean_inc(v_x_5010_);
lean_inc(v_X_5009_);
lean_inc(v_O_5008_);
lean_inc(v_v_5007_);
lean_inc(v_zabbrev_5006_);
lean_inc(v_z_5005_);
lean_inc(v_V_5004_);
lean_inc(v_N_5003_);
lean_inc(v_n_5002_);
lean_inc(v_A_5001_);
lean_inc(v_S_5000_);
lean_inc(v_s_4999_);
lean_inc(v_m_4998_);
lean_inc(v_H_4997_);
lean_inc(v_k_4996_);
lean_inc(v_K_4995_);
lean_inc(v_h_4994_);
lean_inc(v_B_4993_);
lean_inc(v_b_4992_);
lean_inc(v_a_4991_);
lean_inc(v_F_4990_);
lean_inc(v_c_4989_);
lean_inc(v_e_4988_);
lean_inc(v_E_4987_);
lean_inc(v_W_4986_);
lean_inc(v_w_4985_);
lean_inc(v_Q_4984_);
lean_inc(v_d_4983_);
lean_inc(v_L_4982_);
lean_inc(v_M_4981_);
lean_inc(v_D_4980_);
lean_inc(v_Y_4979_);
lean_inc(v_u_4978_);
lean_inc(v_y_4977_);
lean_inc(v_G_4976_);
lean_dec(v_date_4561_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5021_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
lean_object* v___x_5016_; 
if (v_isShared_4975_ == 0)
{
lean_ctor_set_tag(v___x_4974_, 1);
lean_ctor_set(v___x_4974_, 0, v_data_4563_);
v___x_5016_ = v___x_4974_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_data_4563_);
v___x_5016_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
lean_object* v___x_5018_; 
if (v_isShared_5014_ == 0)
{
lean_ctor_set(v___x_5013_, 9, v___x_5016_);
v___x_5018_ = v___x_5013_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_G_4976_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v_y_4977_);
lean_ctor_set(v_reuseFailAlloc_5019_, 2, v_u_4978_);
lean_ctor_set(v_reuseFailAlloc_5019_, 3, v_Y_4979_);
lean_ctor_set(v_reuseFailAlloc_5019_, 4, v_D_4980_);
lean_ctor_set(v_reuseFailAlloc_5019_, 5, v_M_4981_);
lean_ctor_set(v_reuseFailAlloc_5019_, 6, v_L_4982_);
lean_ctor_set(v_reuseFailAlloc_5019_, 7, v_d_4983_);
lean_ctor_set(v_reuseFailAlloc_5019_, 8, v_Q_4984_);
lean_ctor_set(v_reuseFailAlloc_5019_, 9, v___x_5016_);
lean_ctor_set(v_reuseFailAlloc_5019_, 10, v_w_4985_);
lean_ctor_set(v_reuseFailAlloc_5019_, 11, v_W_4986_);
lean_ctor_set(v_reuseFailAlloc_5019_, 12, v_E_4987_);
lean_ctor_set(v_reuseFailAlloc_5019_, 13, v_e_4988_);
lean_ctor_set(v_reuseFailAlloc_5019_, 14, v_c_4989_);
lean_ctor_set(v_reuseFailAlloc_5019_, 15, v_F_4990_);
lean_ctor_set(v_reuseFailAlloc_5019_, 16, v_a_4991_);
lean_ctor_set(v_reuseFailAlloc_5019_, 17, v_b_4992_);
lean_ctor_set(v_reuseFailAlloc_5019_, 18, v_B_4993_);
lean_ctor_set(v_reuseFailAlloc_5019_, 19, v_h_4994_);
lean_ctor_set(v_reuseFailAlloc_5019_, 20, v_K_4995_);
lean_ctor_set(v_reuseFailAlloc_5019_, 21, v_k_4996_);
lean_ctor_set(v_reuseFailAlloc_5019_, 22, v_H_4997_);
lean_ctor_set(v_reuseFailAlloc_5019_, 23, v_m_4998_);
lean_ctor_set(v_reuseFailAlloc_5019_, 24, v_s_4999_);
lean_ctor_set(v_reuseFailAlloc_5019_, 25, v_S_5000_);
lean_ctor_set(v_reuseFailAlloc_5019_, 26, v_A_5001_);
lean_ctor_set(v_reuseFailAlloc_5019_, 27, v_n_5002_);
lean_ctor_set(v_reuseFailAlloc_5019_, 28, v_N_5003_);
lean_ctor_set(v_reuseFailAlloc_5019_, 29, v_V_5004_);
lean_ctor_set(v_reuseFailAlloc_5019_, 30, v_z_5005_);
lean_ctor_set(v_reuseFailAlloc_5019_, 31, v_zabbrev_5006_);
lean_ctor_set(v_reuseFailAlloc_5019_, 32, v_v_5007_);
lean_ctor_set(v_reuseFailAlloc_5019_, 33, v_O_5008_);
lean_ctor_set(v_reuseFailAlloc_5019_, 34, v_X_5009_);
lean_ctor_set(v_reuseFailAlloc_5019_, 35, v_x_5010_);
lean_ctor_set(v_reuseFailAlloc_5019_, 36, v_Z_5011_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
}
}
case 9:
{
lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5075_; 
v_isSharedCheck_5075_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5075_ == 0)
{
lean_object* v_unused_5076_; 
v_unused_5076_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5076_);
v___x_5026_ = v_modifier_4562_;
v_isShared_5027_ = v_isSharedCheck_5075_;
goto v_resetjp_5025_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5075_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v_G_5028_; lean_object* v_y_5029_; lean_object* v_u_5030_; lean_object* v_D_5031_; lean_object* v_M_5032_; lean_object* v_L_5033_; lean_object* v_d_5034_; lean_object* v_Q_5035_; lean_object* v_q_5036_; lean_object* v_w_5037_; lean_object* v_W_5038_; lean_object* v_E_5039_; lean_object* v_e_5040_; lean_object* v_c_5041_; lean_object* v_F_5042_; lean_object* v_a_5043_; lean_object* v_b_5044_; lean_object* v_B_5045_; lean_object* v_h_5046_; lean_object* v_K_5047_; lean_object* v_k_5048_; lean_object* v_H_5049_; lean_object* v_m_5050_; lean_object* v_s_5051_; lean_object* v_S_5052_; lean_object* v_A_5053_; lean_object* v_n_5054_; lean_object* v_N_5055_; lean_object* v_V_5056_; lean_object* v_z_5057_; lean_object* v_zabbrev_5058_; lean_object* v_v_5059_; lean_object* v_O_5060_; lean_object* v_X_5061_; lean_object* v_x_5062_; lean_object* v_Z_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5073_; 
v_G_5028_ = lean_ctor_get(v_date_4561_, 0);
v_y_5029_ = lean_ctor_get(v_date_4561_, 1);
v_u_5030_ = lean_ctor_get(v_date_4561_, 2);
v_D_5031_ = lean_ctor_get(v_date_4561_, 4);
v_M_5032_ = lean_ctor_get(v_date_4561_, 5);
v_L_5033_ = lean_ctor_get(v_date_4561_, 6);
v_d_5034_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5035_ = lean_ctor_get(v_date_4561_, 8);
v_q_5036_ = lean_ctor_get(v_date_4561_, 9);
v_w_5037_ = lean_ctor_get(v_date_4561_, 10);
v_W_5038_ = lean_ctor_get(v_date_4561_, 11);
v_E_5039_ = lean_ctor_get(v_date_4561_, 12);
v_e_5040_ = lean_ctor_get(v_date_4561_, 13);
v_c_5041_ = lean_ctor_get(v_date_4561_, 14);
v_F_5042_ = lean_ctor_get(v_date_4561_, 15);
v_a_5043_ = lean_ctor_get(v_date_4561_, 16);
v_b_5044_ = lean_ctor_get(v_date_4561_, 17);
v_B_5045_ = lean_ctor_get(v_date_4561_, 18);
v_h_5046_ = lean_ctor_get(v_date_4561_, 19);
v_K_5047_ = lean_ctor_get(v_date_4561_, 20);
v_k_5048_ = lean_ctor_get(v_date_4561_, 21);
v_H_5049_ = lean_ctor_get(v_date_4561_, 22);
v_m_5050_ = lean_ctor_get(v_date_4561_, 23);
v_s_5051_ = lean_ctor_get(v_date_4561_, 24);
v_S_5052_ = lean_ctor_get(v_date_4561_, 25);
v_A_5053_ = lean_ctor_get(v_date_4561_, 26);
v_n_5054_ = lean_ctor_get(v_date_4561_, 27);
v_N_5055_ = lean_ctor_get(v_date_4561_, 28);
v_V_5056_ = lean_ctor_get(v_date_4561_, 29);
v_z_5057_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5058_ = lean_ctor_get(v_date_4561_, 31);
v_v_5059_ = lean_ctor_get(v_date_4561_, 32);
v_O_5060_ = lean_ctor_get(v_date_4561_, 33);
v_X_5061_ = lean_ctor_get(v_date_4561_, 34);
v_x_5062_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5063_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5073_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5073_ == 0)
{
lean_object* v_unused_5074_; 
v_unused_5074_ = lean_ctor_get(v_date_4561_, 3);
lean_dec(v_unused_5074_);
v___x_5065_ = v_date_4561_;
v_isShared_5066_ = v_isSharedCheck_5073_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_Z_5063_);
lean_inc(v_x_5062_);
lean_inc(v_X_5061_);
lean_inc(v_O_5060_);
lean_inc(v_v_5059_);
lean_inc(v_zabbrev_5058_);
lean_inc(v_z_5057_);
lean_inc(v_V_5056_);
lean_inc(v_N_5055_);
lean_inc(v_n_5054_);
lean_inc(v_A_5053_);
lean_inc(v_S_5052_);
lean_inc(v_s_5051_);
lean_inc(v_m_5050_);
lean_inc(v_H_5049_);
lean_inc(v_k_5048_);
lean_inc(v_K_5047_);
lean_inc(v_h_5046_);
lean_inc(v_B_5045_);
lean_inc(v_b_5044_);
lean_inc(v_a_5043_);
lean_inc(v_F_5042_);
lean_inc(v_c_5041_);
lean_inc(v_e_5040_);
lean_inc(v_E_5039_);
lean_inc(v_W_5038_);
lean_inc(v_w_5037_);
lean_inc(v_q_5036_);
lean_inc(v_Q_5035_);
lean_inc(v_d_5034_);
lean_inc(v_L_5033_);
lean_inc(v_M_5032_);
lean_inc(v_D_5031_);
lean_inc(v_u_5030_);
lean_inc(v_y_5029_);
lean_inc(v_G_5028_);
lean_dec(v_date_4561_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5073_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5068_; 
if (v_isShared_5027_ == 0)
{
lean_ctor_set_tag(v___x_5026_, 1);
lean_ctor_set(v___x_5026_, 0, v_data_4563_);
v___x_5068_ = v___x_5026_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_data_4563_);
v___x_5068_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
lean_object* v___x_5070_; 
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 3, v___x_5068_);
v___x_5070_ = v___x_5065_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_G_5028_);
lean_ctor_set(v_reuseFailAlloc_5071_, 1, v_y_5029_);
lean_ctor_set(v_reuseFailAlloc_5071_, 2, v_u_5030_);
lean_ctor_set(v_reuseFailAlloc_5071_, 3, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5071_, 4, v_D_5031_);
lean_ctor_set(v_reuseFailAlloc_5071_, 5, v_M_5032_);
lean_ctor_set(v_reuseFailAlloc_5071_, 6, v_L_5033_);
lean_ctor_set(v_reuseFailAlloc_5071_, 7, v_d_5034_);
lean_ctor_set(v_reuseFailAlloc_5071_, 8, v_Q_5035_);
lean_ctor_set(v_reuseFailAlloc_5071_, 9, v_q_5036_);
lean_ctor_set(v_reuseFailAlloc_5071_, 10, v_w_5037_);
lean_ctor_set(v_reuseFailAlloc_5071_, 11, v_W_5038_);
lean_ctor_set(v_reuseFailAlloc_5071_, 12, v_E_5039_);
lean_ctor_set(v_reuseFailAlloc_5071_, 13, v_e_5040_);
lean_ctor_set(v_reuseFailAlloc_5071_, 14, v_c_5041_);
lean_ctor_set(v_reuseFailAlloc_5071_, 15, v_F_5042_);
lean_ctor_set(v_reuseFailAlloc_5071_, 16, v_a_5043_);
lean_ctor_set(v_reuseFailAlloc_5071_, 17, v_b_5044_);
lean_ctor_set(v_reuseFailAlloc_5071_, 18, v_B_5045_);
lean_ctor_set(v_reuseFailAlloc_5071_, 19, v_h_5046_);
lean_ctor_set(v_reuseFailAlloc_5071_, 20, v_K_5047_);
lean_ctor_set(v_reuseFailAlloc_5071_, 21, v_k_5048_);
lean_ctor_set(v_reuseFailAlloc_5071_, 22, v_H_5049_);
lean_ctor_set(v_reuseFailAlloc_5071_, 23, v_m_5050_);
lean_ctor_set(v_reuseFailAlloc_5071_, 24, v_s_5051_);
lean_ctor_set(v_reuseFailAlloc_5071_, 25, v_S_5052_);
lean_ctor_set(v_reuseFailAlloc_5071_, 26, v_A_5053_);
lean_ctor_set(v_reuseFailAlloc_5071_, 27, v_n_5054_);
lean_ctor_set(v_reuseFailAlloc_5071_, 28, v_N_5055_);
lean_ctor_set(v_reuseFailAlloc_5071_, 29, v_V_5056_);
lean_ctor_set(v_reuseFailAlloc_5071_, 30, v_z_5057_);
lean_ctor_set(v_reuseFailAlloc_5071_, 31, v_zabbrev_5058_);
lean_ctor_set(v_reuseFailAlloc_5071_, 32, v_v_5059_);
lean_ctor_set(v_reuseFailAlloc_5071_, 33, v_O_5060_);
lean_ctor_set(v_reuseFailAlloc_5071_, 34, v_X_5061_);
lean_ctor_set(v_reuseFailAlloc_5071_, 35, v_x_5062_);
lean_ctor_set(v_reuseFailAlloc_5071_, 36, v_Z_5063_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
}
case 10:
{
lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5127_; 
v_isSharedCheck_5127_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5127_ == 0)
{
lean_object* v_unused_5128_; 
v_unused_5128_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5128_);
v___x_5078_ = v_modifier_4562_;
v_isShared_5079_ = v_isSharedCheck_5127_;
goto v_resetjp_5077_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5127_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v_G_5080_; lean_object* v_y_5081_; lean_object* v_u_5082_; lean_object* v_Y_5083_; lean_object* v_D_5084_; lean_object* v_M_5085_; lean_object* v_L_5086_; lean_object* v_d_5087_; lean_object* v_Q_5088_; lean_object* v_q_5089_; lean_object* v_W_5090_; lean_object* v_E_5091_; lean_object* v_e_5092_; lean_object* v_c_5093_; lean_object* v_F_5094_; lean_object* v_a_5095_; lean_object* v_b_5096_; lean_object* v_B_5097_; lean_object* v_h_5098_; lean_object* v_K_5099_; lean_object* v_k_5100_; lean_object* v_H_5101_; lean_object* v_m_5102_; lean_object* v_s_5103_; lean_object* v_S_5104_; lean_object* v_A_5105_; lean_object* v_n_5106_; lean_object* v_N_5107_; lean_object* v_V_5108_; lean_object* v_z_5109_; lean_object* v_zabbrev_5110_; lean_object* v_v_5111_; lean_object* v_O_5112_; lean_object* v_X_5113_; lean_object* v_x_5114_; lean_object* v_Z_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5125_; 
v_G_5080_ = lean_ctor_get(v_date_4561_, 0);
v_y_5081_ = lean_ctor_get(v_date_4561_, 1);
v_u_5082_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5083_ = lean_ctor_get(v_date_4561_, 3);
v_D_5084_ = lean_ctor_get(v_date_4561_, 4);
v_M_5085_ = lean_ctor_get(v_date_4561_, 5);
v_L_5086_ = lean_ctor_get(v_date_4561_, 6);
v_d_5087_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5088_ = lean_ctor_get(v_date_4561_, 8);
v_q_5089_ = lean_ctor_get(v_date_4561_, 9);
v_W_5090_ = lean_ctor_get(v_date_4561_, 11);
v_E_5091_ = lean_ctor_get(v_date_4561_, 12);
v_e_5092_ = lean_ctor_get(v_date_4561_, 13);
v_c_5093_ = lean_ctor_get(v_date_4561_, 14);
v_F_5094_ = lean_ctor_get(v_date_4561_, 15);
v_a_5095_ = lean_ctor_get(v_date_4561_, 16);
v_b_5096_ = lean_ctor_get(v_date_4561_, 17);
v_B_5097_ = lean_ctor_get(v_date_4561_, 18);
v_h_5098_ = lean_ctor_get(v_date_4561_, 19);
v_K_5099_ = lean_ctor_get(v_date_4561_, 20);
v_k_5100_ = lean_ctor_get(v_date_4561_, 21);
v_H_5101_ = lean_ctor_get(v_date_4561_, 22);
v_m_5102_ = lean_ctor_get(v_date_4561_, 23);
v_s_5103_ = lean_ctor_get(v_date_4561_, 24);
v_S_5104_ = lean_ctor_get(v_date_4561_, 25);
v_A_5105_ = lean_ctor_get(v_date_4561_, 26);
v_n_5106_ = lean_ctor_get(v_date_4561_, 27);
v_N_5107_ = lean_ctor_get(v_date_4561_, 28);
v_V_5108_ = lean_ctor_get(v_date_4561_, 29);
v_z_5109_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5110_ = lean_ctor_get(v_date_4561_, 31);
v_v_5111_ = lean_ctor_get(v_date_4561_, 32);
v_O_5112_ = lean_ctor_get(v_date_4561_, 33);
v_X_5113_ = lean_ctor_get(v_date_4561_, 34);
v_x_5114_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5115_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5125_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5125_ == 0)
{
lean_object* v_unused_5126_; 
v_unused_5126_ = lean_ctor_get(v_date_4561_, 10);
lean_dec(v_unused_5126_);
v___x_5117_ = v_date_4561_;
v_isShared_5118_ = v_isSharedCheck_5125_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_Z_5115_);
lean_inc(v_x_5114_);
lean_inc(v_X_5113_);
lean_inc(v_O_5112_);
lean_inc(v_v_5111_);
lean_inc(v_zabbrev_5110_);
lean_inc(v_z_5109_);
lean_inc(v_V_5108_);
lean_inc(v_N_5107_);
lean_inc(v_n_5106_);
lean_inc(v_A_5105_);
lean_inc(v_S_5104_);
lean_inc(v_s_5103_);
lean_inc(v_m_5102_);
lean_inc(v_H_5101_);
lean_inc(v_k_5100_);
lean_inc(v_K_5099_);
lean_inc(v_h_5098_);
lean_inc(v_B_5097_);
lean_inc(v_b_5096_);
lean_inc(v_a_5095_);
lean_inc(v_F_5094_);
lean_inc(v_c_5093_);
lean_inc(v_e_5092_);
lean_inc(v_E_5091_);
lean_inc(v_W_5090_);
lean_inc(v_q_5089_);
lean_inc(v_Q_5088_);
lean_inc(v_d_5087_);
lean_inc(v_L_5086_);
lean_inc(v_M_5085_);
lean_inc(v_D_5084_);
lean_inc(v_Y_5083_);
lean_inc(v_u_5082_);
lean_inc(v_y_5081_);
lean_inc(v_G_5080_);
lean_dec(v_date_4561_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5125_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5079_ == 0)
{
lean_ctor_set_tag(v___x_5078_, 1);
lean_ctor_set(v___x_5078_, 0, v_data_4563_);
v___x_5120_ = v___x_5078_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_data_4563_);
v___x_5120_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
lean_object* v___x_5122_; 
if (v_isShared_5118_ == 0)
{
lean_ctor_set(v___x_5117_, 10, v___x_5120_);
v___x_5122_ = v___x_5117_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v_G_5080_);
lean_ctor_set(v_reuseFailAlloc_5123_, 1, v_y_5081_);
lean_ctor_set(v_reuseFailAlloc_5123_, 2, v_u_5082_);
lean_ctor_set(v_reuseFailAlloc_5123_, 3, v_Y_5083_);
lean_ctor_set(v_reuseFailAlloc_5123_, 4, v_D_5084_);
lean_ctor_set(v_reuseFailAlloc_5123_, 5, v_M_5085_);
lean_ctor_set(v_reuseFailAlloc_5123_, 6, v_L_5086_);
lean_ctor_set(v_reuseFailAlloc_5123_, 7, v_d_5087_);
lean_ctor_set(v_reuseFailAlloc_5123_, 8, v_Q_5088_);
lean_ctor_set(v_reuseFailAlloc_5123_, 9, v_q_5089_);
lean_ctor_set(v_reuseFailAlloc_5123_, 10, v___x_5120_);
lean_ctor_set(v_reuseFailAlloc_5123_, 11, v_W_5090_);
lean_ctor_set(v_reuseFailAlloc_5123_, 12, v_E_5091_);
lean_ctor_set(v_reuseFailAlloc_5123_, 13, v_e_5092_);
lean_ctor_set(v_reuseFailAlloc_5123_, 14, v_c_5093_);
lean_ctor_set(v_reuseFailAlloc_5123_, 15, v_F_5094_);
lean_ctor_set(v_reuseFailAlloc_5123_, 16, v_a_5095_);
lean_ctor_set(v_reuseFailAlloc_5123_, 17, v_b_5096_);
lean_ctor_set(v_reuseFailAlloc_5123_, 18, v_B_5097_);
lean_ctor_set(v_reuseFailAlloc_5123_, 19, v_h_5098_);
lean_ctor_set(v_reuseFailAlloc_5123_, 20, v_K_5099_);
lean_ctor_set(v_reuseFailAlloc_5123_, 21, v_k_5100_);
lean_ctor_set(v_reuseFailAlloc_5123_, 22, v_H_5101_);
lean_ctor_set(v_reuseFailAlloc_5123_, 23, v_m_5102_);
lean_ctor_set(v_reuseFailAlloc_5123_, 24, v_s_5103_);
lean_ctor_set(v_reuseFailAlloc_5123_, 25, v_S_5104_);
lean_ctor_set(v_reuseFailAlloc_5123_, 26, v_A_5105_);
lean_ctor_set(v_reuseFailAlloc_5123_, 27, v_n_5106_);
lean_ctor_set(v_reuseFailAlloc_5123_, 28, v_N_5107_);
lean_ctor_set(v_reuseFailAlloc_5123_, 29, v_V_5108_);
lean_ctor_set(v_reuseFailAlloc_5123_, 30, v_z_5109_);
lean_ctor_set(v_reuseFailAlloc_5123_, 31, v_zabbrev_5110_);
lean_ctor_set(v_reuseFailAlloc_5123_, 32, v_v_5111_);
lean_ctor_set(v_reuseFailAlloc_5123_, 33, v_O_5112_);
lean_ctor_set(v_reuseFailAlloc_5123_, 34, v_X_5113_);
lean_ctor_set(v_reuseFailAlloc_5123_, 35, v_x_5114_);
lean_ctor_set(v_reuseFailAlloc_5123_, 36, v_Z_5115_);
v___x_5122_ = v_reuseFailAlloc_5123_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
return v___x_5122_;
}
}
}
}
}
case 11:
{
lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5179_; 
v_isSharedCheck_5179_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5179_ == 0)
{
lean_object* v_unused_5180_; 
v_unused_5180_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5180_);
v___x_5130_ = v_modifier_4562_;
v_isShared_5131_ = v_isSharedCheck_5179_;
goto v_resetjp_5129_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5179_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v_G_5132_; lean_object* v_y_5133_; lean_object* v_u_5134_; lean_object* v_Y_5135_; lean_object* v_D_5136_; lean_object* v_M_5137_; lean_object* v_L_5138_; lean_object* v_d_5139_; lean_object* v_Q_5140_; lean_object* v_q_5141_; lean_object* v_w_5142_; lean_object* v_E_5143_; lean_object* v_e_5144_; lean_object* v_c_5145_; lean_object* v_F_5146_; lean_object* v_a_5147_; lean_object* v_b_5148_; lean_object* v_B_5149_; lean_object* v_h_5150_; lean_object* v_K_5151_; lean_object* v_k_5152_; lean_object* v_H_5153_; lean_object* v_m_5154_; lean_object* v_s_5155_; lean_object* v_S_5156_; lean_object* v_A_5157_; lean_object* v_n_5158_; lean_object* v_N_5159_; lean_object* v_V_5160_; lean_object* v_z_5161_; lean_object* v_zabbrev_5162_; lean_object* v_v_5163_; lean_object* v_O_5164_; lean_object* v_X_5165_; lean_object* v_x_5166_; lean_object* v_Z_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5177_; 
v_G_5132_ = lean_ctor_get(v_date_4561_, 0);
v_y_5133_ = lean_ctor_get(v_date_4561_, 1);
v_u_5134_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5135_ = lean_ctor_get(v_date_4561_, 3);
v_D_5136_ = lean_ctor_get(v_date_4561_, 4);
v_M_5137_ = lean_ctor_get(v_date_4561_, 5);
v_L_5138_ = lean_ctor_get(v_date_4561_, 6);
v_d_5139_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5140_ = lean_ctor_get(v_date_4561_, 8);
v_q_5141_ = lean_ctor_get(v_date_4561_, 9);
v_w_5142_ = lean_ctor_get(v_date_4561_, 10);
v_E_5143_ = lean_ctor_get(v_date_4561_, 12);
v_e_5144_ = lean_ctor_get(v_date_4561_, 13);
v_c_5145_ = lean_ctor_get(v_date_4561_, 14);
v_F_5146_ = lean_ctor_get(v_date_4561_, 15);
v_a_5147_ = lean_ctor_get(v_date_4561_, 16);
v_b_5148_ = lean_ctor_get(v_date_4561_, 17);
v_B_5149_ = lean_ctor_get(v_date_4561_, 18);
v_h_5150_ = lean_ctor_get(v_date_4561_, 19);
v_K_5151_ = lean_ctor_get(v_date_4561_, 20);
v_k_5152_ = lean_ctor_get(v_date_4561_, 21);
v_H_5153_ = lean_ctor_get(v_date_4561_, 22);
v_m_5154_ = lean_ctor_get(v_date_4561_, 23);
v_s_5155_ = lean_ctor_get(v_date_4561_, 24);
v_S_5156_ = lean_ctor_get(v_date_4561_, 25);
v_A_5157_ = lean_ctor_get(v_date_4561_, 26);
v_n_5158_ = lean_ctor_get(v_date_4561_, 27);
v_N_5159_ = lean_ctor_get(v_date_4561_, 28);
v_V_5160_ = lean_ctor_get(v_date_4561_, 29);
v_z_5161_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5162_ = lean_ctor_get(v_date_4561_, 31);
v_v_5163_ = lean_ctor_get(v_date_4561_, 32);
v_O_5164_ = lean_ctor_get(v_date_4561_, 33);
v_X_5165_ = lean_ctor_get(v_date_4561_, 34);
v_x_5166_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5167_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5177_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5177_ == 0)
{
lean_object* v_unused_5178_; 
v_unused_5178_ = lean_ctor_get(v_date_4561_, 11);
lean_dec(v_unused_5178_);
v___x_5169_ = v_date_4561_;
v_isShared_5170_ = v_isSharedCheck_5177_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_Z_5167_);
lean_inc(v_x_5166_);
lean_inc(v_X_5165_);
lean_inc(v_O_5164_);
lean_inc(v_v_5163_);
lean_inc(v_zabbrev_5162_);
lean_inc(v_z_5161_);
lean_inc(v_V_5160_);
lean_inc(v_N_5159_);
lean_inc(v_n_5158_);
lean_inc(v_A_5157_);
lean_inc(v_S_5156_);
lean_inc(v_s_5155_);
lean_inc(v_m_5154_);
lean_inc(v_H_5153_);
lean_inc(v_k_5152_);
lean_inc(v_K_5151_);
lean_inc(v_h_5150_);
lean_inc(v_B_5149_);
lean_inc(v_b_5148_);
lean_inc(v_a_5147_);
lean_inc(v_F_5146_);
lean_inc(v_c_5145_);
lean_inc(v_e_5144_);
lean_inc(v_E_5143_);
lean_inc(v_w_5142_);
lean_inc(v_q_5141_);
lean_inc(v_Q_5140_);
lean_inc(v_d_5139_);
lean_inc(v_L_5138_);
lean_inc(v_M_5137_);
lean_inc(v_D_5136_);
lean_inc(v_Y_5135_);
lean_inc(v_u_5134_);
lean_inc(v_y_5133_);
lean_inc(v_G_5132_);
lean_dec(v_date_4561_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5177_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5172_; 
if (v_isShared_5131_ == 0)
{
lean_ctor_set_tag(v___x_5130_, 1);
lean_ctor_set(v___x_5130_, 0, v_data_4563_);
v___x_5172_ = v___x_5130_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_data_4563_);
v___x_5172_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
lean_object* v___x_5174_; 
if (v_isShared_5170_ == 0)
{
lean_ctor_set(v___x_5169_, 11, v___x_5172_);
v___x_5174_ = v___x_5169_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_G_5132_);
lean_ctor_set(v_reuseFailAlloc_5175_, 1, v_y_5133_);
lean_ctor_set(v_reuseFailAlloc_5175_, 2, v_u_5134_);
lean_ctor_set(v_reuseFailAlloc_5175_, 3, v_Y_5135_);
lean_ctor_set(v_reuseFailAlloc_5175_, 4, v_D_5136_);
lean_ctor_set(v_reuseFailAlloc_5175_, 5, v_M_5137_);
lean_ctor_set(v_reuseFailAlloc_5175_, 6, v_L_5138_);
lean_ctor_set(v_reuseFailAlloc_5175_, 7, v_d_5139_);
lean_ctor_set(v_reuseFailAlloc_5175_, 8, v_Q_5140_);
lean_ctor_set(v_reuseFailAlloc_5175_, 9, v_q_5141_);
lean_ctor_set(v_reuseFailAlloc_5175_, 10, v_w_5142_);
lean_ctor_set(v_reuseFailAlloc_5175_, 11, v___x_5172_);
lean_ctor_set(v_reuseFailAlloc_5175_, 12, v_E_5143_);
lean_ctor_set(v_reuseFailAlloc_5175_, 13, v_e_5144_);
lean_ctor_set(v_reuseFailAlloc_5175_, 14, v_c_5145_);
lean_ctor_set(v_reuseFailAlloc_5175_, 15, v_F_5146_);
lean_ctor_set(v_reuseFailAlloc_5175_, 16, v_a_5147_);
lean_ctor_set(v_reuseFailAlloc_5175_, 17, v_b_5148_);
lean_ctor_set(v_reuseFailAlloc_5175_, 18, v_B_5149_);
lean_ctor_set(v_reuseFailAlloc_5175_, 19, v_h_5150_);
lean_ctor_set(v_reuseFailAlloc_5175_, 20, v_K_5151_);
lean_ctor_set(v_reuseFailAlloc_5175_, 21, v_k_5152_);
lean_ctor_set(v_reuseFailAlloc_5175_, 22, v_H_5153_);
lean_ctor_set(v_reuseFailAlloc_5175_, 23, v_m_5154_);
lean_ctor_set(v_reuseFailAlloc_5175_, 24, v_s_5155_);
lean_ctor_set(v_reuseFailAlloc_5175_, 25, v_S_5156_);
lean_ctor_set(v_reuseFailAlloc_5175_, 26, v_A_5157_);
lean_ctor_set(v_reuseFailAlloc_5175_, 27, v_n_5158_);
lean_ctor_set(v_reuseFailAlloc_5175_, 28, v_N_5159_);
lean_ctor_set(v_reuseFailAlloc_5175_, 29, v_V_5160_);
lean_ctor_set(v_reuseFailAlloc_5175_, 30, v_z_5161_);
lean_ctor_set(v_reuseFailAlloc_5175_, 31, v_zabbrev_5162_);
lean_ctor_set(v_reuseFailAlloc_5175_, 32, v_v_5163_);
lean_ctor_set(v_reuseFailAlloc_5175_, 33, v_O_5164_);
lean_ctor_set(v_reuseFailAlloc_5175_, 34, v_X_5165_);
lean_ctor_set(v_reuseFailAlloc_5175_, 35, v_x_5166_);
lean_ctor_set(v_reuseFailAlloc_5175_, 36, v_Z_5167_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
}
case 12:
{
lean_object* v_G_5181_; lean_object* v_y_5182_; lean_object* v_u_5183_; lean_object* v_Y_5184_; lean_object* v_D_5185_; lean_object* v_M_5186_; lean_object* v_L_5187_; lean_object* v_d_5188_; lean_object* v_Q_5189_; lean_object* v_q_5190_; lean_object* v_w_5191_; lean_object* v_W_5192_; lean_object* v_e_5193_; lean_object* v_c_5194_; lean_object* v_F_5195_; lean_object* v_a_5196_; lean_object* v_b_5197_; lean_object* v_B_5198_; lean_object* v_h_5199_; lean_object* v_K_5200_; lean_object* v_k_5201_; lean_object* v_H_5202_; lean_object* v_m_5203_; lean_object* v_s_5204_; lean_object* v_S_5205_; lean_object* v_A_5206_; lean_object* v_n_5207_; lean_object* v_N_5208_; lean_object* v_V_5209_; lean_object* v_z_5210_; lean_object* v_zabbrev_5211_; lean_object* v_v_5212_; lean_object* v_O_5213_; lean_object* v_X_5214_; lean_object* v_x_5215_; lean_object* v_Z_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5224_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_G_5181_ = lean_ctor_get(v_date_4561_, 0);
v_y_5182_ = lean_ctor_get(v_date_4561_, 1);
v_u_5183_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5184_ = lean_ctor_get(v_date_4561_, 3);
v_D_5185_ = lean_ctor_get(v_date_4561_, 4);
v_M_5186_ = lean_ctor_get(v_date_4561_, 5);
v_L_5187_ = lean_ctor_get(v_date_4561_, 6);
v_d_5188_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5189_ = lean_ctor_get(v_date_4561_, 8);
v_q_5190_ = lean_ctor_get(v_date_4561_, 9);
v_w_5191_ = lean_ctor_get(v_date_4561_, 10);
v_W_5192_ = lean_ctor_get(v_date_4561_, 11);
v_e_5193_ = lean_ctor_get(v_date_4561_, 13);
v_c_5194_ = lean_ctor_get(v_date_4561_, 14);
v_F_5195_ = lean_ctor_get(v_date_4561_, 15);
v_a_5196_ = lean_ctor_get(v_date_4561_, 16);
v_b_5197_ = lean_ctor_get(v_date_4561_, 17);
v_B_5198_ = lean_ctor_get(v_date_4561_, 18);
v_h_5199_ = lean_ctor_get(v_date_4561_, 19);
v_K_5200_ = lean_ctor_get(v_date_4561_, 20);
v_k_5201_ = lean_ctor_get(v_date_4561_, 21);
v_H_5202_ = lean_ctor_get(v_date_4561_, 22);
v_m_5203_ = lean_ctor_get(v_date_4561_, 23);
v_s_5204_ = lean_ctor_get(v_date_4561_, 24);
v_S_5205_ = lean_ctor_get(v_date_4561_, 25);
v_A_5206_ = lean_ctor_get(v_date_4561_, 26);
v_n_5207_ = lean_ctor_get(v_date_4561_, 27);
v_N_5208_ = lean_ctor_get(v_date_4561_, 28);
v_V_5209_ = lean_ctor_get(v_date_4561_, 29);
v_z_5210_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5211_ = lean_ctor_get(v_date_4561_, 31);
v_v_5212_ = lean_ctor_get(v_date_4561_, 32);
v_O_5213_ = lean_ctor_get(v_date_4561_, 33);
v_X_5214_ = lean_ctor_get(v_date_4561_, 34);
v_x_5215_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5216_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5224_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5224_ == 0)
{
lean_object* v_unused_5225_; 
v_unused_5225_ = lean_ctor_get(v_date_4561_, 12);
lean_dec(v_unused_5225_);
v___x_5218_ = v_date_4561_;
v_isShared_5219_ = v_isSharedCheck_5224_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_Z_5216_);
lean_inc(v_x_5215_);
lean_inc(v_X_5214_);
lean_inc(v_O_5213_);
lean_inc(v_v_5212_);
lean_inc(v_zabbrev_5211_);
lean_inc(v_z_5210_);
lean_inc(v_V_5209_);
lean_inc(v_N_5208_);
lean_inc(v_n_5207_);
lean_inc(v_A_5206_);
lean_inc(v_S_5205_);
lean_inc(v_s_5204_);
lean_inc(v_m_5203_);
lean_inc(v_H_5202_);
lean_inc(v_k_5201_);
lean_inc(v_K_5200_);
lean_inc(v_h_5199_);
lean_inc(v_B_5198_);
lean_inc(v_b_5197_);
lean_inc(v_a_5196_);
lean_inc(v_F_5195_);
lean_inc(v_c_5194_);
lean_inc(v_e_5193_);
lean_inc(v_W_5192_);
lean_inc(v_w_5191_);
lean_inc(v_q_5190_);
lean_inc(v_Q_5189_);
lean_inc(v_d_5188_);
lean_inc(v_L_5187_);
lean_inc(v_M_5186_);
lean_inc(v_D_5185_);
lean_inc(v_Y_5184_);
lean_inc(v_u_5183_);
lean_inc(v_y_5182_);
lean_inc(v_G_5181_);
lean_dec(v_date_4561_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5224_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5220_; lean_object* v___x_5222_; 
v___x_5220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5220_, 0, v_data_4563_);
if (v_isShared_5219_ == 0)
{
lean_ctor_set(v___x_5218_, 12, v___x_5220_);
v___x_5222_ = v___x_5218_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_G_5181_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v_y_5182_);
lean_ctor_set(v_reuseFailAlloc_5223_, 2, v_u_5183_);
lean_ctor_set(v_reuseFailAlloc_5223_, 3, v_Y_5184_);
lean_ctor_set(v_reuseFailAlloc_5223_, 4, v_D_5185_);
lean_ctor_set(v_reuseFailAlloc_5223_, 5, v_M_5186_);
lean_ctor_set(v_reuseFailAlloc_5223_, 6, v_L_5187_);
lean_ctor_set(v_reuseFailAlloc_5223_, 7, v_d_5188_);
lean_ctor_set(v_reuseFailAlloc_5223_, 8, v_Q_5189_);
lean_ctor_set(v_reuseFailAlloc_5223_, 9, v_q_5190_);
lean_ctor_set(v_reuseFailAlloc_5223_, 10, v_w_5191_);
lean_ctor_set(v_reuseFailAlloc_5223_, 11, v_W_5192_);
lean_ctor_set(v_reuseFailAlloc_5223_, 12, v___x_5220_);
lean_ctor_set(v_reuseFailAlloc_5223_, 13, v_e_5193_);
lean_ctor_set(v_reuseFailAlloc_5223_, 14, v_c_5194_);
lean_ctor_set(v_reuseFailAlloc_5223_, 15, v_F_5195_);
lean_ctor_set(v_reuseFailAlloc_5223_, 16, v_a_5196_);
lean_ctor_set(v_reuseFailAlloc_5223_, 17, v_b_5197_);
lean_ctor_set(v_reuseFailAlloc_5223_, 18, v_B_5198_);
lean_ctor_set(v_reuseFailAlloc_5223_, 19, v_h_5199_);
lean_ctor_set(v_reuseFailAlloc_5223_, 20, v_K_5200_);
lean_ctor_set(v_reuseFailAlloc_5223_, 21, v_k_5201_);
lean_ctor_set(v_reuseFailAlloc_5223_, 22, v_H_5202_);
lean_ctor_set(v_reuseFailAlloc_5223_, 23, v_m_5203_);
lean_ctor_set(v_reuseFailAlloc_5223_, 24, v_s_5204_);
lean_ctor_set(v_reuseFailAlloc_5223_, 25, v_S_5205_);
lean_ctor_set(v_reuseFailAlloc_5223_, 26, v_A_5206_);
lean_ctor_set(v_reuseFailAlloc_5223_, 27, v_n_5207_);
lean_ctor_set(v_reuseFailAlloc_5223_, 28, v_N_5208_);
lean_ctor_set(v_reuseFailAlloc_5223_, 29, v_V_5209_);
lean_ctor_set(v_reuseFailAlloc_5223_, 30, v_z_5210_);
lean_ctor_set(v_reuseFailAlloc_5223_, 31, v_zabbrev_5211_);
lean_ctor_set(v_reuseFailAlloc_5223_, 32, v_v_5212_);
lean_ctor_set(v_reuseFailAlloc_5223_, 33, v_O_5213_);
lean_ctor_set(v_reuseFailAlloc_5223_, 34, v_X_5214_);
lean_ctor_set(v_reuseFailAlloc_5223_, 35, v_x_5215_);
lean_ctor_set(v_reuseFailAlloc_5223_, 36, v_Z_5216_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
case 13:
{
lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5276_; 
v_isSharedCheck_5276_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5276_ == 0)
{
lean_object* v_unused_5277_; 
v_unused_5277_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5277_);
v___x_5227_ = v_modifier_4562_;
v_isShared_5228_ = v_isSharedCheck_5276_;
goto v_resetjp_5226_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5276_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v_G_5229_; lean_object* v_y_5230_; lean_object* v_u_5231_; lean_object* v_Y_5232_; lean_object* v_D_5233_; lean_object* v_M_5234_; lean_object* v_L_5235_; lean_object* v_d_5236_; lean_object* v_Q_5237_; lean_object* v_q_5238_; lean_object* v_w_5239_; lean_object* v_W_5240_; lean_object* v_E_5241_; lean_object* v_c_5242_; lean_object* v_F_5243_; lean_object* v_a_5244_; lean_object* v_b_5245_; lean_object* v_B_5246_; lean_object* v_h_5247_; lean_object* v_K_5248_; lean_object* v_k_5249_; lean_object* v_H_5250_; lean_object* v_m_5251_; lean_object* v_s_5252_; lean_object* v_S_5253_; lean_object* v_A_5254_; lean_object* v_n_5255_; lean_object* v_N_5256_; lean_object* v_V_5257_; lean_object* v_z_5258_; lean_object* v_zabbrev_5259_; lean_object* v_v_5260_; lean_object* v_O_5261_; lean_object* v_X_5262_; lean_object* v_x_5263_; lean_object* v_Z_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5274_; 
v_G_5229_ = lean_ctor_get(v_date_4561_, 0);
v_y_5230_ = lean_ctor_get(v_date_4561_, 1);
v_u_5231_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5232_ = lean_ctor_get(v_date_4561_, 3);
v_D_5233_ = lean_ctor_get(v_date_4561_, 4);
v_M_5234_ = lean_ctor_get(v_date_4561_, 5);
v_L_5235_ = lean_ctor_get(v_date_4561_, 6);
v_d_5236_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5237_ = lean_ctor_get(v_date_4561_, 8);
v_q_5238_ = lean_ctor_get(v_date_4561_, 9);
v_w_5239_ = lean_ctor_get(v_date_4561_, 10);
v_W_5240_ = lean_ctor_get(v_date_4561_, 11);
v_E_5241_ = lean_ctor_get(v_date_4561_, 12);
v_c_5242_ = lean_ctor_get(v_date_4561_, 14);
v_F_5243_ = lean_ctor_get(v_date_4561_, 15);
v_a_5244_ = lean_ctor_get(v_date_4561_, 16);
v_b_5245_ = lean_ctor_get(v_date_4561_, 17);
v_B_5246_ = lean_ctor_get(v_date_4561_, 18);
v_h_5247_ = lean_ctor_get(v_date_4561_, 19);
v_K_5248_ = lean_ctor_get(v_date_4561_, 20);
v_k_5249_ = lean_ctor_get(v_date_4561_, 21);
v_H_5250_ = lean_ctor_get(v_date_4561_, 22);
v_m_5251_ = lean_ctor_get(v_date_4561_, 23);
v_s_5252_ = lean_ctor_get(v_date_4561_, 24);
v_S_5253_ = lean_ctor_get(v_date_4561_, 25);
v_A_5254_ = lean_ctor_get(v_date_4561_, 26);
v_n_5255_ = lean_ctor_get(v_date_4561_, 27);
v_N_5256_ = lean_ctor_get(v_date_4561_, 28);
v_V_5257_ = lean_ctor_get(v_date_4561_, 29);
v_z_5258_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5259_ = lean_ctor_get(v_date_4561_, 31);
v_v_5260_ = lean_ctor_get(v_date_4561_, 32);
v_O_5261_ = lean_ctor_get(v_date_4561_, 33);
v_X_5262_ = lean_ctor_get(v_date_4561_, 34);
v_x_5263_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5264_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5274_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5274_ == 0)
{
lean_object* v_unused_5275_; 
v_unused_5275_ = lean_ctor_get(v_date_4561_, 13);
lean_dec(v_unused_5275_);
v___x_5266_ = v_date_4561_;
v_isShared_5267_ = v_isSharedCheck_5274_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_Z_5264_);
lean_inc(v_x_5263_);
lean_inc(v_X_5262_);
lean_inc(v_O_5261_);
lean_inc(v_v_5260_);
lean_inc(v_zabbrev_5259_);
lean_inc(v_z_5258_);
lean_inc(v_V_5257_);
lean_inc(v_N_5256_);
lean_inc(v_n_5255_);
lean_inc(v_A_5254_);
lean_inc(v_S_5253_);
lean_inc(v_s_5252_);
lean_inc(v_m_5251_);
lean_inc(v_H_5250_);
lean_inc(v_k_5249_);
lean_inc(v_K_5248_);
lean_inc(v_h_5247_);
lean_inc(v_B_5246_);
lean_inc(v_b_5245_);
lean_inc(v_a_5244_);
lean_inc(v_F_5243_);
lean_inc(v_c_5242_);
lean_inc(v_E_5241_);
lean_inc(v_W_5240_);
lean_inc(v_w_5239_);
lean_inc(v_q_5238_);
lean_inc(v_Q_5237_);
lean_inc(v_d_5236_);
lean_inc(v_L_5235_);
lean_inc(v_M_5234_);
lean_inc(v_D_5233_);
lean_inc(v_Y_5232_);
lean_inc(v_u_5231_);
lean_inc(v_y_5230_);
lean_inc(v_G_5229_);
lean_dec(v_date_4561_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5274_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v___x_5269_; 
if (v_isShared_5228_ == 0)
{
lean_ctor_set_tag(v___x_5227_, 1);
lean_ctor_set(v___x_5227_, 0, v_data_4563_);
v___x_5269_ = v___x_5227_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_data_4563_);
v___x_5269_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5268_;
}
v_reusejp_5268_:
{
lean_object* v___x_5271_; 
if (v_isShared_5267_ == 0)
{
lean_ctor_set(v___x_5266_, 13, v___x_5269_);
v___x_5271_ = v___x_5266_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_G_5229_);
lean_ctor_set(v_reuseFailAlloc_5272_, 1, v_y_5230_);
lean_ctor_set(v_reuseFailAlloc_5272_, 2, v_u_5231_);
lean_ctor_set(v_reuseFailAlloc_5272_, 3, v_Y_5232_);
lean_ctor_set(v_reuseFailAlloc_5272_, 4, v_D_5233_);
lean_ctor_set(v_reuseFailAlloc_5272_, 5, v_M_5234_);
lean_ctor_set(v_reuseFailAlloc_5272_, 6, v_L_5235_);
lean_ctor_set(v_reuseFailAlloc_5272_, 7, v_d_5236_);
lean_ctor_set(v_reuseFailAlloc_5272_, 8, v_Q_5237_);
lean_ctor_set(v_reuseFailAlloc_5272_, 9, v_q_5238_);
lean_ctor_set(v_reuseFailAlloc_5272_, 10, v_w_5239_);
lean_ctor_set(v_reuseFailAlloc_5272_, 11, v_W_5240_);
lean_ctor_set(v_reuseFailAlloc_5272_, 12, v_E_5241_);
lean_ctor_set(v_reuseFailAlloc_5272_, 13, v___x_5269_);
lean_ctor_set(v_reuseFailAlloc_5272_, 14, v_c_5242_);
lean_ctor_set(v_reuseFailAlloc_5272_, 15, v_F_5243_);
lean_ctor_set(v_reuseFailAlloc_5272_, 16, v_a_5244_);
lean_ctor_set(v_reuseFailAlloc_5272_, 17, v_b_5245_);
lean_ctor_set(v_reuseFailAlloc_5272_, 18, v_B_5246_);
lean_ctor_set(v_reuseFailAlloc_5272_, 19, v_h_5247_);
lean_ctor_set(v_reuseFailAlloc_5272_, 20, v_K_5248_);
lean_ctor_set(v_reuseFailAlloc_5272_, 21, v_k_5249_);
lean_ctor_set(v_reuseFailAlloc_5272_, 22, v_H_5250_);
lean_ctor_set(v_reuseFailAlloc_5272_, 23, v_m_5251_);
lean_ctor_set(v_reuseFailAlloc_5272_, 24, v_s_5252_);
lean_ctor_set(v_reuseFailAlloc_5272_, 25, v_S_5253_);
lean_ctor_set(v_reuseFailAlloc_5272_, 26, v_A_5254_);
lean_ctor_set(v_reuseFailAlloc_5272_, 27, v_n_5255_);
lean_ctor_set(v_reuseFailAlloc_5272_, 28, v_N_5256_);
lean_ctor_set(v_reuseFailAlloc_5272_, 29, v_V_5257_);
lean_ctor_set(v_reuseFailAlloc_5272_, 30, v_z_5258_);
lean_ctor_set(v_reuseFailAlloc_5272_, 31, v_zabbrev_5259_);
lean_ctor_set(v_reuseFailAlloc_5272_, 32, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5272_, 33, v_O_5261_);
lean_ctor_set(v_reuseFailAlloc_5272_, 34, v_X_5262_);
lean_ctor_set(v_reuseFailAlloc_5272_, 35, v_x_5263_);
lean_ctor_set(v_reuseFailAlloc_5272_, 36, v_Z_5264_);
v___x_5271_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
return v___x_5271_;
}
}
}
}
}
case 14:
{
lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5328_; 
v_isSharedCheck_5328_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5328_ == 0)
{
lean_object* v_unused_5329_; 
v_unused_5329_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5329_);
v___x_5279_ = v_modifier_4562_;
v_isShared_5280_ = v_isSharedCheck_5328_;
goto v_resetjp_5278_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5328_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v_G_5281_; lean_object* v_y_5282_; lean_object* v_u_5283_; lean_object* v_Y_5284_; lean_object* v_D_5285_; lean_object* v_M_5286_; lean_object* v_L_5287_; lean_object* v_d_5288_; lean_object* v_Q_5289_; lean_object* v_q_5290_; lean_object* v_w_5291_; lean_object* v_W_5292_; lean_object* v_E_5293_; lean_object* v_e_5294_; lean_object* v_F_5295_; lean_object* v_a_5296_; lean_object* v_b_5297_; lean_object* v_B_5298_; lean_object* v_h_5299_; lean_object* v_K_5300_; lean_object* v_k_5301_; lean_object* v_H_5302_; lean_object* v_m_5303_; lean_object* v_s_5304_; lean_object* v_S_5305_; lean_object* v_A_5306_; lean_object* v_n_5307_; lean_object* v_N_5308_; lean_object* v_V_5309_; lean_object* v_z_5310_; lean_object* v_zabbrev_5311_; lean_object* v_v_5312_; lean_object* v_O_5313_; lean_object* v_X_5314_; lean_object* v_x_5315_; lean_object* v_Z_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5326_; 
v_G_5281_ = lean_ctor_get(v_date_4561_, 0);
v_y_5282_ = lean_ctor_get(v_date_4561_, 1);
v_u_5283_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5284_ = lean_ctor_get(v_date_4561_, 3);
v_D_5285_ = lean_ctor_get(v_date_4561_, 4);
v_M_5286_ = lean_ctor_get(v_date_4561_, 5);
v_L_5287_ = lean_ctor_get(v_date_4561_, 6);
v_d_5288_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5289_ = lean_ctor_get(v_date_4561_, 8);
v_q_5290_ = lean_ctor_get(v_date_4561_, 9);
v_w_5291_ = lean_ctor_get(v_date_4561_, 10);
v_W_5292_ = lean_ctor_get(v_date_4561_, 11);
v_E_5293_ = lean_ctor_get(v_date_4561_, 12);
v_e_5294_ = lean_ctor_get(v_date_4561_, 13);
v_F_5295_ = lean_ctor_get(v_date_4561_, 15);
v_a_5296_ = lean_ctor_get(v_date_4561_, 16);
v_b_5297_ = lean_ctor_get(v_date_4561_, 17);
v_B_5298_ = lean_ctor_get(v_date_4561_, 18);
v_h_5299_ = lean_ctor_get(v_date_4561_, 19);
v_K_5300_ = lean_ctor_get(v_date_4561_, 20);
v_k_5301_ = lean_ctor_get(v_date_4561_, 21);
v_H_5302_ = lean_ctor_get(v_date_4561_, 22);
v_m_5303_ = lean_ctor_get(v_date_4561_, 23);
v_s_5304_ = lean_ctor_get(v_date_4561_, 24);
v_S_5305_ = lean_ctor_get(v_date_4561_, 25);
v_A_5306_ = lean_ctor_get(v_date_4561_, 26);
v_n_5307_ = lean_ctor_get(v_date_4561_, 27);
v_N_5308_ = lean_ctor_get(v_date_4561_, 28);
v_V_5309_ = lean_ctor_get(v_date_4561_, 29);
v_z_5310_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5311_ = lean_ctor_get(v_date_4561_, 31);
v_v_5312_ = lean_ctor_get(v_date_4561_, 32);
v_O_5313_ = lean_ctor_get(v_date_4561_, 33);
v_X_5314_ = lean_ctor_get(v_date_4561_, 34);
v_x_5315_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5316_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5326_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5326_ == 0)
{
lean_object* v_unused_5327_; 
v_unused_5327_ = lean_ctor_get(v_date_4561_, 14);
lean_dec(v_unused_5327_);
v___x_5318_ = v_date_4561_;
v_isShared_5319_ = v_isSharedCheck_5326_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_Z_5316_);
lean_inc(v_x_5315_);
lean_inc(v_X_5314_);
lean_inc(v_O_5313_);
lean_inc(v_v_5312_);
lean_inc(v_zabbrev_5311_);
lean_inc(v_z_5310_);
lean_inc(v_V_5309_);
lean_inc(v_N_5308_);
lean_inc(v_n_5307_);
lean_inc(v_A_5306_);
lean_inc(v_S_5305_);
lean_inc(v_s_5304_);
lean_inc(v_m_5303_);
lean_inc(v_H_5302_);
lean_inc(v_k_5301_);
lean_inc(v_K_5300_);
lean_inc(v_h_5299_);
lean_inc(v_B_5298_);
lean_inc(v_b_5297_);
lean_inc(v_a_5296_);
lean_inc(v_F_5295_);
lean_inc(v_e_5294_);
lean_inc(v_E_5293_);
lean_inc(v_W_5292_);
lean_inc(v_w_5291_);
lean_inc(v_q_5290_);
lean_inc(v_Q_5289_);
lean_inc(v_d_5288_);
lean_inc(v_L_5287_);
lean_inc(v_M_5286_);
lean_inc(v_D_5285_);
lean_inc(v_Y_5284_);
lean_inc(v_u_5283_);
lean_inc(v_y_5282_);
lean_inc(v_G_5281_);
lean_dec(v_date_4561_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5326_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5280_ == 0)
{
lean_ctor_set_tag(v___x_5279_, 1);
lean_ctor_set(v___x_5279_, 0, v_data_4563_);
v___x_5321_ = v___x_5279_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_data_4563_);
v___x_5321_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
lean_object* v___x_5323_; 
if (v_isShared_5319_ == 0)
{
lean_ctor_set(v___x_5318_, 14, v___x_5321_);
v___x_5323_ = v___x_5318_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_G_5281_);
lean_ctor_set(v_reuseFailAlloc_5324_, 1, v_y_5282_);
lean_ctor_set(v_reuseFailAlloc_5324_, 2, v_u_5283_);
lean_ctor_set(v_reuseFailAlloc_5324_, 3, v_Y_5284_);
lean_ctor_set(v_reuseFailAlloc_5324_, 4, v_D_5285_);
lean_ctor_set(v_reuseFailAlloc_5324_, 5, v_M_5286_);
lean_ctor_set(v_reuseFailAlloc_5324_, 6, v_L_5287_);
lean_ctor_set(v_reuseFailAlloc_5324_, 7, v_d_5288_);
lean_ctor_set(v_reuseFailAlloc_5324_, 8, v_Q_5289_);
lean_ctor_set(v_reuseFailAlloc_5324_, 9, v_q_5290_);
lean_ctor_set(v_reuseFailAlloc_5324_, 10, v_w_5291_);
lean_ctor_set(v_reuseFailAlloc_5324_, 11, v_W_5292_);
lean_ctor_set(v_reuseFailAlloc_5324_, 12, v_E_5293_);
lean_ctor_set(v_reuseFailAlloc_5324_, 13, v_e_5294_);
lean_ctor_set(v_reuseFailAlloc_5324_, 14, v___x_5321_);
lean_ctor_set(v_reuseFailAlloc_5324_, 15, v_F_5295_);
lean_ctor_set(v_reuseFailAlloc_5324_, 16, v_a_5296_);
lean_ctor_set(v_reuseFailAlloc_5324_, 17, v_b_5297_);
lean_ctor_set(v_reuseFailAlloc_5324_, 18, v_B_5298_);
lean_ctor_set(v_reuseFailAlloc_5324_, 19, v_h_5299_);
lean_ctor_set(v_reuseFailAlloc_5324_, 20, v_K_5300_);
lean_ctor_set(v_reuseFailAlloc_5324_, 21, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5324_, 22, v_H_5302_);
lean_ctor_set(v_reuseFailAlloc_5324_, 23, v_m_5303_);
lean_ctor_set(v_reuseFailAlloc_5324_, 24, v_s_5304_);
lean_ctor_set(v_reuseFailAlloc_5324_, 25, v_S_5305_);
lean_ctor_set(v_reuseFailAlloc_5324_, 26, v_A_5306_);
lean_ctor_set(v_reuseFailAlloc_5324_, 27, v_n_5307_);
lean_ctor_set(v_reuseFailAlloc_5324_, 28, v_N_5308_);
lean_ctor_set(v_reuseFailAlloc_5324_, 29, v_V_5309_);
lean_ctor_set(v_reuseFailAlloc_5324_, 30, v_z_5310_);
lean_ctor_set(v_reuseFailAlloc_5324_, 31, v_zabbrev_5311_);
lean_ctor_set(v_reuseFailAlloc_5324_, 32, v_v_5312_);
lean_ctor_set(v_reuseFailAlloc_5324_, 33, v_O_5313_);
lean_ctor_set(v_reuseFailAlloc_5324_, 34, v_X_5314_);
lean_ctor_set(v_reuseFailAlloc_5324_, 35, v_x_5315_);
lean_ctor_set(v_reuseFailAlloc_5324_, 36, v_Z_5316_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
}
}
case 15:
{
lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5380_; 
v_isSharedCheck_5380_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5380_ == 0)
{
lean_object* v_unused_5381_; 
v_unused_5381_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5381_);
v___x_5331_ = v_modifier_4562_;
v_isShared_5332_ = v_isSharedCheck_5380_;
goto v_resetjp_5330_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5380_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v_G_5333_; lean_object* v_y_5334_; lean_object* v_u_5335_; lean_object* v_Y_5336_; lean_object* v_D_5337_; lean_object* v_M_5338_; lean_object* v_L_5339_; lean_object* v_d_5340_; lean_object* v_Q_5341_; lean_object* v_q_5342_; lean_object* v_w_5343_; lean_object* v_W_5344_; lean_object* v_E_5345_; lean_object* v_e_5346_; lean_object* v_c_5347_; lean_object* v_a_5348_; lean_object* v_b_5349_; lean_object* v_B_5350_; lean_object* v_h_5351_; lean_object* v_K_5352_; lean_object* v_k_5353_; lean_object* v_H_5354_; lean_object* v_m_5355_; lean_object* v_s_5356_; lean_object* v_S_5357_; lean_object* v_A_5358_; lean_object* v_n_5359_; lean_object* v_N_5360_; lean_object* v_V_5361_; lean_object* v_z_5362_; lean_object* v_zabbrev_5363_; lean_object* v_v_5364_; lean_object* v_O_5365_; lean_object* v_X_5366_; lean_object* v_x_5367_; lean_object* v_Z_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5378_; 
v_G_5333_ = lean_ctor_get(v_date_4561_, 0);
v_y_5334_ = lean_ctor_get(v_date_4561_, 1);
v_u_5335_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5336_ = lean_ctor_get(v_date_4561_, 3);
v_D_5337_ = lean_ctor_get(v_date_4561_, 4);
v_M_5338_ = lean_ctor_get(v_date_4561_, 5);
v_L_5339_ = lean_ctor_get(v_date_4561_, 6);
v_d_5340_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5341_ = lean_ctor_get(v_date_4561_, 8);
v_q_5342_ = lean_ctor_get(v_date_4561_, 9);
v_w_5343_ = lean_ctor_get(v_date_4561_, 10);
v_W_5344_ = lean_ctor_get(v_date_4561_, 11);
v_E_5345_ = lean_ctor_get(v_date_4561_, 12);
v_e_5346_ = lean_ctor_get(v_date_4561_, 13);
v_c_5347_ = lean_ctor_get(v_date_4561_, 14);
v_a_5348_ = lean_ctor_get(v_date_4561_, 16);
v_b_5349_ = lean_ctor_get(v_date_4561_, 17);
v_B_5350_ = lean_ctor_get(v_date_4561_, 18);
v_h_5351_ = lean_ctor_get(v_date_4561_, 19);
v_K_5352_ = lean_ctor_get(v_date_4561_, 20);
v_k_5353_ = lean_ctor_get(v_date_4561_, 21);
v_H_5354_ = lean_ctor_get(v_date_4561_, 22);
v_m_5355_ = lean_ctor_get(v_date_4561_, 23);
v_s_5356_ = lean_ctor_get(v_date_4561_, 24);
v_S_5357_ = lean_ctor_get(v_date_4561_, 25);
v_A_5358_ = lean_ctor_get(v_date_4561_, 26);
v_n_5359_ = lean_ctor_get(v_date_4561_, 27);
v_N_5360_ = lean_ctor_get(v_date_4561_, 28);
v_V_5361_ = lean_ctor_get(v_date_4561_, 29);
v_z_5362_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5363_ = lean_ctor_get(v_date_4561_, 31);
v_v_5364_ = lean_ctor_get(v_date_4561_, 32);
v_O_5365_ = lean_ctor_get(v_date_4561_, 33);
v_X_5366_ = lean_ctor_get(v_date_4561_, 34);
v_x_5367_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5368_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5378_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5378_ == 0)
{
lean_object* v_unused_5379_; 
v_unused_5379_ = lean_ctor_get(v_date_4561_, 15);
lean_dec(v_unused_5379_);
v___x_5370_ = v_date_4561_;
v_isShared_5371_ = v_isSharedCheck_5378_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_Z_5368_);
lean_inc(v_x_5367_);
lean_inc(v_X_5366_);
lean_inc(v_O_5365_);
lean_inc(v_v_5364_);
lean_inc(v_zabbrev_5363_);
lean_inc(v_z_5362_);
lean_inc(v_V_5361_);
lean_inc(v_N_5360_);
lean_inc(v_n_5359_);
lean_inc(v_A_5358_);
lean_inc(v_S_5357_);
lean_inc(v_s_5356_);
lean_inc(v_m_5355_);
lean_inc(v_H_5354_);
lean_inc(v_k_5353_);
lean_inc(v_K_5352_);
lean_inc(v_h_5351_);
lean_inc(v_B_5350_);
lean_inc(v_b_5349_);
lean_inc(v_a_5348_);
lean_inc(v_c_5347_);
lean_inc(v_e_5346_);
lean_inc(v_E_5345_);
lean_inc(v_W_5344_);
lean_inc(v_w_5343_);
lean_inc(v_q_5342_);
lean_inc(v_Q_5341_);
lean_inc(v_d_5340_);
lean_inc(v_L_5339_);
lean_inc(v_M_5338_);
lean_inc(v_D_5337_);
lean_inc(v_Y_5336_);
lean_inc(v_u_5335_);
lean_inc(v_y_5334_);
lean_inc(v_G_5333_);
lean_dec(v_date_4561_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5378_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5373_; 
if (v_isShared_5332_ == 0)
{
lean_ctor_set_tag(v___x_5331_, 1);
lean_ctor_set(v___x_5331_, 0, v_data_4563_);
v___x_5373_ = v___x_5331_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_data_4563_);
v___x_5373_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
lean_object* v___x_5375_; 
if (v_isShared_5371_ == 0)
{
lean_ctor_set(v___x_5370_, 15, v___x_5373_);
v___x_5375_ = v___x_5370_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_G_5333_);
lean_ctor_set(v_reuseFailAlloc_5376_, 1, v_y_5334_);
lean_ctor_set(v_reuseFailAlloc_5376_, 2, v_u_5335_);
lean_ctor_set(v_reuseFailAlloc_5376_, 3, v_Y_5336_);
lean_ctor_set(v_reuseFailAlloc_5376_, 4, v_D_5337_);
lean_ctor_set(v_reuseFailAlloc_5376_, 5, v_M_5338_);
lean_ctor_set(v_reuseFailAlloc_5376_, 6, v_L_5339_);
lean_ctor_set(v_reuseFailAlloc_5376_, 7, v_d_5340_);
lean_ctor_set(v_reuseFailAlloc_5376_, 8, v_Q_5341_);
lean_ctor_set(v_reuseFailAlloc_5376_, 9, v_q_5342_);
lean_ctor_set(v_reuseFailAlloc_5376_, 10, v_w_5343_);
lean_ctor_set(v_reuseFailAlloc_5376_, 11, v_W_5344_);
lean_ctor_set(v_reuseFailAlloc_5376_, 12, v_E_5345_);
lean_ctor_set(v_reuseFailAlloc_5376_, 13, v_e_5346_);
lean_ctor_set(v_reuseFailAlloc_5376_, 14, v_c_5347_);
lean_ctor_set(v_reuseFailAlloc_5376_, 15, v___x_5373_);
lean_ctor_set(v_reuseFailAlloc_5376_, 16, v_a_5348_);
lean_ctor_set(v_reuseFailAlloc_5376_, 17, v_b_5349_);
lean_ctor_set(v_reuseFailAlloc_5376_, 18, v_B_5350_);
lean_ctor_set(v_reuseFailAlloc_5376_, 19, v_h_5351_);
lean_ctor_set(v_reuseFailAlloc_5376_, 20, v_K_5352_);
lean_ctor_set(v_reuseFailAlloc_5376_, 21, v_k_5353_);
lean_ctor_set(v_reuseFailAlloc_5376_, 22, v_H_5354_);
lean_ctor_set(v_reuseFailAlloc_5376_, 23, v_m_5355_);
lean_ctor_set(v_reuseFailAlloc_5376_, 24, v_s_5356_);
lean_ctor_set(v_reuseFailAlloc_5376_, 25, v_S_5357_);
lean_ctor_set(v_reuseFailAlloc_5376_, 26, v_A_5358_);
lean_ctor_set(v_reuseFailAlloc_5376_, 27, v_n_5359_);
lean_ctor_set(v_reuseFailAlloc_5376_, 28, v_N_5360_);
lean_ctor_set(v_reuseFailAlloc_5376_, 29, v_V_5361_);
lean_ctor_set(v_reuseFailAlloc_5376_, 30, v_z_5362_);
lean_ctor_set(v_reuseFailAlloc_5376_, 31, v_zabbrev_5363_);
lean_ctor_set(v_reuseFailAlloc_5376_, 32, v_v_5364_);
lean_ctor_set(v_reuseFailAlloc_5376_, 33, v_O_5365_);
lean_ctor_set(v_reuseFailAlloc_5376_, 34, v_X_5366_);
lean_ctor_set(v_reuseFailAlloc_5376_, 35, v_x_5367_);
lean_ctor_set(v_reuseFailAlloc_5376_, 36, v_Z_5368_);
v___x_5375_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
return v___x_5375_;
}
}
}
}
}
case 16:
{
lean_object* v_G_5382_; lean_object* v_y_5383_; lean_object* v_u_5384_; lean_object* v_Y_5385_; lean_object* v_D_5386_; lean_object* v_M_5387_; lean_object* v_L_5388_; lean_object* v_d_5389_; lean_object* v_Q_5390_; lean_object* v_q_5391_; lean_object* v_w_5392_; lean_object* v_W_5393_; lean_object* v_E_5394_; lean_object* v_e_5395_; lean_object* v_c_5396_; lean_object* v_F_5397_; lean_object* v_b_5398_; lean_object* v_B_5399_; lean_object* v_h_5400_; lean_object* v_K_5401_; lean_object* v_k_5402_; lean_object* v_H_5403_; lean_object* v_m_5404_; lean_object* v_s_5405_; lean_object* v_S_5406_; lean_object* v_A_5407_; lean_object* v_n_5408_; lean_object* v_N_5409_; lean_object* v_V_5410_; lean_object* v_z_5411_; lean_object* v_zabbrev_5412_; lean_object* v_v_5413_; lean_object* v_O_5414_; lean_object* v_X_5415_; lean_object* v_x_5416_; lean_object* v_Z_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5425_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_G_5382_ = lean_ctor_get(v_date_4561_, 0);
v_y_5383_ = lean_ctor_get(v_date_4561_, 1);
v_u_5384_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5385_ = lean_ctor_get(v_date_4561_, 3);
v_D_5386_ = lean_ctor_get(v_date_4561_, 4);
v_M_5387_ = lean_ctor_get(v_date_4561_, 5);
v_L_5388_ = lean_ctor_get(v_date_4561_, 6);
v_d_5389_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5390_ = lean_ctor_get(v_date_4561_, 8);
v_q_5391_ = lean_ctor_get(v_date_4561_, 9);
v_w_5392_ = lean_ctor_get(v_date_4561_, 10);
v_W_5393_ = lean_ctor_get(v_date_4561_, 11);
v_E_5394_ = lean_ctor_get(v_date_4561_, 12);
v_e_5395_ = lean_ctor_get(v_date_4561_, 13);
v_c_5396_ = lean_ctor_get(v_date_4561_, 14);
v_F_5397_ = lean_ctor_get(v_date_4561_, 15);
v_b_5398_ = lean_ctor_get(v_date_4561_, 17);
v_B_5399_ = lean_ctor_get(v_date_4561_, 18);
v_h_5400_ = lean_ctor_get(v_date_4561_, 19);
v_K_5401_ = lean_ctor_get(v_date_4561_, 20);
v_k_5402_ = lean_ctor_get(v_date_4561_, 21);
v_H_5403_ = lean_ctor_get(v_date_4561_, 22);
v_m_5404_ = lean_ctor_get(v_date_4561_, 23);
v_s_5405_ = lean_ctor_get(v_date_4561_, 24);
v_S_5406_ = lean_ctor_get(v_date_4561_, 25);
v_A_5407_ = lean_ctor_get(v_date_4561_, 26);
v_n_5408_ = lean_ctor_get(v_date_4561_, 27);
v_N_5409_ = lean_ctor_get(v_date_4561_, 28);
v_V_5410_ = lean_ctor_get(v_date_4561_, 29);
v_z_5411_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5412_ = lean_ctor_get(v_date_4561_, 31);
v_v_5413_ = lean_ctor_get(v_date_4561_, 32);
v_O_5414_ = lean_ctor_get(v_date_4561_, 33);
v_X_5415_ = lean_ctor_get(v_date_4561_, 34);
v_x_5416_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5417_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5425_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5425_ == 0)
{
lean_object* v_unused_5426_; 
v_unused_5426_ = lean_ctor_get(v_date_4561_, 16);
lean_dec(v_unused_5426_);
v___x_5419_ = v_date_4561_;
v_isShared_5420_ = v_isSharedCheck_5425_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_Z_5417_);
lean_inc(v_x_5416_);
lean_inc(v_X_5415_);
lean_inc(v_O_5414_);
lean_inc(v_v_5413_);
lean_inc(v_zabbrev_5412_);
lean_inc(v_z_5411_);
lean_inc(v_V_5410_);
lean_inc(v_N_5409_);
lean_inc(v_n_5408_);
lean_inc(v_A_5407_);
lean_inc(v_S_5406_);
lean_inc(v_s_5405_);
lean_inc(v_m_5404_);
lean_inc(v_H_5403_);
lean_inc(v_k_5402_);
lean_inc(v_K_5401_);
lean_inc(v_h_5400_);
lean_inc(v_B_5399_);
lean_inc(v_b_5398_);
lean_inc(v_F_5397_);
lean_inc(v_c_5396_);
lean_inc(v_e_5395_);
lean_inc(v_E_5394_);
lean_inc(v_W_5393_);
lean_inc(v_w_5392_);
lean_inc(v_q_5391_);
lean_inc(v_Q_5390_);
lean_inc(v_d_5389_);
lean_inc(v_L_5388_);
lean_inc(v_M_5387_);
lean_inc(v_D_5386_);
lean_inc(v_Y_5385_);
lean_inc(v_u_5384_);
lean_inc(v_y_5383_);
lean_inc(v_G_5382_);
lean_dec(v_date_4561_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5425_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v___x_5421_; lean_object* v___x_5423_; 
v___x_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5421_, 0, v_data_4563_);
if (v_isShared_5420_ == 0)
{
lean_ctor_set(v___x_5419_, 16, v___x_5421_);
v___x_5423_ = v___x_5419_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_G_5382_);
lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_y_5383_);
lean_ctor_set(v_reuseFailAlloc_5424_, 2, v_u_5384_);
lean_ctor_set(v_reuseFailAlloc_5424_, 3, v_Y_5385_);
lean_ctor_set(v_reuseFailAlloc_5424_, 4, v_D_5386_);
lean_ctor_set(v_reuseFailAlloc_5424_, 5, v_M_5387_);
lean_ctor_set(v_reuseFailAlloc_5424_, 6, v_L_5388_);
lean_ctor_set(v_reuseFailAlloc_5424_, 7, v_d_5389_);
lean_ctor_set(v_reuseFailAlloc_5424_, 8, v_Q_5390_);
lean_ctor_set(v_reuseFailAlloc_5424_, 9, v_q_5391_);
lean_ctor_set(v_reuseFailAlloc_5424_, 10, v_w_5392_);
lean_ctor_set(v_reuseFailAlloc_5424_, 11, v_W_5393_);
lean_ctor_set(v_reuseFailAlloc_5424_, 12, v_E_5394_);
lean_ctor_set(v_reuseFailAlloc_5424_, 13, v_e_5395_);
lean_ctor_set(v_reuseFailAlloc_5424_, 14, v_c_5396_);
lean_ctor_set(v_reuseFailAlloc_5424_, 15, v_F_5397_);
lean_ctor_set(v_reuseFailAlloc_5424_, 16, v___x_5421_);
lean_ctor_set(v_reuseFailAlloc_5424_, 17, v_b_5398_);
lean_ctor_set(v_reuseFailAlloc_5424_, 18, v_B_5399_);
lean_ctor_set(v_reuseFailAlloc_5424_, 19, v_h_5400_);
lean_ctor_set(v_reuseFailAlloc_5424_, 20, v_K_5401_);
lean_ctor_set(v_reuseFailAlloc_5424_, 21, v_k_5402_);
lean_ctor_set(v_reuseFailAlloc_5424_, 22, v_H_5403_);
lean_ctor_set(v_reuseFailAlloc_5424_, 23, v_m_5404_);
lean_ctor_set(v_reuseFailAlloc_5424_, 24, v_s_5405_);
lean_ctor_set(v_reuseFailAlloc_5424_, 25, v_S_5406_);
lean_ctor_set(v_reuseFailAlloc_5424_, 26, v_A_5407_);
lean_ctor_set(v_reuseFailAlloc_5424_, 27, v_n_5408_);
lean_ctor_set(v_reuseFailAlloc_5424_, 28, v_N_5409_);
lean_ctor_set(v_reuseFailAlloc_5424_, 29, v_V_5410_);
lean_ctor_set(v_reuseFailAlloc_5424_, 30, v_z_5411_);
lean_ctor_set(v_reuseFailAlloc_5424_, 31, v_zabbrev_5412_);
lean_ctor_set(v_reuseFailAlloc_5424_, 32, v_v_5413_);
lean_ctor_set(v_reuseFailAlloc_5424_, 33, v_O_5414_);
lean_ctor_set(v_reuseFailAlloc_5424_, 34, v_X_5415_);
lean_ctor_set(v_reuseFailAlloc_5424_, 35, v_x_5416_);
lean_ctor_set(v_reuseFailAlloc_5424_, 36, v_Z_5417_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
return v___x_5423_;
}
}
}
case 17:
{
lean_object* v_G_5427_; lean_object* v_y_5428_; lean_object* v_u_5429_; lean_object* v_Y_5430_; lean_object* v_D_5431_; lean_object* v_M_5432_; lean_object* v_L_5433_; lean_object* v_d_5434_; lean_object* v_Q_5435_; lean_object* v_q_5436_; lean_object* v_w_5437_; lean_object* v_W_5438_; lean_object* v_E_5439_; lean_object* v_e_5440_; lean_object* v_c_5441_; lean_object* v_F_5442_; lean_object* v_a_5443_; lean_object* v_B_5444_; lean_object* v_h_5445_; lean_object* v_K_5446_; lean_object* v_k_5447_; lean_object* v_H_5448_; lean_object* v_m_5449_; lean_object* v_s_5450_; lean_object* v_S_5451_; lean_object* v_A_5452_; lean_object* v_n_5453_; lean_object* v_N_5454_; lean_object* v_V_5455_; lean_object* v_z_5456_; lean_object* v_zabbrev_5457_; lean_object* v_v_5458_; lean_object* v_O_5459_; lean_object* v_X_5460_; lean_object* v_x_5461_; lean_object* v_Z_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5470_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_G_5427_ = lean_ctor_get(v_date_4561_, 0);
v_y_5428_ = lean_ctor_get(v_date_4561_, 1);
v_u_5429_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5430_ = lean_ctor_get(v_date_4561_, 3);
v_D_5431_ = lean_ctor_get(v_date_4561_, 4);
v_M_5432_ = lean_ctor_get(v_date_4561_, 5);
v_L_5433_ = lean_ctor_get(v_date_4561_, 6);
v_d_5434_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5435_ = lean_ctor_get(v_date_4561_, 8);
v_q_5436_ = lean_ctor_get(v_date_4561_, 9);
v_w_5437_ = lean_ctor_get(v_date_4561_, 10);
v_W_5438_ = lean_ctor_get(v_date_4561_, 11);
v_E_5439_ = lean_ctor_get(v_date_4561_, 12);
v_e_5440_ = lean_ctor_get(v_date_4561_, 13);
v_c_5441_ = lean_ctor_get(v_date_4561_, 14);
v_F_5442_ = lean_ctor_get(v_date_4561_, 15);
v_a_5443_ = lean_ctor_get(v_date_4561_, 16);
v_B_5444_ = lean_ctor_get(v_date_4561_, 18);
v_h_5445_ = lean_ctor_get(v_date_4561_, 19);
v_K_5446_ = lean_ctor_get(v_date_4561_, 20);
v_k_5447_ = lean_ctor_get(v_date_4561_, 21);
v_H_5448_ = lean_ctor_get(v_date_4561_, 22);
v_m_5449_ = lean_ctor_get(v_date_4561_, 23);
v_s_5450_ = lean_ctor_get(v_date_4561_, 24);
v_S_5451_ = lean_ctor_get(v_date_4561_, 25);
v_A_5452_ = lean_ctor_get(v_date_4561_, 26);
v_n_5453_ = lean_ctor_get(v_date_4561_, 27);
v_N_5454_ = lean_ctor_get(v_date_4561_, 28);
v_V_5455_ = lean_ctor_get(v_date_4561_, 29);
v_z_5456_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5457_ = lean_ctor_get(v_date_4561_, 31);
v_v_5458_ = lean_ctor_get(v_date_4561_, 32);
v_O_5459_ = lean_ctor_get(v_date_4561_, 33);
v_X_5460_ = lean_ctor_get(v_date_4561_, 34);
v_x_5461_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5462_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5470_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5470_ == 0)
{
lean_object* v_unused_5471_; 
v_unused_5471_ = lean_ctor_get(v_date_4561_, 17);
lean_dec(v_unused_5471_);
v___x_5464_ = v_date_4561_;
v_isShared_5465_ = v_isSharedCheck_5470_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_Z_5462_);
lean_inc(v_x_5461_);
lean_inc(v_X_5460_);
lean_inc(v_O_5459_);
lean_inc(v_v_5458_);
lean_inc(v_zabbrev_5457_);
lean_inc(v_z_5456_);
lean_inc(v_V_5455_);
lean_inc(v_N_5454_);
lean_inc(v_n_5453_);
lean_inc(v_A_5452_);
lean_inc(v_S_5451_);
lean_inc(v_s_5450_);
lean_inc(v_m_5449_);
lean_inc(v_H_5448_);
lean_inc(v_k_5447_);
lean_inc(v_K_5446_);
lean_inc(v_h_5445_);
lean_inc(v_B_5444_);
lean_inc(v_a_5443_);
lean_inc(v_F_5442_);
lean_inc(v_c_5441_);
lean_inc(v_e_5440_);
lean_inc(v_E_5439_);
lean_inc(v_W_5438_);
lean_inc(v_w_5437_);
lean_inc(v_q_5436_);
lean_inc(v_Q_5435_);
lean_inc(v_d_5434_);
lean_inc(v_L_5433_);
lean_inc(v_M_5432_);
lean_inc(v_D_5431_);
lean_inc(v_Y_5430_);
lean_inc(v_u_5429_);
lean_inc(v_y_5428_);
lean_inc(v_G_5427_);
lean_dec(v_date_4561_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5470_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5466_; lean_object* v___x_5468_; 
v___x_5466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5466_, 0, v_data_4563_);
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 17, v___x_5466_);
v___x_5468_ = v___x_5464_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_G_5427_);
lean_ctor_set(v_reuseFailAlloc_5469_, 1, v_y_5428_);
lean_ctor_set(v_reuseFailAlloc_5469_, 2, v_u_5429_);
lean_ctor_set(v_reuseFailAlloc_5469_, 3, v_Y_5430_);
lean_ctor_set(v_reuseFailAlloc_5469_, 4, v_D_5431_);
lean_ctor_set(v_reuseFailAlloc_5469_, 5, v_M_5432_);
lean_ctor_set(v_reuseFailAlloc_5469_, 6, v_L_5433_);
lean_ctor_set(v_reuseFailAlloc_5469_, 7, v_d_5434_);
lean_ctor_set(v_reuseFailAlloc_5469_, 8, v_Q_5435_);
lean_ctor_set(v_reuseFailAlloc_5469_, 9, v_q_5436_);
lean_ctor_set(v_reuseFailAlloc_5469_, 10, v_w_5437_);
lean_ctor_set(v_reuseFailAlloc_5469_, 11, v_W_5438_);
lean_ctor_set(v_reuseFailAlloc_5469_, 12, v_E_5439_);
lean_ctor_set(v_reuseFailAlloc_5469_, 13, v_e_5440_);
lean_ctor_set(v_reuseFailAlloc_5469_, 14, v_c_5441_);
lean_ctor_set(v_reuseFailAlloc_5469_, 15, v_F_5442_);
lean_ctor_set(v_reuseFailAlloc_5469_, 16, v_a_5443_);
lean_ctor_set(v_reuseFailAlloc_5469_, 17, v___x_5466_);
lean_ctor_set(v_reuseFailAlloc_5469_, 18, v_B_5444_);
lean_ctor_set(v_reuseFailAlloc_5469_, 19, v_h_5445_);
lean_ctor_set(v_reuseFailAlloc_5469_, 20, v_K_5446_);
lean_ctor_set(v_reuseFailAlloc_5469_, 21, v_k_5447_);
lean_ctor_set(v_reuseFailAlloc_5469_, 22, v_H_5448_);
lean_ctor_set(v_reuseFailAlloc_5469_, 23, v_m_5449_);
lean_ctor_set(v_reuseFailAlloc_5469_, 24, v_s_5450_);
lean_ctor_set(v_reuseFailAlloc_5469_, 25, v_S_5451_);
lean_ctor_set(v_reuseFailAlloc_5469_, 26, v_A_5452_);
lean_ctor_set(v_reuseFailAlloc_5469_, 27, v_n_5453_);
lean_ctor_set(v_reuseFailAlloc_5469_, 28, v_N_5454_);
lean_ctor_set(v_reuseFailAlloc_5469_, 29, v_V_5455_);
lean_ctor_set(v_reuseFailAlloc_5469_, 30, v_z_5456_);
lean_ctor_set(v_reuseFailAlloc_5469_, 31, v_zabbrev_5457_);
lean_ctor_set(v_reuseFailAlloc_5469_, 32, v_v_5458_);
lean_ctor_set(v_reuseFailAlloc_5469_, 33, v_O_5459_);
lean_ctor_set(v_reuseFailAlloc_5469_, 34, v_X_5460_);
lean_ctor_set(v_reuseFailAlloc_5469_, 35, v_x_5461_);
lean_ctor_set(v_reuseFailAlloc_5469_, 36, v_Z_5462_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
case 18:
{
lean_object* v_G_5472_; lean_object* v_y_5473_; lean_object* v_u_5474_; lean_object* v_Y_5475_; lean_object* v_D_5476_; lean_object* v_M_5477_; lean_object* v_L_5478_; lean_object* v_d_5479_; lean_object* v_Q_5480_; lean_object* v_q_5481_; lean_object* v_w_5482_; lean_object* v_W_5483_; lean_object* v_E_5484_; lean_object* v_e_5485_; lean_object* v_c_5486_; lean_object* v_F_5487_; lean_object* v_a_5488_; lean_object* v_b_5489_; lean_object* v_h_5490_; lean_object* v_K_5491_; lean_object* v_k_5492_; lean_object* v_H_5493_; lean_object* v_m_5494_; lean_object* v_s_5495_; lean_object* v_S_5496_; lean_object* v_A_5497_; lean_object* v_n_5498_; lean_object* v_N_5499_; lean_object* v_V_5500_; lean_object* v_z_5501_; lean_object* v_zabbrev_5502_; lean_object* v_v_5503_; lean_object* v_O_5504_; lean_object* v_X_5505_; lean_object* v_x_5506_; lean_object* v_Z_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5515_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_G_5472_ = lean_ctor_get(v_date_4561_, 0);
v_y_5473_ = lean_ctor_get(v_date_4561_, 1);
v_u_5474_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5475_ = lean_ctor_get(v_date_4561_, 3);
v_D_5476_ = lean_ctor_get(v_date_4561_, 4);
v_M_5477_ = lean_ctor_get(v_date_4561_, 5);
v_L_5478_ = lean_ctor_get(v_date_4561_, 6);
v_d_5479_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5480_ = lean_ctor_get(v_date_4561_, 8);
v_q_5481_ = lean_ctor_get(v_date_4561_, 9);
v_w_5482_ = lean_ctor_get(v_date_4561_, 10);
v_W_5483_ = lean_ctor_get(v_date_4561_, 11);
v_E_5484_ = lean_ctor_get(v_date_4561_, 12);
v_e_5485_ = lean_ctor_get(v_date_4561_, 13);
v_c_5486_ = lean_ctor_get(v_date_4561_, 14);
v_F_5487_ = lean_ctor_get(v_date_4561_, 15);
v_a_5488_ = lean_ctor_get(v_date_4561_, 16);
v_b_5489_ = lean_ctor_get(v_date_4561_, 17);
v_h_5490_ = lean_ctor_get(v_date_4561_, 19);
v_K_5491_ = lean_ctor_get(v_date_4561_, 20);
v_k_5492_ = lean_ctor_get(v_date_4561_, 21);
v_H_5493_ = lean_ctor_get(v_date_4561_, 22);
v_m_5494_ = lean_ctor_get(v_date_4561_, 23);
v_s_5495_ = lean_ctor_get(v_date_4561_, 24);
v_S_5496_ = lean_ctor_get(v_date_4561_, 25);
v_A_5497_ = lean_ctor_get(v_date_4561_, 26);
v_n_5498_ = lean_ctor_get(v_date_4561_, 27);
v_N_5499_ = lean_ctor_get(v_date_4561_, 28);
v_V_5500_ = lean_ctor_get(v_date_4561_, 29);
v_z_5501_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5502_ = lean_ctor_get(v_date_4561_, 31);
v_v_5503_ = lean_ctor_get(v_date_4561_, 32);
v_O_5504_ = lean_ctor_get(v_date_4561_, 33);
v_X_5505_ = lean_ctor_get(v_date_4561_, 34);
v_x_5506_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5507_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5515_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5515_ == 0)
{
lean_object* v_unused_5516_; 
v_unused_5516_ = lean_ctor_get(v_date_4561_, 18);
lean_dec(v_unused_5516_);
v___x_5509_ = v_date_4561_;
v_isShared_5510_ = v_isSharedCheck_5515_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_Z_5507_);
lean_inc(v_x_5506_);
lean_inc(v_X_5505_);
lean_inc(v_O_5504_);
lean_inc(v_v_5503_);
lean_inc(v_zabbrev_5502_);
lean_inc(v_z_5501_);
lean_inc(v_V_5500_);
lean_inc(v_N_5499_);
lean_inc(v_n_5498_);
lean_inc(v_A_5497_);
lean_inc(v_S_5496_);
lean_inc(v_s_5495_);
lean_inc(v_m_5494_);
lean_inc(v_H_5493_);
lean_inc(v_k_5492_);
lean_inc(v_K_5491_);
lean_inc(v_h_5490_);
lean_inc(v_b_5489_);
lean_inc(v_a_5488_);
lean_inc(v_F_5487_);
lean_inc(v_c_5486_);
lean_inc(v_e_5485_);
lean_inc(v_E_5484_);
lean_inc(v_W_5483_);
lean_inc(v_w_5482_);
lean_inc(v_q_5481_);
lean_inc(v_Q_5480_);
lean_inc(v_d_5479_);
lean_inc(v_L_5478_);
lean_inc(v_M_5477_);
lean_inc(v_D_5476_);
lean_inc(v_Y_5475_);
lean_inc(v_u_5474_);
lean_inc(v_y_5473_);
lean_inc(v_G_5472_);
lean_dec(v_date_4561_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5515_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5511_; lean_object* v___x_5513_; 
v___x_5511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5511_, 0, v_data_4563_);
if (v_isShared_5510_ == 0)
{
lean_ctor_set(v___x_5509_, 18, v___x_5511_);
v___x_5513_ = v___x_5509_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_G_5472_);
lean_ctor_set(v_reuseFailAlloc_5514_, 1, v_y_5473_);
lean_ctor_set(v_reuseFailAlloc_5514_, 2, v_u_5474_);
lean_ctor_set(v_reuseFailAlloc_5514_, 3, v_Y_5475_);
lean_ctor_set(v_reuseFailAlloc_5514_, 4, v_D_5476_);
lean_ctor_set(v_reuseFailAlloc_5514_, 5, v_M_5477_);
lean_ctor_set(v_reuseFailAlloc_5514_, 6, v_L_5478_);
lean_ctor_set(v_reuseFailAlloc_5514_, 7, v_d_5479_);
lean_ctor_set(v_reuseFailAlloc_5514_, 8, v_Q_5480_);
lean_ctor_set(v_reuseFailAlloc_5514_, 9, v_q_5481_);
lean_ctor_set(v_reuseFailAlloc_5514_, 10, v_w_5482_);
lean_ctor_set(v_reuseFailAlloc_5514_, 11, v_W_5483_);
lean_ctor_set(v_reuseFailAlloc_5514_, 12, v_E_5484_);
lean_ctor_set(v_reuseFailAlloc_5514_, 13, v_e_5485_);
lean_ctor_set(v_reuseFailAlloc_5514_, 14, v_c_5486_);
lean_ctor_set(v_reuseFailAlloc_5514_, 15, v_F_5487_);
lean_ctor_set(v_reuseFailAlloc_5514_, 16, v_a_5488_);
lean_ctor_set(v_reuseFailAlloc_5514_, 17, v_b_5489_);
lean_ctor_set(v_reuseFailAlloc_5514_, 18, v___x_5511_);
lean_ctor_set(v_reuseFailAlloc_5514_, 19, v_h_5490_);
lean_ctor_set(v_reuseFailAlloc_5514_, 20, v_K_5491_);
lean_ctor_set(v_reuseFailAlloc_5514_, 21, v_k_5492_);
lean_ctor_set(v_reuseFailAlloc_5514_, 22, v_H_5493_);
lean_ctor_set(v_reuseFailAlloc_5514_, 23, v_m_5494_);
lean_ctor_set(v_reuseFailAlloc_5514_, 24, v_s_5495_);
lean_ctor_set(v_reuseFailAlloc_5514_, 25, v_S_5496_);
lean_ctor_set(v_reuseFailAlloc_5514_, 26, v_A_5497_);
lean_ctor_set(v_reuseFailAlloc_5514_, 27, v_n_5498_);
lean_ctor_set(v_reuseFailAlloc_5514_, 28, v_N_5499_);
lean_ctor_set(v_reuseFailAlloc_5514_, 29, v_V_5500_);
lean_ctor_set(v_reuseFailAlloc_5514_, 30, v_z_5501_);
lean_ctor_set(v_reuseFailAlloc_5514_, 31, v_zabbrev_5502_);
lean_ctor_set(v_reuseFailAlloc_5514_, 32, v_v_5503_);
lean_ctor_set(v_reuseFailAlloc_5514_, 33, v_O_5504_);
lean_ctor_set(v_reuseFailAlloc_5514_, 34, v_X_5505_);
lean_ctor_set(v_reuseFailAlloc_5514_, 35, v_x_5506_);
lean_ctor_set(v_reuseFailAlloc_5514_, 36, v_Z_5507_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
case 19:
{
lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5567_; 
v_isSharedCheck_5567_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5567_ == 0)
{
lean_object* v_unused_5568_; 
v_unused_5568_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5568_);
v___x_5518_ = v_modifier_4562_;
v_isShared_5519_ = v_isSharedCheck_5567_;
goto v_resetjp_5517_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5567_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v_G_5520_; lean_object* v_y_5521_; lean_object* v_u_5522_; lean_object* v_Y_5523_; lean_object* v_D_5524_; lean_object* v_M_5525_; lean_object* v_L_5526_; lean_object* v_d_5527_; lean_object* v_Q_5528_; lean_object* v_q_5529_; lean_object* v_w_5530_; lean_object* v_W_5531_; lean_object* v_E_5532_; lean_object* v_e_5533_; lean_object* v_c_5534_; lean_object* v_F_5535_; lean_object* v_a_5536_; lean_object* v_b_5537_; lean_object* v_B_5538_; lean_object* v_K_5539_; lean_object* v_k_5540_; lean_object* v_H_5541_; lean_object* v_m_5542_; lean_object* v_s_5543_; lean_object* v_S_5544_; lean_object* v_A_5545_; lean_object* v_n_5546_; lean_object* v_N_5547_; lean_object* v_V_5548_; lean_object* v_z_5549_; lean_object* v_zabbrev_5550_; lean_object* v_v_5551_; lean_object* v_O_5552_; lean_object* v_X_5553_; lean_object* v_x_5554_; lean_object* v_Z_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5565_; 
v_G_5520_ = lean_ctor_get(v_date_4561_, 0);
v_y_5521_ = lean_ctor_get(v_date_4561_, 1);
v_u_5522_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5523_ = lean_ctor_get(v_date_4561_, 3);
v_D_5524_ = lean_ctor_get(v_date_4561_, 4);
v_M_5525_ = lean_ctor_get(v_date_4561_, 5);
v_L_5526_ = lean_ctor_get(v_date_4561_, 6);
v_d_5527_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5528_ = lean_ctor_get(v_date_4561_, 8);
v_q_5529_ = lean_ctor_get(v_date_4561_, 9);
v_w_5530_ = lean_ctor_get(v_date_4561_, 10);
v_W_5531_ = lean_ctor_get(v_date_4561_, 11);
v_E_5532_ = lean_ctor_get(v_date_4561_, 12);
v_e_5533_ = lean_ctor_get(v_date_4561_, 13);
v_c_5534_ = lean_ctor_get(v_date_4561_, 14);
v_F_5535_ = lean_ctor_get(v_date_4561_, 15);
v_a_5536_ = lean_ctor_get(v_date_4561_, 16);
v_b_5537_ = lean_ctor_get(v_date_4561_, 17);
v_B_5538_ = lean_ctor_get(v_date_4561_, 18);
v_K_5539_ = lean_ctor_get(v_date_4561_, 20);
v_k_5540_ = lean_ctor_get(v_date_4561_, 21);
v_H_5541_ = lean_ctor_get(v_date_4561_, 22);
v_m_5542_ = lean_ctor_get(v_date_4561_, 23);
v_s_5543_ = lean_ctor_get(v_date_4561_, 24);
v_S_5544_ = lean_ctor_get(v_date_4561_, 25);
v_A_5545_ = lean_ctor_get(v_date_4561_, 26);
v_n_5546_ = lean_ctor_get(v_date_4561_, 27);
v_N_5547_ = lean_ctor_get(v_date_4561_, 28);
v_V_5548_ = lean_ctor_get(v_date_4561_, 29);
v_z_5549_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5550_ = lean_ctor_get(v_date_4561_, 31);
v_v_5551_ = lean_ctor_get(v_date_4561_, 32);
v_O_5552_ = lean_ctor_get(v_date_4561_, 33);
v_X_5553_ = lean_ctor_get(v_date_4561_, 34);
v_x_5554_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5555_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5565_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5565_ == 0)
{
lean_object* v_unused_5566_; 
v_unused_5566_ = lean_ctor_get(v_date_4561_, 19);
lean_dec(v_unused_5566_);
v___x_5557_ = v_date_4561_;
v_isShared_5558_ = v_isSharedCheck_5565_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_Z_5555_);
lean_inc(v_x_5554_);
lean_inc(v_X_5553_);
lean_inc(v_O_5552_);
lean_inc(v_v_5551_);
lean_inc(v_zabbrev_5550_);
lean_inc(v_z_5549_);
lean_inc(v_V_5548_);
lean_inc(v_N_5547_);
lean_inc(v_n_5546_);
lean_inc(v_A_5545_);
lean_inc(v_S_5544_);
lean_inc(v_s_5543_);
lean_inc(v_m_5542_);
lean_inc(v_H_5541_);
lean_inc(v_k_5540_);
lean_inc(v_K_5539_);
lean_inc(v_B_5538_);
lean_inc(v_b_5537_);
lean_inc(v_a_5536_);
lean_inc(v_F_5535_);
lean_inc(v_c_5534_);
lean_inc(v_e_5533_);
lean_inc(v_E_5532_);
lean_inc(v_W_5531_);
lean_inc(v_w_5530_);
lean_inc(v_q_5529_);
lean_inc(v_Q_5528_);
lean_inc(v_d_5527_);
lean_inc(v_L_5526_);
lean_inc(v_M_5525_);
lean_inc(v_D_5524_);
lean_inc(v_Y_5523_);
lean_inc(v_u_5522_);
lean_inc(v_y_5521_);
lean_inc(v_G_5520_);
lean_dec(v_date_4561_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5565_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v___x_5560_; 
if (v_isShared_5519_ == 0)
{
lean_ctor_set_tag(v___x_5518_, 1);
lean_ctor_set(v___x_5518_, 0, v_data_4563_);
v___x_5560_ = v___x_5518_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_data_4563_);
v___x_5560_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
lean_object* v___x_5562_; 
if (v_isShared_5558_ == 0)
{
lean_ctor_set(v___x_5557_, 19, v___x_5560_);
v___x_5562_ = v___x_5557_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_G_5520_);
lean_ctor_set(v_reuseFailAlloc_5563_, 1, v_y_5521_);
lean_ctor_set(v_reuseFailAlloc_5563_, 2, v_u_5522_);
lean_ctor_set(v_reuseFailAlloc_5563_, 3, v_Y_5523_);
lean_ctor_set(v_reuseFailAlloc_5563_, 4, v_D_5524_);
lean_ctor_set(v_reuseFailAlloc_5563_, 5, v_M_5525_);
lean_ctor_set(v_reuseFailAlloc_5563_, 6, v_L_5526_);
lean_ctor_set(v_reuseFailAlloc_5563_, 7, v_d_5527_);
lean_ctor_set(v_reuseFailAlloc_5563_, 8, v_Q_5528_);
lean_ctor_set(v_reuseFailAlloc_5563_, 9, v_q_5529_);
lean_ctor_set(v_reuseFailAlloc_5563_, 10, v_w_5530_);
lean_ctor_set(v_reuseFailAlloc_5563_, 11, v_W_5531_);
lean_ctor_set(v_reuseFailAlloc_5563_, 12, v_E_5532_);
lean_ctor_set(v_reuseFailAlloc_5563_, 13, v_e_5533_);
lean_ctor_set(v_reuseFailAlloc_5563_, 14, v_c_5534_);
lean_ctor_set(v_reuseFailAlloc_5563_, 15, v_F_5535_);
lean_ctor_set(v_reuseFailAlloc_5563_, 16, v_a_5536_);
lean_ctor_set(v_reuseFailAlloc_5563_, 17, v_b_5537_);
lean_ctor_set(v_reuseFailAlloc_5563_, 18, v_B_5538_);
lean_ctor_set(v_reuseFailAlloc_5563_, 19, v___x_5560_);
lean_ctor_set(v_reuseFailAlloc_5563_, 20, v_K_5539_);
lean_ctor_set(v_reuseFailAlloc_5563_, 21, v_k_5540_);
lean_ctor_set(v_reuseFailAlloc_5563_, 22, v_H_5541_);
lean_ctor_set(v_reuseFailAlloc_5563_, 23, v_m_5542_);
lean_ctor_set(v_reuseFailAlloc_5563_, 24, v_s_5543_);
lean_ctor_set(v_reuseFailAlloc_5563_, 25, v_S_5544_);
lean_ctor_set(v_reuseFailAlloc_5563_, 26, v_A_5545_);
lean_ctor_set(v_reuseFailAlloc_5563_, 27, v_n_5546_);
lean_ctor_set(v_reuseFailAlloc_5563_, 28, v_N_5547_);
lean_ctor_set(v_reuseFailAlloc_5563_, 29, v_V_5548_);
lean_ctor_set(v_reuseFailAlloc_5563_, 30, v_z_5549_);
lean_ctor_set(v_reuseFailAlloc_5563_, 31, v_zabbrev_5550_);
lean_ctor_set(v_reuseFailAlloc_5563_, 32, v_v_5551_);
lean_ctor_set(v_reuseFailAlloc_5563_, 33, v_O_5552_);
lean_ctor_set(v_reuseFailAlloc_5563_, 34, v_X_5553_);
lean_ctor_set(v_reuseFailAlloc_5563_, 35, v_x_5554_);
lean_ctor_set(v_reuseFailAlloc_5563_, 36, v_Z_5555_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
}
}
case 20:
{
lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5619_; 
v_isSharedCheck_5619_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5619_ == 0)
{
lean_object* v_unused_5620_; 
v_unused_5620_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5620_);
v___x_5570_ = v_modifier_4562_;
v_isShared_5571_ = v_isSharedCheck_5619_;
goto v_resetjp_5569_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5619_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v_G_5572_; lean_object* v_y_5573_; lean_object* v_u_5574_; lean_object* v_Y_5575_; lean_object* v_D_5576_; lean_object* v_M_5577_; lean_object* v_L_5578_; lean_object* v_d_5579_; lean_object* v_Q_5580_; lean_object* v_q_5581_; lean_object* v_w_5582_; lean_object* v_W_5583_; lean_object* v_E_5584_; lean_object* v_e_5585_; lean_object* v_c_5586_; lean_object* v_F_5587_; lean_object* v_a_5588_; lean_object* v_b_5589_; lean_object* v_B_5590_; lean_object* v_h_5591_; lean_object* v_k_5592_; lean_object* v_H_5593_; lean_object* v_m_5594_; lean_object* v_s_5595_; lean_object* v_S_5596_; lean_object* v_A_5597_; lean_object* v_n_5598_; lean_object* v_N_5599_; lean_object* v_V_5600_; lean_object* v_z_5601_; lean_object* v_zabbrev_5602_; lean_object* v_v_5603_; lean_object* v_O_5604_; lean_object* v_X_5605_; lean_object* v_x_5606_; lean_object* v_Z_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5617_; 
v_G_5572_ = lean_ctor_get(v_date_4561_, 0);
v_y_5573_ = lean_ctor_get(v_date_4561_, 1);
v_u_5574_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5575_ = lean_ctor_get(v_date_4561_, 3);
v_D_5576_ = lean_ctor_get(v_date_4561_, 4);
v_M_5577_ = lean_ctor_get(v_date_4561_, 5);
v_L_5578_ = lean_ctor_get(v_date_4561_, 6);
v_d_5579_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5580_ = lean_ctor_get(v_date_4561_, 8);
v_q_5581_ = lean_ctor_get(v_date_4561_, 9);
v_w_5582_ = lean_ctor_get(v_date_4561_, 10);
v_W_5583_ = lean_ctor_get(v_date_4561_, 11);
v_E_5584_ = lean_ctor_get(v_date_4561_, 12);
v_e_5585_ = lean_ctor_get(v_date_4561_, 13);
v_c_5586_ = lean_ctor_get(v_date_4561_, 14);
v_F_5587_ = lean_ctor_get(v_date_4561_, 15);
v_a_5588_ = lean_ctor_get(v_date_4561_, 16);
v_b_5589_ = lean_ctor_get(v_date_4561_, 17);
v_B_5590_ = lean_ctor_get(v_date_4561_, 18);
v_h_5591_ = lean_ctor_get(v_date_4561_, 19);
v_k_5592_ = lean_ctor_get(v_date_4561_, 21);
v_H_5593_ = lean_ctor_get(v_date_4561_, 22);
v_m_5594_ = lean_ctor_get(v_date_4561_, 23);
v_s_5595_ = lean_ctor_get(v_date_4561_, 24);
v_S_5596_ = lean_ctor_get(v_date_4561_, 25);
v_A_5597_ = lean_ctor_get(v_date_4561_, 26);
v_n_5598_ = lean_ctor_get(v_date_4561_, 27);
v_N_5599_ = lean_ctor_get(v_date_4561_, 28);
v_V_5600_ = lean_ctor_get(v_date_4561_, 29);
v_z_5601_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5602_ = lean_ctor_get(v_date_4561_, 31);
v_v_5603_ = lean_ctor_get(v_date_4561_, 32);
v_O_5604_ = lean_ctor_get(v_date_4561_, 33);
v_X_5605_ = lean_ctor_get(v_date_4561_, 34);
v_x_5606_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5607_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5617_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5617_ == 0)
{
lean_object* v_unused_5618_; 
v_unused_5618_ = lean_ctor_get(v_date_4561_, 20);
lean_dec(v_unused_5618_);
v___x_5609_ = v_date_4561_;
v_isShared_5610_ = v_isSharedCheck_5617_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_Z_5607_);
lean_inc(v_x_5606_);
lean_inc(v_X_5605_);
lean_inc(v_O_5604_);
lean_inc(v_v_5603_);
lean_inc(v_zabbrev_5602_);
lean_inc(v_z_5601_);
lean_inc(v_V_5600_);
lean_inc(v_N_5599_);
lean_inc(v_n_5598_);
lean_inc(v_A_5597_);
lean_inc(v_S_5596_);
lean_inc(v_s_5595_);
lean_inc(v_m_5594_);
lean_inc(v_H_5593_);
lean_inc(v_k_5592_);
lean_inc(v_h_5591_);
lean_inc(v_B_5590_);
lean_inc(v_b_5589_);
lean_inc(v_a_5588_);
lean_inc(v_F_5587_);
lean_inc(v_c_5586_);
lean_inc(v_e_5585_);
lean_inc(v_E_5584_);
lean_inc(v_W_5583_);
lean_inc(v_w_5582_);
lean_inc(v_q_5581_);
lean_inc(v_Q_5580_);
lean_inc(v_d_5579_);
lean_inc(v_L_5578_);
lean_inc(v_M_5577_);
lean_inc(v_D_5576_);
lean_inc(v_Y_5575_);
lean_inc(v_u_5574_);
lean_inc(v_y_5573_);
lean_inc(v_G_5572_);
lean_dec(v_date_4561_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5617_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5612_; 
if (v_isShared_5571_ == 0)
{
lean_ctor_set_tag(v___x_5570_, 1);
lean_ctor_set(v___x_5570_, 0, v_data_4563_);
v___x_5612_ = v___x_5570_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v_data_4563_);
v___x_5612_ = v_reuseFailAlloc_5616_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
lean_object* v___x_5614_; 
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 20, v___x_5612_);
v___x_5614_ = v___x_5609_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v_G_5572_);
lean_ctor_set(v_reuseFailAlloc_5615_, 1, v_y_5573_);
lean_ctor_set(v_reuseFailAlloc_5615_, 2, v_u_5574_);
lean_ctor_set(v_reuseFailAlloc_5615_, 3, v_Y_5575_);
lean_ctor_set(v_reuseFailAlloc_5615_, 4, v_D_5576_);
lean_ctor_set(v_reuseFailAlloc_5615_, 5, v_M_5577_);
lean_ctor_set(v_reuseFailAlloc_5615_, 6, v_L_5578_);
lean_ctor_set(v_reuseFailAlloc_5615_, 7, v_d_5579_);
lean_ctor_set(v_reuseFailAlloc_5615_, 8, v_Q_5580_);
lean_ctor_set(v_reuseFailAlloc_5615_, 9, v_q_5581_);
lean_ctor_set(v_reuseFailAlloc_5615_, 10, v_w_5582_);
lean_ctor_set(v_reuseFailAlloc_5615_, 11, v_W_5583_);
lean_ctor_set(v_reuseFailAlloc_5615_, 12, v_E_5584_);
lean_ctor_set(v_reuseFailAlloc_5615_, 13, v_e_5585_);
lean_ctor_set(v_reuseFailAlloc_5615_, 14, v_c_5586_);
lean_ctor_set(v_reuseFailAlloc_5615_, 15, v_F_5587_);
lean_ctor_set(v_reuseFailAlloc_5615_, 16, v_a_5588_);
lean_ctor_set(v_reuseFailAlloc_5615_, 17, v_b_5589_);
lean_ctor_set(v_reuseFailAlloc_5615_, 18, v_B_5590_);
lean_ctor_set(v_reuseFailAlloc_5615_, 19, v_h_5591_);
lean_ctor_set(v_reuseFailAlloc_5615_, 20, v___x_5612_);
lean_ctor_set(v_reuseFailAlloc_5615_, 21, v_k_5592_);
lean_ctor_set(v_reuseFailAlloc_5615_, 22, v_H_5593_);
lean_ctor_set(v_reuseFailAlloc_5615_, 23, v_m_5594_);
lean_ctor_set(v_reuseFailAlloc_5615_, 24, v_s_5595_);
lean_ctor_set(v_reuseFailAlloc_5615_, 25, v_S_5596_);
lean_ctor_set(v_reuseFailAlloc_5615_, 26, v_A_5597_);
lean_ctor_set(v_reuseFailAlloc_5615_, 27, v_n_5598_);
lean_ctor_set(v_reuseFailAlloc_5615_, 28, v_N_5599_);
lean_ctor_set(v_reuseFailAlloc_5615_, 29, v_V_5600_);
lean_ctor_set(v_reuseFailAlloc_5615_, 30, v_z_5601_);
lean_ctor_set(v_reuseFailAlloc_5615_, 31, v_zabbrev_5602_);
lean_ctor_set(v_reuseFailAlloc_5615_, 32, v_v_5603_);
lean_ctor_set(v_reuseFailAlloc_5615_, 33, v_O_5604_);
lean_ctor_set(v_reuseFailAlloc_5615_, 34, v_X_5605_);
lean_ctor_set(v_reuseFailAlloc_5615_, 35, v_x_5606_);
lean_ctor_set(v_reuseFailAlloc_5615_, 36, v_Z_5607_);
v___x_5614_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
return v___x_5614_;
}
}
}
}
}
case 21:
{
lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5671_; 
v_isSharedCheck_5671_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5671_ == 0)
{
lean_object* v_unused_5672_; 
v_unused_5672_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5672_);
v___x_5622_ = v_modifier_4562_;
v_isShared_5623_ = v_isSharedCheck_5671_;
goto v_resetjp_5621_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5671_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v_G_5624_; lean_object* v_y_5625_; lean_object* v_u_5626_; lean_object* v_Y_5627_; lean_object* v_D_5628_; lean_object* v_M_5629_; lean_object* v_L_5630_; lean_object* v_d_5631_; lean_object* v_Q_5632_; lean_object* v_q_5633_; lean_object* v_w_5634_; lean_object* v_W_5635_; lean_object* v_E_5636_; lean_object* v_e_5637_; lean_object* v_c_5638_; lean_object* v_F_5639_; lean_object* v_a_5640_; lean_object* v_b_5641_; lean_object* v_B_5642_; lean_object* v_h_5643_; lean_object* v_K_5644_; lean_object* v_H_5645_; lean_object* v_m_5646_; lean_object* v_s_5647_; lean_object* v_S_5648_; lean_object* v_A_5649_; lean_object* v_n_5650_; lean_object* v_N_5651_; lean_object* v_V_5652_; lean_object* v_z_5653_; lean_object* v_zabbrev_5654_; lean_object* v_v_5655_; lean_object* v_O_5656_; lean_object* v_X_5657_; lean_object* v_x_5658_; lean_object* v_Z_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5669_; 
v_G_5624_ = lean_ctor_get(v_date_4561_, 0);
v_y_5625_ = lean_ctor_get(v_date_4561_, 1);
v_u_5626_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5627_ = lean_ctor_get(v_date_4561_, 3);
v_D_5628_ = lean_ctor_get(v_date_4561_, 4);
v_M_5629_ = lean_ctor_get(v_date_4561_, 5);
v_L_5630_ = lean_ctor_get(v_date_4561_, 6);
v_d_5631_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5632_ = lean_ctor_get(v_date_4561_, 8);
v_q_5633_ = lean_ctor_get(v_date_4561_, 9);
v_w_5634_ = lean_ctor_get(v_date_4561_, 10);
v_W_5635_ = lean_ctor_get(v_date_4561_, 11);
v_E_5636_ = lean_ctor_get(v_date_4561_, 12);
v_e_5637_ = lean_ctor_get(v_date_4561_, 13);
v_c_5638_ = lean_ctor_get(v_date_4561_, 14);
v_F_5639_ = lean_ctor_get(v_date_4561_, 15);
v_a_5640_ = lean_ctor_get(v_date_4561_, 16);
v_b_5641_ = lean_ctor_get(v_date_4561_, 17);
v_B_5642_ = lean_ctor_get(v_date_4561_, 18);
v_h_5643_ = lean_ctor_get(v_date_4561_, 19);
v_K_5644_ = lean_ctor_get(v_date_4561_, 20);
v_H_5645_ = lean_ctor_get(v_date_4561_, 22);
v_m_5646_ = lean_ctor_get(v_date_4561_, 23);
v_s_5647_ = lean_ctor_get(v_date_4561_, 24);
v_S_5648_ = lean_ctor_get(v_date_4561_, 25);
v_A_5649_ = lean_ctor_get(v_date_4561_, 26);
v_n_5650_ = lean_ctor_get(v_date_4561_, 27);
v_N_5651_ = lean_ctor_get(v_date_4561_, 28);
v_V_5652_ = lean_ctor_get(v_date_4561_, 29);
v_z_5653_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5654_ = lean_ctor_get(v_date_4561_, 31);
v_v_5655_ = lean_ctor_get(v_date_4561_, 32);
v_O_5656_ = lean_ctor_get(v_date_4561_, 33);
v_X_5657_ = lean_ctor_get(v_date_4561_, 34);
v_x_5658_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5659_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5669_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5669_ == 0)
{
lean_object* v_unused_5670_; 
v_unused_5670_ = lean_ctor_get(v_date_4561_, 21);
lean_dec(v_unused_5670_);
v___x_5661_ = v_date_4561_;
v_isShared_5662_ = v_isSharedCheck_5669_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_Z_5659_);
lean_inc(v_x_5658_);
lean_inc(v_X_5657_);
lean_inc(v_O_5656_);
lean_inc(v_v_5655_);
lean_inc(v_zabbrev_5654_);
lean_inc(v_z_5653_);
lean_inc(v_V_5652_);
lean_inc(v_N_5651_);
lean_inc(v_n_5650_);
lean_inc(v_A_5649_);
lean_inc(v_S_5648_);
lean_inc(v_s_5647_);
lean_inc(v_m_5646_);
lean_inc(v_H_5645_);
lean_inc(v_K_5644_);
lean_inc(v_h_5643_);
lean_inc(v_B_5642_);
lean_inc(v_b_5641_);
lean_inc(v_a_5640_);
lean_inc(v_F_5639_);
lean_inc(v_c_5638_);
lean_inc(v_e_5637_);
lean_inc(v_E_5636_);
lean_inc(v_W_5635_);
lean_inc(v_w_5634_);
lean_inc(v_q_5633_);
lean_inc(v_Q_5632_);
lean_inc(v_d_5631_);
lean_inc(v_L_5630_);
lean_inc(v_M_5629_);
lean_inc(v_D_5628_);
lean_inc(v_Y_5627_);
lean_inc(v_u_5626_);
lean_inc(v_y_5625_);
lean_inc(v_G_5624_);
lean_dec(v_date_4561_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5669_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5623_ == 0)
{
lean_ctor_set_tag(v___x_5622_, 1);
lean_ctor_set(v___x_5622_, 0, v_data_4563_);
v___x_5664_ = v___x_5622_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_data_4563_);
v___x_5664_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
lean_object* v___x_5666_; 
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 21, v___x_5664_);
v___x_5666_ = v___x_5661_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_G_5624_);
lean_ctor_set(v_reuseFailAlloc_5667_, 1, v_y_5625_);
lean_ctor_set(v_reuseFailAlloc_5667_, 2, v_u_5626_);
lean_ctor_set(v_reuseFailAlloc_5667_, 3, v_Y_5627_);
lean_ctor_set(v_reuseFailAlloc_5667_, 4, v_D_5628_);
lean_ctor_set(v_reuseFailAlloc_5667_, 5, v_M_5629_);
lean_ctor_set(v_reuseFailAlloc_5667_, 6, v_L_5630_);
lean_ctor_set(v_reuseFailAlloc_5667_, 7, v_d_5631_);
lean_ctor_set(v_reuseFailAlloc_5667_, 8, v_Q_5632_);
lean_ctor_set(v_reuseFailAlloc_5667_, 9, v_q_5633_);
lean_ctor_set(v_reuseFailAlloc_5667_, 10, v_w_5634_);
lean_ctor_set(v_reuseFailAlloc_5667_, 11, v_W_5635_);
lean_ctor_set(v_reuseFailAlloc_5667_, 12, v_E_5636_);
lean_ctor_set(v_reuseFailAlloc_5667_, 13, v_e_5637_);
lean_ctor_set(v_reuseFailAlloc_5667_, 14, v_c_5638_);
lean_ctor_set(v_reuseFailAlloc_5667_, 15, v_F_5639_);
lean_ctor_set(v_reuseFailAlloc_5667_, 16, v_a_5640_);
lean_ctor_set(v_reuseFailAlloc_5667_, 17, v_b_5641_);
lean_ctor_set(v_reuseFailAlloc_5667_, 18, v_B_5642_);
lean_ctor_set(v_reuseFailAlloc_5667_, 19, v_h_5643_);
lean_ctor_set(v_reuseFailAlloc_5667_, 20, v_K_5644_);
lean_ctor_set(v_reuseFailAlloc_5667_, 21, v___x_5664_);
lean_ctor_set(v_reuseFailAlloc_5667_, 22, v_H_5645_);
lean_ctor_set(v_reuseFailAlloc_5667_, 23, v_m_5646_);
lean_ctor_set(v_reuseFailAlloc_5667_, 24, v_s_5647_);
lean_ctor_set(v_reuseFailAlloc_5667_, 25, v_S_5648_);
lean_ctor_set(v_reuseFailAlloc_5667_, 26, v_A_5649_);
lean_ctor_set(v_reuseFailAlloc_5667_, 27, v_n_5650_);
lean_ctor_set(v_reuseFailAlloc_5667_, 28, v_N_5651_);
lean_ctor_set(v_reuseFailAlloc_5667_, 29, v_V_5652_);
lean_ctor_set(v_reuseFailAlloc_5667_, 30, v_z_5653_);
lean_ctor_set(v_reuseFailAlloc_5667_, 31, v_zabbrev_5654_);
lean_ctor_set(v_reuseFailAlloc_5667_, 32, v_v_5655_);
lean_ctor_set(v_reuseFailAlloc_5667_, 33, v_O_5656_);
lean_ctor_set(v_reuseFailAlloc_5667_, 34, v_X_5657_);
lean_ctor_set(v_reuseFailAlloc_5667_, 35, v_x_5658_);
lean_ctor_set(v_reuseFailAlloc_5667_, 36, v_Z_5659_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
}
case 22:
{
lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5723_; 
v_isSharedCheck_5723_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5723_ == 0)
{
lean_object* v_unused_5724_; 
v_unused_5724_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5724_);
v___x_5674_ = v_modifier_4562_;
v_isShared_5675_ = v_isSharedCheck_5723_;
goto v_resetjp_5673_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5723_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v_G_5676_; lean_object* v_y_5677_; lean_object* v_u_5678_; lean_object* v_Y_5679_; lean_object* v_D_5680_; lean_object* v_M_5681_; lean_object* v_L_5682_; lean_object* v_d_5683_; lean_object* v_Q_5684_; lean_object* v_q_5685_; lean_object* v_w_5686_; lean_object* v_W_5687_; lean_object* v_E_5688_; lean_object* v_e_5689_; lean_object* v_c_5690_; lean_object* v_F_5691_; lean_object* v_a_5692_; lean_object* v_b_5693_; lean_object* v_B_5694_; lean_object* v_h_5695_; lean_object* v_K_5696_; lean_object* v_k_5697_; lean_object* v_m_5698_; lean_object* v_s_5699_; lean_object* v_S_5700_; lean_object* v_A_5701_; lean_object* v_n_5702_; lean_object* v_N_5703_; lean_object* v_V_5704_; lean_object* v_z_5705_; lean_object* v_zabbrev_5706_; lean_object* v_v_5707_; lean_object* v_O_5708_; lean_object* v_X_5709_; lean_object* v_x_5710_; lean_object* v_Z_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5721_; 
v_G_5676_ = lean_ctor_get(v_date_4561_, 0);
v_y_5677_ = lean_ctor_get(v_date_4561_, 1);
v_u_5678_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5679_ = lean_ctor_get(v_date_4561_, 3);
v_D_5680_ = lean_ctor_get(v_date_4561_, 4);
v_M_5681_ = lean_ctor_get(v_date_4561_, 5);
v_L_5682_ = lean_ctor_get(v_date_4561_, 6);
v_d_5683_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5684_ = lean_ctor_get(v_date_4561_, 8);
v_q_5685_ = lean_ctor_get(v_date_4561_, 9);
v_w_5686_ = lean_ctor_get(v_date_4561_, 10);
v_W_5687_ = lean_ctor_get(v_date_4561_, 11);
v_E_5688_ = lean_ctor_get(v_date_4561_, 12);
v_e_5689_ = lean_ctor_get(v_date_4561_, 13);
v_c_5690_ = lean_ctor_get(v_date_4561_, 14);
v_F_5691_ = lean_ctor_get(v_date_4561_, 15);
v_a_5692_ = lean_ctor_get(v_date_4561_, 16);
v_b_5693_ = lean_ctor_get(v_date_4561_, 17);
v_B_5694_ = lean_ctor_get(v_date_4561_, 18);
v_h_5695_ = lean_ctor_get(v_date_4561_, 19);
v_K_5696_ = lean_ctor_get(v_date_4561_, 20);
v_k_5697_ = lean_ctor_get(v_date_4561_, 21);
v_m_5698_ = lean_ctor_get(v_date_4561_, 23);
v_s_5699_ = lean_ctor_get(v_date_4561_, 24);
v_S_5700_ = lean_ctor_get(v_date_4561_, 25);
v_A_5701_ = lean_ctor_get(v_date_4561_, 26);
v_n_5702_ = lean_ctor_get(v_date_4561_, 27);
v_N_5703_ = lean_ctor_get(v_date_4561_, 28);
v_V_5704_ = lean_ctor_get(v_date_4561_, 29);
v_z_5705_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5706_ = lean_ctor_get(v_date_4561_, 31);
v_v_5707_ = lean_ctor_get(v_date_4561_, 32);
v_O_5708_ = lean_ctor_get(v_date_4561_, 33);
v_X_5709_ = lean_ctor_get(v_date_4561_, 34);
v_x_5710_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5711_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5721_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5721_ == 0)
{
lean_object* v_unused_5722_; 
v_unused_5722_ = lean_ctor_get(v_date_4561_, 22);
lean_dec(v_unused_5722_);
v___x_5713_ = v_date_4561_;
v_isShared_5714_ = v_isSharedCheck_5721_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_Z_5711_);
lean_inc(v_x_5710_);
lean_inc(v_X_5709_);
lean_inc(v_O_5708_);
lean_inc(v_v_5707_);
lean_inc(v_zabbrev_5706_);
lean_inc(v_z_5705_);
lean_inc(v_V_5704_);
lean_inc(v_N_5703_);
lean_inc(v_n_5702_);
lean_inc(v_A_5701_);
lean_inc(v_S_5700_);
lean_inc(v_s_5699_);
lean_inc(v_m_5698_);
lean_inc(v_k_5697_);
lean_inc(v_K_5696_);
lean_inc(v_h_5695_);
lean_inc(v_B_5694_);
lean_inc(v_b_5693_);
lean_inc(v_a_5692_);
lean_inc(v_F_5691_);
lean_inc(v_c_5690_);
lean_inc(v_e_5689_);
lean_inc(v_E_5688_);
lean_inc(v_W_5687_);
lean_inc(v_w_5686_);
lean_inc(v_q_5685_);
lean_inc(v_Q_5684_);
lean_inc(v_d_5683_);
lean_inc(v_L_5682_);
lean_inc(v_M_5681_);
lean_inc(v_D_5680_);
lean_inc(v_Y_5679_);
lean_inc(v_u_5678_);
lean_inc(v_y_5677_);
lean_inc(v_G_5676_);
lean_dec(v_date_4561_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5721_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v___x_5716_; 
if (v_isShared_5675_ == 0)
{
lean_ctor_set_tag(v___x_5674_, 1);
lean_ctor_set(v___x_5674_, 0, v_data_4563_);
v___x_5716_ = v___x_5674_;
goto v_reusejp_5715_;
}
else
{
lean_object* v_reuseFailAlloc_5720_; 
v_reuseFailAlloc_5720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5720_, 0, v_data_4563_);
v___x_5716_ = v_reuseFailAlloc_5720_;
goto v_reusejp_5715_;
}
v_reusejp_5715_:
{
lean_object* v___x_5718_; 
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 22, v___x_5716_);
v___x_5718_ = v___x_5713_;
goto v_reusejp_5717_;
}
else
{
lean_object* v_reuseFailAlloc_5719_; 
v_reuseFailAlloc_5719_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5719_, 0, v_G_5676_);
lean_ctor_set(v_reuseFailAlloc_5719_, 1, v_y_5677_);
lean_ctor_set(v_reuseFailAlloc_5719_, 2, v_u_5678_);
lean_ctor_set(v_reuseFailAlloc_5719_, 3, v_Y_5679_);
lean_ctor_set(v_reuseFailAlloc_5719_, 4, v_D_5680_);
lean_ctor_set(v_reuseFailAlloc_5719_, 5, v_M_5681_);
lean_ctor_set(v_reuseFailAlloc_5719_, 6, v_L_5682_);
lean_ctor_set(v_reuseFailAlloc_5719_, 7, v_d_5683_);
lean_ctor_set(v_reuseFailAlloc_5719_, 8, v_Q_5684_);
lean_ctor_set(v_reuseFailAlloc_5719_, 9, v_q_5685_);
lean_ctor_set(v_reuseFailAlloc_5719_, 10, v_w_5686_);
lean_ctor_set(v_reuseFailAlloc_5719_, 11, v_W_5687_);
lean_ctor_set(v_reuseFailAlloc_5719_, 12, v_E_5688_);
lean_ctor_set(v_reuseFailAlloc_5719_, 13, v_e_5689_);
lean_ctor_set(v_reuseFailAlloc_5719_, 14, v_c_5690_);
lean_ctor_set(v_reuseFailAlloc_5719_, 15, v_F_5691_);
lean_ctor_set(v_reuseFailAlloc_5719_, 16, v_a_5692_);
lean_ctor_set(v_reuseFailAlloc_5719_, 17, v_b_5693_);
lean_ctor_set(v_reuseFailAlloc_5719_, 18, v_B_5694_);
lean_ctor_set(v_reuseFailAlloc_5719_, 19, v_h_5695_);
lean_ctor_set(v_reuseFailAlloc_5719_, 20, v_K_5696_);
lean_ctor_set(v_reuseFailAlloc_5719_, 21, v_k_5697_);
lean_ctor_set(v_reuseFailAlloc_5719_, 22, v___x_5716_);
lean_ctor_set(v_reuseFailAlloc_5719_, 23, v_m_5698_);
lean_ctor_set(v_reuseFailAlloc_5719_, 24, v_s_5699_);
lean_ctor_set(v_reuseFailAlloc_5719_, 25, v_S_5700_);
lean_ctor_set(v_reuseFailAlloc_5719_, 26, v_A_5701_);
lean_ctor_set(v_reuseFailAlloc_5719_, 27, v_n_5702_);
lean_ctor_set(v_reuseFailAlloc_5719_, 28, v_N_5703_);
lean_ctor_set(v_reuseFailAlloc_5719_, 29, v_V_5704_);
lean_ctor_set(v_reuseFailAlloc_5719_, 30, v_z_5705_);
lean_ctor_set(v_reuseFailAlloc_5719_, 31, v_zabbrev_5706_);
lean_ctor_set(v_reuseFailAlloc_5719_, 32, v_v_5707_);
lean_ctor_set(v_reuseFailAlloc_5719_, 33, v_O_5708_);
lean_ctor_set(v_reuseFailAlloc_5719_, 34, v_X_5709_);
lean_ctor_set(v_reuseFailAlloc_5719_, 35, v_x_5710_);
lean_ctor_set(v_reuseFailAlloc_5719_, 36, v_Z_5711_);
v___x_5718_ = v_reuseFailAlloc_5719_;
goto v_reusejp_5717_;
}
v_reusejp_5717_:
{
return v___x_5718_;
}
}
}
}
}
case 23:
{
lean_object* v___x_5726_; uint8_t v_isShared_5727_; uint8_t v_isSharedCheck_5775_; 
v_isSharedCheck_5775_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5775_ == 0)
{
lean_object* v_unused_5776_; 
v_unused_5776_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5776_);
v___x_5726_ = v_modifier_4562_;
v_isShared_5727_ = v_isSharedCheck_5775_;
goto v_resetjp_5725_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5726_ = lean_box(0);
v_isShared_5727_ = v_isSharedCheck_5775_;
goto v_resetjp_5725_;
}
v_resetjp_5725_:
{
lean_object* v_G_5728_; lean_object* v_y_5729_; lean_object* v_u_5730_; lean_object* v_Y_5731_; lean_object* v_D_5732_; lean_object* v_M_5733_; lean_object* v_L_5734_; lean_object* v_d_5735_; lean_object* v_Q_5736_; lean_object* v_q_5737_; lean_object* v_w_5738_; lean_object* v_W_5739_; lean_object* v_E_5740_; lean_object* v_e_5741_; lean_object* v_c_5742_; lean_object* v_F_5743_; lean_object* v_a_5744_; lean_object* v_b_5745_; lean_object* v_B_5746_; lean_object* v_h_5747_; lean_object* v_K_5748_; lean_object* v_k_5749_; lean_object* v_H_5750_; lean_object* v_s_5751_; lean_object* v_S_5752_; lean_object* v_A_5753_; lean_object* v_n_5754_; lean_object* v_N_5755_; lean_object* v_V_5756_; lean_object* v_z_5757_; lean_object* v_zabbrev_5758_; lean_object* v_v_5759_; lean_object* v_O_5760_; lean_object* v_X_5761_; lean_object* v_x_5762_; lean_object* v_Z_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5773_; 
v_G_5728_ = lean_ctor_get(v_date_4561_, 0);
v_y_5729_ = lean_ctor_get(v_date_4561_, 1);
v_u_5730_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5731_ = lean_ctor_get(v_date_4561_, 3);
v_D_5732_ = lean_ctor_get(v_date_4561_, 4);
v_M_5733_ = lean_ctor_get(v_date_4561_, 5);
v_L_5734_ = lean_ctor_get(v_date_4561_, 6);
v_d_5735_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5736_ = lean_ctor_get(v_date_4561_, 8);
v_q_5737_ = lean_ctor_get(v_date_4561_, 9);
v_w_5738_ = lean_ctor_get(v_date_4561_, 10);
v_W_5739_ = lean_ctor_get(v_date_4561_, 11);
v_E_5740_ = lean_ctor_get(v_date_4561_, 12);
v_e_5741_ = lean_ctor_get(v_date_4561_, 13);
v_c_5742_ = lean_ctor_get(v_date_4561_, 14);
v_F_5743_ = lean_ctor_get(v_date_4561_, 15);
v_a_5744_ = lean_ctor_get(v_date_4561_, 16);
v_b_5745_ = lean_ctor_get(v_date_4561_, 17);
v_B_5746_ = lean_ctor_get(v_date_4561_, 18);
v_h_5747_ = lean_ctor_get(v_date_4561_, 19);
v_K_5748_ = lean_ctor_get(v_date_4561_, 20);
v_k_5749_ = lean_ctor_get(v_date_4561_, 21);
v_H_5750_ = lean_ctor_get(v_date_4561_, 22);
v_s_5751_ = lean_ctor_get(v_date_4561_, 24);
v_S_5752_ = lean_ctor_get(v_date_4561_, 25);
v_A_5753_ = lean_ctor_get(v_date_4561_, 26);
v_n_5754_ = lean_ctor_get(v_date_4561_, 27);
v_N_5755_ = lean_ctor_get(v_date_4561_, 28);
v_V_5756_ = lean_ctor_get(v_date_4561_, 29);
v_z_5757_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5758_ = lean_ctor_get(v_date_4561_, 31);
v_v_5759_ = lean_ctor_get(v_date_4561_, 32);
v_O_5760_ = lean_ctor_get(v_date_4561_, 33);
v_X_5761_ = lean_ctor_get(v_date_4561_, 34);
v_x_5762_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5763_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5773_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5773_ == 0)
{
lean_object* v_unused_5774_; 
v_unused_5774_ = lean_ctor_get(v_date_4561_, 23);
lean_dec(v_unused_5774_);
v___x_5765_ = v_date_4561_;
v_isShared_5766_ = v_isSharedCheck_5773_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_Z_5763_);
lean_inc(v_x_5762_);
lean_inc(v_X_5761_);
lean_inc(v_O_5760_);
lean_inc(v_v_5759_);
lean_inc(v_zabbrev_5758_);
lean_inc(v_z_5757_);
lean_inc(v_V_5756_);
lean_inc(v_N_5755_);
lean_inc(v_n_5754_);
lean_inc(v_A_5753_);
lean_inc(v_S_5752_);
lean_inc(v_s_5751_);
lean_inc(v_H_5750_);
lean_inc(v_k_5749_);
lean_inc(v_K_5748_);
lean_inc(v_h_5747_);
lean_inc(v_B_5746_);
lean_inc(v_b_5745_);
lean_inc(v_a_5744_);
lean_inc(v_F_5743_);
lean_inc(v_c_5742_);
lean_inc(v_e_5741_);
lean_inc(v_E_5740_);
lean_inc(v_W_5739_);
lean_inc(v_w_5738_);
lean_inc(v_q_5737_);
lean_inc(v_Q_5736_);
lean_inc(v_d_5735_);
lean_inc(v_L_5734_);
lean_inc(v_M_5733_);
lean_inc(v_D_5732_);
lean_inc(v_Y_5731_);
lean_inc(v_u_5730_);
lean_inc(v_y_5729_);
lean_inc(v_G_5728_);
lean_dec(v_date_4561_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5773_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v___x_5768_; 
if (v_isShared_5727_ == 0)
{
lean_ctor_set_tag(v___x_5726_, 1);
lean_ctor_set(v___x_5726_, 0, v_data_4563_);
v___x_5768_ = v___x_5726_;
goto v_reusejp_5767_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_data_4563_);
v___x_5768_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5767_;
}
v_reusejp_5767_:
{
lean_object* v___x_5770_; 
if (v_isShared_5766_ == 0)
{
lean_ctor_set(v___x_5765_, 23, v___x_5768_);
v___x_5770_ = v___x_5765_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_G_5728_);
lean_ctor_set(v_reuseFailAlloc_5771_, 1, v_y_5729_);
lean_ctor_set(v_reuseFailAlloc_5771_, 2, v_u_5730_);
lean_ctor_set(v_reuseFailAlloc_5771_, 3, v_Y_5731_);
lean_ctor_set(v_reuseFailAlloc_5771_, 4, v_D_5732_);
lean_ctor_set(v_reuseFailAlloc_5771_, 5, v_M_5733_);
lean_ctor_set(v_reuseFailAlloc_5771_, 6, v_L_5734_);
lean_ctor_set(v_reuseFailAlloc_5771_, 7, v_d_5735_);
lean_ctor_set(v_reuseFailAlloc_5771_, 8, v_Q_5736_);
lean_ctor_set(v_reuseFailAlloc_5771_, 9, v_q_5737_);
lean_ctor_set(v_reuseFailAlloc_5771_, 10, v_w_5738_);
lean_ctor_set(v_reuseFailAlloc_5771_, 11, v_W_5739_);
lean_ctor_set(v_reuseFailAlloc_5771_, 12, v_E_5740_);
lean_ctor_set(v_reuseFailAlloc_5771_, 13, v_e_5741_);
lean_ctor_set(v_reuseFailAlloc_5771_, 14, v_c_5742_);
lean_ctor_set(v_reuseFailAlloc_5771_, 15, v_F_5743_);
lean_ctor_set(v_reuseFailAlloc_5771_, 16, v_a_5744_);
lean_ctor_set(v_reuseFailAlloc_5771_, 17, v_b_5745_);
lean_ctor_set(v_reuseFailAlloc_5771_, 18, v_B_5746_);
lean_ctor_set(v_reuseFailAlloc_5771_, 19, v_h_5747_);
lean_ctor_set(v_reuseFailAlloc_5771_, 20, v_K_5748_);
lean_ctor_set(v_reuseFailAlloc_5771_, 21, v_k_5749_);
lean_ctor_set(v_reuseFailAlloc_5771_, 22, v_H_5750_);
lean_ctor_set(v_reuseFailAlloc_5771_, 23, v___x_5768_);
lean_ctor_set(v_reuseFailAlloc_5771_, 24, v_s_5751_);
lean_ctor_set(v_reuseFailAlloc_5771_, 25, v_S_5752_);
lean_ctor_set(v_reuseFailAlloc_5771_, 26, v_A_5753_);
lean_ctor_set(v_reuseFailAlloc_5771_, 27, v_n_5754_);
lean_ctor_set(v_reuseFailAlloc_5771_, 28, v_N_5755_);
lean_ctor_set(v_reuseFailAlloc_5771_, 29, v_V_5756_);
lean_ctor_set(v_reuseFailAlloc_5771_, 30, v_z_5757_);
lean_ctor_set(v_reuseFailAlloc_5771_, 31, v_zabbrev_5758_);
lean_ctor_set(v_reuseFailAlloc_5771_, 32, v_v_5759_);
lean_ctor_set(v_reuseFailAlloc_5771_, 33, v_O_5760_);
lean_ctor_set(v_reuseFailAlloc_5771_, 34, v_X_5761_);
lean_ctor_set(v_reuseFailAlloc_5771_, 35, v_x_5762_);
lean_ctor_set(v_reuseFailAlloc_5771_, 36, v_Z_5763_);
v___x_5770_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
return v___x_5770_;
}
}
}
}
}
case 24:
{
lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5827_; 
v_isSharedCheck_5827_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5827_ == 0)
{
lean_object* v_unused_5828_; 
v_unused_5828_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5828_);
v___x_5778_ = v_modifier_4562_;
v_isShared_5779_ = v_isSharedCheck_5827_;
goto v_resetjp_5777_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5827_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v_G_5780_; lean_object* v_y_5781_; lean_object* v_u_5782_; lean_object* v_Y_5783_; lean_object* v_D_5784_; lean_object* v_M_5785_; lean_object* v_L_5786_; lean_object* v_d_5787_; lean_object* v_Q_5788_; lean_object* v_q_5789_; lean_object* v_w_5790_; lean_object* v_W_5791_; lean_object* v_E_5792_; lean_object* v_e_5793_; lean_object* v_c_5794_; lean_object* v_F_5795_; lean_object* v_a_5796_; lean_object* v_b_5797_; lean_object* v_B_5798_; lean_object* v_h_5799_; lean_object* v_K_5800_; lean_object* v_k_5801_; lean_object* v_H_5802_; lean_object* v_m_5803_; lean_object* v_S_5804_; lean_object* v_A_5805_; lean_object* v_n_5806_; lean_object* v_N_5807_; lean_object* v_V_5808_; lean_object* v_z_5809_; lean_object* v_zabbrev_5810_; lean_object* v_v_5811_; lean_object* v_O_5812_; lean_object* v_X_5813_; lean_object* v_x_5814_; lean_object* v_Z_5815_; lean_object* v___x_5817_; uint8_t v_isShared_5818_; uint8_t v_isSharedCheck_5825_; 
v_G_5780_ = lean_ctor_get(v_date_4561_, 0);
v_y_5781_ = lean_ctor_get(v_date_4561_, 1);
v_u_5782_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5783_ = lean_ctor_get(v_date_4561_, 3);
v_D_5784_ = lean_ctor_get(v_date_4561_, 4);
v_M_5785_ = lean_ctor_get(v_date_4561_, 5);
v_L_5786_ = lean_ctor_get(v_date_4561_, 6);
v_d_5787_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5788_ = lean_ctor_get(v_date_4561_, 8);
v_q_5789_ = lean_ctor_get(v_date_4561_, 9);
v_w_5790_ = lean_ctor_get(v_date_4561_, 10);
v_W_5791_ = lean_ctor_get(v_date_4561_, 11);
v_E_5792_ = lean_ctor_get(v_date_4561_, 12);
v_e_5793_ = lean_ctor_get(v_date_4561_, 13);
v_c_5794_ = lean_ctor_get(v_date_4561_, 14);
v_F_5795_ = lean_ctor_get(v_date_4561_, 15);
v_a_5796_ = lean_ctor_get(v_date_4561_, 16);
v_b_5797_ = lean_ctor_get(v_date_4561_, 17);
v_B_5798_ = lean_ctor_get(v_date_4561_, 18);
v_h_5799_ = lean_ctor_get(v_date_4561_, 19);
v_K_5800_ = lean_ctor_get(v_date_4561_, 20);
v_k_5801_ = lean_ctor_get(v_date_4561_, 21);
v_H_5802_ = lean_ctor_get(v_date_4561_, 22);
v_m_5803_ = lean_ctor_get(v_date_4561_, 23);
v_S_5804_ = lean_ctor_get(v_date_4561_, 25);
v_A_5805_ = lean_ctor_get(v_date_4561_, 26);
v_n_5806_ = lean_ctor_get(v_date_4561_, 27);
v_N_5807_ = lean_ctor_get(v_date_4561_, 28);
v_V_5808_ = lean_ctor_get(v_date_4561_, 29);
v_z_5809_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5810_ = lean_ctor_get(v_date_4561_, 31);
v_v_5811_ = lean_ctor_get(v_date_4561_, 32);
v_O_5812_ = lean_ctor_get(v_date_4561_, 33);
v_X_5813_ = lean_ctor_get(v_date_4561_, 34);
v_x_5814_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5815_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5825_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5825_ == 0)
{
lean_object* v_unused_5826_; 
v_unused_5826_ = lean_ctor_get(v_date_4561_, 24);
lean_dec(v_unused_5826_);
v___x_5817_ = v_date_4561_;
v_isShared_5818_ = v_isSharedCheck_5825_;
goto v_resetjp_5816_;
}
else
{
lean_inc(v_Z_5815_);
lean_inc(v_x_5814_);
lean_inc(v_X_5813_);
lean_inc(v_O_5812_);
lean_inc(v_v_5811_);
lean_inc(v_zabbrev_5810_);
lean_inc(v_z_5809_);
lean_inc(v_V_5808_);
lean_inc(v_N_5807_);
lean_inc(v_n_5806_);
lean_inc(v_A_5805_);
lean_inc(v_S_5804_);
lean_inc(v_m_5803_);
lean_inc(v_H_5802_);
lean_inc(v_k_5801_);
lean_inc(v_K_5800_);
lean_inc(v_h_5799_);
lean_inc(v_B_5798_);
lean_inc(v_b_5797_);
lean_inc(v_a_5796_);
lean_inc(v_F_5795_);
lean_inc(v_c_5794_);
lean_inc(v_e_5793_);
lean_inc(v_E_5792_);
lean_inc(v_W_5791_);
lean_inc(v_w_5790_);
lean_inc(v_q_5789_);
lean_inc(v_Q_5788_);
lean_inc(v_d_5787_);
lean_inc(v_L_5786_);
lean_inc(v_M_5785_);
lean_inc(v_D_5784_);
lean_inc(v_Y_5783_);
lean_inc(v_u_5782_);
lean_inc(v_y_5781_);
lean_inc(v_G_5780_);
lean_dec(v_date_4561_);
v___x_5817_ = lean_box(0);
v_isShared_5818_ = v_isSharedCheck_5825_;
goto v_resetjp_5816_;
}
v_resetjp_5816_:
{
lean_object* v___x_5820_; 
if (v_isShared_5779_ == 0)
{
lean_ctor_set_tag(v___x_5778_, 1);
lean_ctor_set(v___x_5778_, 0, v_data_4563_);
v___x_5820_ = v___x_5778_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_data_4563_);
v___x_5820_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
lean_object* v___x_5822_; 
if (v_isShared_5818_ == 0)
{
lean_ctor_set(v___x_5817_, 24, v___x_5820_);
v___x_5822_ = v___x_5817_;
goto v_reusejp_5821_;
}
else
{
lean_object* v_reuseFailAlloc_5823_; 
v_reuseFailAlloc_5823_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5823_, 0, v_G_5780_);
lean_ctor_set(v_reuseFailAlloc_5823_, 1, v_y_5781_);
lean_ctor_set(v_reuseFailAlloc_5823_, 2, v_u_5782_);
lean_ctor_set(v_reuseFailAlloc_5823_, 3, v_Y_5783_);
lean_ctor_set(v_reuseFailAlloc_5823_, 4, v_D_5784_);
lean_ctor_set(v_reuseFailAlloc_5823_, 5, v_M_5785_);
lean_ctor_set(v_reuseFailAlloc_5823_, 6, v_L_5786_);
lean_ctor_set(v_reuseFailAlloc_5823_, 7, v_d_5787_);
lean_ctor_set(v_reuseFailAlloc_5823_, 8, v_Q_5788_);
lean_ctor_set(v_reuseFailAlloc_5823_, 9, v_q_5789_);
lean_ctor_set(v_reuseFailAlloc_5823_, 10, v_w_5790_);
lean_ctor_set(v_reuseFailAlloc_5823_, 11, v_W_5791_);
lean_ctor_set(v_reuseFailAlloc_5823_, 12, v_E_5792_);
lean_ctor_set(v_reuseFailAlloc_5823_, 13, v_e_5793_);
lean_ctor_set(v_reuseFailAlloc_5823_, 14, v_c_5794_);
lean_ctor_set(v_reuseFailAlloc_5823_, 15, v_F_5795_);
lean_ctor_set(v_reuseFailAlloc_5823_, 16, v_a_5796_);
lean_ctor_set(v_reuseFailAlloc_5823_, 17, v_b_5797_);
lean_ctor_set(v_reuseFailAlloc_5823_, 18, v_B_5798_);
lean_ctor_set(v_reuseFailAlloc_5823_, 19, v_h_5799_);
lean_ctor_set(v_reuseFailAlloc_5823_, 20, v_K_5800_);
lean_ctor_set(v_reuseFailAlloc_5823_, 21, v_k_5801_);
lean_ctor_set(v_reuseFailAlloc_5823_, 22, v_H_5802_);
lean_ctor_set(v_reuseFailAlloc_5823_, 23, v_m_5803_);
lean_ctor_set(v_reuseFailAlloc_5823_, 24, v___x_5820_);
lean_ctor_set(v_reuseFailAlloc_5823_, 25, v_S_5804_);
lean_ctor_set(v_reuseFailAlloc_5823_, 26, v_A_5805_);
lean_ctor_set(v_reuseFailAlloc_5823_, 27, v_n_5806_);
lean_ctor_set(v_reuseFailAlloc_5823_, 28, v_N_5807_);
lean_ctor_set(v_reuseFailAlloc_5823_, 29, v_V_5808_);
lean_ctor_set(v_reuseFailAlloc_5823_, 30, v_z_5809_);
lean_ctor_set(v_reuseFailAlloc_5823_, 31, v_zabbrev_5810_);
lean_ctor_set(v_reuseFailAlloc_5823_, 32, v_v_5811_);
lean_ctor_set(v_reuseFailAlloc_5823_, 33, v_O_5812_);
lean_ctor_set(v_reuseFailAlloc_5823_, 34, v_X_5813_);
lean_ctor_set(v_reuseFailAlloc_5823_, 35, v_x_5814_);
lean_ctor_set(v_reuseFailAlloc_5823_, 36, v_Z_5815_);
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
}
case 25:
{
lean_object* v___x_5830_; uint8_t v_isShared_5831_; uint8_t v_isSharedCheck_5879_; 
v_isSharedCheck_5879_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5879_ == 0)
{
lean_object* v_unused_5880_; 
v_unused_5880_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5880_);
v___x_5830_ = v_modifier_4562_;
v_isShared_5831_ = v_isSharedCheck_5879_;
goto v_resetjp_5829_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5830_ = lean_box(0);
v_isShared_5831_ = v_isSharedCheck_5879_;
goto v_resetjp_5829_;
}
v_resetjp_5829_:
{
lean_object* v_G_5832_; lean_object* v_y_5833_; lean_object* v_u_5834_; lean_object* v_Y_5835_; lean_object* v_D_5836_; lean_object* v_M_5837_; lean_object* v_L_5838_; lean_object* v_d_5839_; lean_object* v_Q_5840_; lean_object* v_q_5841_; lean_object* v_w_5842_; lean_object* v_W_5843_; lean_object* v_E_5844_; lean_object* v_e_5845_; lean_object* v_c_5846_; lean_object* v_F_5847_; lean_object* v_a_5848_; lean_object* v_b_5849_; lean_object* v_B_5850_; lean_object* v_h_5851_; lean_object* v_K_5852_; lean_object* v_k_5853_; lean_object* v_H_5854_; lean_object* v_m_5855_; lean_object* v_s_5856_; lean_object* v_A_5857_; lean_object* v_n_5858_; lean_object* v_N_5859_; lean_object* v_V_5860_; lean_object* v_z_5861_; lean_object* v_zabbrev_5862_; lean_object* v_v_5863_; lean_object* v_O_5864_; lean_object* v_X_5865_; lean_object* v_x_5866_; lean_object* v_Z_5867_; lean_object* v___x_5869_; uint8_t v_isShared_5870_; uint8_t v_isSharedCheck_5877_; 
v_G_5832_ = lean_ctor_get(v_date_4561_, 0);
v_y_5833_ = lean_ctor_get(v_date_4561_, 1);
v_u_5834_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5835_ = lean_ctor_get(v_date_4561_, 3);
v_D_5836_ = lean_ctor_get(v_date_4561_, 4);
v_M_5837_ = lean_ctor_get(v_date_4561_, 5);
v_L_5838_ = lean_ctor_get(v_date_4561_, 6);
v_d_5839_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5840_ = lean_ctor_get(v_date_4561_, 8);
v_q_5841_ = lean_ctor_get(v_date_4561_, 9);
v_w_5842_ = lean_ctor_get(v_date_4561_, 10);
v_W_5843_ = lean_ctor_get(v_date_4561_, 11);
v_E_5844_ = lean_ctor_get(v_date_4561_, 12);
v_e_5845_ = lean_ctor_get(v_date_4561_, 13);
v_c_5846_ = lean_ctor_get(v_date_4561_, 14);
v_F_5847_ = lean_ctor_get(v_date_4561_, 15);
v_a_5848_ = lean_ctor_get(v_date_4561_, 16);
v_b_5849_ = lean_ctor_get(v_date_4561_, 17);
v_B_5850_ = lean_ctor_get(v_date_4561_, 18);
v_h_5851_ = lean_ctor_get(v_date_4561_, 19);
v_K_5852_ = lean_ctor_get(v_date_4561_, 20);
v_k_5853_ = lean_ctor_get(v_date_4561_, 21);
v_H_5854_ = lean_ctor_get(v_date_4561_, 22);
v_m_5855_ = lean_ctor_get(v_date_4561_, 23);
v_s_5856_ = lean_ctor_get(v_date_4561_, 24);
v_A_5857_ = lean_ctor_get(v_date_4561_, 26);
v_n_5858_ = lean_ctor_get(v_date_4561_, 27);
v_N_5859_ = lean_ctor_get(v_date_4561_, 28);
v_V_5860_ = lean_ctor_get(v_date_4561_, 29);
v_z_5861_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5862_ = lean_ctor_get(v_date_4561_, 31);
v_v_5863_ = lean_ctor_get(v_date_4561_, 32);
v_O_5864_ = lean_ctor_get(v_date_4561_, 33);
v_X_5865_ = lean_ctor_get(v_date_4561_, 34);
v_x_5866_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5867_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5877_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5877_ == 0)
{
lean_object* v_unused_5878_; 
v_unused_5878_ = lean_ctor_get(v_date_4561_, 25);
lean_dec(v_unused_5878_);
v___x_5869_ = v_date_4561_;
v_isShared_5870_ = v_isSharedCheck_5877_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_Z_5867_);
lean_inc(v_x_5866_);
lean_inc(v_X_5865_);
lean_inc(v_O_5864_);
lean_inc(v_v_5863_);
lean_inc(v_zabbrev_5862_);
lean_inc(v_z_5861_);
lean_inc(v_V_5860_);
lean_inc(v_N_5859_);
lean_inc(v_n_5858_);
lean_inc(v_A_5857_);
lean_inc(v_s_5856_);
lean_inc(v_m_5855_);
lean_inc(v_H_5854_);
lean_inc(v_k_5853_);
lean_inc(v_K_5852_);
lean_inc(v_h_5851_);
lean_inc(v_B_5850_);
lean_inc(v_b_5849_);
lean_inc(v_a_5848_);
lean_inc(v_F_5847_);
lean_inc(v_c_5846_);
lean_inc(v_e_5845_);
lean_inc(v_E_5844_);
lean_inc(v_W_5843_);
lean_inc(v_w_5842_);
lean_inc(v_q_5841_);
lean_inc(v_Q_5840_);
lean_inc(v_d_5839_);
lean_inc(v_L_5838_);
lean_inc(v_M_5837_);
lean_inc(v_D_5836_);
lean_inc(v_Y_5835_);
lean_inc(v_u_5834_);
lean_inc(v_y_5833_);
lean_inc(v_G_5832_);
lean_dec(v_date_4561_);
v___x_5869_ = lean_box(0);
v_isShared_5870_ = v_isSharedCheck_5877_;
goto v_resetjp_5868_;
}
v_resetjp_5868_:
{
lean_object* v___x_5872_; 
if (v_isShared_5831_ == 0)
{
lean_ctor_set_tag(v___x_5830_, 1);
lean_ctor_set(v___x_5830_, 0, v_data_4563_);
v___x_5872_ = v___x_5830_;
goto v_reusejp_5871_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_data_4563_);
v___x_5872_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5871_;
}
v_reusejp_5871_:
{
lean_object* v___x_5874_; 
if (v_isShared_5870_ == 0)
{
lean_ctor_set(v___x_5869_, 25, v___x_5872_);
v___x_5874_ = v___x_5869_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_G_5832_);
lean_ctor_set(v_reuseFailAlloc_5875_, 1, v_y_5833_);
lean_ctor_set(v_reuseFailAlloc_5875_, 2, v_u_5834_);
lean_ctor_set(v_reuseFailAlloc_5875_, 3, v_Y_5835_);
lean_ctor_set(v_reuseFailAlloc_5875_, 4, v_D_5836_);
lean_ctor_set(v_reuseFailAlloc_5875_, 5, v_M_5837_);
lean_ctor_set(v_reuseFailAlloc_5875_, 6, v_L_5838_);
lean_ctor_set(v_reuseFailAlloc_5875_, 7, v_d_5839_);
lean_ctor_set(v_reuseFailAlloc_5875_, 8, v_Q_5840_);
lean_ctor_set(v_reuseFailAlloc_5875_, 9, v_q_5841_);
lean_ctor_set(v_reuseFailAlloc_5875_, 10, v_w_5842_);
lean_ctor_set(v_reuseFailAlloc_5875_, 11, v_W_5843_);
lean_ctor_set(v_reuseFailAlloc_5875_, 12, v_E_5844_);
lean_ctor_set(v_reuseFailAlloc_5875_, 13, v_e_5845_);
lean_ctor_set(v_reuseFailAlloc_5875_, 14, v_c_5846_);
lean_ctor_set(v_reuseFailAlloc_5875_, 15, v_F_5847_);
lean_ctor_set(v_reuseFailAlloc_5875_, 16, v_a_5848_);
lean_ctor_set(v_reuseFailAlloc_5875_, 17, v_b_5849_);
lean_ctor_set(v_reuseFailAlloc_5875_, 18, v_B_5850_);
lean_ctor_set(v_reuseFailAlloc_5875_, 19, v_h_5851_);
lean_ctor_set(v_reuseFailAlloc_5875_, 20, v_K_5852_);
lean_ctor_set(v_reuseFailAlloc_5875_, 21, v_k_5853_);
lean_ctor_set(v_reuseFailAlloc_5875_, 22, v_H_5854_);
lean_ctor_set(v_reuseFailAlloc_5875_, 23, v_m_5855_);
lean_ctor_set(v_reuseFailAlloc_5875_, 24, v_s_5856_);
lean_ctor_set(v_reuseFailAlloc_5875_, 25, v___x_5872_);
lean_ctor_set(v_reuseFailAlloc_5875_, 26, v_A_5857_);
lean_ctor_set(v_reuseFailAlloc_5875_, 27, v_n_5858_);
lean_ctor_set(v_reuseFailAlloc_5875_, 28, v_N_5859_);
lean_ctor_set(v_reuseFailAlloc_5875_, 29, v_V_5860_);
lean_ctor_set(v_reuseFailAlloc_5875_, 30, v_z_5861_);
lean_ctor_set(v_reuseFailAlloc_5875_, 31, v_zabbrev_5862_);
lean_ctor_set(v_reuseFailAlloc_5875_, 32, v_v_5863_);
lean_ctor_set(v_reuseFailAlloc_5875_, 33, v_O_5864_);
lean_ctor_set(v_reuseFailAlloc_5875_, 34, v_X_5865_);
lean_ctor_set(v_reuseFailAlloc_5875_, 35, v_x_5866_);
lean_ctor_set(v_reuseFailAlloc_5875_, 36, v_Z_5867_);
v___x_5874_ = v_reuseFailAlloc_5875_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
return v___x_5874_;
}
}
}
}
}
case 26:
{
lean_object* v___x_5882_; uint8_t v_isShared_5883_; uint8_t v_isSharedCheck_5931_; 
v_isSharedCheck_5931_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5931_ == 0)
{
lean_object* v_unused_5932_; 
v_unused_5932_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5932_);
v___x_5882_ = v_modifier_4562_;
v_isShared_5883_ = v_isSharedCheck_5931_;
goto v_resetjp_5881_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5882_ = lean_box(0);
v_isShared_5883_ = v_isSharedCheck_5931_;
goto v_resetjp_5881_;
}
v_resetjp_5881_:
{
lean_object* v_G_5884_; lean_object* v_y_5885_; lean_object* v_u_5886_; lean_object* v_Y_5887_; lean_object* v_D_5888_; lean_object* v_M_5889_; lean_object* v_L_5890_; lean_object* v_d_5891_; lean_object* v_Q_5892_; lean_object* v_q_5893_; lean_object* v_w_5894_; lean_object* v_W_5895_; lean_object* v_E_5896_; lean_object* v_e_5897_; lean_object* v_c_5898_; lean_object* v_F_5899_; lean_object* v_a_5900_; lean_object* v_b_5901_; lean_object* v_B_5902_; lean_object* v_h_5903_; lean_object* v_K_5904_; lean_object* v_k_5905_; lean_object* v_H_5906_; lean_object* v_m_5907_; lean_object* v_s_5908_; lean_object* v_S_5909_; lean_object* v_n_5910_; lean_object* v_N_5911_; lean_object* v_V_5912_; lean_object* v_z_5913_; lean_object* v_zabbrev_5914_; lean_object* v_v_5915_; lean_object* v_O_5916_; lean_object* v_X_5917_; lean_object* v_x_5918_; lean_object* v_Z_5919_; lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_5929_; 
v_G_5884_ = lean_ctor_get(v_date_4561_, 0);
v_y_5885_ = lean_ctor_get(v_date_4561_, 1);
v_u_5886_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5887_ = lean_ctor_get(v_date_4561_, 3);
v_D_5888_ = lean_ctor_get(v_date_4561_, 4);
v_M_5889_ = lean_ctor_get(v_date_4561_, 5);
v_L_5890_ = lean_ctor_get(v_date_4561_, 6);
v_d_5891_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5892_ = lean_ctor_get(v_date_4561_, 8);
v_q_5893_ = lean_ctor_get(v_date_4561_, 9);
v_w_5894_ = lean_ctor_get(v_date_4561_, 10);
v_W_5895_ = lean_ctor_get(v_date_4561_, 11);
v_E_5896_ = lean_ctor_get(v_date_4561_, 12);
v_e_5897_ = lean_ctor_get(v_date_4561_, 13);
v_c_5898_ = lean_ctor_get(v_date_4561_, 14);
v_F_5899_ = lean_ctor_get(v_date_4561_, 15);
v_a_5900_ = lean_ctor_get(v_date_4561_, 16);
v_b_5901_ = lean_ctor_get(v_date_4561_, 17);
v_B_5902_ = lean_ctor_get(v_date_4561_, 18);
v_h_5903_ = lean_ctor_get(v_date_4561_, 19);
v_K_5904_ = lean_ctor_get(v_date_4561_, 20);
v_k_5905_ = lean_ctor_get(v_date_4561_, 21);
v_H_5906_ = lean_ctor_get(v_date_4561_, 22);
v_m_5907_ = lean_ctor_get(v_date_4561_, 23);
v_s_5908_ = lean_ctor_get(v_date_4561_, 24);
v_S_5909_ = lean_ctor_get(v_date_4561_, 25);
v_n_5910_ = lean_ctor_get(v_date_4561_, 27);
v_N_5911_ = lean_ctor_get(v_date_4561_, 28);
v_V_5912_ = lean_ctor_get(v_date_4561_, 29);
v_z_5913_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5914_ = lean_ctor_get(v_date_4561_, 31);
v_v_5915_ = lean_ctor_get(v_date_4561_, 32);
v_O_5916_ = lean_ctor_get(v_date_4561_, 33);
v_X_5917_ = lean_ctor_get(v_date_4561_, 34);
v_x_5918_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5919_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5929_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5929_ == 0)
{
lean_object* v_unused_5930_; 
v_unused_5930_ = lean_ctor_get(v_date_4561_, 26);
lean_dec(v_unused_5930_);
v___x_5921_ = v_date_4561_;
v_isShared_5922_ = v_isSharedCheck_5929_;
goto v_resetjp_5920_;
}
else
{
lean_inc(v_Z_5919_);
lean_inc(v_x_5918_);
lean_inc(v_X_5917_);
lean_inc(v_O_5916_);
lean_inc(v_v_5915_);
lean_inc(v_zabbrev_5914_);
lean_inc(v_z_5913_);
lean_inc(v_V_5912_);
lean_inc(v_N_5911_);
lean_inc(v_n_5910_);
lean_inc(v_S_5909_);
lean_inc(v_s_5908_);
lean_inc(v_m_5907_);
lean_inc(v_H_5906_);
lean_inc(v_k_5905_);
lean_inc(v_K_5904_);
lean_inc(v_h_5903_);
lean_inc(v_B_5902_);
lean_inc(v_b_5901_);
lean_inc(v_a_5900_);
lean_inc(v_F_5899_);
lean_inc(v_c_5898_);
lean_inc(v_e_5897_);
lean_inc(v_E_5896_);
lean_inc(v_W_5895_);
lean_inc(v_w_5894_);
lean_inc(v_q_5893_);
lean_inc(v_Q_5892_);
lean_inc(v_d_5891_);
lean_inc(v_L_5890_);
lean_inc(v_M_5889_);
lean_inc(v_D_5888_);
lean_inc(v_Y_5887_);
lean_inc(v_u_5886_);
lean_inc(v_y_5885_);
lean_inc(v_G_5884_);
lean_dec(v_date_4561_);
v___x_5921_ = lean_box(0);
v_isShared_5922_ = v_isSharedCheck_5929_;
goto v_resetjp_5920_;
}
v_resetjp_5920_:
{
lean_object* v___x_5924_; 
if (v_isShared_5883_ == 0)
{
lean_ctor_set_tag(v___x_5882_, 1);
lean_ctor_set(v___x_5882_, 0, v_data_4563_);
v___x_5924_ = v___x_5882_;
goto v_reusejp_5923_;
}
else
{
lean_object* v_reuseFailAlloc_5928_; 
v_reuseFailAlloc_5928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5928_, 0, v_data_4563_);
v___x_5924_ = v_reuseFailAlloc_5928_;
goto v_reusejp_5923_;
}
v_reusejp_5923_:
{
lean_object* v___x_5926_; 
if (v_isShared_5922_ == 0)
{
lean_ctor_set(v___x_5921_, 26, v___x_5924_);
v___x_5926_ = v___x_5921_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5927_; 
v_reuseFailAlloc_5927_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_G_5884_);
lean_ctor_set(v_reuseFailAlloc_5927_, 1, v_y_5885_);
lean_ctor_set(v_reuseFailAlloc_5927_, 2, v_u_5886_);
lean_ctor_set(v_reuseFailAlloc_5927_, 3, v_Y_5887_);
lean_ctor_set(v_reuseFailAlloc_5927_, 4, v_D_5888_);
lean_ctor_set(v_reuseFailAlloc_5927_, 5, v_M_5889_);
lean_ctor_set(v_reuseFailAlloc_5927_, 6, v_L_5890_);
lean_ctor_set(v_reuseFailAlloc_5927_, 7, v_d_5891_);
lean_ctor_set(v_reuseFailAlloc_5927_, 8, v_Q_5892_);
lean_ctor_set(v_reuseFailAlloc_5927_, 9, v_q_5893_);
lean_ctor_set(v_reuseFailAlloc_5927_, 10, v_w_5894_);
lean_ctor_set(v_reuseFailAlloc_5927_, 11, v_W_5895_);
lean_ctor_set(v_reuseFailAlloc_5927_, 12, v_E_5896_);
lean_ctor_set(v_reuseFailAlloc_5927_, 13, v_e_5897_);
lean_ctor_set(v_reuseFailAlloc_5927_, 14, v_c_5898_);
lean_ctor_set(v_reuseFailAlloc_5927_, 15, v_F_5899_);
lean_ctor_set(v_reuseFailAlloc_5927_, 16, v_a_5900_);
lean_ctor_set(v_reuseFailAlloc_5927_, 17, v_b_5901_);
lean_ctor_set(v_reuseFailAlloc_5927_, 18, v_B_5902_);
lean_ctor_set(v_reuseFailAlloc_5927_, 19, v_h_5903_);
lean_ctor_set(v_reuseFailAlloc_5927_, 20, v_K_5904_);
lean_ctor_set(v_reuseFailAlloc_5927_, 21, v_k_5905_);
lean_ctor_set(v_reuseFailAlloc_5927_, 22, v_H_5906_);
lean_ctor_set(v_reuseFailAlloc_5927_, 23, v_m_5907_);
lean_ctor_set(v_reuseFailAlloc_5927_, 24, v_s_5908_);
lean_ctor_set(v_reuseFailAlloc_5927_, 25, v_S_5909_);
lean_ctor_set(v_reuseFailAlloc_5927_, 26, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_5927_, 27, v_n_5910_);
lean_ctor_set(v_reuseFailAlloc_5927_, 28, v_N_5911_);
lean_ctor_set(v_reuseFailAlloc_5927_, 29, v_V_5912_);
lean_ctor_set(v_reuseFailAlloc_5927_, 30, v_z_5913_);
lean_ctor_set(v_reuseFailAlloc_5927_, 31, v_zabbrev_5914_);
lean_ctor_set(v_reuseFailAlloc_5927_, 32, v_v_5915_);
lean_ctor_set(v_reuseFailAlloc_5927_, 33, v_O_5916_);
lean_ctor_set(v_reuseFailAlloc_5927_, 34, v_X_5917_);
lean_ctor_set(v_reuseFailAlloc_5927_, 35, v_x_5918_);
lean_ctor_set(v_reuseFailAlloc_5927_, 36, v_Z_5919_);
v___x_5926_ = v_reuseFailAlloc_5927_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
return v___x_5926_;
}
}
}
}
}
case 27:
{
lean_object* v___x_5934_; uint8_t v_isShared_5935_; uint8_t v_isSharedCheck_5983_; 
v_isSharedCheck_5983_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_5983_ == 0)
{
lean_object* v_unused_5984_; 
v_unused_5984_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_5984_);
v___x_5934_ = v_modifier_4562_;
v_isShared_5935_ = v_isSharedCheck_5983_;
goto v_resetjp_5933_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5934_ = lean_box(0);
v_isShared_5935_ = v_isSharedCheck_5983_;
goto v_resetjp_5933_;
}
v_resetjp_5933_:
{
lean_object* v_G_5936_; lean_object* v_y_5937_; lean_object* v_u_5938_; lean_object* v_Y_5939_; lean_object* v_D_5940_; lean_object* v_M_5941_; lean_object* v_L_5942_; lean_object* v_d_5943_; lean_object* v_Q_5944_; lean_object* v_q_5945_; lean_object* v_w_5946_; lean_object* v_W_5947_; lean_object* v_E_5948_; lean_object* v_e_5949_; lean_object* v_c_5950_; lean_object* v_F_5951_; lean_object* v_a_5952_; lean_object* v_b_5953_; lean_object* v_B_5954_; lean_object* v_h_5955_; lean_object* v_K_5956_; lean_object* v_k_5957_; lean_object* v_H_5958_; lean_object* v_m_5959_; lean_object* v_s_5960_; lean_object* v_S_5961_; lean_object* v_A_5962_; lean_object* v_N_5963_; lean_object* v_V_5964_; lean_object* v_z_5965_; lean_object* v_zabbrev_5966_; lean_object* v_v_5967_; lean_object* v_O_5968_; lean_object* v_X_5969_; lean_object* v_x_5970_; lean_object* v_Z_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_5981_; 
v_G_5936_ = lean_ctor_get(v_date_4561_, 0);
v_y_5937_ = lean_ctor_get(v_date_4561_, 1);
v_u_5938_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5939_ = lean_ctor_get(v_date_4561_, 3);
v_D_5940_ = lean_ctor_get(v_date_4561_, 4);
v_M_5941_ = lean_ctor_get(v_date_4561_, 5);
v_L_5942_ = lean_ctor_get(v_date_4561_, 6);
v_d_5943_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5944_ = lean_ctor_get(v_date_4561_, 8);
v_q_5945_ = lean_ctor_get(v_date_4561_, 9);
v_w_5946_ = lean_ctor_get(v_date_4561_, 10);
v_W_5947_ = lean_ctor_get(v_date_4561_, 11);
v_E_5948_ = lean_ctor_get(v_date_4561_, 12);
v_e_5949_ = lean_ctor_get(v_date_4561_, 13);
v_c_5950_ = lean_ctor_get(v_date_4561_, 14);
v_F_5951_ = lean_ctor_get(v_date_4561_, 15);
v_a_5952_ = lean_ctor_get(v_date_4561_, 16);
v_b_5953_ = lean_ctor_get(v_date_4561_, 17);
v_B_5954_ = lean_ctor_get(v_date_4561_, 18);
v_h_5955_ = lean_ctor_get(v_date_4561_, 19);
v_K_5956_ = lean_ctor_get(v_date_4561_, 20);
v_k_5957_ = lean_ctor_get(v_date_4561_, 21);
v_H_5958_ = lean_ctor_get(v_date_4561_, 22);
v_m_5959_ = lean_ctor_get(v_date_4561_, 23);
v_s_5960_ = lean_ctor_get(v_date_4561_, 24);
v_S_5961_ = lean_ctor_get(v_date_4561_, 25);
v_A_5962_ = lean_ctor_get(v_date_4561_, 26);
v_N_5963_ = lean_ctor_get(v_date_4561_, 28);
v_V_5964_ = lean_ctor_get(v_date_4561_, 29);
v_z_5965_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_5966_ = lean_ctor_get(v_date_4561_, 31);
v_v_5967_ = lean_ctor_get(v_date_4561_, 32);
v_O_5968_ = lean_ctor_get(v_date_4561_, 33);
v_X_5969_ = lean_ctor_get(v_date_4561_, 34);
v_x_5970_ = lean_ctor_get(v_date_4561_, 35);
v_Z_5971_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_5981_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_5981_ == 0)
{
lean_object* v_unused_5982_; 
v_unused_5982_ = lean_ctor_get(v_date_4561_, 27);
lean_dec(v_unused_5982_);
v___x_5973_ = v_date_4561_;
v_isShared_5974_ = v_isSharedCheck_5981_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_Z_5971_);
lean_inc(v_x_5970_);
lean_inc(v_X_5969_);
lean_inc(v_O_5968_);
lean_inc(v_v_5967_);
lean_inc(v_zabbrev_5966_);
lean_inc(v_z_5965_);
lean_inc(v_V_5964_);
lean_inc(v_N_5963_);
lean_inc(v_A_5962_);
lean_inc(v_S_5961_);
lean_inc(v_s_5960_);
lean_inc(v_m_5959_);
lean_inc(v_H_5958_);
lean_inc(v_k_5957_);
lean_inc(v_K_5956_);
lean_inc(v_h_5955_);
lean_inc(v_B_5954_);
lean_inc(v_b_5953_);
lean_inc(v_a_5952_);
lean_inc(v_F_5951_);
lean_inc(v_c_5950_);
lean_inc(v_e_5949_);
lean_inc(v_E_5948_);
lean_inc(v_W_5947_);
lean_inc(v_w_5946_);
lean_inc(v_q_5945_);
lean_inc(v_Q_5944_);
lean_inc(v_d_5943_);
lean_inc(v_L_5942_);
lean_inc(v_M_5941_);
lean_inc(v_D_5940_);
lean_inc(v_Y_5939_);
lean_inc(v_u_5938_);
lean_inc(v_y_5937_);
lean_inc(v_G_5936_);
lean_dec(v_date_4561_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_5981_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v___x_5976_; 
if (v_isShared_5935_ == 0)
{
lean_ctor_set_tag(v___x_5934_, 1);
lean_ctor_set(v___x_5934_, 0, v_data_4563_);
v___x_5976_ = v___x_5934_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_data_4563_);
v___x_5976_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
lean_object* v___x_5978_; 
if (v_isShared_5974_ == 0)
{
lean_ctor_set(v___x_5973_, 27, v___x_5976_);
v___x_5978_ = v___x_5973_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v_G_5936_);
lean_ctor_set(v_reuseFailAlloc_5979_, 1, v_y_5937_);
lean_ctor_set(v_reuseFailAlloc_5979_, 2, v_u_5938_);
lean_ctor_set(v_reuseFailAlloc_5979_, 3, v_Y_5939_);
lean_ctor_set(v_reuseFailAlloc_5979_, 4, v_D_5940_);
lean_ctor_set(v_reuseFailAlloc_5979_, 5, v_M_5941_);
lean_ctor_set(v_reuseFailAlloc_5979_, 6, v_L_5942_);
lean_ctor_set(v_reuseFailAlloc_5979_, 7, v_d_5943_);
lean_ctor_set(v_reuseFailAlloc_5979_, 8, v_Q_5944_);
lean_ctor_set(v_reuseFailAlloc_5979_, 9, v_q_5945_);
lean_ctor_set(v_reuseFailAlloc_5979_, 10, v_w_5946_);
lean_ctor_set(v_reuseFailAlloc_5979_, 11, v_W_5947_);
lean_ctor_set(v_reuseFailAlloc_5979_, 12, v_E_5948_);
lean_ctor_set(v_reuseFailAlloc_5979_, 13, v_e_5949_);
lean_ctor_set(v_reuseFailAlloc_5979_, 14, v_c_5950_);
lean_ctor_set(v_reuseFailAlloc_5979_, 15, v_F_5951_);
lean_ctor_set(v_reuseFailAlloc_5979_, 16, v_a_5952_);
lean_ctor_set(v_reuseFailAlloc_5979_, 17, v_b_5953_);
lean_ctor_set(v_reuseFailAlloc_5979_, 18, v_B_5954_);
lean_ctor_set(v_reuseFailAlloc_5979_, 19, v_h_5955_);
lean_ctor_set(v_reuseFailAlloc_5979_, 20, v_K_5956_);
lean_ctor_set(v_reuseFailAlloc_5979_, 21, v_k_5957_);
lean_ctor_set(v_reuseFailAlloc_5979_, 22, v_H_5958_);
lean_ctor_set(v_reuseFailAlloc_5979_, 23, v_m_5959_);
lean_ctor_set(v_reuseFailAlloc_5979_, 24, v_s_5960_);
lean_ctor_set(v_reuseFailAlloc_5979_, 25, v_S_5961_);
lean_ctor_set(v_reuseFailAlloc_5979_, 26, v_A_5962_);
lean_ctor_set(v_reuseFailAlloc_5979_, 27, v___x_5976_);
lean_ctor_set(v_reuseFailAlloc_5979_, 28, v_N_5963_);
lean_ctor_set(v_reuseFailAlloc_5979_, 29, v_V_5964_);
lean_ctor_set(v_reuseFailAlloc_5979_, 30, v_z_5965_);
lean_ctor_set(v_reuseFailAlloc_5979_, 31, v_zabbrev_5966_);
lean_ctor_set(v_reuseFailAlloc_5979_, 32, v_v_5967_);
lean_ctor_set(v_reuseFailAlloc_5979_, 33, v_O_5968_);
lean_ctor_set(v_reuseFailAlloc_5979_, 34, v_X_5969_);
lean_ctor_set(v_reuseFailAlloc_5979_, 35, v_x_5970_);
lean_ctor_set(v_reuseFailAlloc_5979_, 36, v_Z_5971_);
v___x_5978_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
return v___x_5978_;
}
}
}
}
}
case 28:
{
lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_6035_; 
v_isSharedCheck_6035_ = !lean_is_exclusive(v_modifier_4562_);
if (v_isSharedCheck_6035_ == 0)
{
lean_object* v_unused_6036_; 
v_unused_6036_ = lean_ctor_get(v_modifier_4562_, 0);
lean_dec(v_unused_6036_);
v___x_5986_ = v_modifier_4562_;
v_isShared_5987_ = v_isSharedCheck_6035_;
goto v_resetjp_5985_;
}
else
{
lean_dec(v_modifier_4562_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_6035_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v_G_5988_; lean_object* v_y_5989_; lean_object* v_u_5990_; lean_object* v_Y_5991_; lean_object* v_D_5992_; lean_object* v_M_5993_; lean_object* v_L_5994_; lean_object* v_d_5995_; lean_object* v_Q_5996_; lean_object* v_q_5997_; lean_object* v_w_5998_; lean_object* v_W_5999_; lean_object* v_E_6000_; lean_object* v_e_6001_; lean_object* v_c_6002_; lean_object* v_F_6003_; lean_object* v_a_6004_; lean_object* v_b_6005_; lean_object* v_B_6006_; lean_object* v_h_6007_; lean_object* v_K_6008_; lean_object* v_k_6009_; lean_object* v_H_6010_; lean_object* v_m_6011_; lean_object* v_s_6012_; lean_object* v_S_6013_; lean_object* v_A_6014_; lean_object* v_n_6015_; lean_object* v_V_6016_; lean_object* v_z_6017_; lean_object* v_zabbrev_6018_; lean_object* v_v_6019_; lean_object* v_O_6020_; lean_object* v_X_6021_; lean_object* v_x_6022_; lean_object* v_Z_6023_; lean_object* v___x_6025_; uint8_t v_isShared_6026_; uint8_t v_isSharedCheck_6033_; 
v_G_5988_ = lean_ctor_get(v_date_4561_, 0);
v_y_5989_ = lean_ctor_get(v_date_4561_, 1);
v_u_5990_ = lean_ctor_get(v_date_4561_, 2);
v_Y_5991_ = lean_ctor_get(v_date_4561_, 3);
v_D_5992_ = lean_ctor_get(v_date_4561_, 4);
v_M_5993_ = lean_ctor_get(v_date_4561_, 5);
v_L_5994_ = lean_ctor_get(v_date_4561_, 6);
v_d_5995_ = lean_ctor_get(v_date_4561_, 7);
v_Q_5996_ = lean_ctor_get(v_date_4561_, 8);
v_q_5997_ = lean_ctor_get(v_date_4561_, 9);
v_w_5998_ = lean_ctor_get(v_date_4561_, 10);
v_W_5999_ = lean_ctor_get(v_date_4561_, 11);
v_E_6000_ = lean_ctor_get(v_date_4561_, 12);
v_e_6001_ = lean_ctor_get(v_date_4561_, 13);
v_c_6002_ = lean_ctor_get(v_date_4561_, 14);
v_F_6003_ = lean_ctor_get(v_date_4561_, 15);
v_a_6004_ = lean_ctor_get(v_date_4561_, 16);
v_b_6005_ = lean_ctor_get(v_date_4561_, 17);
v_B_6006_ = lean_ctor_get(v_date_4561_, 18);
v_h_6007_ = lean_ctor_get(v_date_4561_, 19);
v_K_6008_ = lean_ctor_get(v_date_4561_, 20);
v_k_6009_ = lean_ctor_get(v_date_4561_, 21);
v_H_6010_ = lean_ctor_get(v_date_4561_, 22);
v_m_6011_ = lean_ctor_get(v_date_4561_, 23);
v_s_6012_ = lean_ctor_get(v_date_4561_, 24);
v_S_6013_ = lean_ctor_get(v_date_4561_, 25);
v_A_6014_ = lean_ctor_get(v_date_4561_, 26);
v_n_6015_ = lean_ctor_get(v_date_4561_, 27);
v_V_6016_ = lean_ctor_get(v_date_4561_, 29);
v_z_6017_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_6018_ = lean_ctor_get(v_date_4561_, 31);
v_v_6019_ = lean_ctor_get(v_date_4561_, 32);
v_O_6020_ = lean_ctor_get(v_date_4561_, 33);
v_X_6021_ = lean_ctor_get(v_date_4561_, 34);
v_x_6022_ = lean_ctor_get(v_date_4561_, 35);
v_Z_6023_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_6033_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_6033_ == 0)
{
lean_object* v_unused_6034_; 
v_unused_6034_ = lean_ctor_get(v_date_4561_, 28);
lean_dec(v_unused_6034_);
v___x_6025_ = v_date_4561_;
v_isShared_6026_ = v_isSharedCheck_6033_;
goto v_resetjp_6024_;
}
else
{
lean_inc(v_Z_6023_);
lean_inc(v_x_6022_);
lean_inc(v_X_6021_);
lean_inc(v_O_6020_);
lean_inc(v_v_6019_);
lean_inc(v_zabbrev_6018_);
lean_inc(v_z_6017_);
lean_inc(v_V_6016_);
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
lean_dec(v_date_4561_);
v___x_6025_ = lean_box(0);
v_isShared_6026_ = v_isSharedCheck_6033_;
goto v_resetjp_6024_;
}
v_resetjp_6024_:
{
lean_object* v___x_6028_; 
if (v_isShared_5987_ == 0)
{
lean_ctor_set_tag(v___x_5986_, 1);
lean_ctor_set(v___x_5986_, 0, v_data_4563_);
v___x_6028_ = v___x_5986_;
goto v_reusejp_6027_;
}
else
{
lean_object* v_reuseFailAlloc_6032_; 
v_reuseFailAlloc_6032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6032_, 0, v_data_4563_);
v___x_6028_ = v_reuseFailAlloc_6032_;
goto v_reusejp_6027_;
}
v_reusejp_6027_:
{
lean_object* v___x_6030_; 
if (v_isShared_6026_ == 0)
{
lean_ctor_set(v___x_6025_, 28, v___x_6028_);
v___x_6030_ = v___x_6025_;
goto v_reusejp_6029_;
}
else
{
lean_object* v_reuseFailAlloc_6031_; 
v_reuseFailAlloc_6031_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6031_, 0, v_G_5988_);
lean_ctor_set(v_reuseFailAlloc_6031_, 1, v_y_5989_);
lean_ctor_set(v_reuseFailAlloc_6031_, 2, v_u_5990_);
lean_ctor_set(v_reuseFailAlloc_6031_, 3, v_Y_5991_);
lean_ctor_set(v_reuseFailAlloc_6031_, 4, v_D_5992_);
lean_ctor_set(v_reuseFailAlloc_6031_, 5, v_M_5993_);
lean_ctor_set(v_reuseFailAlloc_6031_, 6, v_L_5994_);
lean_ctor_set(v_reuseFailAlloc_6031_, 7, v_d_5995_);
lean_ctor_set(v_reuseFailAlloc_6031_, 8, v_Q_5996_);
lean_ctor_set(v_reuseFailAlloc_6031_, 9, v_q_5997_);
lean_ctor_set(v_reuseFailAlloc_6031_, 10, v_w_5998_);
lean_ctor_set(v_reuseFailAlloc_6031_, 11, v_W_5999_);
lean_ctor_set(v_reuseFailAlloc_6031_, 12, v_E_6000_);
lean_ctor_set(v_reuseFailAlloc_6031_, 13, v_e_6001_);
lean_ctor_set(v_reuseFailAlloc_6031_, 14, v_c_6002_);
lean_ctor_set(v_reuseFailAlloc_6031_, 15, v_F_6003_);
lean_ctor_set(v_reuseFailAlloc_6031_, 16, v_a_6004_);
lean_ctor_set(v_reuseFailAlloc_6031_, 17, v_b_6005_);
lean_ctor_set(v_reuseFailAlloc_6031_, 18, v_B_6006_);
lean_ctor_set(v_reuseFailAlloc_6031_, 19, v_h_6007_);
lean_ctor_set(v_reuseFailAlloc_6031_, 20, v_K_6008_);
lean_ctor_set(v_reuseFailAlloc_6031_, 21, v_k_6009_);
lean_ctor_set(v_reuseFailAlloc_6031_, 22, v_H_6010_);
lean_ctor_set(v_reuseFailAlloc_6031_, 23, v_m_6011_);
lean_ctor_set(v_reuseFailAlloc_6031_, 24, v_s_6012_);
lean_ctor_set(v_reuseFailAlloc_6031_, 25, v_S_6013_);
lean_ctor_set(v_reuseFailAlloc_6031_, 26, v_A_6014_);
lean_ctor_set(v_reuseFailAlloc_6031_, 27, v_n_6015_);
lean_ctor_set(v_reuseFailAlloc_6031_, 28, v___x_6028_);
lean_ctor_set(v_reuseFailAlloc_6031_, 29, v_V_6016_);
lean_ctor_set(v_reuseFailAlloc_6031_, 30, v_z_6017_);
lean_ctor_set(v_reuseFailAlloc_6031_, 31, v_zabbrev_6018_);
lean_ctor_set(v_reuseFailAlloc_6031_, 32, v_v_6019_);
lean_ctor_set(v_reuseFailAlloc_6031_, 33, v_O_6020_);
lean_ctor_set(v_reuseFailAlloc_6031_, 34, v_X_6021_);
lean_ctor_set(v_reuseFailAlloc_6031_, 35, v_x_6022_);
lean_ctor_set(v_reuseFailAlloc_6031_, 36, v_Z_6023_);
v___x_6030_ = v_reuseFailAlloc_6031_;
goto v_reusejp_6029_;
}
v_reusejp_6029_:
{
return v___x_6030_;
}
}
}
}
}
case 29:
{
lean_object* v_G_6037_; lean_object* v_y_6038_; lean_object* v_u_6039_; lean_object* v_Y_6040_; lean_object* v_D_6041_; lean_object* v_M_6042_; lean_object* v_L_6043_; lean_object* v_d_6044_; lean_object* v_Q_6045_; lean_object* v_q_6046_; lean_object* v_w_6047_; lean_object* v_W_6048_; lean_object* v_E_6049_; lean_object* v_e_6050_; lean_object* v_c_6051_; lean_object* v_F_6052_; lean_object* v_a_6053_; lean_object* v_b_6054_; lean_object* v_B_6055_; lean_object* v_h_6056_; lean_object* v_K_6057_; lean_object* v_k_6058_; lean_object* v_H_6059_; lean_object* v_m_6060_; lean_object* v_s_6061_; lean_object* v_S_6062_; lean_object* v_A_6063_; lean_object* v_n_6064_; lean_object* v_N_6065_; lean_object* v_z_6066_; lean_object* v_zabbrev_6067_; lean_object* v_v_6068_; lean_object* v_O_6069_; lean_object* v_X_6070_; lean_object* v_x_6071_; lean_object* v_Z_6072_; lean_object* v___x_6074_; uint8_t v_isShared_6075_; uint8_t v_isSharedCheck_6080_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_G_6037_ = lean_ctor_get(v_date_4561_, 0);
v_y_6038_ = lean_ctor_get(v_date_4561_, 1);
v_u_6039_ = lean_ctor_get(v_date_4561_, 2);
v_Y_6040_ = lean_ctor_get(v_date_4561_, 3);
v_D_6041_ = lean_ctor_get(v_date_4561_, 4);
v_M_6042_ = lean_ctor_get(v_date_4561_, 5);
v_L_6043_ = lean_ctor_get(v_date_4561_, 6);
v_d_6044_ = lean_ctor_get(v_date_4561_, 7);
v_Q_6045_ = lean_ctor_get(v_date_4561_, 8);
v_q_6046_ = lean_ctor_get(v_date_4561_, 9);
v_w_6047_ = lean_ctor_get(v_date_4561_, 10);
v_W_6048_ = lean_ctor_get(v_date_4561_, 11);
v_E_6049_ = lean_ctor_get(v_date_4561_, 12);
v_e_6050_ = lean_ctor_get(v_date_4561_, 13);
v_c_6051_ = lean_ctor_get(v_date_4561_, 14);
v_F_6052_ = lean_ctor_get(v_date_4561_, 15);
v_a_6053_ = lean_ctor_get(v_date_4561_, 16);
v_b_6054_ = lean_ctor_get(v_date_4561_, 17);
v_B_6055_ = lean_ctor_get(v_date_4561_, 18);
v_h_6056_ = lean_ctor_get(v_date_4561_, 19);
v_K_6057_ = lean_ctor_get(v_date_4561_, 20);
v_k_6058_ = lean_ctor_get(v_date_4561_, 21);
v_H_6059_ = lean_ctor_get(v_date_4561_, 22);
v_m_6060_ = lean_ctor_get(v_date_4561_, 23);
v_s_6061_ = lean_ctor_get(v_date_4561_, 24);
v_S_6062_ = lean_ctor_get(v_date_4561_, 25);
v_A_6063_ = lean_ctor_get(v_date_4561_, 26);
v_n_6064_ = lean_ctor_get(v_date_4561_, 27);
v_N_6065_ = lean_ctor_get(v_date_4561_, 28);
v_z_6066_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_6067_ = lean_ctor_get(v_date_4561_, 31);
v_v_6068_ = lean_ctor_get(v_date_4561_, 32);
v_O_6069_ = lean_ctor_get(v_date_4561_, 33);
v_X_6070_ = lean_ctor_get(v_date_4561_, 34);
v_x_6071_ = lean_ctor_get(v_date_4561_, 35);
v_Z_6072_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_6080_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_6080_ == 0)
{
lean_object* v_unused_6081_; 
v_unused_6081_ = lean_ctor_get(v_date_4561_, 29);
lean_dec(v_unused_6081_);
v___x_6074_ = v_date_4561_;
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
lean_inc(v_zabbrev_6067_);
lean_inc(v_z_6066_);
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
lean_dec(v_date_4561_);
v___x_6074_ = lean_box(0);
v_isShared_6075_ = v_isSharedCheck_6080_;
goto v_resetjp_6073_;
}
v_resetjp_6073_:
{
lean_object* v___x_6076_; lean_object* v___x_6078_; 
v___x_6076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6076_, 0, v_data_4563_);
if (v_isShared_6075_ == 0)
{
lean_ctor_set(v___x_6074_, 29, v___x_6076_);
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
lean_ctor_set(v_reuseFailAlloc_6079_, 29, v___x_6076_);
lean_ctor_set(v_reuseFailAlloc_6079_, 30, v_z_6066_);
lean_ctor_set(v_reuseFailAlloc_6079_, 31, v_zabbrev_6067_);
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
case 30:
{
uint8_t v_presentation_6082_; 
v_presentation_6082_ = lean_ctor_get_uint8(v_modifier_4562_, 0);
lean_dec_ref_known(v_modifier_4562_, 0);
if (v_presentation_6082_ == 0)
{
lean_object* v_G_6083_; lean_object* v_y_6084_; lean_object* v_u_6085_; lean_object* v_Y_6086_; lean_object* v_D_6087_; lean_object* v_M_6088_; lean_object* v_L_6089_; lean_object* v_d_6090_; lean_object* v_Q_6091_; lean_object* v_q_6092_; lean_object* v_w_6093_; lean_object* v_W_6094_; lean_object* v_E_6095_; lean_object* v_e_6096_; lean_object* v_c_6097_; lean_object* v_F_6098_; lean_object* v_a_6099_; lean_object* v_b_6100_; lean_object* v_B_6101_; lean_object* v_h_6102_; lean_object* v_K_6103_; lean_object* v_k_6104_; lean_object* v_H_6105_; lean_object* v_m_6106_; lean_object* v_s_6107_; lean_object* v_S_6108_; lean_object* v_A_6109_; lean_object* v_n_6110_; lean_object* v_N_6111_; lean_object* v_V_6112_; lean_object* v_z_6113_; lean_object* v_v_6114_; lean_object* v_O_6115_; lean_object* v_X_6116_; lean_object* v_x_6117_; lean_object* v_Z_6118_; lean_object* v___x_6120_; uint8_t v_isShared_6121_; uint8_t v_isSharedCheck_6126_; 
v_G_6083_ = lean_ctor_get(v_date_4561_, 0);
v_y_6084_ = lean_ctor_get(v_date_4561_, 1);
v_u_6085_ = lean_ctor_get(v_date_4561_, 2);
v_Y_6086_ = lean_ctor_get(v_date_4561_, 3);
v_D_6087_ = lean_ctor_get(v_date_4561_, 4);
v_M_6088_ = lean_ctor_get(v_date_4561_, 5);
v_L_6089_ = lean_ctor_get(v_date_4561_, 6);
v_d_6090_ = lean_ctor_get(v_date_4561_, 7);
v_Q_6091_ = lean_ctor_get(v_date_4561_, 8);
v_q_6092_ = lean_ctor_get(v_date_4561_, 9);
v_w_6093_ = lean_ctor_get(v_date_4561_, 10);
v_W_6094_ = lean_ctor_get(v_date_4561_, 11);
v_E_6095_ = lean_ctor_get(v_date_4561_, 12);
v_e_6096_ = lean_ctor_get(v_date_4561_, 13);
v_c_6097_ = lean_ctor_get(v_date_4561_, 14);
v_F_6098_ = lean_ctor_get(v_date_4561_, 15);
v_a_6099_ = lean_ctor_get(v_date_4561_, 16);
v_b_6100_ = lean_ctor_get(v_date_4561_, 17);
v_B_6101_ = lean_ctor_get(v_date_4561_, 18);
v_h_6102_ = lean_ctor_get(v_date_4561_, 19);
v_K_6103_ = lean_ctor_get(v_date_4561_, 20);
v_k_6104_ = lean_ctor_get(v_date_4561_, 21);
v_H_6105_ = lean_ctor_get(v_date_4561_, 22);
v_m_6106_ = lean_ctor_get(v_date_4561_, 23);
v_s_6107_ = lean_ctor_get(v_date_4561_, 24);
v_S_6108_ = lean_ctor_get(v_date_4561_, 25);
v_A_6109_ = lean_ctor_get(v_date_4561_, 26);
v_n_6110_ = lean_ctor_get(v_date_4561_, 27);
v_N_6111_ = lean_ctor_get(v_date_4561_, 28);
v_V_6112_ = lean_ctor_get(v_date_4561_, 29);
v_z_6113_ = lean_ctor_get(v_date_4561_, 30);
v_v_6114_ = lean_ctor_get(v_date_4561_, 32);
v_O_6115_ = lean_ctor_get(v_date_4561_, 33);
v_X_6116_ = lean_ctor_get(v_date_4561_, 34);
v_x_6117_ = lean_ctor_get(v_date_4561_, 35);
v_Z_6118_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_6126_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_6126_ == 0)
{
lean_object* v_unused_6127_; 
v_unused_6127_ = lean_ctor_get(v_date_4561_, 31);
lean_dec(v_unused_6127_);
v___x_6120_ = v_date_4561_;
v_isShared_6121_ = v_isSharedCheck_6126_;
goto v_resetjp_6119_;
}
else
{
lean_inc(v_Z_6118_);
lean_inc(v_x_6117_);
lean_inc(v_X_6116_);
lean_inc(v_O_6115_);
lean_inc(v_v_6114_);
lean_inc(v_z_6113_);
lean_inc(v_V_6112_);
lean_inc(v_N_6111_);
lean_inc(v_n_6110_);
lean_inc(v_A_6109_);
lean_inc(v_S_6108_);
lean_inc(v_s_6107_);
lean_inc(v_m_6106_);
lean_inc(v_H_6105_);
lean_inc(v_k_6104_);
lean_inc(v_K_6103_);
lean_inc(v_h_6102_);
lean_inc(v_B_6101_);
lean_inc(v_b_6100_);
lean_inc(v_a_6099_);
lean_inc(v_F_6098_);
lean_inc(v_c_6097_);
lean_inc(v_e_6096_);
lean_inc(v_E_6095_);
lean_inc(v_W_6094_);
lean_inc(v_w_6093_);
lean_inc(v_q_6092_);
lean_inc(v_Q_6091_);
lean_inc(v_d_6090_);
lean_inc(v_L_6089_);
lean_inc(v_M_6088_);
lean_inc(v_D_6087_);
lean_inc(v_Y_6086_);
lean_inc(v_u_6085_);
lean_inc(v_y_6084_);
lean_inc(v_G_6083_);
lean_dec(v_date_4561_);
v___x_6120_ = lean_box(0);
v_isShared_6121_ = v_isSharedCheck_6126_;
goto v_resetjp_6119_;
}
v_resetjp_6119_:
{
lean_object* v___x_6122_; lean_object* v___x_6124_; 
v___x_6122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6122_, 0, v_data_4563_);
if (v_isShared_6121_ == 0)
{
lean_ctor_set(v___x_6120_, 31, v___x_6122_);
v___x_6124_ = v___x_6120_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6125_; 
v_reuseFailAlloc_6125_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6125_, 0, v_G_6083_);
lean_ctor_set(v_reuseFailAlloc_6125_, 1, v_y_6084_);
lean_ctor_set(v_reuseFailAlloc_6125_, 2, v_u_6085_);
lean_ctor_set(v_reuseFailAlloc_6125_, 3, v_Y_6086_);
lean_ctor_set(v_reuseFailAlloc_6125_, 4, v_D_6087_);
lean_ctor_set(v_reuseFailAlloc_6125_, 5, v_M_6088_);
lean_ctor_set(v_reuseFailAlloc_6125_, 6, v_L_6089_);
lean_ctor_set(v_reuseFailAlloc_6125_, 7, v_d_6090_);
lean_ctor_set(v_reuseFailAlloc_6125_, 8, v_Q_6091_);
lean_ctor_set(v_reuseFailAlloc_6125_, 9, v_q_6092_);
lean_ctor_set(v_reuseFailAlloc_6125_, 10, v_w_6093_);
lean_ctor_set(v_reuseFailAlloc_6125_, 11, v_W_6094_);
lean_ctor_set(v_reuseFailAlloc_6125_, 12, v_E_6095_);
lean_ctor_set(v_reuseFailAlloc_6125_, 13, v_e_6096_);
lean_ctor_set(v_reuseFailAlloc_6125_, 14, v_c_6097_);
lean_ctor_set(v_reuseFailAlloc_6125_, 15, v_F_6098_);
lean_ctor_set(v_reuseFailAlloc_6125_, 16, v_a_6099_);
lean_ctor_set(v_reuseFailAlloc_6125_, 17, v_b_6100_);
lean_ctor_set(v_reuseFailAlloc_6125_, 18, v_B_6101_);
lean_ctor_set(v_reuseFailAlloc_6125_, 19, v_h_6102_);
lean_ctor_set(v_reuseFailAlloc_6125_, 20, v_K_6103_);
lean_ctor_set(v_reuseFailAlloc_6125_, 21, v_k_6104_);
lean_ctor_set(v_reuseFailAlloc_6125_, 22, v_H_6105_);
lean_ctor_set(v_reuseFailAlloc_6125_, 23, v_m_6106_);
lean_ctor_set(v_reuseFailAlloc_6125_, 24, v_s_6107_);
lean_ctor_set(v_reuseFailAlloc_6125_, 25, v_S_6108_);
lean_ctor_set(v_reuseFailAlloc_6125_, 26, v_A_6109_);
lean_ctor_set(v_reuseFailAlloc_6125_, 27, v_n_6110_);
lean_ctor_set(v_reuseFailAlloc_6125_, 28, v_N_6111_);
lean_ctor_set(v_reuseFailAlloc_6125_, 29, v_V_6112_);
lean_ctor_set(v_reuseFailAlloc_6125_, 30, v_z_6113_);
lean_ctor_set(v_reuseFailAlloc_6125_, 31, v___x_6122_);
lean_ctor_set(v_reuseFailAlloc_6125_, 32, v_v_6114_);
lean_ctor_set(v_reuseFailAlloc_6125_, 33, v_O_6115_);
lean_ctor_set(v_reuseFailAlloc_6125_, 34, v_X_6116_);
lean_ctor_set(v_reuseFailAlloc_6125_, 35, v_x_6117_);
lean_ctor_set(v_reuseFailAlloc_6125_, 36, v_Z_6118_);
v___x_6124_ = v_reuseFailAlloc_6125_;
goto v_reusejp_6123_;
}
v_reusejp_6123_:
{
return v___x_6124_;
}
}
}
else
{
lean_object* v_G_6128_; lean_object* v_y_6129_; lean_object* v_u_6130_; lean_object* v_Y_6131_; lean_object* v_D_6132_; lean_object* v_M_6133_; lean_object* v_L_6134_; lean_object* v_d_6135_; lean_object* v_Q_6136_; lean_object* v_q_6137_; lean_object* v_w_6138_; lean_object* v_W_6139_; lean_object* v_E_6140_; lean_object* v_e_6141_; lean_object* v_c_6142_; lean_object* v_F_6143_; lean_object* v_a_6144_; lean_object* v_b_6145_; lean_object* v_B_6146_; lean_object* v_h_6147_; lean_object* v_K_6148_; lean_object* v_k_6149_; lean_object* v_H_6150_; lean_object* v_m_6151_; lean_object* v_s_6152_; lean_object* v_S_6153_; lean_object* v_A_6154_; lean_object* v_n_6155_; lean_object* v_N_6156_; lean_object* v_V_6157_; lean_object* v_zabbrev_6158_; lean_object* v_v_6159_; lean_object* v_O_6160_; lean_object* v_X_6161_; lean_object* v_x_6162_; lean_object* v_Z_6163_; lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6171_; 
v_G_6128_ = lean_ctor_get(v_date_4561_, 0);
v_y_6129_ = lean_ctor_get(v_date_4561_, 1);
v_u_6130_ = lean_ctor_get(v_date_4561_, 2);
v_Y_6131_ = lean_ctor_get(v_date_4561_, 3);
v_D_6132_ = lean_ctor_get(v_date_4561_, 4);
v_M_6133_ = lean_ctor_get(v_date_4561_, 5);
v_L_6134_ = lean_ctor_get(v_date_4561_, 6);
v_d_6135_ = lean_ctor_get(v_date_4561_, 7);
v_Q_6136_ = lean_ctor_get(v_date_4561_, 8);
v_q_6137_ = lean_ctor_get(v_date_4561_, 9);
v_w_6138_ = lean_ctor_get(v_date_4561_, 10);
v_W_6139_ = lean_ctor_get(v_date_4561_, 11);
v_E_6140_ = lean_ctor_get(v_date_4561_, 12);
v_e_6141_ = lean_ctor_get(v_date_4561_, 13);
v_c_6142_ = lean_ctor_get(v_date_4561_, 14);
v_F_6143_ = lean_ctor_get(v_date_4561_, 15);
v_a_6144_ = lean_ctor_get(v_date_4561_, 16);
v_b_6145_ = lean_ctor_get(v_date_4561_, 17);
v_B_6146_ = lean_ctor_get(v_date_4561_, 18);
v_h_6147_ = lean_ctor_get(v_date_4561_, 19);
v_K_6148_ = lean_ctor_get(v_date_4561_, 20);
v_k_6149_ = lean_ctor_get(v_date_4561_, 21);
v_H_6150_ = lean_ctor_get(v_date_4561_, 22);
v_m_6151_ = lean_ctor_get(v_date_4561_, 23);
v_s_6152_ = lean_ctor_get(v_date_4561_, 24);
v_S_6153_ = lean_ctor_get(v_date_4561_, 25);
v_A_6154_ = lean_ctor_get(v_date_4561_, 26);
v_n_6155_ = lean_ctor_get(v_date_4561_, 27);
v_N_6156_ = lean_ctor_get(v_date_4561_, 28);
v_V_6157_ = lean_ctor_get(v_date_4561_, 29);
v_zabbrev_6158_ = lean_ctor_get(v_date_4561_, 31);
v_v_6159_ = lean_ctor_get(v_date_4561_, 32);
v_O_6160_ = lean_ctor_get(v_date_4561_, 33);
v_X_6161_ = lean_ctor_get(v_date_4561_, 34);
v_x_6162_ = lean_ctor_get(v_date_4561_, 35);
v_Z_6163_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_6171_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_6171_ == 0)
{
lean_object* v_unused_6172_; 
v_unused_6172_ = lean_ctor_get(v_date_4561_, 30);
lean_dec(v_unused_6172_);
v___x_6165_ = v_date_4561_;
v_isShared_6166_ = v_isSharedCheck_6171_;
goto v_resetjp_6164_;
}
else
{
lean_inc(v_Z_6163_);
lean_inc(v_x_6162_);
lean_inc(v_X_6161_);
lean_inc(v_O_6160_);
lean_inc(v_v_6159_);
lean_inc(v_zabbrev_6158_);
lean_inc(v_V_6157_);
lean_inc(v_N_6156_);
lean_inc(v_n_6155_);
lean_inc(v_A_6154_);
lean_inc(v_S_6153_);
lean_inc(v_s_6152_);
lean_inc(v_m_6151_);
lean_inc(v_H_6150_);
lean_inc(v_k_6149_);
lean_inc(v_K_6148_);
lean_inc(v_h_6147_);
lean_inc(v_B_6146_);
lean_inc(v_b_6145_);
lean_inc(v_a_6144_);
lean_inc(v_F_6143_);
lean_inc(v_c_6142_);
lean_inc(v_e_6141_);
lean_inc(v_E_6140_);
lean_inc(v_W_6139_);
lean_inc(v_w_6138_);
lean_inc(v_q_6137_);
lean_inc(v_Q_6136_);
lean_inc(v_d_6135_);
lean_inc(v_L_6134_);
lean_inc(v_M_6133_);
lean_inc(v_D_6132_);
lean_inc(v_Y_6131_);
lean_inc(v_u_6130_);
lean_inc(v_y_6129_);
lean_inc(v_G_6128_);
lean_dec(v_date_4561_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6171_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
lean_object* v___x_6167_; lean_object* v___x_6169_; 
v___x_6167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6167_, 0, v_data_4563_);
if (v_isShared_6166_ == 0)
{
lean_ctor_set(v___x_6165_, 30, v___x_6167_);
v___x_6169_ = v___x_6165_;
goto v_reusejp_6168_;
}
else
{
lean_object* v_reuseFailAlloc_6170_; 
v_reuseFailAlloc_6170_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6170_, 0, v_G_6128_);
lean_ctor_set(v_reuseFailAlloc_6170_, 1, v_y_6129_);
lean_ctor_set(v_reuseFailAlloc_6170_, 2, v_u_6130_);
lean_ctor_set(v_reuseFailAlloc_6170_, 3, v_Y_6131_);
lean_ctor_set(v_reuseFailAlloc_6170_, 4, v_D_6132_);
lean_ctor_set(v_reuseFailAlloc_6170_, 5, v_M_6133_);
lean_ctor_set(v_reuseFailAlloc_6170_, 6, v_L_6134_);
lean_ctor_set(v_reuseFailAlloc_6170_, 7, v_d_6135_);
lean_ctor_set(v_reuseFailAlloc_6170_, 8, v_Q_6136_);
lean_ctor_set(v_reuseFailAlloc_6170_, 9, v_q_6137_);
lean_ctor_set(v_reuseFailAlloc_6170_, 10, v_w_6138_);
lean_ctor_set(v_reuseFailAlloc_6170_, 11, v_W_6139_);
lean_ctor_set(v_reuseFailAlloc_6170_, 12, v_E_6140_);
lean_ctor_set(v_reuseFailAlloc_6170_, 13, v_e_6141_);
lean_ctor_set(v_reuseFailAlloc_6170_, 14, v_c_6142_);
lean_ctor_set(v_reuseFailAlloc_6170_, 15, v_F_6143_);
lean_ctor_set(v_reuseFailAlloc_6170_, 16, v_a_6144_);
lean_ctor_set(v_reuseFailAlloc_6170_, 17, v_b_6145_);
lean_ctor_set(v_reuseFailAlloc_6170_, 18, v_B_6146_);
lean_ctor_set(v_reuseFailAlloc_6170_, 19, v_h_6147_);
lean_ctor_set(v_reuseFailAlloc_6170_, 20, v_K_6148_);
lean_ctor_set(v_reuseFailAlloc_6170_, 21, v_k_6149_);
lean_ctor_set(v_reuseFailAlloc_6170_, 22, v_H_6150_);
lean_ctor_set(v_reuseFailAlloc_6170_, 23, v_m_6151_);
lean_ctor_set(v_reuseFailAlloc_6170_, 24, v_s_6152_);
lean_ctor_set(v_reuseFailAlloc_6170_, 25, v_S_6153_);
lean_ctor_set(v_reuseFailAlloc_6170_, 26, v_A_6154_);
lean_ctor_set(v_reuseFailAlloc_6170_, 27, v_n_6155_);
lean_ctor_set(v_reuseFailAlloc_6170_, 28, v_N_6156_);
lean_ctor_set(v_reuseFailAlloc_6170_, 29, v_V_6157_);
lean_ctor_set(v_reuseFailAlloc_6170_, 30, v___x_6167_);
lean_ctor_set(v_reuseFailAlloc_6170_, 31, v_zabbrev_6158_);
lean_ctor_set(v_reuseFailAlloc_6170_, 32, v_v_6159_);
lean_ctor_set(v_reuseFailAlloc_6170_, 33, v_O_6160_);
lean_ctor_set(v_reuseFailAlloc_6170_, 34, v_X_6161_);
lean_ctor_set(v_reuseFailAlloc_6170_, 35, v_x_6162_);
lean_ctor_set(v_reuseFailAlloc_6170_, 36, v_Z_6163_);
v___x_6169_ = v_reuseFailAlloc_6170_;
goto v_reusejp_6168_;
}
v_reusejp_6168_:
{
return v___x_6169_;
}
}
}
}
case 31:
{
lean_object* v_G_6173_; lean_object* v_y_6174_; lean_object* v_u_6175_; lean_object* v_Y_6176_; lean_object* v_D_6177_; lean_object* v_M_6178_; lean_object* v_L_6179_; lean_object* v_d_6180_; lean_object* v_Q_6181_; lean_object* v_q_6182_; lean_object* v_w_6183_; lean_object* v_W_6184_; lean_object* v_E_6185_; lean_object* v_e_6186_; lean_object* v_c_6187_; lean_object* v_F_6188_; lean_object* v_a_6189_; lean_object* v_b_6190_; lean_object* v_B_6191_; lean_object* v_h_6192_; lean_object* v_K_6193_; lean_object* v_k_6194_; lean_object* v_H_6195_; lean_object* v_m_6196_; lean_object* v_s_6197_; lean_object* v_S_6198_; lean_object* v_A_6199_; lean_object* v_n_6200_; lean_object* v_N_6201_; lean_object* v_V_6202_; lean_object* v_z_6203_; lean_object* v_zabbrev_6204_; lean_object* v_O_6205_; lean_object* v_X_6206_; lean_object* v_x_6207_; lean_object* v_Z_6208_; lean_object* v___x_6210_; uint8_t v_isShared_6211_; uint8_t v_isSharedCheck_6216_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_G_6173_ = lean_ctor_get(v_date_4561_, 0);
v_y_6174_ = lean_ctor_get(v_date_4561_, 1);
v_u_6175_ = lean_ctor_get(v_date_4561_, 2);
v_Y_6176_ = lean_ctor_get(v_date_4561_, 3);
v_D_6177_ = lean_ctor_get(v_date_4561_, 4);
v_M_6178_ = lean_ctor_get(v_date_4561_, 5);
v_L_6179_ = lean_ctor_get(v_date_4561_, 6);
v_d_6180_ = lean_ctor_get(v_date_4561_, 7);
v_Q_6181_ = lean_ctor_get(v_date_4561_, 8);
v_q_6182_ = lean_ctor_get(v_date_4561_, 9);
v_w_6183_ = lean_ctor_get(v_date_4561_, 10);
v_W_6184_ = lean_ctor_get(v_date_4561_, 11);
v_E_6185_ = lean_ctor_get(v_date_4561_, 12);
v_e_6186_ = lean_ctor_get(v_date_4561_, 13);
v_c_6187_ = lean_ctor_get(v_date_4561_, 14);
v_F_6188_ = lean_ctor_get(v_date_4561_, 15);
v_a_6189_ = lean_ctor_get(v_date_4561_, 16);
v_b_6190_ = lean_ctor_get(v_date_4561_, 17);
v_B_6191_ = lean_ctor_get(v_date_4561_, 18);
v_h_6192_ = lean_ctor_get(v_date_4561_, 19);
v_K_6193_ = lean_ctor_get(v_date_4561_, 20);
v_k_6194_ = lean_ctor_get(v_date_4561_, 21);
v_H_6195_ = lean_ctor_get(v_date_4561_, 22);
v_m_6196_ = lean_ctor_get(v_date_4561_, 23);
v_s_6197_ = lean_ctor_get(v_date_4561_, 24);
v_S_6198_ = lean_ctor_get(v_date_4561_, 25);
v_A_6199_ = lean_ctor_get(v_date_4561_, 26);
v_n_6200_ = lean_ctor_get(v_date_4561_, 27);
v_N_6201_ = lean_ctor_get(v_date_4561_, 28);
v_V_6202_ = lean_ctor_get(v_date_4561_, 29);
v_z_6203_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_6204_ = lean_ctor_get(v_date_4561_, 31);
v_O_6205_ = lean_ctor_get(v_date_4561_, 33);
v_X_6206_ = lean_ctor_get(v_date_4561_, 34);
v_x_6207_ = lean_ctor_get(v_date_4561_, 35);
v_Z_6208_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_6216_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_6216_ == 0)
{
lean_object* v_unused_6217_; 
v_unused_6217_ = lean_ctor_get(v_date_4561_, 32);
lean_dec(v_unused_6217_);
v___x_6210_ = v_date_4561_;
v_isShared_6211_ = v_isSharedCheck_6216_;
goto v_resetjp_6209_;
}
else
{
lean_inc(v_Z_6208_);
lean_inc(v_x_6207_);
lean_inc(v_X_6206_);
lean_inc(v_O_6205_);
lean_inc(v_zabbrev_6204_);
lean_inc(v_z_6203_);
lean_inc(v_V_6202_);
lean_inc(v_N_6201_);
lean_inc(v_n_6200_);
lean_inc(v_A_6199_);
lean_inc(v_S_6198_);
lean_inc(v_s_6197_);
lean_inc(v_m_6196_);
lean_inc(v_H_6195_);
lean_inc(v_k_6194_);
lean_inc(v_K_6193_);
lean_inc(v_h_6192_);
lean_inc(v_B_6191_);
lean_inc(v_b_6190_);
lean_inc(v_a_6189_);
lean_inc(v_F_6188_);
lean_inc(v_c_6187_);
lean_inc(v_e_6186_);
lean_inc(v_E_6185_);
lean_inc(v_W_6184_);
lean_inc(v_w_6183_);
lean_inc(v_q_6182_);
lean_inc(v_Q_6181_);
lean_inc(v_d_6180_);
lean_inc(v_L_6179_);
lean_inc(v_M_6178_);
lean_inc(v_D_6177_);
lean_inc(v_Y_6176_);
lean_inc(v_u_6175_);
lean_inc(v_y_6174_);
lean_inc(v_G_6173_);
lean_dec(v_date_4561_);
v___x_6210_ = lean_box(0);
v_isShared_6211_ = v_isSharedCheck_6216_;
goto v_resetjp_6209_;
}
v_resetjp_6209_:
{
lean_object* v___x_6212_; lean_object* v___x_6214_; 
v___x_6212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6212_, 0, v_data_4563_);
if (v_isShared_6211_ == 0)
{
lean_ctor_set(v___x_6210_, 32, v___x_6212_);
v___x_6214_ = v___x_6210_;
goto v_reusejp_6213_;
}
else
{
lean_object* v_reuseFailAlloc_6215_; 
v_reuseFailAlloc_6215_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6215_, 0, v_G_6173_);
lean_ctor_set(v_reuseFailAlloc_6215_, 1, v_y_6174_);
lean_ctor_set(v_reuseFailAlloc_6215_, 2, v_u_6175_);
lean_ctor_set(v_reuseFailAlloc_6215_, 3, v_Y_6176_);
lean_ctor_set(v_reuseFailAlloc_6215_, 4, v_D_6177_);
lean_ctor_set(v_reuseFailAlloc_6215_, 5, v_M_6178_);
lean_ctor_set(v_reuseFailAlloc_6215_, 6, v_L_6179_);
lean_ctor_set(v_reuseFailAlloc_6215_, 7, v_d_6180_);
lean_ctor_set(v_reuseFailAlloc_6215_, 8, v_Q_6181_);
lean_ctor_set(v_reuseFailAlloc_6215_, 9, v_q_6182_);
lean_ctor_set(v_reuseFailAlloc_6215_, 10, v_w_6183_);
lean_ctor_set(v_reuseFailAlloc_6215_, 11, v_W_6184_);
lean_ctor_set(v_reuseFailAlloc_6215_, 12, v_E_6185_);
lean_ctor_set(v_reuseFailAlloc_6215_, 13, v_e_6186_);
lean_ctor_set(v_reuseFailAlloc_6215_, 14, v_c_6187_);
lean_ctor_set(v_reuseFailAlloc_6215_, 15, v_F_6188_);
lean_ctor_set(v_reuseFailAlloc_6215_, 16, v_a_6189_);
lean_ctor_set(v_reuseFailAlloc_6215_, 17, v_b_6190_);
lean_ctor_set(v_reuseFailAlloc_6215_, 18, v_B_6191_);
lean_ctor_set(v_reuseFailAlloc_6215_, 19, v_h_6192_);
lean_ctor_set(v_reuseFailAlloc_6215_, 20, v_K_6193_);
lean_ctor_set(v_reuseFailAlloc_6215_, 21, v_k_6194_);
lean_ctor_set(v_reuseFailAlloc_6215_, 22, v_H_6195_);
lean_ctor_set(v_reuseFailAlloc_6215_, 23, v_m_6196_);
lean_ctor_set(v_reuseFailAlloc_6215_, 24, v_s_6197_);
lean_ctor_set(v_reuseFailAlloc_6215_, 25, v_S_6198_);
lean_ctor_set(v_reuseFailAlloc_6215_, 26, v_A_6199_);
lean_ctor_set(v_reuseFailAlloc_6215_, 27, v_n_6200_);
lean_ctor_set(v_reuseFailAlloc_6215_, 28, v_N_6201_);
lean_ctor_set(v_reuseFailAlloc_6215_, 29, v_V_6202_);
lean_ctor_set(v_reuseFailAlloc_6215_, 30, v_z_6203_);
lean_ctor_set(v_reuseFailAlloc_6215_, 31, v_zabbrev_6204_);
lean_ctor_set(v_reuseFailAlloc_6215_, 32, v___x_6212_);
lean_ctor_set(v_reuseFailAlloc_6215_, 33, v_O_6205_);
lean_ctor_set(v_reuseFailAlloc_6215_, 34, v_X_6206_);
lean_ctor_set(v_reuseFailAlloc_6215_, 35, v_x_6207_);
lean_ctor_set(v_reuseFailAlloc_6215_, 36, v_Z_6208_);
v___x_6214_ = v_reuseFailAlloc_6215_;
goto v_reusejp_6213_;
}
v_reusejp_6213_:
{
return v___x_6214_;
}
}
}
case 32:
{
lean_object* v_G_6218_; lean_object* v_y_6219_; lean_object* v_u_6220_; lean_object* v_Y_6221_; lean_object* v_D_6222_; lean_object* v_M_6223_; lean_object* v_L_6224_; lean_object* v_d_6225_; lean_object* v_Q_6226_; lean_object* v_q_6227_; lean_object* v_w_6228_; lean_object* v_W_6229_; lean_object* v_E_6230_; lean_object* v_e_6231_; lean_object* v_c_6232_; lean_object* v_F_6233_; lean_object* v_a_6234_; lean_object* v_b_6235_; lean_object* v_B_6236_; lean_object* v_h_6237_; lean_object* v_K_6238_; lean_object* v_k_6239_; lean_object* v_H_6240_; lean_object* v_m_6241_; lean_object* v_s_6242_; lean_object* v_S_6243_; lean_object* v_A_6244_; lean_object* v_n_6245_; lean_object* v_N_6246_; lean_object* v_V_6247_; lean_object* v_z_6248_; lean_object* v_zabbrev_6249_; lean_object* v_v_6250_; lean_object* v_X_6251_; lean_object* v_x_6252_; lean_object* v_Z_6253_; lean_object* v___x_6255_; uint8_t v_isShared_6256_; uint8_t v_isSharedCheck_6261_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_G_6218_ = lean_ctor_get(v_date_4561_, 0);
v_y_6219_ = lean_ctor_get(v_date_4561_, 1);
v_u_6220_ = lean_ctor_get(v_date_4561_, 2);
v_Y_6221_ = lean_ctor_get(v_date_4561_, 3);
v_D_6222_ = lean_ctor_get(v_date_4561_, 4);
v_M_6223_ = lean_ctor_get(v_date_4561_, 5);
v_L_6224_ = lean_ctor_get(v_date_4561_, 6);
v_d_6225_ = lean_ctor_get(v_date_4561_, 7);
v_Q_6226_ = lean_ctor_get(v_date_4561_, 8);
v_q_6227_ = lean_ctor_get(v_date_4561_, 9);
v_w_6228_ = lean_ctor_get(v_date_4561_, 10);
v_W_6229_ = lean_ctor_get(v_date_4561_, 11);
v_E_6230_ = lean_ctor_get(v_date_4561_, 12);
v_e_6231_ = lean_ctor_get(v_date_4561_, 13);
v_c_6232_ = lean_ctor_get(v_date_4561_, 14);
v_F_6233_ = lean_ctor_get(v_date_4561_, 15);
v_a_6234_ = lean_ctor_get(v_date_4561_, 16);
v_b_6235_ = lean_ctor_get(v_date_4561_, 17);
v_B_6236_ = lean_ctor_get(v_date_4561_, 18);
v_h_6237_ = lean_ctor_get(v_date_4561_, 19);
v_K_6238_ = lean_ctor_get(v_date_4561_, 20);
v_k_6239_ = lean_ctor_get(v_date_4561_, 21);
v_H_6240_ = lean_ctor_get(v_date_4561_, 22);
v_m_6241_ = lean_ctor_get(v_date_4561_, 23);
v_s_6242_ = lean_ctor_get(v_date_4561_, 24);
v_S_6243_ = lean_ctor_get(v_date_4561_, 25);
v_A_6244_ = lean_ctor_get(v_date_4561_, 26);
v_n_6245_ = lean_ctor_get(v_date_4561_, 27);
v_N_6246_ = lean_ctor_get(v_date_4561_, 28);
v_V_6247_ = lean_ctor_get(v_date_4561_, 29);
v_z_6248_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_6249_ = lean_ctor_get(v_date_4561_, 31);
v_v_6250_ = lean_ctor_get(v_date_4561_, 32);
v_X_6251_ = lean_ctor_get(v_date_4561_, 34);
v_x_6252_ = lean_ctor_get(v_date_4561_, 35);
v_Z_6253_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_6261_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_6261_ == 0)
{
lean_object* v_unused_6262_; 
v_unused_6262_ = lean_ctor_get(v_date_4561_, 33);
lean_dec(v_unused_6262_);
v___x_6255_ = v_date_4561_;
v_isShared_6256_ = v_isSharedCheck_6261_;
goto v_resetjp_6254_;
}
else
{
lean_inc(v_Z_6253_);
lean_inc(v_x_6252_);
lean_inc(v_X_6251_);
lean_inc(v_v_6250_);
lean_inc(v_zabbrev_6249_);
lean_inc(v_z_6248_);
lean_inc(v_V_6247_);
lean_inc(v_N_6246_);
lean_inc(v_n_6245_);
lean_inc(v_A_6244_);
lean_inc(v_S_6243_);
lean_inc(v_s_6242_);
lean_inc(v_m_6241_);
lean_inc(v_H_6240_);
lean_inc(v_k_6239_);
lean_inc(v_K_6238_);
lean_inc(v_h_6237_);
lean_inc(v_B_6236_);
lean_inc(v_b_6235_);
lean_inc(v_a_6234_);
lean_inc(v_F_6233_);
lean_inc(v_c_6232_);
lean_inc(v_e_6231_);
lean_inc(v_E_6230_);
lean_inc(v_W_6229_);
lean_inc(v_w_6228_);
lean_inc(v_q_6227_);
lean_inc(v_Q_6226_);
lean_inc(v_d_6225_);
lean_inc(v_L_6224_);
lean_inc(v_M_6223_);
lean_inc(v_D_6222_);
lean_inc(v_Y_6221_);
lean_inc(v_u_6220_);
lean_inc(v_y_6219_);
lean_inc(v_G_6218_);
lean_dec(v_date_4561_);
v___x_6255_ = lean_box(0);
v_isShared_6256_ = v_isSharedCheck_6261_;
goto v_resetjp_6254_;
}
v_resetjp_6254_:
{
lean_object* v___x_6257_; lean_object* v___x_6259_; 
v___x_6257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6257_, 0, v_data_4563_);
if (v_isShared_6256_ == 0)
{
lean_ctor_set(v___x_6255_, 33, v___x_6257_);
v___x_6259_ = v___x_6255_;
goto v_reusejp_6258_;
}
else
{
lean_object* v_reuseFailAlloc_6260_; 
v_reuseFailAlloc_6260_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6260_, 0, v_G_6218_);
lean_ctor_set(v_reuseFailAlloc_6260_, 1, v_y_6219_);
lean_ctor_set(v_reuseFailAlloc_6260_, 2, v_u_6220_);
lean_ctor_set(v_reuseFailAlloc_6260_, 3, v_Y_6221_);
lean_ctor_set(v_reuseFailAlloc_6260_, 4, v_D_6222_);
lean_ctor_set(v_reuseFailAlloc_6260_, 5, v_M_6223_);
lean_ctor_set(v_reuseFailAlloc_6260_, 6, v_L_6224_);
lean_ctor_set(v_reuseFailAlloc_6260_, 7, v_d_6225_);
lean_ctor_set(v_reuseFailAlloc_6260_, 8, v_Q_6226_);
lean_ctor_set(v_reuseFailAlloc_6260_, 9, v_q_6227_);
lean_ctor_set(v_reuseFailAlloc_6260_, 10, v_w_6228_);
lean_ctor_set(v_reuseFailAlloc_6260_, 11, v_W_6229_);
lean_ctor_set(v_reuseFailAlloc_6260_, 12, v_E_6230_);
lean_ctor_set(v_reuseFailAlloc_6260_, 13, v_e_6231_);
lean_ctor_set(v_reuseFailAlloc_6260_, 14, v_c_6232_);
lean_ctor_set(v_reuseFailAlloc_6260_, 15, v_F_6233_);
lean_ctor_set(v_reuseFailAlloc_6260_, 16, v_a_6234_);
lean_ctor_set(v_reuseFailAlloc_6260_, 17, v_b_6235_);
lean_ctor_set(v_reuseFailAlloc_6260_, 18, v_B_6236_);
lean_ctor_set(v_reuseFailAlloc_6260_, 19, v_h_6237_);
lean_ctor_set(v_reuseFailAlloc_6260_, 20, v_K_6238_);
lean_ctor_set(v_reuseFailAlloc_6260_, 21, v_k_6239_);
lean_ctor_set(v_reuseFailAlloc_6260_, 22, v_H_6240_);
lean_ctor_set(v_reuseFailAlloc_6260_, 23, v_m_6241_);
lean_ctor_set(v_reuseFailAlloc_6260_, 24, v_s_6242_);
lean_ctor_set(v_reuseFailAlloc_6260_, 25, v_S_6243_);
lean_ctor_set(v_reuseFailAlloc_6260_, 26, v_A_6244_);
lean_ctor_set(v_reuseFailAlloc_6260_, 27, v_n_6245_);
lean_ctor_set(v_reuseFailAlloc_6260_, 28, v_N_6246_);
lean_ctor_set(v_reuseFailAlloc_6260_, 29, v_V_6247_);
lean_ctor_set(v_reuseFailAlloc_6260_, 30, v_z_6248_);
lean_ctor_set(v_reuseFailAlloc_6260_, 31, v_zabbrev_6249_);
lean_ctor_set(v_reuseFailAlloc_6260_, 32, v_v_6250_);
lean_ctor_set(v_reuseFailAlloc_6260_, 33, v___x_6257_);
lean_ctor_set(v_reuseFailAlloc_6260_, 34, v_X_6251_);
lean_ctor_set(v_reuseFailAlloc_6260_, 35, v_x_6252_);
lean_ctor_set(v_reuseFailAlloc_6260_, 36, v_Z_6253_);
v___x_6259_ = v_reuseFailAlloc_6260_;
goto v_reusejp_6258_;
}
v_reusejp_6258_:
{
return v___x_6259_;
}
}
}
case 33:
{
lean_object* v_G_6263_; lean_object* v_y_6264_; lean_object* v_u_6265_; lean_object* v_Y_6266_; lean_object* v_D_6267_; lean_object* v_M_6268_; lean_object* v_L_6269_; lean_object* v_d_6270_; lean_object* v_Q_6271_; lean_object* v_q_6272_; lean_object* v_w_6273_; lean_object* v_W_6274_; lean_object* v_E_6275_; lean_object* v_e_6276_; lean_object* v_c_6277_; lean_object* v_F_6278_; lean_object* v_a_6279_; lean_object* v_b_6280_; lean_object* v_B_6281_; lean_object* v_h_6282_; lean_object* v_K_6283_; lean_object* v_k_6284_; lean_object* v_H_6285_; lean_object* v_m_6286_; lean_object* v_s_6287_; lean_object* v_S_6288_; lean_object* v_A_6289_; lean_object* v_n_6290_; lean_object* v_N_6291_; lean_object* v_V_6292_; lean_object* v_z_6293_; lean_object* v_zabbrev_6294_; lean_object* v_v_6295_; lean_object* v_O_6296_; lean_object* v_x_6297_; lean_object* v_Z_6298_; lean_object* v___x_6300_; uint8_t v_isShared_6301_; uint8_t v_isSharedCheck_6306_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_G_6263_ = lean_ctor_get(v_date_4561_, 0);
v_y_6264_ = lean_ctor_get(v_date_4561_, 1);
v_u_6265_ = lean_ctor_get(v_date_4561_, 2);
v_Y_6266_ = lean_ctor_get(v_date_4561_, 3);
v_D_6267_ = lean_ctor_get(v_date_4561_, 4);
v_M_6268_ = lean_ctor_get(v_date_4561_, 5);
v_L_6269_ = lean_ctor_get(v_date_4561_, 6);
v_d_6270_ = lean_ctor_get(v_date_4561_, 7);
v_Q_6271_ = lean_ctor_get(v_date_4561_, 8);
v_q_6272_ = lean_ctor_get(v_date_4561_, 9);
v_w_6273_ = lean_ctor_get(v_date_4561_, 10);
v_W_6274_ = lean_ctor_get(v_date_4561_, 11);
v_E_6275_ = lean_ctor_get(v_date_4561_, 12);
v_e_6276_ = lean_ctor_get(v_date_4561_, 13);
v_c_6277_ = lean_ctor_get(v_date_4561_, 14);
v_F_6278_ = lean_ctor_get(v_date_4561_, 15);
v_a_6279_ = lean_ctor_get(v_date_4561_, 16);
v_b_6280_ = lean_ctor_get(v_date_4561_, 17);
v_B_6281_ = lean_ctor_get(v_date_4561_, 18);
v_h_6282_ = lean_ctor_get(v_date_4561_, 19);
v_K_6283_ = lean_ctor_get(v_date_4561_, 20);
v_k_6284_ = lean_ctor_get(v_date_4561_, 21);
v_H_6285_ = lean_ctor_get(v_date_4561_, 22);
v_m_6286_ = lean_ctor_get(v_date_4561_, 23);
v_s_6287_ = lean_ctor_get(v_date_4561_, 24);
v_S_6288_ = lean_ctor_get(v_date_4561_, 25);
v_A_6289_ = lean_ctor_get(v_date_4561_, 26);
v_n_6290_ = lean_ctor_get(v_date_4561_, 27);
v_N_6291_ = lean_ctor_get(v_date_4561_, 28);
v_V_6292_ = lean_ctor_get(v_date_4561_, 29);
v_z_6293_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_6294_ = lean_ctor_get(v_date_4561_, 31);
v_v_6295_ = lean_ctor_get(v_date_4561_, 32);
v_O_6296_ = lean_ctor_get(v_date_4561_, 33);
v_x_6297_ = lean_ctor_get(v_date_4561_, 35);
v_Z_6298_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_6306_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_6306_ == 0)
{
lean_object* v_unused_6307_; 
v_unused_6307_ = lean_ctor_get(v_date_4561_, 34);
lean_dec(v_unused_6307_);
v___x_6300_ = v_date_4561_;
v_isShared_6301_ = v_isSharedCheck_6306_;
goto v_resetjp_6299_;
}
else
{
lean_inc(v_Z_6298_);
lean_inc(v_x_6297_);
lean_inc(v_O_6296_);
lean_inc(v_v_6295_);
lean_inc(v_zabbrev_6294_);
lean_inc(v_z_6293_);
lean_inc(v_V_6292_);
lean_inc(v_N_6291_);
lean_inc(v_n_6290_);
lean_inc(v_A_6289_);
lean_inc(v_S_6288_);
lean_inc(v_s_6287_);
lean_inc(v_m_6286_);
lean_inc(v_H_6285_);
lean_inc(v_k_6284_);
lean_inc(v_K_6283_);
lean_inc(v_h_6282_);
lean_inc(v_B_6281_);
lean_inc(v_b_6280_);
lean_inc(v_a_6279_);
lean_inc(v_F_6278_);
lean_inc(v_c_6277_);
lean_inc(v_e_6276_);
lean_inc(v_E_6275_);
lean_inc(v_W_6274_);
lean_inc(v_w_6273_);
lean_inc(v_q_6272_);
lean_inc(v_Q_6271_);
lean_inc(v_d_6270_);
lean_inc(v_L_6269_);
lean_inc(v_M_6268_);
lean_inc(v_D_6267_);
lean_inc(v_Y_6266_);
lean_inc(v_u_6265_);
lean_inc(v_y_6264_);
lean_inc(v_G_6263_);
lean_dec(v_date_4561_);
v___x_6300_ = lean_box(0);
v_isShared_6301_ = v_isSharedCheck_6306_;
goto v_resetjp_6299_;
}
v_resetjp_6299_:
{
lean_object* v___x_6302_; lean_object* v___x_6304_; 
v___x_6302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6302_, 0, v_data_4563_);
if (v_isShared_6301_ == 0)
{
lean_ctor_set(v___x_6300_, 34, v___x_6302_);
v___x_6304_ = v___x_6300_;
goto v_reusejp_6303_;
}
else
{
lean_object* v_reuseFailAlloc_6305_; 
v_reuseFailAlloc_6305_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6305_, 0, v_G_6263_);
lean_ctor_set(v_reuseFailAlloc_6305_, 1, v_y_6264_);
lean_ctor_set(v_reuseFailAlloc_6305_, 2, v_u_6265_);
lean_ctor_set(v_reuseFailAlloc_6305_, 3, v_Y_6266_);
lean_ctor_set(v_reuseFailAlloc_6305_, 4, v_D_6267_);
lean_ctor_set(v_reuseFailAlloc_6305_, 5, v_M_6268_);
lean_ctor_set(v_reuseFailAlloc_6305_, 6, v_L_6269_);
lean_ctor_set(v_reuseFailAlloc_6305_, 7, v_d_6270_);
lean_ctor_set(v_reuseFailAlloc_6305_, 8, v_Q_6271_);
lean_ctor_set(v_reuseFailAlloc_6305_, 9, v_q_6272_);
lean_ctor_set(v_reuseFailAlloc_6305_, 10, v_w_6273_);
lean_ctor_set(v_reuseFailAlloc_6305_, 11, v_W_6274_);
lean_ctor_set(v_reuseFailAlloc_6305_, 12, v_E_6275_);
lean_ctor_set(v_reuseFailAlloc_6305_, 13, v_e_6276_);
lean_ctor_set(v_reuseFailAlloc_6305_, 14, v_c_6277_);
lean_ctor_set(v_reuseFailAlloc_6305_, 15, v_F_6278_);
lean_ctor_set(v_reuseFailAlloc_6305_, 16, v_a_6279_);
lean_ctor_set(v_reuseFailAlloc_6305_, 17, v_b_6280_);
lean_ctor_set(v_reuseFailAlloc_6305_, 18, v_B_6281_);
lean_ctor_set(v_reuseFailAlloc_6305_, 19, v_h_6282_);
lean_ctor_set(v_reuseFailAlloc_6305_, 20, v_K_6283_);
lean_ctor_set(v_reuseFailAlloc_6305_, 21, v_k_6284_);
lean_ctor_set(v_reuseFailAlloc_6305_, 22, v_H_6285_);
lean_ctor_set(v_reuseFailAlloc_6305_, 23, v_m_6286_);
lean_ctor_set(v_reuseFailAlloc_6305_, 24, v_s_6287_);
lean_ctor_set(v_reuseFailAlloc_6305_, 25, v_S_6288_);
lean_ctor_set(v_reuseFailAlloc_6305_, 26, v_A_6289_);
lean_ctor_set(v_reuseFailAlloc_6305_, 27, v_n_6290_);
lean_ctor_set(v_reuseFailAlloc_6305_, 28, v_N_6291_);
lean_ctor_set(v_reuseFailAlloc_6305_, 29, v_V_6292_);
lean_ctor_set(v_reuseFailAlloc_6305_, 30, v_z_6293_);
lean_ctor_set(v_reuseFailAlloc_6305_, 31, v_zabbrev_6294_);
lean_ctor_set(v_reuseFailAlloc_6305_, 32, v_v_6295_);
lean_ctor_set(v_reuseFailAlloc_6305_, 33, v_O_6296_);
lean_ctor_set(v_reuseFailAlloc_6305_, 34, v___x_6302_);
lean_ctor_set(v_reuseFailAlloc_6305_, 35, v_x_6297_);
lean_ctor_set(v_reuseFailAlloc_6305_, 36, v_Z_6298_);
v___x_6304_ = v_reuseFailAlloc_6305_;
goto v_reusejp_6303_;
}
v_reusejp_6303_:
{
return v___x_6304_;
}
}
}
case 34:
{
lean_object* v_G_6308_; lean_object* v_y_6309_; lean_object* v_u_6310_; lean_object* v_Y_6311_; lean_object* v_D_6312_; lean_object* v_M_6313_; lean_object* v_L_6314_; lean_object* v_d_6315_; lean_object* v_Q_6316_; lean_object* v_q_6317_; lean_object* v_w_6318_; lean_object* v_W_6319_; lean_object* v_E_6320_; lean_object* v_e_6321_; lean_object* v_c_6322_; lean_object* v_F_6323_; lean_object* v_a_6324_; lean_object* v_b_6325_; lean_object* v_B_6326_; lean_object* v_h_6327_; lean_object* v_K_6328_; lean_object* v_k_6329_; lean_object* v_H_6330_; lean_object* v_m_6331_; lean_object* v_s_6332_; lean_object* v_S_6333_; lean_object* v_A_6334_; lean_object* v_n_6335_; lean_object* v_N_6336_; lean_object* v_V_6337_; lean_object* v_z_6338_; lean_object* v_zabbrev_6339_; lean_object* v_v_6340_; lean_object* v_O_6341_; lean_object* v_X_6342_; lean_object* v_Z_6343_; lean_object* v___x_6345_; uint8_t v_isShared_6346_; uint8_t v_isSharedCheck_6351_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_G_6308_ = lean_ctor_get(v_date_4561_, 0);
v_y_6309_ = lean_ctor_get(v_date_4561_, 1);
v_u_6310_ = lean_ctor_get(v_date_4561_, 2);
v_Y_6311_ = lean_ctor_get(v_date_4561_, 3);
v_D_6312_ = lean_ctor_get(v_date_4561_, 4);
v_M_6313_ = lean_ctor_get(v_date_4561_, 5);
v_L_6314_ = lean_ctor_get(v_date_4561_, 6);
v_d_6315_ = lean_ctor_get(v_date_4561_, 7);
v_Q_6316_ = lean_ctor_get(v_date_4561_, 8);
v_q_6317_ = lean_ctor_get(v_date_4561_, 9);
v_w_6318_ = lean_ctor_get(v_date_4561_, 10);
v_W_6319_ = lean_ctor_get(v_date_4561_, 11);
v_E_6320_ = lean_ctor_get(v_date_4561_, 12);
v_e_6321_ = lean_ctor_get(v_date_4561_, 13);
v_c_6322_ = lean_ctor_get(v_date_4561_, 14);
v_F_6323_ = lean_ctor_get(v_date_4561_, 15);
v_a_6324_ = lean_ctor_get(v_date_4561_, 16);
v_b_6325_ = lean_ctor_get(v_date_4561_, 17);
v_B_6326_ = lean_ctor_get(v_date_4561_, 18);
v_h_6327_ = lean_ctor_get(v_date_4561_, 19);
v_K_6328_ = lean_ctor_get(v_date_4561_, 20);
v_k_6329_ = lean_ctor_get(v_date_4561_, 21);
v_H_6330_ = lean_ctor_get(v_date_4561_, 22);
v_m_6331_ = lean_ctor_get(v_date_4561_, 23);
v_s_6332_ = lean_ctor_get(v_date_4561_, 24);
v_S_6333_ = lean_ctor_get(v_date_4561_, 25);
v_A_6334_ = lean_ctor_get(v_date_4561_, 26);
v_n_6335_ = lean_ctor_get(v_date_4561_, 27);
v_N_6336_ = lean_ctor_get(v_date_4561_, 28);
v_V_6337_ = lean_ctor_get(v_date_4561_, 29);
v_z_6338_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_6339_ = lean_ctor_get(v_date_4561_, 31);
v_v_6340_ = lean_ctor_get(v_date_4561_, 32);
v_O_6341_ = lean_ctor_get(v_date_4561_, 33);
v_X_6342_ = lean_ctor_get(v_date_4561_, 34);
v_Z_6343_ = lean_ctor_get(v_date_4561_, 36);
v_isSharedCheck_6351_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_6351_ == 0)
{
lean_object* v_unused_6352_; 
v_unused_6352_ = lean_ctor_get(v_date_4561_, 35);
lean_dec(v_unused_6352_);
v___x_6345_ = v_date_4561_;
v_isShared_6346_ = v_isSharedCheck_6351_;
goto v_resetjp_6344_;
}
else
{
lean_inc(v_Z_6343_);
lean_inc(v_X_6342_);
lean_inc(v_O_6341_);
lean_inc(v_v_6340_);
lean_inc(v_zabbrev_6339_);
lean_inc(v_z_6338_);
lean_inc(v_V_6337_);
lean_inc(v_N_6336_);
lean_inc(v_n_6335_);
lean_inc(v_A_6334_);
lean_inc(v_S_6333_);
lean_inc(v_s_6332_);
lean_inc(v_m_6331_);
lean_inc(v_H_6330_);
lean_inc(v_k_6329_);
lean_inc(v_K_6328_);
lean_inc(v_h_6327_);
lean_inc(v_B_6326_);
lean_inc(v_b_6325_);
lean_inc(v_a_6324_);
lean_inc(v_F_6323_);
lean_inc(v_c_6322_);
lean_inc(v_e_6321_);
lean_inc(v_E_6320_);
lean_inc(v_W_6319_);
lean_inc(v_w_6318_);
lean_inc(v_q_6317_);
lean_inc(v_Q_6316_);
lean_inc(v_d_6315_);
lean_inc(v_L_6314_);
lean_inc(v_M_6313_);
lean_inc(v_D_6312_);
lean_inc(v_Y_6311_);
lean_inc(v_u_6310_);
lean_inc(v_y_6309_);
lean_inc(v_G_6308_);
lean_dec(v_date_4561_);
v___x_6345_ = lean_box(0);
v_isShared_6346_ = v_isSharedCheck_6351_;
goto v_resetjp_6344_;
}
v_resetjp_6344_:
{
lean_object* v___x_6347_; lean_object* v___x_6349_; 
v___x_6347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6347_, 0, v_data_4563_);
if (v_isShared_6346_ == 0)
{
lean_ctor_set(v___x_6345_, 35, v___x_6347_);
v___x_6349_ = v___x_6345_;
goto v_reusejp_6348_;
}
else
{
lean_object* v_reuseFailAlloc_6350_; 
v_reuseFailAlloc_6350_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6350_, 0, v_G_6308_);
lean_ctor_set(v_reuseFailAlloc_6350_, 1, v_y_6309_);
lean_ctor_set(v_reuseFailAlloc_6350_, 2, v_u_6310_);
lean_ctor_set(v_reuseFailAlloc_6350_, 3, v_Y_6311_);
lean_ctor_set(v_reuseFailAlloc_6350_, 4, v_D_6312_);
lean_ctor_set(v_reuseFailAlloc_6350_, 5, v_M_6313_);
lean_ctor_set(v_reuseFailAlloc_6350_, 6, v_L_6314_);
lean_ctor_set(v_reuseFailAlloc_6350_, 7, v_d_6315_);
lean_ctor_set(v_reuseFailAlloc_6350_, 8, v_Q_6316_);
lean_ctor_set(v_reuseFailAlloc_6350_, 9, v_q_6317_);
lean_ctor_set(v_reuseFailAlloc_6350_, 10, v_w_6318_);
lean_ctor_set(v_reuseFailAlloc_6350_, 11, v_W_6319_);
lean_ctor_set(v_reuseFailAlloc_6350_, 12, v_E_6320_);
lean_ctor_set(v_reuseFailAlloc_6350_, 13, v_e_6321_);
lean_ctor_set(v_reuseFailAlloc_6350_, 14, v_c_6322_);
lean_ctor_set(v_reuseFailAlloc_6350_, 15, v_F_6323_);
lean_ctor_set(v_reuseFailAlloc_6350_, 16, v_a_6324_);
lean_ctor_set(v_reuseFailAlloc_6350_, 17, v_b_6325_);
lean_ctor_set(v_reuseFailAlloc_6350_, 18, v_B_6326_);
lean_ctor_set(v_reuseFailAlloc_6350_, 19, v_h_6327_);
lean_ctor_set(v_reuseFailAlloc_6350_, 20, v_K_6328_);
lean_ctor_set(v_reuseFailAlloc_6350_, 21, v_k_6329_);
lean_ctor_set(v_reuseFailAlloc_6350_, 22, v_H_6330_);
lean_ctor_set(v_reuseFailAlloc_6350_, 23, v_m_6331_);
lean_ctor_set(v_reuseFailAlloc_6350_, 24, v_s_6332_);
lean_ctor_set(v_reuseFailAlloc_6350_, 25, v_S_6333_);
lean_ctor_set(v_reuseFailAlloc_6350_, 26, v_A_6334_);
lean_ctor_set(v_reuseFailAlloc_6350_, 27, v_n_6335_);
lean_ctor_set(v_reuseFailAlloc_6350_, 28, v_N_6336_);
lean_ctor_set(v_reuseFailAlloc_6350_, 29, v_V_6337_);
lean_ctor_set(v_reuseFailAlloc_6350_, 30, v_z_6338_);
lean_ctor_set(v_reuseFailAlloc_6350_, 31, v_zabbrev_6339_);
lean_ctor_set(v_reuseFailAlloc_6350_, 32, v_v_6340_);
lean_ctor_set(v_reuseFailAlloc_6350_, 33, v_O_6341_);
lean_ctor_set(v_reuseFailAlloc_6350_, 34, v_X_6342_);
lean_ctor_set(v_reuseFailAlloc_6350_, 35, v___x_6347_);
lean_ctor_set(v_reuseFailAlloc_6350_, 36, v_Z_6343_);
v___x_6349_ = v_reuseFailAlloc_6350_;
goto v_reusejp_6348_;
}
v_reusejp_6348_:
{
return v___x_6349_;
}
}
}
default: 
{
lean_object* v_G_6353_; lean_object* v_y_6354_; lean_object* v_u_6355_; lean_object* v_Y_6356_; lean_object* v_D_6357_; lean_object* v_M_6358_; lean_object* v_L_6359_; lean_object* v_d_6360_; lean_object* v_Q_6361_; lean_object* v_q_6362_; lean_object* v_w_6363_; lean_object* v_W_6364_; lean_object* v_E_6365_; lean_object* v_e_6366_; lean_object* v_c_6367_; lean_object* v_F_6368_; lean_object* v_a_6369_; lean_object* v_b_6370_; lean_object* v_B_6371_; lean_object* v_h_6372_; lean_object* v_K_6373_; lean_object* v_k_6374_; lean_object* v_H_6375_; lean_object* v_m_6376_; lean_object* v_s_6377_; lean_object* v_S_6378_; lean_object* v_A_6379_; lean_object* v_n_6380_; lean_object* v_N_6381_; lean_object* v_V_6382_; lean_object* v_z_6383_; lean_object* v_zabbrev_6384_; lean_object* v_v_6385_; lean_object* v_O_6386_; lean_object* v_X_6387_; lean_object* v_x_6388_; lean_object* v___x_6390_; uint8_t v_isShared_6391_; uint8_t v_isSharedCheck_6396_; 
lean_dec_ref_known(v_modifier_4562_, 0);
v_G_6353_ = lean_ctor_get(v_date_4561_, 0);
v_y_6354_ = lean_ctor_get(v_date_4561_, 1);
v_u_6355_ = lean_ctor_get(v_date_4561_, 2);
v_Y_6356_ = lean_ctor_get(v_date_4561_, 3);
v_D_6357_ = lean_ctor_get(v_date_4561_, 4);
v_M_6358_ = lean_ctor_get(v_date_4561_, 5);
v_L_6359_ = lean_ctor_get(v_date_4561_, 6);
v_d_6360_ = lean_ctor_get(v_date_4561_, 7);
v_Q_6361_ = lean_ctor_get(v_date_4561_, 8);
v_q_6362_ = lean_ctor_get(v_date_4561_, 9);
v_w_6363_ = lean_ctor_get(v_date_4561_, 10);
v_W_6364_ = lean_ctor_get(v_date_4561_, 11);
v_E_6365_ = lean_ctor_get(v_date_4561_, 12);
v_e_6366_ = lean_ctor_get(v_date_4561_, 13);
v_c_6367_ = lean_ctor_get(v_date_4561_, 14);
v_F_6368_ = lean_ctor_get(v_date_4561_, 15);
v_a_6369_ = lean_ctor_get(v_date_4561_, 16);
v_b_6370_ = lean_ctor_get(v_date_4561_, 17);
v_B_6371_ = lean_ctor_get(v_date_4561_, 18);
v_h_6372_ = lean_ctor_get(v_date_4561_, 19);
v_K_6373_ = lean_ctor_get(v_date_4561_, 20);
v_k_6374_ = lean_ctor_get(v_date_4561_, 21);
v_H_6375_ = lean_ctor_get(v_date_4561_, 22);
v_m_6376_ = lean_ctor_get(v_date_4561_, 23);
v_s_6377_ = lean_ctor_get(v_date_4561_, 24);
v_S_6378_ = lean_ctor_get(v_date_4561_, 25);
v_A_6379_ = lean_ctor_get(v_date_4561_, 26);
v_n_6380_ = lean_ctor_get(v_date_4561_, 27);
v_N_6381_ = lean_ctor_get(v_date_4561_, 28);
v_V_6382_ = lean_ctor_get(v_date_4561_, 29);
v_z_6383_ = lean_ctor_get(v_date_4561_, 30);
v_zabbrev_6384_ = lean_ctor_get(v_date_4561_, 31);
v_v_6385_ = lean_ctor_get(v_date_4561_, 32);
v_O_6386_ = lean_ctor_get(v_date_4561_, 33);
v_X_6387_ = lean_ctor_get(v_date_4561_, 34);
v_x_6388_ = lean_ctor_get(v_date_4561_, 35);
v_isSharedCheck_6396_ = !lean_is_exclusive(v_date_4561_);
if (v_isSharedCheck_6396_ == 0)
{
lean_object* v_unused_6397_; 
v_unused_6397_ = lean_ctor_get(v_date_4561_, 36);
lean_dec(v_unused_6397_);
v___x_6390_ = v_date_4561_;
v_isShared_6391_ = v_isSharedCheck_6396_;
goto v_resetjp_6389_;
}
else
{
lean_inc(v_x_6388_);
lean_inc(v_X_6387_);
lean_inc(v_O_6386_);
lean_inc(v_v_6385_);
lean_inc(v_zabbrev_6384_);
lean_inc(v_z_6383_);
lean_inc(v_V_6382_);
lean_inc(v_N_6381_);
lean_inc(v_n_6380_);
lean_inc(v_A_6379_);
lean_inc(v_S_6378_);
lean_inc(v_s_6377_);
lean_inc(v_m_6376_);
lean_inc(v_H_6375_);
lean_inc(v_k_6374_);
lean_inc(v_K_6373_);
lean_inc(v_h_6372_);
lean_inc(v_B_6371_);
lean_inc(v_b_6370_);
lean_inc(v_a_6369_);
lean_inc(v_F_6368_);
lean_inc(v_c_6367_);
lean_inc(v_e_6366_);
lean_inc(v_E_6365_);
lean_inc(v_W_6364_);
lean_inc(v_w_6363_);
lean_inc(v_q_6362_);
lean_inc(v_Q_6361_);
lean_inc(v_d_6360_);
lean_inc(v_L_6359_);
lean_inc(v_M_6358_);
lean_inc(v_D_6357_);
lean_inc(v_Y_6356_);
lean_inc(v_u_6355_);
lean_inc(v_y_6354_);
lean_inc(v_G_6353_);
lean_dec(v_date_4561_);
v___x_6390_ = lean_box(0);
v_isShared_6391_ = v_isSharedCheck_6396_;
goto v_resetjp_6389_;
}
v_resetjp_6389_:
{
lean_object* v___x_6392_; lean_object* v___x_6394_; 
v___x_6392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6392_, 0, v_data_4563_);
if (v_isShared_6391_ == 0)
{
lean_ctor_set(v___x_6390_, 36, v___x_6392_);
v___x_6394_ = v___x_6390_;
goto v_reusejp_6393_;
}
else
{
lean_object* v_reuseFailAlloc_6395_; 
v_reuseFailAlloc_6395_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6395_, 0, v_G_6353_);
lean_ctor_set(v_reuseFailAlloc_6395_, 1, v_y_6354_);
lean_ctor_set(v_reuseFailAlloc_6395_, 2, v_u_6355_);
lean_ctor_set(v_reuseFailAlloc_6395_, 3, v_Y_6356_);
lean_ctor_set(v_reuseFailAlloc_6395_, 4, v_D_6357_);
lean_ctor_set(v_reuseFailAlloc_6395_, 5, v_M_6358_);
lean_ctor_set(v_reuseFailAlloc_6395_, 6, v_L_6359_);
lean_ctor_set(v_reuseFailAlloc_6395_, 7, v_d_6360_);
lean_ctor_set(v_reuseFailAlloc_6395_, 8, v_Q_6361_);
lean_ctor_set(v_reuseFailAlloc_6395_, 9, v_q_6362_);
lean_ctor_set(v_reuseFailAlloc_6395_, 10, v_w_6363_);
lean_ctor_set(v_reuseFailAlloc_6395_, 11, v_W_6364_);
lean_ctor_set(v_reuseFailAlloc_6395_, 12, v_E_6365_);
lean_ctor_set(v_reuseFailAlloc_6395_, 13, v_e_6366_);
lean_ctor_set(v_reuseFailAlloc_6395_, 14, v_c_6367_);
lean_ctor_set(v_reuseFailAlloc_6395_, 15, v_F_6368_);
lean_ctor_set(v_reuseFailAlloc_6395_, 16, v_a_6369_);
lean_ctor_set(v_reuseFailAlloc_6395_, 17, v_b_6370_);
lean_ctor_set(v_reuseFailAlloc_6395_, 18, v_B_6371_);
lean_ctor_set(v_reuseFailAlloc_6395_, 19, v_h_6372_);
lean_ctor_set(v_reuseFailAlloc_6395_, 20, v_K_6373_);
lean_ctor_set(v_reuseFailAlloc_6395_, 21, v_k_6374_);
lean_ctor_set(v_reuseFailAlloc_6395_, 22, v_H_6375_);
lean_ctor_set(v_reuseFailAlloc_6395_, 23, v_m_6376_);
lean_ctor_set(v_reuseFailAlloc_6395_, 24, v_s_6377_);
lean_ctor_set(v_reuseFailAlloc_6395_, 25, v_S_6378_);
lean_ctor_set(v_reuseFailAlloc_6395_, 26, v_A_6379_);
lean_ctor_set(v_reuseFailAlloc_6395_, 27, v_n_6380_);
lean_ctor_set(v_reuseFailAlloc_6395_, 28, v_N_6381_);
lean_ctor_set(v_reuseFailAlloc_6395_, 29, v_V_6382_);
lean_ctor_set(v_reuseFailAlloc_6395_, 30, v_z_6383_);
lean_ctor_set(v_reuseFailAlloc_6395_, 31, v_zabbrev_6384_);
lean_ctor_set(v_reuseFailAlloc_6395_, 32, v_v_6385_);
lean_ctor_set(v_reuseFailAlloc_6395_, 33, v_O_6386_);
lean_ctor_set(v_reuseFailAlloc_6395_, 34, v_X_6387_);
lean_ctor_set(v_reuseFailAlloc_6395_, 35, v_x_6388_);
lean_ctor_set(v_reuseFailAlloc_6395_, 36, v___x_6392_);
v___x_6394_ = v_reuseFailAlloc_6395_;
goto v_reusejp_6393_;
}
v_reusejp_6393_:
{
return v___x_6394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object* v_year_6398_, uint8_t v_x_6399_){
_start:
{
if (v_x_6399_ == 0)
{
lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; 
v___x_6400_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6401_ = lean_int_add(v_year_6398_, v___x_6400_);
v___x_6402_ = lean_int_neg(v___x_6401_);
lean_dec(v___x_6401_);
return v___x_6402_;
}
else
{
lean_inc(v_year_6398_);
return v_year_6398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object* v_year_6403_, lean_object* v_x_6404_){
_start:
{
uint8_t v_x_42__boxed_6405_; lean_object* v_res_6406_; 
v_x_42__boxed_6405_ = lean_unbox(v_x_6404_);
v_res_6406_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6403_, v_x_42__boxed_6405_);
lean_dec(v_year_6403_);
return v_res_6406_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t v_x_6407_){
_start:
{
switch(v_x_6407_)
{
case 1:
{
uint8_t v___x_6408_; 
v___x_6408_ = 1;
return v___x_6408_;
}
case 2:
{
uint8_t v___x_6409_; 
v___x_6409_ = 1;
return v___x_6409_;
}
default: 
{
uint8_t v___x_6410_; 
v___x_6410_ = 0;
return v___x_6410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object* v_x_6411_){
_start:
{
uint8_t v_x_28__boxed_6412_; uint8_t v_res_6413_; lean_object* v_r_6414_; 
v_x_28__boxed_6412_ = lean_unbox(v_x_6411_);
v_res_6413_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_28__boxed_6412_);
v_r_6414_ = lean_box(v_res_6413_);
return v_r_6414_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(uint8_t v_x_6415_){
_start:
{
switch(v_x_6415_)
{
case 3:
{
uint8_t v___x_6416_; 
v___x_6416_ = 1;
return v___x_6416_;
}
case 4:
{
uint8_t v___x_6417_; 
v___x_6417_ = 1;
return v___x_6417_;
}
case 5:
{
uint8_t v___x_6418_; 
v___x_6418_ = 1;
return v___x_6418_;
}
default: 
{
uint8_t v___x_6419_; 
v___x_6419_ = 0;
return v___x_6419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object* v_x_6420_){
_start:
{
uint8_t v_x_38__boxed_6421_; uint8_t v_res_6422_; lean_object* v_r_6423_; 
v_x_38__boxed_6421_ = lean_unbox(v_x_6420_);
v_res_6422_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_x_38__boxed_6421_);
v_r_6423_ = lean_box(v_res_6422_);
return v_r_6423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object* v_val_6424_, lean_object* v_x_6425_){
_start:
{
lean_inc_ref(v_val_6424_);
return v_val_6424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object* v_val_6426_, lean_object* v_x_6427_){
_start:
{
lean_object* v_res_6428_; 
v_res_6428_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v_val_6426_, v_x_6427_);
lean_dec_ref(v_val_6426_);
return v_res_6428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object* v___y_6429_, lean_object* v_00___6430_){
_start:
{
uint8_t v___x_6431_; lean_object* v___x_6432_; 
v___x_6431_ = 1;
v___x_6432_ = l_Std_Time_TimeZone_Offset_toIsoString(v___y_6429_, v___x_6431_);
return v___x_6432_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1(void){
_start:
{
lean_object* v___x_6435_; lean_object* v___x_6436_; 
v___x_6435_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6436_ = lean_int_neg(v___x_6435_);
return v___x_6436_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2(void){
_start:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; 
v___x_6437_ = lean_unsigned_to_nat(1000000u);
v___x_6438_ = lean_nat_to_int(v___x_6437_);
return v___x_6438_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3(void){
_start:
{
lean_object* v___x_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; 
v___x_6439_ = lean_unsigned_to_nat(1000000000u);
v___x_6440_ = lean_unsigned_to_nat(0u);
v___x_6441_ = lean_nat_mod(v___x_6440_, v___x_6439_);
return v___x_6441_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4(void){
_start:
{
lean_object* v___x_6442_; lean_object* v___x_6443_; 
v___x_6442_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3);
v___x_6443_ = lean_nat_to_int(v___x_6442_);
return v___x_6443_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5(void){
_start:
{
lean_object* v___x_6444_; uint8_t v___x_6445_; lean_object* v___x_6446_; 
v___x_6444_ = lean_unsigned_to_nat(0u);
v___x_6445_ = 1;
v___x_6446_ = l_Std_Time_Second_instOfNatOrdinal(v___x_6445_, v___x_6444_);
return v___x_6446_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6(void){
_start:
{
lean_object* v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; 
v___x_6447_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_6448_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6449_ = lean_int_add(v___x_6448_, v___x_6447_);
return v___x_6449_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7(void){
_start:
{
lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; 
v___x_6450_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6451_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6452_ = lean_int_sub(v___x_6451_, v___x_6450_);
return v___x_6452_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8(void){
_start:
{
lean_object* v___x_6453_; lean_object* v___x_6454_; lean_object* v_range_6455_; 
v___x_6453_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6454_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7);
v_range_6455_ = lean_int_add(v___x_6454_, v___x_6453_);
return v_range_6455_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9(void){
_start:
{
lean_object* v___x_6456_; lean_object* v___x_6457_; 
v___x_6456_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6457_ = lean_int_sub(v___x_6456_, v___x_6456_);
return v___x_6457_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10(void){
_start:
{
lean_object* v_range_6458_; lean_object* v___x_6459_; lean_object* v___x_6460_; 
v_range_6458_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6459_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9);
v___x_6460_ = lean_int_emod(v___x_6459_, v_range_6458_);
return v___x_6460_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11(void){
_start:
{
lean_object* v_range_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; 
v_range_6461_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6462_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10);
v___x_6463_ = lean_int_add(v___x_6462_, v_range_6461_);
return v___x_6463_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12(void){
_start:
{
lean_object* v_range_6464_; lean_object* v___x_6465_; lean_object* v___x_6466_; 
v_range_6464_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6465_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11);
v___x_6466_ = lean_int_emod(v___x_6465_, v_range_6464_);
return v___x_6466_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13(void){
_start:
{
lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; 
v___x_6467_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6468_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12);
v___x_6469_ = lean_int_add(v___x_6468_, v___x_6467_);
return v___x_6469_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14(void){
_start:
{
lean_object* v___x_6470_; lean_object* v___x_6471_; 
v___x_6470_ = lean_unsigned_to_nat(30u);
v___x_6471_ = lean_nat_to_int(v___x_6470_);
return v___x_6471_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15(void){
_start:
{
lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; 
v___x_6472_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14);
v___x_6473_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6474_ = lean_int_add(v___x_6473_, v___x_6472_);
return v___x_6474_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16(void){
_start:
{
lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; 
v___x_6475_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6476_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6477_ = lean_int_sub(v___x_6476_, v___x_6475_);
return v___x_6477_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17(void){
_start:
{
lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v_range_6480_; 
v___x_6478_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6479_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v_range_6480_ = lean_int_add(v___x_6479_, v___x_6478_);
return v_range_6480_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18(void){
_start:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; 
v___x_6481_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6482_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6483_ = lean_int_sub(v___x_6482_, v___x_6481_);
return v___x_6483_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19(void){
_start:
{
lean_object* v_range_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; 
v_range_6484_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6485_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6486_ = lean_int_emod(v___x_6485_, v_range_6484_);
return v___x_6486_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20(void){
_start:
{
lean_object* v_range_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; 
v_range_6487_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6488_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19);
v___x_6489_ = lean_int_add(v___x_6488_, v_range_6487_);
return v___x_6489_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21(void){
_start:
{
lean_object* v_range_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; 
v_range_6490_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6491_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20);
v___x_6492_ = lean_int_emod(v___x_6491_, v_range_6490_);
return v___x_6492_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22(void){
_start:
{
lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; 
v___x_6493_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6494_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21);
v___x_6495_ = lean_int_add(v___x_6494_, v___x_6493_);
return v___x_6495_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23(void){
_start:
{
lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6496_ = lean_unsigned_to_nat(11u);
v___x_6497_ = lean_nat_to_int(v___x_6496_);
return v___x_6497_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24(void){
_start:
{
lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; 
v___x_6498_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23);
v___x_6499_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6500_ = lean_int_add(v___x_6499_, v___x_6498_);
return v___x_6500_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25(void){
_start:
{
lean_object* v___x_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; 
v___x_6501_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6502_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6503_ = lean_int_sub(v___x_6502_, v___x_6501_);
return v___x_6503_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26(void){
_start:
{
lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v_range_6506_; 
v___x_6504_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6505_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25);
v_range_6506_ = lean_int_add(v___x_6505_, v___x_6504_);
return v_range_6506_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27(void){
_start:
{
lean_object* v_range_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; 
v_range_6507_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6508_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6509_ = lean_int_emod(v___x_6508_, v_range_6507_);
return v___x_6509_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28(void){
_start:
{
lean_object* v_range_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; 
v_range_6510_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6511_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27);
v___x_6512_ = lean_int_add(v___x_6511_, v_range_6510_);
return v___x_6512_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29(void){
_start:
{
lean_object* v_range_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; 
v_range_6513_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6514_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28);
v___x_6515_ = lean_int_emod(v___x_6514_, v_range_6513_);
return v___x_6515_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30(void){
_start:
{
lean_object* v___x_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; 
v___x_6516_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6517_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29);
v___x_6518_ = lean_int_add(v___x_6517_, v___x_6516_);
return v___x_6518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object* v_builder_6519_, lean_object* v_aw_6520_){
_start:
{
lean_object* v___y_6522_; lean_object* v___y_6523_; lean_object* v___y_6562_; lean_object* v___y_6563_; lean_object* v___y_6566_; lean_object* v___y_6567_; lean_object* v___y_6568_; lean_object* v___y_6569_; lean_object* v___y_6570_; uint8_t v___y_6571_; lean_object* v___y_6579_; lean_object* v___y_6580_; lean_object* v___y_6581_; lean_object* v___y_6582_; uint8_t v___y_6583_; lean_object* v___y_6584_; lean_object* v___y_6585_; lean_object* v___y_6590_; uint8_t v___y_6591_; lean_object* v___y_6592_; lean_object* v___y_6593_; lean_object* v___y_6594_; lean_object* v___y_6595_; lean_object* v_G_6603_; lean_object* v_y_6604_; lean_object* v_u_6605_; lean_object* v_Y_6606_; lean_object* v_M_6607_; lean_object* v_L_6608_; lean_object* v_d_6609_; lean_object* v_a_6610_; lean_object* v_b_6611_; lean_object* v_B_6612_; lean_object* v_h_6613_; lean_object* v_K_6614_; lean_object* v_k_6615_; lean_object* v_H_6616_; lean_object* v_m_6617_; lean_object* v_s_6618_; lean_object* v_S_6619_; lean_object* v_A_6620_; lean_object* v_n_6621_; lean_object* v_N_6622_; lean_object* v_V_6623_; lean_object* v_z_6624_; lean_object* v_zabbrev_6625_; lean_object* v_v_6626_; lean_object* v_O_6627_; lean_object* v_X_6628_; lean_object* v_x_6629_; lean_object* v_Z_6630_; lean_object* v___y_6632_; lean_object* v___y_6633_; lean_object* v___y_6634_; uint8_t v___y_6635_; lean_object* v___y_6636_; lean_object* v___y_6637_; lean_object* v___y_6638_; lean_object* v___y_6639_; lean_object* v___y_6640_; lean_object* v___y_6649_; lean_object* v___y_6650_; uint8_t v___y_6651_; lean_object* v___y_6652_; lean_object* v___y_6653_; lean_object* v___y_6654_; lean_object* v___y_6655_; lean_object* v___y_6656_; lean_object* v___y_6661_; lean_object* v___y_6662_; lean_object* v___y_6663_; uint8_t v___y_6664_; lean_object* v___y_6665_; lean_object* v___y_6666_; lean_object* v___y_6667_; lean_object* v___y_6671_; uint8_t v___y_6672_; lean_object* v___y_6673_; lean_object* v___y_6674_; lean_object* v___y_6675_; lean_object* v___y_6676_; lean_object* v___y_6680_; lean_object* v___y_6681_; uint8_t v___y_6682_; lean_object* v___y_6683_; lean_object* v___y_6684_; lean_object* v___y_6692_; uint8_t v___y_6693_; lean_object* v___y_6694_; lean_object* v___y_6695_; lean_object* v___y_6696_; uint8_t v_val_6697_; lean_object* v___y_6705_; lean_object* v___y_6706_; uint8_t v___y_6707_; lean_object* v___y_6708_; lean_object* v___y_6709_; lean_object* v___y_6719_; uint8_t v___y_6720_; lean_object* v___y_6721_; lean_object* v___y_6722_; uint8_t v___y_6723_; uint8_t v___y_6730_; lean_object* v___y_6731_; lean_object* v___y_6732_; lean_object* v___y_6733_; lean_object* v___y_6738_; uint8_t v___y_6739_; lean_object* v___y_6740_; lean_object* v___y_6744_; lean_object* v___y_6745_; lean_object* v___y_6746_; lean_object* v___y_6753_; lean_object* v___y_6754_; lean_object* v___y_6755_; lean_object* v___y_6760_; 
v_G_6603_ = lean_ctor_get(v_builder_6519_, 0);
lean_inc(v_G_6603_);
v_y_6604_ = lean_ctor_get(v_builder_6519_, 1);
lean_inc(v_y_6604_);
v_u_6605_ = lean_ctor_get(v_builder_6519_, 2);
lean_inc(v_u_6605_);
v_Y_6606_ = lean_ctor_get(v_builder_6519_, 3);
lean_inc(v_Y_6606_);
v_M_6607_ = lean_ctor_get(v_builder_6519_, 5);
lean_inc(v_M_6607_);
v_L_6608_ = lean_ctor_get(v_builder_6519_, 6);
lean_inc(v_L_6608_);
v_d_6609_ = lean_ctor_get(v_builder_6519_, 7);
lean_inc(v_d_6609_);
v_a_6610_ = lean_ctor_get(v_builder_6519_, 16);
lean_inc(v_a_6610_);
v_b_6611_ = lean_ctor_get(v_builder_6519_, 17);
lean_inc(v_b_6611_);
v_B_6612_ = lean_ctor_get(v_builder_6519_, 18);
lean_inc(v_B_6612_);
v_h_6613_ = lean_ctor_get(v_builder_6519_, 19);
lean_inc(v_h_6613_);
v_K_6614_ = lean_ctor_get(v_builder_6519_, 20);
lean_inc(v_K_6614_);
v_k_6615_ = lean_ctor_get(v_builder_6519_, 21);
lean_inc(v_k_6615_);
v_H_6616_ = lean_ctor_get(v_builder_6519_, 22);
lean_inc(v_H_6616_);
v_m_6617_ = lean_ctor_get(v_builder_6519_, 23);
lean_inc(v_m_6617_);
v_s_6618_ = lean_ctor_get(v_builder_6519_, 24);
lean_inc(v_s_6618_);
v_S_6619_ = lean_ctor_get(v_builder_6519_, 25);
lean_inc(v_S_6619_);
v_A_6620_ = lean_ctor_get(v_builder_6519_, 26);
lean_inc(v_A_6620_);
v_n_6621_ = lean_ctor_get(v_builder_6519_, 27);
lean_inc(v_n_6621_);
v_N_6622_ = lean_ctor_get(v_builder_6519_, 28);
lean_inc(v_N_6622_);
v_V_6623_ = lean_ctor_get(v_builder_6519_, 29);
lean_inc(v_V_6623_);
v_z_6624_ = lean_ctor_get(v_builder_6519_, 30);
lean_inc(v_z_6624_);
v_zabbrev_6625_ = lean_ctor_get(v_builder_6519_, 31);
lean_inc(v_zabbrev_6625_);
v_v_6626_ = lean_ctor_get(v_builder_6519_, 32);
lean_inc(v_v_6626_);
v_O_6627_ = lean_ctor_get(v_builder_6519_, 33);
lean_inc(v_O_6627_);
v_X_6628_ = lean_ctor_get(v_builder_6519_, 34);
lean_inc(v_X_6628_);
v_x_6629_ = lean_ctor_get(v_builder_6519_, 35);
lean_inc(v_x_6629_);
v_Z_6630_ = lean_ctor_get(v_builder_6519_, 36);
lean_inc(v_Z_6630_);
lean_dec_ref(v_builder_6519_);
if (lean_obj_tag(v_O_6627_) == 0)
{
if (lean_obj_tag(v_X_6628_) == 0)
{
if (lean_obj_tag(v_x_6629_) == 0)
{
if (lean_obj_tag(v_Z_6630_) == 0)
{
lean_object* v___x_6767_; 
v___x_6767_ = l_Std_Time_TimeZone_Offset_zero;
v___y_6760_ = v___x_6767_;
goto v___jp_6759_;
}
else
{
lean_object* v_val_6768_; 
v_val_6768_ = lean_ctor_get(v_Z_6630_, 0);
lean_inc(v_val_6768_);
lean_dec_ref_known(v_Z_6630_, 1);
v___y_6760_ = v_val_6768_;
goto v___jp_6759_;
}
}
else
{
lean_object* v_val_6769_; 
lean_dec(v_Z_6630_);
v_val_6769_ = lean_ctor_get(v_x_6629_, 0);
lean_inc(v_val_6769_);
lean_dec_ref_known(v_x_6629_, 1);
v___y_6760_ = v_val_6769_;
goto v___jp_6759_;
}
}
else
{
lean_object* v_val_6770_; 
lean_dec(v_Z_6630_);
lean_dec(v_x_6629_);
v_val_6770_ = lean_ctor_get(v_X_6628_, 0);
lean_inc(v_val_6770_);
lean_dec_ref_known(v_X_6628_, 1);
v___y_6760_ = v_val_6770_;
goto v___jp_6759_;
}
}
else
{
lean_object* v_val_6771_; 
lean_dec(v_Z_6630_);
lean_dec(v_x_6629_);
lean_dec(v_X_6628_);
v_val_6771_ = lean_ctor_get(v_O_6627_, 0);
lean_inc(v_val_6771_);
lean_dec_ref_known(v_O_6627_, 1);
v___y_6760_ = v_val_6771_;
goto v___jp_6759_;
}
v___jp_6521_:
{
if (lean_obj_tag(v___y_6522_) == 0)
{
lean_object* v___x_6524_; 
lean_dec_ref(v___y_6523_);
v___x_6524_ = lean_box(0);
return v___x_6524_;
}
else
{
lean_object* v_val_6525_; lean_object* v___x_6527_; uint8_t v_isShared_6528_; uint8_t v_isSharedCheck_6560_; 
v_val_6525_ = lean_ctor_get(v___y_6522_, 0);
v_isSharedCheck_6560_ = !lean_is_exclusive(v___y_6522_);
if (v_isSharedCheck_6560_ == 0)
{
v___x_6527_ = v___y_6522_;
v_isShared_6528_ = v_isSharedCheck_6560_;
goto v_resetjp_6526_;
}
else
{
lean_inc(v_val_6525_);
lean_dec(v___y_6522_);
v___x_6527_ = lean_box(0);
v_isShared_6528_ = v_isSharedCheck_6560_;
goto v_resetjp_6526_;
}
v_resetjp_6526_:
{
lean_object* v_offset_6529_; lean_object* v_name_6530_; lean_object* v_abbreviation_6531_; uint8_t v_isDST_6532_; uint8_t v___x_6533_; uint8_t v___x_6534_; lean_object* v_ltt_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; lean_object* v_wt_6539_; lean_object* v_ltt_6540_; lean_object* v_tz_6541_; lean_object* v_offset_6542_; lean_object* v_second_6543_; lean_object* v_nano_6544_; lean_object* v___f_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v___x_6558_; 
v_offset_6529_ = lean_ctor_get(v___y_6523_, 0);
lean_inc(v_offset_6529_);
v_name_6530_ = lean_ctor_get(v___y_6523_, 1);
lean_inc_ref(v_name_6530_);
v_abbreviation_6531_ = lean_ctor_get(v___y_6523_, 2);
lean_inc_ref(v_abbreviation_6531_);
v_isDST_6532_ = lean_ctor_get_uint8(v___y_6523_, sizeof(void*)*3);
lean_dec_ref(v___y_6523_);
v___x_6533_ = 0;
v___x_6534_ = 1;
v_ltt_6535_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6535_, 0, v_offset_6529_);
lean_ctor_set(v_ltt_6535_, 1, v_abbreviation_6531_);
lean_ctor_set(v_ltt_6535_, 2, v_name_6530_);
lean_ctor_set_uint8(v_ltt_6535_, sizeof(void*)*3, v_isDST_6532_);
lean_ctor_set_uint8(v_ltt_6535_, sizeof(void*)*3 + 1, v___x_6533_);
lean_ctor_set_uint8(v_ltt_6535_, sizeof(void*)*3 + 2, v___x_6534_);
v___x_6536_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6537_ = lean_box(0);
v___x_6538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6538_, 0, v_ltt_6535_);
lean_ctor_set(v___x_6538_, 1, v___x_6536_);
lean_ctor_set(v___x_6538_, 2, v___x_6537_);
lean_inc(v_val_6525_);
v_wt_6539_ = l_Std_Time_PlainDateTime_toWallTime(v_val_6525_);
lean_inc_ref(v___x_6538_);
v_ltt_6540_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_6538_, v_wt_6539_);
v_tz_6541_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_6540_);
lean_dec_ref(v_ltt_6540_);
v_offset_6542_ = lean_ctor_get(v_tz_6541_, 0);
lean_inc(v_offset_6542_);
v_second_6543_ = lean_ctor_get(v_wt_6539_, 0);
lean_inc(v_second_6543_);
v_nano_6544_ = lean_ctor_get(v_wt_6539_, 1);
lean_inc(v_nano_6544_);
lean_dec_ref(v_wt_6539_);
v___f_6545_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6545_, 0, v_val_6525_);
v___x_6546_ = lean_mk_thunk(v___f_6545_);
v___x_6547_ = lean_int_neg(v_offset_6542_);
lean_dec(v_offset_6542_);
v___x_6548_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1);
v___x_6549_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6550_ = lean_int_mul(v_second_6543_, v___x_6549_);
lean_dec(v_second_6543_);
v___x_6551_ = lean_int_add(v___x_6550_, v_nano_6544_);
lean_dec(v_nano_6544_);
lean_dec(v___x_6550_);
v___x_6552_ = lean_int_mul(v___x_6547_, v___x_6549_);
lean_dec(v___x_6547_);
v___x_6553_ = lean_int_add(v___x_6552_, v___x_6548_);
lean_dec(v___x_6552_);
v___x_6554_ = lean_int_add(v___x_6551_, v___x_6553_);
lean_dec(v___x_6553_);
lean_dec(v___x_6551_);
v___x_6555_ = l_Std_Time_Duration_ofNanoseconds(v___x_6554_);
lean_dec(v___x_6554_);
v___x_6556_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6556_, 0, v___x_6546_);
lean_ctor_set(v___x_6556_, 1, v___x_6555_);
lean_ctor_set(v___x_6556_, 2, v___x_6538_);
lean_ctor_set(v___x_6556_, 3, v_tz_6541_);
if (v_isShared_6528_ == 0)
{
lean_ctor_set(v___x_6527_, 0, v___x_6556_);
v___x_6558_ = v___x_6527_;
goto v_reusejp_6557_;
}
else
{
lean_object* v_reuseFailAlloc_6559_; 
v_reuseFailAlloc_6559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6559_, 0, v___x_6556_);
v___x_6558_ = v_reuseFailAlloc_6559_;
goto v_reusejp_6557_;
}
v_reusejp_6557_:
{
return v___x_6558_;
}
}
}
}
v___jp_6561_:
{
if (lean_obj_tag(v_aw_6520_) == 0)
{
lean_object* v_a_6564_; 
lean_dec_ref(v___y_6562_);
v_a_6564_ = lean_ctor_get(v_aw_6520_, 0);
lean_inc_ref(v_a_6564_);
lean_dec_ref_known(v_aw_6520_, 1);
v___y_6522_ = v___y_6563_;
v___y_6523_ = v_a_6564_;
goto v___jp_6521_;
}
else
{
v___y_6522_ = v___y_6563_;
v___y_6523_ = v___y_6562_;
goto v___jp_6521_;
}
}
v___jp_6565_:
{
lean_object* v___x_6572_; uint8_t v___x_6573_; 
v___x_6572_ = l_Std_Time_Month_Ordinal_days(v___y_6571_, v___y_6569_);
v___x_6573_ = lean_int_dec_le(v___y_6567_, v___x_6572_);
lean_dec(v___x_6572_);
if (v___x_6573_ == 0)
{
lean_object* v___x_6574_; 
lean_dec(v___y_6570_);
lean_dec(v___y_6569_);
lean_dec(v___y_6567_);
lean_dec_ref(v___y_6566_);
v___x_6574_ = lean_box(0);
v___y_6562_ = v___y_6568_;
v___y_6563_ = v___x_6574_;
goto v___jp_6561_;
}
else
{
lean_object* v_date_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; 
v_date_6575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_date_6575_, 0, v___y_6570_);
lean_ctor_set(v_date_6575_, 1, v___y_6569_);
lean_ctor_set(v_date_6575_, 2, v___y_6567_);
v___x_6576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6576_, 0, v_date_6575_);
lean_ctor_set(v___x_6576_, 1, v___y_6566_);
v___x_6577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6577_, 0, v___x_6576_);
v___y_6562_ = v___y_6568_;
v___y_6563_ = v___x_6577_;
goto v___jp_6561_;
}
}
v___jp_6578_:
{
lean_object* v___x_6586_; lean_object* v___x_6587_; uint8_t v___x_6588_; 
v___x_6586_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_6587_ = lean_int_mod(v___y_6585_, v___x_6586_);
v___x_6588_ = lean_int_dec_eq(v___x_6587_, v___y_6581_);
lean_dec(v___x_6587_);
if (v___x_6588_ == 0)
{
v___y_6566_ = v___y_6580_;
v___y_6567_ = v___y_6579_;
v___y_6568_ = v___y_6582_;
v___y_6569_ = v___y_6584_;
v___y_6570_ = v___y_6585_;
v___y_6571_ = v___y_6583_;
goto v___jp_6565_;
}
else
{
v___y_6566_ = v___y_6580_;
v___y_6567_ = v___y_6579_;
v___y_6568_ = v___y_6582_;
v___y_6569_ = v___y_6584_;
v___y_6570_ = v___y_6585_;
v___y_6571_ = v___x_6588_;
goto v___jp_6565_;
}
}
v___jp_6589_:
{
lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; uint8_t v___x_6599_; 
v___x_6596_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_6597_ = lean_int_mod(v___y_6594_, v___x_6596_);
v___x_6598_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6599_ = lean_int_dec_eq(v___x_6597_, v___x_6598_);
lean_dec(v___x_6597_);
if (v___x_6599_ == 0)
{
v___y_6566_ = v___y_6595_;
v___y_6567_ = v___y_6590_;
v___y_6568_ = v___y_6592_;
v___y_6569_ = v___y_6593_;
v___y_6570_ = v___y_6594_;
v___y_6571_ = v___y_6591_;
goto v___jp_6565_;
}
else
{
lean_object* v___x_6600_; lean_object* v___x_6601_; uint8_t v___x_6602_; 
v___x_6600_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6601_ = lean_int_mod(v___y_6594_, v___x_6600_);
v___x_6602_ = lean_int_dec_eq(v___x_6601_, v___x_6598_);
lean_dec(v___x_6601_);
if (v___x_6602_ == 0)
{
if (v___x_6599_ == 0)
{
v___y_6579_ = v___y_6590_;
v___y_6580_ = v___y_6595_;
v___y_6581_ = v___x_6598_;
v___y_6582_ = v___y_6592_;
v___y_6583_ = v___y_6591_;
v___y_6584_ = v___y_6593_;
v___y_6585_ = v___y_6594_;
goto v___jp_6578_;
}
else
{
v___y_6566_ = v___y_6595_;
v___y_6567_ = v___y_6590_;
v___y_6568_ = v___y_6592_;
v___y_6569_ = v___y_6593_;
v___y_6570_ = v___y_6594_;
v___y_6571_ = v___x_6599_;
goto v___jp_6565_;
}
}
else
{
v___y_6579_ = v___y_6590_;
v___y_6580_ = v___y_6595_;
v___y_6581_ = v___x_6598_;
v___y_6582_ = v___y_6592_;
v___y_6583_ = v___y_6591_;
v___y_6584_ = v___y_6593_;
v___y_6585_ = v___y_6594_;
goto v___jp_6578_;
}
}
}
v___jp_6631_:
{
if (lean_obj_tag(v_N_6622_) == 0)
{
if (lean_obj_tag(v_A_6620_) == 0)
{
lean_object* v___x_6641_; 
v___x_6641_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6641_, 0, v___y_6633_);
lean_ctor_set(v___x_6641_, 1, v___y_6639_);
lean_ctor_set(v___x_6641_, 2, v___y_6637_);
lean_ctor_set(v___x_6641_, 3, v___y_6640_);
v___y_6590_ = v___y_6632_;
v___y_6591_ = v___y_6635_;
v___y_6592_ = v___y_6634_;
v___y_6593_ = v___y_6636_;
v___y_6594_ = v___y_6638_;
v___y_6595_ = v___x_6641_;
goto v___jp_6589_;
}
else
{
lean_object* v_val_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; 
lean_dec(v___y_6640_);
lean_dec(v___y_6639_);
lean_dec(v___y_6637_);
lean_dec(v___y_6633_);
v_val_6642_ = lean_ctor_get(v_A_6620_, 0);
lean_inc(v_val_6642_);
lean_dec_ref_known(v_A_6620_, 1);
v___x_6643_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2);
v___x_6644_ = lean_int_mul(v_val_6642_, v___x_6643_);
lean_dec(v_val_6642_);
v___x_6645_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_6644_);
lean_dec(v___x_6644_);
v___y_6590_ = v___y_6632_;
v___y_6591_ = v___y_6635_;
v___y_6592_ = v___y_6634_;
v___y_6593_ = v___y_6636_;
v___y_6594_ = v___y_6638_;
v___y_6595_ = v___x_6645_;
goto v___jp_6589_;
}
}
else
{
lean_object* v_val_6646_; lean_object* v___x_6647_; 
lean_dec(v___y_6640_);
lean_dec(v___y_6639_);
lean_dec(v___y_6637_);
lean_dec(v___y_6633_);
lean_dec(v_A_6620_);
v_val_6646_ = lean_ctor_get(v_N_6622_, 0);
lean_inc(v_val_6646_);
lean_dec_ref_known(v_N_6622_, 1);
v___x_6647_ = l_Std_Time_PlainTime_ofNanoseconds(v_val_6646_);
lean_dec(v_val_6646_);
v___y_6590_ = v___y_6632_;
v___y_6591_ = v___y_6635_;
v___y_6592_ = v___y_6634_;
v___y_6593_ = v___y_6636_;
v___y_6594_ = v___y_6638_;
v___y_6595_ = v___x_6647_;
goto v___jp_6589_;
}
}
v___jp_6648_:
{
if (lean_obj_tag(v_n_6621_) == 0)
{
if (lean_obj_tag(v_S_6619_) == 0)
{
lean_object* v___x_6657_; 
v___x_6657_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4);
v___y_6632_ = v___y_6649_;
v___y_6633_ = v___y_6650_;
v___y_6634_ = v___y_6652_;
v___y_6635_ = v___y_6651_;
v___y_6636_ = v___y_6653_;
v___y_6637_ = v___y_6656_;
v___y_6638_ = v___y_6654_;
v___y_6639_ = v___y_6655_;
v___y_6640_ = v___x_6657_;
goto v___jp_6631_;
}
else
{
lean_object* v_val_6658_; 
v_val_6658_ = lean_ctor_get(v_S_6619_, 0);
lean_inc(v_val_6658_);
lean_dec_ref_known(v_S_6619_, 1);
v___y_6632_ = v___y_6649_;
v___y_6633_ = v___y_6650_;
v___y_6634_ = v___y_6652_;
v___y_6635_ = v___y_6651_;
v___y_6636_ = v___y_6653_;
v___y_6637_ = v___y_6656_;
v___y_6638_ = v___y_6654_;
v___y_6639_ = v___y_6655_;
v___y_6640_ = v_val_6658_;
goto v___jp_6631_;
}
}
else
{
lean_object* v_val_6659_; 
lean_dec(v_S_6619_);
v_val_6659_ = lean_ctor_get(v_n_6621_, 0);
lean_inc(v_val_6659_);
lean_dec_ref_known(v_n_6621_, 1);
v___y_6632_ = v___y_6649_;
v___y_6633_ = v___y_6650_;
v___y_6634_ = v___y_6652_;
v___y_6635_ = v___y_6651_;
v___y_6636_ = v___y_6653_;
v___y_6637_ = v___y_6656_;
v___y_6638_ = v___y_6654_;
v___y_6639_ = v___y_6655_;
v___y_6640_ = v_val_6659_;
goto v___jp_6631_;
}
}
v___jp_6660_:
{
if (lean_obj_tag(v_s_6618_) == 0)
{
lean_object* v___x_6668_; 
v___x_6668_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v___y_6649_ = v___y_6661_;
v___y_6650_ = v___y_6662_;
v___y_6651_ = v___y_6664_;
v___y_6652_ = v___y_6663_;
v___y_6653_ = v___y_6665_;
v___y_6654_ = v___y_6666_;
v___y_6655_ = v___y_6667_;
v___y_6656_ = v___x_6668_;
goto v___jp_6648_;
}
else
{
lean_object* v_val_6669_; 
v_val_6669_ = lean_ctor_get(v_s_6618_, 0);
lean_inc(v_val_6669_);
lean_dec_ref_known(v_s_6618_, 1);
v___y_6649_ = v___y_6661_;
v___y_6650_ = v___y_6662_;
v___y_6651_ = v___y_6664_;
v___y_6652_ = v___y_6663_;
v___y_6653_ = v___y_6665_;
v___y_6654_ = v___y_6666_;
v___y_6655_ = v___y_6667_;
v___y_6656_ = v_val_6669_;
goto v___jp_6648_;
}
}
v___jp_6670_:
{
if (lean_obj_tag(v_m_6617_) == 0)
{
lean_object* v___x_6677_; 
v___x_6677_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13);
v___y_6661_ = v___y_6671_;
v___y_6662_ = v___y_6676_;
v___y_6663_ = v___y_6673_;
v___y_6664_ = v___y_6672_;
v___y_6665_ = v___y_6674_;
v___y_6666_ = v___y_6675_;
v___y_6667_ = v___x_6677_;
goto v___jp_6660_;
}
else
{
lean_object* v_val_6678_; 
v_val_6678_ = lean_ctor_get(v_m_6617_, 0);
lean_inc(v_val_6678_);
lean_dec_ref_known(v_m_6617_, 1);
v___y_6661_ = v___y_6671_;
v___y_6662_ = v___y_6676_;
v___y_6663_ = v___y_6673_;
v___y_6664_ = v___y_6672_;
v___y_6665_ = v___y_6674_;
v___y_6666_ = v___y_6675_;
v___y_6667_ = v_val_6678_;
goto v___jp_6660_;
}
}
v___jp_6679_:
{
if (lean_obj_tag(v_k_6615_) == 0)
{
if (lean_obj_tag(v_H_6616_) == 0)
{
lean_object* v___x_6685_; 
v___x_6685_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6671_ = v___y_6680_;
v___y_6672_ = v___y_6682_;
v___y_6673_ = v___y_6681_;
v___y_6674_ = v___y_6683_;
v___y_6675_ = v___y_6684_;
v___y_6676_ = v___x_6685_;
goto v___jp_6670_;
}
else
{
lean_object* v_val_6686_; 
v_val_6686_ = lean_ctor_get(v_H_6616_, 0);
lean_inc(v_val_6686_);
lean_dec_ref_known(v_H_6616_, 1);
v___y_6671_ = v___y_6680_;
v___y_6672_ = v___y_6682_;
v___y_6673_ = v___y_6681_;
v___y_6674_ = v___y_6683_;
v___y_6675_ = v___y_6684_;
v___y_6676_ = v_val_6686_;
goto v___jp_6670_;
}
}
else
{
if (lean_obj_tag(v_H_6616_) == 0)
{
lean_object* v_val_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; 
v_val_6687_ = lean_ctor_get(v_k_6615_, 0);
lean_inc(v_val_6687_);
lean_dec_ref_known(v_k_6615_, 1);
v___x_6688_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_6689_ = lean_int_add(v_val_6687_, v___x_6688_);
lean_dec(v_val_6687_);
v___y_6671_ = v___y_6680_;
v___y_6672_ = v___y_6682_;
v___y_6673_ = v___y_6681_;
v___y_6674_ = v___y_6683_;
v___y_6675_ = v___y_6684_;
v___y_6676_ = v___x_6689_;
goto v___jp_6670_;
}
else
{
lean_object* v_val_6690_; 
lean_dec_ref_known(v_k_6615_, 1);
v_val_6690_ = lean_ctor_get(v_H_6616_, 0);
lean_inc(v_val_6690_);
lean_dec_ref_known(v_H_6616_, 1);
v___y_6671_ = v___y_6680_;
v___y_6672_ = v___y_6682_;
v___y_6673_ = v___y_6681_;
v___y_6674_ = v___y_6683_;
v___y_6675_ = v___y_6684_;
v___y_6676_ = v_val_6690_;
goto v___jp_6670_;
}
}
}
v___jp_6691_:
{
if (lean_obj_tag(v_h_6613_) == 0)
{
if (lean_obj_tag(v_K_6614_) == 0)
{
v___y_6680_ = v___y_6692_;
v___y_6681_ = v___y_6694_;
v___y_6682_ = v___y_6693_;
v___y_6683_ = v___y_6695_;
v___y_6684_ = v___y_6696_;
goto v___jp_6679_;
}
else
{
lean_object* v_val_6698_; lean_object* v___x_6699_; lean_object* v___x_6700_; lean_object* v___x_6701_; 
lean_dec(v_H_6616_);
lean_dec(v_k_6615_);
v_val_6698_ = lean_ctor_get(v_K_6614_, 0);
lean_inc(v_val_6698_);
lean_dec_ref_known(v_K_6614_, 1);
v___x_6699_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6700_ = lean_int_add(v_val_6698_, v___x_6699_);
lean_dec(v_val_6698_);
v___x_6701_ = l_Std_Time_HourMarker_toAbsolute(v_val_6697_, v___x_6700_);
lean_dec(v___x_6700_);
v___y_6671_ = v___y_6692_;
v___y_6672_ = v___y_6693_;
v___y_6673_ = v___y_6694_;
v___y_6674_ = v___y_6695_;
v___y_6675_ = v___y_6696_;
v___y_6676_ = v___x_6701_;
goto v___jp_6670_;
}
}
else
{
lean_object* v_val_6702_; lean_object* v___x_6703_; 
lean_dec(v_H_6616_);
lean_dec(v_k_6615_);
lean_dec(v_K_6614_);
v_val_6702_ = lean_ctor_get(v_h_6613_, 0);
lean_inc(v_val_6702_);
lean_dec_ref_known(v_h_6613_, 1);
v___x_6703_ = l_Std_Time_HourMarker_toAbsolute(v_val_6697_, v_val_6702_);
lean_dec(v_val_6702_);
v___y_6671_ = v___y_6692_;
v___y_6672_ = v___y_6693_;
v___y_6673_ = v___y_6694_;
v___y_6674_ = v___y_6695_;
v___y_6675_ = v___y_6696_;
v___y_6676_ = v___x_6703_;
goto v___jp_6670_;
}
}
v___jp_6704_:
{
if (lean_obj_tag(v_a_6610_) == 0)
{
if (lean_obj_tag(v_b_6611_) == 0)
{
if (lean_obj_tag(v_B_6612_) == 0)
{
lean_dec(v_K_6614_);
lean_dec(v_h_6613_);
v___y_6680_ = v___y_6705_;
v___y_6681_ = v___y_6706_;
v___y_6682_ = v___y_6707_;
v___y_6683_ = v___y_6708_;
v___y_6684_ = v___y_6709_;
goto v___jp_6679_;
}
else
{
lean_object* v_val_6710_; uint8_t v___x_6711_; uint8_t v___x_6712_; 
v_val_6710_ = lean_ctor_get(v_B_6612_, 0);
lean_inc(v_val_6710_);
lean_dec_ref_known(v_B_6612_, 1);
v___x_6711_ = lean_unbox(v_val_6710_);
lean_dec(v_val_6710_);
v___x_6712_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v___x_6711_);
v___y_6692_ = v___y_6705_;
v___y_6693_ = v___y_6707_;
v___y_6694_ = v___y_6706_;
v___y_6695_ = v___y_6708_;
v___y_6696_ = v___y_6709_;
v_val_6697_ = v___x_6712_;
goto v___jp_6691_;
}
}
else
{
lean_object* v_val_6713_; uint8_t v___x_6714_; uint8_t v___x_6715_; 
lean_dec(v_B_6612_);
v_val_6713_ = lean_ctor_get(v_b_6611_, 0);
lean_inc(v_val_6713_);
lean_dec_ref_known(v_b_6611_, 1);
v___x_6714_ = lean_unbox(v_val_6713_);
lean_dec(v_val_6713_);
v___x_6715_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v___x_6714_);
v___y_6692_ = v___y_6705_;
v___y_6693_ = v___y_6707_;
v___y_6694_ = v___y_6706_;
v___y_6695_ = v___y_6708_;
v___y_6696_ = v___y_6709_;
v_val_6697_ = v___x_6715_;
goto v___jp_6691_;
}
}
else
{
lean_object* v_val_6716_; uint8_t v___x_6717_; 
lean_dec(v_B_6612_);
lean_dec(v_b_6611_);
v_val_6716_ = lean_ctor_get(v_a_6610_, 0);
lean_inc(v_val_6716_);
lean_dec_ref_known(v_a_6610_, 1);
v___x_6717_ = lean_unbox(v_val_6716_);
lean_dec(v_val_6716_);
v___y_6692_ = v___y_6705_;
v___y_6693_ = v___y_6707_;
v___y_6694_ = v___y_6706_;
v___y_6695_ = v___y_6708_;
v___y_6696_ = v___y_6709_;
v_val_6697_ = v___x_6717_;
goto v___jp_6691_;
}
}
v___jp_6718_:
{
if (lean_obj_tag(v_u_6605_) == 0)
{
if (lean_obj_tag(v_y_6604_) == 0)
{
if (lean_obj_tag(v_Y_6606_) == 0)
{
lean_object* v___x_6724_; 
v___x_6724_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6705_ = v___y_6719_;
v___y_6706_ = v___y_6721_;
v___y_6707_ = v___y_6720_;
v___y_6708_ = v___y_6722_;
v___y_6709_ = v___x_6724_;
goto v___jp_6704_;
}
else
{
lean_object* v_val_6725_; 
v_val_6725_ = lean_ctor_get(v_Y_6606_, 0);
lean_inc(v_val_6725_);
lean_dec_ref_known(v_Y_6606_, 1);
v___y_6705_ = v___y_6719_;
v___y_6706_ = v___y_6721_;
v___y_6707_ = v___y_6720_;
v___y_6708_ = v___y_6722_;
v___y_6709_ = v_val_6725_;
goto v___jp_6704_;
}
}
else
{
lean_object* v_val_6726_; lean_object* v___x_6727_; 
lean_dec(v_Y_6606_);
v_val_6726_ = lean_ctor_get(v_y_6604_, 0);
lean_inc(v_val_6726_);
lean_dec_ref_known(v_y_6604_, 1);
v___x_6727_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6726_, v___y_6723_);
lean_dec(v_val_6726_);
v___y_6705_ = v___y_6719_;
v___y_6706_ = v___y_6721_;
v___y_6707_ = v___y_6720_;
v___y_6708_ = v___y_6722_;
v___y_6709_ = v___x_6727_;
goto v___jp_6704_;
}
}
else
{
lean_object* v_val_6728_; 
lean_dec(v_Y_6606_);
lean_dec(v_y_6604_);
v_val_6728_ = lean_ctor_get(v_u_6605_, 0);
lean_inc(v_val_6728_);
lean_dec_ref_known(v_u_6605_, 1);
v___y_6705_ = v___y_6719_;
v___y_6706_ = v___y_6721_;
v___y_6707_ = v___y_6720_;
v___y_6708_ = v___y_6722_;
v___y_6709_ = v_val_6728_;
goto v___jp_6704_;
}
}
v___jp_6729_:
{
if (lean_obj_tag(v_G_6603_) == 0)
{
uint8_t v___x_6734_; 
v___x_6734_ = 1;
v___y_6719_ = v___y_6733_;
v___y_6720_ = v___y_6730_;
v___y_6721_ = v___y_6731_;
v___y_6722_ = v___y_6732_;
v___y_6723_ = v___x_6734_;
goto v___jp_6718_;
}
else
{
lean_object* v_val_6735_; uint8_t v___x_6736_; 
v_val_6735_ = lean_ctor_get(v_G_6603_, 0);
lean_inc(v_val_6735_);
lean_dec_ref_known(v_G_6603_, 1);
v___x_6736_ = lean_unbox(v_val_6735_);
lean_dec(v_val_6735_);
v___y_6719_ = v___y_6733_;
v___y_6720_ = v___y_6730_;
v___y_6721_ = v___y_6731_;
v___y_6722_ = v___y_6732_;
v___y_6723_ = v___x_6736_;
goto v___jp_6718_;
}
}
v___jp_6737_:
{
if (lean_obj_tag(v_d_6609_) == 0)
{
lean_object* v___x_6741_; 
v___x_6741_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22);
v___y_6730_ = v___y_6739_;
v___y_6731_ = v___y_6738_;
v___y_6732_ = v___y_6740_;
v___y_6733_ = v___x_6741_;
goto v___jp_6729_;
}
else
{
lean_object* v_val_6742_; 
v_val_6742_ = lean_ctor_get(v_d_6609_, 0);
lean_inc(v_val_6742_);
lean_dec_ref_known(v_d_6609_, 1);
v___y_6730_ = v___y_6739_;
v___y_6731_ = v___y_6738_;
v___y_6732_ = v___y_6740_;
v___y_6733_ = v_val_6742_;
goto v___jp_6729_;
}
}
v___jp_6743_:
{
uint8_t v___x_6747_; lean_object* v_tz_6748_; 
v___x_6747_ = 0;
v_tz_6748_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tz_6748_, 0, v___y_6744_);
lean_ctor_set(v_tz_6748_, 1, v___y_6745_);
lean_ctor_set(v_tz_6748_, 2, v___y_6746_);
lean_ctor_set_uint8(v_tz_6748_, sizeof(void*)*3, v___x_6747_);
if (lean_obj_tag(v_M_6607_) == 0)
{
if (lean_obj_tag(v_L_6608_) == 0)
{
lean_object* v___x_6749_; 
v___x_6749_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30);
v___y_6738_ = v_tz_6748_;
v___y_6739_ = v___x_6747_;
v___y_6740_ = v___x_6749_;
goto v___jp_6737_;
}
else
{
lean_object* v_val_6750_; 
v_val_6750_ = lean_ctor_get(v_L_6608_, 0);
lean_inc(v_val_6750_);
lean_dec_ref_known(v_L_6608_, 1);
v___y_6738_ = v_tz_6748_;
v___y_6739_ = v___x_6747_;
v___y_6740_ = v_val_6750_;
goto v___jp_6737_;
}
}
else
{
lean_object* v_val_6751_; 
lean_dec(v_L_6608_);
v_val_6751_ = lean_ctor_get(v_M_6607_, 0);
lean_inc(v_val_6751_);
lean_dec_ref_known(v_M_6607_, 1);
v___y_6738_ = v_tz_6748_;
v___y_6739_ = v___x_6747_;
v___y_6740_ = v_val_6751_;
goto v___jp_6737_;
}
}
v___jp_6752_:
{
if (lean_obj_tag(v_zabbrev_6625_) == 0)
{
lean_object* v___x_6756_; lean_object* v___x_6757_; 
v___x_6756_ = lean_box(0);
v___x_6757_ = lean_apply_1(v___y_6753_, v___x_6756_);
v___y_6744_ = v___y_6754_;
v___y_6745_ = v___y_6755_;
v___y_6746_ = v___x_6757_;
goto v___jp_6743_;
}
else
{
lean_object* v_val_6758_; 
lean_dec_ref(v___y_6753_);
v_val_6758_ = lean_ctor_get(v_zabbrev_6625_, 0);
lean_inc(v_val_6758_);
lean_dec_ref_known(v_zabbrev_6625_, 1);
v___y_6744_ = v___y_6754_;
v___y_6745_ = v___y_6755_;
v___y_6746_ = v_val_6758_;
goto v___jp_6743_;
}
}
v___jp_6759_:
{
lean_object* v___f_6761_; 
lean_inc(v___y_6760_);
v___f_6761_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1), 2, 1);
lean_closure_set(v___f_6761_, 0, v___y_6760_);
if (lean_obj_tag(v_V_6623_) == 0)
{
if (lean_obj_tag(v_v_6626_) == 0)
{
if (lean_obj_tag(v_z_6624_) == 0)
{
lean_object* v___x_6762_; lean_object* v___x_6763_; 
v___x_6762_ = lean_box(0);
lean_inc(v___y_6760_);
v___x_6763_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(v___y_6760_, v___x_6762_);
v___y_6753_ = v___f_6761_;
v___y_6754_ = v___y_6760_;
v___y_6755_ = v___x_6763_;
goto v___jp_6752_;
}
else
{
lean_object* v_val_6764_; 
v_val_6764_ = lean_ctor_get(v_z_6624_, 0);
lean_inc(v_val_6764_);
lean_dec_ref_known(v_z_6624_, 1);
v___y_6753_ = v___f_6761_;
v___y_6754_ = v___y_6760_;
v___y_6755_ = v_val_6764_;
goto v___jp_6752_;
}
}
else
{
lean_object* v_val_6765_; 
lean_dec(v_z_6624_);
v_val_6765_ = lean_ctor_get(v_v_6626_, 0);
lean_inc(v_val_6765_);
lean_dec_ref_known(v_v_6626_, 1);
v___y_6753_ = v___f_6761_;
v___y_6754_ = v___y_6760_;
v___y_6755_ = v_val_6765_;
goto v___jp_6752_;
}
}
else
{
lean_object* v_val_6766_; 
lean_dec(v_v_6626_);
lean_dec(v_z_6624_);
v_val_6766_ = lean_ctor_get(v_V_6623_, 0);
lean_inc(v_val_6766_);
lean_dec_ref_known(v_V_6623_, 1);
v___y_6753_ = v___f_6761_;
v___y_6754_ = v___y_6760_;
v___y_6755_ = v_val_6766_;
goto v___jp_6752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object* v_date_6772_, lean_object* v_config_6773_, lean_object* v_mod_6774_, lean_object* v_a_6775_){
_start:
{
if (lean_obj_tag(v_mod_6774_) == 0)
{
lean_object* v_val_6776_; lean_object* v___x_6777_; 
lean_dec_ref(v_config_6773_);
v_val_6776_ = lean_ctor_get(v_mod_6774_, 0);
lean_inc_ref(v_val_6776_);
lean_dec_ref_known(v_mod_6774_, 1);
v___x_6777_ = l_Std_Internal_Parsec_String_pstring(v_val_6776_, v_a_6775_);
if (lean_obj_tag(v___x_6777_) == 0)
{
lean_object* v_pos_6778_; lean_object* v___x_6780_; uint8_t v_isShared_6781_; uint8_t v_isSharedCheck_6785_; 
v_pos_6778_ = lean_ctor_get(v___x_6777_, 0);
v_isSharedCheck_6785_ = !lean_is_exclusive(v___x_6777_);
if (v_isSharedCheck_6785_ == 0)
{
lean_object* v_unused_6786_; 
v_unused_6786_ = lean_ctor_get(v___x_6777_, 1);
lean_dec(v_unused_6786_);
v___x_6780_ = v___x_6777_;
v_isShared_6781_ = v_isSharedCheck_6785_;
goto v_resetjp_6779_;
}
else
{
lean_inc(v_pos_6778_);
lean_dec(v___x_6777_);
v___x_6780_ = lean_box(0);
v_isShared_6781_ = v_isSharedCheck_6785_;
goto v_resetjp_6779_;
}
v_resetjp_6779_:
{
lean_object* v___x_6783_; 
if (v_isShared_6781_ == 0)
{
lean_ctor_set(v___x_6780_, 1, v_date_6772_);
v___x_6783_ = v___x_6780_;
goto v_reusejp_6782_;
}
else
{
lean_object* v_reuseFailAlloc_6784_; 
v_reuseFailAlloc_6784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6784_, 0, v_pos_6778_);
lean_ctor_set(v_reuseFailAlloc_6784_, 1, v_date_6772_);
v___x_6783_ = v_reuseFailAlloc_6784_;
goto v_reusejp_6782_;
}
v_reusejp_6782_:
{
return v___x_6783_;
}
}
}
else
{
lean_object* v_pos_6787_; lean_object* v_err_6788_; lean_object* v___x_6790_; uint8_t v_isShared_6791_; uint8_t v_isSharedCheck_6795_; 
lean_dec_ref(v_date_6772_);
v_pos_6787_ = lean_ctor_get(v___x_6777_, 0);
v_err_6788_ = lean_ctor_get(v___x_6777_, 1);
v_isSharedCheck_6795_ = !lean_is_exclusive(v___x_6777_);
if (v_isSharedCheck_6795_ == 0)
{
v___x_6790_ = v___x_6777_;
v_isShared_6791_ = v_isSharedCheck_6795_;
goto v_resetjp_6789_;
}
else
{
lean_inc(v_err_6788_);
lean_inc(v_pos_6787_);
lean_dec(v___x_6777_);
v___x_6790_ = lean_box(0);
v_isShared_6791_ = v_isSharedCheck_6795_;
goto v_resetjp_6789_;
}
v_resetjp_6789_:
{
lean_object* v___x_6793_; 
if (v_isShared_6791_ == 0)
{
v___x_6793_ = v___x_6790_;
goto v_reusejp_6792_;
}
else
{
lean_object* v_reuseFailAlloc_6794_; 
v_reuseFailAlloc_6794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6794_, 0, v_pos_6787_);
lean_ctor_set(v_reuseFailAlloc_6794_, 1, v_err_6788_);
v___x_6793_ = v_reuseFailAlloc_6794_;
goto v_reusejp_6792_;
}
v_reusejp_6792_:
{
return v___x_6793_;
}
}
}
}
else
{
lean_object* v_modifier_6796_; lean_object* v___x_6797_; 
v_modifier_6796_ = lean_ctor_get(v_mod_6774_, 0);
lean_inc_ref_n(v_modifier_6796_, 2);
lean_dec_ref_known(v_mod_6774_, 1);
v___x_6797_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6773_, v_modifier_6796_, v_a_6775_);
if (lean_obj_tag(v___x_6797_) == 0)
{
lean_object* v_pos_6798_; lean_object* v_res_6799_; lean_object* v___x_6801_; uint8_t v_isShared_6802_; uint8_t v_isSharedCheck_6807_; 
v_pos_6798_ = lean_ctor_get(v___x_6797_, 0);
v_res_6799_ = lean_ctor_get(v___x_6797_, 1);
v_isSharedCheck_6807_ = !lean_is_exclusive(v___x_6797_);
if (v_isSharedCheck_6807_ == 0)
{
v___x_6801_ = v___x_6797_;
v_isShared_6802_ = v_isSharedCheck_6807_;
goto v_resetjp_6800_;
}
else
{
lean_inc(v_res_6799_);
lean_inc(v_pos_6798_);
lean_dec(v___x_6797_);
v___x_6801_ = lean_box(0);
v_isShared_6802_ = v_isSharedCheck_6807_;
goto v_resetjp_6800_;
}
v_resetjp_6800_:
{
lean_object* v___x_6803_; lean_object* v___x_6805_; 
v___x_6803_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(v_date_6772_, v_modifier_6796_, v_res_6799_);
if (v_isShared_6802_ == 0)
{
lean_ctor_set(v___x_6801_, 1, v___x_6803_);
v___x_6805_ = v___x_6801_;
goto v_reusejp_6804_;
}
else
{
lean_object* v_reuseFailAlloc_6806_; 
v_reuseFailAlloc_6806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6806_, 0, v_pos_6798_);
lean_ctor_set(v_reuseFailAlloc_6806_, 1, v___x_6803_);
v___x_6805_ = v_reuseFailAlloc_6806_;
goto v_reusejp_6804_;
}
v_reusejp_6804_:
{
return v___x_6805_;
}
}
}
else
{
lean_object* v_pos_6808_; lean_object* v_err_6809_; lean_object* v___x_6811_; uint8_t v_isShared_6812_; uint8_t v_isSharedCheck_6816_; 
lean_dec_ref(v_modifier_6796_);
lean_dec_ref(v_date_6772_);
v_pos_6808_ = lean_ctor_get(v___x_6797_, 0);
v_err_6809_ = lean_ctor_get(v___x_6797_, 1);
v_isSharedCheck_6816_ = !lean_is_exclusive(v___x_6797_);
if (v_isSharedCheck_6816_ == 0)
{
v___x_6811_ = v___x_6797_;
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
else
{
lean_inc(v_err_6809_);
lean_inc(v_pos_6808_);
lean_dec(v___x_6797_);
v___x_6811_ = lean_box(0);
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
v_resetjp_6810_:
{
lean_object* v___x_6814_; 
if (v_isShared_6812_ == 0)
{
v___x_6814_ = v___x_6811_;
goto v_reusejp_6813_;
}
else
{
lean_object* v_reuseFailAlloc_6815_; 
v_reuseFailAlloc_6815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6815_, 0, v_pos_6808_);
lean_ctor_set(v_reuseFailAlloc_6815_, 1, v_err_6809_);
v___x_6814_ = v_reuseFailAlloc_6815_;
goto v_reusejp_6813_;
}
v_reusejp_6813_:
{
return v___x_6814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object* v_input_6817_, lean_object* v_config_6818_){
_start:
{
lean_object* v___x_6819_; lean_object* v___x_6820_; 
v___x_6819_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6820_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6819_, v_input_6817_);
if (lean_obj_tag(v___x_6820_) == 0)
{
lean_object* v_a_6821_; lean_object* v___x_6823_; uint8_t v_isShared_6824_; uint8_t v_isSharedCheck_6828_; 
lean_dec_ref(v_config_6818_);
v_a_6821_ = lean_ctor_get(v___x_6820_, 0);
v_isSharedCheck_6828_ = !lean_is_exclusive(v___x_6820_);
if (v_isSharedCheck_6828_ == 0)
{
v___x_6823_ = v___x_6820_;
v_isShared_6824_ = v_isSharedCheck_6828_;
goto v_resetjp_6822_;
}
else
{
lean_inc(v_a_6821_);
lean_dec(v___x_6820_);
v___x_6823_ = lean_box(0);
v_isShared_6824_ = v_isSharedCheck_6828_;
goto v_resetjp_6822_;
}
v_resetjp_6822_:
{
lean_object* v___x_6826_; 
if (v_isShared_6824_ == 0)
{
v___x_6826_ = v___x_6823_;
goto v_reusejp_6825_;
}
else
{
lean_object* v_reuseFailAlloc_6827_; 
v_reuseFailAlloc_6827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6827_, 0, v_a_6821_);
v___x_6826_ = v_reuseFailAlloc_6827_;
goto v_reusejp_6825_;
}
v_reusejp_6825_:
{
return v___x_6826_;
}
}
}
else
{
lean_object* v_a_6829_; lean_object* v___x_6831_; uint8_t v_isShared_6832_; uint8_t v_isSharedCheck_6837_; 
v_a_6829_ = lean_ctor_get(v___x_6820_, 0);
v_isSharedCheck_6837_ = !lean_is_exclusive(v___x_6820_);
if (v_isSharedCheck_6837_ == 0)
{
v___x_6831_ = v___x_6820_;
v_isShared_6832_ = v_isSharedCheck_6837_;
goto v_resetjp_6830_;
}
else
{
lean_inc(v_a_6829_);
lean_dec(v___x_6820_);
v___x_6831_ = lean_box(0);
v_isShared_6832_ = v_isSharedCheck_6837_;
goto v_resetjp_6830_;
}
v_resetjp_6830_:
{
lean_object* v___x_6833_; lean_object* v___x_6835_; 
v___x_6833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6833_, 0, v_config_6818_);
lean_ctor_set(v___x_6833_, 1, v_a_6829_);
if (v_isShared_6832_ == 0)
{
lean_ctor_set(v___x_6831_, 0, v___x_6833_);
v___x_6835_ = v___x_6831_;
goto v_reusejp_6834_;
}
else
{
lean_object* v_reuseFailAlloc_6836_; 
v_reuseFailAlloc_6836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6836_, 0, v___x_6833_);
v___x_6835_ = v_reuseFailAlloc_6836_;
goto v_reusejp_6834_;
}
v_reusejp_6834_:
{
return v___x_6835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object* v_tz_6838_, lean_object* v_input_6839_, lean_object* v_config_6840_){
_start:
{
lean_object* v___x_6841_; 
v___x_6841_ = l_Std_Time_GenericFormat_spec___redArg(v_input_6839_, v_config_6840_);
return v___x_6841_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object* v_tz_6842_, lean_object* v_input_6843_, lean_object* v_config_6844_){
_start:
{
lean_object* v_res_6845_; 
v_res_6845_ = l_Std_Time_GenericFormat_spec(v_tz_6842_, v_input_6843_, v_config_6844_);
lean_dec(v_tz_6842_);
return v_res_6845_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object* v_tz_6846_, lean_object* v_msg_6847_){
_start:
{
lean_object* v___x_6848_; lean_object* v___x_6849_; 
v___x_6848_ = l_Std_Time_instInhabitedGenericFormat_default(v_tz_6846_);
v___x_6849_ = lean_panic_fn_borrowed(v___x_6848_, v_msg_6847_);
lean_dec_ref(v___x_6848_);
return v___x_6849_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object* v_tz_6850_, lean_object* v_msg_6851_){
_start:
{
lean_object* v_res_6852_; 
v_res_6852_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6850_, v_msg_6851_);
lean_dec(v_tz_6850_);
return v_res_6852_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object* v_tz_6855_, lean_object* v_input_6856_, lean_object* v_config_6857_){
_start:
{
lean_object* v___x_6858_; lean_object* v___x_6859_; 
v___x_6858_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6859_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6858_, v_input_6856_);
if (lean_obj_tag(v___x_6859_) == 0)
{
lean_object* v_a_6860_; lean_object* v___x_6861_; lean_object* v___x_6862_; lean_object* v___x_6863_; lean_object* v___x_6864_; lean_object* v___x_6865_; lean_object* v___x_6866_; 
lean_dec_ref(v_config_6857_);
v_a_6860_ = lean_ctor_get(v___x_6859_, 0);
lean_inc(v_a_6860_);
lean_dec_ref_known(v___x_6859_, 1);
v___x_6861_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6862_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__1));
v___x_6863_ = lean_unsigned_to_nat(1071u);
v___x_6864_ = lean_unsigned_to_nat(18u);
v___x_6865_ = l_mkPanicMessageWithDecl(v___x_6861_, v___x_6862_, v___x_6863_, v___x_6864_, v_a_6860_);
lean_dec(v_a_6860_);
v___x_6866_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6855_, v___x_6865_);
return v___x_6866_;
}
else
{
lean_object* v_a_6867_; lean_object* v___x_6868_; 
v_a_6867_ = lean_ctor_get(v___x_6859_, 0);
lean_inc(v_a_6867_);
lean_dec_ref_known(v___x_6859_, 1);
v___x_6868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6868_, 0, v_config_6857_);
lean_ctor_set(v___x_6868_, 1, v_a_6867_);
return v___x_6868_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object* v_tz_6869_, lean_object* v_input_6870_, lean_object* v_config_6871_){
_start:
{
lean_object* v_res_6872_; 
v_res_6872_ = l_Std_Time_GenericFormat_spec_x21(v_tz_6869_, v_input_6870_, v_config_6871_);
lean_dec(v_tz_6869_);
return v_res_6872_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(lean_object* v_x_6873_, lean_object* v_x_6874_){
_start:
{
if (lean_obj_tag(v_x_6874_) == 0)
{
return v_x_6873_;
}
else
{
lean_object* v_head_6875_; lean_object* v_tail_6876_; lean_object* v___x_6877_; 
v_head_6875_ = lean_ctor_get(v_x_6874_, 0);
v_tail_6876_ = lean_ctor_get(v_x_6874_, 1);
v___x_6877_ = lean_string_append(v_x_6873_, v_head_6875_);
v_x_6873_ = v___x_6877_;
v_x_6874_ = v_tail_6876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1___boxed(lean_object* v_x_6879_, lean_object* v_x_6880_){
_start:
{
lean_object* v_res_6881_; 
v_res_6881_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v_x_6879_, v_x_6880_);
lean_dec(v_x_6880_);
return v_res_6881_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(lean_object* v_tz_6882_, lean_object* v_timestamp_6883_, lean_object* v___x_6884_, lean_object* v_x_6885_){
_start:
{
lean_object* v_offset_6886_; lean_object* v_second_6887_; lean_object* v_nano_6888_; lean_object* v___x_6889_; lean_object* v___x_6890_; lean_object* v___x_6891_; lean_object* v___x_6892_; lean_object* v___x_6893_; lean_object* v___x_6894_; lean_object* v___x_6895_; lean_object* v___x_6896_; lean_object* v___x_6897_; 
v_offset_6886_ = lean_ctor_get(v_tz_6882_, 0);
v_second_6887_ = lean_ctor_get(v_timestamp_6883_, 0);
v_nano_6888_ = lean_ctor_get(v_timestamp_6883_, 1);
v___x_6889_ = lean_nat_to_int(v___x_6884_);
v___x_6890_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6891_ = lean_int_mul(v_second_6887_, v___x_6890_);
v___x_6892_ = lean_int_add(v___x_6891_, v_nano_6888_);
lean_dec(v___x_6891_);
v___x_6893_ = lean_int_mul(v_offset_6886_, v___x_6890_);
v___x_6894_ = lean_int_add(v___x_6893_, v___x_6889_);
lean_dec(v___x_6889_);
lean_dec(v___x_6893_);
v___x_6895_ = lean_int_add(v___x_6892_, v___x_6894_);
lean_dec(v___x_6894_);
lean_dec(v___x_6892_);
v___x_6896_ = l_Std_Time_Duration_ofNanoseconds(v___x_6895_);
lean_dec(v___x_6895_);
v___x_6897_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_6896_);
return v___x_6897_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed(lean_object* v_tz_6898_, lean_object* v_timestamp_6899_, lean_object* v___x_6900_, lean_object* v_x_6901_){
_start:
{
lean_object* v_res_6902_; 
v_res_6902_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(v_tz_6898_, v_timestamp_6899_, v___x_6900_, v_x_6901_);
lean_dec_ref(v_timestamp_6899_);
lean_dec_ref(v_tz_6898_);
return v_res_6902_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(lean_object* v_aw_6903_, lean_object* v_date_6904_, lean_object* v_dateformat_6905_, lean_object* v_a_6906_, lean_object* v_a_6907_){
_start:
{
if (lean_obj_tag(v_a_6906_) == 0)
{
lean_object* v___x_6908_; 
lean_dec_ref(v_date_6904_);
v___x_6908_ = l_List_reverse___redArg(v_a_6907_);
return v___x_6908_;
}
else
{
lean_object* v_head_6909_; lean_object* v_tail_6910_; lean_object* v___x_6912_; uint8_t v_isShared_6913_; uint8_t v_isSharedCheck_6939_; 
v_head_6909_ = lean_ctor_get(v_a_6906_, 0);
v_tail_6910_ = lean_ctor_get(v_a_6906_, 1);
v_isSharedCheck_6939_ = !lean_is_exclusive(v_a_6906_);
if (v_isSharedCheck_6939_ == 0)
{
v___x_6912_ = v_a_6906_;
v_isShared_6913_ = v_isSharedCheck_6939_;
goto v_resetjp_6911_;
}
else
{
lean_inc(v_tail_6910_);
lean_inc(v_head_6909_);
lean_dec(v_a_6906_);
v___x_6912_ = lean_box(0);
v_isShared_6913_ = v_isSharedCheck_6939_;
goto v_resetjp_6911_;
}
v_resetjp_6911_:
{
lean_object* v___y_6915_; 
if (lean_obj_tag(v_aw_6903_) == 0)
{
lean_object* v_a_6920_; lean_object* v_offset_6921_; lean_object* v_name_6922_; lean_object* v_abbreviation_6923_; uint8_t v_isDST_6924_; lean_object* v_timestamp_6925_; uint8_t v___x_6926_; uint8_t v___x_6927_; lean_object* v_ltt_6928_; lean_object* v___x_6929_; lean_object* v___x_6930_; lean_object* v___x_6931_; lean_object* v___x_6932_; lean_object* v_tz_6933_; lean_object* v___f_6934_; lean_object* v___x_6935_; lean_object* v___x_6936_; lean_object* v___x_6937_; 
v_a_6920_ = lean_ctor_get(v_aw_6903_, 0);
v_offset_6921_ = lean_ctor_get(v_a_6920_, 0);
v_name_6922_ = lean_ctor_get(v_a_6920_, 1);
v_abbreviation_6923_ = lean_ctor_get(v_a_6920_, 2);
v_isDST_6924_ = lean_ctor_get_uint8(v_a_6920_, sizeof(void*)*3);
v_timestamp_6925_ = lean_ctor_get(v_date_6904_, 1);
v___x_6926_ = 0;
v___x_6927_ = 1;
lean_inc_ref(v_name_6922_);
lean_inc_ref(v_abbreviation_6923_);
lean_inc(v_offset_6921_);
v_ltt_6928_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6928_, 0, v_offset_6921_);
lean_ctor_set(v_ltt_6928_, 1, v_abbreviation_6923_);
lean_ctor_set(v_ltt_6928_, 2, v_name_6922_);
lean_ctor_set_uint8(v_ltt_6928_, sizeof(void*)*3, v_isDST_6924_);
lean_ctor_set_uint8(v_ltt_6928_, sizeof(void*)*3 + 1, v___x_6926_);
lean_ctor_set_uint8(v_ltt_6928_, sizeof(void*)*3 + 2, v___x_6927_);
v___x_6929_ = lean_unsigned_to_nat(0u);
v___x_6930_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6931_ = lean_box(0);
v___x_6932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6932_, 0, v_ltt_6928_);
lean_ctor_set(v___x_6932_, 1, v___x_6930_);
lean_ctor_set(v___x_6932_, 2, v___x_6931_);
lean_inc_ref(v___x_6932_);
v_tz_6933_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_6932_, v_timestamp_6925_);
lean_inc_ref_n(v_timestamp_6925_, 2);
lean_inc_ref(v_tz_6933_);
v___f_6934_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_6934_, 0, v_tz_6933_);
lean_closure_set(v___f_6934_, 1, v_timestamp_6925_);
lean_closure_set(v___f_6934_, 2, v___x_6929_);
v___x_6935_ = lean_mk_thunk(v___f_6934_);
v___x_6936_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6936_, 0, v___x_6935_);
lean_ctor_set(v___x_6936_, 1, v_timestamp_6925_);
lean_ctor_set(v___x_6936_, 2, v___x_6932_);
lean_ctor_set(v___x_6936_, 3, v_tz_6933_);
v___x_6937_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6905_, v___x_6936_, v_head_6909_);
v___y_6915_ = v___x_6937_;
goto v___jp_6914_;
}
else
{
lean_object* v___x_6938_; 
lean_inc_ref(v_date_6904_);
v___x_6938_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6905_, v_date_6904_, v_head_6909_);
v___y_6915_ = v___x_6938_;
goto v___jp_6914_;
}
v___jp_6914_:
{
lean_object* v___x_6917_; 
if (v_isShared_6913_ == 0)
{
lean_ctor_set(v___x_6912_, 1, v_a_6907_);
lean_ctor_set(v___x_6912_, 0, v___y_6915_);
v___x_6917_ = v___x_6912_;
goto v_reusejp_6916_;
}
else
{
lean_object* v_reuseFailAlloc_6919_; 
v_reuseFailAlloc_6919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6919_, 0, v___y_6915_);
lean_ctor_set(v_reuseFailAlloc_6919_, 1, v_a_6907_);
v___x_6917_ = v_reuseFailAlloc_6919_;
goto v_reusejp_6916_;
}
v_reusejp_6916_:
{
v_a_6906_ = v_tail_6910_;
v_a_6907_ = v___x_6917_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___boxed(lean_object* v_aw_6940_, lean_object* v_date_6941_, lean_object* v_dateformat_6942_, lean_object* v_a_6943_, lean_object* v_a_6944_){
_start:
{
lean_object* v_res_6945_; 
v_res_6945_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6940_, v_date_6941_, v_dateformat_6942_, v_a_6943_, v_a_6944_);
lean_dec_ref(v_dateformat_6942_);
lean_dec(v_aw_6940_);
return v_res_6945_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object* v_aw_6946_, lean_object* v_format_6947_, lean_object* v_date_6948_){
_start:
{
lean_object* v_config_6949_; lean_object* v_string_6950_; lean_object* v_dateformat_6951_; lean_object* v___x_6952_; lean_object* v___x_6953_; lean_object* v___x_6954_; lean_object* v___x_6955_; 
v_config_6949_ = lean_ctor_get(v_format_6947_, 0);
lean_inc_ref(v_config_6949_);
v_string_6950_ = lean_ctor_get(v_format_6947_, 1);
lean_inc(v_string_6950_);
lean_dec_ref(v_format_6947_);
v_dateformat_6951_ = lean_ctor_get(v_config_6949_, 0);
lean_inc_ref(v_dateformat_6951_);
lean_dec_ref(v_config_6949_);
v___x_6952_ = lean_box(0);
v___x_6953_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6946_, v_date_6948_, v_dateformat_6951_, v_string_6950_, v___x_6952_);
lean_dec_ref(v_dateformat_6951_);
v___x_6954_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_6955_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v___x_6954_, v___x_6953_);
lean_dec(v___x_6953_);
return v___x_6955_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object* v_aw_6956_, lean_object* v_format_6957_, lean_object* v_date_6958_){
_start:
{
lean_object* v_res_6959_; 
v_res_6959_ = l_Std_Time_GenericFormat_format(v_aw_6956_, v_format_6957_, v_date_6958_);
lean_dec(v_aw_6956_);
return v_res_6959_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object* v_config_6963_, lean_object* v_aw_6964_, lean_object* v_builder_6965_, lean_object* v_x_6966_, lean_object* v_a_6967_){
_start:
{
if (lean_obj_tag(v_x_6966_) == 0)
{
lean_object* v___x_6968_; 
lean_dec_ref(v_config_6963_);
v___x_6968_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_6965_, v_aw_6964_);
if (lean_obj_tag(v___x_6968_) == 0)
{
lean_object* v___x_6969_; lean_object* v___x_6970_; 
v___x_6969_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1));
v___x_6970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6970_, 0, v_a_6967_);
lean_ctor_set(v___x_6970_, 1, v___x_6969_);
return v___x_6970_;
}
else
{
lean_object* v_val_6971_; lean_object* v___x_6972_; 
v_val_6971_ = lean_ctor_get(v___x_6968_, 0);
lean_inc(v_val_6971_);
lean_dec_ref_known(v___x_6968_, 1);
v___x_6972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6972_, 0, v_a_6967_);
lean_ctor_set(v___x_6972_, 1, v_val_6971_);
return v___x_6972_;
}
}
else
{
lean_object* v_head_6973_; lean_object* v_tail_6974_; lean_object* v___x_6975_; 
v_head_6973_ = lean_ctor_get(v_x_6966_, 0);
lean_inc(v_head_6973_);
v_tail_6974_ = lean_ctor_get(v_x_6966_, 1);
lean_inc(v_tail_6974_);
lean_dec_ref_known(v_x_6966_, 2);
lean_inc_ref(v_config_6963_);
v___x_6975_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(v_builder_6965_, v_config_6963_, v_head_6973_, v_a_6967_);
if (lean_obj_tag(v___x_6975_) == 0)
{
lean_object* v_pos_6976_; lean_object* v_res_6977_; 
v_pos_6976_ = lean_ctor_get(v___x_6975_, 0);
lean_inc(v_pos_6976_);
v_res_6977_ = lean_ctor_get(v___x_6975_, 1);
lean_inc(v_res_6977_);
lean_dec_ref_known(v___x_6975_, 2);
v_builder_6965_ = v_res_6977_;
v_x_6966_ = v_tail_6974_;
v_a_6967_ = v_pos_6976_;
goto _start;
}
else
{
lean_object* v_pos_6979_; lean_object* v_err_6980_; lean_object* v___x_6982_; uint8_t v_isShared_6983_; uint8_t v_isSharedCheck_6987_; 
lean_dec(v_tail_6974_);
lean_dec(v_aw_6964_);
lean_dec_ref(v_config_6963_);
v_pos_6979_ = lean_ctor_get(v___x_6975_, 0);
v_err_6980_ = lean_ctor_get(v___x_6975_, 1);
v_isSharedCheck_6987_ = !lean_is_exclusive(v___x_6975_);
if (v_isSharedCheck_6987_ == 0)
{
v___x_6982_ = v___x_6975_;
v_isShared_6983_ = v_isSharedCheck_6987_;
goto v_resetjp_6981_;
}
else
{
lean_inc(v_err_6980_);
lean_inc(v_pos_6979_);
lean_dec(v___x_6975_);
v___x_6982_ = lean_box(0);
v_isShared_6983_ = v_isSharedCheck_6987_;
goto v_resetjp_6981_;
}
v_resetjp_6981_:
{
lean_object* v___x_6985_; 
if (v_isShared_6983_ == 0)
{
v___x_6985_ = v___x_6982_;
goto v_reusejp_6984_;
}
else
{
lean_object* v_reuseFailAlloc_6986_; 
v_reuseFailAlloc_6986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6986_, 0, v_pos_6979_);
lean_ctor_set(v_reuseFailAlloc_6986_, 1, v_err_6980_);
v___x_6985_ = v_reuseFailAlloc_6986_;
goto v_reusejp_6984_;
}
v_reusejp_6984_:
{
return v___x_6985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object* v_format_6990_, lean_object* v_config_6991_, lean_object* v_aw_6992_, lean_object* v_a_6993_){
_start:
{
lean_object* v___x_6994_; lean_object* v___x_6995_; 
v___x_6994_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0));
v___x_6995_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(v_config_6991_, v_aw_6992_, v___x_6994_, v_format_6990_, v_a_6993_);
return v___x_6995_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object* v_config_6999_, lean_object* v_format_7000_, lean_object* v_func_7001_, lean_object* v_a_7002_){
_start:
{
if (lean_obj_tag(v_format_7000_) == 0)
{
lean_dec_ref(v_config_6999_);
if (lean_obj_tag(v_func_7001_) == 0)
{
lean_object* v___x_7003_; lean_object* v___x_7004_; 
v___x_7003_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1));
v___x_7004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7004_, 0, v_a_7002_);
lean_ctor_set(v___x_7004_, 1, v___x_7003_);
return v___x_7004_;
}
else
{
lean_object* v_val_7005_; lean_object* v_fst_7006_; lean_object* v_snd_7007_; lean_object* v___x_7008_; uint8_t v___x_7009_; 
v_val_7005_ = lean_ctor_get(v_func_7001_, 0);
lean_inc(v_val_7005_);
lean_dec_ref_known(v_func_7001_, 1);
v_fst_7006_ = lean_ctor_get(v_a_7002_, 0);
v_snd_7007_ = lean_ctor_get(v_a_7002_, 1);
v___x_7008_ = lean_string_utf8_byte_size(v_fst_7006_);
v___x_7009_ = lean_nat_dec_eq(v_snd_7007_, v___x_7008_);
if (v___x_7009_ == 0)
{
lean_object* v___x_7010_; lean_object* v___x_7011_; 
lean_dec(v_val_7005_);
v___x_7010_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
v___x_7011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7011_, 0, v_a_7002_);
lean_ctor_set(v___x_7011_, 1, v___x_7010_);
return v___x_7011_;
}
else
{
lean_object* v___x_7012_; 
v___x_7012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7012_, 0, v_a_7002_);
lean_ctor_set(v___x_7012_, 1, v_val_7005_);
return v___x_7012_;
}
}
}
else
{
lean_object* v_head_7013_; 
v_head_7013_ = lean_ctor_get(v_format_7000_, 0);
lean_inc(v_head_7013_);
if (lean_obj_tag(v_head_7013_) == 0)
{
lean_object* v_tail_7014_; lean_object* v_val_7015_; lean_object* v___x_7016_; 
v_tail_7014_ = lean_ctor_get(v_format_7000_, 1);
lean_inc(v_tail_7014_);
lean_dec_ref_known(v_format_7000_, 2);
v_val_7015_ = lean_ctor_get(v_head_7013_, 0);
lean_inc_ref(v_val_7015_);
lean_dec_ref_known(v_head_7013_, 1);
v___x_7016_ = l_Std_Internal_Parsec_String_pstring(v_val_7015_, v_a_7002_);
if (lean_obj_tag(v___x_7016_) == 0)
{
lean_object* v_pos_7017_; 
v_pos_7017_ = lean_ctor_get(v___x_7016_, 0);
lean_inc(v_pos_7017_);
lean_dec_ref_known(v___x_7016_, 2);
v_format_7000_ = v_tail_7014_;
v_a_7002_ = v_pos_7017_;
goto _start;
}
else
{
lean_object* v_pos_7019_; lean_object* v_err_7020_; lean_object* v___x_7022_; uint8_t v_isShared_7023_; uint8_t v_isSharedCheck_7027_; 
lean_dec(v_tail_7014_);
lean_dec(v_func_7001_);
lean_dec_ref(v_config_6999_);
v_pos_7019_ = lean_ctor_get(v___x_7016_, 0);
v_err_7020_ = lean_ctor_get(v___x_7016_, 1);
v_isSharedCheck_7027_ = !lean_is_exclusive(v___x_7016_);
if (v_isSharedCheck_7027_ == 0)
{
v___x_7022_ = v___x_7016_;
v_isShared_7023_ = v_isSharedCheck_7027_;
goto v_resetjp_7021_;
}
else
{
lean_inc(v_err_7020_);
lean_inc(v_pos_7019_);
lean_dec(v___x_7016_);
v___x_7022_ = lean_box(0);
v_isShared_7023_ = v_isSharedCheck_7027_;
goto v_resetjp_7021_;
}
v_resetjp_7021_:
{
lean_object* v___x_7025_; 
if (v_isShared_7023_ == 0)
{
v___x_7025_ = v___x_7022_;
goto v_reusejp_7024_;
}
else
{
lean_object* v_reuseFailAlloc_7026_; 
v_reuseFailAlloc_7026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7026_, 0, v_pos_7019_);
lean_ctor_set(v_reuseFailAlloc_7026_, 1, v_err_7020_);
v___x_7025_ = v_reuseFailAlloc_7026_;
goto v_reusejp_7024_;
}
v_reusejp_7024_:
{
return v___x_7025_;
}
}
}
}
else
{
lean_object* v_tail_7028_; lean_object* v_modifier_7029_; lean_object* v___x_7030_; 
v_tail_7028_ = lean_ctor_get(v_format_7000_, 1);
lean_inc(v_tail_7028_);
lean_dec_ref_known(v_format_7000_, 2);
v_modifier_7029_ = lean_ctor_get(v_head_7013_, 0);
lean_inc_ref(v_modifier_7029_);
lean_dec_ref_known(v_head_7013_, 1);
lean_inc_ref(v_config_6999_);
v___x_7030_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6999_, v_modifier_7029_, v_a_7002_);
if (lean_obj_tag(v___x_7030_) == 0)
{
lean_object* v_pos_7031_; lean_object* v_res_7032_; lean_object* v___x_7033_; 
v_pos_7031_ = lean_ctor_get(v___x_7030_, 0);
lean_inc(v_pos_7031_);
v_res_7032_ = lean_ctor_get(v___x_7030_, 1);
lean_inc(v_res_7032_);
lean_dec_ref_known(v___x_7030_, 2);
v___x_7033_ = lean_apply_1(v_func_7001_, v_res_7032_);
v_format_7000_ = v_tail_7028_;
v_func_7001_ = v___x_7033_;
v_a_7002_ = v_pos_7031_;
goto _start;
}
else
{
lean_object* v_pos_7035_; lean_object* v_err_7036_; lean_object* v___x_7038_; uint8_t v_isShared_7039_; uint8_t v_isSharedCheck_7043_; 
lean_dec(v_tail_7028_);
lean_dec(v_func_7001_);
lean_dec_ref(v_config_6999_);
v_pos_7035_ = lean_ctor_get(v___x_7030_, 0);
v_err_7036_ = lean_ctor_get(v___x_7030_, 1);
v_isSharedCheck_7043_ = !lean_is_exclusive(v___x_7030_);
if (v_isSharedCheck_7043_ == 0)
{
v___x_7038_ = v___x_7030_;
v_isShared_7039_ = v_isSharedCheck_7043_;
goto v_resetjp_7037_;
}
else
{
lean_inc(v_err_7036_);
lean_inc(v_pos_7035_);
lean_dec(v___x_7030_);
v___x_7038_ = lean_box(0);
v_isShared_7039_ = v_isSharedCheck_7043_;
goto v_resetjp_7037_;
}
v_resetjp_7037_:
{
lean_object* v___x_7041_; 
if (v_isShared_7039_ == 0)
{
v___x_7041_ = v___x_7038_;
goto v_reusejp_7040_;
}
else
{
lean_object* v_reuseFailAlloc_7042_; 
v_reuseFailAlloc_7042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7042_, 0, v_pos_7035_);
lean_ctor_set(v_reuseFailAlloc_7042_, 1, v_err_7036_);
v___x_7041_ = v_reuseFailAlloc_7042_;
goto v_reusejp_7040_;
}
v_reusejp_7040_:
{
return v___x_7041_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object* v_00_u03b1_7044_, lean_object* v_config_7045_, lean_object* v_format_7046_, lean_object* v_func_7047_, lean_object* v_a_7048_){
_start:
{
lean_object* v___x_7049_; 
v___x_7049_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7045_, v_format_7046_, v_func_7047_, v_a_7048_);
return v___x_7049_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object* v_format_7050_, lean_object* v_config_7051_, lean_object* v_func_7052_, lean_object* v_a_7053_){
_start:
{
lean_object* v___x_7054_; 
v___x_7054_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7051_, v_format_7050_, v_func_7052_, v_a_7053_);
return v___x_7054_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object* v_00_u03b1_7055_, lean_object* v_format_7056_, lean_object* v_config_7057_, lean_object* v_func_7058_, lean_object* v_a_7059_){
_start:
{
lean_object* v___x_7060_; 
v___x_7060_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7057_, v_format_7056_, v_func_7058_, v_a_7059_);
return v___x_7060_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object* v_string_7061_, lean_object* v_config_7062_, lean_object* v_aw_7063_, lean_object* v___y_7064_){
_start:
{
lean_object* v___x_7065_; 
v___x_7065_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(v_string_7061_, v_config_7062_, v_aw_7063_, v___y_7064_);
if (lean_obj_tag(v___x_7065_) == 0)
{
lean_object* v_pos_7066_; lean_object* v_fst_7067_; lean_object* v_snd_7068_; lean_object* v___x_7069_; uint8_t v___x_7070_; 
v_pos_7066_ = lean_ctor_get(v___x_7065_, 0);
lean_inc(v_pos_7066_);
v_fst_7067_ = lean_ctor_get(v_pos_7066_, 0);
v_snd_7068_ = lean_ctor_get(v_pos_7066_, 1);
v___x_7069_ = lean_string_utf8_byte_size(v_fst_7067_);
v___x_7070_ = lean_nat_dec_eq(v_snd_7068_, v___x_7069_);
if (v___x_7070_ == 0)
{
lean_object* v___x_7072_; uint8_t v_isShared_7073_; uint8_t v_isSharedCheck_7078_; 
v_isSharedCheck_7078_ = !lean_is_exclusive(v___x_7065_);
if (v_isSharedCheck_7078_ == 0)
{
lean_object* v_unused_7079_; lean_object* v_unused_7080_; 
v_unused_7079_ = lean_ctor_get(v___x_7065_, 1);
lean_dec(v_unused_7079_);
v_unused_7080_ = lean_ctor_get(v___x_7065_, 0);
lean_dec(v_unused_7080_);
v___x_7072_ = v___x_7065_;
v_isShared_7073_ = v_isSharedCheck_7078_;
goto v_resetjp_7071_;
}
else
{
lean_dec(v___x_7065_);
v___x_7072_ = lean_box(0);
v_isShared_7073_ = v_isSharedCheck_7078_;
goto v_resetjp_7071_;
}
v_resetjp_7071_:
{
lean_object* v___x_7074_; lean_object* v___x_7076_; 
v___x_7074_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_7073_ == 0)
{
lean_ctor_set_tag(v___x_7072_, 1);
lean_ctor_set(v___x_7072_, 1, v___x_7074_);
v___x_7076_ = v___x_7072_;
goto v_reusejp_7075_;
}
else
{
lean_object* v_reuseFailAlloc_7077_; 
v_reuseFailAlloc_7077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7077_, 0, v_pos_7066_);
lean_ctor_set(v_reuseFailAlloc_7077_, 1, v___x_7074_);
v___x_7076_ = v_reuseFailAlloc_7077_;
goto v_reusejp_7075_;
}
v_reusejp_7075_:
{
return v___x_7076_;
}
}
}
else
{
lean_dec(v_pos_7066_);
return v___x_7065_;
}
}
else
{
return v___x_7065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object* v_aw_7081_, lean_object* v_format_7082_, lean_object* v_input_7083_){
_start:
{
lean_object* v_config_7084_; lean_object* v_string_7085_; lean_object* v___f_7086_; lean_object* v___x_7087_; 
v_config_7084_ = lean_ctor_get(v_format_7082_, 0);
lean_inc_ref(v_config_7084_);
v_string_7085_ = lean_ctor_get(v_format_7082_, 1);
lean_inc(v_string_7085_);
lean_dec_ref(v_format_7082_);
v___f_7086_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parse___lam__0), 4, 3);
lean_closure_set(v___f_7086_, 0, v_string_7085_);
lean_closure_set(v___f_7086_, 1, v_config_7084_);
lean_closure_set(v___f_7086_, 2, v_aw_7081_);
v___x_7087_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7086_, v_input_7083_);
return v___x_7087_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object* v_msg_7088_){
_start:
{
lean_object* v___x_7089_; lean_object* v___x_7090_; 
v___x_7089_ = l_Std_Time_instInhabitedDateTime;
v___x_7090_ = lean_panic_fn_borrowed(v___x_7089_, v_msg_7088_);
return v___x_7090_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object* v_aw_7092_, lean_object* v_format_7093_, lean_object* v_input_7094_){
_start:
{
lean_object* v___x_7095_; 
v___x_7095_ = l_Std_Time_GenericFormat_parse(v_aw_7092_, v_format_7093_, v_input_7094_);
if (lean_obj_tag(v___x_7095_) == 0)
{
lean_object* v_a_7096_; lean_object* v___x_7097_; lean_object* v___x_7098_; lean_object* v___x_7099_; lean_object* v___x_7100_; lean_object* v___x_7101_; lean_object* v___x_7102_; 
v_a_7096_ = lean_ctor_get(v___x_7095_, 0);
lean_inc(v_a_7096_);
lean_dec_ref_known(v___x_7095_, 1);
v___x_7097_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7098_ = ((lean_object*)(l_Std_Time_GenericFormat_parse_x21___closed__0));
v___x_7099_ = lean_unsigned_to_nat(1124u);
v___x_7100_ = lean_unsigned_to_nat(18u);
v___x_7101_ = l_mkPanicMessageWithDecl(v___x_7097_, v___x_7098_, v___x_7099_, v___x_7100_, v_a_7096_);
lean_dec(v_a_7096_);
v___x_7102_ = l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(v___x_7101_);
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
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object* v_config_7104_, lean_object* v_string_7105_, lean_object* v_builder_7106_, lean_object* v___y_7107_){
_start:
{
lean_object* v___x_7108_; 
v___x_7108_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7104_, v_string_7105_, v_builder_7106_, v___y_7107_);
return v___x_7108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object* v_format_7109_, lean_object* v_builder_7110_, lean_object* v_input_7111_){
_start:
{
lean_object* v_config_7112_; lean_object* v_string_7113_; lean_object* v___f_7114_; lean_object* v___x_7115_; 
v_config_7112_ = lean_ctor_get(v_format_7109_, 0);
lean_inc_ref(v_config_7112_);
v_string_7113_ = lean_ctor_get(v_format_7109_, 1);
lean_inc(v_string_7113_);
lean_dec_ref(v_format_7109_);
v___f_7114_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0), 4, 3);
lean_closure_set(v___f_7114_, 0, v_config_7112_);
lean_closure_set(v___f_7114_, 1, v_string_7113_);
lean_closure_set(v___f_7114_, 2, v_builder_7110_);
v___x_7115_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7114_, v_input_7111_);
return v___x_7115_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object* v_aw_7116_, lean_object* v_00_u03b1_7117_, lean_object* v_format_7118_, lean_object* v_builder_7119_, lean_object* v_input_7120_){
_start:
{
lean_object* v___x_7121_; 
v___x_7121_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7118_, v_builder_7119_, v_input_7120_);
return v___x_7121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object* v_aw_7122_, lean_object* v_00_u03b1_7123_, lean_object* v_format_7124_, lean_object* v_builder_7125_, lean_object* v_input_7126_){
_start:
{
lean_object* v_res_7127_; 
v_res_7127_ = l_Std_Time_GenericFormat_parseBuilder(v_aw_7122_, v_00_u03b1_7123_, v_format_7124_, v_builder_7125_, v_input_7126_);
lean_dec(v_aw_7122_);
return v_res_7127_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object* v_inst_7129_, lean_object* v_format_7130_, lean_object* v_builder_7131_, lean_object* v_input_7132_){
_start:
{
lean_object* v___x_7133_; 
v___x_7133_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7130_, v_builder_7131_, v_input_7132_);
if (lean_obj_tag(v___x_7133_) == 0)
{
lean_object* v_a_7134_; lean_object* v___x_7135_; lean_object* v___x_7136_; lean_object* v___x_7137_; lean_object* v___x_7138_; lean_object* v___x_7139_; lean_object* v___x_7140_; 
v_a_7134_ = lean_ctor_get(v___x_7133_, 0);
lean_inc(v_a_7134_);
lean_dec_ref_known(v___x_7133_, 1);
v___x_7135_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7136_ = ((lean_object*)(l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0));
v___x_7137_ = lean_unsigned_to_nat(1138u);
v___x_7138_ = lean_unsigned_to_nat(18u);
v___x_7139_ = l_mkPanicMessageWithDecl(v___x_7135_, v___x_7136_, v___x_7137_, v___x_7138_, v_a_7134_);
lean_dec(v_a_7134_);
v___x_7140_ = l_panic___redArg(v_inst_7129_, v___x_7139_);
return v___x_7140_;
}
else
{
lean_object* v_a_7141_; 
v_a_7141_ = lean_ctor_get(v___x_7133_, 0);
lean_inc(v_a_7141_);
lean_dec_ref_known(v___x_7133_, 1);
return v_a_7141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object* v_inst_7142_, lean_object* v_format_7143_, lean_object* v_builder_7144_, lean_object* v_input_7145_){
_start:
{
lean_object* v_res_7146_; 
v_res_7146_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7142_, v_format_7143_, v_builder_7144_, v_input_7145_);
lean_dec(v_inst_7142_);
return v_res_7146_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object* v_00_u03b1_7147_, lean_object* v_aw_7148_, lean_object* v_inst_7149_, lean_object* v_format_7150_, lean_object* v_builder_7151_, lean_object* v_input_7152_){
_start:
{
lean_object* v___x_7153_; 
v___x_7153_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7149_, v_format_7150_, v_builder_7151_, v_input_7152_);
return v___x_7153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object* v_00_u03b1_7154_, lean_object* v_aw_7155_, lean_object* v_inst_7156_, lean_object* v_format_7157_, lean_object* v_builder_7158_, lean_object* v_input_7159_){
_start:
{
lean_object* v_res_7160_; 
v_res_7160_ = l_Std_Time_GenericFormat_parseBuilder_x21(v_00_u03b1_7154_, v_aw_7155_, v_inst_7156_, v_format_7157_, v_builder_7158_, v_input_7159_);
lean_dec(v_inst_7156_);
lean_dec(v_aw_7155_);
return v_res_7160_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object* v_getInfo_7161_, lean_object* v_dateformat_7162_, lean_object* v_data_7163_, lean_object* v_format_7164_){
_start:
{
if (lean_obj_tag(v_format_7164_) == 0)
{
lean_object* v___x_7165_; 
lean_dec_ref(v_getInfo_7161_);
v___x_7165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7165_, 0, v_data_7163_);
return v___x_7165_;
}
else
{
lean_object* v_head_7166_; 
v_head_7166_ = lean_ctor_get(v_format_7164_, 0);
lean_inc(v_head_7166_);
if (lean_obj_tag(v_head_7166_) == 0)
{
lean_object* v_tail_7167_; lean_object* v_val_7168_; lean_object* v___x_7169_; 
v_tail_7167_ = lean_ctor_get(v_format_7164_, 1);
lean_inc(v_tail_7167_);
lean_dec_ref_known(v_format_7164_, 2);
v_val_7168_ = lean_ctor_get(v_head_7166_, 0);
lean_inc_ref(v_val_7168_);
lean_dec_ref_known(v_head_7166_, 1);
v___x_7169_ = lean_string_append(v_data_7163_, v_val_7168_);
lean_dec_ref(v_val_7168_);
v_data_7163_ = v___x_7169_;
v_format_7164_ = v_tail_7167_;
goto _start;
}
else
{
lean_object* v_tail_7171_; lean_object* v_modifier_7172_; lean_object* v___x_7173_; 
v_tail_7171_ = lean_ctor_get(v_format_7164_, 1);
lean_inc(v_tail_7171_);
lean_dec_ref_known(v_format_7164_, 2);
v_modifier_7172_ = lean_ctor_get(v_head_7166_, 0);
lean_inc_ref_n(v_modifier_7172_, 2);
lean_dec_ref_known(v_head_7166_, 1);
lean_inc_ref(v_getInfo_7161_);
v___x_7173_ = lean_apply_1(v_getInfo_7161_, v_modifier_7172_);
if (lean_obj_tag(v___x_7173_) == 0)
{
lean_object* v___x_7174_; 
lean_dec_ref(v_modifier_7172_);
lean_dec(v_tail_7171_);
lean_dec_ref(v_data_7163_);
lean_dec_ref(v_getInfo_7161_);
v___x_7174_ = lean_box(0);
return v___x_7174_;
}
else
{
lean_object* v_val_7175_; lean_object* v___x_7176_; lean_object* v___x_7177_; 
v_val_7175_ = lean_ctor_get(v___x_7173_, 0);
lean_inc(v_val_7175_);
lean_dec_ref_known(v___x_7173_, 1);
v___x_7176_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7162_, v_modifier_7172_, v_val_7175_);
v___x_7177_ = lean_string_append(v_data_7163_, v___x_7176_);
lean_dec_ref(v___x_7176_);
v_data_7163_ = v___x_7177_;
v_format_7164_ = v_tail_7171_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go___boxed(lean_object* v_getInfo_7179_, lean_object* v_dateformat_7180_, lean_object* v_data_7181_, lean_object* v_format_7182_){
_start:
{
lean_object* v_res_7183_; 
v_res_7183_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7179_, v_dateformat_7180_, v_data_7181_, v_format_7182_);
lean_dec_ref(v_dateformat_7180_);
return v_res_7183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object* v_format_7184_, lean_object* v_getInfo_7185_){
_start:
{
lean_object* v_config_7186_; lean_object* v_string_7187_; lean_object* v_dateformat_7188_; lean_object* v___x_7189_; lean_object* v___x_7190_; 
v_config_7186_ = lean_ctor_get(v_format_7184_, 0);
lean_inc_ref(v_config_7186_);
v_string_7187_ = lean_ctor_get(v_format_7184_, 1);
lean_inc(v_string_7187_);
lean_dec_ref(v_format_7184_);
v_dateformat_7188_ = lean_ctor_get(v_config_7186_, 0);
lean_inc_ref(v_dateformat_7188_);
lean_dec_ref(v_config_7186_);
v___x_7189_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_7190_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7185_, v_dateformat_7188_, v___x_7189_, v_string_7187_);
lean_dec_ref(v_dateformat_7188_);
return v___x_7190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object* v_aw_7191_, lean_object* v_format_7192_, lean_object* v_getInfo_7193_){
_start:
{
lean_object* v___x_7194_; 
v___x_7194_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7192_, v_getInfo_7193_);
return v___x_7194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object* v_aw_7195_, lean_object* v_format_7196_, lean_object* v_getInfo_7197_){
_start:
{
lean_object* v_res_7198_; 
v_res_7198_ = l_Std_Time_GenericFormat_formatGeneric(v_aw_7195_, v_format_7196_, v_getInfo_7197_);
lean_dec(v_aw_7195_);
return v_res_7198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object* v_dateformat_7199_, lean_object* v_data_7200_, lean_object* v_format_7201_){
_start:
{
if (lean_obj_tag(v_format_7201_) == 0)
{
lean_dec_ref(v_dateformat_7199_);
return v_data_7200_;
}
else
{
lean_object* v_head_7202_; 
v_head_7202_ = lean_ctor_get(v_format_7201_, 0);
lean_inc(v_head_7202_);
if (lean_obj_tag(v_head_7202_) == 0)
{
lean_object* v_tail_7203_; lean_object* v_val_7204_; lean_object* v___x_7205_; 
v_tail_7203_ = lean_ctor_get(v_format_7201_, 1);
lean_inc(v_tail_7203_);
lean_dec_ref_known(v_format_7201_, 2);
v_val_7204_ = lean_ctor_get(v_head_7202_, 0);
lean_inc_ref(v_val_7204_);
lean_dec_ref_known(v_head_7202_, 1);
v___x_7205_ = lean_string_append(v_data_7200_, v_val_7204_);
lean_dec_ref(v_val_7204_);
v_data_7200_ = v___x_7205_;
v_format_7201_ = v_tail_7203_;
goto _start;
}
else
{
lean_object* v_tail_7207_; lean_object* v_modifier_7208_; lean_object* v___f_7209_; 
v_tail_7207_ = lean_ctor_get(v_format_7201_, 1);
lean_inc(v_tail_7207_);
lean_dec_ref_known(v_format_7201_, 2);
v_modifier_7208_ = lean_ctor_get(v_head_7202_, 0);
lean_inc_ref(v_modifier_7208_);
lean_dec_ref_known(v_head_7202_, 1);
v___f_7209_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0), 5, 4);
lean_closure_set(v___f_7209_, 0, v_dateformat_7199_);
lean_closure_set(v___f_7209_, 1, v_modifier_7208_);
lean_closure_set(v___f_7209_, 2, v_data_7200_);
lean_closure_set(v___f_7209_, 3, v_tail_7207_);
return v___f_7209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object* v_dateformat_7210_, lean_object* v_modifier_7211_, lean_object* v_data_7212_, lean_object* v_tail_7213_, lean_object* v___y_7214_){
_start:
{
lean_object* v___x_7215_; lean_object* v___x_7216_; lean_object* v___x_7217_; 
v___x_7215_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7210_, v_modifier_7211_, v___y_7214_);
v___x_7216_ = lean_string_append(v_data_7212_, v___x_7215_);
lean_dec_ref(v___x_7215_);
v___x_7217_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7210_, v___x_7216_, v_tail_7213_);
return v___x_7217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object* v_format_7218_){
_start:
{
lean_object* v_config_7219_; lean_object* v_string_7220_; lean_object* v_dateformat_7221_; lean_object* v___x_7222_; lean_object* v___x_7223_; 
v_config_7219_ = lean_ctor_get(v_format_7218_, 0);
lean_inc_ref(v_config_7219_);
v_string_7220_ = lean_ctor_get(v_format_7218_, 1);
lean_inc(v_string_7220_);
lean_dec_ref(v_format_7218_);
v_dateformat_7221_ = lean_ctor_get(v_config_7219_, 0);
lean_inc_ref(v_dateformat_7221_);
lean_dec_ref(v_config_7219_);
v___x_7222_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_7223_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7221_, v___x_7222_, v_string_7220_);
return v___x_7223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object* v_aw_7224_, lean_object* v_format_7225_){
_start:
{
lean_object* v___x_7226_; 
v___x_7226_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v_format_7225_);
return v___x_7226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object* v_aw_7227_, lean_object* v_format_7228_){
_start:
{
lean_object* v_res_7229_; 
v_res_7229_ = l_Std_Time_GenericFormat_formatBuilder(v_aw_7227_, v_format_7228_);
lean_dec(v_aw_7227_);
return v_res_7229_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instFormatGenericFormatFormatTypeString(lean_object* v_aw_7230_){
_start:
{
lean_object* v___x_7231_; lean_object* v___x_7232_; lean_object* v___x_7233_; 
lean_inc(v_aw_7230_);
v___x_7231_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_formatBuilder___boxed), 2, 1);
lean_closure_set(v___x_7231_, 0, v_aw_7230_);
v___x_7232_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___boxed), 5, 1);
lean_closure_set(v___x_7232_, 0, v_aw_7230_);
v___x_7233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7233_, 0, v___x_7231_);
lean_ctor_set(v___x_7233_, 1, v___x_7232_);
return v___x_7233_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Format_Modifier(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Format_DateFormat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
