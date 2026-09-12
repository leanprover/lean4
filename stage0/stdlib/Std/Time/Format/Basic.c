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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint8_t v_decide_272_, uint32_t v___x_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v___x_280_; uint8_t v_decide_281_; 
v_fst_278_ = lean_ctor_get(v___y_274_, 0);
v_snd_279_ = lean_ctor_get(v___y_274_, 1);
v___x_280_ = lean_string_utf8_byte_size(v_fst_278_);
v_decide_281_ = lean_nat_dec_eq(v_snd_279_, v___x_280_);
if (v_decide_281_ == 0)
{
if (v_decide_272_ == 0)
{
goto v___jp_275_;
}
else
{
uint32_t v_c_282_; uint8_t v___x_283_; 
v_c_282_ = lean_string_utf8_get_fast(v_fst_278_, v_snd_279_);
v___x_283_ = lean_uint32_dec_eq(v_c_282_, v___x_273_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_284_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_285_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_286_ = lean_string_push(v___x_285_, v___x_273_);
v___x_287_ = lean_string_append(v___x_284_, v___x_286_);
lean_dec_ref(v___x_286_);
v___x_288_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_289_ = lean_string_append(v___x_287_, v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v___y_274_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
else
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_350_; 
lean_inc(v_snd_279_);
lean_inc(v_fst_278_);
v_isSharedCheck_350_ = !lean_is_exclusive(v___y_274_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_351_ = lean_ctor_get(v___y_274_, 1);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v___y_274_, 0);
lean_dec(v_unused_352_);
v___x_293_ = v___y_274_;
v_isShared_294_ = v_isSharedCheck_350_;
goto v_resetjp_292_;
}
else
{
lean_dec(v___y_274_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_350_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v_it_x27_297_; 
v___x_295_ = lean_string_utf8_next_fast(v_fst_278_, v_snd_279_);
lean_dec(v_snd_279_);
lean_inc(v_fst_278_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_295_);
v_it_x27_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_fst_278_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_295_);
v_it_x27_297_ = v_reuseFailAlloc_349_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
uint8_t v_decide_301_; 
v_decide_301_ = lean_nat_dec_eq(v___x_295_, v___x_280_);
if (v_decide_301_ == 0)
{
if (v___x_283_ == 0)
{
lean_dec(v_fst_278_);
goto v___jp_298_;
}
else
{
uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_string_utf8_get_fast(v_fst_278_, v___x_295_);
v___x_303_ = lean_uint32_dec_eq(v___x_302_, v___x_273_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec_ref(v_it_x27_297_);
v___x_304_ = lean_string_utf8_next_fast(v_fst_278_, v___x_295_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_fst_278_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_307_ = lean_string_push(v___x_306_, v___x_302_);
v___x_308_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(v___x_307_, v___x_305_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_pos_309_; lean_object* v_res_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_346_; 
v_pos_309_ = lean_ctor_get(v___x_308_, 0);
v_res_310_ = lean_ctor_get(v___x_308_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_346_ == 0)
{
v___x_312_ = v___x_308_;
v_isShared_313_ = v_isSharedCheck_346_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_res_310_);
lean_inc(v_pos_309_);
lean_dec(v___x_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_346_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_fst_314_; lean_object* v_snd_315_; lean_object* v___x_316_; uint8_t v_decide_317_; 
v_fst_314_ = lean_ctor_get(v_pos_309_, 0);
v_snd_315_ = lean_ctor_get(v_pos_309_, 1);
v___x_316_ = lean_string_utf8_byte_size(v_fst_314_);
v_decide_317_ = lean_nat_dec_eq(v_snd_315_, v___x_316_);
if (v_decide_317_ == 0)
{
uint32_t v_c_318_; uint8_t v___x_319_; 
v_c_318_ = lean_string_utf8_get_fast(v_fst_314_, v_snd_315_);
v___x_319_ = lean_uint32_dec_eq(v_c_318_, v___x_273_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
lean_dec(v_res_310_);
v___x_320_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_321_ = lean_string_push(v___x_306_, v___x_273_);
v___x_322_ = lean_string_append(v___x_320_, v___x_321_);
lean_dec_ref(v___x_321_);
v___x_323_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_324_ = lean_string_append(v___x_322_, v___x_323_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 1);
lean_ctor_set(v___x_312_, 1, v___x_325_);
v___x_327_ = v___x_312_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_pos_309_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
else
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_339_; 
lean_inc(v_snd_315_);
lean_inc(v_fst_314_);
v_isSharedCheck_339_ = !lean_is_exclusive(v_pos_309_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; lean_object* v_unused_341_; 
v_unused_340_ = lean_ctor_get(v_pos_309_, 1);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v_pos_309_, 0);
lean_dec(v_unused_341_);
v___x_330_ = v_pos_309_;
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_pos_309_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v_it_x27_334_; 
v___x_332_ = lean_string_utf8_next_fast(v_fst_314_, v_snd_315_);
lean_dec(v_snd_315_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v___x_332_);
v_it_x27_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_fst_314_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_332_);
v_it_x27_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v_it_x27_334_);
v___x_336_ = v___x_312_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_it_x27_334_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_res_310_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_344_; 
lean_dec(v_res_310_);
v___x_342_ = lean_box(0);
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 1);
lean_ctor_set(v___x_312_, 1, v___x_342_);
v___x_344_ = v___x_312_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_pos_309_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
return v___x_308_;
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_fst_278_);
v___x_347_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v_it_x27_297_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
return v___x_348_;
}
}
}
else
{
lean_dec(v_fst_278_);
goto v___jp_298_;
}
v___jp_298_:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_box(0);
v___x_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_300_, 0, v_it_x27_297_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
return v___x_300_;
}
}
}
}
}
}
else
{
goto v___jp_275_;
}
v___jp_275_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v___y_274_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object* v_decide_353_, lean_object* v___x_354_, lean_object* v___y_355_){
_start:
{
uint8_t v_decide_11288__boxed_356_; uint32_t v___x_11289__boxed_357_; lean_object* v_res_358_; 
v_decide_11288__boxed_356_ = lean_unbox(v_decide_353_);
v___x_11289__boxed_357_ = lean_unbox_uint32(v___x_354_);
lean_dec(v___x_354_);
v_res_358_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(v_decide_11288__boxed_356_, v___x_11289__boxed_357_, v___y_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(lean_object* v_acc_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_fst_361_; lean_object* v_snd_362_; lean_object* v_pos_364_; lean_object* v_snd_365_; lean_object* v_err_366_; lean_object* v___x_370_; uint8_t v_decide_371_; 
v_fst_361_ = lean_ctor_get(v_a_360_, 0);
v_snd_362_ = lean_ctor_get(v_a_360_, 1);
lean_inc(v_snd_362_);
v___x_370_ = lean_string_utf8_byte_size(v_fst_361_);
v_decide_371_ = lean_nat_dec_eq(v_snd_362_, v___x_370_);
if (v_decide_371_ == 0)
{
uint32_t v___x_372_; uint32_t v_c_373_; uint8_t v___x_374_; 
v___x_372_ = 39;
v_c_373_ = lean_string_utf8_get_fast(v_fst_361_, v_snd_362_);
v___x_374_ = lean_uint32_dec_eq(v_c_373_, v___x_372_);
if (v___x_374_ == 0)
{
lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_384_; 
lean_inc(v_fst_361_);
v_isSharedCheck_384_ = !lean_is_exclusive(v_a_360_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; lean_object* v_unused_386_; 
v_unused_385_ = lean_ctor_get(v_a_360_, 1);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_a_360_, 0);
lean_dec(v_unused_386_);
v___x_376_ = v_a_360_;
v_isShared_377_ = v_isSharedCheck_384_;
goto v_resetjp_375_;
}
else
{
lean_dec(v_a_360_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_384_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v_it_x27_380_; 
v___x_378_ = lean_string_utf8_next_fast(v_fst_361_, v_snd_362_);
lean_dec(v_snd_362_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 1, v___x_378_);
v_it_x27_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_fst_361_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_378_);
v_it_x27_380_ = v_reuseFailAlloc_383_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; 
v___x_381_ = lean_string_push(v_acc_359_, v_c_373_);
v_acc_359_ = v___x_381_;
v_a_360_ = v_it_x27_380_;
goto _start;
}
}
}
else
{
lean_object* v___x_387_; 
v___x_387_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_362_);
v_pos_364_ = v_a_360_;
v_snd_365_ = v_snd_362_;
v_err_366_ = v___x_387_;
goto v___jp_363_;
}
}
else
{
lean_object* v___x_388_; 
v___x_388_ = lean_box(0);
lean_inc(v_snd_362_);
v_pos_364_ = v_a_360_;
v_snd_365_ = v_snd_362_;
v_err_366_ = v___x_388_;
goto v___jp_363_;
}
v___jp_363_:
{
uint8_t v_decide_367_; 
v_decide_367_ = lean_nat_dec_eq(v_snd_362_, v_snd_365_);
lean_dec(v_snd_365_);
lean_dec(v_snd_362_);
if (v_decide_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec_ref(v_acc_359_);
lean_inc(v_err_366_);
v___x_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_368_, 0, v_pos_364_);
lean_ctor_set(v___x_368_, 1, v_err_366_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_pos_364_);
lean_ctor_set(v___x_369_, 1, v_acc_359_);
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(lean_object* v_acc_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v_pos_394_; lean_object* v_snd_395_; lean_object* v_err_396_; lean_object* v___x_400_; uint8_t v_decide_401_; 
v_fst_391_ = lean_ctor_get(v_a_390_, 0);
v_snd_392_ = lean_ctor_get(v_a_390_, 1);
lean_inc(v_snd_392_);
v___x_400_ = lean_string_utf8_byte_size(v_fst_391_);
v_decide_401_ = lean_nat_dec_eq(v_snd_392_, v___x_400_);
if (v_decide_401_ == 0)
{
uint32_t v___x_402_; uint32_t v_c_403_; uint8_t v___x_404_; 
v___x_402_ = 39;
v_c_403_ = lean_string_utf8_get_fast(v_fst_391_, v_snd_392_);
v___x_404_ = lean_uint32_dec_eq(v_c_403_, v___x_402_);
if (v___x_404_ == 0)
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_414_; 
lean_inc(v_fst_391_);
v_isSharedCheck_414_ = !lean_is_exclusive(v_a_390_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; lean_object* v_unused_416_; 
v_unused_415_ = lean_ctor_get(v_a_390_, 1);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_a_390_, 0);
lean_dec(v_unused_416_);
v___x_406_ = v_a_390_;
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
else
{
lean_dec(v_a_390_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v_it_x27_410_; 
v___x_408_ = lean_string_utf8_next_fast(v_fst_391_, v_snd_392_);
lean_dec(v_snd_392_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v___x_408_);
v_it_x27_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_fst_391_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_408_);
v_it_x27_410_ = v_reuseFailAlloc_413_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_string_push(v_acc_389_, v_c_403_);
v___x_412_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(v___x_411_, v_it_x27_410_);
return v___x_412_;
}
}
}
else
{
lean_object* v___x_417_; 
v___x_417_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_392_);
v_pos_394_ = v_a_390_;
v_snd_395_ = v_snd_392_;
v_err_396_ = v___x_417_;
goto v___jp_393_;
}
}
else
{
lean_object* v___x_418_; 
v___x_418_ = lean_box(0);
lean_inc(v_snd_392_);
v_pos_394_ = v_a_390_;
v_snd_395_ = v_snd_392_;
v_err_396_ = v___x_418_;
goto v___jp_393_;
}
v___jp_393_:
{
uint8_t v_decide_397_; 
v_decide_397_ = lean_nat_dec_eq(v_snd_392_, v_snd_395_);
lean_dec(v_snd_395_);
lean_dec(v_snd_392_);
if (v_decide_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec_ref(v_acc_389_);
lean_inc(v_err_396_);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v_pos_394_);
lean_ctor_set(v___x_398_, 1, v_err_396_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_pos_394_);
lean_ctor_set(v___x_399_, 1, v_acc_389_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(uint8_t v_decide_419_, uint32_t v___x_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_fst_425_; lean_object* v_snd_426_; lean_object* v___x_427_; uint8_t v_decide_428_; 
v_fst_425_ = lean_ctor_get(v___y_421_, 0);
v_snd_426_ = lean_ctor_get(v___y_421_, 1);
v___x_427_ = lean_string_utf8_byte_size(v_fst_425_);
v_decide_428_ = lean_nat_dec_eq(v_snd_426_, v___x_427_);
if (v_decide_428_ == 0)
{
if (v_decide_419_ == 0)
{
goto v___jp_422_;
}
else
{
uint32_t v_c_429_; uint8_t v___x_430_; 
v_c_429_ = lean_string_utf8_get_fast(v_fst_425_, v_snd_426_);
v___x_430_ = lean_uint32_dec_eq(v_c_429_, v___x_420_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_431_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_432_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_433_ = lean_string_push(v___x_432_, v___x_420_);
v___x_434_ = lean_string_append(v___x_431_, v___x_433_);
lean_dec_ref(v___x_433_);
v___x_435_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_436_ = lean_string_append(v___x_434_, v___x_435_);
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
v___x_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_438_, 0, v___y_421_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
return v___x_438_;
}
else
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_497_; 
lean_inc(v_snd_426_);
lean_inc(v_fst_425_);
v_isSharedCheck_497_ = !lean_is_exclusive(v___y_421_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_498_ = lean_ctor_get(v___y_421_, 1);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v___y_421_, 0);
lean_dec(v_unused_499_);
v___x_440_ = v___y_421_;
v_isShared_441_ = v_isSharedCheck_497_;
goto v_resetjp_439_;
}
else
{
lean_dec(v___y_421_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_497_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v_it_x27_444_; 
v___x_442_ = lean_string_utf8_next_fast(v_fst_425_, v_snd_426_);
lean_dec(v_snd_426_);
lean_inc(v_fst_425_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_442_);
v_it_x27_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_fst_425_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_442_);
v_it_x27_444_ = v_reuseFailAlloc_496_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
uint8_t v_decide_448_; 
v_decide_448_ = lean_nat_dec_eq(v___x_442_, v___x_427_);
if (v_decide_448_ == 0)
{
if (v___x_430_ == 0)
{
lean_dec(v_fst_425_);
goto v___jp_445_;
}
else
{
uint32_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_string_utf8_get_fast(v_fst_425_, v___x_442_);
v___x_450_ = lean_uint32_dec_eq(v___x_449_, v___x_420_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec_ref(v_it_x27_444_);
v___x_451_ = lean_string_utf8_next_fast(v_fst_425_, v___x_442_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v_fst_425_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_454_ = lean_string_push(v___x_453_, v___x_449_);
v___x_455_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(v___x_454_, v___x_452_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_pos_456_; lean_object* v_res_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_493_; 
v_pos_456_ = lean_ctor_get(v___x_455_, 0);
v_res_457_ = lean_ctor_get(v___x_455_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_493_ == 0)
{
v___x_459_ = v___x_455_;
v_isShared_460_ = v_isSharedCheck_493_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_res_457_);
lean_inc(v_pos_456_);
lean_dec(v___x_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_493_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_463_; uint8_t v_decide_464_; 
v_fst_461_ = lean_ctor_get(v_pos_456_, 0);
v_snd_462_ = lean_ctor_get(v_pos_456_, 1);
v___x_463_ = lean_string_utf8_byte_size(v_fst_461_);
v_decide_464_ = lean_nat_dec_eq(v_snd_462_, v___x_463_);
if (v_decide_464_ == 0)
{
uint32_t v_c_465_; uint8_t v___x_466_; 
v_c_465_ = lean_string_utf8_get_fast(v_fst_461_, v_snd_462_);
v___x_466_ = lean_uint32_dec_eq(v_c_465_, v___x_420_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec(v_res_457_);
v___x_467_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_468_ = lean_string_push(v___x_453_, v___x_420_);
v___x_469_ = lean_string_append(v___x_467_, v___x_468_);
lean_dec_ref(v___x_468_);
v___x_470_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_471_ = lean_string_append(v___x_469_, v___x_470_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 1);
lean_ctor_set(v___x_459_, 1, v___x_472_);
v___x_474_ = v___x_459_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_pos_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
else
{
lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_486_; 
lean_inc(v_snd_462_);
lean_inc(v_fst_461_);
v_isSharedCheck_486_ = !lean_is_exclusive(v_pos_456_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; lean_object* v_unused_488_; 
v_unused_487_ = lean_ctor_get(v_pos_456_, 1);
lean_dec(v_unused_487_);
v_unused_488_ = lean_ctor_get(v_pos_456_, 0);
lean_dec(v_unused_488_);
v___x_477_ = v_pos_456_;
v_isShared_478_ = v_isSharedCheck_486_;
goto v_resetjp_476_;
}
else
{
lean_dec(v_pos_456_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_486_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v_it_x27_481_; 
v___x_479_ = lean_string_utf8_next_fast(v_fst_461_, v_snd_462_);
lean_dec(v_snd_462_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v___x_479_);
v_it_x27_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_fst_461_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_479_);
v_it_x27_481_ = v_reuseFailAlloc_485_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_483_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v_it_x27_481_);
v___x_483_ = v___x_459_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_it_x27_481_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_res_457_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
else
{
lean_object* v___x_489_; lean_object* v___x_491_; 
lean_dec(v_res_457_);
v___x_489_ = lean_box(0);
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 1);
lean_ctor_set(v___x_459_, 1, v___x_489_);
v___x_491_ = v___x_459_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_pos_456_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
return v___x_455_;
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v_fst_425_);
v___x_494_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v_it_x27_444_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
return v___x_495_;
}
}
}
else
{
lean_dec(v_fst_425_);
goto v___jp_445_;
}
v___jp_445_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_box(0);
v___x_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_447_, 0, v_it_x27_444_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
return v___x_447_;
}
}
}
}
}
}
else
{
goto v___jp_422_;
}
v___jp_422_:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_box(0);
v___x_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_424_, 0, v___y_421_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object* v_decide_500_, lean_object* v___x_501_, lean_object* v___y_502_){
_start:
{
uint8_t v_decide_11555__boxed_503_; uint32_t v___x_11556__boxed_504_; lean_object* v_res_505_; 
v_decide_11555__boxed_503_ = lean_unbox(v_decide_500_);
v___x_11556__boxed_504_ = lean_unbox_uint32(v___x_501_);
lean_dec(v___x_501_);
v_res_505_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(v_decide_11555__boxed_503_, v___x_11556__boxed_504_, v___y_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object* v_acc_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_fst_508_; lean_object* v_snd_509_; lean_object* v_pos_511_; lean_object* v_snd_512_; lean_object* v_err_513_; lean_object* v___x_519_; uint8_t v_decide_520_; 
v_fst_508_ = lean_ctor_get(v_a_507_, 0);
v_snd_509_ = lean_ctor_get(v_a_507_, 1);
lean_inc(v_snd_509_);
v___x_519_ = lean_string_utf8_byte_size(v_fst_508_);
v_decide_520_ = lean_nat_dec_eq(v_snd_509_, v___x_519_);
if (v_decide_520_ == 0)
{
uint32_t v___x_521_; uint32_t v___x_522_; uint8_t v___x_523_; uint32_t v_c_524_; lean_object* v___x_525_; lean_object* v_it_x27_526_; uint8_t v___y_528_; uint8_t v___y_529_; uint8_t v___y_533_; uint8_t v___y_534_; uint8_t v___y_535_; uint8_t v___y_537_; uint8_t v___y_538_; uint8_t v___y_541_; uint8_t v___y_544_; uint8_t v___y_546_; uint32_t v___x_551_; uint8_t v___x_552_; 
v___x_521_ = 39;
v___x_522_ = 34;
v___x_523_ = 1;
v_c_524_ = lean_string_utf8_get_fast(v_fst_508_, v_snd_509_);
v___x_525_ = lean_string_utf8_next_fast(v_fst_508_, v_snd_509_);
lean_inc(v_fst_508_);
v_it_x27_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_526_, 0, v_fst_508_);
lean_ctor_set(v_it_x27_526_, 1, v___x_525_);
v___x_551_ = 65;
v___x_552_ = lean_uint32_dec_le(v___x_551_, v_c_524_);
if (v___x_552_ == 0)
{
v___y_546_ = v___x_552_;
goto v___jp_545_;
}
else
{
uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 90;
v___x_554_ = lean_uint32_dec_le(v_c_524_, v___x_553_);
v___y_546_ = v___x_554_;
goto v___jp_545_;
}
v___jp_527_:
{
if (v___y_528_ == 0)
{
lean_dec_ref_known(v_it_x27_526_, 2);
goto v___jp_517_;
}
else
{
if (v___y_529_ == 0)
{
lean_dec_ref_known(v_it_x27_526_, 2);
goto v___jp_517_;
}
else
{
lean_object* v___x_530_; 
lean_dec(v_snd_509_);
lean_dec_ref(v_a_507_);
v___x_530_ = lean_string_push(v_acc_506_, v_c_524_);
v_acc_506_ = v___x_530_;
v_a_507_ = v_it_x27_526_;
goto _start;
}
}
}
v___jp_532_:
{
if (v___y_534_ == 0)
{
v___y_528_ = v___y_533_;
v___y_529_ = v___y_534_;
goto v___jp_527_;
}
else
{
v___y_528_ = v___y_533_;
v___y_529_ = v___y_535_;
goto v___jp_527_;
}
}
v___jp_536_:
{
uint8_t v___x_539_; 
v___x_539_ = lean_uint32_dec_eq(v_c_524_, v___x_522_);
if (v___x_539_ == 0)
{
v___y_533_ = v___y_537_;
v___y_534_ = v___y_538_;
v___y_535_ = v___x_523_;
goto v___jp_532_;
}
else
{
v___y_533_ = v___y_537_;
v___y_534_ = v___y_538_;
v___y_535_ = v_decide_520_;
goto v___jp_532_;
}
}
v___jp_540_:
{
uint8_t v___x_542_; 
v___x_542_ = lean_uint32_dec_eq(v_c_524_, v___x_521_);
if (v___x_542_ == 0)
{
v___y_537_ = v___y_541_;
v___y_538_ = v___x_523_;
goto v___jp_536_;
}
else
{
v___y_537_ = v___y_541_;
v___y_538_ = v_decide_520_;
goto v___jp_536_;
}
}
v___jp_543_:
{
if (v___y_544_ == 0)
{
v___y_541_ = v___x_523_;
goto v___jp_540_;
}
else
{
v___y_541_ = v_decide_520_;
goto v___jp_540_;
}
}
v___jp_545_:
{
if (v___y_546_ == 0)
{
uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 97;
v___x_548_ = lean_uint32_dec_le(v___x_547_, v_c_524_);
if (v___x_548_ == 0)
{
v___y_544_ = v___x_548_;
goto v___jp_543_;
}
else
{
uint32_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 122;
v___x_550_ = lean_uint32_dec_le(v_c_524_, v___x_549_);
v___y_544_ = v___x_550_;
goto v___jp_543_;
}
}
else
{
v___y_541_ = v_decide_520_;
goto v___jp_540_;
}
}
}
else
{
lean_object* v___x_555_; 
v___x_555_ = lean_box(0);
lean_inc(v_snd_509_);
v_pos_511_ = v_a_507_;
v_snd_512_ = v_snd_509_;
v_err_513_ = v___x_555_;
goto v___jp_510_;
}
v___jp_510_:
{
uint8_t v_decide_514_; 
v_decide_514_ = lean_nat_dec_eq(v_snd_509_, v_snd_512_);
lean_dec(v_snd_512_);
lean_dec(v_snd_509_);
if (v_decide_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec_ref(v_acc_506_);
lean_inc(v_err_513_);
v___x_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_515_, 0, v_pos_511_);
lean_ctor_set(v___x_515_, 1, v_err_513_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v_pos_511_);
lean_ctor_set(v___x_516_, 1, v_acc_506_);
return v___x_516_;
}
}
v___jp_517_:
{
lean_object* v___x_518_; 
v___x_518_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_509_);
v_pos_511_ = v_a_507_;
v_snd_512_ = v_snd_509_;
v_err_513_ = v___x_518_;
goto v___jp_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint8_t v_decide_556_, uint32_t v___x_557_, uint32_t v___x_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v___x_568_; uint8_t v_decide_569_; 
v_fst_566_ = lean_ctor_get(v___y_559_, 0);
v_snd_567_ = lean_ctor_get(v___y_559_, 1);
v___x_568_ = lean_string_utf8_byte_size(v_fst_566_);
v_decide_569_ = lean_nat_dec_eq(v_snd_567_, v___x_568_);
if (v_decide_569_ == 0)
{
if (v_decide_556_ == 0)
{
goto v___jp_563_;
}
else
{
uint32_t v_c_570_; lean_object* v___x_571_; lean_object* v_it_x27_572_; uint8_t v___y_574_; uint8_t v___y_575_; uint8_t v___y_580_; uint8_t v___y_581_; uint8_t v___y_582_; uint8_t v___y_584_; uint8_t v___y_585_; uint8_t v___y_588_; uint8_t v___y_591_; uint8_t v___y_593_; uint32_t v___x_598_; uint8_t v___x_599_; 
v_c_570_ = lean_string_utf8_get_fast(v_fst_566_, v_snd_567_);
v___x_571_ = lean_string_utf8_next_fast(v_fst_566_, v_snd_567_);
lean_inc(v_fst_566_);
v_it_x27_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_572_, 0, v_fst_566_);
lean_ctor_set(v_it_x27_572_, 1, v___x_571_);
v___x_598_ = 65;
v___x_599_ = lean_uint32_dec_le(v___x_598_, v_c_570_);
if (v___x_599_ == 0)
{
v___y_593_ = v___x_599_;
goto v___jp_592_;
}
else
{
uint32_t v___x_600_; uint8_t v___x_601_; 
v___x_600_ = 90;
v___x_601_ = lean_uint32_dec_le(v_c_570_, v___x_600_);
v___y_593_ = v___x_601_;
goto v___jp_592_;
}
v___jp_573_:
{
if (v___y_574_ == 0)
{
lean_dec_ref_known(v_it_x27_572_, 2);
goto v___jp_560_;
}
else
{
if (v___y_575_ == 0)
{
lean_dec_ref_known(v_it_x27_572_, 2);
goto v___jp_560_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec_ref(v___y_559_);
v___x_576_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_577_ = lean_string_push(v___x_576_, v_c_570_);
v___x_578_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(v___x_577_, v_it_x27_572_);
return v___x_578_;
}
}
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
v___y_574_ = v___y_581_;
v___y_575_ = v___y_580_;
goto v___jp_573_;
}
else
{
v___y_574_ = v___y_581_;
v___y_575_ = v___y_582_;
goto v___jp_573_;
}
}
v___jp_583_:
{
uint8_t v___x_586_; 
v___x_586_ = lean_uint32_dec_eq(v_c_570_, v___x_557_);
if (v___x_586_ == 0)
{
v___y_580_ = v___y_585_;
v___y_581_ = v___y_584_;
v___y_582_ = v_decide_556_;
goto v___jp_579_;
}
else
{
v___y_580_ = v___y_585_;
v___y_581_ = v___y_584_;
v___y_582_ = v_decide_569_;
goto v___jp_579_;
}
}
v___jp_587_:
{
uint8_t v___x_589_; 
v___x_589_ = lean_uint32_dec_eq(v_c_570_, v___x_558_);
if (v___x_589_ == 0)
{
v___y_584_ = v___y_588_;
v___y_585_ = v_decide_556_;
goto v___jp_583_;
}
else
{
v___y_584_ = v___y_588_;
v___y_585_ = v_decide_569_;
goto v___jp_583_;
}
}
v___jp_590_:
{
if (v___y_591_ == 0)
{
v___y_588_ = v_decide_556_;
goto v___jp_587_;
}
else
{
v___y_588_ = v_decide_569_;
goto v___jp_587_;
}
}
v___jp_592_:
{
if (v___y_593_ == 0)
{
uint32_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 97;
v___x_595_ = lean_uint32_dec_le(v___x_594_, v_c_570_);
if (v___x_595_ == 0)
{
v___y_591_ = v___x_595_;
goto v___jp_590_;
}
else
{
uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 122;
v___x_597_ = lean_uint32_dec_le(v_c_570_, v___x_596_);
v___y_591_ = v___x_597_;
goto v___jp_590_;
}
}
else
{
v___y_588_ = v_decide_569_;
goto v___jp_587_;
}
}
}
}
else
{
goto v___jp_563_;
}
v___jp_560_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_562_, 0, v___y_559_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
return v___x_562_;
}
v___jp_563_:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_box(0);
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v___y_559_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object* v_decide_602_, lean_object* v___x_603_, lean_object* v___x_604_, lean_object* v___y_605_){
_start:
{
uint8_t v_decide_11803__boxed_606_; uint32_t v___x_11804__boxed_607_; uint32_t v___x_11805__boxed_608_; lean_object* v_res_609_; 
v_decide_11803__boxed_606_ = lean_unbox(v_decide_602_);
v___x_11804__boxed_607_ = lean_unbox_uint32(v___x_603_);
lean_dec(v___x_603_);
v___x_11805__boxed_608_ = lean_unbox_uint32(v___x_604_);
lean_dec(v___x_604_);
v_res_609_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(v_decide_11803__boxed_606_, v___x_11804__boxed_607_, v___x_11805__boxed_608_, v___y_605_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t v___y_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_612_ = lean_string_push(v___x_611_, v___y_610_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object* v___y_614_){
_start:
{
uint32_t v___y_11893__boxed_615_; lean_object* v_res_616_; 
v___y_11893__boxed_615_ = lean_unbox_uint32(v___y_614_);
lean_dec(v___y_614_);
v_res_616_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(v___y_11893__boxed_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(uint8_t v___x_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_fst_622_; lean_object* v_snd_623_; lean_object* v___x_624_; uint8_t v_decide_625_; 
v_fst_622_ = lean_ctor_get(v___y_618_, 0);
v_snd_623_ = lean_ctor_get(v___y_618_, 1);
v___x_624_ = lean_string_utf8_byte_size(v_fst_622_);
v_decide_625_ = lean_nat_dec_eq(v_snd_623_, v___x_624_);
if (v_decide_625_ == 0)
{
if (v___x_617_ == 0)
{
goto v___jp_619_;
}
else
{
lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_636_; 
lean_inc(v_snd_623_);
lean_inc(v_fst_622_);
v_isSharedCheck_636_ = !lean_is_exclusive(v___y_618_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; lean_object* v_unused_638_; 
v_unused_637_ = lean_ctor_get(v___y_618_, 1);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v___y_618_, 0);
lean_dec(v_unused_638_);
v___x_627_ = v___y_618_;
v_isShared_628_ = v_isSharedCheck_636_;
goto v_resetjp_626_;
}
else
{
lean_dec(v___y_618_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_636_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
uint32_t v_c_629_; lean_object* v___x_630_; lean_object* v_it_x27_632_; 
v_c_629_ = lean_string_utf8_get_fast(v_fst_622_, v_snd_623_);
v___x_630_ = lean_string_utf8_next_fast(v_fst_622_, v_snd_623_);
lean_dec(v_snd_623_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_630_);
v_it_x27_632_ = v___x_627_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_fst_622_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_630_);
v_it_x27_632_ = v_reuseFailAlloc_635_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_box_uint32(v_c_629_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_it_x27_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
return v___x_634_;
}
}
}
}
else
{
goto v___jp_619_;
}
v___jp_619_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_box(0);
v___x_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_621_, 0, v___y_618_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed(lean_object* v___x_639_, lean_object* v___y_640_){
_start:
{
uint8_t v___x_11902__boxed_641_; lean_object* v_res_642_; 
v___x_11902__boxed_641_ = lean_unbox(v___x_639_);
v_res_642_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(v___x_11902__boxed_641_, v___y_640_);
return v_res_642_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0(void){
_start:
{
uint32_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = 92;
v___x_644_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_645_ = lean_string_push(v___x_644_, v___x_643_);
return v___x_645_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0);
v___x_647_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_648_ = lean_string_append(v___x_647_, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_650_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1);
v___x_651_ = lean_string_append(v___x_650_, v___x_649_);
return v___x_651_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2);
v___x_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1(void){
_start:
{
uint32_t v___x_655_; lean_object* v___x_656_; 
v___x_655_ = 34;
v___x_656_ = lean_box_uint32(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2(void){
_start:
{
uint32_t v___x_657_; lean_object* v___x_658_; 
v___x_657_ = 39;
v___x_658_ = lean_box_uint32(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(lean_object* v_a_659_){
_start:
{
lean_object* v___x_660_; 
lean_inc_ref(v_a_659_);
v___x_660_ = l_Std_Time_parseModifier(v_a_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_pos_661_; lean_object* v_res_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v_a_659_);
v_pos_661_ = lean_ctor_get(v___x_660_, 0);
v_res_662_ = lean_ctor_get(v___x_660_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_670_ == 0)
{
v___x_664_ = v___x_660_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_res_662_);
lean_inc(v_pos_661_);
lean_dec(v___x_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_666_, 0, v_res_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_pos_661_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v_pos_671_; lean_object* v_err_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_743_; 
v_pos_671_ = lean_ctor_get(v___x_660_, 0);
v_err_672_ = lean_ctor_get(v___x_660_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_743_ == 0)
{
v___x_674_ = v___x_660_;
v_isShared_675_ = v_isSharedCheck_743_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_err_672_);
lean_inc(v_pos_671_);
lean_dec(v___x_660_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_743_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_snd_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_741_; 
v_snd_676_ = lean_ctor_get(v_a_659_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_a_659_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_a_659_, 0);
lean_dec(v_unused_742_);
v___x_678_ = v_a_659_;
v_isShared_679_ = v_isSharedCheck_741_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snd_676_);
lean_dec(v_a_659_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_741_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_fst_680_; lean_object* v_snd_681_; uint8_t v_decide_682_; 
v_fst_680_ = lean_ctor_get(v_pos_671_, 0);
v_snd_681_ = lean_ctor_get(v_pos_671_, 1);
v_decide_682_ = lean_nat_dec_eq(v_snd_676_, v_snd_681_);
lean_dec(v_snd_676_);
if (v_decide_682_ == 0)
{
lean_object* v___x_684_; 
lean_del_object(v___x_678_);
if (v_isShared_675_ == 0)
{
v___x_684_ = v___x_674_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_pos_671_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_err_672_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
else
{
lean_object* v___f_686_; lean_object* v___y_688_; lean_object* v_pos_689_; lean_object* v_snd_690_; lean_object* v___x_716_; uint8_t v_decide_717_; 
lean_inc(v_snd_681_);
lean_dec(v_err_672_);
v___f_686_ = ((lean_object*)(l_Std_Time_instCoeStringFormatPart___closed__0));
v___x_716_ = lean_string_utf8_byte_size(v_fst_680_);
v_decide_717_ = lean_nat_dec_eq(v_snd_681_, v___x_716_);
if (v_decide_717_ == 0)
{
if (v_decide_682_ == 0)
{
lean_del_object(v___x_678_);
goto v___jp_711_;
}
else
{
uint32_t v___x_718_; uint32_t v_c_719_; uint8_t v___x_720_; 
lean_del_object(v___x_674_);
v___x_718_ = 92;
v_c_719_ = lean_string_utf8_get_fast(v_fst_680_, v_snd_681_);
v___x_720_ = lean_uint32_dec_eq(v_c_719_, v___x_718_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3);
lean_inc(v_pos_671_);
if (v_isShared_679_ == 0)
{
lean_ctor_set_tag(v___x_678_, 1);
lean_ctor_set(v___x_678_, 1, v___x_721_);
lean_ctor_set(v___x_678_, 0, v_pos_671_);
v___x_723_ = v___x_678_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_pos_671_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_inc(v_snd_681_);
v___y_688_ = v___x_723_;
v_pos_689_ = v_pos_671_;
v_snd_690_ = v_snd_681_;
goto v___jp_687_;
}
}
else
{
lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_738_; 
lean_inc(v_fst_680_);
lean_del_object(v___x_678_);
v_isSharedCheck_738_ = !lean_is_exclusive(v_pos_671_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; lean_object* v_unused_740_; 
v_unused_739_ = lean_ctor_get(v_pos_671_, 1);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_pos_671_, 0);
lean_dec(v_unused_740_);
v___x_726_ = v_pos_671_;
v_isShared_727_ = v_isSharedCheck_738_;
goto v_resetjp_725_;
}
else
{
lean_dec(v_pos_671_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_738_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___f_730_; lean_object* v___x_731_; lean_object* v_it_x27_733_; 
v___f_728_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4));
v___x_729_ = lean_box(v___x_720_);
v___f_730_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed), 2, 1);
lean_closure_set(v___f_730_, 0, v___x_729_);
v___x_731_ = lean_string_utf8_next_fast(v_fst_680_, v_snd_681_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_731_);
v_it_x27_733_ = v___x_726_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_fst_680_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_731_);
v_it_x27_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_730_, v___f_728_, v_it_x27_733_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_dec(v_snd_681_);
return v___x_734_;
}
else
{
lean_object* v_pos_735_; lean_object* v_snd_736_; 
v_pos_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_pos_735_);
v_snd_736_ = lean_ctor_get(v_pos_735_, 1);
lean_inc(v_snd_736_);
v___y_688_ = v___x_734_;
v_pos_689_ = v_pos_735_;
v_snd_690_ = v_snd_736_;
goto v___jp_687_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_678_);
goto v___jp_711_;
}
v___jp_687_:
{
uint8_t v_decide_691_; 
v_decide_691_ = lean_nat_dec_eq(v_snd_681_, v_snd_690_);
lean_dec(v_snd_681_);
if (v_decide_691_ == 0)
{
lean_dec(v_snd_690_);
lean_dec_ref(v_pos_689_);
return v___y_688_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___f_694_; lean_object* v___x_695_; 
lean_dec_ref(v___y_688_);
v___x_692_ = lean_box(v_decide_691_);
v___x_693_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___f_694_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed), 3, 2);
lean_closure_set(v___f_694_, 0, v___x_692_);
lean_closure_set(v___f_694_, 1, v___x_693_);
v___x_695_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_694_, v___f_686_, v_pos_689_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_dec(v_snd_690_);
return v___x_695_;
}
else
{
lean_object* v_pos_696_; lean_object* v_snd_697_; uint8_t v_decide_698_; 
v_pos_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_pos_696_);
v_snd_697_ = lean_ctor_get(v_pos_696_, 1);
lean_inc(v_snd_697_);
v_decide_698_ = lean_nat_dec_eq(v_snd_690_, v_snd_697_);
lean_dec(v_snd_690_);
if (v_decide_698_ == 0)
{
lean_dec(v_snd_697_);
lean_dec(v_pos_696_);
return v___x_695_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___f_701_; lean_object* v___x_702_; 
lean_dec_ref_known(v___x_695_, 2);
v___x_699_ = lean_box(v_decide_698_);
v___x_700_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_701_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed), 3, 2);
lean_closure_set(v___f_701_, 0, v___x_699_);
lean_closure_set(v___f_701_, 1, v___x_700_);
v___x_702_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_701_, v___f_686_, v_pos_696_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_dec(v_snd_697_);
return v___x_702_;
}
else
{
lean_object* v_pos_703_; lean_object* v_snd_704_; uint8_t v_decide_705_; 
v_pos_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_pos_703_);
v_snd_704_ = lean_ctor_get(v_pos_703_, 1);
v_decide_705_ = lean_nat_dec_eq(v_snd_697_, v_snd_704_);
lean_dec(v_snd_697_);
if (v_decide_705_ == 0)
{
lean_dec(v_pos_703_);
return v___x_702_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___f_709_; lean_object* v___x_710_; 
lean_dec_ref_known(v___x_702_, 2);
v___x_706_ = lean_box(v_decide_705_);
v___x_707_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___x_708_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_709_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed), 4, 3);
lean_closure_set(v___f_709_, 0, v___x_706_);
lean_closure_set(v___f_709_, 1, v___x_707_);
lean_closure_set(v___f_709_, 2, v___x_708_);
v___x_710_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_709_, v___f_686_, v_pos_703_);
return v___x_710_;
}
}
}
}
}
}
v___jp_711_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_box(0);
lean_inc(v_pos_671_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_712_);
v___x_714_ = v___x_674_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_pos_671_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_inc(v_snd_681_);
v___y_688_ = v___x_714_;
v_pos_689_ = v_pos_671_;
v_snd_690_ = v_snd_681_;
goto v___jp_687_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(lean_object* v_acc_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_746_; 
lean_inc_ref(v_a_745_);
v___x_746_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(v_a_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_pos_747_; lean_object* v_res_748_; lean_object* v___x_749_; 
lean_dec_ref(v_a_745_);
v_pos_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_pos_747_);
v_res_748_ = lean_ctor_get(v___x_746_, 1);
lean_inc(v_res_748_);
lean_dec_ref_known(v___x_746_, 2);
v___x_749_ = lean_array_push(v_acc_744_, v_res_748_);
v_acc_744_ = v___x_749_;
v_a_745_ = v_pos_747_;
goto _start;
}
else
{
lean_object* v_pos_751_; lean_object* v_err_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_765_; 
v_pos_751_ = lean_ctor_get(v___x_746_, 0);
v_err_752_ = lean_ctor_get(v___x_746_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_765_ == 0)
{
v___x_754_ = v___x_746_;
v_isShared_755_ = v_isSharedCheck_765_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_err_752_);
lean_inc(v_pos_751_);
lean_dec(v___x_746_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_765_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_snd_756_; lean_object* v_snd_757_; uint8_t v_decide_758_; 
v_snd_756_ = lean_ctor_get(v_a_745_, 1);
lean_inc(v_snd_756_);
lean_dec_ref(v_a_745_);
v_snd_757_ = lean_ctor_get(v_pos_751_, 1);
v_decide_758_ = lean_nat_dec_eq(v_snd_756_, v_snd_757_);
lean_dec(v_snd_756_);
if (v_decide_758_ == 0)
{
lean_object* v___x_760_; 
lean_dec_ref(v_acc_744_);
if (v_isShared_755_ == 0)
{
v___x_760_ = v___x_754_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_pos_751_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_err_752_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
else
{
lean_object* v___x_763_; 
lean_dec(v_err_752_);
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 0);
lean_ctor_set(v___x_754_, 1, v_acc_744_);
v___x_763_ = v___x_754_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_pos_751_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_acc_744_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser(lean_object* v_a_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0));
v___x_773_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(v___x_772_, v_a_771_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_pos_774_; lean_object* v_res_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_791_; 
v_pos_774_ = lean_ctor_get(v___x_773_, 0);
v_res_775_ = lean_ctor_get(v___x_773_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_791_ == 0)
{
v___x_777_ = v___x_773_;
v_isShared_778_ = v_isSharedCheck_791_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_res_775_);
lean_inc(v_pos_774_);
lean_dec(v___x_773_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_791_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___x_781_; uint8_t v_decide_782_; 
v_fst_779_ = lean_ctor_get(v_pos_774_, 0);
v_snd_780_ = lean_ctor_get(v_pos_774_, 1);
v___x_781_ = lean_string_utf8_byte_size(v_fst_779_);
v_decide_782_ = lean_nat_dec_eq(v_snd_780_, v___x_781_);
if (v_decide_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_785_; 
lean_dec(v_res_775_);
v___x_783_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_778_ == 0)
{
lean_ctor_set_tag(v___x_777_, 1);
lean_ctor_set(v___x_777_, 1, v___x_783_);
v___x_785_ = v___x_777_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_pos_774_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_array_to_list(v_res_775_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_787_);
v___x_789_ = v___x_777_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_pos_774_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_787_);
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
else
{
lean_object* v_pos_792_; lean_object* v_err_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
v_pos_792_ = lean_ctor_get(v___x_773_, 0);
v_err_793_ = lean_ctor_get(v___x_773_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_773_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_err_793_);
lean_inc(v_pos_792_);
lean_dec(v___x_773_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_pos_792_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_err_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParse(lean_object* v_s_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_803_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_802_, v_s_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(uint32_t v_a_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v_zero_807_; uint8_t v_isZero_808_; 
v_zero_807_ = lean_unsigned_to_nat(0u);
v_isZero_808_ = lean_nat_dec_eq(v_x_805_, v_zero_807_);
if (v_isZero_808_ == 1)
{
lean_dec(v_x_805_);
return v_x_806_;
}
else
{
lean_object* v_one_809_; lean_object* v_n_810_; lean_object* v___x_811_; 
v_one_809_ = lean_unsigned_to_nat(1u);
v_n_810_ = lean_nat_sub(v_x_805_, v_one_809_);
lean_dec(v_x_805_);
v___x_811_ = lean_string_push(v_x_806_, v_a_804_);
v_x_805_ = v_n_810_;
v_x_806_ = v___x_811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1___boxed(lean_object* v_a_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
uint32_t v_a_boxed_816_; lean_object* v_res_817_; 
v_a_boxed_816_ = lean_unbox_uint32(v_a_813_);
lean_dec(v_a_813_);
v_res_817_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_boxed_816_, v_x_814_, v_x_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(lean_object* v___x_818_, lean_object* v_s_819_, lean_object* v_a_820_, lean_object* v_b_821_){
_start:
{
uint8_t v_decide_822_; 
v_decide_822_ = lean_nat_dec_eq(v_a_820_, v___x_818_);
if (v_decide_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_string_utf8_next_fast(v_s_819_, v_a_820_);
lean_dec(v_a_820_);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_add(v_b_821_, v___x_824_);
lean_dec(v_b_821_);
v_a_820_ = v___x_823_;
v_b_821_ = v___x_825_;
goto _start;
}
else
{
lean_dec(v_a_820_);
return v_b_821_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg___boxed(lean_object* v___x_827_, lean_object* v_s_828_, lean_object* v_a_829_, lean_object* v_b_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_827_, v_s_828_, v_a_829_, v_b_830_);
lean_dec_ref(v_s_828_);
lean_dec(v___x_827_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(lean_object* v_n_832_, uint32_t v_a_833_, lean_object* v_s_834_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_835_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_string_utf8_byte_size(v_s_834_);
v___x_838_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_837_, v_s_834_, v___x_836_, v___x_836_);
v___x_839_ = lean_nat_sub(v_n_832_, v___x_838_);
lean_dec(v___x_838_);
v___x_840_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_833_, v___x_839_, v___x_835_);
v___x_841_ = lean_string_append(v___x_840_, v_s_834_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii___boxed(lean_object* v_n_842_, lean_object* v_a_843_, lean_object* v_s_844_){
_start:
{
uint32_t v_a_boxed_845_; lean_object* v_res_846_; 
v_a_boxed_845_ = lean_unbox_uint32(v_a_843_);
lean_dec(v_a_843_);
v_res_846_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_n_842_, v_a_boxed_845_, v_s_844_);
lean_dec_ref(v_s_844_);
lean_dec(v_n_842_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(lean_object* v___x_847_, lean_object* v___x_848_, lean_object* v_s_849_, lean_object* v_inst_850_, lean_object* v_R_851_, lean_object* v_a_852_, lean_object* v_b_853_, lean_object* v_c_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_847_, v_s_849_, v_a_852_, v_b_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___boxed(lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v_s_858_, lean_object* v_inst_859_, lean_object* v_R_860_, lean_object* v_a_861_, lean_object* v_b_862_, lean_object* v_c_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(v___x_856_, v___x_857_, v_s_858_, v_inst_859_, v_R_860_, v_a_861_, v_b_862_, v_c_863_);
lean_dec_ref(v_s_858_);
lean_dec_ref(v___x_857_);
lean_dec(v___x_856_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(lean_object* v_n_865_, uint32_t v_a_866_, lean_object* v_s_867_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_868_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_string_utf8_byte_size(v_s_867_);
v___x_871_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_870_, v_s_867_, v___x_869_, v___x_869_);
v___x_872_ = lean_nat_sub(v_n_865_, v___x_871_);
lean_dec(v___x_871_);
v___x_873_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_866_, v___x_872_, v___x_868_);
v___x_874_ = lean_string_append(v_s_867_, v___x_873_);
lean_dec_ref(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii___boxed(lean_object* v_n_875_, lean_object* v_a_876_, lean_object* v_s_877_){
_start:
{
uint32_t v_a_boxed_878_; lean_object* v_res_879_; 
v_a_boxed_878_ = lean_unbox_uint32(v_a_876_);
lean_dec(v_a_876_);
v_res_879_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_n_875_, v_a_boxed_878_, v_s_877_);
lean_dec(v_n_875_);
return v_res_879_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_nat_to_int(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad(lean_object* v_size_883_, lean_object* v_n_884_, uint8_t v_cut_885_){
_start:
{
lean_object* v_fst_887_; lean_object* v_snd_888_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_903_ = lean_int_dec_lt(v_n_884_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
v___x_904_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v_fst_887_ = v___x_904_;
v_snd_888_ = v_n_884_;
goto v___jp_886_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_906_ = lean_int_neg(v_n_884_);
lean_dec(v_n_884_);
v_fst_887_ = v___x_905_;
v_snd_888_ = v___x_906_;
goto v___jp_886_;
}
v___jp_886_:
{
lean_object* v_numStr_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v_numStr_889_ = l_Int_repr(v_snd_888_);
lean_dec(v_snd_888_);
v___x_890_ = lean_string_utf8_byte_size(v_numStr_889_);
v___x_891_ = lean_nat_dec_lt(v_size_883_, v___x_890_);
if (v___x_891_ == 0)
{
uint32_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = 48;
v___x_893_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_size_883_, v___x_892_, v_numStr_889_);
lean_dec_ref(v_numStr_889_);
lean_inc_ref(v_fst_887_);
v___x_894_ = lean_string_append(v_fst_887_, v___x_893_);
lean_dec_ref(v___x_893_);
return v___x_894_;
}
else
{
if (v_cut_885_ == 0)
{
lean_object* v___x_895_; 
lean_inc_ref(v_fst_887_);
v___x_895_ = lean_string_append(v_fst_887_, v_numStr_889_);
lean_dec_ref(v_numStr_889_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_896_ = lean_nat_sub(v___x_890_, v_size_883_);
v___x_897_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_numStr_889_);
v___x_898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_898_, 0, v_numStr_889_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
lean_ctor_set(v___x_898_, 2, v___x_890_);
v___x_899_ = l_String_Slice_Pos_nextn(v___x_898_, v___x_897_, v___x_896_);
lean_dec_ref_known(v___x_898_, 3);
v___x_900_ = lean_string_utf8_extract_fast(v_numStr_889_, v___x_899_, v___x_890_);
lean_dec(v___x_899_);
lean_dec_ref(v_numStr_889_);
lean_inc_ref(v_fst_887_);
v___x_901_ = lean_string_append(v_fst_887_, v___x_900_);
lean_dec_ref(v___x_900_);
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___boxed(lean_object* v_size_907_, lean_object* v_n_908_, lean_object* v_cut_909_){
_start:
{
uint8_t v_cut_boxed_910_; lean_object* v_res_911_; 
v_cut_boxed_910_ = lean_unbox(v_cut_909_);
v_res_911_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_size_907_, v_n_908_, v_cut_boxed_910_);
lean_dec(v_size_907_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(lean_object* v_size_912_, lean_object* v_n_913_, uint8_t v_cut_914_){
_start:
{
lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_932_ = lean_int_dec_lt(v_n_913_, v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
v___x_933_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v_fst_916_ = v___x_933_;
v_snd_917_ = v_n_913_;
goto v___jp_915_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_935_ = lean_int_neg(v_n_913_);
lean_dec(v_n_913_);
v_fst_916_ = v___x_934_;
v_snd_917_ = v___x_935_;
goto v___jp_915_;
}
v___jp_915_:
{
lean_object* v_numStr_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_numStr_918_ = l_Int_repr(v_snd_917_);
lean_dec(v_snd_917_);
v___x_919_ = lean_string_length(v_numStr_918_);
v___x_920_ = lean_nat_dec_lt(v_size_912_, v___x_919_);
if (v___x_920_ == 0)
{
uint32_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = 48;
v___x_922_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_size_912_, v___x_921_, v_numStr_918_);
lean_dec(v_size_912_);
lean_inc_ref(v_fst_916_);
v___x_923_ = lean_string_append(v_fst_916_, v___x_922_);
lean_dec_ref(v___x_922_);
return v___x_923_;
}
else
{
if (v_cut_914_ == 0)
{
lean_object* v___x_924_; 
lean_dec(v_size_912_);
lean_inc_ref(v_fst_916_);
v___x_924_ = lean_string_append(v_fst_916_, v_numStr_918_);
lean_dec_ref(v_numStr_918_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_string_utf8_byte_size(v_numStr_918_);
lean_inc_ref(v_numStr_918_);
v___x_927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_927_, 0, v_numStr_918_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
lean_ctor_set(v___x_927_, 2, v___x_926_);
v___x_928_ = l_String_Slice_Pos_nextn(v___x_927_, v___x_925_, v_size_912_);
lean_dec_ref_known(v___x_927_, 3);
v___x_929_ = lean_string_utf8_extract_fast(v_numStr_918_, v___x_925_, v___x_928_);
lean_dec(v___x_928_);
lean_dec_ref(v_numStr_918_);
lean_inc_ref(v_fst_916_);
v___x_930_ = lean_string_append(v_fst_916_, v___x_929_);
lean_dec_ref(v___x_929_);
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate___boxed(lean_object* v_size_936_, lean_object* v_n_937_, lean_object* v_cut_938_){
_start:
{
uint8_t v_cut_boxed_939_; lean_object* v_res_940_; 
v_cut_boxed_939_ = lean_unbox(v_cut_938_);
v_res_940_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(v_size_936_, v_n_937_, v_cut_boxed_939_);
return v_res_940_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_unsigned_to_nat(2u);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_nat_mod(v___x_942_, v___x_941_);
return v___x_943_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_unsigned_to_nat(2u);
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_mod(v___x_945_, v___x_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(uint8_t v_x_947_){
_start:
{
if (v_x_947_ == 0)
{
lean_object* v___x_948_; 
v___x_948_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0);
return v___x_948_;
}
else
{
lean_object* v___x_949_; 
v___x_949_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___boxed(lean_object* v_x_950_){
_start:
{
uint8_t v_x_52__boxed_951_; lean_object* v_res_952_; 
v_x_52__boxed_951_ = lean_unbox(v_x_950_);
v_res_952_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_x_52__boxed_951_);
return v_res_952_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_954_ = lean_int_neg(v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(lean_object* v_symbols_955_, lean_object* v_month_956_){
_start:
{
lean_object* v_monthLong_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_monthLong_957_ = lean_ctor_get(v_symbols_955_, 0);
v___x_958_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_959_ = lean_int_add(v_month_956_, v___x_958_);
v___x_960_ = l_Int_toNat(v___x_959_);
lean_dec(v___x_959_);
v___x_961_ = lean_array_fget_borrowed(v_monthLong_957_, v___x_960_);
lean_dec(v___x_960_);
lean_inc(v___x_961_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___boxed(lean_object* v_symbols_962_, lean_object* v_month_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_962_, v_month_963_);
lean_dec(v_month_963_);
lean_dec_ref(v_symbols_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(lean_object* v_symbols_965_, lean_object* v_month_966_){
_start:
{
lean_object* v_monthShort_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_monthShort_967_ = lean_ctor_get(v_symbols_965_, 1);
v___x_968_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_969_ = lean_int_add(v_month_966_, v___x_968_);
v___x_970_ = l_Int_toNat(v___x_969_);
lean_dec(v___x_969_);
v___x_971_ = lean_array_fget_borrowed(v_monthShort_967_, v___x_970_);
lean_dec(v___x_970_);
lean_inc(v___x_971_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort___boxed(lean_object* v_symbols_972_, lean_object* v_month_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_972_, v_month_973_);
lean_dec(v_month_973_);
lean_dec_ref(v_symbols_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(lean_object* v_symbols_975_, lean_object* v_month_976_){
_start:
{
lean_object* v_monthNarrow_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_monthNarrow_977_ = lean_ctor_get(v_symbols_975_, 2);
v___x_978_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_979_ = lean_int_add(v_month_976_, v___x_978_);
v___x_980_ = l_Int_toNat(v___x_979_);
lean_dec(v___x_979_);
v___x_981_ = lean_array_fget_borrowed(v_monthNarrow_977_, v___x_980_);
lean_dec(v___x_980_);
lean_inc(v___x_981_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow___boxed(lean_object* v_symbols_982_, lean_object* v_month_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_982_, v_month_983_);
lean_dec(v_month_983_);
lean_dec_ref(v_symbols_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(lean_object* v_symbols_985_, uint8_t v_wd_986_){
_start:
{
lean_object* v_weekdayLong_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_weekdayLong_987_ = lean_ctor_get(v_symbols_985_, 3);
v___x_988_ = l_Std_Time_Weekday_toOrdinal(v_wd_986_);
v___x_989_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_990_ = lean_int_add(v___x_988_, v___x_989_);
lean_dec(v___x_988_);
v___x_991_ = l_Int_toNat(v___x_990_);
lean_dec(v___x_990_);
v___x_992_ = lean_array_fget_borrowed(v_weekdayLong_987_, v___x_991_);
lean_dec(v___x_991_);
lean_inc(v___x_992_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong___boxed(lean_object* v_symbols_993_, lean_object* v_wd_994_){
_start:
{
uint8_t v_wd_boxed_995_; lean_object* v_res_996_; 
v_wd_boxed_995_ = lean_unbox(v_wd_994_);
v_res_996_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_993_, v_wd_boxed_995_);
lean_dec_ref(v_symbols_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(lean_object* v_symbols_997_, uint8_t v_wd_998_){
_start:
{
lean_object* v_weekdayShort_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_weekdayShort_999_ = lean_ctor_get(v_symbols_997_, 4);
v___x_1000_ = l_Std_Time_Weekday_toOrdinal(v_wd_998_);
v___x_1001_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1002_ = lean_int_add(v___x_1000_, v___x_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = l_Int_toNat(v___x_1002_);
lean_dec(v___x_1002_);
v___x_1004_ = lean_array_fget_borrowed(v_weekdayShort_999_, v___x_1003_);
lean_dec(v___x_1003_);
lean_inc(v___x_1004_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort___boxed(lean_object* v_symbols_1005_, lean_object* v_wd_1006_){
_start:
{
uint8_t v_wd_boxed_1007_; lean_object* v_res_1008_; 
v_wd_boxed_1007_ = lean_unbox(v_wd_1006_);
v_res_1008_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1005_, v_wd_boxed_1007_);
lean_dec_ref(v_symbols_1005_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(lean_object* v_symbols_1009_, uint8_t v_wd_1010_){
_start:
{
lean_object* v_weekdayNarrow_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_weekdayNarrow_1011_ = lean_ctor_get(v_symbols_1009_, 5);
v___x_1012_ = l_Std_Time_Weekday_toOrdinal(v_wd_1010_);
v___x_1013_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1014_ = lean_int_add(v___x_1012_, v___x_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = l_Int_toNat(v___x_1014_);
lean_dec(v___x_1014_);
v___x_1016_ = lean_array_fget_borrowed(v_weekdayNarrow_1011_, v___x_1015_);
lean_dec(v___x_1015_);
lean_inc(v___x_1016_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow___boxed(lean_object* v_symbols_1017_, lean_object* v_wd_1018_){
_start:
{
uint8_t v_wd_boxed_1019_; lean_object* v_res_1020_; 
v_wd_boxed_1019_ = lean_unbox(v_wd_1018_);
v_res_1020_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1017_, v_wd_boxed_1019_);
lean_dec_ref(v_symbols_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(lean_object* v_symbols_1021_, uint8_t v_wd_1022_){
_start:
{
lean_object* v_weekdayTwoLetter_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_weekdayTwoLetter_1023_ = lean_ctor_get(v_symbols_1021_, 6);
v___x_1024_ = l_Std_Time_Weekday_toOrdinal(v_wd_1022_);
v___x_1025_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1026_ = lean_int_add(v___x_1024_, v___x_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = l_Int_toNat(v___x_1026_);
lean_dec(v___x_1026_);
v___x_1028_ = lean_array_fget_borrowed(v_weekdayTwoLetter_1023_, v___x_1027_);
lean_dec(v___x_1027_);
lean_inc(v___x_1028_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter___boxed(lean_object* v_symbols_1029_, lean_object* v_wd_1030_){
_start:
{
uint8_t v_wd_boxed_1031_; lean_object* v_res_1032_; 
v_wd_boxed_1031_ = lean_unbox(v_wd_1030_);
v_res_1032_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1029_, v_wd_boxed_1031_);
lean_dec_ref(v_symbols_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(lean_object* v_symbols_1033_, uint8_t v_era_1034_){
_start:
{
lean_object* v_eraShort_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_eraShort_1035_ = lean_ctor_get(v_symbols_1033_, 7);
v___x_1036_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1034_);
v___x_1037_ = lean_array_fget_borrowed(v_eraShort_1035_, v___x_1036_);
lean_dec(v___x_1036_);
lean_inc(v___x_1037_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort___boxed(lean_object* v_symbols_1038_, lean_object* v_era_1039_){
_start:
{
uint8_t v_era_boxed_1040_; lean_object* v_res_1041_; 
v_era_boxed_1040_ = lean_unbox(v_era_1039_);
v_res_1041_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1038_, v_era_boxed_1040_);
lean_dec_ref(v_symbols_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(lean_object* v_symbols_1042_, uint8_t v_era_1043_){
_start:
{
lean_object* v_eraLong_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_eraLong_1044_ = lean_ctor_get(v_symbols_1042_, 8);
v___x_1045_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1043_);
v___x_1046_ = lean_array_fget_borrowed(v_eraLong_1044_, v___x_1045_);
lean_dec(v___x_1045_);
lean_inc(v___x_1046_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong___boxed(lean_object* v_symbols_1047_, lean_object* v_era_1048_){
_start:
{
uint8_t v_era_boxed_1049_; lean_object* v_res_1050_; 
v_era_boxed_1049_ = lean_unbox(v_era_1048_);
v_res_1050_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1047_, v_era_boxed_1049_);
lean_dec_ref(v_symbols_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(lean_object* v_symbols_1051_, uint8_t v_era_1052_){
_start:
{
lean_object* v_eraNarrow_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_eraNarrow_1053_ = lean_ctor_get(v_symbols_1051_, 9);
v___x_1054_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1052_);
v___x_1055_ = lean_array_fget_borrowed(v_eraNarrow_1053_, v___x_1054_);
lean_dec(v___x_1054_);
lean_inc(v___x_1055_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow___boxed(lean_object* v_symbols_1056_, lean_object* v_era_1057_){
_start:
{
uint8_t v_era_boxed_1058_; lean_object* v_res_1059_; 
v_era_boxed_1058_ = lean_unbox(v_era_1057_);
v_res_1059_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1056_, v_era_boxed_1058_);
lean_dec_ref(v_symbols_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(lean_object* v_x_1064_){
_start:
{
lean_object* v_natZero_1065_; lean_object* v_intZero_1066_; uint8_t v_isNeg_1067_; lean_object* v_a_1068_; uint8_t v_isZero_1069_; lean_object* v_one_1070_; lean_object* v_n_1071_; uint8_t v_isZero_1072_; 
v_natZero_1065_ = lean_unsigned_to_nat(0u);
v_intZero_1066_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v_isNeg_1067_ = lean_int_dec_lt(v_x_1064_, v_intZero_1066_);
v_a_1068_ = lean_nat_abs(v_x_1064_);
v_isZero_1069_ = lean_nat_dec_eq(v_a_1068_, v_natZero_1065_);
v_one_1070_ = lean_unsigned_to_nat(1u);
v_n_1071_ = lean_nat_sub(v_a_1068_, v_one_1070_);
lean_dec(v_a_1068_);
v_isZero_1072_ = lean_nat_dec_eq(v_n_1071_, v_natZero_1065_);
if (v_isZero_1072_ == 1)
{
lean_object* v___x_1073_; 
lean_dec(v_n_1071_);
v___x_1073_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
return v___x_1073_;
}
else
{
lean_object* v_n_1074_; uint8_t v_isZero_1075_; 
v_n_1074_ = lean_nat_sub(v_n_1071_, v_one_1070_);
lean_dec(v_n_1071_);
v_isZero_1075_ = lean_nat_dec_eq(v_n_1074_, v_natZero_1065_);
if (v_isZero_1075_ == 1)
{
lean_object* v___x_1076_; 
lean_dec(v_n_1074_);
v___x_1076_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
return v___x_1076_;
}
else
{
lean_object* v_n_1077_; uint8_t v_isZero_1078_; 
v_n_1077_ = lean_nat_sub(v_n_1074_, v_one_1070_);
lean_dec(v_n_1074_);
v_isZero_1078_ = lean_nat_dec_eq(v_n_1077_, v_natZero_1065_);
if (v_isZero_1078_ == 1)
{
lean_object* v___x_1079_; 
lean_dec(v_n_1077_);
v___x_1079_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
return v___x_1079_;
}
else
{
lean_object* v_n_1080_; uint8_t v_isZero_1081_; lean_object* v___x_1082_; 
v_n_1080_ = lean_nat_sub(v_n_1077_, v_one_1070_);
lean_dec(v_n_1077_);
v_isZero_1081_ = lean_nat_dec_eq(v_n_1080_, v_natZero_1065_);
lean_dec(v_n_1080_);
v___x_1082_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
return v___x_1082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___boxed(lean_object* v_x_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_x_1083_);
lean_dec(v_x_1083_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(lean_object* v_symbols_1085_, lean_object* v_q_1086_){
_start:
{
lean_object* v_quarterShort_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_quarterShort_1087_ = lean_ctor_get(v_symbols_1085_, 10);
v___x_1088_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1089_ = lean_int_add(v_q_1086_, v___x_1088_);
v___x_1090_ = l_Int_toNat(v___x_1089_);
lean_dec(v___x_1089_);
v___x_1091_ = lean_array_fget_borrowed(v_quarterShort_1087_, v___x_1090_);
lean_dec(v___x_1090_);
lean_inc(v___x_1091_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort___boxed(lean_object* v_symbols_1092_, lean_object* v_q_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1092_, v_q_1093_);
lean_dec(v_q_1093_);
lean_dec_ref(v_symbols_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(lean_object* v_symbols_1095_, lean_object* v_q_1096_){
_start:
{
lean_object* v_quarterLong_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_quarterLong_1097_ = lean_ctor_get(v_symbols_1095_, 11);
v___x_1098_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1099_ = lean_int_add(v_q_1096_, v___x_1098_);
v___x_1100_ = l_Int_toNat(v___x_1099_);
lean_dec(v___x_1099_);
v___x_1101_ = lean_array_fget_borrowed(v_quarterLong_1097_, v___x_1100_);
lean_dec(v___x_1100_);
lean_inc(v___x_1101_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong___boxed(lean_object* v_symbols_1102_, lean_object* v_q_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1102_, v_q_1103_);
lean_dec(v_q_1103_);
lean_dec_ref(v_symbols_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(lean_object* v_symbols_1105_, lean_object* v_q_1106_){
_start:
{
lean_object* v_quarterNarrow_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_quarterNarrow_1107_ = lean_ctor_get(v_symbols_1105_, 12);
v___x_1108_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1109_ = lean_int_add(v_q_1106_, v___x_1108_);
v___x_1110_ = l_Int_toNat(v___x_1109_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_array_fget_borrowed(v_quarterNarrow_1107_, v___x_1110_);
lean_dec(v___x_1110_);
lean_inc(v___x_1111_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow___boxed(lean_object* v_symbols_1112_, lean_object* v_q_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1112_, v_q_1113_);
lean_dec(v_q_1113_);
lean_dec_ref(v_symbols_1112_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(lean_object* v_symbols_1115_, uint8_t v_marker_1116_){
_start:
{
if (v_marker_1116_ == 0)
{
lean_object* v_amShort_1117_; 
v_amShort_1117_ = lean_ctor_get(v_symbols_1115_, 13);
lean_inc_ref(v_amShort_1117_);
return v_amShort_1117_;
}
else
{
lean_object* v_pmShort_1118_; 
v_pmShort_1118_ = lean_ctor_get(v_symbols_1115_, 14);
lean_inc_ref(v_pmShort_1118_);
return v_pmShort_1118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort___boxed(lean_object* v_symbols_1119_, lean_object* v_marker_1120_){
_start:
{
uint8_t v_marker_boxed_1121_; lean_object* v_res_1122_; 
v_marker_boxed_1121_ = lean_unbox(v_marker_1120_);
v_res_1122_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1119_, v_marker_boxed_1121_);
lean_dec_ref(v_symbols_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(lean_object* v_symbols_1123_, uint8_t v_marker_1124_){
_start:
{
if (v_marker_1124_ == 0)
{
lean_object* v_amLong_1125_; 
v_amLong_1125_ = lean_ctor_get(v_symbols_1123_, 15);
lean_inc_ref(v_amLong_1125_);
return v_amLong_1125_;
}
else
{
lean_object* v_pmLong_1126_; 
v_pmLong_1126_ = lean_ctor_get(v_symbols_1123_, 16);
lean_inc_ref(v_pmLong_1126_);
return v_pmLong_1126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong___boxed(lean_object* v_symbols_1127_, lean_object* v_marker_1128_){
_start:
{
uint8_t v_marker_boxed_1129_; lean_object* v_res_1130_; 
v_marker_boxed_1129_ = lean_unbox(v_marker_1128_);
v_res_1130_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(v_symbols_1127_, v_marker_boxed_1129_);
lean_dec_ref(v_symbols_1127_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(lean_object* v_symbols_1131_, uint8_t v_marker_1132_){
_start:
{
if (v_marker_1132_ == 0)
{
lean_object* v_amNarrow_1133_; 
v_amNarrow_1133_ = lean_ctor_get(v_symbols_1131_, 17);
lean_inc_ref(v_amNarrow_1133_);
return v_amNarrow_1133_;
}
else
{
lean_object* v_pmNarrow_1134_; 
v_pmNarrow_1134_ = lean_ctor_get(v_symbols_1131_, 18);
lean_inc_ref(v_pmNarrow_1134_);
return v_pmNarrow_1134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow___boxed(lean_object* v_symbols_1135_, lean_object* v_marker_1136_){
_start:
{
uint8_t v_marker_boxed_1137_; lean_object* v_res_1138_; 
v_marker_boxed_1137_ = lean_unbox(v_marker_1136_);
v_res_1138_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1135_, v_marker_boxed_1137_);
lean_dec_ref(v_symbols_1135_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(lean_object* v_dp_1139_, uint8_t v_period_1140_){
_start:
{
switch(v_period_1140_)
{
case 0:
{
lean_object* v_am_1141_; 
v_am_1141_ = lean_ctor_get(v_dp_1139_, 0);
lean_inc_ref(v_am_1141_);
return v_am_1141_;
}
case 1:
{
lean_object* v_pm_1142_; 
v_pm_1142_ = lean_ctor_get(v_dp_1139_, 1);
lean_inc_ref(v_pm_1142_);
return v_pm_1142_;
}
case 2:
{
lean_object* v_noon_1143_; 
v_noon_1143_ = lean_ctor_get(v_dp_1139_, 2);
lean_inc_ref(v_noon_1143_);
return v_noon_1143_;
}
default: 
{
lean_object* v_midnight_1144_; 
v_midnight_1144_ = lean_ctor_get(v_dp_1139_, 3);
lean_inc_ref(v_midnight_1144_);
return v_midnight_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod___boxed(lean_object* v_dp_1145_, lean_object* v_period_1146_){
_start:
{
uint8_t v_period_boxed_1147_; lean_object* v_res_1148_; 
v_period_boxed_1147_ = lean_unbox(v_period_1146_);
v_res_1148_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dp_1145_, v_period_boxed_1147_);
lean_dec_ref(v_dp_1145_);
return v_res_1148_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_unsigned_to_nat(6u);
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = lean_nat_mod(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_unsigned_to_nat(6u);
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_mod(v___x_1153_, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(6u);
v___x_1156_ = lean_unsigned_to_nat(2u);
v___x_1157_ = lean_nat_mod(v___x_1156_, v___x_1155_);
return v___x_1157_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_unsigned_to_nat(6u);
v___x_1159_ = lean_unsigned_to_nat(3u);
v___x_1160_ = lean_nat_mod(v___x_1159_, v___x_1158_);
return v___x_1160_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_unsigned_to_nat(6u);
v___x_1162_ = lean_unsigned_to_nat(4u);
v___x_1163_ = lean_nat_mod(v___x_1162_, v___x_1161_);
return v___x_1163_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_unsigned_to_nat(6u);
v___x_1165_ = lean_unsigned_to_nat(5u);
v___x_1166_ = lean_nat_mod(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t v_x_1167_){
_start:
{
switch(v_x_1167_)
{
case 0:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0);
return v___x_1168_;
}
case 1:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1);
return v___x_1169_;
}
case 2:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2);
return v___x_1170_;
}
case 3:
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3);
return v___x_1171_;
}
case 4:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4);
return v___x_1172_;
}
default: 
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5);
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object* v_x_1174_){
_start:
{
uint8_t v_x_148__boxed_1175_; lean_object* v_res_1176_; 
v_x_148__boxed_1175_ = lean_unbox(v_x_1174_);
v_res_1176_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_x_148__boxed_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(lean_object* v_arr_1177_, uint8_t v_period_1178_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_period_1178_);
v___x_1180_ = lean_array_fget_borrowed(v_arr_1177_, v___x_1179_);
lean_dec(v___x_1179_);
lean_inc(v___x_1180_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod___boxed(lean_object* v_arr_1181_, lean_object* v_period_1182_){
_start:
{
uint8_t v_period_boxed_1183_; lean_object* v_res_1184_; 
v_period_boxed_1183_ = lean_unbox(v_period_1182_);
v_res_1184_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_arr_1181_, v_period_boxed_1183_);
lean_dec_ref(v_arr_1181_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(lean_object* v_data_1186_){
_start:
{
lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1188_ = lean_int_dec_lt(v_data_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1190_ = l_Int_repr(v_data_1186_);
v___x_1191_ = lean_string_append(v___x_1189_, v___x_1190_);
lean_dec_ref(v___x_1190_);
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Int_repr(v_data_1186_);
return v___x_1192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___boxed(lean_object* v_data_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(v_data_1193_);
lean_dec(v_data_1193_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(uint8_t v_x_1195_){
_start:
{
switch(v_x_1195_)
{
case 0:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
return v___x_1196_;
}
case 1:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_unsigned_to_nat(1u);
return v___x_1197_;
}
default: 
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_unsigned_to_nat(2u);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___boxed(lean_object* v_x_1199_){
_start:
{
uint8_t v_x_boxed_1200_; lean_object* v_res_1201_; 
v_x_boxed_1200_ = lean_unbox(v_x_1199_);
v_res_1201_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_x_boxed_1200_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(lean_object* v_k_1202_){
_start:
{
lean_inc(v_k_1202_);
return v_k_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg___boxed(lean_object* v_k_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(v_k_1203_);
lean_dec(v_k_1203_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_object* v_motive_1205_, lean_object* v_ctorIdx_1206_, uint8_t v_t_1207_, lean_object* v_h_1208_, lean_object* v_k_1209_){
_start:
{
lean_inc(v_k_1209_);
return v_k_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___boxed(lean_object* v_motive_1210_, lean_object* v_ctorIdx_1211_, lean_object* v_t_1212_, lean_object* v_h_1213_, lean_object* v_k_1214_){
_start:
{
uint8_t v_t_boxed_1215_; lean_object* v_res_1216_; 
v_t_boxed_1215_ = lean_unbox(v_t_1212_);
v_res_1216_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(v_motive_1210_, v_ctorIdx_1211_, v_t_boxed_1215_, v_h_1213_, v_k_1214_);
lean_dec(v_k_1214_);
lean_dec(v_ctorIdx_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(lean_object* v_yes_1217_){
_start:
{
lean_inc(v_yes_1217_);
return v_yes_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg___boxed(lean_object* v_yes_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(v_yes_1218_);
lean_dec(v_yes_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_object* v_motive_1220_, uint8_t v_t_1221_, lean_object* v_h_1222_, lean_object* v_yes_1223_){
_start:
{
lean_inc(v_yes_1223_);
return v_yes_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___boxed(lean_object* v_motive_1224_, lean_object* v_t_1225_, lean_object* v_h_1226_, lean_object* v_yes_1227_){
_start:
{
uint8_t v_t_boxed_1228_; lean_object* v_res_1229_; 
v_t_boxed_1228_ = lean_unbox(v_t_1225_);
v_res_1229_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(v_motive_1224_, v_t_boxed_1228_, v_h_1226_, v_yes_1227_);
lean_dec(v_yes_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(lean_object* v_no_1230_){
_start:
{
lean_inc(v_no_1230_);
return v_no_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg___boxed(lean_object* v_no_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(v_no_1231_);
lean_dec(v_no_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_object* v_motive_1233_, uint8_t v_t_1234_, lean_object* v_h_1235_, lean_object* v_no_1236_){
_start:
{
lean_inc(v_no_1236_);
return v_no_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___boxed(lean_object* v_motive_1237_, lean_object* v_t_1238_, lean_object* v_h_1239_, lean_object* v_no_1240_){
_start:
{
uint8_t v_t_boxed_1241_; lean_object* v_res_1242_; 
v_t_boxed_1241_ = lean_unbox(v_t_1238_);
v_res_1242_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(v_motive_1237_, v_t_boxed_1241_, v_h_1239_, v_no_1240_);
lean_dec(v_no_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(lean_object* v_optional_1243_){
_start:
{
lean_inc(v_optional_1243_);
return v_optional_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg___boxed(lean_object* v_optional_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(v_optional_1244_);
lean_dec(v_optional_1244_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_object* v_motive_1246_, uint8_t v_t_1247_, lean_object* v_h_1248_, lean_object* v_optional_1249_){
_start:
{
lean_inc(v_optional_1249_);
return v_optional_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___boxed(lean_object* v_motive_1250_, lean_object* v_t_1251_, lean_object* v_h_1252_, lean_object* v_optional_1253_){
_start:
{
uint8_t v_t_boxed_1254_; lean_object* v_res_1255_; 
v_t_boxed_1254_ = lean_unbox(v_t_1251_);
v_res_1255_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(v_motive_1250_, v_t_boxed_1254_, v_h_1252_, v_optional_1253_);
lean_dec(v_optional_1253_);
return v_res_1255_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(uint8_t v_x_1256_, uint8_t v_y_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1258_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_x_1256_);
v___x_1259_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_y_1257_);
v___x_1260_ = lean_nat_dec_eq(v___x_1258_, v___x_1259_);
lean_dec(v___x_1259_);
lean_dec(v___x_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq___boxed(lean_object* v_x_1261_, lean_object* v_y_1262_){
_start:
{
uint8_t v_x_21__boxed_1263_; uint8_t v_y_22__boxed_1264_; uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_x_21__boxed_1263_ = lean_unbox(v_x_1261_);
v_y_22__boxed_1264_ = lean_unbox(v_y_1262_);
v_res_1265_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_x_21__boxed_1263_, v_y_22__boxed_1264_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__1(lean_object* v_a_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Rat_ofInt(v_a_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_unsigned_to_nat(1000000000u);
v___x_1273_ = lean_nat_to_int(v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(lean_object* v_offset_1274_, uint8_t v_withMinutes_1275_, uint8_t v_withSeconds_1276_, uint8_t v_colon_1277_, uint8_t v_padHour_1278_){
_start:
{
lean_object* v___y_1280_; uint32_t v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1290_; uint32_t v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1297_; uint8_t v___y_1298_; uint32_t v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; uint8_t v___y_1302_; uint8_t v___y_1304_; lean_object* v___y_1305_; uint8_t v___y_1306_; uint32_t v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; uint8_t v___y_1310_; uint8_t v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; uint32_t v___y_1315_; lean_object* v___y_1316_; uint8_t v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1325_; uint8_t v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; uint32_t v___y_1330_; lean_object* v___y_1331_; uint8_t v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1339_; uint8_t v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; uint32_t v___y_1344_; lean_object* v___y_1345_; uint8_t v___y_1346_; lean_object* v___y_1350_; uint8_t v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; uint8_t v___y_1355_; uint32_t v___y_1356_; lean_object* v___y_1357_; uint8_t v___y_1358_; uint8_t v___y_1359_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; uint8_t v___y_1365_; lean_object* v___y_1366_; uint8_t v___y_1367_; uint32_t v___y_1368_; lean_object* v___y_1369_; uint8_t v___y_1370_; uint8_t v___y_1371_; lean_object* v___y_1373_; lean_object* v___y_1374_; uint32_t v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v_fst_1390_; lean_object* v_snd_1391_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1403_ = lean_int_dec_le(v___x_1402_, v_offset_1274_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1405_ = lean_int_neg(v_offset_1274_);
lean_dec(v_offset_1274_);
v_fst_1390_ = v___x_1404_;
v_snd_1391_ = v___x_1405_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1406_; 
v___x_1406_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1390_ = v___x_1406_;
v_snd_1391_ = v_offset_1274_;
goto v___jp_1389_;
}
v___jp_1279_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = lean_string_append(v___y_1283_, v___y_1284_);
v___x_1286_ = l_Int_repr(v___y_1280_);
lean_dec(v___y_1280_);
v___x_1287_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1282_, v___y_1281_, v___x_1286_);
lean_dec_ref(v___x_1286_);
v___x_1288_ = lean_string_append(v___x_1285_, v___x_1287_);
lean_dec_ref(v___x_1287_);
return v___x_1288_;
}
v___jp_1289_:
{
if (v_colon_1277_ == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___y_1280_ = v___y_1290_;
v___y_1281_ = v___y_1291_;
v___y_1282_ = v___y_1292_;
v___y_1283_ = v___y_1293_;
v___y_1284_ = v___x_1294_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1280_ = v___y_1290_;
v___y_1281_ = v___y_1291_;
v___y_1282_ = v___y_1292_;
v___y_1283_ = v___y_1293_;
v___y_1284_ = v___x_1295_;
goto v___jp_1279_;
}
}
v___jp_1296_:
{
if (v___y_1298_ == 0)
{
if (v___y_1302_ == 0)
{
lean_dec(v___y_1297_);
return v___y_1301_;
}
else
{
v___y_1290_ = v___y_1297_;
v___y_1291_ = v___y_1299_;
v___y_1292_ = v___y_1300_;
v___y_1293_ = v___y_1301_;
goto v___jp_1289_;
}
}
else
{
v___y_1290_ = v___y_1297_;
v___y_1291_ = v___y_1299_;
v___y_1292_ = v___y_1300_;
v___y_1293_ = v___y_1301_;
goto v___jp_1289_;
}
}
v___jp_1303_:
{
if (v___y_1304_ == 0)
{
v___y_1297_ = v___y_1305_;
v___y_1298_ = v___y_1306_;
v___y_1299_ = v___y_1307_;
v___y_1300_ = v___y_1308_;
v___y_1301_ = v___y_1309_;
v___y_1302_ = v___y_1304_;
goto v___jp_1296_;
}
else
{
v___y_1297_ = v___y_1305_;
v___y_1298_ = v___y_1306_;
v___y_1299_ = v___y_1307_;
v___y_1300_ = v___y_1308_;
v___y_1301_ = v___y_1309_;
v___y_1302_ = v___y_1310_;
goto v___jp_1296_;
}
}
v___jp_1311_:
{
uint8_t v___x_1319_; uint8_t v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1276_, v___y_1317_);
v___x_1320_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1276_, v___y_1312_);
v___x_1321_ = lean_int_dec_eq(v___y_1314_, v___y_1313_);
if (v___x_1321_ == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = 1;
v___y_1304_ = v___x_1320_;
v___y_1305_ = v___y_1314_;
v___y_1306_ = v___x_1319_;
v___y_1307_ = v___y_1315_;
v___y_1308_ = v___y_1316_;
v___y_1309_ = v___y_1318_;
v___y_1310_ = v___x_1322_;
goto v___jp_1303_;
}
else
{
uint8_t v___x_1323_; 
v___x_1323_ = 0;
v___y_1304_ = v___x_1320_;
v___y_1305_ = v___y_1314_;
v___y_1306_ = v___x_1319_;
v___y_1307_ = v___y_1315_;
v___y_1308_ = v___y_1316_;
v___y_1309_ = v___y_1318_;
v___y_1310_ = v___x_1323_;
goto v___jp_1303_;
}
}
v___jp_1324_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1334_ = lean_string_append(v___y_1327_, v___y_1333_);
v___x_1335_ = l_Int_repr(v___y_1325_);
lean_dec(v___y_1325_);
v___x_1336_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1331_, v___y_1330_, v___x_1335_);
lean_dec_ref(v___x_1335_);
v___x_1337_ = lean_string_append(v___x_1334_, v___x_1336_);
lean_dec_ref(v___x_1336_);
v___y_1312_ = v___y_1326_;
v___y_1313_ = v___y_1328_;
v___y_1314_ = v___y_1329_;
v___y_1315_ = v___y_1330_;
v___y_1316_ = v___y_1331_;
v___y_1317_ = v___y_1332_;
v___y_1318_ = v___x_1337_;
goto v___jp_1311_;
}
v___jp_1338_:
{
if (v_colon_1277_ == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___y_1325_ = v___y_1339_;
v___y_1326_ = v___y_1340_;
v___y_1327_ = v___y_1341_;
v___y_1328_ = v___y_1342_;
v___y_1329_ = v___y_1343_;
v___y_1330_ = v___y_1344_;
v___y_1331_ = v___y_1345_;
v___y_1332_ = v___y_1346_;
v___y_1333_ = v___x_1347_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1348_; 
v___x_1348_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1325_ = v___y_1339_;
v___y_1326_ = v___y_1340_;
v___y_1327_ = v___y_1341_;
v___y_1328_ = v___y_1342_;
v___y_1329_ = v___y_1343_;
v___y_1330_ = v___y_1344_;
v___y_1331_ = v___y_1345_;
v___y_1332_ = v___y_1346_;
v___y_1333_ = v___x_1348_;
goto v___jp_1324_;
}
}
v___jp_1349_:
{
if (v___y_1355_ == 0)
{
if (v___y_1359_ == 0)
{
lean_dec(v___y_1350_);
v___y_1312_ = v___y_1351_;
v___y_1313_ = v___y_1353_;
v___y_1314_ = v___y_1354_;
v___y_1315_ = v___y_1356_;
v___y_1316_ = v___y_1357_;
v___y_1317_ = v___y_1358_;
v___y_1318_ = v___y_1352_;
goto v___jp_1311_;
}
else
{
v___y_1339_ = v___y_1350_;
v___y_1340_ = v___y_1351_;
v___y_1341_ = v___y_1352_;
v___y_1342_ = v___y_1353_;
v___y_1343_ = v___y_1354_;
v___y_1344_ = v___y_1356_;
v___y_1345_ = v___y_1357_;
v___y_1346_ = v___y_1358_;
goto v___jp_1338_;
}
}
else
{
v___y_1339_ = v___y_1350_;
v___y_1340_ = v___y_1351_;
v___y_1341_ = v___y_1352_;
v___y_1342_ = v___y_1353_;
v___y_1343_ = v___y_1354_;
v___y_1344_ = v___y_1356_;
v___y_1345_ = v___y_1357_;
v___y_1346_ = v___y_1358_;
goto v___jp_1338_;
}
}
v___jp_1360_:
{
if (v___y_1365_ == 0)
{
v___y_1350_ = v___y_1361_;
v___y_1351_ = v___y_1362_;
v___y_1352_ = v___y_1363_;
v___y_1353_ = v___y_1364_;
v___y_1354_ = v___y_1366_;
v___y_1355_ = v___y_1367_;
v___y_1356_ = v___y_1368_;
v___y_1357_ = v___y_1369_;
v___y_1358_ = v___y_1370_;
v___y_1359_ = v___y_1365_;
goto v___jp_1349_;
}
else
{
v___y_1350_ = v___y_1361_;
v___y_1351_ = v___y_1362_;
v___y_1352_ = v___y_1363_;
v___y_1353_ = v___y_1364_;
v___y_1354_ = v___y_1366_;
v___y_1355_ = v___y_1367_;
v___y_1356_ = v___y_1368_;
v___y_1357_ = v___y_1369_;
v___y_1358_ = v___y_1370_;
v___y_1359_ = v___y_1371_;
goto v___jp_1349_;
}
}
v___jp_1372_:
{
lean_object* v_minute_1378_; lean_object* v_second_1379_; uint8_t v___x_1380_; uint8_t v___x_1381_; lean_object* v_data_1382_; uint8_t v___x_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v_minute_1378_ = lean_ctor_get(v___y_1373_, 1);
lean_inc(v_minute_1378_);
v_second_1379_ = lean_ctor_get(v___y_1373_, 2);
lean_inc(v_second_1379_);
lean_dec_ref(v___y_1373_);
v___x_1380_ = 0;
v___x_1381_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1275_, v___x_1380_);
lean_inc_ref(v___y_1374_);
v_data_1382_ = lean_string_append(v___y_1374_, v___y_1377_);
lean_dec_ref(v___y_1377_);
v___x_1383_ = 2;
v___x_1384_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1275_, v___x_1383_);
v___x_1385_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1386_ = lean_int_dec_eq(v_minute_1378_, v___x_1385_);
if (v___x_1386_ == 0)
{
uint8_t v___x_1387_; 
v___x_1387_ = 1;
v___y_1361_ = v_minute_1378_;
v___y_1362_ = v___x_1383_;
v___y_1363_ = v_data_1382_;
v___y_1364_ = v___x_1385_;
v___y_1365_ = v___x_1384_;
v___y_1366_ = v_second_1379_;
v___y_1367_ = v___x_1381_;
v___y_1368_ = v___y_1375_;
v___y_1369_ = v___y_1376_;
v___y_1370_ = v___x_1380_;
v___y_1371_ = v___x_1387_;
goto v___jp_1360_;
}
else
{
uint8_t v___x_1388_; 
v___x_1388_ = 0;
v___y_1361_ = v_minute_1378_;
v___y_1362_ = v___x_1383_;
v___y_1363_ = v_data_1382_;
v___y_1364_ = v___x_1385_;
v___y_1365_ = v___x_1384_;
v___y_1366_ = v_second_1379_;
v___y_1367_ = v___x_1381_;
v___y_1368_ = v___y_1375_;
v___y_1369_ = v___y_1376_;
v___y_1370_ = v___x_1380_;
v___y_1371_ = v___x_1388_;
goto v___jp_1360_;
}
}
v___jp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_time_1394_; lean_object* v___x_1395_; uint32_t v___x_1396_; 
v___x_1392_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1393_ = lean_int_mul(v_snd_1391_, v___x_1392_);
lean_dec(v_snd_1391_);
v_time_1394_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1393_);
lean_dec(v___x_1393_);
v___x_1395_ = lean_unsigned_to_nat(2u);
v___x_1396_ = 48;
if (v_padHour_1278_ == 0)
{
lean_object* v_hour_1397_; lean_object* v___x_1398_; 
v_hour_1397_ = lean_ctor_get(v_time_1394_, 0);
lean_inc(v_hour_1397_);
v___x_1398_ = l_Int_repr(v_hour_1397_);
lean_dec(v_hour_1397_);
v___y_1373_ = v_time_1394_;
v___y_1374_ = v_fst_1390_;
v___y_1375_ = v___x_1396_;
v___y_1376_ = v___x_1395_;
v___y_1377_ = v___x_1398_;
goto v___jp_1372_;
}
else
{
lean_object* v_hour_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_hour_1399_ = lean_ctor_get(v_time_1394_, 0);
lean_inc(v_hour_1399_);
v___x_1400_ = l_Int_repr(v_hour_1399_);
lean_dec(v_hour_1399_);
v___x_1401_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1395_, v___x_1396_, v___x_1400_);
lean_dec_ref(v___x_1400_);
v___y_1373_ = v_time_1394_;
v___y_1374_ = v_fst_1390_;
v___y_1375_ = v___x_1396_;
v___y_1376_ = v___x_1395_;
v___y_1377_ = v___x_1401_;
goto v___jp_1372_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___boxed(lean_object* v_offset_1407_, lean_object* v_withMinutes_1408_, lean_object* v_withSeconds_1409_, lean_object* v_colon_1410_, lean_object* v_padHour_1411_){
_start:
{
uint8_t v_withMinutes_boxed_1412_; uint8_t v_withSeconds_boxed_1413_; uint8_t v_colon_boxed_1414_; uint8_t v_padHour_boxed_1415_; lean_object* v_res_1416_; 
v_withMinutes_boxed_1412_ = lean_unbox(v_withMinutes_1408_);
v_withSeconds_boxed_1413_ = lean_unbox(v_withSeconds_1409_);
v_colon_boxed_1414_ = lean_unbox(v_colon_1410_);
v_padHour_boxed_1415_ = lean_unbox(v_padHour_1411_);
v_res_1416_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1407_, v_withMinutes_boxed_1412_, v_withSeconds_boxed_1413_, v_colon_boxed_1414_, v_padHour_boxed_1415_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0_spec__0(lean_object* v_a_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_nat_to_int(v_a_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(lean_object* v_a_1419_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_nat_to_int(v_a_1419_);
v___x_1421_ = l_Rat_ofInt(v___x_1420_);
return v___x_1421_;
}
}
static lean_object* _init_l_Std_Time_classifyDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_unsigned_to_nat(12u);
v___x_1423_ = lean_nat_to_int(v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod(lean_object* v_hour_1424_, lean_object* v_minute_1425_, lean_object* v_second_1426_){
_start:
{
lean_object* v___y_1428_; uint8_t v___y_1429_; uint8_t v___y_1435_; uint8_t v___y_1436_; lean_object* v___x_1440_; uint8_t v___x_1441_; uint8_t v___y_1443_; uint8_t v___x_1444_; 
v___x_1440_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1441_ = lean_int_dec_eq(v_hour_1424_, v___x_1440_);
v___x_1444_ = lean_int_dec_eq(v_minute_1425_, v___x_1440_);
if (v___x_1444_ == 0)
{
v___y_1443_ = v___x_1444_;
goto v___jp_1442_;
}
else
{
uint8_t v___x_1445_; 
v___x_1445_ = lean_int_dec_eq(v_second_1426_, v___x_1440_);
v___y_1443_ = v___x_1445_;
goto v___jp_1442_;
}
v___jp_1427_:
{
if (v___y_1429_ == 0)
{
uint8_t v___x_1430_; 
v___x_1430_ = lean_int_dec_lt(v_hour_1424_, v___y_1428_);
if (v___x_1430_ == 0)
{
uint8_t v___x_1431_; 
v___x_1431_ = 1;
return v___x_1431_;
}
else
{
uint8_t v___x_1432_; 
v___x_1432_ = 0;
return v___x_1432_;
}
}
else
{
uint8_t v___x_1433_; 
v___x_1433_ = 2;
return v___x_1433_;
}
}
v___jp_1434_:
{
if (v___y_1436_ == 0)
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1438_ = lean_int_dec_eq(v_hour_1424_, v___x_1437_);
if (v___x_1438_ == 0)
{
v___y_1428_ = v___x_1437_;
v___y_1429_ = v___x_1438_;
goto v___jp_1427_;
}
else
{
v___y_1428_ = v___x_1437_;
v___y_1429_ = v___y_1435_;
goto v___jp_1427_;
}
}
else
{
uint8_t v___x_1439_; 
v___x_1439_ = 3;
return v___x_1439_;
}
}
v___jp_1442_:
{
if (v___x_1441_ == 0)
{
v___y_1435_ = v___y_1443_;
v___y_1436_ = v___x_1441_;
goto v___jp_1434_;
}
else
{
v___y_1435_ = v___y_1443_;
v___y_1436_ = v___y_1443_;
goto v___jp_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___boxed(lean_object* v_hour_1446_, lean_object* v_minute_1447_, lean_object* v_second_1448_){
_start:
{
uint8_t v_res_1449_; lean_object* v_r_1450_; 
v_res_1449_ = l_Std_Time_classifyDayPeriod(v_hour_1446_, v_minute_1447_, v_second_1448_);
lean_dec(v_second_1448_);
lean_dec(v_minute_1447_);
lean_dec(v_hour_1446_);
v_r_1450_ = lean_box(v_res_1449_);
return v_r_1450_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_unsigned_to_nat(6u);
v___x_1452_ = lean_nat_to_int(v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__1(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_unsigned_to_nat(18u);
v___x_1454_ = lean_nat_to_int(v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__2(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_unsigned_to_nat(21u);
v___x_1456_ = lean_nat_to_int(v___x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object* v_hour_1457_, lean_object* v_minute_1458_, lean_object* v_second_1459_){
_start:
{
lean_object* v___y_1461_; uint8_t v___y_1462_; uint8_t v___y_1477_; uint8_t v___y_1478_; lean_object* v___x_1482_; uint8_t v___x_1483_; uint8_t v___y_1485_; uint8_t v___x_1486_; 
v___x_1482_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1483_ = lean_int_dec_eq(v_hour_1457_, v___x_1482_);
v___x_1486_ = lean_int_dec_eq(v_minute_1458_, v___x_1482_);
if (v___x_1486_ == 0)
{
v___y_1485_ = v___x_1486_;
goto v___jp_1484_;
}
else
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_int_dec_eq(v_second_1459_, v___x_1482_);
v___y_1485_ = v___x_1487_;
goto v___jp_1484_;
}
v___jp_1460_:
{
if (v___y_1462_ == 0)
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_1464_ = lean_int_dec_lt(v_hour_1457_, v___x_1463_);
if (v___x_1464_ == 0)
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_int_dec_lt(v_hour_1457_, v___y_1461_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__1, &l_Std_Time_classifyExtendedDayPeriod___closed__1_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__1);
v___x_1467_ = lean_int_dec_lt(v_hour_1457_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__2, &l_Std_Time_classifyExtendedDayPeriod___closed__2_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__2);
v___x_1469_ = lean_int_dec_lt(v_hour_1457_, v___x_1468_);
if (v___x_1469_ == 0)
{
uint8_t v___x_1470_; 
v___x_1470_ = 1;
return v___x_1470_;
}
else
{
uint8_t v___x_1471_; 
v___x_1471_ = 5;
return v___x_1471_;
}
}
else
{
uint8_t v___x_1472_; 
v___x_1472_ = 4;
return v___x_1472_;
}
}
else
{
uint8_t v___x_1473_; 
v___x_1473_ = 2;
return v___x_1473_;
}
}
else
{
uint8_t v___x_1474_; 
v___x_1474_ = 1;
return v___x_1474_;
}
}
else
{
uint8_t v___x_1475_; 
v___x_1475_ = 3;
return v___x_1475_;
}
}
v___jp_1476_:
{
if (v___y_1478_ == 0)
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1480_ = lean_int_dec_eq(v_hour_1457_, v___x_1479_);
if (v___x_1480_ == 0)
{
v___y_1461_ = v___x_1479_;
v___y_1462_ = v___x_1480_;
goto v___jp_1460_;
}
else
{
v___y_1461_ = v___x_1479_;
v___y_1462_ = v___y_1477_;
goto v___jp_1460_;
}
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = 0;
return v___x_1481_;
}
}
v___jp_1484_:
{
if (v___x_1483_ == 0)
{
v___y_1477_ = v___y_1485_;
v___y_1478_ = v___x_1483_;
goto v___jp_1476_;
}
else
{
v___y_1477_ = v___y_1485_;
v___y_1478_ = v___y_1485_;
goto v___jp_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyExtendedDayPeriod___boxed(lean_object* v_hour_1488_, lean_object* v_minute_1489_, lean_object* v_second_1490_){
_start:
{
uint8_t v_res_1491_; lean_object* v_r_1492_; 
v_res_1491_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1488_, v_minute_1489_, v_second_1490_);
lean_dec(v_second_1490_);
lean_dec(v_minute_1489_);
lean_dec(v_hour_1488_);
v_r_1492_ = lean_box(v_res_1491_);
return v_r_1492_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_unsigned_to_nat(100u);
v___x_1494_ = lean_nat_to_int(v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_unsigned_to_nat(7u);
v___x_1496_ = lean_nat_to_int(v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object* v_dateformat_1500_, lean_object* v_modifier_1501_, lean_object* v_data_1502_){
_start:
{
switch(lean_obj_tag(v_modifier_1501_))
{
case 0:
{
uint8_t v_presentation_1503_; 
v_presentation_1503_ = lean_ctor_get_uint8(v_modifier_1501_, 0);
lean_dec_ref_known(v_modifier_1501_, 0);
switch(v_presentation_1503_)
{
case 1:
{
lean_object* v_symbols_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; 
v_symbols_1504_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1505_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1506_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1504_, v___x_1505_);
return v___x_1506_;
}
case 2:
{
lean_object* v_symbols_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; 
v_symbols_1507_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1508_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1509_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1507_, v___x_1508_);
return v___x_1509_;
}
default: 
{
lean_object* v_symbols_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; 
v_symbols_1510_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1511_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1512_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1510_, v___x_1511_);
return v___x_1512_;
}
}
}
case 1:
{
lean_object* v_presentation_1513_; 
v_presentation_1513_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1513_);
lean_dec_ref_known(v_modifier_1501_, 1);
switch(lean_obj_tag(v_presentation_1513_))
{
case 0:
{
lean_object* v___x_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = lean_unsigned_to_nat(0u);
v___x_1515_ = 0;
v___x_1516_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1514_, v_data_1502_, v___x_1515_);
return v___x_1516_;
}
case 1:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1517_ = lean_unsigned_to_nat(2u);
v___x_1518_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1519_ = lean_int_emod(v_data_1502_, v___x_1518_);
lean_dec(v_data_1502_);
v___x_1520_ = 0;
v___x_1521_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1517_, v___x_1519_, v___x_1520_);
return v___x_1521_;
}
case 2:
{
lean_object* v___x_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = lean_unsigned_to_nat(4u);
v___x_1523_ = 0;
v___x_1524_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1522_, v_data_1502_, v___x_1523_);
return v___x_1524_;
}
default: 
{
lean_object* v_num_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; 
v_num_1525_ = lean_ctor_get(v_presentation_1513_, 0);
lean_inc(v_num_1525_);
lean_dec_ref_known(v_presentation_1513_, 1);
v___x_1526_ = 0;
v___x_1527_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1525_, v_data_1502_, v___x_1526_);
lean_dec(v_num_1525_);
return v___x_1527_;
}
}
}
case 2:
{
lean_object* v_presentation_1528_; lean_object* v___x_1529_; lean_object* v___y_1531_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v_presentation_1528_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1528_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1546_ = lean_int_dec_le(v_data_1502_, v___x_1545_);
if (v___x_1546_ == 0)
{
v___y_1531_ = v_data_1502_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = lean_int_neg(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1548_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1549_ = lean_int_add(v___x_1547_, v___x_1548_);
lean_dec(v___x_1547_);
v___y_1531_ = v___x_1549_;
goto v___jp_1530_;
}
v___jp_1530_:
{
switch(lean_obj_tag(v_presentation_1528_))
{
case 0:
{
uint8_t v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = 0;
v___x_1533_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1529_, v___y_1531_, v___x_1532_);
return v___x_1533_;
}
case 1:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; 
v___x_1534_ = lean_unsigned_to_nat(2u);
v___x_1535_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1536_ = lean_int_emod(v___y_1531_, v___x_1535_);
lean_dec(v___y_1531_);
v___x_1537_ = 0;
v___x_1538_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1534_, v___x_1536_, v___x_1537_);
return v___x_1538_;
}
case 2:
{
lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = lean_unsigned_to_nat(4u);
v___x_1540_ = 0;
v___x_1541_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1539_, v___y_1531_, v___x_1540_);
return v___x_1541_;
}
default: 
{
lean_object* v_num_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; 
v_num_1542_ = lean_ctor_get(v_presentation_1528_, 0);
lean_inc(v_num_1542_);
lean_dec_ref_known(v_presentation_1528_, 1);
v___x_1543_ = 0;
v___x_1544_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1542_, v___y_1531_, v___x_1543_);
lean_dec(v_num_1542_);
return v___x_1544_;
}
}
}
}
case 3:
{
lean_object* v_presentation_1550_; lean_object* v_snd_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; 
v_presentation_1550_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1550_);
lean_dec_ref_known(v_modifier_1501_, 1);
v_snd_1551_ = lean_ctor_get(v_data_1502_, 1);
lean_inc(v_snd_1551_);
lean_dec(v_data_1502_);
v___x_1552_ = 0;
v___x_1553_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1550_, v_snd_1551_, v___x_1552_);
lean_dec(v_presentation_1550_);
return v___x_1553_;
}
case 4:
{
lean_object* v_presentation_1554_; 
v_presentation_1554_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc_ref(v_presentation_1554_);
lean_dec_ref_known(v_modifier_1501_, 1);
if (lean_obj_tag(v_presentation_1554_) == 0)
{
lean_object* v_val_1555_; uint8_t v___x_1556_; lean_object* v___x_1557_; 
v_val_1555_ = lean_ctor_get(v_presentation_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v_presentation_1554_, 1);
v___x_1556_ = 0;
v___x_1557_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1555_, v_data_1502_, v___x_1556_);
lean_dec(v_val_1555_);
return v___x_1557_;
}
else
{
lean_object* v_val_1558_; uint8_t v___x_1559_; 
v_val_1558_ = lean_ctor_get(v_presentation_1554_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v_presentation_1554_, 1);
v___x_1559_ = lean_unbox(v_val_1558_);
lean_dec(v_val_1558_);
switch(v___x_1559_)
{
case 1:
{
lean_object* v_symbols_1560_; lean_object* v___x_1561_; 
v_symbols_1560_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1561_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1560_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1561_;
}
case 2:
{
lean_object* v_symbols_1562_; lean_object* v___x_1563_; 
v_symbols_1562_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1563_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1562_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1563_;
}
default: 
{
lean_object* v_symbols_1564_; lean_object* v___x_1565_; 
v_symbols_1564_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1565_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1564_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1565_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1566_; 
v_presentation_1566_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc_ref(v_presentation_1566_);
lean_dec_ref_known(v_modifier_1501_, 1);
if (lean_obj_tag(v_presentation_1566_) == 0)
{
lean_object* v_val_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; 
v_val_1567_ = lean_ctor_get(v_presentation_1566_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v_presentation_1566_, 1);
v___x_1568_ = 0;
v___x_1569_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1567_, v_data_1502_, v___x_1568_);
lean_dec(v_val_1567_);
return v___x_1569_;
}
else
{
lean_object* v_val_1570_; uint8_t v___x_1571_; 
v_val_1570_ = lean_ctor_get(v_presentation_1566_, 0);
lean_inc(v_val_1570_);
lean_dec_ref_known(v_presentation_1566_, 1);
v___x_1571_ = lean_unbox(v_val_1570_);
lean_dec(v_val_1570_);
switch(v___x_1571_)
{
case 1:
{
lean_object* v_symbols_1572_; lean_object* v___x_1573_; 
v_symbols_1572_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1573_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1572_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1573_;
}
case 2:
{
lean_object* v_symbols_1574_; lean_object* v___x_1575_; 
v_symbols_1574_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1575_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1574_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1575_;
}
default: 
{
lean_object* v_symbols_1576_; lean_object* v___x_1577_; 
v_symbols_1576_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1577_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1576_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1577_;
}
}
}
}
case 6:
{
lean_object* v_presentation_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; 
v_presentation_1578_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1578_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1579_ = 0;
v___x_1580_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1578_, v_data_1502_, v___x_1579_);
lean_dec(v_presentation_1578_);
return v___x_1580_;
}
case 7:
{
lean_object* v_presentation_1581_; 
v_presentation_1581_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc_ref(v_presentation_1581_);
lean_dec_ref_known(v_modifier_1501_, 1);
if (lean_obj_tag(v_presentation_1581_) == 0)
{
lean_object* v_val_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; 
v_val_1582_ = lean_ctor_get(v_presentation_1581_, 0);
lean_inc(v_val_1582_);
lean_dec_ref_known(v_presentation_1581_, 1);
v___x_1583_ = 0;
v___x_1584_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1582_, v_data_1502_, v___x_1583_);
lean_dec(v_val_1582_);
return v___x_1584_;
}
else
{
lean_object* v_val_1585_; uint8_t v___x_1586_; 
v_val_1585_ = lean_ctor_get(v_presentation_1581_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v_presentation_1581_, 1);
v___x_1586_ = lean_unbox(v_val_1585_);
lean_dec(v_val_1585_);
switch(v___x_1586_)
{
case 0:
{
lean_object* v_symbols_1587_; lean_object* v___x_1588_; 
v_symbols_1587_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1588_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1587_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1588_;
}
case 1:
{
lean_object* v_symbols_1589_; lean_object* v___x_1590_; 
v_symbols_1589_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1590_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1589_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1590_;
}
case 2:
{
lean_object* v_symbols_1591_; lean_object* v___x_1592_; 
v_symbols_1591_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1592_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1591_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1592_;
}
default: 
{
lean_object* v___x_1593_; 
v___x_1593_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1593_;
}
}
}
}
case 8:
{
lean_object* v_presentation_1594_; 
v_presentation_1594_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc_ref(v_presentation_1594_);
lean_dec_ref_known(v_modifier_1501_, 1);
if (lean_obj_tag(v_presentation_1594_) == 0)
{
lean_object* v_val_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; 
v_val_1595_ = lean_ctor_get(v_presentation_1594_, 0);
lean_inc(v_val_1595_);
lean_dec_ref_known(v_presentation_1594_, 1);
v___x_1596_ = 0;
v___x_1597_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1595_, v_data_1502_, v___x_1596_);
lean_dec(v_val_1595_);
return v___x_1597_;
}
else
{
lean_object* v_val_1598_; uint8_t v___x_1599_; 
v_val_1598_ = lean_ctor_get(v_presentation_1594_, 0);
lean_inc(v_val_1598_);
lean_dec_ref_known(v_presentation_1594_, 1);
v___x_1599_ = lean_unbox(v_val_1598_);
lean_dec(v_val_1598_);
switch(v___x_1599_)
{
case 0:
{
lean_object* v_symbols_1600_; lean_object* v___x_1601_; 
v_symbols_1600_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1601_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1600_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1601_;
}
case 1:
{
lean_object* v_symbols_1602_; lean_object* v___x_1603_; 
v_symbols_1602_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1603_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1602_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1603_;
}
case 2:
{
lean_object* v_symbols_1604_; lean_object* v___x_1605_; 
v_symbols_1604_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1605_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1604_, v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1605_;
}
default: 
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1502_);
lean_dec(v_data_1502_);
return v___x_1606_;
}
}
}
}
case 9:
{
lean_object* v_presentation_1607_; lean_object* v___x_1608_; lean_object* v___y_1610_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_presentation_1607_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1607_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1625_ = lean_int_dec_le(v_data_1502_, v___x_1624_);
if (v___x_1625_ == 0)
{
v___y_1610_ = v_data_1502_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = lean_int_neg(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1627_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1628_ = lean_int_add(v___x_1626_, v___x_1627_);
lean_dec(v___x_1626_);
v___y_1610_ = v___x_1628_;
goto v___jp_1609_;
}
v___jp_1609_:
{
switch(lean_obj_tag(v_presentation_1607_))
{
case 0:
{
uint8_t v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = 0;
v___x_1612_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1608_, v___y_1610_, v___x_1611_);
return v___x_1612_;
}
case 1:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1613_ = lean_unsigned_to_nat(2u);
v___x_1614_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1615_ = lean_int_emod(v___y_1610_, v___x_1614_);
lean_dec(v___y_1610_);
v___x_1616_ = 0;
v___x_1617_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1613_, v___x_1615_, v___x_1616_);
return v___x_1617_;
}
case 2:
{
lean_object* v___x_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_unsigned_to_nat(4u);
v___x_1619_ = 0;
v___x_1620_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1618_, v___y_1610_, v___x_1619_);
return v___x_1620_;
}
default: 
{
lean_object* v_num_1621_; uint8_t v___x_1622_; lean_object* v___x_1623_; 
v_num_1621_ = lean_ctor_get(v_presentation_1607_, 0);
lean_inc(v_num_1621_);
lean_dec_ref_known(v_presentation_1607_, 1);
v___x_1622_ = 0;
v___x_1623_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1621_, v___y_1610_, v___x_1622_);
lean_dec(v_num_1621_);
return v___x_1623_;
}
}
}
}
case 10:
{
lean_object* v_presentation_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; 
v_presentation_1629_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1629_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1630_ = 0;
v___x_1631_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1629_, v_data_1502_, v___x_1630_);
lean_dec(v_presentation_1629_);
return v___x_1631_;
}
case 11:
{
lean_object* v_presentation_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; 
v_presentation_1632_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1632_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1633_ = 0;
v___x_1634_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1632_, v_data_1502_, v___x_1633_);
lean_dec(v_presentation_1632_);
return v___x_1634_;
}
case 12:
{
uint8_t v_presentation_1635_; 
v_presentation_1635_ = lean_ctor_get_uint8(v_modifier_1501_, 0);
lean_dec_ref_known(v_modifier_1501_, 0);
switch(v_presentation_1635_)
{
case 0:
{
lean_object* v_symbols_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; 
v_symbols_1636_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1637_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1638_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1636_, v___x_1637_);
return v___x_1638_;
}
case 1:
{
lean_object* v_symbols_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; 
v_symbols_1639_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1640_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1641_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1639_, v___x_1640_);
return v___x_1641_;
}
case 2:
{
lean_object* v_symbols_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; 
v_symbols_1642_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1643_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1644_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1642_, v___x_1643_);
return v___x_1644_;
}
default: 
{
lean_object* v_symbols_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; 
v_symbols_1645_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1646_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1647_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1645_, v___x_1646_);
return v___x_1647_;
}
}
}
case 13:
{
lean_object* v_presentation_1648_; 
v_presentation_1648_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc_ref(v_presentation_1648_);
lean_dec_ref_known(v_modifier_1501_, 1);
if (lean_obj_tag(v_presentation_1648_) == 0)
{
lean_object* v_val_1649_; uint8_t v_firstDayOfWeek_1650_; lean_object* v_firstOrd_1651_; uint8_t v___x_1652_; lean_object* v_dayOrd_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; lean_object* v___x_1661_; 
v_val_1649_ = lean_ctor_get(v_presentation_1648_, 0);
lean_inc(v_val_1649_);
lean_dec_ref_known(v_presentation_1648_, 1);
v_firstDayOfWeek_1650_ = lean_ctor_get_uint8(v_dateformat_1500_, sizeof(void*)*2);
v_firstOrd_1651_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1650_);
v___x_1652_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v_dayOrd_1653_ = l_Std_Time_Weekday_toOrdinal(v___x_1652_);
v___x_1654_ = lean_int_sub(v_dayOrd_1653_, v_firstOrd_1651_);
lean_dec(v_firstOrd_1651_);
lean_dec(v_dayOrd_1653_);
v___x_1655_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1656_ = lean_int_add(v___x_1654_, v___x_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_int_emod(v___x_1656_, v___x_1655_);
lean_dec(v___x_1656_);
v___x_1658_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1659_ = lean_int_add(v___x_1657_, v___x_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = 0;
v___x_1661_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1649_, v___x_1659_, v___x_1660_);
lean_dec(v_val_1649_);
return v___x_1661_;
}
else
{
lean_object* v_val_1662_; uint8_t v___x_1663_; 
v_val_1662_ = lean_ctor_get(v_presentation_1648_, 0);
lean_inc(v_val_1662_);
lean_dec_ref_known(v_presentation_1648_, 1);
v___x_1663_ = lean_unbox(v_val_1662_);
lean_dec(v_val_1662_);
switch(v___x_1663_)
{
case 0:
{
lean_object* v_symbols_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; 
v_symbols_1664_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1665_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1666_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1664_, v___x_1665_);
return v___x_1666_;
}
case 1:
{
lean_object* v_symbols_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; 
v_symbols_1667_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1668_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1669_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1667_, v___x_1668_);
return v___x_1669_;
}
case 2:
{
lean_object* v_symbols_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; 
v_symbols_1670_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1671_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1672_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1670_, v___x_1671_);
return v___x_1672_;
}
default: 
{
lean_object* v_symbols_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; 
v_symbols_1673_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1674_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1675_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1673_, v___x_1674_);
return v___x_1675_;
}
}
}
}
case 14:
{
lean_object* v_presentation_1676_; 
v_presentation_1676_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc_ref(v_presentation_1676_);
lean_dec_ref_known(v_modifier_1501_, 1);
if (lean_obj_tag(v_presentation_1676_) == 0)
{
lean_object* v_val_1677_; uint8_t v_firstDayOfWeek_1678_; lean_object* v_firstOrd_1679_; uint8_t v___x_1680_; lean_object* v_dayOrd_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; 
v_val_1677_ = lean_ctor_get(v_presentation_1676_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v_presentation_1676_, 1);
v_firstDayOfWeek_1678_ = lean_ctor_get_uint8(v_dateformat_1500_, sizeof(void*)*2);
v_firstOrd_1679_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1678_);
v___x_1680_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v_dayOrd_1681_ = l_Std_Time_Weekday_toOrdinal(v___x_1680_);
v___x_1682_ = lean_int_sub(v_dayOrd_1681_, v_firstOrd_1679_);
lean_dec(v_firstOrd_1679_);
lean_dec(v_dayOrd_1681_);
v___x_1683_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1684_ = lean_int_add(v___x_1682_, v___x_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_int_emod(v___x_1684_, v___x_1683_);
lean_dec(v___x_1684_);
v___x_1686_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1687_ = lean_int_add(v___x_1685_, v___x_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = 0;
v___x_1689_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1677_, v___x_1687_, v___x_1688_);
lean_dec(v_val_1677_);
return v___x_1689_;
}
else
{
lean_object* v_val_1690_; uint8_t v___x_1691_; 
v_val_1690_ = lean_ctor_get(v_presentation_1676_, 0);
lean_inc(v_val_1690_);
lean_dec_ref_known(v_presentation_1676_, 1);
v___x_1691_ = lean_unbox(v_val_1690_);
lean_dec(v_val_1690_);
switch(v___x_1691_)
{
case 0:
{
lean_object* v_symbols_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; 
v_symbols_1692_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1693_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1694_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1692_, v___x_1693_);
return v___x_1694_;
}
case 1:
{
lean_object* v_symbols_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; 
v_symbols_1695_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1696_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1697_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1695_, v___x_1696_);
return v___x_1697_;
}
case 2:
{
lean_object* v_symbols_1698_; uint8_t v___x_1699_; lean_object* v___x_1700_; 
v_symbols_1698_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1699_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1700_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1698_, v___x_1699_);
return v___x_1700_;
}
default: 
{
lean_object* v_symbols_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; 
v_symbols_1701_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1702_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1703_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1701_, v___x_1702_);
return v___x_1703_;
}
}
}
}
case 15:
{
lean_object* v_presentation_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; 
v_presentation_1704_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1704_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1705_ = 0;
v___x_1706_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1704_, v_data_1502_, v___x_1705_);
lean_dec(v_presentation_1704_);
return v___x_1706_;
}
case 16:
{
uint8_t v_presentation_1707_; 
v_presentation_1707_ = lean_ctor_get_uint8(v_modifier_1501_, 0);
lean_dec_ref_known(v_modifier_1501_, 0);
if (v_presentation_1707_ == 2)
{
lean_object* v_symbols_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; 
v_symbols_1708_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1709_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1710_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1708_, v___x_1709_);
return v___x_1710_;
}
else
{
lean_object* v_symbols_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; 
v_symbols_1711_ = lean_ctor_get(v_dateformat_1500_, 1);
v___x_1712_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1713_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1711_, v___x_1712_);
return v___x_1713_;
}
}
case 17:
{
uint8_t v_presentation_1714_; 
v_presentation_1714_ = lean_ctor_get_uint8(v_modifier_1501_, 0);
lean_dec_ref_known(v_modifier_1501_, 0);
switch(v_presentation_1714_)
{
case 1:
{
lean_object* v_symbols_1715_; lean_object* v_dayPeriodLong_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; 
v_symbols_1715_ = lean_ctor_get(v_dateformat_1500_, 1);
v_dayPeriodLong_1716_ = lean_ctor_get(v_symbols_1715_, 20);
v___x_1717_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1718_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodLong_1716_, v___x_1717_);
return v___x_1718_;
}
case 2:
{
lean_object* v_symbols_1719_; lean_object* v_dayPeriodNarrow_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; 
v_symbols_1719_ = lean_ctor_get(v_dateformat_1500_, 1);
v_dayPeriodNarrow_1720_ = lean_ctor_get(v_symbols_1719_, 21);
v___x_1721_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1722_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodNarrow_1720_, v___x_1721_);
return v___x_1722_;
}
default: 
{
lean_object* v_symbols_1723_; lean_object* v_dayPeriodShort_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; 
v_symbols_1723_ = lean_ctor_get(v_dateformat_1500_, 1);
v_dayPeriodShort_1724_ = lean_ctor_get(v_symbols_1723_, 19);
v___x_1725_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1726_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodShort_1724_, v___x_1725_);
return v___x_1726_;
}
}
}
case 18:
{
uint8_t v_presentation_1727_; 
v_presentation_1727_ = lean_ctor_get_uint8(v_modifier_1501_, 0);
lean_dec_ref_known(v_modifier_1501_, 0);
switch(v_presentation_1727_)
{
case 1:
{
lean_object* v_symbols_1728_; lean_object* v_extendedDayPeriodLong_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; 
v_symbols_1728_ = lean_ctor_get(v_dateformat_1500_, 1);
v_extendedDayPeriodLong_1729_ = lean_ctor_get(v_symbols_1728_, 23);
v___x_1730_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1731_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodLong_1729_, v___x_1730_);
return v___x_1731_;
}
case 2:
{
lean_object* v_symbols_1732_; lean_object* v_extendedDayPeriodNarrow_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; 
v_symbols_1732_ = lean_ctor_get(v_dateformat_1500_, 1);
v_extendedDayPeriodNarrow_1733_ = lean_ctor_get(v_symbols_1732_, 24);
v___x_1734_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1735_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodNarrow_1733_, v___x_1734_);
return v___x_1735_;
}
default: 
{
lean_object* v_symbols_1736_; lean_object* v_extendedDayPeriodShort_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; 
v_symbols_1736_ = lean_ctor_get(v_dateformat_1500_, 1);
v_extendedDayPeriodShort_1737_ = lean_ctor_get(v_symbols_1736_, 22);
v___x_1738_ = lean_unbox(v_data_1502_);
lean_dec(v_data_1502_);
v___x_1739_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodShort_1737_, v___x_1738_);
return v___x_1739_;
}
}
}
case 19:
{
lean_object* v_presentation_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; 
v_presentation_1740_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1740_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1741_ = 0;
v___x_1742_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1740_, v_data_1502_, v___x_1741_);
lean_dec(v_presentation_1740_);
return v___x_1742_;
}
case 20:
{
lean_object* v_presentation_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; 
v_presentation_1743_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1743_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1744_ = 0;
v___x_1745_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1743_, v_data_1502_, v___x_1744_);
lean_dec(v_presentation_1743_);
return v___x_1745_;
}
case 21:
{
lean_object* v_presentation_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; 
v_presentation_1746_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1746_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1747_ = 0;
v___x_1748_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1746_, v_data_1502_, v___x_1747_);
lean_dec(v_presentation_1746_);
return v___x_1748_;
}
case 22:
{
lean_object* v_presentation_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; 
v_presentation_1749_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1749_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1750_ = 0;
v___x_1751_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1749_, v_data_1502_, v___x_1750_);
lean_dec(v_presentation_1749_);
return v___x_1751_;
}
case 23:
{
lean_object* v_presentation_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; 
v_presentation_1752_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1752_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1753_ = 0;
v___x_1754_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1752_, v_data_1502_, v___x_1753_);
lean_dec(v_presentation_1752_);
return v___x_1754_;
}
case 24:
{
lean_object* v_presentation_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; 
v_presentation_1755_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1755_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1756_ = 0;
v___x_1757_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1755_, v_data_1502_, v___x_1756_);
lean_dec(v_presentation_1755_);
return v___x_1757_;
}
case 25:
{
lean_object* v_presentation_1758_; 
v_presentation_1758_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1758_);
lean_dec_ref_known(v_modifier_1501_, 1);
if (lean_obj_tag(v_presentation_1758_) == 0)
{
lean_object* v___x_1759_; uint8_t v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = lean_unsigned_to_nat(9u);
v___x_1760_ = 0;
v___x_1761_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1759_, v_data_1502_, v___x_1760_);
return v___x_1761_;
}
else
{
lean_object* v_digits_1762_; lean_object* v___x_1763_; uint32_t v___x_1764_; lean_object* v___x_1765_; lean_object* v_s_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_digits_1762_ = lean_ctor_get(v_presentation_1758_, 0);
lean_inc(v_digits_1762_);
lean_dec_ref_known(v_presentation_1758_, 1);
v___x_1763_ = lean_unsigned_to_nat(9u);
v___x_1764_ = 48;
v___x_1765_ = l_Int_repr(v_data_1502_);
lean_dec(v_data_1502_);
v_s_1766_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1763_, v___x_1764_, v___x_1765_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_string_utf8_byte_size(v_s_1766_);
lean_inc_ref(v_s_1766_);
v___x_1769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1769_, 0, v_s_1766_);
lean_ctor_set(v___x_1769_, 1, v___x_1767_);
lean_ctor_set(v___x_1769_, 2, v___x_1768_);
v___x_1770_ = l_String_Slice_Pos_nextn(v___x_1769_, v___x_1767_, v_digits_1762_);
lean_dec_ref_known(v___x_1769_, 3);
v___x_1771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1771_, 0, v_s_1766_);
lean_ctor_set(v___x_1771_, 1, v___x_1767_);
lean_ctor_set(v___x_1771_, 2, v___x_1770_);
v___x_1772_ = l_String_Slice_toString(v___x_1771_);
lean_dec_ref_known(v___x_1771_, 3);
return v___x_1772_;
}
}
case 26:
{
lean_object* v_presentation_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; 
v_presentation_1773_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1773_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1774_ = 0;
v___x_1775_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1773_, v_data_1502_, v___x_1774_);
lean_dec(v_presentation_1773_);
return v___x_1775_;
}
case 27:
{
lean_object* v_presentation_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; 
v_presentation_1776_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1776_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1777_ = 0;
v___x_1778_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1776_, v_data_1502_, v___x_1777_);
lean_dec(v_presentation_1776_);
return v___x_1778_;
}
case 28:
{
lean_object* v_presentation_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; 
v_presentation_1779_ = lean_ctor_get(v_modifier_1501_, 0);
lean_inc(v_presentation_1779_);
lean_dec_ref_known(v_modifier_1501_, 1);
v___x_1780_ = 0;
v___x_1781_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1779_, v_data_1502_, v___x_1780_);
lean_dec(v_presentation_1779_);
return v___x_1781_;
}
case 29:
{
uint8_t v_presentation_1782_; 
v_presentation_1782_ = lean_ctor_get_uint8(v_modifier_1501_, 0);
lean_dec_ref_known(v_modifier_1501_, 0);
if (v_presentation_1782_ == 0)
{
lean_object* v___x_1783_; 
lean_dec(v_data_1502_);
v___x_1783_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1783_;
}
else
{
return v_data_1502_;
}
}
case 32:
{
uint8_t v_presentation_1784_; 
v_presentation_1784_ = lean_ctor_get_uint8(v_modifier_1501_, 0);
lean_dec_ref_known(v_modifier_1501_, 0);
if (v_presentation_1784_ == 0)
{
lean_object* v_fst_1786_; lean_object* v_snd_1787_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1811_ = lean_int_dec_eq(v_data_1502_, v___x_1810_);
if (v___x_1811_ == 0)
{
uint8_t v___x_1812_; 
v___x_1812_ = lean_int_dec_le(v___x_1810_, v_data_1502_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1814_ = lean_int_neg(v_data_1502_);
lean_dec(v_data_1502_);
v_fst_1786_ = v___x_1813_;
v_snd_1787_ = v___x_1814_;
goto v___jp_1785_;
}
else
{
lean_object* v___x_1815_; 
v___x_1815_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1786_ = v___x_1815_;
v_snd_1787_ = v_data_1502_;
goto v___jp_1785_;
}
}
else
{
lean_object* v___x_1816_; 
lean_dec(v_data_1502_);
v___x_1816_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1816_;
}
v___jp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v_t_1790_; lean_object* v_hour_1791_; lean_object* v_minute_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1788_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1789_ = lean_int_mul(v_snd_1787_, v___x_1788_);
lean_dec(v_snd_1787_);
v_t_1790_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1789_);
lean_dec(v___x_1789_);
v_hour_1791_ = lean_ctor_get(v_t_1790_, 0);
lean_inc(v_hour_1791_);
v_minute_1792_ = lean_ctor_get(v_t_1790_, 1);
lean_inc(v_minute_1792_);
lean_dec_ref(v_t_1790_);
v___x_1793_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1794_ = lean_int_dec_eq(v_minute_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; uint32_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1795_ = lean_unsigned_to_nat(2u);
v___x_1796_ = 48;
v___x_1797_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1798_ = lean_string_append(v___x_1797_, v_fst_1786_);
v___x_1799_ = l_Int_repr(v_hour_1791_);
lean_dec(v_hour_1791_);
v___x_1800_ = lean_string_append(v___x_1798_, v___x_1799_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___x_1802_ = lean_string_append(v___x_1800_, v___x_1801_);
v___x_1803_ = l_Int_repr(v_minute_1792_);
lean_dec(v_minute_1792_);
v___x_1804_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1795_, v___x_1796_, v___x_1803_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = lean_string_append(v___x_1802_, v___x_1804_);
lean_dec_ref(v___x_1804_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v_minute_1792_);
v___x_1806_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1807_ = lean_string_append(v___x_1806_, v_fst_1786_);
v___x_1808_ = l_Int_repr(v_hour_1791_);
lean_dec(v_hour_1791_);
v___x_1809_ = lean_string_append(v___x_1807_, v___x_1808_);
lean_dec_ref(v___x_1808_);
return v___x_1809_;
}
}
}
else
{
lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1818_ = lean_int_dec_eq(v_data_1502_, v___x_1817_);
if (v___x_1818_ == 0)
{
uint8_t v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1819_ = 1;
v___x_1820_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1821_ = 0;
v___x_1822_ = 1;
v___x_1823_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1821_, v___x_1822_, v___x_1819_, v___x_1819_);
v___x_1824_ = lean_string_append(v___x_1820_, v___x_1823_);
lean_dec_ref(v___x_1823_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; 
lean_dec(v_data_1502_);
v___x_1825_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1825_;
}
}
}
case 33:
{
uint8_t v_presentation_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_presentation_1826_ = lean_ctor_get_uint8(v_modifier_1501_, 0);
lean_dec_ref_known(v_modifier_1501_, 0);
v___x_1827_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1828_ = lean_int_dec_eq(v_data_1502_, v___x_1827_);
if (v___x_1828_ == 0)
{
uint8_t v___x_1829_; 
v___x_1829_ = 1;
switch(v_presentation_1826_)
{
case 0:
{
uint8_t v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = 2;
v___x_1831_ = 1;
v___x_1832_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1830_, v___x_1831_, v___x_1828_, v___x_1829_);
return v___x_1832_;
}
case 1:
{
uint8_t v___x_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = 0;
v___x_1834_ = 1;
v___x_1835_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1833_, v___x_1834_, v___x_1828_, v___x_1829_);
return v___x_1835_;
}
case 2:
{
uint8_t v___x_1836_; uint8_t v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = 0;
v___x_1837_ = 1;
v___x_1838_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1836_, v___x_1837_, v___x_1829_, v___x_1829_);
return v___x_1838_;
}
case 3:
{
uint8_t v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = 0;
v___x_1840_ = 2;
v___x_1841_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1839_, v___x_1840_, v___x_1828_, v___x_1829_);
return v___x_1841_;
}
default: 
{
uint8_t v___x_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = 0;
v___x_1843_ = 2;
v___x_1844_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1842_, v___x_1843_, v___x_1829_, v___x_1829_);
return v___x_1844_;
}
}
}
else
{
lean_object* v___x_1845_; 
lean_dec(v_data_1502_);
v___x_1845_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1845_;
}
}
case 34:
{
uint8_t v_presentation_1846_; 
v_presentation_1846_ = lean_ctor_get_uint8(v_modifier_1501_, 0);
lean_dec_ref_known(v_modifier_1501_, 0);
switch(v_presentation_1846_)
{
case 0:
{
uint8_t v___x_1847_; uint8_t v___x_1848_; uint8_t v___x_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; 
v___x_1847_ = 2;
v___x_1848_ = 1;
v___x_1849_ = 0;
v___x_1850_ = 1;
v___x_1851_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1847_, v___x_1848_, v___x_1849_, v___x_1850_);
return v___x_1851_;
}
case 1:
{
uint8_t v___x_1852_; uint8_t v___x_1853_; uint8_t v___x_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; 
v___x_1852_ = 0;
v___x_1853_ = 1;
v___x_1854_ = 0;
v___x_1855_ = 1;
v___x_1856_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1852_, v___x_1853_, v___x_1854_, v___x_1855_);
return v___x_1856_;
}
case 2:
{
uint8_t v___x_1857_; uint8_t v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1857_ = 0;
v___x_1858_ = 1;
v___x_1859_ = 1;
v___x_1860_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1857_, v___x_1858_, v___x_1859_, v___x_1859_);
return v___x_1860_;
}
case 3:
{
uint8_t v___x_1861_; uint8_t v___x_1862_; uint8_t v___x_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1861_ = 0;
v___x_1862_ = 2;
v___x_1863_ = 0;
v___x_1864_ = 1;
v___x_1865_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1861_, v___x_1862_, v___x_1863_, v___x_1864_);
return v___x_1865_;
}
default: 
{
uint8_t v___x_1866_; uint8_t v___x_1867_; uint8_t v___x_1868_; lean_object* v___x_1869_; 
v___x_1866_ = 0;
v___x_1867_ = 2;
v___x_1868_ = 1;
v___x_1869_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1866_, v___x_1867_, v___x_1868_, v___x_1868_);
return v___x_1869_;
}
}
}
case 35:
{
uint8_t v_presentation_1870_; 
v_presentation_1870_ = lean_ctor_get_uint8(v_modifier_1501_, 0);
lean_dec_ref_known(v_modifier_1501_, 0);
switch(v_presentation_1870_)
{
case 0:
{
uint8_t v___x_1871_; uint8_t v___x_1872_; uint8_t v___x_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; 
v___x_1871_ = 0;
v___x_1872_ = 2;
v___x_1873_ = 0;
v___x_1874_ = 1;
v___x_1875_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1871_, v___x_1872_, v___x_1873_, v___x_1874_);
return v___x_1875_;
}
case 1:
{
lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1877_ = lean_int_dec_eq(v_data_1502_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; uint8_t v___x_1879_; uint8_t v___x_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1878_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1879_ = 0;
v___x_1880_ = 1;
v___x_1881_ = 1;
v___x_1882_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1879_, v___x_1880_, v___x_1881_, v___x_1881_);
v___x_1883_ = lean_string_append(v___x_1878_, v___x_1882_);
lean_dec_ref(v___x_1882_);
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; 
lean_dec(v_data_1502_);
v___x_1884_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1884_;
}
}
default: 
{
lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1886_ = lean_int_dec_eq(v_data_1502_, v___x_1885_);
if (v___x_1886_ == 0)
{
uint8_t v___x_1887_; uint8_t v___x_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = 1;
v___x_1888_ = 0;
v___x_1889_ = 2;
v___x_1890_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1502_, v___x_1888_, v___x_1889_, v___x_1887_, v___x_1887_);
return v___x_1890_;
}
else
{
lean_object* v___x_1891_; 
lean_dec(v_data_1502_);
v___x_1891_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1891_;
}
}
}
}
default: 
{
lean_dec_ref(v_modifier_1501_);
return v_data_1502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___boxed(lean_object* v_dateformat_1892_, lean_object* v_modifier_1893_, lean_object* v_data_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_1892_, v_modifier_1893_, v_data_1894_);
lean_dec_ref(v_dateformat_1892_);
return v_res_1895_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_unsigned_to_nat(4u);
v___x_1897_ = lean_nat_to_int(v___x_1896_);
return v___x_1897_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_unsigned_to_nat(400u);
v___x_1899_ = lean_nat_to_int(v___x_1898_);
return v___x_1899_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1901_ = lean_string_utf8_byte_size(v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1903_ = lean_string_utf8_byte_size(v___x_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(lean_object* v_modifier_1904_, lean_object* v_dateformat_1905_, lean_object* v_date_1906_){
_start:
{
uint8_t v_firstDayOfWeek_1907_; lean_object* v_minimalDaysInFirstWeek_1908_; lean_object* v_date_1909_; lean_object* v_timezone_1910_; 
v_firstDayOfWeek_1907_ = lean_ctor_get_uint8(v_dateformat_1905_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1908_ = lean_ctor_get(v_dateformat_1905_, 0);
v_date_1909_ = lean_ctor_get(v_date_1906_, 0);
v_timezone_1910_ = lean_ctor_get(v_date_1906_, 3);
switch(lean_obj_tag(v_modifier_1904_))
{
case 0:
{
lean_object* v___x_1928_; lean_object* v_date_1929_; lean_object* v_year_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_1928_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc_ref(v_date_1929_);
lean_dec(v___x_1928_);
v_year_1930_ = lean_ctor_get(v_date_1929_, 0);
lean_inc(v_year_1930_);
lean_dec_ref(v_date_1929_);
v___x_1931_ = l_Std_Time_Year_Offset_era(v_year_1930_);
lean_dec(v_year_1930_);
v___x_1932_ = lean_box(v___x_1931_);
return v___x_1932_;
}
case 1:
{
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
goto v___jp_1911_;
}
case 2:
{
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
goto v___jp_1911_;
}
case 3:
{
lean_object* v___x_1933_; lean_object* v_date_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1962_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_1933_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v___x_1933_, 1);
lean_dec(v_unused_1963_);
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1962_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_date_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1962_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v_year_1938_; lean_object* v_month_1939_; lean_object* v_day_1940_; uint8_t v___y_1942_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; uint8_t v___y_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v_year_1938_ = lean_ctor_get(v_date_1934_, 0);
lean_inc(v_year_1938_);
v_month_1939_ = lean_ctor_get(v_date_1934_, 1);
lean_inc(v_month_1939_);
v_day_1940_ = lean_ctor_get(v_date_1934_, 2);
lean_inc(v_day_1940_);
lean_dec_ref(v_date_1934_);
v___x_1949_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1950_ = lean_int_mod(v_year_1938_, v___x_1949_);
v___x_1951_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1952_ = lean_int_dec_eq(v___x_1950_, v___x_1951_);
lean_dec(v___x_1950_);
v___x_1955_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1956_ = lean_int_mod(v_year_1938_, v___x_1955_);
v___x_1957_ = lean_int_dec_eq(v___x_1956_, v___x_1951_);
lean_dec(v___x_1956_);
if (v___x_1957_ == 0)
{
uint8_t v___x_1958_; 
lean_dec(v_year_1938_);
v___x_1958_ = 1;
v___y_1954_ = v___x_1958_;
goto v___jp_1953_;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1959_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1960_ = lean_int_mod(v_year_1938_, v___x_1959_);
lean_dec(v_year_1938_);
v___x_1961_ = lean_int_dec_eq(v___x_1960_, v___x_1951_);
lean_dec(v___x_1960_);
v___y_1954_ = v___x_1961_;
goto v___jp_1953_;
}
v___jp_1941_:
{
lean_object* v___x_1944_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 1, v_day_1940_);
lean_ctor_set(v___x_1936_, 0, v_month_1939_);
v___x_1944_ = v___x_1936_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_month_1939_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_day_1940_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = l_Std_Time_ValidDate_dayOfYear(v___y_1942_, v___x_1944_);
lean_dec_ref(v___x_1944_);
v___x_1946_ = lean_box(v___y_1942_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v___x_1945_);
return v___x_1947_;
}
}
v___jp_1953_:
{
if (v___x_1952_ == 0)
{
v___y_1942_ = v___x_1952_;
goto v___jp_1941_;
}
else
{
v___y_1942_ = v___y_1954_;
goto v___jp_1941_;
}
}
}
}
case 4:
{
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
goto v___jp_1915_;
}
case 5:
{
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
goto v___jp_1915_;
}
case 6:
{
lean_object* v___x_1964_; lean_object* v_date_1965_; lean_object* v_day_1966_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_1964_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc_ref(v_date_1965_);
lean_dec(v___x_1964_);
v_day_1966_ = lean_ctor_get(v_date_1965_, 2);
lean_inc(v_day_1966_);
lean_dec_ref(v_date_1965_);
return v_day_1966_;
}
case 7:
{
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
goto v___jp_1919_;
}
case 8:
{
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
goto v___jp_1919_;
}
case 9:
{
lean_object* v___x_1967_; lean_object* v_date_1968_; lean_object* v___x_1969_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_1967_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc_ref(v_date_1968_);
lean_dec(v___x_1967_);
v___x_1969_ = l_Std_Time_PlainDate_weekYear(v_date_1968_, v_firstDayOfWeek_1907_, v_minimalDaysInFirstWeek_1908_);
return v___x_1969_;
}
case 10:
{
lean_object* v___x_1970_; lean_object* v_date_1971_; lean_object* v___x_1972_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_1970_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc_ref(v_date_1971_);
lean_dec(v___x_1970_);
v___x_1972_ = l_Std_Time_PlainDate_weekOfYear(v_date_1971_, v_firstDayOfWeek_1907_, v_minimalDaysInFirstWeek_1908_);
return v___x_1972_;
}
case 11:
{
lean_object* v___x_1973_; lean_object* v_date_1974_; lean_object* v___x_1975_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_1973_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc_ref(v_date_1974_);
lean_dec(v___x_1973_);
v___x_1975_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1974_, v_firstDayOfWeek_1907_);
return v___x_1975_;
}
case 12:
{
lean_object* v___x_1976_; lean_object* v_date_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_1976_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc_ref(v_date_1977_);
lean_dec(v___x_1976_);
v___x_1978_ = l_Std_Time_PlainDate_weekday(v_date_1977_);
v___x_1979_ = lean_box(v___x_1978_);
return v___x_1979_;
}
case 13:
{
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
goto v___jp_1923_;
}
case 14:
{
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
goto v___jp_1923_;
}
case 15:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_1906_);
lean_dec_ref(v_date_1906_);
return v___x_1980_;
}
case 16:
{
lean_object* v___x_1981_; lean_object* v_time_1982_; lean_object* v_hour_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_1981_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_1982_ = lean_ctor_get(v___x_1981_, 1);
lean_inc_ref(v_time_1982_);
lean_dec(v___x_1981_);
v_hour_1983_ = lean_ctor_get(v_time_1982_, 0);
lean_inc(v_hour_1983_);
lean_dec_ref(v_time_1982_);
v___x_1984_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1983_);
lean_dec(v_hour_1983_);
v___x_1985_ = lean_box(v___x_1984_);
return v___x_1985_;
}
case 17:
{
lean_object* v___x_1986_; lean_object* v_time_1987_; lean_object* v_hour_1988_; lean_object* v_minute_1989_; lean_object* v_second_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_1986_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_1987_ = lean_ctor_get(v___x_1986_, 1);
lean_inc_ref(v_time_1987_);
lean_dec(v___x_1986_);
v_hour_1988_ = lean_ctor_get(v_time_1987_, 0);
lean_inc(v_hour_1988_);
v_minute_1989_ = lean_ctor_get(v_time_1987_, 1);
lean_inc(v_minute_1989_);
v_second_1990_ = lean_ctor_get(v_time_1987_, 2);
lean_inc(v_second_1990_);
lean_dec_ref(v_time_1987_);
v___x_1991_ = l_Std_Time_classifyDayPeriod(v_hour_1988_, v_minute_1989_, v_second_1990_);
lean_dec(v_second_1990_);
lean_dec(v_minute_1989_);
lean_dec(v_hour_1988_);
v___x_1992_ = lean_box(v___x_1991_);
return v___x_1992_;
}
case 18:
{
lean_object* v___x_1993_; lean_object* v_time_1994_; lean_object* v_hour_1995_; lean_object* v_minute_1996_; lean_object* v_second_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_1993_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_1994_ = lean_ctor_get(v___x_1993_, 1);
lean_inc_ref(v_time_1994_);
lean_dec(v___x_1993_);
v_hour_1995_ = lean_ctor_get(v_time_1994_, 0);
lean_inc(v_hour_1995_);
v_minute_1996_ = lean_ctor_get(v_time_1994_, 1);
lean_inc(v_minute_1996_);
v_second_1997_ = lean_ctor_get(v_time_1994_, 2);
lean_inc(v_second_1997_);
lean_dec_ref(v_time_1994_);
v___x_1998_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1995_, v_minute_1996_, v_second_1997_);
lean_dec(v_second_1997_);
lean_dec(v_minute_1996_);
lean_dec(v_hour_1995_);
v___x_1999_ = lean_box(v___x_1998_);
return v___x_1999_;
}
case 19:
{
lean_object* v___x_2000_; lean_object* v_time_2001_; lean_object* v_hour_2002_; lean_object* v___x_2003_; lean_object* v_fst_2004_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_2000_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_2001_ = lean_ctor_get(v___x_2000_, 1);
lean_inc_ref(v_time_2001_);
lean_dec(v___x_2000_);
v_hour_2002_ = lean_ctor_get(v_time_2001_, 0);
lean_inc(v_hour_2002_);
lean_dec_ref(v_time_2001_);
v___x_2003_ = l_Std_Time_HourMarker_toRelative(v_hour_2002_);
v_fst_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_fst_2004_);
lean_dec_ref(v___x_2003_);
return v_fst_2004_;
}
case 20:
{
lean_object* v___x_2005_; lean_object* v_time_2006_; lean_object* v_hour_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_2005_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_2006_ = lean_ctor_get(v___x_2005_, 1);
lean_inc_ref(v_time_2006_);
lean_dec(v___x_2005_);
v_hour_2007_ = lean_ctor_get(v_time_2006_, 0);
lean_inc(v_hour_2007_);
lean_dec_ref(v_time_2006_);
v___x_2008_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_2009_ = lean_int_emod(v_hour_2007_, v___x_2008_);
lean_dec(v_hour_2007_);
return v___x_2009_;
}
case 21:
{
lean_object* v___x_2010_; lean_object* v_time_2011_; lean_object* v_hour_2012_; lean_object* v___x_2013_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_2010_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_2011_ = lean_ctor_get(v___x_2010_, 1);
lean_inc_ref(v_time_2011_);
lean_dec(v___x_2010_);
v_hour_2012_ = lean_ctor_get(v_time_2011_, 0);
lean_inc(v_hour_2012_);
lean_dec_ref(v_time_2011_);
v___x_2013_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_2012_);
lean_dec(v_hour_2012_);
return v___x_2013_;
}
case 22:
{
lean_object* v___x_2014_; lean_object* v_time_2015_; lean_object* v_hour_2016_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_2014_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_2015_ = lean_ctor_get(v___x_2014_, 1);
lean_inc_ref(v_time_2015_);
lean_dec(v___x_2014_);
v_hour_2016_ = lean_ctor_get(v_time_2015_, 0);
lean_inc(v_hour_2016_);
lean_dec_ref(v_time_2015_);
return v_hour_2016_;
}
case 23:
{
lean_object* v___x_2017_; lean_object* v_time_2018_; lean_object* v_minute_2019_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_2017_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_2018_ = lean_ctor_get(v___x_2017_, 1);
lean_inc_ref(v_time_2018_);
lean_dec(v___x_2017_);
v_minute_2019_ = lean_ctor_get(v_time_2018_, 1);
lean_inc(v_minute_2019_);
lean_dec_ref(v_time_2018_);
return v_minute_2019_;
}
case 24:
{
lean_object* v___x_2020_; lean_object* v_time_2021_; lean_object* v_second_2022_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_2020_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_2021_ = lean_ctor_get(v___x_2020_, 1);
lean_inc_ref(v_time_2021_);
lean_dec(v___x_2020_);
v_second_2022_ = lean_ctor_get(v_time_2021_, 2);
lean_inc(v_second_2022_);
lean_dec_ref(v_time_2021_);
return v_second_2022_;
}
case 25:
{
lean_object* v___x_2023_; lean_object* v_time_2024_; lean_object* v_nanosecond_2025_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_2023_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_2024_ = lean_ctor_get(v___x_2023_, 1);
lean_inc_ref(v_time_2024_);
lean_dec(v___x_2023_);
v_nanosecond_2025_ = lean_ctor_get(v_time_2024_, 3);
lean_inc(v_nanosecond_2025_);
lean_dec_ref(v_time_2024_);
return v_nanosecond_2025_;
}
case 26:
{
lean_object* v___x_2026_; lean_object* v_time_2027_; lean_object* v___x_2028_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_2026_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_2027_ = lean_ctor_get(v___x_2026_, 1);
lean_inc_ref(v_time_2027_);
lean_dec(v___x_2026_);
v___x_2028_ = l_Std_Time_PlainTime_toMilliseconds(v_time_2027_);
lean_dec_ref(v_time_2027_);
return v___x_2028_;
}
case 27:
{
lean_object* v___x_2029_; lean_object* v_time_2030_; lean_object* v_nanosecond_2031_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_2029_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_2030_ = lean_ctor_get(v___x_2029_, 1);
lean_inc_ref(v_time_2030_);
lean_dec(v___x_2029_);
v_nanosecond_2031_ = lean_ctor_get(v_time_2030_, 3);
lean_inc(v_nanosecond_2031_);
lean_dec_ref(v_time_2030_);
return v_nanosecond_2031_;
}
case 28:
{
lean_object* v___x_2032_; lean_object* v_time_2033_; lean_object* v___x_2034_; 
lean_inc_ref(v_date_1909_);
lean_dec_ref(v_date_1906_);
v___x_2032_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_time_2033_ = lean_ctor_get(v___x_2032_, 1);
lean_inc_ref(v_time_2033_);
lean_dec(v___x_2032_);
v___x_2034_ = l_Std_Time_PlainTime_toNanoseconds(v_time_2033_);
lean_dec_ref(v_time_2033_);
return v___x_2034_;
}
case 29:
{
uint8_t v_presentation_2035_; 
lean_inc_ref(v_timezone_1910_);
lean_dec_ref(v_date_1906_);
v_presentation_2035_ = lean_ctor_get_uint8(v_modifier_1904_, 0);
if (v_presentation_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_dec_ref(v_timezone_1910_);
v___x_2036_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_2036_;
}
else
{
lean_object* v_offset_2037_; lean_object* v_name_2038_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v_offset_2037_ = lean_ctor_get(v_timezone_1910_, 0);
lean_inc(v_offset_2037_);
v_name_2038_ = lean_ctor_get(v_timezone_1910_, 1);
lean_inc_ref(v_name_2038_);
lean_dec_ref(v_timezone_1910_);
v___x_2053_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2054_ = lean_string_utf8_byte_size(v_name_2038_);
v___x_2055_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2056_ = lean_nat_dec_le(v___x_2055_, v___x_2054_);
if (v___x_2056_ == 0)
{
goto v___jp_2046_;
}
else
{
lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = lean_string_memcmp(v_name_2038_, v___x_2053_, v___x_2057_, v___x_2057_, v___x_2055_);
if (v___x_2058_ == 0)
{
goto v___jp_2046_;
}
else
{
lean_dec_ref(v_name_2038_);
goto v___jp_2039_;
}
}
v___jp_2039_:
{
uint8_t v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; uint8_t v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2040_ = 1;
v___x_2041_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2042_ = 0;
v___x_2043_ = 1;
v___x_2044_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2037_, v___x_2042_, v___x_2043_, v___x_2040_, v___x_2040_);
v___x_2045_ = lean_string_append(v___x_2041_, v___x_2044_);
lean_dec_ref(v___x_2044_);
return v___x_2045_;
}
v___jp_2046_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2047_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2048_ = lean_string_utf8_byte_size(v_name_2038_);
v___x_2049_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2050_ = lean_nat_dec_le(v___x_2049_, v___x_2048_);
if (v___x_2050_ == 0)
{
lean_dec(v_offset_2037_);
return v_name_2038_;
}
else
{
lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = lean_string_memcmp(v_name_2038_, v___x_2047_, v___x_2051_, v___x_2051_, v___x_2049_);
if (v___x_2052_ == 0)
{
lean_dec(v_offset_2037_);
return v_name_2038_;
}
else
{
lean_dec_ref(v_name_2038_);
goto v___jp_2039_;
}
}
}
}
}
case 30:
{
uint8_t v_presentation_2059_; 
lean_inc_ref(v_timezone_1910_);
lean_dec_ref(v_date_1906_);
v_presentation_2059_ = lean_ctor_get_uint8(v_modifier_1904_, 0);
if (v_presentation_2059_ == 0)
{
lean_object* v_offset_2060_; lean_object* v_abbreviation_2061_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v_offset_2060_ = lean_ctor_get(v_timezone_1910_, 0);
lean_inc(v_offset_2060_);
v_abbreviation_2061_ = lean_ctor_get(v_timezone_1910_, 2);
lean_inc_ref(v_abbreviation_2061_);
lean_dec_ref(v_timezone_1910_);
v___x_2076_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2077_ = lean_string_utf8_byte_size(v_abbreviation_2061_);
v___x_2078_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2079_ = lean_nat_dec_le(v___x_2078_, v___x_2077_);
if (v___x_2079_ == 0)
{
goto v___jp_2069_;
}
else
{
lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_string_memcmp(v_abbreviation_2061_, v___x_2076_, v___x_2080_, v___x_2080_, v___x_2078_);
if (v___x_2081_ == 0)
{
goto v___jp_2069_;
}
else
{
lean_dec_ref(v_abbreviation_2061_);
goto v___jp_2062_;
}
}
v___jp_2062_:
{
uint8_t v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2063_ = 1;
v___x_2064_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2065_ = 0;
v___x_2066_ = 1;
v___x_2067_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2060_, v___x_2065_, v___x_2066_, v___x_2063_, v___x_2063_);
v___x_2068_ = lean_string_append(v___x_2064_, v___x_2067_);
lean_dec_ref(v___x_2067_);
return v___x_2068_;
}
v___jp_2069_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2070_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2071_ = lean_string_utf8_byte_size(v_abbreviation_2061_);
v___x_2072_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2073_ = lean_nat_dec_le(v___x_2072_, v___x_2071_);
if (v___x_2073_ == 0)
{
lean_dec(v_offset_2060_);
return v_abbreviation_2061_;
}
else
{
lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = lean_string_memcmp(v_abbreviation_2061_, v___x_2070_, v___x_2074_, v___x_2074_, v___x_2072_);
if (v___x_2075_ == 0)
{
lean_dec(v_offset_2060_);
return v_abbreviation_2061_;
}
else
{
lean_dec_ref(v_abbreviation_2061_);
goto v___jp_2062_;
}
}
}
}
else
{
lean_object* v_offset_2082_; lean_object* v_name_2083_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_offset_2082_ = lean_ctor_get(v_timezone_1910_, 0);
lean_inc(v_offset_2082_);
v_name_2083_ = lean_ctor_get(v_timezone_1910_, 1);
lean_inc_ref(v_name_2083_);
lean_dec_ref(v_timezone_1910_);
v___x_2098_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2099_ = lean_string_utf8_byte_size(v_name_2083_);
v___x_2100_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2101_ = lean_nat_dec_le(v___x_2100_, v___x_2099_);
if (v___x_2101_ == 0)
{
goto v___jp_2091_;
}
else
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = lean_unsigned_to_nat(0u);
v___x_2103_ = lean_string_memcmp(v_name_2083_, v___x_2098_, v___x_2102_, v___x_2102_, v___x_2100_);
if (v___x_2103_ == 0)
{
goto v___jp_2091_;
}
else
{
lean_dec_ref(v_name_2083_);
goto v___jp_2084_;
}
}
v___jp_2084_:
{
uint8_t v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2085_ = 1;
v___x_2086_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2087_ = 0;
v___x_2088_ = 1;
v___x_2089_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2082_, v___x_2087_, v___x_2088_, v___x_2085_, v___x_2085_);
v___x_2090_ = lean_string_append(v___x_2086_, v___x_2089_);
lean_dec_ref(v___x_2089_);
return v___x_2090_;
}
v___jp_2091_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2092_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2093_ = lean_string_utf8_byte_size(v_name_2083_);
v___x_2094_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2095_ = lean_nat_dec_le(v___x_2094_, v___x_2093_);
if (v___x_2095_ == 0)
{
lean_dec(v_offset_2082_);
return v_name_2083_;
}
else
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = lean_string_memcmp(v_name_2083_, v___x_2092_, v___x_2096_, v___x_2096_, v___x_2094_);
if (v___x_2097_ == 0)
{
lean_dec(v_offset_2082_);
return v_name_2083_;
}
else
{
lean_dec_ref(v_name_2083_);
goto v___jp_2084_;
}
}
}
}
}
case 31:
{
uint8_t v_presentation_2104_; 
lean_inc_ref(v_timezone_1910_);
lean_dec_ref(v_date_1906_);
v_presentation_2104_ = lean_ctor_get_uint8(v_modifier_1904_, 0);
if (v_presentation_2104_ == 0)
{
lean_object* v_offset_2105_; lean_object* v_abbreviation_2106_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v_offset_2105_ = lean_ctor_get(v_timezone_1910_, 0);
lean_inc(v_offset_2105_);
v_abbreviation_2106_ = lean_ctor_get(v_timezone_1910_, 2);
lean_inc_ref(v_abbreviation_2106_);
lean_dec_ref(v_timezone_1910_);
v___x_2121_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2122_ = lean_string_utf8_byte_size(v_abbreviation_2106_);
v___x_2123_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2124_ = lean_nat_dec_le(v___x_2123_, v___x_2122_);
if (v___x_2124_ == 0)
{
goto v___jp_2114_;
}
else
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = lean_string_memcmp(v_abbreviation_2106_, v___x_2121_, v___x_2125_, v___x_2125_, v___x_2123_);
if (v___x_2126_ == 0)
{
goto v___jp_2114_;
}
else
{
lean_dec_ref(v_abbreviation_2106_);
goto v___jp_2107_;
}
}
v___jp_2107_:
{
uint8_t v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2108_ = 1;
v___x_2109_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2110_ = 0;
v___x_2111_ = 1;
v___x_2112_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2105_, v___x_2110_, v___x_2111_, v___x_2108_, v___x_2108_);
v___x_2113_ = lean_string_append(v___x_2109_, v___x_2112_);
lean_dec_ref(v___x_2112_);
return v___x_2113_;
}
v___jp_2114_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2115_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2116_ = lean_string_utf8_byte_size(v_abbreviation_2106_);
v___x_2117_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2118_ = lean_nat_dec_le(v___x_2117_, v___x_2116_);
if (v___x_2118_ == 0)
{
lean_dec(v_offset_2105_);
return v_abbreviation_2106_;
}
else
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = lean_string_memcmp(v_abbreviation_2106_, v___x_2115_, v___x_2119_, v___x_2119_, v___x_2117_);
if (v___x_2120_ == 0)
{
lean_dec(v_offset_2105_);
return v_abbreviation_2106_;
}
else
{
lean_dec_ref(v_abbreviation_2106_);
goto v___jp_2107_;
}
}
}
}
else
{
lean_object* v_offset_2127_; lean_object* v_name_2128_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_offset_2127_ = lean_ctor_get(v_timezone_1910_, 0);
lean_inc(v_offset_2127_);
v_name_2128_ = lean_ctor_get(v_timezone_1910_, 1);
lean_inc_ref(v_name_2128_);
lean_dec_ref(v_timezone_1910_);
v___x_2143_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2144_ = lean_string_utf8_byte_size(v_name_2128_);
v___x_2145_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2146_ = lean_nat_dec_le(v___x_2145_, v___x_2144_);
if (v___x_2146_ == 0)
{
goto v___jp_2136_;
}
else
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = lean_string_memcmp(v_name_2128_, v___x_2143_, v___x_2147_, v___x_2147_, v___x_2145_);
if (v___x_2148_ == 0)
{
goto v___jp_2136_;
}
else
{
lean_dec_ref(v_name_2128_);
goto v___jp_2129_;
}
}
v___jp_2129_:
{
uint8_t v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2130_ = 1;
v___x_2131_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2132_ = 0;
v___x_2133_ = 1;
v___x_2134_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2127_, v___x_2132_, v___x_2133_, v___x_2130_, v___x_2130_);
v___x_2135_ = lean_string_append(v___x_2131_, v___x_2134_);
lean_dec_ref(v___x_2134_);
return v___x_2135_;
}
v___jp_2136_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2137_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2138_ = lean_string_utf8_byte_size(v_name_2128_);
v___x_2139_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2140_ = lean_nat_dec_le(v___x_2139_, v___x_2138_);
if (v___x_2140_ == 0)
{
lean_dec(v_offset_2127_);
return v_name_2128_;
}
else
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = lean_string_memcmp(v_name_2128_, v___x_2137_, v___x_2141_, v___x_2141_, v___x_2139_);
if (v___x_2142_ == 0)
{
lean_dec(v_offset_2127_);
return v_name_2128_;
}
else
{
lean_dec_ref(v_name_2128_);
goto v___jp_2129_;
}
}
}
}
}
default: 
{
lean_object* v_offset_2149_; 
lean_inc_ref(v_timezone_1910_);
lean_dec_ref(v_date_1906_);
v_offset_2149_ = lean_ctor_get(v_timezone_1910_, 0);
lean_inc(v_offset_2149_);
lean_dec_ref(v_timezone_1910_);
return v_offset_2149_;
}
}
v___jp_1911_:
{
lean_object* v___x_1912_; lean_object* v_date_1913_; lean_object* v_year_1914_; 
v___x_1912_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc_ref(v_date_1913_);
lean_dec(v___x_1912_);
v_year_1914_ = lean_ctor_get(v_date_1913_, 0);
lean_inc(v_year_1914_);
lean_dec_ref(v_date_1913_);
return v_year_1914_;
}
v___jp_1915_:
{
lean_object* v___x_1916_; lean_object* v_date_1917_; lean_object* v_month_1918_; 
v___x_1916_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_date_1917_);
lean_dec(v___x_1916_);
v_month_1918_ = lean_ctor_get(v_date_1917_, 1);
lean_inc(v_month_1918_);
lean_dec_ref(v_date_1917_);
return v_month_1918_;
}
v___jp_1919_:
{
lean_object* v___x_1920_; lean_object* v_date_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc_ref(v_date_1921_);
lean_dec(v___x_1920_);
v___x_1922_ = l_Std_Time_PlainDate_quarter(v_date_1921_);
lean_dec_ref(v_date_1921_);
return v___x_1922_;
}
v___jp_1923_:
{
lean_object* v___x_1924_; lean_object* v_date_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1924_ = lean_thunk_get_own(v_date_1909_);
lean_dec_ref(v_date_1909_);
v_date_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc_ref(v_date_1925_);
lean_dec(v___x_1924_);
v___x_1926_ = l_Std_Time_PlainDate_weekday(v_date_1925_);
v___x_1927_ = lean_box(v___x_1926_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___boxed(lean_object* v_modifier_2150_, lean_object* v_dateformat_2151_, lean_object* v_date_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_2150_, v_dateformat_2151_, v_date_2152_);
lean_dec_ref(v_dateformat_2151_);
lean_dec_ref(v_modifier_2150_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0(lean_object* v___x_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
v___x_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___y_2155_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0(lean_object* v___x_2158_, lean_object* v_b_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_fst_2161_; lean_object* v_snd_2162_; lean_object* v___x_2163_; 
v_fst_2161_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_fst_2161_);
v_snd_2162_ = lean_ctor_get(v___x_2158_, 1);
lean_inc(v_snd_2162_);
lean_dec_ref(v___x_2158_);
lean_inc_ref(v___y_2160_);
v___x_2163_ = lean_apply_1(v_b_2159_, v___y_2160_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_dec(v_snd_2162_);
lean_dec(v_fst_2161_);
lean_dec_ref(v___y_2160_);
return v___x_2163_;
}
else
{
lean_object* v_pos_2164_; lean_object* v_snd_2165_; lean_object* v_snd_2166_; uint8_t v_decide_2167_; 
v_pos_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_pos_2164_);
v_snd_2165_ = lean_ctor_get(v___y_2160_, 1);
lean_inc(v_snd_2165_);
lean_dec_ref(v___y_2160_);
v_snd_2166_ = lean_ctor_get(v_pos_2164_, 1);
v_decide_2167_ = lean_nat_dec_eq(v_snd_2165_, v_snd_2166_);
lean_dec(v_snd_2165_);
if (v_decide_2167_ == 0)
{
lean_dec(v_pos_2164_);
lean_dec(v_snd_2162_);
lean_dec(v_fst_2161_);
return v___x_2163_;
}
else
{
lean_object* v___x_2168_; 
lean_dec_ref_known(v___x_2163_, 2);
v___x_2168_ = l_Std_Internal_Parsec_String_pstring(v_fst_2161_, v_pos_2164_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_pos_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_pos_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2176_ == 0)
{
lean_object* v_unused_2177_; 
v_unused_2177_ = lean_ctor_get(v___x_2168_, 1);
lean_dec(v_unused_2177_);
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_pos_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 1, v_snd_2162_);
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_pos_2169_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_snd_2162_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
else
{
lean_object* v_pos_2178_; lean_object* v_err_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_snd_2162_);
v_pos_2178_ = lean_ctor_get(v___x_2168_, 0);
v_err_2179_ = lean_ctor_get(v___x_2168_, 1);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2168_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_err_2179_);
lean_inc(v_pos_2178_);
lean_dec(v___x_2168_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_pos_2178_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_err_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(lean_object* v_as_2187_, size_t v_i_2188_, size_t v_stop_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_){
_start:
{
uint8_t v___x_2192_; 
v___x_2192_ = lean_usize_dec_eq(v_i_2188_, v_stop_2189_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; lean_object* v___f_2194_; size_t v___x_2195_; size_t v___x_2196_; 
v___x_2193_ = lean_array_uget_borrowed(v_as_2187_, v_i_2188_);
lean_inc(v___x_2193_);
v___f_2194_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2194_, 0, v___x_2193_);
lean_closure_set(v___f_2194_, 1, v_b_2190_);
v___x_2195_ = ((size_t)1ULL);
v___x_2196_ = lean_usize_add(v_i_2188_, v___x_2195_);
v_i_2188_ = v___x_2196_;
v_b_2190_ = v___f_2194_;
goto _start;
}
else
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_apply_1(v_b_2190_, v___y_2191_);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___boxed(lean_object* v_as_2199_, lean_object* v_i_2200_, lean_object* v_stop_2201_, lean_object* v_b_2202_, lean_object* v___y_2203_){
_start:
{
size_t v_i_boxed_2204_; size_t v_stop_boxed_2205_; lean_object* v_res_2206_; 
v_i_boxed_2204_ = lean_unbox_usize(v_i_2200_);
lean_dec(v_i_2200_);
v_stop_boxed_2205_ = lean_unbox_usize(v_stop_2201_);
lean_dec(v_stop_2201_);
v_res_2206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2199_, v_i_boxed_2204_, v_stop_boxed_2205_, v_b_2202_, v___y_2203_);
lean_dec_ref(v_as_2199_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(lean_object* v_pairs_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = lean_array_get_size(v_pairs_2212_);
v___x_2216_ = lean_nat_dec_lt(v___x_2214_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2218_, 0, v_a_2213_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
return v___x_2218_;
}
else
{
lean_object* v___f_2219_; uint8_t v___x_2220_; 
v___f_2219_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2));
v___x_2220_ = lean_nat_dec_le(v___x_2215_, v___x_2215_);
if (v___x_2220_ == 0)
{
if (v___x_2216_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_a_2213_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
return v___x_2222_;
}
else
{
size_t v___x_2223_; size_t v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = ((size_t)0ULL);
v___x_2224_ = lean_usize_of_nat(v___x_2215_);
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2212_, v___x_2223_, v___x_2224_, v___f_2219_, v_a_2213_);
return v___x_2225_;
}
}
else
{
size_t v___x_2226_; size_t v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = lean_usize_of_nat(v___x_2215_);
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2212_, v___x_2226_, v___x_2227_, v___f_2219_, v_a_2213_);
return v___x_2228_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___boxed(lean_object* v_pairs_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2229_, v_a_2230_);
lean_dec_ref(v_pairs_2229_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(lean_object* v_00_u03b1_2232_, lean_object* v_pairs_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2233_, v_a_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___boxed(lean_object* v_00_u03b1_2236_, lean_object* v_pairs_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(v_00_u03b1_2236_, v_pairs_2237_, v_a_2238_);
lean_dec_ref(v_pairs_2237_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_object* v_00_u03b1_2240_, lean_object* v_as_2241_, size_t v_i_2242_, size_t v_stop_2243_, lean_object* v_b_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2241_, v_i_2242_, v_stop_2243_, v_b_2244_, v___y_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___boxed(lean_object* v_00_u03b1_2247_, lean_object* v_as_2248_, lean_object* v_i_2249_, lean_object* v_stop_2250_, lean_object* v_b_2251_, lean_object* v___y_2252_){
_start:
{
size_t v_i_boxed_2253_; size_t v_stop_boxed_2254_; lean_object* v_res_2255_; 
v_i_boxed_2253_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_stop_boxed_2254_ = lean_unbox_usize(v_stop_2250_);
lean_dec(v_stop_2250_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(v_00_u03b1_2247_, v_as_2248_, v_i_boxed_2253_, v_stop_boxed_2254_, v_b_2251_, v___y_2252_);
lean_dec_ref(v_as_2248_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(size_t v_sz_2256_, size_t v_i_2257_, lean_object* v_bs_2258_){
_start:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_usize_dec_lt(v_i_2257_, v_sz_2256_);
if (v___x_2259_ == 0)
{
return v_bs_2258_;
}
else
{
lean_object* v_v_2260_; lean_object* v___x_2261_; lean_object* v_bs_x27_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; size_t v___x_2268_; size_t v___x_2269_; lean_object* v___x_2270_; 
v_v_2260_ = lean_array_uget(v_bs_2258_, v_i_2257_);
v___x_2261_ = lean_unsigned_to_nat(0u);
v_bs_x27_2262_ = lean_array_uset(v_bs_2258_, v_i_2257_, v___x_2261_);
v___x_2263_ = lean_usize_to_nat(v_i_2257_);
v___x_2264_ = lean_nat_to_int(v___x_2263_);
v___x_2265_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2266_ = lean_int_add(v___x_2264_, v___x_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v_v_2260_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = ((size_t)1ULL);
v___x_2269_ = lean_usize_add(v_i_2257_, v___x_2268_);
v___x_2270_ = lean_array_uset(v_bs_x27_2262_, v_i_2257_, v___x_2267_);
v_i_2257_ = v___x_2269_;
v_bs_2258_ = v___x_2270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2272_, lean_object* v_i_2273_, lean_object* v_bs_2274_){
_start:
{
size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2272_);
lean_dec(v_sz_2272_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_boxed_2275_, v_i_boxed_2276_, v_bs_2274_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(lean_object* v_as_2278_, size_t v_sz_2279_, size_t v_i_2280_, lean_object* v_bs_2281_){
_start:
{
uint8_t v___x_2282_; 
v___x_2282_ = lean_usize_dec_lt(v_i_2280_, v_sz_2279_);
if (v___x_2282_ == 0)
{
return v_bs_2281_;
}
else
{
lean_object* v_v_2283_; lean_object* v___x_2284_; lean_object* v_bs_x27_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; size_t v___x_2291_; size_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_v_2283_ = lean_array_uget(v_bs_2281_, v_i_2280_);
v___x_2284_ = lean_unsigned_to_nat(0u);
v_bs_x27_2285_ = lean_array_uset(v_bs_2281_, v_i_2280_, v___x_2284_);
v___x_2286_ = lean_usize_to_nat(v_i_2280_);
v___x_2287_ = lean_nat_to_int(v___x_2286_);
v___x_2288_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2289_ = lean_int_add(v___x_2287_, v___x_2288_);
lean_dec(v___x_2287_);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v_v_2283_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = ((size_t)1ULL);
v___x_2292_ = lean_usize_add(v_i_2280_, v___x_2291_);
v___x_2293_ = lean_array_uset(v_bs_x27_2285_, v_i_2280_, v___x_2290_);
v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2279_, v___x_2292_, v___x_2293_);
return v___x_2294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0___boxed(lean_object* v_as_2295_, lean_object* v_sz_2296_, lean_object* v_i_2297_, lean_object* v_bs_2298_){
_start:
{
size_t v_sz_boxed_2299_; size_t v_i_boxed_2300_; lean_object* v_res_2301_; 
v_sz_boxed_2299_ = lean_unbox_usize(v_sz_2296_);
lean_dec(v_sz_2296_);
v_i_boxed_2300_ = lean_unbox_usize(v_i_2297_);
lean_dec(v_i_2297_);
v_res_2301_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_as_2295_, v_sz_boxed_2299_, v_i_boxed_2300_, v_bs_2298_);
lean_dec_ref(v_as_2295_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(lean_object* v_arr_2302_){
_start:
{
size_t v_sz_2303_; size_t v___x_2304_; lean_object* v___x_2305_; 
v_sz_2303_ = lean_array_size(v_arr_2302_);
v___x_2304_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2302_);
v___x_2305_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2302_, v_sz_2303_, v___x_2304_, v_arr_2302_);
lean_dec_ref(v_arr_2302_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(lean_object* v_as_2306_, size_t v_sz_2307_, size_t v_i_2308_, lean_object* v_bs_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2307_, v_i_2308_, v_bs_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___boxed(lean_object* v_as_2311_, lean_object* v_sz_2312_, lean_object* v_i_2313_, lean_object* v_bs_2314_){
_start:
{
size_t v_sz_boxed_2315_; size_t v_i_boxed_2316_; lean_object* v_res_2317_; 
v_sz_boxed_2315_ = lean_unbox_usize(v_sz_2312_);
lean_dec(v_sz_2312_);
v_i_boxed_2316_ = lean_unbox_usize(v_i_2313_);
lean_dec(v_i_2313_);
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(v_as_2311_, v_sz_boxed_2315_, v_i_boxed_2316_, v_bs_2314_);
lean_dec_ref(v_as_2311_);
return v_res_2317_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object* v_x_2318_){
_start:
{
lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2319_ = lean_unsigned_to_nat(0u);
v___x_2320_ = lean_nat_dec_eq(v_x_2318_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = lean_nat_dec_eq(v_x_2318_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2323_ = lean_unsigned_to_nat(2u);
v___x_2324_ = lean_nat_dec_eq(v_x_2318_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = lean_unsigned_to_nat(3u);
v___x_2326_ = lean_nat_dec_eq(v_x_2318_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = lean_unsigned_to_nat(4u);
v___x_2328_ = lean_nat_dec_eq(v_x_2318_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2329_ = lean_unsigned_to_nat(5u);
v___x_2330_ = lean_nat_dec_eq(v_x_2318_, v___x_2329_);
if (v___x_2330_ == 0)
{
uint8_t v___x_2331_; 
v___x_2331_ = 5;
return v___x_2331_;
}
else
{
uint8_t v___x_2332_; 
v___x_2332_ = 4;
return v___x_2332_;
}
}
else
{
uint8_t v___x_2333_; 
v___x_2333_ = 3;
return v___x_2333_;
}
}
else
{
uint8_t v___x_2334_; 
v___x_2334_ = 2;
return v___x_2334_;
}
}
else
{
uint8_t v___x_2335_; 
v___x_2335_ = 1;
return v___x_2335_;
}
}
else
{
uint8_t v___x_2336_; 
v___x_2336_ = 0;
return v___x_2336_;
}
}
else
{
uint8_t v___x_2337_; 
v___x_2337_ = 6;
return v___x_2337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object* v_x_2338_){
_start:
{
uint8_t v_res_2339_; lean_object* v_r_2340_; 
v_res_2339_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_x_2338_);
lean_dec(v_x_2338_);
v_r_2340_ = lean_box(v_res_2339_);
return v_r_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(size_t v_sz_2341_, size_t v_i_2342_, lean_object* v_bs_2343_){
_start:
{
uint8_t v___x_2344_; 
v___x_2344_ = lean_usize_dec_lt(v_i_2342_, v_sz_2341_);
if (v___x_2344_ == 0)
{
return v_bs_2343_;
}
else
{
lean_object* v_v_2345_; lean_object* v___x_2346_; lean_object* v_bs_x27_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; size_t v___x_2355_; size_t v___x_2356_; lean_object* v___x_2357_; 
v_v_2345_ = lean_array_uget(v_bs_2343_, v_i_2342_);
v___x_2346_ = lean_unsigned_to_nat(0u);
v_bs_x27_2347_ = lean_array_uset(v_bs_2343_, v_i_2342_, v___x_2346_);
v___x_2348_ = lean_usize_to_nat(v_i_2342_);
v___x_2349_ = lean_nat_to_int(v___x_2348_);
v___x_2350_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2351_ = lean_int_add(v___x_2349_, v___x_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = l_Std_Time_Weekday_ofOrdinal(v___x_2351_);
lean_dec(v___x_2351_);
v___x_2353_ = lean_box(v___x_2352_);
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v_v_2345_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = lean_usize_add(v_i_2342_, v___x_2355_);
v___x_2357_ = lean_array_uset(v_bs_x27_2347_, v_i_2342_, v___x_2354_);
v_i_2342_ = v___x_2356_;
v_bs_2343_ = v___x_2357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2359_, lean_object* v_i_2360_, lean_object* v_bs_2361_){
_start:
{
size_t v_sz_boxed_2362_; size_t v_i_boxed_2363_; lean_object* v_res_2364_; 
v_sz_boxed_2362_ = lean_unbox_usize(v_sz_2359_);
lean_dec(v_sz_2359_);
v_i_boxed_2363_ = lean_unbox_usize(v_i_2360_);
lean_dec(v_i_2360_);
v_res_2364_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_boxed_2362_, v_i_boxed_2363_, v_bs_2361_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(lean_object* v_as_2365_, size_t v_sz_2366_, size_t v_i_2367_, lean_object* v_bs_2368_){
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
lean_object* v_v_2370_; lean_object* v___x_2371_; lean_object* v_bs_x27_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; size_t v___x_2380_; size_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_v_2370_ = lean_array_uget(v_bs_2368_, v_i_2367_);
v___x_2371_ = lean_unsigned_to_nat(0u);
v_bs_x27_2372_ = lean_array_uset(v_bs_2368_, v_i_2367_, v___x_2371_);
v___x_2373_ = lean_usize_to_nat(v_i_2367_);
v___x_2374_ = lean_nat_to_int(v___x_2373_);
v___x_2375_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2376_ = lean_int_add(v___x_2374_, v___x_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = l_Std_Time_Weekday_ofOrdinal(v___x_2376_);
lean_dec(v___x_2376_);
v___x_2378_ = lean_box(v___x_2377_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_v_2370_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = ((size_t)1ULL);
v___x_2381_ = lean_usize_add(v_i_2367_, v___x_2380_);
v___x_2382_ = lean_array_uset(v_bs_x27_2372_, v_i_2367_, v___x_2379_);
v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2366_, v___x_2381_, v___x_2382_);
return v___x_2383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0___boxed(lean_object* v_as_2384_, lean_object* v_sz_2385_, lean_object* v_i_2386_, lean_object* v_bs_2387_){
_start:
{
size_t v_sz_boxed_2388_; size_t v_i_boxed_2389_; lean_object* v_res_2390_; 
v_sz_boxed_2388_ = lean_unbox_usize(v_sz_2385_);
lean_dec(v_sz_2385_);
v_i_boxed_2389_ = lean_unbox_usize(v_i_2386_);
lean_dec(v_i_2386_);
v_res_2390_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_as_2384_, v_sz_boxed_2388_, v_i_boxed_2389_, v_bs_2387_);
lean_dec_ref(v_as_2384_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(lean_object* v_arr_2391_){
_start:
{
size_t v_sz_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
v_sz_2392_ = lean_array_size(v_arr_2391_);
v___x_2393_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2391_);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_arr_2391_, v_sz_2392_, v___x_2393_, v_arr_2391_);
lean_dec_ref(v_arr_2391_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(lean_object* v_as_2395_, size_t v_sz_2396_, size_t v_i_2397_, lean_object* v_bs_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2396_, v_i_2397_, v_bs_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___boxed(lean_object* v_as_2400_, lean_object* v_sz_2401_, lean_object* v_i_2402_, lean_object* v_bs_2403_){
_start:
{
size_t v_sz_boxed_2404_; size_t v_i_boxed_2405_; lean_object* v_res_2406_; 
v_sz_boxed_2404_ = lean_unbox_usize(v_sz_2401_);
lean_dec(v_sz_2401_);
v_i_boxed_2405_ = lean_unbox_usize(v_i_2402_);
lean_dec(v_i_2402_);
v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(v_as_2400_, v_sz_boxed_2404_, v_i_boxed_2405_, v_bs_2403_);
lean_dec_ref(v_as_2400_);
return v_res_2406_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object* v_x_2407_){
_start:
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = lean_unsigned_to_nat(0u);
v___x_2409_ = lean_nat_dec_eq(v_x_2407_, v___x_2408_);
if (v___x_2409_ == 0)
{
uint8_t v___x_2410_; 
v___x_2410_ = 1;
return v___x_2410_;
}
else
{
uint8_t v___x_2411_; 
v___x_2411_ = 0;
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object* v_x_2412_){
_start:
{
uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_res_2413_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_x_2412_);
lean_dec(v_x_2412_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(size_t v_sz_2415_, size_t v_i_2416_, lean_object* v_bs_2417_){
_start:
{
uint8_t v___x_2418_; 
v___x_2418_ = lean_usize_dec_lt(v_i_2416_, v_sz_2415_);
if (v___x_2418_ == 0)
{
return v_bs_2417_;
}
else
{
lean_object* v_v_2419_; lean_object* v___x_2420_; lean_object* v_bs_x27_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; size_t v___x_2426_; size_t v___x_2427_; lean_object* v___x_2428_; 
v_v_2419_ = lean_array_uget(v_bs_2417_, v_i_2416_);
v___x_2420_ = lean_unsigned_to_nat(0u);
v_bs_x27_2421_ = lean_array_uset(v_bs_2417_, v_i_2416_, v___x_2420_);
v___x_2422_ = lean_usize_to_nat(v_i_2416_);
v___x_2423_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v___x_2422_);
lean_dec(v___x_2422_);
v___x_2424_ = lean_box(v___x_2423_);
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v_v_2419_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = ((size_t)1ULL);
v___x_2427_ = lean_usize_add(v_i_2416_, v___x_2426_);
v___x_2428_ = lean_array_uset(v_bs_x27_2421_, v_i_2416_, v___x_2425_);
v_i_2416_ = v___x_2427_;
v_bs_2417_ = v___x_2428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg___boxed(lean_object* v_sz_2430_, lean_object* v_i_2431_, lean_object* v_bs_2432_){
_start:
{
size_t v_sz_boxed_2433_; size_t v_i_boxed_2434_; lean_object* v_res_2435_; 
v_sz_boxed_2433_ = lean_unbox_usize(v_sz_2430_);
lean_dec(v_sz_2430_);
v_i_boxed_2434_ = lean_unbox_usize(v_i_2431_);
lean_dec(v_i_2431_);
v_res_2435_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_boxed_2433_, v_i_boxed_2434_, v_bs_2432_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(lean_object* v_arr_2436_){
_start:
{
size_t v_sz_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v_sz_2437_ = lean_array_size(v_arr_2436_);
v___x_2438_ = ((size_t)0ULL);
v___x_2439_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2437_, v___x_2438_, v_arr_2436_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(lean_object* v_as_2440_, size_t v_sz_2441_, size_t v_i_2442_, lean_object* v_bs_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2441_, v_i_2442_, v_bs_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___boxed(lean_object* v_as_2445_, lean_object* v_sz_2446_, lean_object* v_i_2447_, lean_object* v_bs_2448_){
_start:
{
size_t v_sz_boxed_2449_; size_t v_i_boxed_2450_; lean_object* v_res_2451_; 
v_sz_boxed_2449_ = lean_unbox_usize(v_sz_2446_);
lean_dec(v_sz_2446_);
v_i_boxed_2450_ = lean_unbox_usize(v_i_2447_);
lean_dec(v_i_2447_);
v_res_2451_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(v_as_2445_, v_sz_boxed_2449_, v_i_boxed_2450_, v_bs_2448_);
lean_dec_ref(v_as_2445_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(lean_object* v_arr_2452_){
_start:
{
size_t v_sz_2453_; size_t v___x_2454_; lean_object* v___x_2455_; 
v_sz_2453_ = lean_array_size(v_arr_2452_);
v___x_2454_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2452_);
v___x_2455_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2452_, v_sz_2453_, v___x_2454_, v_arr_2452_);
lean_dec_ref(v_arr_2452_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(lean_object* v_symbols_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_monthLong_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_monthLong_2458_ = lean_ctor_get(v_symbols_2456_, 0);
lean_inc_ref(v_monthLong_2458_);
lean_dec_ref(v_symbols_2456_);
v___x_2459_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthLong_2458_);
v___x_2460_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2459_, v_a_2457_);
lean_dec_ref(v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object* v_symbols_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_monthShort_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_monthShort_2463_ = lean_ctor_get(v_symbols_2461_, 1);
lean_inc_ref(v_monthShort_2463_);
lean_dec_ref(v_symbols_2461_);
v___x_2464_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthShort_2463_);
v___x_2465_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2464_, v_a_2462_);
lean_dec_ref(v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(lean_object* v_symbols_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_monthNarrow_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_monthNarrow_2468_ = lean_ctor_get(v_symbols_2466_, 2);
lean_inc_ref(v_monthNarrow_2468_);
lean_dec_ref(v_symbols_2466_);
v___x_2469_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthNarrow_2468_);
v___x_2470_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2469_, v_a_2467_);
lean_dec_ref(v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(lean_object* v_symbols_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_weekdayLong_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v_weekdayLong_2473_ = lean_ctor_get(v_symbols_2471_, 3);
lean_inc_ref(v_weekdayLong_2473_);
lean_dec_ref(v_symbols_2471_);
v___x_2474_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayLong_2473_);
v___x_2475_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2474_, v_a_2472_);
lean_dec_ref(v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(lean_object* v_symbols_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_weekdayShort_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_weekdayShort_2478_ = lean_ctor_get(v_symbols_2476_, 4);
lean_inc_ref(v_weekdayShort_2478_);
lean_dec_ref(v_symbols_2476_);
v___x_2479_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayShort_2478_);
v___x_2480_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2479_, v_a_2477_);
lean_dec_ref(v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(lean_object* v_symbols_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_weekdayNarrow_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_weekdayNarrow_2483_ = lean_ctor_get(v_symbols_2481_, 5);
lean_inc_ref(v_weekdayNarrow_2483_);
lean_dec_ref(v_symbols_2481_);
v___x_2484_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayNarrow_2483_);
v___x_2485_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2484_, v_a_2482_);
lean_dec_ref(v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(lean_object* v_symbols_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_weekdayTwoLetter_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_weekdayTwoLetter_2488_ = lean_ctor_get(v_symbols_2486_, 6);
lean_inc_ref(v_weekdayTwoLetter_2488_);
lean_dec_ref(v_symbols_2486_);
v___x_2489_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayTwoLetter_2488_);
v___x_2490_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2489_, v_a_2487_);
lean_dec_ref(v___x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(lean_object* v_symbols_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_eraShort_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v_eraShort_2493_ = lean_ctor_get(v_symbols_2491_, 7);
lean_inc_ref(v_eraShort_2493_);
lean_dec_ref(v_symbols_2491_);
v___x_2494_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraShort_2493_);
v___x_2495_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2494_, v_a_2492_);
lean_dec_ref(v___x_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(lean_object* v_symbols_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_eraLong_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_eraLong_2498_ = lean_ctor_get(v_symbols_2496_, 8);
lean_inc_ref(v_eraLong_2498_);
lean_dec_ref(v_symbols_2496_);
v___x_2499_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraLong_2498_);
v___x_2500_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2499_, v_a_2497_);
lean_dec_ref(v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(lean_object* v_symbols_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v_eraNarrow_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_eraNarrow_2503_ = lean_ctor_get(v_symbols_2501_, 9);
lean_inc_ref(v_eraNarrow_2503_);
lean_dec_ref(v_symbols_2501_);
v___x_2504_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraNarrow_2503_);
v___x_2505_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2504_, v_a_2502_);
lean_dec_ref(v___x_2504_);
return v___x_2505_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = lean_unsigned_to_nat(3u);
v___x_2507_ = lean_nat_to_int(v___x_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber(lean_object* v_a_2508_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
lean_inc_ref(v_a_2508_);
v___x_2510_ = l_Std_Internal_Parsec_String_pstring(v___x_2509_, v_a_2508_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_pos_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2519_; 
lean_dec_ref(v_a_2508_);
v_pos_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v___x_2510_, 1);
lean_dec(v_unused_2520_);
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2519_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_pos_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2519_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2515_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 1, v___x_2515_);
v___x_2517_ = v___x_2513_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_pos_2511_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
else
{
lean_object* v_pos_2521_; lean_object* v_err_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2599_; 
v_pos_2521_ = lean_ctor_get(v___x_2510_, 0);
v_err_2522_ = lean_ctor_get(v___x_2510_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2524_ = v___x_2510_;
v_isShared_2525_ = v_isSharedCheck_2599_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_err_2522_);
lean_inc(v_pos_2521_);
lean_dec(v___x_2510_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2599_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v_snd_2526_; lean_object* v_snd_2527_; uint8_t v_decide_2528_; 
v_snd_2526_ = lean_ctor_get(v_a_2508_, 1);
lean_inc(v_snd_2526_);
lean_dec_ref(v_a_2508_);
v_snd_2527_ = lean_ctor_get(v_pos_2521_, 1);
v_decide_2528_ = lean_nat_dec_eq(v_snd_2526_, v_snd_2527_);
lean_dec(v_snd_2526_);
if (v_decide_2528_ == 0)
{
lean_object* v___x_2530_; 
if (v_isShared_2525_ == 0)
{
v___x_2530_ = v___x_2524_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_pos_2521_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_err_2522_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_inc(v_snd_2527_);
lean_del_object(v___x_2524_);
lean_dec(v_err_2522_);
v___x_2532_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
v___x_2533_ = l_Std_Internal_Parsec_String_pstring(v___x_2532_, v_pos_2521_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_pos_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_snd_2527_);
v_pos_2534_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; 
v_unused_2543_ = lean_ctor_get(v___x_2533_, 1);
lean_dec(v_unused_2543_);
v___x_2536_ = v___x_2533_;
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_pos_2534_);
lean_dec(v___x_2533_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 1, v___x_2538_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_pos_2534_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
lean_object* v_pos_2544_; lean_object* v_err_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2598_; 
v_pos_2544_ = lean_ctor_get(v___x_2533_, 0);
v_err_2545_ = lean_ctor_get(v___x_2533_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2547_ = v___x_2533_;
v_isShared_2548_ = v_isSharedCheck_2598_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_err_2545_);
lean_inc(v_pos_2544_);
lean_dec(v___x_2533_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2598_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_snd_2549_; uint8_t v_decide_2550_; 
v_snd_2549_ = lean_ctor_get(v_pos_2544_, 1);
v_decide_2550_ = lean_nat_dec_eq(v_snd_2527_, v_snd_2549_);
lean_dec(v_snd_2527_);
if (v_decide_2550_ == 0)
{
lean_object* v___x_2552_; 
if (v_isShared_2548_ == 0)
{
v___x_2552_ = v___x_2547_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_pos_2544_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_err_2545_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
else
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_inc(v_snd_2549_);
lean_del_object(v___x_2547_);
lean_dec(v_err_2545_);
v___x_2554_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
v___x_2555_ = l_Std_Internal_Parsec_String_pstring(v___x_2554_, v_pos_2544_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_pos_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2564_; 
lean_dec(v_snd_2549_);
v_pos_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v___x_2555_, 1);
lean_dec(v_unused_2565_);
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_pos_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2560_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 1, v___x_2560_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_pos_2556_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_object* v_pos_2566_; lean_object* v_err_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2597_; 
v_pos_2566_ = lean_ctor_get(v___x_2555_, 0);
v_err_2567_ = lean_ctor_get(v___x_2555_, 1);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2569_ = v___x_2555_;
v_isShared_2570_ = v_isSharedCheck_2597_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_err_2567_);
lean_inc(v_pos_2566_);
lean_dec(v___x_2555_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2597_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v_snd_2571_; uint8_t v_decide_2572_; 
v_snd_2571_ = lean_ctor_get(v_pos_2566_, 1);
v_decide_2572_ = lean_nat_dec_eq(v_snd_2549_, v_snd_2571_);
lean_dec(v_snd_2549_);
if (v_decide_2572_ == 0)
{
lean_object* v___x_2574_; 
if (v_isShared_2570_ == 0)
{
v___x_2574_ = v___x_2569_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_pos_2566_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_err_2567_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_del_object(v___x_2569_);
lean_dec(v_err_2567_);
v___x_2576_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
v___x_2577_ = l_Std_Internal_Parsec_String_pstring(v___x_2576_, v_pos_2566_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_pos_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2586_; 
v_pos_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v___x_2577_, 1);
lean_dec(v_unused_2587_);
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2586_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_pos_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2586_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2582_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 1, v___x_2582_);
v___x_2584_ = v___x_2580_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_pos_2578_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_object* v_pos_2588_; lean_object* v_err_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v_pos_2588_ = lean_ctor_get(v___x_2577_, 0);
v_err_2589_ = lean_ctor_get(v___x_2577_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2577_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_err_2589_);
lean_inc(v_pos_2588_);
lean_dec(v___x_2577_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_pos_2588_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_err_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(lean_object* v_symbols_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_quarterLong_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_quarterLong_2602_ = lean_ctor_get(v_symbols_2600_, 11);
lean_inc_ref(v_quarterLong_2602_);
lean_dec_ref(v_symbols_2600_);
v___x_2603_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterLong_2602_);
v___x_2604_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2603_, v_a_2601_);
lean_dec_ref(v___x_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(lean_object* v_symbols_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_quarterShort_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v_quarterShort_2607_ = lean_ctor_get(v_symbols_2605_, 10);
lean_inc_ref(v_quarterShort_2607_);
lean_dec_ref(v_symbols_2605_);
v___x_2608_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterShort_2607_);
v___x_2609_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2608_, v_a_2606_);
lean_dec_ref(v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(lean_object* v_symbols_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_quarterNarrow_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_quarterNarrow_2612_ = lean_ctor_get(v_symbols_2610_, 12);
lean_inc_ref(v_quarterNarrow_2612_);
lean_dec_ref(v_symbols_2610_);
v___x_2613_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterNarrow_2612_);
v___x_2614_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2613_, v_a_2611_);
lean_dec_ref(v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(lean_object* v_symbols_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v_amShort_2617_; lean_object* v_pmShort_2618_; lean_object* v___x_2619_; 
v_amShort_2617_ = lean_ctor_get(v_symbols_2615_, 13);
lean_inc_ref(v_amShort_2617_);
v_pmShort_2618_ = lean_ctor_get(v_symbols_2615_, 14);
lean_inc_ref(v_pmShort_2618_);
lean_dec_ref(v_symbols_2615_);
lean_inc_ref(v_a_2616_);
v___x_2619_ = l_Std_Internal_Parsec_String_pstring(v_amShort_2617_, v_a_2616_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_pos_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2629_; 
lean_dec_ref(v_pmShort_2618_);
lean_dec_ref(v_a_2616_);
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
v___x_2624_ = 0;
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
lean_object* v_pos_2631_; lean_object* v_err_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2663_; 
v_pos_2631_ = lean_ctor_get(v___x_2619_, 0);
v_err_2632_ = lean_ctor_get(v___x_2619_, 1);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2634_ = v___x_2619_;
v_isShared_2635_ = v_isSharedCheck_2663_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_err_2632_);
lean_inc(v_pos_2631_);
lean_dec(v___x_2619_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2663_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_snd_2636_; lean_object* v_snd_2637_; uint8_t v_decide_2638_; 
v_snd_2636_ = lean_ctor_get(v_a_2616_, 1);
lean_inc(v_snd_2636_);
lean_dec_ref(v_a_2616_);
v_snd_2637_ = lean_ctor_get(v_pos_2631_, 1);
v_decide_2638_ = lean_nat_dec_eq(v_snd_2636_, v_snd_2637_);
lean_dec(v_snd_2636_);
if (v_decide_2638_ == 0)
{
lean_object* v___x_2640_; 
lean_dec_ref(v_pmShort_2618_);
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
lean_del_object(v___x_2634_);
lean_dec(v_err_2632_);
v___x_2642_ = l_Std_Internal_Parsec_String_pstring(v_pmShort_2618_, v_pos_2631_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_pos_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2652_; 
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
v___x_2647_ = 1;
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
lean_object* v_pos_2654_; lean_object* v_err_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
v_pos_2654_ = lean_ctor_get(v___x_2642_, 0);
v_err_2655_ = lean_ctor_get(v___x_2642_, 1);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2642_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_err_2655_);
lean_inc(v_pos_2654_);
lean_dec(v___x_2642_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_pos_2654_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_err_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(lean_object* v_symbols_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_amLong_2666_; lean_object* v_pmLong_2667_; lean_object* v___x_2668_; 
v_amLong_2666_ = lean_ctor_get(v_symbols_2664_, 15);
lean_inc_ref(v_amLong_2666_);
v_pmLong_2667_ = lean_ctor_get(v_symbols_2664_, 16);
lean_inc_ref(v_pmLong_2667_);
lean_dec_ref(v_symbols_2664_);
lean_inc_ref(v_a_2665_);
v___x_2668_ = l_Std_Internal_Parsec_String_pstring(v_amLong_2666_, v_a_2665_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_pos_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v_pmLong_2667_);
lean_dec_ref(v_a_2665_);
v_pos_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v___x_2668_, 1);
lean_dec(v_unused_2679_);
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2678_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_pos_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2678_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2673_ = 0;
v___x_2674_ = lean_box(v___x_2673_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2674_);
v___x_2676_ = v___x_2671_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_pos_2669_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
else
{
lean_object* v_pos_2680_; lean_object* v_err_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2712_; 
v_pos_2680_ = lean_ctor_get(v___x_2668_, 0);
v_err_2681_ = lean_ctor_get(v___x_2668_, 1);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2683_ = v___x_2668_;
v_isShared_2684_ = v_isSharedCheck_2712_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_err_2681_);
lean_inc(v_pos_2680_);
lean_dec(v___x_2668_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2712_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v_snd_2685_; lean_object* v_snd_2686_; uint8_t v_decide_2687_; 
v_snd_2685_ = lean_ctor_get(v_a_2665_, 1);
lean_inc(v_snd_2685_);
lean_dec_ref(v_a_2665_);
v_snd_2686_ = lean_ctor_get(v_pos_2680_, 1);
v_decide_2687_ = lean_nat_dec_eq(v_snd_2685_, v_snd_2686_);
lean_dec(v_snd_2685_);
if (v_decide_2687_ == 0)
{
lean_object* v___x_2689_; 
lean_dec_ref(v_pmLong_2667_);
if (v_isShared_2684_ == 0)
{
v___x_2689_ = v___x_2683_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_pos_2680_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_err_2681_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
else
{
lean_object* v___x_2691_; 
lean_del_object(v___x_2683_);
lean_dec(v_err_2681_);
v___x_2691_ = l_Std_Internal_Parsec_String_pstring(v_pmLong_2667_, v_pos_2680_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_pos_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2701_; 
v_pos_2692_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; 
v_unused_2702_ = lean_ctor_get(v___x_2691_, 1);
lean_dec(v_unused_2702_);
v___x_2694_ = v___x_2691_;
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_pos_2692_);
lean_dec(v___x_2691_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2696_ = 1;
v___x_2697_ = lean_box(v___x_2696_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 1, v___x_2697_);
v___x_2699_ = v___x_2694_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_pos_2692_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
else
{
lean_object* v_pos_2703_; lean_object* v_err_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
v_pos_2703_ = lean_ctor_get(v___x_2691_, 0);
v_err_2704_ = lean_ctor_get(v___x_2691_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2691_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_err_2704_);
lean_inc(v_pos_2703_);
lean_dec(v___x_2691_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_pos_2703_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_err_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(lean_object* v_symbols_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_amNarrow_2715_; lean_object* v_pmNarrow_2716_; lean_object* v___x_2717_; 
v_amNarrow_2715_ = lean_ctor_get(v_symbols_2713_, 17);
lean_inc_ref(v_amNarrow_2715_);
v_pmNarrow_2716_ = lean_ctor_get(v_symbols_2713_, 18);
lean_inc_ref(v_pmNarrow_2716_);
lean_dec_ref(v_symbols_2713_);
lean_inc_ref(v_a_2714_);
v___x_2717_ = l_Std_Internal_Parsec_String_pstring(v_amNarrow_2715_, v_a_2714_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_pos_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v_pmNarrow_2716_);
lean_dec_ref(v_a_2714_);
v_pos_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; 
v_unused_2728_ = lean_ctor_get(v___x_2717_, 1);
lean_dec(v_unused_2728_);
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2727_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_pos_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2727_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2722_ = 0;
v___x_2723_ = lean_box(v___x_2722_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 1, v___x_2723_);
v___x_2725_ = v___x_2720_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_pos_2718_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
else
{
lean_object* v_pos_2729_; lean_object* v_err_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2761_; 
v_pos_2729_ = lean_ctor_get(v___x_2717_, 0);
v_err_2730_ = lean_ctor_get(v___x_2717_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2732_ = v___x_2717_;
v_isShared_2733_ = v_isSharedCheck_2761_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_err_2730_);
lean_inc(v_pos_2729_);
lean_dec(v___x_2717_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2761_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v_snd_2734_; lean_object* v_snd_2735_; uint8_t v_decide_2736_; 
v_snd_2734_ = lean_ctor_get(v_a_2714_, 1);
lean_inc(v_snd_2734_);
lean_dec_ref(v_a_2714_);
v_snd_2735_ = lean_ctor_get(v_pos_2729_, 1);
v_decide_2736_ = lean_nat_dec_eq(v_snd_2734_, v_snd_2735_);
lean_dec(v_snd_2734_);
if (v_decide_2736_ == 0)
{
lean_object* v___x_2738_; 
lean_dec_ref(v_pmNarrow_2716_);
if (v_isShared_2733_ == 0)
{
v___x_2738_ = v___x_2732_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_pos_2729_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_err_2730_);
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
lean_del_object(v___x_2732_);
lean_dec(v_err_2730_);
v___x_2740_ = l_Std_Internal_Parsec_String_pstring(v_pmNarrow_2716_, v_pos_2729_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(lean_object* v_dp_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v_am_2764_; lean_object* v_pm_2765_; lean_object* v_noon_2766_; lean_object* v_midnight_2767_; lean_object* v___x_2768_; 
v_am_2764_ = lean_ctor_get(v_dp_2762_, 0);
lean_inc_ref(v_am_2764_);
v_pm_2765_ = lean_ctor_get(v_dp_2762_, 1);
lean_inc_ref(v_pm_2765_);
v_noon_2766_ = lean_ctor_get(v_dp_2762_, 2);
lean_inc_ref(v_noon_2766_);
v_midnight_2767_ = lean_ctor_get(v_dp_2762_, 3);
lean_inc_ref(v_midnight_2767_);
lean_dec_ref(v_dp_2762_);
lean_inc_ref(v_a_2763_);
v___x_2768_ = l_Std_Internal_Parsec_String_pstring(v_midnight_2767_, v_a_2763_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_pos_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2778_; 
lean_dec_ref(v_noon_2766_);
lean_dec_ref(v_pm_2765_);
lean_dec_ref(v_am_2764_);
lean_dec_ref(v_a_2763_);
v_pos_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2778_ == 0)
{
lean_object* v_unused_2779_; 
v_unused_2779_ = lean_ctor_get(v___x_2768_, 1);
lean_dec(v_unused_2779_);
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2778_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_pos_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2778_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
uint8_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2773_ = 3;
v___x_2774_ = lean_box(v___x_2773_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 1, v___x_2774_);
v___x_2776_ = v___x_2771_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_pos_2769_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
else
{
lean_object* v_pos_2780_; lean_object* v_err_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2858_; 
v_pos_2780_ = lean_ctor_get(v___x_2768_, 0);
v_err_2781_ = lean_ctor_get(v___x_2768_, 1);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2783_ = v___x_2768_;
v_isShared_2784_ = v_isSharedCheck_2858_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_err_2781_);
lean_inc(v_pos_2780_);
lean_dec(v___x_2768_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2858_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v_snd_2785_; lean_object* v_snd_2786_; uint8_t v_decide_2787_; 
v_snd_2785_ = lean_ctor_get(v_a_2763_, 1);
lean_inc(v_snd_2785_);
lean_dec_ref(v_a_2763_);
v_snd_2786_ = lean_ctor_get(v_pos_2780_, 1);
v_decide_2787_ = lean_nat_dec_eq(v_snd_2785_, v_snd_2786_);
lean_dec(v_snd_2785_);
if (v_decide_2787_ == 0)
{
lean_object* v___x_2789_; 
lean_dec_ref(v_noon_2766_);
lean_dec_ref(v_pm_2765_);
lean_dec_ref(v_am_2764_);
if (v_isShared_2784_ == 0)
{
v___x_2789_ = v___x_2783_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_pos_2780_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_err_2781_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
else
{
lean_object* v___x_2791_; 
lean_inc(v_snd_2786_);
lean_del_object(v___x_2783_);
lean_dec(v_err_2781_);
v___x_2791_ = l_Std_Internal_Parsec_String_pstring(v_noon_2766_, v_pos_2780_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_pos_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v_snd_2786_);
lean_dec_ref(v_pm_2765_);
lean_dec_ref(v_am_2764_);
v_pos_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2801_ == 0)
{
lean_object* v_unused_2802_; 
v_unused_2802_ = lean_ctor_get(v___x_2791_, 1);
lean_dec(v_unused_2802_);
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2801_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_pos_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2801_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
uint8_t v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2796_ = 2;
v___x_2797_ = lean_box(v___x_2796_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 1, v___x_2797_);
v___x_2799_ = v___x_2794_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_pos_2792_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
else
{
lean_object* v_pos_2803_; lean_object* v_err_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2857_; 
v_pos_2803_ = lean_ctor_get(v___x_2791_, 0);
v_err_2804_ = lean_ctor_get(v___x_2791_, 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2806_ = v___x_2791_;
v_isShared_2807_ = v_isSharedCheck_2857_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_err_2804_);
lean_inc(v_pos_2803_);
lean_dec(v___x_2791_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2857_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v_snd_2808_; uint8_t v_decide_2809_; 
v_snd_2808_ = lean_ctor_get(v_pos_2803_, 1);
v_decide_2809_ = lean_nat_dec_eq(v_snd_2786_, v_snd_2808_);
lean_dec(v_snd_2786_);
if (v_decide_2809_ == 0)
{
lean_object* v___x_2811_; 
lean_dec_ref(v_pm_2765_);
lean_dec_ref(v_am_2764_);
if (v_isShared_2807_ == 0)
{
v___x_2811_ = v___x_2806_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_pos_2803_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_err_2804_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
else
{
lean_object* v___x_2813_; 
lean_inc(v_snd_2808_);
lean_del_object(v___x_2806_);
lean_dec(v_err_2804_);
v___x_2813_ = l_Std_Internal_Parsec_String_pstring(v_am_2764_, v_pos_2803_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_pos_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_snd_2808_);
lean_dec_ref(v_pm_2765_);
v_pos_2814_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2813_, 1);
lean_dec(v_unused_2824_);
v___x_2816_ = v___x_2813_;
v_isShared_2817_ = v_isSharedCheck_2823_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_pos_2814_);
lean_dec(v___x_2813_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2823_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
uint8_t v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2818_ = 0;
v___x_2819_ = lean_box(v___x_2818_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 1, v___x_2819_);
v___x_2821_ = v___x_2816_;
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
lean_object* v_pos_2825_; lean_object* v_err_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2856_; 
v_pos_2825_ = lean_ctor_get(v___x_2813_, 0);
v_err_2826_ = lean_ctor_get(v___x_2813_, 1);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2828_ = v___x_2813_;
v_isShared_2829_ = v_isSharedCheck_2856_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_err_2826_);
lean_inc(v_pos_2825_);
lean_dec(v___x_2813_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2856_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v_snd_2830_; uint8_t v_decide_2831_; 
v_snd_2830_ = lean_ctor_get(v_pos_2825_, 1);
v_decide_2831_ = lean_nat_dec_eq(v_snd_2808_, v_snd_2830_);
lean_dec(v_snd_2808_);
if (v_decide_2831_ == 0)
{
lean_object* v___x_2833_; 
lean_dec_ref(v_pm_2765_);
if (v_isShared_2829_ == 0)
{
v___x_2833_ = v___x_2828_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_pos_2825_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_err_2826_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
else
{
lean_object* v___x_2835_; 
lean_del_object(v___x_2828_);
lean_dec(v_err_2826_);
v___x_2835_ = l_Std_Internal_Parsec_String_pstring(v_pm_2765_, v_pos_2825_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_pos_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2845_; 
v_pos_2836_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v___x_2835_, 1);
lean_dec(v_unused_2846_);
v___x_2838_ = v___x_2835_;
v_isShared_2839_ = v_isSharedCheck_2845_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_pos_2836_);
lean_dec(v___x_2835_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2845_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
uint8_t v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2840_ = 1;
v___x_2841_ = lean_box(v___x_2840_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v___x_2841_);
v___x_2843_ = v___x_2838_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_pos_2836_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_pos_2847_; lean_object* v_err_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
v_pos_2847_ = lean_ctor_get(v___x_2835_, 0);
v_err_2848_ = lean_ctor_get(v___x_2835_, 1);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2835_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_err_2848_);
lean_inc(v_pos_2847_);
lean_dec(v___x_2835_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_pos_2847_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_err_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(lean_object* v_arr_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v_pairs_2898_; lean_object* v___x_2899_; 
v___x_2861_ = lean_unsigned_to_nat(6u);
v___x_2862_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0);
v___x_2863_ = lean_array_fget_borrowed(v_arr_2859_, v___x_2862_);
v___x_2864_ = 0;
v___x_2865_ = lean_box(v___x_2864_);
lean_inc(v___x_2863_);
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2863_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1);
v___x_2868_ = lean_array_fget_borrowed(v_arr_2859_, v___x_2867_);
v___x_2869_ = 1;
v___x_2870_ = lean_box(v___x_2869_);
lean_inc(v___x_2868_);
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2868_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2);
v___x_2873_ = lean_array_fget_borrowed(v_arr_2859_, v___x_2872_);
v___x_2874_ = 2;
v___x_2875_ = lean_box(v___x_2874_);
lean_inc(v___x_2873_);
v___x_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2873_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3);
v___x_2878_ = lean_array_fget_borrowed(v_arr_2859_, v___x_2877_);
v___x_2879_ = 3;
v___x_2880_ = lean_box(v___x_2879_);
lean_inc(v___x_2878_);
v___x_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2878_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4);
v___x_2883_ = lean_array_fget_borrowed(v_arr_2859_, v___x_2882_);
v___x_2884_ = 4;
v___x_2885_ = lean_box(v___x_2884_);
lean_inc(v___x_2883_);
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2883_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5);
v___x_2888_ = lean_array_fget_borrowed(v_arr_2859_, v___x_2887_);
v___x_2889_ = 5;
v___x_2890_ = lean_box(v___x_2889_);
lean_inc(v___x_2888_);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2888_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = lean_mk_empty_array_with_capacity(v___x_2861_);
v___x_2893_ = lean_array_push(v___x_2892_, v___x_2866_);
v___x_2894_ = lean_array_push(v___x_2893_, v___x_2871_);
v___x_2895_ = lean_array_push(v___x_2894_, v___x_2876_);
v___x_2896_ = lean_array_push(v___x_2895_, v___x_2881_);
v___x_2897_ = lean_array_push(v___x_2896_, v___x_2886_);
v_pairs_2898_ = lean_array_push(v___x_2897_, v___x_2891_);
v___x_2899_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2898_, v_a_2860_);
lean_dec_ref(v_pairs_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom___boxed(lean_object* v_arr_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_arr_2900_, v_a_2901_);
lean_dec_ref(v_arr_2900_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(lean_object* v_parse_2903_, lean_object* v_size_2904_, lean_object* v_acc_2905_, lean_object* v_count_2906_, lean_object* v_a_2907_){
_start:
{
uint8_t v___x_2908_; 
v___x_2908_ = lean_nat_dec_le(v_size_2904_, v_count_2906_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; 
lean_inc_ref(v_parse_2903_);
v___x_2909_ = lean_apply_1(v_parse_2903_, v_a_2907_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_pos_2910_; lean_object* v_res_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v_pos_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_pos_2910_);
v_res_2911_ = lean_ctor_get(v___x_2909_, 1);
lean_inc(v_res_2911_);
lean_dec_ref_known(v___x_2909_, 2);
v___x_2912_ = lean_array_push(v_acc_2905_, v_res_2911_);
v___x_2913_ = lean_unsigned_to_nat(1u);
v___x_2914_ = lean_nat_add(v_count_2906_, v___x_2913_);
lean_dec(v_count_2906_);
v_acc_2905_ = v___x_2912_;
v_count_2906_ = v___x_2914_;
v_a_2907_ = v_pos_2910_;
goto _start;
}
else
{
lean_object* v_pos_2916_; lean_object* v_err_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v_count_2906_);
lean_dec_ref(v_acc_2905_);
lean_dec_ref(v_parse_2903_);
v_pos_2916_ = lean_ctor_get(v___x_2909_, 0);
v_err_2917_ = lean_ctor_get(v___x_2909_, 1);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2909_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_err_2917_);
lean_inc(v_pos_2916_);
lean_dec(v___x_2909_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_pos_2916_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_err_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v___x_2925_; 
lean_dec(v_count_2906_);
lean_dec_ref(v_parse_2903_);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v_a_2907_);
lean_ctor_set(v___x_2925_, 1, v_acc_2905_);
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg___boxed(lean_object* v_parse_2926_, lean_object* v_size_2927_, lean_object* v_acc_2928_, lean_object* v_count_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2926_, v_size_2927_, v_acc_2928_, v_count_2929_, v_a_2930_);
lean_dec(v_size_2927_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(lean_object* v_00_u03b1_2932_, lean_object* v_parse_2933_, lean_object* v_size_2934_, lean_object* v_acc_2935_, lean_object* v_count_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2933_, v_size_2934_, v_acc_2935_, v_count_2936_, v_a_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___boxed(lean_object* v_00_u03b1_2939_, lean_object* v_parse_2940_, lean_object* v_size_2941_, lean_object* v_acc_2942_, lean_object* v_count_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(v_00_u03b1_2939_, v_parse_2940_, v_size_2941_, v_acc_2942_, v_count_2943_, v_a_2944_);
lean_dec(v_size_2941_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(lean_object* v_parse_2948_, lean_object* v_size_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0));
v___x_2952_ = lean_unsigned_to_nat(12u);
v___x_2953_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2948_, v_size_2949_, v___x_2951_, v___x_2952_, v_a_2950_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___boxed(lean_object* v_parse_2954_, lean_object* v_size_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2954_, v_size_2955_, v_a_2956_);
lean_dec(v_size_2955_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly(lean_object* v_00_u03b1_2958_, lean_object* v_parse_2959_, lean_object* v_size_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2959_, v_size_2960_, v_a_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___boxed(lean_object* v_00_u03b1_2963_, lean_object* v_parse_2964_, lean_object* v_size_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly(v_00_u03b1_2963_, v_parse_2964_, v_size_2965_, v_a_2966_);
lean_dec(v_size_2965_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object* v_parse_2968_, lean_object* v_size_2969_, lean_object* v_acc_2970_, lean_object* v_count_2971_, lean_object* v_a_2972_){
_start:
{
uint8_t v___x_2973_; 
v___x_2973_ = lean_nat_dec_le(v_size_2969_, v_count_2971_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_inc_ref(v_parse_2968_);
v___x_2974_ = lean_apply_1(v_parse_2968_, v_a_2972_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_pos_2975_; lean_object* v_res_2976_; uint32_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_pos_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_pos_2975_);
v_res_2976_ = lean_ctor_get(v___x_2974_, 1);
lean_inc(v_res_2976_);
lean_dec_ref_known(v___x_2974_, 2);
v___x_2977_ = lean_unbox_uint32(v_res_2976_);
lean_dec(v_res_2976_);
v___x_2978_ = lean_string_push(v_acc_2970_, v___x_2977_);
v___x_2979_ = lean_unsigned_to_nat(1u);
v___x_2980_ = lean_nat_add(v_count_2971_, v___x_2979_);
lean_dec(v_count_2971_);
v_acc_2970_ = v___x_2978_;
v_count_2971_ = v___x_2980_;
v_a_2972_ = v_pos_2975_;
goto _start;
}
else
{
lean_object* v_pos_2982_; lean_object* v_err_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v_count_2971_);
lean_dec_ref(v_acc_2970_);
lean_dec_ref(v_parse_2968_);
v_pos_2982_ = lean_ctor_get(v___x_2974_, 0);
v_err_2983_ = lean_ctor_get(v___x_2974_, 1);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2974_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_err_2983_);
lean_inc(v_pos_2982_);
lean_dec(v___x_2974_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_pos_2982_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_err_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_object* v___x_2991_; 
lean_dec(v_count_2971_);
lean_dec_ref(v_parse_2968_);
v___x_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2991_, 0, v_a_2972_);
lean_ctor_set(v___x_2991_, 1, v_acc_2970_);
return v___x_2991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object* v_parse_2992_, lean_object* v_size_2993_, lean_object* v_acc_2994_, lean_object* v_count_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2992_, v_size_2993_, v_acc_2994_, v_count_2995_, v_a_2996_);
lean_dec(v_size_2993_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object* v_parse_2998_, lean_object* v_size_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3001_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3002_ = lean_unsigned_to_nat(0u);
v___x_3003_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2998_, v_size_2999_, v___x_3001_, v___x_3002_, v_a_3000_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object* v_parse_3004_, lean_object* v_size_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v_parse_3004_, v_size_3005_, v_a_3006_);
lean_dec(v_size_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object* v_parser_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v_pos_3011_; lean_object* v_res_3012_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
lean_inc_ref(v_a_3009_);
v___x_3045_ = l_Std_Internal_Parsec_String_pstring(v___x_3044_, v_a_3009_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_pos_3046_; lean_object* v_res_3047_; lean_object* v___x_3048_; 
lean_dec_ref(v_a_3009_);
v_pos_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_pos_3046_);
v_res_3047_ = lean_ctor_get(v___x_3045_, 1);
lean_inc(v_res_3047_);
lean_dec_ref_known(v___x_3045_, 2);
v___x_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3048_, 0, v_res_3047_);
v_pos_3011_ = v_pos_3046_;
v_res_3012_ = v___x_3048_;
goto v___jp_3010_;
}
else
{
lean_object* v_pos_3049_; lean_object* v_err_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3061_; 
v_pos_3049_ = lean_ctor_get(v___x_3045_, 0);
v_err_3050_ = lean_ctor_get(v___x_3045_, 1);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3052_ = v___x_3045_;
v_isShared_3053_ = v_isSharedCheck_3061_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_err_3050_);
lean_inc(v_pos_3049_);
lean_dec(v___x_3045_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3061_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v_snd_3054_; lean_object* v_snd_3055_; uint8_t v_decide_3056_; 
v_snd_3054_ = lean_ctor_get(v_a_3009_, 1);
lean_inc(v_snd_3054_);
lean_dec_ref(v_a_3009_);
v_snd_3055_ = lean_ctor_get(v_pos_3049_, 1);
v_decide_3056_ = lean_nat_dec_eq(v_snd_3054_, v_snd_3055_);
lean_dec(v_snd_3054_);
if (v_decide_3056_ == 0)
{
lean_object* v___x_3058_; 
lean_dec_ref(v_parser_3008_);
if (v_isShared_3053_ == 0)
{
v___x_3058_ = v___x_3052_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_pos_3049_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_err_3050_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
else
{
lean_object* v___x_3060_; 
lean_del_object(v___x_3052_);
lean_dec(v_err_3050_);
v___x_3060_ = lean_box(0);
v_pos_3011_ = v_pos_3049_;
v_res_3012_ = v___x_3060_;
goto v___jp_3010_;
}
}
}
v___jp_3010_:
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_apply_1(v_parser_3008_, v_pos_3011_);
if (lean_obj_tag(v___x_3013_) == 0)
{
if (lean_obj_tag(v_res_3012_) == 0)
{
lean_object* v_pos_3014_; lean_object* v_res_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3023_; 
v_pos_3014_ = lean_ctor_get(v___x_3013_, 0);
v_res_3015_ = lean_ctor_get(v___x_3013_, 1);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3017_ = v___x_3013_;
v_isShared_3018_ = v_isSharedCheck_3023_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_res_3015_);
lean_inc(v_pos_3014_);
lean_dec(v___x_3013_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3023_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3019_ = lean_nat_to_int(v_res_3015_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 1, v___x_3019_);
v___x_3021_ = v___x_3017_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_pos_3014_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
else
{
lean_object* v_pos_3024_; lean_object* v_res_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref_known(v_res_3012_, 1);
v_pos_3024_ = lean_ctor_get(v___x_3013_, 0);
v_res_3025_ = lean_ctor_get(v___x_3013_, 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3027_ = v___x_3013_;
v_isShared_3028_ = v_isSharedCheck_3034_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_res_3025_);
lean_inc(v_pos_3024_);
lean_dec(v___x_3013_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3034_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3029_ = lean_nat_to_int(v_res_3025_);
v___x_3030_ = lean_int_neg(v___x_3029_);
lean_dec(v___x_3029_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 1, v___x_3030_);
v___x_3032_ = v___x_3027_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_pos_3024_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3030_);
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
else
{
lean_object* v_pos_3035_; lean_object* v_err_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v_res_3012_);
v_pos_3035_ = lean_ctor_get(v___x_3013_, 0);
v_err_3036_ = lean_ctor_get(v___x_3013_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3013_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_err_3036_);
lean_inc(v_pos_3035_);
lean_dec(v___x_3013_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_pos_3035_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_err_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___lam__0(lean_object* v___y_3062_){
_start:
{
lean_object* v_fst_3066_; lean_object* v_snd_3067_; lean_object* v___x_3068_; uint8_t v_decide_3069_; 
v_fst_3066_ = lean_ctor_get(v___y_3062_, 0);
v_snd_3067_ = lean_ctor_get(v___y_3062_, 1);
v___x_3068_ = lean_string_utf8_byte_size(v_fst_3066_);
v_decide_3069_ = lean_nat_dec_eq(v_snd_3067_, v___x_3068_);
if (v_decide_3069_ == 0)
{
uint32_t v_c_3070_; lean_object* v___x_3071_; lean_object* v_it_x27_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; uint32_t v___x_3075_; uint8_t v___x_3076_; 
v_c_3070_ = lean_string_utf8_get_fast(v_fst_3066_, v_snd_3067_);
v___x_3071_ = lean_string_utf8_next_fast(v_fst_3066_, v_snd_3067_);
lean_inc(v_fst_3066_);
v_it_x27_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3072_, 0, v_fst_3066_);
lean_ctor_set(v_it_x27_3072_, 1, v___x_3071_);
v___x_3073_ = lean_box_uint32(v_c_3070_);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_it_x27_3072_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = 48;
v___x_3076_ = lean_uint32_dec_le(v___x_3075_, v_c_3070_);
if (v___x_3076_ == 0)
{
lean_dec_ref_known(v___x_3074_, 2);
goto v___jp_3063_;
}
else
{
uint32_t v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = 57;
v___x_3078_ = lean_uint32_dec_le(v_c_3070_, v___x_3077_);
if (v___x_3078_ == 0)
{
lean_dec_ref_known(v___x_3074_, 2);
goto v___jp_3063_;
}
else
{
lean_dec_ref(v___y_3062_);
return v___x_3074_;
}
}
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___y_3062_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
return v___x_3080_;
}
v___jp_3063_:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___y_3062_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
return v___x_3065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object* v_size_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v___f_3084_; lean_object* v___x_3085_; 
v___f_3084_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3085_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3084_, v_size_3082_, v_a_3083_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_pos_3086_; lean_object* v_res_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3098_; 
v_pos_3086_ = lean_ctor_get(v___x_3085_, 0);
v_res_3087_ = lean_ctor_get(v___x_3085_, 1);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3089_ = v___x_3085_;
v_isShared_3090_ = v_isSharedCheck_3098_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_res_3087_);
lean_inc(v_pos_3086_);
lean_dec(v___x_3085_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3098_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3091_ = lean_unsigned_to_nat(0u);
v___x_3092_ = lean_string_utf8_byte_size(v_res_3087_);
v___x_3093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3093_, 0, v_res_3087_);
lean_ctor_set(v___x_3093_, 1, v___x_3091_);
lean_ctor_set(v___x_3093_, 2, v___x_3092_);
v___x_3094_ = l_String_Slice_toNat_x21(v___x_3093_);
lean_dec_ref_known(v___x_3093_, 3);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 1, v___x_3094_);
v___x_3096_ = v___x_3089_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_pos_3086_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
lean_object* v_pos_3099_; lean_object* v_err_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
v_pos_3099_ = lean_ctor_get(v___x_3085_, 0);
v_err_3100_ = lean_ctor_get(v___x_3085_, 1);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3085_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_err_3100_);
lean_inc(v_pos_3099_);
lean_dec(v___x_3085_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_pos_3099_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v_err_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed(lean_object* v_size_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3108_, v_a_3109_);
lean_dec(v_size_3108_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object* v_acc_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_fst_3113_; lean_object* v_snd_3114_; lean_object* v_pos_3116_; lean_object* v_snd_3117_; lean_object* v_err_3118_; lean_object* v___x_3124_; uint8_t v_decide_3125_; 
v_fst_3113_ = lean_ctor_get(v_a_3112_, 0);
v_snd_3114_ = lean_ctor_get(v_a_3112_, 1);
lean_inc(v_snd_3114_);
v___x_3124_ = lean_string_utf8_byte_size(v_fst_3113_);
v_decide_3125_ = lean_nat_dec_eq(v_snd_3114_, v___x_3124_);
if (v_decide_3125_ == 0)
{
uint32_t v_c_3126_; uint32_t v___x_3127_; uint8_t v___x_3128_; 
v_c_3126_ = lean_string_utf8_get_fast(v_fst_3113_, v_snd_3114_);
v___x_3127_ = 48;
v___x_3128_ = lean_uint32_dec_le(v___x_3127_, v_c_3126_);
if (v___x_3128_ == 0)
{
goto v___jp_3122_;
}
else
{
uint32_t v___x_3129_; uint8_t v___x_3130_; 
v___x_3129_ = 57;
v___x_3130_ = lean_uint32_dec_le(v_c_3126_, v___x_3129_);
if (v___x_3130_ == 0)
{
goto v___jp_3122_;
}
else
{
lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3140_; 
lean_inc(v_fst_3113_);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_a_3112_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; lean_object* v_unused_3142_; 
v_unused_3141_ = lean_ctor_get(v_a_3112_, 1);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v_a_3112_, 0);
lean_dec(v_unused_3142_);
v___x_3132_ = v_a_3112_;
v_isShared_3133_ = v_isSharedCheck_3140_;
goto v_resetjp_3131_;
}
else
{
lean_dec(v_a_3112_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3140_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v_it_x27_3136_; 
v___x_3134_ = lean_string_utf8_next_fast(v_fst_3113_, v_snd_3114_);
lean_dec(v_snd_3114_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 1, v___x_3134_);
v_it_x27_3136_ = v___x_3132_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_fst_3113_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_3134_);
v_it_x27_3136_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3137_; 
v___x_3137_ = lean_string_push(v_acc_3111_, v_c_3126_);
v_acc_3111_ = v___x_3137_;
v_a_3112_ = v_it_x27_3136_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_3143_; 
v___x_3143_ = lean_box(0);
lean_inc(v_snd_3114_);
v_pos_3116_ = v_a_3112_;
v_snd_3117_ = v_snd_3114_;
v_err_3118_ = v___x_3143_;
goto v___jp_3115_;
}
v___jp_3115_:
{
uint8_t v_decide_3119_; 
v_decide_3119_ = lean_nat_dec_eq(v_snd_3114_, v_snd_3117_);
lean_dec(v_snd_3117_);
lean_dec(v_snd_3114_);
if (v_decide_3119_ == 0)
{
lean_object* v___x_3120_; 
lean_dec_ref(v_acc_3111_);
lean_inc(v_err_3118_);
v___x_3120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3120_, 0, v_pos_3116_);
lean_ctor_set(v___x_3120_, 1, v_err_3118_);
return v___x_3120_;
}
else
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3121_, 0, v_pos_3116_);
lean_ctor_set(v___x_3121_, 1, v_acc_3111_);
return v___x_3121_;
}
}
v___jp_3122_:
{
lean_object* v___x_3123_; 
v___x_3123_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3114_);
v_pos_3116_ = v_a_3112_;
v_snd_3117_ = v_snd_3114_;
v_err_3118_ = v___x_3123_;
goto v___jp_3115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object* v_size_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_pos_3147_; lean_object* v_res_3148_; lean_object* v___y_3155_; lean_object* v___f_3167_; lean_object* v___x_3168_; 
v___f_3167_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3168_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3167_, v_size_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_pos_3169_; lean_object* v_res_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_pos_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_pos_3169_);
v_res_3170_ = lean_ctor_get(v___x_3168_, 1);
lean_inc(v_res_3170_);
lean_dec_ref_known(v___x_3168_, 2);
v___x_3171_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3172_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(v___x_3171_, v_pos_3169_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_pos_3173_; lean_object* v_res_3174_; lean_object* v___x_3175_; 
v_pos_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_pos_3173_);
v_res_3174_ = lean_ctor_get(v___x_3172_, 1);
lean_inc(v_res_3174_);
lean_dec_ref_known(v___x_3172_, 2);
v___x_3175_ = lean_string_append(v_res_3170_, v_res_3174_);
lean_dec(v_res_3174_);
v_pos_3147_ = v_pos_3173_;
v_res_3148_ = v___x_3175_;
goto v___jp_3146_;
}
else
{
lean_dec(v_res_3170_);
v___y_3155_ = v___x_3172_;
goto v___jp_3154_;
}
}
else
{
v___y_3155_ = v___x_3168_;
goto v___jp_3154_;
}
v___jp_3146_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3149_ = lean_unsigned_to_nat(0u);
v___x_3150_ = lean_string_utf8_byte_size(v_res_3148_);
v___x_3151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3151_, 0, v_res_3148_);
lean_ctor_set(v___x_3151_, 1, v___x_3149_);
lean_ctor_set(v___x_3151_, 2, v___x_3150_);
v___x_3152_ = l_String_Slice_toNat_x21(v___x_3151_);
lean_dec_ref_known(v___x_3151_, 3);
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v_pos_3147_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
return v___x_3153_;
}
v___jp_3154_:
{
if (lean_obj_tag(v___y_3155_) == 0)
{
lean_object* v_pos_3156_; lean_object* v_res_3157_; 
v_pos_3156_ = lean_ctor_get(v___y_3155_, 0);
lean_inc(v_pos_3156_);
v_res_3157_ = lean_ctor_get(v___y_3155_, 1);
lean_inc(v_res_3157_);
lean_dec_ref_known(v___y_3155_, 2);
v_pos_3147_ = v_pos_3156_;
v_res_3148_ = v_res_3157_;
goto v___jp_3146_;
}
else
{
lean_object* v_pos_3158_; lean_object* v_err_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
v_pos_3158_ = lean_ctor_get(v___y_3155_, 0);
v_err_3159_ = lean_ctor_get(v___y_3155_, 1);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___y_3155_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___y_3155_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_err_3159_);
lean_inc(v_pos_3158_);
lean_dec(v___y_3155_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_pos_3158_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_err_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object* v_size_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v_size_3176_, v_a_3177_);
lean_dec(v_size_3176_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object* v_size_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v___x_3181_; uint8_t v___x_3182_; 
v___x_3181_ = lean_unsigned_to_nat(1u);
v___x_3182_ = lean_nat_dec_eq(v_size_3179_, v___x_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; 
v___x_3183_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3179_, v_a_3180_);
return v___x_3183_;
}
else
{
lean_object* v___x_3184_; 
v___x_3184_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3181_, v_a_3180_);
return v___x_3184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed(lean_object* v_size_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_size_3185_, v_a_3186_);
lean_dec(v_size_3185_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object* v_size_3188_, lean_object* v_pad_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v_pos_3192_; lean_object* v_res_3193_; lean_object* v___f_3199_; lean_object* v___x_3200_; 
v___f_3199_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3200_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3199_, v_size_3188_, v_a_3190_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_pos_3201_; lean_object* v_res_3202_; uint32_t v___x_3203_; lean_object* v___x_3204_; 
v_pos_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_pos_3201_);
v_res_3202_ = lean_ctor_get(v___x_3200_, 1);
lean_inc(v_res_3202_);
lean_dec_ref_known(v___x_3200_, 2);
v___x_3203_ = 48;
v___x_3204_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_pad_3189_, v___x_3203_, v_res_3202_);
v_pos_3192_ = v_pos_3201_;
v_res_3193_ = v___x_3204_;
goto v___jp_3191_;
}
else
{
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_pos_3205_; lean_object* v_res_3206_; 
v_pos_3205_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_pos_3205_);
v_res_3206_ = lean_ctor_get(v___x_3200_, 1);
lean_inc(v_res_3206_);
lean_dec_ref_known(v___x_3200_, 2);
v_pos_3192_ = v_pos_3205_;
v_res_3193_ = v_res_3206_;
goto v___jp_3191_;
}
else
{
lean_object* v_pos_3207_; lean_object* v_err_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
v_pos_3207_ = lean_ctor_get(v___x_3200_, 0);
v_err_3208_ = lean_ctor_get(v___x_3200_, 1);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3200_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_err_3208_);
lean_inc(v_pos_3207_);
lean_dec(v___x_3200_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_pos_3207_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_err_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
v___jp_3191_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3194_ = lean_unsigned_to_nat(0u);
v___x_3195_ = lean_string_utf8_byte_size(v_res_3193_);
v___x_3196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3196_, 0, v_res_3193_);
lean_ctor_set(v___x_3196_, 1, v___x_3194_);
lean_ctor_set(v___x_3196_, 2, v___x_3195_);
v___x_3197_ = l_String_Slice_toNat_x21(v___x_3196_);
lean_dec_ref_known(v___x_3196_, 3);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_pos_3192_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
return v___x_3198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object* v_size_3216_, lean_object* v_pad_3217_, lean_object* v_a_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(v_size_3216_, v_pad_3217_, v_a_3218_);
lean_dec(v_pad_3217_);
lean_dec(v_size_3216_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object* v_acc_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v_fst_3222_; lean_object* v_snd_3223_; lean_object* v_pos_3225_; lean_object* v_snd_3226_; lean_object* v_err_3227_; lean_object* v___x_3231_; uint8_t v_decide_3232_; 
v_fst_3222_ = lean_ctor_get(v_a_3221_, 0);
v_snd_3223_ = lean_ctor_get(v_a_3221_, 1);
lean_inc(v_snd_3223_);
v___x_3231_ = lean_string_utf8_byte_size(v_fst_3222_);
v_decide_3232_ = lean_nat_dec_eq(v_snd_3223_, v___x_3231_);
if (v_decide_3232_ == 0)
{
uint32_t v_c_3233_; lean_object* v___x_3234_; lean_object* v_it_x27_3235_; uint8_t v___y_3240_; uint8_t v___y_3241_; uint8_t v___y_3244_; uint8_t v___y_3245_; uint8_t v___y_3246_; uint8_t v___y_3248_; uint8_t v___y_3249_; uint8_t v___y_3250_; uint8_t v___y_3251_; uint8_t v___y_3253_; uint8_t v___y_3254_; uint8_t v___y_3262_; uint8_t v___y_3268_; uint32_t v___x_3273_; uint8_t v___x_3274_; 
v_c_3233_ = lean_string_utf8_get_fast(v_fst_3222_, v_snd_3223_);
v___x_3234_ = lean_string_utf8_next_fast(v_fst_3222_, v_snd_3223_);
lean_inc(v_fst_3222_);
v_it_x27_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3235_, 0, v_fst_3222_);
lean_ctor_set(v_it_x27_3235_, 1, v___x_3234_);
v___x_3273_ = 65;
v___x_3274_ = lean_uint32_dec_le(v___x_3273_, v_c_3233_);
if (v___x_3274_ == 0)
{
v___y_3268_ = v___x_3274_;
goto v___jp_3267_;
}
else
{
uint32_t v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = 90;
v___x_3276_ = lean_uint32_dec_le(v_c_3233_, v___x_3275_);
v___y_3268_ = v___x_3276_;
goto v___jp_3267_;
}
v___jp_3236_:
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_string_push(v_acc_3220_, v_c_3233_);
v_acc_3220_ = v___x_3237_;
v_a_3221_ = v_it_x27_3235_;
goto _start;
}
v___jp_3239_:
{
if (v___y_3240_ == 0)
{
if (v___y_3241_ == 0)
{
lean_object* v___x_3242_; 
lean_dec_ref_known(v_it_x27_3235_, 2);
v___x_3242_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3223_);
v_pos_3225_ = v_a_3221_;
v_snd_3226_ = v_snd_3223_;
v_err_3227_ = v___x_3242_;
goto v___jp_3224_;
}
else
{
lean_dec(v_snd_3223_);
lean_dec_ref(v_a_3221_);
goto v___jp_3236_;
}
}
else
{
lean_dec(v_snd_3223_);
lean_dec_ref(v_a_3221_);
goto v___jp_3236_;
}
}
v___jp_3243_:
{
if (v___y_3245_ == 0)
{
v___y_3240_ = v___y_3244_;
v___y_3241_ = v___y_3246_;
goto v___jp_3239_;
}
else
{
v___y_3240_ = v___y_3244_;
v___y_3241_ = v___y_3245_;
goto v___jp_3239_;
}
}
v___jp_3247_:
{
if (v___y_3249_ == 0)
{
v___y_3244_ = v___y_3248_;
v___y_3245_ = v___y_3250_;
v___y_3246_ = v___y_3251_;
goto v___jp_3243_;
}
else
{
v___y_3244_ = v___y_3248_;
v___y_3245_ = v___y_3250_;
v___y_3246_ = v___y_3249_;
goto v___jp_3243_;
}
}
v___jp_3252_:
{
uint32_t v___x_3255_; uint8_t v___x_3256_; uint32_t v___x_3257_; uint8_t v___x_3258_; 
v___x_3255_ = 95;
v___x_3256_ = lean_uint32_dec_eq(v_c_3233_, v___x_3255_);
v___x_3257_ = 45;
v___x_3258_ = lean_uint32_dec_eq(v_c_3233_, v___x_3257_);
if (v___x_3258_ == 0)
{
uint32_t v___x_3259_; uint8_t v___x_3260_; 
v___x_3259_ = 47;
v___x_3260_ = lean_uint32_dec_eq(v_c_3233_, v___x_3259_);
v___y_3248_ = v___y_3253_;
v___y_3249_ = v___x_3256_;
v___y_3250_ = v___y_3254_;
v___y_3251_ = v___x_3260_;
goto v___jp_3247_;
}
else
{
v___y_3248_ = v___y_3253_;
v___y_3249_ = v___x_3256_;
v___y_3250_ = v___y_3254_;
v___y_3251_ = v___x_3258_;
goto v___jp_3247_;
}
}
v___jp_3261_:
{
uint32_t v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = 48;
v___x_3264_ = lean_uint32_dec_le(v___x_3263_, v_c_3233_);
if (v___x_3264_ == 0)
{
v___y_3253_ = v___y_3262_;
v___y_3254_ = v___x_3264_;
goto v___jp_3252_;
}
else
{
uint32_t v___x_3265_; uint8_t v___x_3266_; 
v___x_3265_ = 57;
v___x_3266_ = lean_uint32_dec_le(v_c_3233_, v___x_3265_);
v___y_3253_ = v___y_3262_;
v___y_3254_ = v___x_3266_;
goto v___jp_3252_;
}
}
v___jp_3267_:
{
if (v___y_3268_ == 0)
{
uint32_t v___x_3269_; uint8_t v___x_3270_; 
v___x_3269_ = 97;
v___x_3270_ = lean_uint32_dec_le(v___x_3269_, v_c_3233_);
if (v___x_3270_ == 0)
{
v___y_3262_ = v___x_3270_;
goto v___jp_3261_;
}
else
{
uint32_t v___x_3271_; uint8_t v___x_3272_; 
v___x_3271_ = 122;
v___x_3272_ = lean_uint32_dec_le(v_c_3233_, v___x_3271_);
v___y_3262_ = v___x_3272_;
goto v___jp_3261_;
}
}
else
{
v___y_3262_ = v___y_3268_;
goto v___jp_3261_;
}
}
}
else
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_box(0);
lean_inc(v_snd_3223_);
v_pos_3225_ = v_a_3221_;
v_snd_3226_ = v_snd_3223_;
v_err_3227_ = v___x_3277_;
goto v___jp_3224_;
}
v___jp_3224_:
{
uint8_t v_decide_3228_; 
v_decide_3228_ = lean_nat_dec_eq(v_snd_3223_, v_snd_3226_);
lean_dec(v_snd_3226_);
lean_dec(v_snd_3223_);
if (v_decide_3228_ == 0)
{
lean_object* v___x_3229_; 
lean_dec_ref(v_acc_3220_);
lean_inc(v_err_3227_);
v___x_3229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3229_, 0, v_pos_3225_);
lean_ctor_set(v___x_3229_, 1, v_err_3227_);
return v___x_3229_;
}
else
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_pos_3225_);
lean_ctor_set(v___x_3230_, 1, v_acc_3220_);
return v___x_3230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object* v_acc_3278_, lean_object* v_a_3279_){
_start:
{
lean_object* v_fst_3280_; lean_object* v_snd_3281_; lean_object* v_pos_3283_; lean_object* v_snd_3284_; lean_object* v_err_3285_; lean_object* v___x_3289_; uint8_t v_decide_3290_; 
v_fst_3280_ = lean_ctor_get(v_a_3279_, 0);
v_snd_3281_ = lean_ctor_get(v_a_3279_, 1);
lean_inc(v_snd_3281_);
v___x_3289_ = lean_string_utf8_byte_size(v_fst_3280_);
v_decide_3290_ = lean_nat_dec_eq(v_snd_3281_, v___x_3289_);
if (v_decide_3290_ == 0)
{
uint32_t v_c_3291_; lean_object* v___x_3292_; lean_object* v_it_x27_3293_; uint8_t v___y_3298_; uint8_t v___y_3299_; uint8_t v___y_3302_; uint8_t v___y_3303_; uint8_t v___y_3304_; uint8_t v___y_3306_; uint8_t v___y_3307_; uint8_t v___y_3308_; uint8_t v___y_3309_; uint8_t v___y_3311_; uint8_t v___y_3312_; uint8_t v___y_3320_; uint8_t v___y_3326_; uint32_t v___x_3331_; uint8_t v___x_3332_; 
v_c_3291_ = lean_string_utf8_get_fast(v_fst_3280_, v_snd_3281_);
v___x_3292_ = lean_string_utf8_next_fast(v_fst_3280_, v_snd_3281_);
lean_inc(v_fst_3280_);
v_it_x27_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3293_, 0, v_fst_3280_);
lean_ctor_set(v_it_x27_3293_, 1, v___x_3292_);
v___x_3331_ = 65;
v___x_3332_ = lean_uint32_dec_le(v___x_3331_, v_c_3291_);
if (v___x_3332_ == 0)
{
v___y_3326_ = v___x_3332_;
goto v___jp_3325_;
}
else
{
uint32_t v___x_3333_; uint8_t v___x_3334_; 
v___x_3333_ = 90;
v___x_3334_ = lean_uint32_dec_le(v_c_3291_, v___x_3333_);
v___y_3326_ = v___x_3334_;
goto v___jp_3325_;
}
v___jp_3294_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = lean_string_push(v_acc_3278_, v_c_3291_);
v___x_3296_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(v___x_3295_, v_it_x27_3293_);
return v___x_3296_;
}
v___jp_3297_:
{
if (v___y_3298_ == 0)
{
if (v___y_3299_ == 0)
{
lean_object* v___x_3300_; 
lean_dec_ref_known(v_it_x27_3293_, 2);
v___x_3300_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3281_);
v_pos_3283_ = v_a_3279_;
v_snd_3284_ = v_snd_3281_;
v_err_3285_ = v___x_3300_;
goto v___jp_3282_;
}
else
{
lean_dec(v_snd_3281_);
lean_dec_ref(v_a_3279_);
goto v___jp_3294_;
}
}
else
{
lean_dec(v_snd_3281_);
lean_dec_ref(v_a_3279_);
goto v___jp_3294_;
}
}
v___jp_3301_:
{
if (v___y_3302_ == 0)
{
v___y_3298_ = v___y_3303_;
v___y_3299_ = v___y_3304_;
goto v___jp_3297_;
}
else
{
v___y_3298_ = v___y_3303_;
v___y_3299_ = v___y_3302_;
goto v___jp_3297_;
}
}
v___jp_3305_:
{
if (v___y_3307_ == 0)
{
v___y_3302_ = v___y_3306_;
v___y_3303_ = v___y_3308_;
v___y_3304_ = v___y_3309_;
goto v___jp_3301_;
}
else
{
v___y_3302_ = v___y_3306_;
v___y_3303_ = v___y_3308_;
v___y_3304_ = v___y_3307_;
goto v___jp_3301_;
}
}
v___jp_3310_:
{
uint32_t v___x_3313_; uint8_t v___x_3314_; uint32_t v___x_3315_; uint8_t v___x_3316_; 
v___x_3313_ = 95;
v___x_3314_ = lean_uint32_dec_eq(v_c_3291_, v___x_3313_);
v___x_3315_ = 45;
v___x_3316_ = lean_uint32_dec_eq(v_c_3291_, v___x_3315_);
if (v___x_3316_ == 0)
{
uint32_t v___x_3317_; uint8_t v___x_3318_; 
v___x_3317_ = 47;
v___x_3318_ = lean_uint32_dec_eq(v_c_3291_, v___x_3317_);
v___y_3306_ = v___y_3312_;
v___y_3307_ = v___x_3314_;
v___y_3308_ = v___y_3311_;
v___y_3309_ = v___x_3318_;
goto v___jp_3305_;
}
else
{
v___y_3306_ = v___y_3312_;
v___y_3307_ = v___x_3314_;
v___y_3308_ = v___y_3311_;
v___y_3309_ = v___x_3316_;
goto v___jp_3305_;
}
}
v___jp_3319_:
{
uint32_t v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = 48;
v___x_3322_ = lean_uint32_dec_le(v___x_3321_, v_c_3291_);
if (v___x_3322_ == 0)
{
v___y_3311_ = v___y_3320_;
v___y_3312_ = v___x_3322_;
goto v___jp_3310_;
}
else
{
uint32_t v___x_3323_; uint8_t v___x_3324_; 
v___x_3323_ = 57;
v___x_3324_ = lean_uint32_dec_le(v_c_3291_, v___x_3323_);
v___y_3311_ = v___y_3320_;
v___y_3312_ = v___x_3324_;
goto v___jp_3310_;
}
}
v___jp_3325_:
{
if (v___y_3326_ == 0)
{
uint32_t v___x_3327_; uint8_t v___x_3328_; 
v___x_3327_ = 97;
v___x_3328_ = lean_uint32_dec_le(v___x_3327_, v_c_3291_);
if (v___x_3328_ == 0)
{
v___y_3320_ = v___x_3328_;
goto v___jp_3319_;
}
else
{
uint32_t v___x_3329_; uint8_t v___x_3330_; 
v___x_3329_ = 122;
v___x_3330_ = lean_uint32_dec_le(v_c_3291_, v___x_3329_);
v___y_3320_ = v___x_3330_;
goto v___jp_3319_;
}
}
else
{
v___y_3320_ = v___y_3326_;
goto v___jp_3319_;
}
}
}
else
{
lean_object* v___x_3335_; 
v___x_3335_ = lean_box(0);
lean_inc(v_snd_3281_);
v_pos_3283_ = v_a_3279_;
v_snd_3284_ = v_snd_3281_;
v_err_3285_ = v___x_3335_;
goto v___jp_3282_;
}
v___jp_3282_:
{
uint8_t v_decide_3286_; 
v_decide_3286_ = lean_nat_dec_eq(v_snd_3281_, v_snd_3284_);
lean_dec(v_snd_3284_);
lean_dec(v_snd_3281_);
if (v_decide_3286_ == 0)
{
lean_object* v___x_3287_; 
lean_dec_ref(v_acc_3278_);
lean_inc(v_err_3285_);
v___x_3287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3287_, 0, v_pos_3283_);
lean_ctor_set(v___x_3287_, 1, v_err_3285_);
return v___x_3287_;
}
else
{
lean_object* v___x_3288_; 
v___x_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3288_, 0, v_pos_3283_);
lean_ctor_set(v___x_3288_, 1, v_acc_3278_);
return v___x_3288_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object* v_a_3336_){
_start:
{
lean_object* v_fst_3337_; lean_object* v_snd_3338_; lean_object* v___x_3339_; uint8_t v_decide_3340_; 
v_fst_3337_ = lean_ctor_get(v_a_3336_, 0);
v_snd_3338_ = lean_ctor_get(v_a_3336_, 1);
v___x_3339_ = lean_string_utf8_byte_size(v_fst_3337_);
v_decide_3340_ = lean_nat_dec_eq(v_snd_3338_, v___x_3339_);
if (v_decide_3340_ == 0)
{
uint32_t v_c_3341_; lean_object* v___x_3342_; uint8_t v___y_3349_; uint8_t v___y_3350_; uint8_t v___y_3354_; uint8_t v___y_3355_; uint8_t v___y_3356_; uint8_t v___y_3358_; uint8_t v___y_3359_; uint8_t v___y_3360_; uint8_t v___y_3361_; uint8_t v___y_3363_; uint8_t v___y_3364_; uint8_t v___y_3372_; uint8_t v___y_3378_; uint32_t v___x_3383_; uint8_t v___x_3384_; 
v_c_3341_ = lean_string_utf8_get_fast(v_fst_3337_, v_snd_3338_);
v___x_3342_ = lean_string_utf8_next_fast(v_fst_3337_, v_snd_3338_);
v___x_3383_ = 65;
v___x_3384_ = lean_uint32_dec_le(v___x_3383_, v_c_3341_);
if (v___x_3384_ == 0)
{
v___y_3378_ = v___x_3384_;
goto v___jp_3377_;
}
else
{
uint32_t v___x_3385_; uint8_t v___x_3386_; 
v___x_3385_ = 90;
v___x_3386_ = lean_uint32_dec_le(v_c_3341_, v___x_3385_);
v___y_3378_ = v___x_3386_;
goto v___jp_3377_;
}
v___jp_3343_:
{
lean_object* v_it_x27_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_it_x27_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3344_, 0, v_fst_3337_);
lean_ctor_set(v_it_x27_3344_, 1, v___x_3342_);
v___x_3345_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3346_ = lean_string_push(v___x_3345_, v_c_3341_);
v___x_3347_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(v___x_3346_, v_it_x27_3344_);
return v___x_3347_;
}
v___jp_3348_:
{
if (v___y_3349_ == 0)
{
if (v___y_3350_ == 0)
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3352_, 0, v_a_3336_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
return v___x_3352_;
}
else
{
lean_inc(v_fst_3337_);
lean_dec_ref(v_a_3336_);
goto v___jp_3343_;
}
}
else
{
lean_inc(v_fst_3337_);
lean_dec_ref(v_a_3336_);
goto v___jp_3343_;
}
}
v___jp_3353_:
{
if (v___y_3354_ == 0)
{
v___y_3349_ = v___y_3355_;
v___y_3350_ = v___y_3356_;
goto v___jp_3348_;
}
else
{
v___y_3349_ = v___y_3355_;
v___y_3350_ = v___y_3354_;
goto v___jp_3348_;
}
}
v___jp_3357_:
{
if (v___y_3358_ == 0)
{
v___y_3354_ = v___y_3359_;
v___y_3355_ = v___y_3360_;
v___y_3356_ = v___y_3361_;
goto v___jp_3353_;
}
else
{
v___y_3354_ = v___y_3359_;
v___y_3355_ = v___y_3360_;
v___y_3356_ = v___y_3358_;
goto v___jp_3353_;
}
}
v___jp_3362_:
{
uint32_t v___x_3365_; uint8_t v___x_3366_; uint32_t v___x_3367_; uint8_t v___x_3368_; 
v___x_3365_ = 95;
v___x_3366_ = lean_uint32_dec_eq(v_c_3341_, v___x_3365_);
v___x_3367_ = 45;
v___x_3368_ = lean_uint32_dec_eq(v_c_3341_, v___x_3367_);
if (v___x_3368_ == 0)
{
uint32_t v___x_3369_; uint8_t v___x_3370_; 
v___x_3369_ = 47;
v___x_3370_ = lean_uint32_dec_eq(v_c_3341_, v___x_3369_);
v___y_3358_ = v___x_3366_;
v___y_3359_ = v___y_3364_;
v___y_3360_ = v___y_3363_;
v___y_3361_ = v___x_3370_;
goto v___jp_3357_;
}
else
{
v___y_3358_ = v___x_3366_;
v___y_3359_ = v___y_3364_;
v___y_3360_ = v___y_3363_;
v___y_3361_ = v___x_3368_;
goto v___jp_3357_;
}
}
v___jp_3371_:
{
uint32_t v___x_3373_; uint8_t v___x_3374_; 
v___x_3373_ = 48;
v___x_3374_ = lean_uint32_dec_le(v___x_3373_, v_c_3341_);
if (v___x_3374_ == 0)
{
v___y_3363_ = v___y_3372_;
v___y_3364_ = v___x_3374_;
goto v___jp_3362_;
}
else
{
uint32_t v___x_3375_; uint8_t v___x_3376_; 
v___x_3375_ = 57;
v___x_3376_ = lean_uint32_dec_le(v_c_3341_, v___x_3375_);
v___y_3363_ = v___y_3372_;
v___y_3364_ = v___x_3376_;
goto v___jp_3362_;
}
}
v___jp_3377_:
{
if (v___y_3378_ == 0)
{
uint32_t v___x_3379_; uint8_t v___x_3380_; 
v___x_3379_ = 97;
v___x_3380_ = lean_uint32_dec_le(v___x_3379_, v_c_3341_);
if (v___x_3380_ == 0)
{
v___y_3372_ = v___x_3380_;
goto v___jp_3371_;
}
else
{
uint32_t v___x_3381_; uint8_t v___x_3382_; 
v___x_3381_ = 122;
v___x_3382_ = lean_uint32_dec_le(v_c_3341_, v___x_3381_);
v___y_3372_ = v___x_3382_;
goto v___jp_3371_;
}
}
else
{
v___y_3372_ = v___y_3378_;
goto v___jp_3371_;
}
}
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = lean_box(0);
v___x_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3388_, 0, v_a_3336_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
return v___x_3388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object* v_n_3391_, lean_object* v_m_3392_, lean_object* v_parser_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_apply_1(v_parser_3393_, v_a_3394_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_pos_3396_; lean_object* v_res_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3420_; 
v_pos_3396_ = lean_ctor_get(v___x_3395_, 0);
v_res_3397_ = lean_ctor_get(v___x_3395_, 1);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3399_ = v___x_3395_;
v_isShared_3400_ = v_isSharedCheck_3420_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_res_3397_);
lean_inc(v_pos_3396_);
lean_dec(v___x_3395_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3420_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
uint8_t v___y_3402_; uint8_t v___x_3418_; 
v___x_3418_ = lean_nat_dec_le(v_n_3391_, v_res_3397_);
if (v___x_3418_ == 0)
{
v___y_3402_ = v___x_3418_;
goto v___jp_3401_;
}
else
{
uint8_t v___x_3419_; 
v___x_3419_ = lean_nat_dec_le(v_res_3397_, v_m_3392_);
v___y_3402_ = v___x_3419_;
goto v___jp_3401_;
}
v___jp_3401_:
{
if (v___y_3402_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3412_; 
lean_dec(v_res_3397_);
v___x_3403_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0));
v___x_3404_ = l_Nat_reprFast(v_n_3391_);
v___x_3405_ = lean_string_append(v___x_3403_, v___x_3404_);
lean_dec_ref(v___x_3404_);
v___x_3406_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1));
v___x_3407_ = lean_string_append(v___x_3405_, v___x_3406_);
v___x_3408_ = l_Nat_reprFast(v_m_3392_);
v___x_3409_ = lean_string_append(v___x_3407_, v___x_3408_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
if (v_isShared_3400_ == 0)
{
lean_ctor_set_tag(v___x_3399_, 1);
lean_ctor_set(v___x_3399_, 1, v___x_3410_);
v___x_3412_ = v___x_3399_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_pos_3396_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_dec(v_m_3392_);
lean_dec(v_n_3391_);
v___x_3414_ = lean_nat_to_int(v_res_3397_);
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 1, v___x_3414_);
v___x_3416_ = v___x_3399_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_pos_3396_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
else
{
lean_object* v_pos_3421_; lean_object* v_err_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_m_3392_);
lean_dec(v_n_3391_);
v_pos_3421_ = lean_ctor_get(v___x_3395_, 0);
v_err_3422_ = lean_ctor_get(v___x_3395_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3395_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_err_3422_);
lean_inc(v_pos_3421_);
lean_dec(v___x_3395_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object* v_a_3430_){
_start:
{
lean_object* v_fst_3434_; lean_object* v_snd_3435_; lean_object* v___x_3436_; uint8_t v_decide_3437_; 
v_fst_3434_ = lean_ctor_get(v_a_3430_, 0);
v_snd_3435_ = lean_ctor_get(v_a_3430_, 1);
v___x_3436_ = lean_string_utf8_byte_size(v_fst_3434_);
v_decide_3437_ = lean_nat_dec_eq(v_snd_3435_, v___x_3436_);
if (v_decide_3437_ == 0)
{
uint32_t v_c_3438_; uint32_t v___x_3439_; uint8_t v___x_3440_; 
v_c_3438_ = lean_string_utf8_get_fast(v_fst_3434_, v_snd_3435_);
v___x_3439_ = 48;
v___x_3440_ = lean_uint32_dec_le(v___x_3439_, v_c_3438_);
if (v___x_3440_ == 0)
{
goto v___jp_3431_;
}
else
{
uint32_t v___x_3441_; uint8_t v___x_3442_; 
v___x_3441_ = 57;
v___x_3442_ = lean_uint32_dec_le(v_c_3438_, v___x_3441_);
if (v___x_3442_ == 0)
{
goto v___jp_3431_;
}
else
{
lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3479_; 
lean_inc(v_snd_3435_);
lean_inc(v_fst_3434_);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_a_3430_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; lean_object* v_unused_3481_; 
v_unused_3480_ = lean_ctor_get(v_a_3430_, 1);
lean_dec(v_unused_3480_);
v_unused_3481_ = lean_ctor_get(v_a_3430_, 0);
lean_dec(v_unused_3481_);
v___x_3444_ = v_a_3430_;
v_isShared_3445_ = v_isSharedCheck_3479_;
goto v_resetjp_3443_;
}
else
{
lean_dec(v_a_3430_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3479_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3446_; lean_object* v_pos_3448_; lean_object* v_snd_3449_; lean_object* v_err_3450_; lean_object* v_it_x27_3458_; 
v___x_3446_ = lean_string_utf8_next_fast(v_fst_3434_, v_snd_3435_);
lean_dec(v_snd_3435_);
lean_inc(v_fst_3434_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 1, v___x_3446_);
v_it_x27_3458_ = v___x_3444_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3446_);
v_it_x27_3458_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3457_;
}
v___jp_3447_:
{
uint8_t v_decide_3451_; 
v_decide_3451_ = lean_nat_dec_eq(v___x_3446_, v_snd_3449_);
lean_dec(v_snd_3449_);
if (v_decide_3451_ == 0)
{
lean_object* v___x_3452_; 
lean_inc(v_err_3450_);
v___x_3452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3452_, 0, v_pos_3448_);
lean_ctor_set(v___x_3452_, 1, v_err_3450_);
return v___x_3452_;
}
else
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3453_ = lean_uint32_to_nat(v_c_3438_);
v___x_3454_ = lean_unsigned_to_nat(48u);
v___x_3455_ = lean_nat_sub(v___x_3453_, v___x_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3456_, 0, v_pos_3448_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
return v___x_3456_;
}
}
v_reusejp_3457_:
{
uint8_t v_decide_3463_; 
v_decide_3463_ = lean_nat_dec_eq(v___x_3446_, v___x_3436_);
if (v_decide_3463_ == 0)
{
if (v___x_3442_ == 0)
{
lean_dec(v_fst_3434_);
goto v___jp_3461_;
}
else
{
uint32_t v___x_3464_; uint8_t v___x_3465_; 
v___x_3464_ = lean_string_utf8_get_fast(v_fst_3434_, v___x_3446_);
v___x_3465_ = lean_uint32_dec_le(v___x_3439_, v___x_3464_);
if (v___x_3465_ == 0)
{
lean_dec(v_fst_3434_);
goto v___jp_3459_;
}
else
{
uint8_t v___x_3466_; 
v___x_3466_ = lean_uint32_dec_le(v___x_3464_, v___x_3441_);
if (v___x_3466_ == 0)
{
lean_dec(v_fst_3434_);
goto v___jp_3459_;
}
else
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_dec_ref(v_it_x27_3458_);
v___x_3467_ = lean_string_utf8_next_fast(v_fst_3434_, v___x_3446_);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v_fst_3434_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_uint32_to_nat(v_c_3438_);
v___x_3470_ = lean_unsigned_to_nat(48u);
v___x_3471_ = lean_nat_sub(v___x_3469_, v___x_3470_);
lean_dec(v___x_3469_);
v___x_3472_ = lean_unsigned_to_nat(10u);
v___x_3473_ = lean_nat_mul(v___x_3471_, v___x_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_uint32_to_nat(v___x_3464_);
v___x_3475_ = lean_nat_sub(v___x_3474_, v___x_3470_);
lean_dec(v___x_3474_);
v___x_3476_ = lean_nat_add(v___x_3473_, v___x_3475_);
lean_dec(v___x_3475_);
lean_dec(v___x_3473_);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3468_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
return v___x_3477_;
}
}
}
}
else
{
lean_dec(v_fst_3434_);
goto v___jp_3461_;
}
v___jp_3459_:
{
lean_object* v___x_3460_; 
v___x_3460_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v_pos_3448_ = v_it_x27_3458_;
v_snd_3449_ = v___x_3446_;
v_err_3450_ = v___x_3460_;
goto v___jp_3447_;
}
v___jp_3461_:
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_box(0);
v_pos_3448_ = v_it_x27_3458_;
v_snd_3449_ = v___x_3446_;
v_err_3450_ = v___x_3462_;
goto v___jp_3447_;
}
}
}
}
}
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = lean_box(0);
v___x_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3483_, 0, v_a_3430_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
return v___x_3483_;
}
v___jp_3431_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3433_, 0, v_a_3430_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
return v___x_3433_;
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0(void){
_start:
{
uint32_t v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = 58;
v___x_3485_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3486_ = lean_string_push(v___x_3485_, v___x_3484_);
return v___x_3486_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3487_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0);
v___x_3488_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3489_ = lean_string_append(v___x_3488_, v___x_3487_);
return v___x_3489_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3490_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3491_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1);
v___x_3492_ = lean_string_append(v___x_3491_, v___x_3490_);
return v___x_3492_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__2);
v___x_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
return v___x_3494_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1(void){
_start:
{
uint32_t v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = 58;
v___x_3496_ = lean_box_uint32(v___x_3495_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(uint8_t v_withColon_3497_, lean_object* v___y_3498_){
_start:
{
if (v_withColon_3497_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___y_3498_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
return v___x_3500_;
}
else
{
lean_object* v_fst_3501_; lean_object* v_snd_3502_; lean_object* v___x_3503_; uint8_t v_decide_3504_; 
v_fst_3501_ = lean_ctor_get(v___y_3498_, 0);
v_snd_3502_ = lean_ctor_get(v___y_3498_, 1);
v___x_3503_ = lean_string_utf8_byte_size(v_fst_3501_);
v_decide_3504_ = lean_nat_dec_eq(v_snd_3502_, v___x_3503_);
if (v_decide_3504_ == 0)
{
uint32_t v___x_3505_; uint32_t v_c_3506_; uint8_t v___x_3507_; 
v___x_3505_ = 58;
v_c_3506_ = lean_string_utf8_get_fast(v_fst_3501_, v_snd_3502_);
v___x_3507_ = lean_uint32_dec_eq(v_c_3506_, v___x_3505_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__3);
v___x_3509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___y_3498_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
return v___x_3509_;
}
else
{
lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3519_; 
lean_inc(v_snd_3502_);
lean_inc(v_fst_3501_);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___y_3498_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; lean_object* v_unused_3521_; 
v_unused_3520_ = lean_ctor_get(v___y_3498_, 1);
lean_dec(v_unused_3520_);
v_unused_3521_ = lean_ctor_get(v___y_3498_, 0);
lean_dec(v_unused_3521_);
v___x_3511_ = v___y_3498_;
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
else
{
lean_dec(v___y_3498_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v_it_x27_3515_; 
v___x_3513_ = lean_string_utf8_next_fast(v_fst_3501_, v_snd_3502_);
lean_dec(v_snd_3502_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v___x_3513_);
v_it_x27_3515_ = v___x_3511_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_fst_3501_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___x_3513_);
v_it_x27_3515_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3517_, 0, v_it_x27_3515_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
return v___x_3517_;
}
}
}
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = lean_box(0);
v___x_3523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___y_3498_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
return v___x_3523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed(lean_object* v_withColon_3524_, lean_object* v___y_3525_){
_start:
{
uint8_t v_withColon_boxed_3526_; lean_object* v_res_3527_; 
v_withColon_boxed_3526_ = lean_unbox(v_withColon_3524_);
v_res_3527_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(v_withColon_boxed_3526_, v___y_3525_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(lean_object* v_a_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = lean_nat_to_int(v_a_3528_);
v___x_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___y_3529_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object* v___y_3532_, lean_object* v___f_3533_, lean_object* v_n_3534_, uint8_t v_reason_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_pos_3538_; lean_object* v_err_3539_; 
switch(v_reason_3535_)
{
case 0:
{
lean_object* v___x_3555_; 
v___x_3555_ = lean_apply_1(v___y_3532_, v___y_3536_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_pos_3556_; lean_object* v___x_3557_; 
v_pos_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_pos_3556_);
lean_dec_ref_known(v___x_3555_, 2);
v___x_3557_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3556_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_pos_3558_; lean_object* v_res_3559_; lean_object* v___x_3560_; 
v_pos_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_pos_3558_);
v_res_3559_ = lean_ctor_get(v___x_3557_, 1);
lean_inc(v_res_3559_);
lean_dec_ref_known(v___x_3557_, 2);
v___x_3560_ = lean_apply_2(v___f_3533_, v_res_3559_, v_pos_3558_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_pos_3561_; lean_object* v_res_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3570_; 
v_pos_3561_ = lean_ctor_get(v___x_3560_, 0);
v_res_3562_ = lean_ctor_get(v___x_3560_, 1);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3564_ = v___x_3560_;
v_isShared_3565_ = v_isSharedCheck_3570_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_res_3562_);
lean_inc(v_pos_3561_);
lean_dec(v___x_3560_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3570_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3566_, 0, v_res_3562_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v___x_3566_);
v___x_3568_ = v___x_3564_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_pos_3561_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
else
{
lean_object* v_pos_3571_; lean_object* v_err_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
v_pos_3571_ = lean_ctor_get(v___x_3560_, 0);
v_err_3572_ = lean_ctor_get(v___x_3560_, 1);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3560_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_err_3572_);
lean_inc(v_pos_3571_);
lean_dec(v___x_3560_);
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
lean_dec_ref(v___f_3533_);
v_pos_3580_ = lean_ctor_get(v___x_3557_, 0);
v_err_3581_ = lean_ctor_get(v___x_3557_, 1);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3557_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_err_3581_);
lean_inc(v_pos_3580_);
lean_dec(v___x_3557_);
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
else
{
lean_object* v_pos_3589_; lean_object* v_err_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v___f_3533_);
v_pos_3589_ = lean_ctor_get(v___x_3555_, 0);
v_err_3590_ = lean_ctor_get(v___x_3555_, 1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3555_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_err_3590_);
lean_inc(v_pos_3589_);
lean_dec(v___x_3555_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_pos_3589_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_err_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
case 1:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_dec_ref(v___f_3533_);
lean_dec_ref(v___y_3532_);
v___x_3598_ = lean_box(0);
v___x_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___y_3536_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
return v___x_3599_;
}
default: 
{
lean_object* v___x_3600_; 
lean_inc_ref(v___y_3536_);
v___x_3600_ = lean_apply_1(v___y_3532_, v___y_3536_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_pos_3601_; lean_object* v___x_3602_; 
v_pos_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_pos_3601_);
lean_dec_ref_known(v___x_3600_, 2);
v___x_3602_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3601_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_pos_3603_; lean_object* v_res_3604_; lean_object* v___x_3605_; 
v_pos_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_pos_3603_);
v_res_3604_ = lean_ctor_get(v___x_3602_, 1);
lean_inc(v_res_3604_);
lean_dec_ref_known(v___x_3602_, 2);
v___x_3605_ = lean_apply_2(v___f_3533_, v_res_3604_, v_pos_3603_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_pos_3606_; lean_object* v_res_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3615_; 
lean_dec_ref(v___y_3536_);
v_pos_3606_ = lean_ctor_get(v___x_3605_, 0);
v_res_3607_ = lean_ctor_get(v___x_3605_, 1);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3609_ = v___x_3605_;
v_isShared_3610_ = v_isSharedCheck_3615_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_res_3607_);
lean_inc(v_pos_3606_);
lean_dec(v___x_3605_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3615_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3611_, 0, v_res_3607_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 1, v___x_3611_);
v___x_3613_ = v___x_3609_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_pos_3606_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
else
{
lean_object* v_pos_3616_; lean_object* v_err_3617_; 
v_pos_3616_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_pos_3616_);
v_err_3617_ = lean_ctor_get(v___x_3605_, 1);
lean_inc(v_err_3617_);
lean_dec_ref_known(v___x_3605_, 2);
v_pos_3538_ = v_pos_3616_;
v_err_3539_ = v_err_3617_;
goto v___jp_3537_;
}
}
else
{
lean_object* v_pos_3618_; lean_object* v_err_3619_; 
lean_dec_ref(v___f_3533_);
v_pos_3618_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_pos_3618_);
v_err_3619_ = lean_ctor_get(v___x_3602_, 1);
lean_inc(v_err_3619_);
lean_dec_ref_known(v___x_3602_, 2);
v_pos_3538_ = v_pos_3618_;
v_err_3539_ = v_err_3619_;
goto v___jp_3537_;
}
}
else
{
lean_object* v_pos_3620_; lean_object* v_err_3621_; 
lean_dec_ref(v___f_3533_);
v_pos_3620_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_pos_3620_);
v_err_3621_ = lean_ctor_get(v___x_3600_, 1);
lean_inc(v_err_3621_);
lean_dec_ref_known(v___x_3600_, 2);
v_pos_3538_ = v_pos_3620_;
v_err_3539_ = v_err_3621_;
goto v___jp_3537_;
}
}
}
v___jp_3537_:
{
lean_object* v_snd_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3553_; 
v_snd_3540_ = lean_ctor_get(v___y_3536_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___y_3536_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; 
v_unused_3554_ = lean_ctor_get(v___y_3536_, 0);
lean_dec(v_unused_3554_);
v___x_3542_ = v___y_3536_;
v_isShared_3543_ = v_isSharedCheck_3553_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_snd_3540_);
lean_dec(v___y_3536_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3553_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_snd_3544_; uint8_t v_decide_3545_; 
v_snd_3544_ = lean_ctor_get(v_pos_3538_, 1);
v_decide_3545_ = lean_nat_dec_eq(v_snd_3540_, v_snd_3544_);
lean_dec(v_snd_3540_);
if (v_decide_3545_ == 0)
{
lean_object* v___x_3547_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 1);
lean_ctor_set(v___x_3542_, 1, v_err_3539_);
lean_ctor_set(v___x_3542_, 0, v_pos_3538_);
v___x_3547_ = v___x_3542_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_pos_3538_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_err_3539_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
lean_dec(v_err_3539_);
v___x_3549_ = lean_box(0);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v___x_3549_);
lean_ctor_set(v___x_3542_, 0, v_pos_3538_);
v___x_3551_ = v___x_3542_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_pos_3538_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object* v___y_3622_, lean_object* v___f_3623_, lean_object* v_n_3624_, lean_object* v_reason_3625_, lean_object* v___y_3626_){
_start:
{
uint8_t v_reason_boxed_3627_; lean_object* v_res_3628_; 
v_reason_boxed_3627_ = lean_unbox(v_reason_3625_);
v_res_3628_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3622_, v___f_3623_, v_n_3624_, v_reason_boxed_3627_, v___y_3626_);
lean_dec_ref(v_n_3624_);
return v_res_3628_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = lean_unsigned_to_nat(3600u);
v___x_3630_ = lean_nat_to_int(v___x_3629_);
return v___x_3630_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = lean_unsigned_to_nat(1u);
v___x_3633_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3632_);
return v___x_3633_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_unsigned_to_nat(59u);
v___x_3635_ = lean_nat_to_int(v___x_3634_);
return v___x_3635_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = lean_unsigned_to_nat(60u);
v___x_3639_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3638_);
return v___x_3639_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = lean_unsigned_to_nat(23u);
v___x_3644_ = lean_nat_to_int(v___x_3643_);
return v___x_3644_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11(void){
_start:
{
uint32_t v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = 45;
v___x_3646_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3647_ = lean_string_push(v___x_3646_, v___x_3645_);
return v___x_3647_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11);
v___x_3649_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3650_ = lean_string_append(v___x_3649_, v___x_3648_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3652_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12);
v___x_3653_ = lean_string_append(v___x_3652_, v___x_3651_);
return v___x_3653_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13);
v___x_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15(void){
_start:
{
uint32_t v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = 43;
v___x_3657_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3658_ = lean_string_push(v___x_3657_, v___x_3656_);
return v___x_3658_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15);
v___x_3660_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3661_ = lean_string_append(v___x_3660_, v___x_3659_);
return v___x_3661_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17(void){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3663_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16);
v___x_3664_ = lean_string_append(v___x_3663_, v___x_3662_);
return v___x_3664_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17);
v___x_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t v_withMinutes_3667_, uint8_t v_withSeconds_3668_, uint8_t v_withColon_3669_, lean_object* v_a_3670_){
_start:
{
lean_object* v___y_3672_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v_fst_3706_; lean_object* v_snd_3707_; lean_object* v___x_3708_; lean_object* v___y_3709_; lean_object* v___f_3710_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; uint8_t v___y_3761_; lean_object* v_pos_3809_; lean_object* v_res_3810_; lean_object* v_pos_3829_; lean_object* v_fst_3830_; lean_object* v_snd_3831_; lean_object* v_err_3832_; lean_object* v___x_3845_; uint8_t v_decide_3846_; 
v_fst_3706_ = lean_ctor_get(v_a_3670_, 0);
lean_inc(v_fst_3706_);
v_snd_3707_ = lean_ctor_get(v_a_3670_, 1);
lean_inc(v_snd_3707_);
v___x_3708_ = lean_box(v_withColon_3669_);
v___y_3709_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed), 2, 1);
lean_closure_set(v___y_3709_, 0, v___x_3708_);
v___f_3710_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1));
v___x_3845_ = lean_string_utf8_byte_size(v_fst_3706_);
v_decide_3846_ = lean_nat_dec_eq(v_snd_3707_, v___x_3845_);
if (v_decide_3846_ == 0)
{
uint32_t v___x_3847_; uint32_t v_c_3848_; uint8_t v___x_3849_; 
v___x_3847_ = 43;
v_c_3848_ = lean_string_utf8_get_fast(v_fst_3706_, v_snd_3707_);
v___x_3849_ = lean_uint32_dec_eq(v_c_3848_, v___x_3847_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; 
v___x_3850_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18);
lean_inc(v_snd_3707_);
v_pos_3829_ = v_a_3670_;
v_fst_3830_ = v_fst_3706_;
v_snd_3831_ = v_snd_3707_;
v_err_3832_ = v___x_3850_;
goto v___jp_3828_;
}
else
{
lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3859_; 
v_isSharedCheck_3859_ = !lean_is_exclusive(v_a_3670_);
if (v_isSharedCheck_3859_ == 0)
{
lean_object* v_unused_3860_; lean_object* v_unused_3861_; 
v_unused_3860_ = lean_ctor_get(v_a_3670_, 1);
lean_dec(v_unused_3860_);
v_unused_3861_ = lean_ctor_get(v_a_3670_, 0);
lean_dec(v_unused_3861_);
v___x_3852_ = v_a_3670_;
v_isShared_3853_ = v_isSharedCheck_3859_;
goto v_resetjp_3851_;
}
else
{
lean_dec(v_a_3670_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3859_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3854_; lean_object* v_it_x27_3856_; 
v___x_3854_ = lean_string_utf8_next_fast(v_fst_3706_, v_snd_3707_);
lean_dec(v_snd_3707_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 1, v___x_3854_);
v_it_x27_3856_ = v___x_3852_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_fst_3706_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v___x_3854_);
v_it_x27_3856_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v_pos_3809_ = v_it_x27_3856_;
v_res_3810_ = v___x_3857_;
goto v___jp_3808_;
}
}
}
}
else
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_box(0);
lean_inc(v_snd_3707_);
v_pos_3829_ = v_a_3670_;
v_fst_3830_ = v_fst_3706_;
v_snd_3831_ = v_snd_3707_;
v_err_3832_ = v___x_3862_;
goto v___jp_3828_;
}
v___jp_3671_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = lean_box(0);
v___x_3674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___y_3672_);
lean_ctor_set(v___x_3674_, 1, v___x_3673_);
return v___x_3674_;
}
v___jp_3675_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3680_ = lean_int_add(v___y_3676_, v___y_3679_);
lean_dec(v___y_3679_);
lean_dec(v___y_3676_);
v___x_3681_ = lean_int_mul(v___x_3680_, v___y_3678_);
lean_dec(v___x_3680_);
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___y_3677_);
lean_ctor_set(v___x_3682_, 1, v___x_3681_);
return v___x_3682_;
}
v___jp_3683_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3691_ = lean_nat_to_int(v___y_3688_);
v___x_3692_ = lean_int_mul(v___y_3690_, v___x_3691_);
lean_dec(v___x_3691_);
lean_dec(v___y_3690_);
v___x_3693_ = lean_int_add(v___y_3686_, v___x_3692_);
lean_dec(v___x_3692_);
lean_dec(v___y_3686_);
if (lean_obj_tag(v___y_3685_) == 0)
{
lean_inc(v___y_3684_);
v___y_3676_ = v___x_3693_;
v___y_3677_ = v___y_3687_;
v___y_3678_ = v___y_3689_;
v___y_3679_ = v___y_3684_;
goto v___jp_3675_;
}
else
{
lean_object* v_val_3694_; 
v_val_3694_ = lean_ctor_get(v___y_3685_, 0);
lean_inc(v_val_3694_);
lean_dec_ref_known(v___y_3685_, 1);
v___y_3676_ = v___x_3693_;
v___y_3677_ = v___y_3687_;
v___y_3678_ = v___y_3689_;
v___y_3679_ = v_val_3694_;
goto v___jp_3675_;
}
}
v___jp_3695_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0);
v___x_3704_ = lean_int_mul(v___y_3697_, v___x_3703_);
lean_dec(v___y_3697_);
if (lean_obj_tag(v___y_3698_) == 0)
{
lean_inc(v___y_3696_);
v___y_3684_ = v___y_3696_;
v___y_3685_ = v___y_3699_;
v___y_3686_ = v___x_3704_;
v___y_3687_ = v___y_3702_;
v___y_3688_ = v___y_3700_;
v___y_3689_ = v___y_3701_;
v___y_3690_ = v___y_3696_;
goto v___jp_3683_;
}
else
{
lean_object* v_val_3705_; 
v_val_3705_ = lean_ctor_get(v___y_3698_, 0);
lean_inc(v_val_3705_);
lean_dec_ref_known(v___y_3698_, 1);
v___y_3684_ = v___y_3696_;
v___y_3685_ = v___y_3699_;
v___y_3686_ = v___x_3704_;
v___y_3687_ = v___y_3702_;
v___y_3688_ = v___y_3700_;
v___y_3689_ = v___y_3701_;
v___y_3690_ = v_val_3705_;
goto v___jp_3683_;
}
}
v___jp_3711_:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2);
v___x_3719_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3709_, v___f_3710_, v___x_3718_, v_withSeconds_3668_, v___y_3717_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_res_3720_; 
v_res_3720_ = lean_ctor_get(v___x_3719_, 1);
lean_inc(v_res_3720_);
if (lean_obj_tag(v_res_3720_) == 1)
{
lean_object* v_pos_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3744_; 
v_pos_3721_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3744_ == 0)
{
lean_object* v_unused_3745_; 
v_unused_3745_ = lean_ctor_get(v___x_3719_, 1);
lean_dec(v_unused_3745_);
v___x_3723_ = v___x_3719_;
v_isShared_3724_ = v_isSharedCheck_3744_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_pos_3721_);
lean_dec(v___x_3719_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3744_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_val_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; 
v_val_3725_ = lean_ctor_get(v_res_3720_, 0);
v___x_3726_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3);
v___x_3727_ = lean_int_dec_lt(v___x_3726_, v_val_3725_);
if (v___x_3727_ == 0)
{
lean_del_object(v___x_3723_);
v___y_3696_ = v___y_3712_;
v___y_3697_ = v___y_3713_;
v___y_3698_ = v___y_3714_;
v___y_3699_ = v_res_3720_;
v___y_3700_ = v___y_3715_;
v___y_3701_ = v___y_3716_;
v___y_3702_ = v_pos_3721_;
goto v___jp_3695_;
}
else
{
lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3742_; 
lean_inc(v_val_3725_);
lean_dec(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec(v___y_3713_);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_res_3720_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; 
v_unused_3743_ = lean_ctor_get(v_res_3720_, 0);
lean_dec(v_unused_3743_);
v___x_3729_ = v_res_3720_;
v_isShared_3730_ = v_isSharedCheck_3742_;
goto v_resetjp_3728_;
}
else
{
lean_dec(v_res_3720_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3742_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3737_; 
v___x_3731_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4));
v___x_3732_ = l_Int_repr(v_val_3725_);
lean_dec(v_val_3725_);
v___x_3733_ = lean_string_append(v___x_3731_, v___x_3732_);
lean_dec_ref(v___x_3732_);
v___x_3734_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5));
v___x_3735_ = lean_string_append(v___x_3733_, v___x_3734_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3735_);
v___x_3737_ = v___x_3729_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3735_);
v___x_3737_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3739_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set_tag(v___x_3723_, 1);
lean_ctor_set(v___x_3723_, 1, v___x_3737_);
v___x_3739_ = v___x_3723_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_pos_3721_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3746_; 
v_pos_3746_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_pos_3746_);
lean_dec_ref_known(v___x_3719_, 2);
v___y_3696_ = v___y_3712_;
v___y_3697_ = v___y_3713_;
v___y_3698_ = v___y_3714_;
v___y_3699_ = v_res_3720_;
v___y_3700_ = v___y_3715_;
v___y_3701_ = v___y_3716_;
v___y_3702_ = v_pos_3746_;
goto v___jp_3695_;
}
}
else
{
lean_object* v_pos_3747_; lean_object* v_err_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec(v___y_3713_);
v_pos_3747_ = lean_ctor_get(v___x_3719_, 0);
v_err_3748_ = lean_ctor_get(v___x_3719_, 1);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3719_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_err_3748_);
lean_inc(v_pos_3747_);
lean_dec(v___x_3719_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_pos_3747_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v_err_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
v___jp_3756_:
{
if (v___y_3761_ == 0)
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3762_ = lean_unsigned_to_nat(60u);
v___x_3763_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6);
lean_inc_ref(v___y_3709_);
v___x_3764_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3709_, v___f_3710_, v___x_3763_, v_withMinutes_3667_, v___y_3759_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_res_3765_; 
v_res_3765_ = lean_ctor_get(v___x_3764_, 1);
lean_inc(v_res_3765_);
if (lean_obj_tag(v_res_3765_) == 1)
{
lean_object* v_pos_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3789_; 
v_pos_3766_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3789_ == 0)
{
lean_object* v_unused_3790_; 
v_unused_3790_ = lean_ctor_get(v___x_3764_, 1);
lean_dec(v_unused_3790_);
v___x_3768_ = v___x_3764_;
v_isShared_3769_ = v_isSharedCheck_3789_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_pos_3766_);
lean_dec(v___x_3764_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3789_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v_val_3770_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
v_val_3770_ = lean_ctor_get(v_res_3765_, 0);
v___x_3771_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3);
v___x_3772_ = lean_int_dec_lt(v___x_3771_, v_val_3770_);
if (v___x_3772_ == 0)
{
lean_del_object(v___x_3768_);
v___y_3712_ = v___y_3757_;
v___y_3713_ = v___y_3758_;
v___y_3714_ = v_res_3765_;
v___y_3715_ = v___x_3762_;
v___y_3716_ = v___y_3760_;
v___y_3717_ = v_pos_3766_;
goto v___jp_3711_;
}
else
{
lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3787_; 
lean_inc(v_val_3770_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3709_);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_res_3765_);
if (v_isSharedCheck_3787_ == 0)
{
lean_object* v_unused_3788_; 
v_unused_3788_ = lean_ctor_get(v_res_3765_, 0);
lean_dec(v_unused_3788_);
v___x_3774_ = v_res_3765_;
v_isShared_3775_ = v_isSharedCheck_3787_;
goto v_resetjp_3773_;
}
else
{
lean_dec(v_res_3765_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3787_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3776_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3777_ = l_Int_repr(v_val_3770_);
lean_dec(v_val_3770_);
v___x_3778_ = lean_string_append(v___x_3776_, v___x_3777_);
lean_dec_ref(v___x_3777_);
v___x_3779_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5));
v___x_3780_ = lean_string_append(v___x_3778_, v___x_3779_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 0, v___x_3780_);
v___x_3782_ = v___x_3774_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3784_; 
if (v_isShared_3769_ == 0)
{
lean_ctor_set_tag(v___x_3768_, 1);
lean_ctor_set(v___x_3768_, 1, v___x_3782_);
v___x_3784_ = v___x_3768_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_pos_3766_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v___x_3782_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3791_; 
v_pos_3791_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_pos_3791_);
lean_dec_ref_known(v___x_3764_, 2);
v___y_3712_ = v___y_3757_;
v___y_3713_ = v___y_3758_;
v___y_3714_ = v_res_3765_;
v___y_3715_ = v___x_3762_;
v___y_3716_ = v___y_3760_;
v___y_3717_ = v_pos_3791_;
goto v___jp_3711_;
}
}
else
{
lean_object* v_pos_3792_; lean_object* v_err_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3709_);
v_pos_3792_ = lean_ctor_get(v___x_3764_, 0);
v_err_3793_ = lean_ctor_get(v___x_3764_, 1);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3764_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_err_3793_);
lean_inc(v_pos_3792_);
lean_dec(v___x_3764_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_pos_3792_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_err_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
lean_dec_ref(v___y_3709_);
v___x_3801_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8));
v___x_3802_ = l_Int_repr(v___y_3758_);
lean_dec(v___y_3758_);
v___x_3803_ = lean_string_append(v___x_3801_, v___x_3802_);
lean_dec_ref(v___x_3802_);
v___x_3804_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9));
v___x_3805_ = lean_string_append(v___x_3803_, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
v___x_3807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___y_3759_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
return v___x_3807_;
}
}
v___jp_3808_:
{
lean_object* v___x_3811_; 
v___x_3811_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3809_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_pos_3812_; lean_object* v_res_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v_pos_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_pos_3812_);
v_res_3813_ = lean_ctor_get(v___x_3811_, 1);
lean_inc(v_res_3813_);
lean_dec_ref_known(v___x_3811_, 2);
v___x_3814_ = lean_nat_to_int(v_res_3813_);
v___x_3815_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_3816_ = lean_int_dec_lt(v___x_3814_, v___x_3815_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; uint8_t v___x_3818_; 
v___x_3817_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10);
v___x_3818_ = lean_int_dec_lt(v___x_3817_, v___x_3814_);
v___y_3757_ = v___x_3815_;
v___y_3758_ = v___x_3814_;
v___y_3759_ = v_pos_3812_;
v___y_3760_ = v_res_3810_;
v___y_3761_ = v___x_3818_;
goto v___jp_3756_;
}
else
{
v___y_3757_ = v___x_3815_;
v___y_3758_ = v___x_3814_;
v___y_3759_ = v_pos_3812_;
v___y_3760_ = v_res_3810_;
v___y_3761_ = v___x_3816_;
goto v___jp_3756_;
}
}
else
{
lean_object* v_pos_3819_; lean_object* v_err_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v___y_3709_);
v_pos_3819_ = lean_ctor_get(v___x_3811_, 0);
v_err_3820_ = lean_ctor_get(v___x_3811_, 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3811_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_err_3820_);
lean_inc(v_pos_3819_);
lean_dec(v___x_3811_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_pos_3819_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_err_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
v___jp_3828_:
{
uint8_t v_decide_3833_; 
v_decide_3833_ = lean_nat_dec_eq(v_snd_3707_, v_snd_3831_);
lean_dec(v_snd_3707_);
if (v_decide_3833_ == 0)
{
lean_object* v___x_3834_; 
lean_dec(v_snd_3831_);
lean_dec(v_fst_3830_);
lean_dec_ref(v___y_3709_);
lean_inc(v_err_3832_);
v___x_3834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3834_, 0, v_pos_3829_);
lean_ctor_set(v___x_3834_, 1, v_err_3832_);
return v___x_3834_;
}
else
{
lean_object* v___x_3835_; uint8_t v_decide_3836_; 
v___x_3835_ = lean_string_utf8_byte_size(v_fst_3830_);
v_decide_3836_ = lean_nat_dec_eq(v_snd_3831_, v___x_3835_);
if (v_decide_3836_ == 0)
{
if (v_decide_3833_ == 0)
{
lean_dec(v_snd_3831_);
lean_dec(v_fst_3830_);
lean_dec_ref(v___y_3709_);
v___y_3672_ = v_pos_3829_;
goto v___jp_3671_;
}
else
{
uint32_t v___x_3837_; uint32_t v_c_3838_; uint8_t v___x_3839_; 
v___x_3837_ = 45;
v_c_3838_ = lean_string_utf8_get_fast(v_fst_3830_, v_snd_3831_);
v___x_3839_ = lean_uint32_dec_eq(v_c_3838_, v___x_3837_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_dec(v_snd_3831_);
lean_dec(v_fst_3830_);
lean_dec_ref(v___y_3709_);
v___x_3840_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14);
v___x_3841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3841_, 0, v_pos_3829_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
return v___x_3841_;
}
else
{
lean_object* v___x_3842_; lean_object* v_it_x27_3843_; lean_object* v___x_3844_; 
lean_dec_ref(v_pos_3829_);
v___x_3842_ = lean_string_utf8_next_fast(v_fst_3830_, v_snd_3831_);
lean_dec(v_snd_3831_);
v_it_x27_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3843_, 0, v_fst_3830_);
lean_ctor_set(v_it_x27_3843_, 1, v___x_3842_);
v___x_3844_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v_pos_3809_ = v_it_x27_3843_;
v_res_3810_ = v___x_3844_;
goto v___jp_3808_;
}
}
}
else
{
lean_dec(v_snd_3831_);
lean_dec(v_fst_3830_);
lean_dec_ref(v___y_3709_);
v___y_3672_ = v_pos_3829_;
goto v___jp_3671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object* v_withMinutes_3863_, lean_object* v_withSeconds_3864_, lean_object* v_withColon_3865_, lean_object* v_a_3866_){
_start:
{
uint8_t v_withMinutes_boxed_3867_; uint8_t v_withSeconds_boxed_3868_; uint8_t v_withColon_boxed_3869_; lean_object* v_res_3870_; 
v_withMinutes_boxed_3867_ = lean_unbox(v_withMinutes_3863_);
v_withSeconds_boxed_3868_ = lean_unbox(v_withSeconds_3864_);
v_withColon_boxed_3869_ = lean_unbox(v_withColon_3865_);
v_res_3870_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_withMinutes_boxed_3867_, v_withSeconds_boxed_3868_, v_withColon_boxed_3869_, v_a_3866_);
return v_res_3870_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1(void){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = lean_unsigned_to_nat(2000u);
v___x_3874_ = lean_nat_to_int(v___x_3873_);
return v___x_3874_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3881_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3882_ = lean_int_sub(v___x_3881_, v___x_3880_);
return v___x_3882_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v_range_3885_; 
v___x_3883_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3884_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5);
v_range_3885_ = lean_int_add(v___x_3884_, v___x_3883_);
return v_range_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object* v_config_3888_, lean_object* v_x_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v___y_3892_; 
switch(lean_obj_tag(v_x_3889_))
{
case 0:
{
uint8_t v_presentation_3918_; 
v_presentation_3918_ = lean_ctor_get_uint8(v_x_3889_, 0);
lean_dec_ref_known(v_x_3889_, 0);
switch(v_presentation_3918_)
{
case 1:
{
lean_object* v_dateformat_3919_; lean_object* v_symbols_3920_; lean_object* v___x_3921_; 
v_dateformat_3919_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_3919_);
lean_dec_ref(v_config_3888_);
v_symbols_3920_ = lean_ctor_get(v_dateformat_3919_, 1);
lean_inc_ref(v_symbols_3920_);
lean_dec_ref(v_dateformat_3919_);
v___x_3921_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(v_symbols_3920_, v_a_3890_);
return v___x_3921_;
}
case 2:
{
lean_object* v_dateformat_3922_; lean_object* v_symbols_3923_; lean_object* v___x_3924_; 
v_dateformat_3922_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_3922_);
lean_dec_ref(v_config_3888_);
v_symbols_3923_ = lean_ctor_get(v_dateformat_3922_, 1);
lean_inc_ref(v_symbols_3923_);
lean_dec_ref(v_dateformat_3922_);
v___x_3924_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(v_symbols_3923_, v_a_3890_);
return v___x_3924_;
}
default: 
{
lean_object* v_dateformat_3925_; lean_object* v_symbols_3926_; lean_object* v___x_3927_; 
v_dateformat_3925_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_3925_);
lean_dec_ref(v_config_3888_);
v_symbols_3926_ = lean_ctor_get(v_dateformat_3925_, 1);
lean_inc_ref(v_symbols_3926_);
lean_dec_ref(v_dateformat_3925_);
v___x_3927_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(v_symbols_3926_, v_a_3890_);
return v___x_3927_;
}
}
}
case 1:
{
lean_object* v_presentation_3928_; 
lean_dec_ref(v_config_3888_);
v_presentation_3928_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_3928_);
lean_dec_ref_known(v_x_3889_, 1);
switch(lean_obj_tag(v_presentation_3928_))
{
case 0:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_3930_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3929_, v_a_3890_);
return v___x_3930_;
}
case 1:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = lean_unsigned_to_nat(2u);
v___x_3932_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3931_, v_a_3890_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_pos_3933_; lean_object* v_res_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3944_; 
v_pos_3933_ = lean_ctor_get(v___x_3932_, 0);
v_res_3934_ = lean_ctor_get(v___x_3932_, 1);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3936_ = v___x_3932_;
v_isShared_3937_ = v_isSharedCheck_3944_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_res_3934_);
lean_inc(v_pos_3933_);
lean_dec(v___x_3932_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3944_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3938_ = lean_nat_to_int(v_res_3934_);
v___x_3939_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3940_ = lean_int_add(v___x_3939_, v___x_3938_);
lean_dec(v___x_3938_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 1, v___x_3940_);
v___x_3942_ = v___x_3936_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_pos_3933_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
else
{
lean_object* v_pos_3945_; lean_object* v_err_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
v_pos_3945_ = lean_ctor_get(v___x_3932_, 0);
v_err_3946_ = lean_ctor_get(v___x_3932_, 1);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3932_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_err_3946_);
lean_inc(v_pos_3945_);
lean_dec(v___x_3932_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_pos_3945_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v_err_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
case 2:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3954_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_3955_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3954_, v_a_3890_);
return v___x_3955_;
}
default: 
{
lean_object* v_num_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v_num_3956_ = lean_ctor_get(v_presentation_3928_, 0);
lean_inc(v_num_3956_);
lean_dec_ref_known(v_presentation_3928_, 1);
v___x_3957_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_3957_, 0, v_num_3956_);
v___x_3958_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3957_, v_a_3890_);
return v___x_3958_;
}
}
}
case 2:
{
lean_object* v_presentation_3959_; 
lean_dec_ref(v_config_3888_);
v_presentation_3959_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_3959_);
lean_dec_ref_known(v_x_3889_, 1);
switch(lean_obj_tag(v_presentation_3959_))
{
case 0:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = lean_unsigned_to_nat(1u);
v___x_3961_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3960_, v_a_3890_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_pos_3962_; lean_object* v_res_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3971_; 
v_pos_3962_ = lean_ctor_get(v___x_3961_, 0);
v_res_3963_ = lean_ctor_get(v___x_3961_, 1);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3965_ = v___x_3961_;
v_isShared_3966_ = v_isSharedCheck_3971_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_res_3963_);
lean_inc(v_pos_3962_);
lean_dec(v___x_3961_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3971_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3967_ = lean_nat_to_int(v_res_3963_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 1, v___x_3967_);
v___x_3969_ = v___x_3965_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_pos_3962_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
else
{
lean_object* v_pos_3972_; lean_object* v_err_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
v_pos_3972_ = lean_ctor_get(v___x_3961_, 0);
v_err_3973_ = lean_ctor_get(v___x_3961_, 1);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3961_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_err_3973_);
lean_inc(v_pos_3972_);
lean_dec(v___x_3961_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_pos_3972_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_err_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
case 1:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3981_ = lean_unsigned_to_nat(2u);
v___x_3982_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3981_, v_a_3890_);
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
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3988_ = lean_nat_to_int(v_res_3984_);
v___x_3989_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3990_ = lean_int_add(v___x_3989_, v___x_3988_);
lean_dec(v___x_3988_);
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
case 2:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = lean_unsigned_to_nat(4u);
v___x_4005_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_4004_, v_a_3890_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_pos_4006_; lean_object* v_res_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4015_; 
v_pos_4006_ = lean_ctor_get(v___x_4005_, 0);
v_res_4007_ = lean_ctor_get(v___x_4005_, 1);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4009_ = v___x_4005_;
v_isShared_4010_ = v_isSharedCheck_4015_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_res_4007_);
lean_inc(v_pos_4006_);
lean_dec(v___x_4005_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4015_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4013_; 
v___x_4011_ = lean_nat_to_int(v_res_4007_);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 1, v___x_4011_);
v___x_4013_ = v___x_4009_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_pos_4006_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
else
{
lean_object* v_pos_4016_; lean_object* v_err_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
v_pos_4016_ = lean_ctor_get(v___x_4005_, 0);
v_err_4017_ = lean_ctor_get(v___x_4005_, 1);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4005_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_err_4017_);
lean_inc(v_pos_4016_);
lean_dec(v___x_4005_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_pos_4016_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v_err_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
default: 
{
lean_object* v_num_4025_; lean_object* v___x_4026_; 
v_num_4025_ = lean_ctor_get(v_presentation_3959_, 0);
lean_inc(v_num_4025_);
lean_dec_ref_known(v_presentation_3959_, 1);
v___x_4026_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_num_4025_, v_a_3890_);
lean_dec(v_num_4025_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_pos_4027_; lean_object* v_res_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4036_; 
v_pos_4027_ = lean_ctor_get(v___x_4026_, 0);
v_res_4028_ = lean_ctor_get(v___x_4026_, 1);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4030_ = v___x_4026_;
v_isShared_4031_ = v_isSharedCheck_4036_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_res_4028_);
lean_inc(v_pos_4027_);
lean_dec(v___x_4026_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4036_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4032_; lean_object* v___x_4034_; 
v___x_4032_ = lean_nat_to_int(v_res_4028_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4032_);
v___x_4034_ = v___x_4030_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_pos_4027_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_4032_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
else
{
lean_object* v_pos_4037_; lean_object* v_err_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
v_pos_4037_ = lean_ctor_get(v___x_4026_, 0);
v_err_4038_ = lean_ctor_get(v___x_4026_, 1);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4026_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_err_4038_);
lean_inc(v_pos_4037_);
lean_dec(v___x_4026_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_pos_4037_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_err_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
}
case 3:
{
lean_object* v_presentation_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
lean_dec_ref(v_config_3888_);
v_presentation_4046_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4046_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4047_ = lean_unsigned_to_nat(1u);
v___x_4048_ = lean_unsigned_to_nat(366u);
v___x_4049_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4049_, 0, v_presentation_4046_);
v___x_4050_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4047_, v___x_4048_, v___x_4049_, v_a_3890_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_pos_4051_; lean_object* v_res_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4062_; 
v_pos_4051_ = lean_ctor_get(v___x_4050_, 0);
v_res_4052_ = lean_ctor_get(v___x_4050_, 1);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4054_ = v___x_4050_;
v_isShared_4055_ = v_isSharedCheck_4062_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_res_4052_);
lean_inc(v_pos_4051_);
lean_dec(v___x_4050_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4062_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
uint8_t v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4060_; 
v___x_4056_ = 1;
v___x_4057_ = lean_box(v___x_4056_);
v___x_4058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
lean_ctor_set(v___x_4058_, 1, v_res_4052_);
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 1, v___x_4058_);
v___x_4060_ = v___x_4054_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_pos_4051_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v___x_4058_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
else
{
lean_object* v_pos_4063_; lean_object* v_err_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
v_pos_4063_ = lean_ctor_get(v___x_4050_, 0);
v_err_4064_ = lean_ctor_get(v___x_4050_, 1);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4050_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_err_4064_);
lean_inc(v_pos_4063_);
lean_dec(v___x_4050_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_pos_4063_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_err_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
case 4:
{
lean_object* v_presentation_4072_; 
v_presentation_4072_ = lean_ctor_get(v_x_3889_, 0);
lean_inc_ref(v_presentation_4072_);
lean_dec_ref_known(v_x_3889_, 1);
if (lean_obj_tag(v_presentation_4072_) == 0)
{
lean_object* v_val_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_dec_ref(v_config_3888_);
v_val_4073_ = lean_ctor_get(v_presentation_4072_, 0);
lean_inc(v_val_4073_);
lean_dec_ref_known(v_presentation_4072_, 1);
v___x_4074_ = lean_unsigned_to_nat(1u);
v___x_4075_ = lean_unsigned_to_nat(12u);
v___x_4076_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4076_, 0, v_val_4073_);
v___x_4077_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4074_, v___x_4075_, v___x_4076_, v_a_3890_);
return v___x_4077_;
}
else
{
lean_object* v_val_4078_; uint8_t v___x_4079_; 
v_val_4078_ = lean_ctor_get(v_presentation_4072_, 0);
lean_inc(v_val_4078_);
lean_dec_ref_known(v_presentation_4072_, 1);
v___x_4079_ = lean_unbox(v_val_4078_);
lean_dec(v_val_4078_);
switch(v___x_4079_)
{
case 1:
{
lean_object* v_dateformat_4080_; lean_object* v_symbols_4081_; lean_object* v___x_4082_; 
v_dateformat_4080_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4080_);
lean_dec_ref(v_config_3888_);
v_symbols_4081_ = lean_ctor_get(v_dateformat_4080_, 1);
lean_inc_ref(v_symbols_4081_);
lean_dec_ref(v_dateformat_4080_);
v___x_4082_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_4081_, v_a_3890_);
return v___x_4082_;
}
case 2:
{
lean_object* v_dateformat_4083_; lean_object* v_symbols_4084_; lean_object* v___x_4085_; 
v_dateformat_4083_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4083_);
lean_dec_ref(v_config_3888_);
v_symbols_4084_ = lean_ctor_get(v_dateformat_4083_, 1);
lean_inc_ref(v_symbols_4084_);
lean_dec_ref(v_dateformat_4083_);
v___x_4085_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_4084_, v_a_3890_);
return v___x_4085_;
}
default: 
{
lean_object* v_dateformat_4086_; lean_object* v_symbols_4087_; lean_object* v___x_4088_; 
v_dateformat_4086_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4086_);
lean_dec_ref(v_config_3888_);
v_symbols_4087_ = lean_ctor_get(v_dateformat_4086_, 1);
lean_inc_ref(v_symbols_4087_);
lean_dec_ref(v_dateformat_4086_);
v___x_4088_ = l_Std_Time_parseMonthShort(v_symbols_4087_, v_a_3890_);
return v___x_4088_;
}
}
}
}
case 5:
{
lean_object* v_presentation_4089_; 
v_presentation_4089_ = lean_ctor_get(v_x_3889_, 0);
lean_inc_ref(v_presentation_4089_);
lean_dec_ref_known(v_x_3889_, 1);
if (lean_obj_tag(v_presentation_4089_) == 0)
{
lean_object* v_val_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
lean_dec_ref(v_config_3888_);
v_val_4090_ = lean_ctor_get(v_presentation_4089_, 0);
lean_inc(v_val_4090_);
lean_dec_ref_known(v_presentation_4089_, 1);
v___x_4091_ = lean_unsigned_to_nat(1u);
v___x_4092_ = lean_unsigned_to_nat(12u);
v___x_4093_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4093_, 0, v_val_4090_);
v___x_4094_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4091_, v___x_4092_, v___x_4093_, v_a_3890_);
return v___x_4094_;
}
else
{
lean_object* v_val_4095_; uint8_t v___x_4096_; 
v_val_4095_ = lean_ctor_get(v_presentation_4089_, 0);
lean_inc(v_val_4095_);
lean_dec_ref_known(v_presentation_4089_, 1);
v___x_4096_ = lean_unbox(v_val_4095_);
lean_dec(v_val_4095_);
switch(v___x_4096_)
{
case 1:
{
lean_object* v_dateformat_4097_; lean_object* v_symbols_4098_; lean_object* v___x_4099_; 
v_dateformat_4097_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4097_);
lean_dec_ref(v_config_3888_);
v_symbols_4098_ = lean_ctor_get(v_dateformat_4097_, 1);
lean_inc_ref(v_symbols_4098_);
lean_dec_ref(v_dateformat_4097_);
v___x_4099_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_4098_, v_a_3890_);
return v___x_4099_;
}
case 2:
{
lean_object* v_dateformat_4100_; lean_object* v_symbols_4101_; lean_object* v___x_4102_; 
v_dateformat_4100_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4100_);
lean_dec_ref(v_config_3888_);
v_symbols_4101_ = lean_ctor_get(v_dateformat_4100_, 1);
lean_inc_ref(v_symbols_4101_);
lean_dec_ref(v_dateformat_4100_);
v___x_4102_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_4101_, v_a_3890_);
return v___x_4102_;
}
default: 
{
lean_object* v_dateformat_4103_; lean_object* v_symbols_4104_; lean_object* v___x_4105_; 
v_dateformat_4103_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4103_);
lean_dec_ref(v_config_3888_);
v_symbols_4104_ = lean_ctor_get(v_dateformat_4103_, 1);
lean_inc_ref(v_symbols_4104_);
lean_dec_ref(v_dateformat_4103_);
v___x_4105_ = l_Std_Time_parseMonthShort(v_symbols_4104_, v_a_3890_);
return v___x_4105_;
}
}
}
}
case 6:
{
lean_object* v_presentation_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
lean_dec_ref(v_config_3888_);
v_presentation_4106_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4106_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4107_ = lean_unsigned_to_nat(1u);
v___x_4108_ = lean_unsigned_to_nat(31u);
v___x_4109_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4109_, 0, v_presentation_4106_);
v___x_4110_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4107_, v___x_4108_, v___x_4109_, v_a_3890_);
return v___x_4110_;
}
case 7:
{
lean_object* v_presentation_4111_; 
v_presentation_4111_ = lean_ctor_get(v_x_3889_, 0);
lean_inc_ref(v_presentation_4111_);
lean_dec_ref_known(v_x_3889_, 1);
if (lean_obj_tag(v_presentation_4111_) == 0)
{
lean_object* v_val_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
lean_dec_ref(v_config_3888_);
v_val_4112_ = lean_ctor_get(v_presentation_4111_, 0);
lean_inc(v_val_4112_);
lean_dec_ref_known(v_presentation_4111_, 1);
v___x_4113_ = lean_unsigned_to_nat(1u);
v___x_4114_ = lean_unsigned_to_nat(4u);
v___x_4115_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4115_, 0, v_val_4112_);
v___x_4116_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4113_, v___x_4114_, v___x_4115_, v_a_3890_);
return v___x_4116_;
}
else
{
lean_object* v_val_4117_; uint8_t v___x_4118_; 
v_val_4117_ = lean_ctor_get(v_presentation_4111_, 0);
lean_inc(v_val_4117_);
lean_dec_ref_known(v_presentation_4111_, 1);
v___x_4118_ = lean_unbox(v_val_4117_);
lean_dec(v_val_4117_);
switch(v___x_4118_)
{
case 0:
{
lean_object* v_dateformat_4119_; lean_object* v_symbols_4120_; lean_object* v___x_4121_; 
v_dateformat_4119_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4119_);
lean_dec_ref(v_config_3888_);
v_symbols_4120_ = lean_ctor_get(v_dateformat_4119_, 1);
lean_inc_ref(v_symbols_4120_);
lean_dec_ref(v_dateformat_4119_);
v___x_4121_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4120_, v_a_3890_);
return v___x_4121_;
}
case 1:
{
lean_object* v_dateformat_4122_; lean_object* v_symbols_4123_; lean_object* v___x_4124_; 
v_dateformat_4122_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4122_);
lean_dec_ref(v_config_3888_);
v_symbols_4123_ = lean_ctor_get(v_dateformat_4122_, 1);
lean_inc_ref(v_symbols_4123_);
lean_dec_ref(v_dateformat_4122_);
v___x_4124_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4123_, v_a_3890_);
return v___x_4124_;
}
default: 
{
lean_object* v_dateformat_4125_; lean_object* v_symbols_4126_; lean_object* v___x_4127_; 
v_dateformat_4125_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4125_);
lean_dec_ref(v_config_3888_);
v_symbols_4126_ = lean_ctor_get(v_dateformat_4125_, 1);
lean_inc_ref(v_symbols_4126_);
lean_dec_ref(v_dateformat_4125_);
v___x_4127_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_4126_, v_a_3890_);
return v___x_4127_;
}
}
}
}
case 8:
{
lean_object* v_presentation_4128_; 
v_presentation_4128_ = lean_ctor_get(v_x_3889_, 0);
lean_inc_ref(v_presentation_4128_);
lean_dec_ref_known(v_x_3889_, 1);
if (lean_obj_tag(v_presentation_4128_) == 0)
{
lean_object* v_val_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
lean_dec_ref(v_config_3888_);
v_val_4129_ = lean_ctor_get(v_presentation_4128_, 0);
lean_inc(v_val_4129_);
lean_dec_ref_known(v_presentation_4128_, 1);
v___x_4130_ = lean_unsigned_to_nat(1u);
v___x_4131_ = lean_unsigned_to_nat(4u);
v___x_4132_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4132_, 0, v_val_4129_);
v___x_4133_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4130_, v___x_4131_, v___x_4132_, v_a_3890_);
return v___x_4133_;
}
else
{
lean_object* v_val_4134_; uint8_t v___x_4135_; 
v_val_4134_ = lean_ctor_get(v_presentation_4128_, 0);
lean_inc(v_val_4134_);
lean_dec_ref_known(v_presentation_4128_, 1);
v___x_4135_ = lean_unbox(v_val_4134_);
lean_dec(v_val_4134_);
switch(v___x_4135_)
{
case 0:
{
lean_object* v_dateformat_4136_; lean_object* v_symbols_4137_; lean_object* v___x_4138_; 
v_dateformat_4136_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4136_);
lean_dec_ref(v_config_3888_);
v_symbols_4137_ = lean_ctor_get(v_dateformat_4136_, 1);
lean_inc_ref(v_symbols_4137_);
lean_dec_ref(v_dateformat_4136_);
v___x_4138_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4137_, v_a_3890_);
return v___x_4138_;
}
case 1:
{
lean_object* v_dateformat_4139_; lean_object* v_symbols_4140_; lean_object* v___x_4141_; 
v_dateformat_4139_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4139_);
lean_dec_ref(v_config_3888_);
v_symbols_4140_ = lean_ctor_get(v_dateformat_4139_, 1);
lean_inc_ref(v_symbols_4140_);
lean_dec_ref(v_dateformat_4139_);
v___x_4141_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4140_, v_a_3890_);
return v___x_4141_;
}
default: 
{
lean_object* v_dateformat_4142_; lean_object* v_symbols_4143_; lean_object* v___x_4144_; 
v_dateformat_4142_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4142_);
lean_dec_ref(v_config_3888_);
v_symbols_4143_ = lean_ctor_get(v_dateformat_4142_, 1);
lean_inc_ref(v_symbols_4143_);
lean_dec_ref(v_dateformat_4142_);
v___x_4144_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_4143_, v_a_3890_);
return v___x_4144_;
}
}
}
}
case 9:
{
lean_object* v_presentation_4145_; 
lean_dec_ref(v_config_3888_);
v_presentation_4145_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4145_);
lean_dec_ref_known(v_x_3889_, 1);
switch(lean_obj_tag(v_presentation_4145_))
{
case 0:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_4147_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4146_, v_a_3890_);
return v___x_4147_;
}
case 1:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_unsigned_to_nat(2u);
v___x_4149_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_4148_, v_a_3890_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_pos_4150_; lean_object* v_res_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4161_; 
v_pos_4150_ = lean_ctor_get(v___x_4149_, 0);
v_res_4151_ = lean_ctor_get(v___x_4149_, 1);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4153_ = v___x_4149_;
v_isShared_4154_ = v_isSharedCheck_4161_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_res_4151_);
lean_inc(v_pos_4150_);
lean_dec(v___x_4149_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4161_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4159_; 
v___x_4155_ = lean_nat_to_int(v_res_4151_);
v___x_4156_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_4157_ = lean_int_add(v___x_4156_, v___x_4155_);
lean_dec(v___x_4155_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 1, v___x_4157_);
v___x_4159_ = v___x_4153_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_pos_4150_);
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
else
{
lean_object* v_pos_4162_; lean_object* v_err_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
v_pos_4162_ = lean_ctor_get(v___x_4149_, 0);
v_err_4163_ = lean_ctor_get(v___x_4149_, 1);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4149_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_err_4163_);
lean_inc(v_pos_4162_);
lean_dec(v___x_4149_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_pos_4162_);
lean_ctor_set(v_reuseFailAlloc_4169_, 1, v_err_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
case 2:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_4172_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4171_, v_a_3890_);
return v___x_4172_;
}
default: 
{
lean_object* v_num_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v_num_4173_ = lean_ctor_get(v_presentation_4145_, 0);
lean_inc(v_num_4173_);
lean_dec_ref_known(v_presentation_4145_, 1);
v___x_4174_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_4174_, 0, v_num_4173_);
v___x_4175_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4174_, v_a_3890_);
return v___x_4175_;
}
}
}
case 10:
{
lean_object* v_presentation_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
lean_dec_ref(v_config_3888_);
v_presentation_4176_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4176_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4177_ = lean_unsigned_to_nat(1u);
v___x_4178_ = lean_unsigned_to_nat(53u);
v___x_4179_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4179_, 0, v_presentation_4176_);
v___x_4180_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4177_, v___x_4178_, v___x_4179_, v_a_3890_);
return v___x_4180_;
}
case 11:
{
lean_object* v_presentation_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_dec_ref(v_config_3888_);
v_presentation_4181_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4181_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4182_ = lean_unsigned_to_nat(1u);
v___x_4183_ = lean_unsigned_to_nat(6u);
v___x_4184_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4184_, 0, v_presentation_4181_);
v___x_4185_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4182_, v___x_4183_, v___x_4184_, v_a_3890_);
return v___x_4185_;
}
case 12:
{
uint8_t v_presentation_4186_; 
v_presentation_4186_ = lean_ctor_get_uint8(v_x_3889_, 0);
lean_dec_ref_known(v_x_3889_, 0);
switch(v_presentation_4186_)
{
case 1:
{
lean_object* v_dateformat_4187_; lean_object* v_symbols_4188_; lean_object* v___x_4189_; 
v_dateformat_4187_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4187_);
lean_dec_ref(v_config_3888_);
v_symbols_4188_ = lean_ctor_get(v_dateformat_4187_, 1);
lean_inc_ref(v_symbols_4188_);
lean_dec_ref(v_dateformat_4187_);
v___x_4189_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4188_, v_a_3890_);
return v___x_4189_;
}
case 2:
{
lean_object* v_dateformat_4190_; lean_object* v_symbols_4191_; lean_object* v___x_4192_; 
v_dateformat_4190_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4190_);
lean_dec_ref(v_config_3888_);
v_symbols_4191_ = lean_ctor_get(v_dateformat_4190_, 1);
lean_inc_ref(v_symbols_4191_);
lean_dec_ref(v_dateformat_4190_);
v___x_4192_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4191_, v_a_3890_);
return v___x_4192_;
}
default: 
{
lean_object* v_dateformat_4193_; lean_object* v_symbols_4194_; lean_object* v___x_4195_; 
v_dateformat_4193_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4193_);
lean_dec_ref(v_config_3888_);
v_symbols_4194_ = lean_ctor_get(v_dateformat_4193_, 1);
lean_inc_ref(v_symbols_4194_);
lean_dec_ref(v_dateformat_4193_);
v___x_4195_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4194_, v_a_3890_);
return v___x_4195_;
}
}
}
case 13:
{
lean_object* v_presentation_4196_; 
v_presentation_4196_ = lean_ctor_get(v_x_3889_, 0);
lean_inc_ref(v_presentation_4196_);
lean_dec_ref_known(v_x_3889_, 1);
if (lean_obj_tag(v_presentation_4196_) == 0)
{
lean_object* v_val_4197_; lean_object* v___x_4198_; 
v_val_4197_ = lean_ctor_get(v_presentation_4196_, 0);
lean_inc(v_val_4197_);
lean_dec_ref_known(v_presentation_4196_, 1);
v___x_4198_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4197_, v_a_3890_);
lean_dec(v_val_4197_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_pos_4199_; lean_object* v_res_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4236_; 
v_pos_4199_ = lean_ctor_get(v___x_4198_, 0);
v_res_4200_ = lean_ctor_get(v___x_4198_, 1);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4202_ = v___x_4198_;
v_isShared_4203_ = v_isSharedCheck_4236_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_res_4200_);
lean_inc(v_pos_4199_);
lean_dec(v___x_4198_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4236_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4204_; uint8_t v___x_4205_; lean_object* v___x_4206_; uint8_t v___y_4208_; 
v___x_4204_ = lean_unsigned_to_nat(1u);
v___x_4205_ = lean_nat_dec_le(v___x_4204_, v_res_4200_);
v___x_4206_ = lean_unsigned_to_nat(7u);
if (v___x_4205_ == 0)
{
v___y_4208_ = v___x_4205_;
goto v___jp_4207_;
}
else
{
uint8_t v___x_4235_; 
v___x_4235_ = lean_nat_dec_le(v_res_4200_, v___x_4206_);
v___y_4208_ = v___x_4235_;
goto v___jp_4207_;
}
v___jp_4207_:
{
if (v___y_4208_ == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4211_; 
lean_dec(v_res_4200_);
lean_dec_ref(v_config_3888_);
v___x_4209_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4203_ == 0)
{
lean_ctor_set_tag(v___x_4202_, 1);
lean_ctor_set(v___x_4202_, 1, v___x_4209_);
v___x_4211_ = v___x_4202_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_pos_4199_);
lean_ctor_set(v_reuseFailAlloc_4212_, 1, v___x_4209_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
else
{
lean_object* v_dateformat_4213_; uint8_t v_firstDayOfWeek_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v_range_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4233_; 
v_dateformat_4213_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4213_);
lean_dec_ref(v_config_3888_);
v_firstDayOfWeek_4214_ = lean_ctor_get_uint8(v_dateformat_4213_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4213_);
v___x_4215_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4214_);
v___x_4216_ = lean_nat_to_int(v_res_4200_);
v___x_4217_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4218_ = lean_int_sub(v___x_4216_, v___x_4217_);
lean_dec(v___x_4216_);
v___x_4219_ = lean_int_add(v___x_4218_, v___x_4215_);
lean_dec(v___x_4215_);
lean_dec(v___x_4218_);
v___x_4220_ = lean_int_sub(v___x_4219_, v___x_4217_);
lean_dec(v___x_4219_);
v___x_4221_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4222_ = lean_int_emod(v___x_4220_, v___x_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_int_add(v___x_4222_, v___x_4217_);
lean_dec(v___x_4222_);
v_range_4224_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4225_ = lean_int_sub(v___x_4223_, v___x_4217_);
lean_dec(v___x_4223_);
v___x_4226_ = lean_int_emod(v___x_4225_, v_range_4224_);
lean_dec(v___x_4225_);
v___x_4227_ = lean_int_add(v___x_4226_, v_range_4224_);
lean_dec(v___x_4226_);
v___x_4228_ = lean_int_emod(v___x_4227_, v_range_4224_);
lean_dec(v___x_4227_);
v___x_4229_ = lean_int_add(v___x_4228_, v___x_4217_);
lean_dec(v___x_4228_);
v___x_4230_ = l_Std_Time_Weekday_ofOrdinal(v___x_4229_);
lean_dec(v___x_4229_);
v___x_4231_ = lean_box(v___x_4230_);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 1, v___x_4231_);
v___x_4233_ = v___x_4202_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_pos_4199_);
lean_ctor_set(v_reuseFailAlloc_4234_, 1, v___x_4231_);
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
}
else
{
lean_object* v_pos_4237_; lean_object* v_err_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_dec_ref(v_config_3888_);
v_pos_4237_ = lean_ctor_get(v___x_4198_, 0);
v_err_4238_ = lean_ctor_get(v___x_4198_, 1);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4198_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_err_4238_);
lean_inc(v_pos_4237_);
lean_dec(v___x_4198_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_pos_4237_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v_err_4238_);
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
else
{
lean_object* v_val_4246_; uint8_t v___x_4247_; 
v_val_4246_ = lean_ctor_get(v_presentation_4196_, 0);
lean_inc(v_val_4246_);
lean_dec_ref_known(v_presentation_4196_, 1);
v___x_4247_ = lean_unbox(v_val_4246_);
lean_dec(v_val_4246_);
switch(v___x_4247_)
{
case 0:
{
lean_object* v_dateformat_4248_; lean_object* v_symbols_4249_; lean_object* v___x_4250_; 
v_dateformat_4248_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4248_);
lean_dec_ref(v_config_3888_);
v_symbols_4249_ = lean_ctor_get(v_dateformat_4248_, 1);
lean_inc_ref(v_symbols_4249_);
lean_dec_ref(v_dateformat_4248_);
v___x_4250_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4249_, v_a_3890_);
return v___x_4250_;
}
case 1:
{
lean_object* v_dateformat_4251_; lean_object* v_symbols_4252_; lean_object* v___x_4253_; 
v_dateformat_4251_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4251_);
lean_dec_ref(v_config_3888_);
v_symbols_4252_ = lean_ctor_get(v_dateformat_4251_, 1);
lean_inc_ref(v_symbols_4252_);
lean_dec_ref(v_dateformat_4251_);
v___x_4253_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4252_, v_a_3890_);
return v___x_4253_;
}
case 2:
{
lean_object* v_dateformat_4254_; lean_object* v_symbols_4255_; lean_object* v___x_4256_; 
v_dateformat_4254_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4254_);
lean_dec_ref(v_config_3888_);
v_symbols_4255_ = lean_ctor_get(v_dateformat_4254_, 1);
lean_inc_ref(v_symbols_4255_);
lean_dec_ref(v_dateformat_4254_);
v___x_4256_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4255_, v_a_3890_);
return v___x_4256_;
}
default: 
{
lean_object* v_dateformat_4257_; lean_object* v_symbols_4258_; lean_object* v___x_4259_; 
v_dateformat_4257_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4257_);
lean_dec_ref(v_config_3888_);
v_symbols_4258_ = lean_ctor_get(v_dateformat_4257_, 1);
lean_inc_ref(v_symbols_4258_);
lean_dec_ref(v_dateformat_4257_);
v___x_4259_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4258_, v_a_3890_);
return v___x_4259_;
}
}
}
}
case 14:
{
lean_object* v_presentation_4260_; 
v_presentation_4260_ = lean_ctor_get(v_x_3889_, 0);
lean_inc_ref(v_presentation_4260_);
lean_dec_ref_known(v_x_3889_, 1);
if (lean_obj_tag(v_presentation_4260_) == 0)
{
lean_object* v_val_4261_; lean_object* v___x_4262_; 
v_val_4261_ = lean_ctor_get(v_presentation_4260_, 0);
lean_inc(v_val_4261_);
lean_dec_ref_known(v_presentation_4260_, 1);
v___x_4262_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4261_, v_a_3890_);
lean_dec(v_val_4261_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_pos_4263_; lean_object* v_res_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4300_; 
v_pos_4263_ = lean_ctor_get(v___x_4262_, 0);
v_res_4264_ = lean_ctor_get(v___x_4262_, 1);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4266_ = v___x_4262_;
v_isShared_4267_ = v_isSharedCheck_4300_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_res_4264_);
lean_inc(v_pos_4263_);
lean_dec(v___x_4262_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4300_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; uint8_t v___x_4269_; lean_object* v___x_4270_; uint8_t v___y_4272_; 
v___x_4268_ = lean_unsigned_to_nat(1u);
v___x_4269_ = lean_nat_dec_le(v___x_4268_, v_res_4264_);
v___x_4270_ = lean_unsigned_to_nat(7u);
if (v___x_4269_ == 0)
{
v___y_4272_ = v___x_4269_;
goto v___jp_4271_;
}
else
{
uint8_t v___x_4299_; 
v___x_4299_ = lean_nat_dec_le(v_res_4264_, v___x_4270_);
v___y_4272_ = v___x_4299_;
goto v___jp_4271_;
}
v___jp_4271_:
{
if (v___y_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4275_; 
lean_dec(v_res_4264_);
lean_dec_ref(v_config_3888_);
v___x_4273_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4267_ == 0)
{
lean_ctor_set_tag(v___x_4266_, 1);
lean_ctor_set(v___x_4266_, 1, v___x_4273_);
v___x_4275_ = v___x_4266_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_pos_4263_);
lean_ctor_set(v_reuseFailAlloc_4276_, 1, v___x_4273_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
else
{
lean_object* v_dateformat_4277_; uint8_t v_firstDayOfWeek_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v_range_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; uint8_t v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4297_; 
v_dateformat_4277_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4277_);
lean_dec_ref(v_config_3888_);
v_firstDayOfWeek_4278_ = lean_ctor_get_uint8(v_dateformat_4277_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4277_);
v___x_4279_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4278_);
v___x_4280_ = lean_nat_to_int(v_res_4264_);
v___x_4281_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4282_ = lean_int_sub(v___x_4280_, v___x_4281_);
lean_dec(v___x_4280_);
v___x_4283_ = lean_int_add(v___x_4282_, v___x_4279_);
lean_dec(v___x_4279_);
lean_dec(v___x_4282_);
v___x_4284_ = lean_int_sub(v___x_4283_, v___x_4281_);
lean_dec(v___x_4283_);
v___x_4285_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4286_ = lean_int_emod(v___x_4284_, v___x_4285_);
lean_dec(v___x_4284_);
v___x_4287_ = lean_int_add(v___x_4286_, v___x_4281_);
lean_dec(v___x_4286_);
v_range_4288_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4289_ = lean_int_sub(v___x_4287_, v___x_4281_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_int_emod(v___x_4289_, v_range_4288_);
lean_dec(v___x_4289_);
v___x_4291_ = lean_int_add(v___x_4290_, v_range_4288_);
lean_dec(v___x_4290_);
v___x_4292_ = lean_int_emod(v___x_4291_, v_range_4288_);
lean_dec(v___x_4291_);
v___x_4293_ = lean_int_add(v___x_4292_, v___x_4281_);
lean_dec(v___x_4292_);
v___x_4294_ = l_Std_Time_Weekday_ofOrdinal(v___x_4293_);
lean_dec(v___x_4293_);
v___x_4295_ = lean_box(v___x_4294_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 1, v___x_4295_);
v___x_4297_ = v___x_4266_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_pos_4263_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
else
{
lean_object* v_pos_4301_; lean_object* v_err_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_dec_ref(v_config_3888_);
v_pos_4301_ = lean_ctor_get(v___x_4262_, 0);
v_err_4302_ = lean_ctor_get(v___x_4262_, 1);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4262_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_err_4302_);
lean_inc(v_pos_4301_);
lean_dec(v___x_4262_);
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
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_pos_4301_);
lean_ctor_set(v_reuseFailAlloc_4308_, 1, v_err_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
else
{
lean_object* v_val_4310_; uint8_t v___x_4311_; 
v_val_4310_ = lean_ctor_get(v_presentation_4260_, 0);
lean_inc(v_val_4310_);
lean_dec_ref_known(v_presentation_4260_, 1);
v___x_4311_ = lean_unbox(v_val_4310_);
lean_dec(v_val_4310_);
switch(v___x_4311_)
{
case 0:
{
lean_object* v_dateformat_4312_; lean_object* v_symbols_4313_; lean_object* v___x_4314_; 
v_dateformat_4312_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4312_);
lean_dec_ref(v_config_3888_);
v_symbols_4313_ = lean_ctor_get(v_dateformat_4312_, 1);
lean_inc_ref(v_symbols_4313_);
lean_dec_ref(v_dateformat_4312_);
v___x_4314_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4313_, v_a_3890_);
return v___x_4314_;
}
case 1:
{
lean_object* v_dateformat_4315_; lean_object* v_symbols_4316_; lean_object* v___x_4317_; 
v_dateformat_4315_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4315_);
lean_dec_ref(v_config_3888_);
v_symbols_4316_ = lean_ctor_get(v_dateformat_4315_, 1);
lean_inc_ref(v_symbols_4316_);
lean_dec_ref(v_dateformat_4315_);
v___x_4317_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4316_, v_a_3890_);
return v___x_4317_;
}
case 2:
{
lean_object* v_dateformat_4318_; lean_object* v_symbols_4319_; lean_object* v___x_4320_; 
v_dateformat_4318_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4318_);
lean_dec_ref(v_config_3888_);
v_symbols_4319_ = lean_ctor_get(v_dateformat_4318_, 1);
lean_inc_ref(v_symbols_4319_);
lean_dec_ref(v_dateformat_4318_);
v___x_4320_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4319_, v_a_3890_);
return v___x_4320_;
}
default: 
{
lean_object* v_dateformat_4321_; lean_object* v_symbols_4322_; lean_object* v___x_4323_; 
v_dateformat_4321_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4321_);
lean_dec_ref(v_config_3888_);
v_symbols_4322_ = lean_ctor_get(v_dateformat_4321_, 1);
lean_inc_ref(v_symbols_4322_);
lean_dec_ref(v_dateformat_4321_);
v___x_4323_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4322_, v_a_3890_);
return v___x_4323_;
}
}
}
}
case 15:
{
lean_object* v_presentation_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
lean_dec_ref(v_config_3888_);
v_presentation_4324_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4324_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4325_ = lean_unsigned_to_nat(1u);
v___x_4326_ = lean_unsigned_to_nat(5u);
v___x_4327_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4327_, 0, v_presentation_4324_);
v___x_4328_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4325_, v___x_4326_, v___x_4327_, v_a_3890_);
return v___x_4328_;
}
case 16:
{
uint8_t v_presentation_4329_; 
v_presentation_4329_ = lean_ctor_get_uint8(v_x_3889_, 0);
lean_dec_ref_known(v_x_3889_, 0);
switch(v_presentation_4329_)
{
case 1:
{
lean_object* v_dateformat_4330_; lean_object* v_symbols_4331_; lean_object* v___x_4332_; 
v_dateformat_4330_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4330_);
lean_dec_ref(v_config_3888_);
v_symbols_4331_ = lean_ctor_get(v_dateformat_4330_, 1);
lean_inc_ref(v_symbols_4331_);
lean_dec_ref(v_dateformat_4330_);
v___x_4332_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(v_symbols_4331_, v_a_3890_);
return v___x_4332_;
}
case 2:
{
lean_object* v_dateformat_4333_; lean_object* v_symbols_4334_; lean_object* v___x_4335_; 
v_dateformat_4333_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4333_);
lean_dec_ref(v_config_3888_);
v_symbols_4334_ = lean_ctor_get(v_dateformat_4333_, 1);
lean_inc_ref(v_symbols_4334_);
lean_dec_ref(v_dateformat_4333_);
v___x_4335_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(v_symbols_4334_, v_a_3890_);
return v___x_4335_;
}
default: 
{
lean_object* v_dateformat_4336_; lean_object* v_symbols_4337_; lean_object* v___x_4338_; 
v_dateformat_4336_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4336_);
lean_dec_ref(v_config_3888_);
v_symbols_4337_ = lean_ctor_get(v_dateformat_4336_, 1);
lean_inc_ref(v_symbols_4337_);
lean_dec_ref(v_dateformat_4336_);
v___x_4338_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(v_symbols_4337_, v_a_3890_);
return v___x_4338_;
}
}
}
case 17:
{
uint8_t v_presentation_4339_; 
v_presentation_4339_ = lean_ctor_get_uint8(v_x_3889_, 0);
lean_dec_ref_known(v_x_3889_, 0);
switch(v_presentation_4339_)
{
case 1:
{
lean_object* v_dateformat_4340_; lean_object* v_symbols_4341_; lean_object* v_dayPeriodLong_4342_; lean_object* v___x_4343_; 
v_dateformat_4340_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4340_);
lean_dec_ref(v_config_3888_);
v_symbols_4341_ = lean_ctor_get(v_dateformat_4340_, 1);
lean_inc_ref(v_symbols_4341_);
lean_dec_ref(v_dateformat_4340_);
v_dayPeriodLong_4342_ = lean_ctor_get(v_symbols_4341_, 20);
lean_inc_ref(v_dayPeriodLong_4342_);
lean_dec_ref(v_symbols_4341_);
v___x_4343_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodLong_4342_, v_a_3890_);
return v___x_4343_;
}
case 2:
{
lean_object* v_dateformat_4344_; lean_object* v_symbols_4345_; lean_object* v_dayPeriodNarrow_4346_; lean_object* v___x_4347_; 
v_dateformat_4344_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4344_);
lean_dec_ref(v_config_3888_);
v_symbols_4345_ = lean_ctor_get(v_dateformat_4344_, 1);
lean_inc_ref(v_symbols_4345_);
lean_dec_ref(v_dateformat_4344_);
v_dayPeriodNarrow_4346_ = lean_ctor_get(v_symbols_4345_, 21);
lean_inc_ref(v_dayPeriodNarrow_4346_);
lean_dec_ref(v_symbols_4345_);
v___x_4347_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodNarrow_4346_, v_a_3890_);
return v___x_4347_;
}
default: 
{
lean_object* v_dateformat_4348_; lean_object* v_symbols_4349_; lean_object* v_dayPeriodShort_4350_; lean_object* v___x_4351_; 
v_dateformat_4348_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4348_);
lean_dec_ref(v_config_3888_);
v_symbols_4349_ = lean_ctor_get(v_dateformat_4348_, 1);
lean_inc_ref(v_symbols_4349_);
lean_dec_ref(v_dateformat_4348_);
v_dayPeriodShort_4350_ = lean_ctor_get(v_symbols_4349_, 19);
lean_inc_ref(v_dayPeriodShort_4350_);
lean_dec_ref(v_symbols_4349_);
v___x_4351_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodShort_4350_, v_a_3890_);
return v___x_4351_;
}
}
}
case 18:
{
uint8_t v_presentation_4352_; 
v_presentation_4352_ = lean_ctor_get_uint8(v_x_3889_, 0);
lean_dec_ref_known(v_x_3889_, 0);
switch(v_presentation_4352_)
{
case 1:
{
lean_object* v_dateformat_4353_; lean_object* v_symbols_4354_; lean_object* v_extendedDayPeriodLong_4355_; lean_object* v___x_4356_; 
v_dateformat_4353_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4353_);
lean_dec_ref(v_config_3888_);
v_symbols_4354_ = lean_ctor_get(v_dateformat_4353_, 1);
lean_inc_ref(v_symbols_4354_);
lean_dec_ref(v_dateformat_4353_);
v_extendedDayPeriodLong_4355_ = lean_ctor_get(v_symbols_4354_, 23);
lean_inc_ref(v_extendedDayPeriodLong_4355_);
lean_dec_ref(v_symbols_4354_);
v___x_4356_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodLong_4355_, v_a_3890_);
lean_dec_ref(v_extendedDayPeriodLong_4355_);
return v___x_4356_;
}
case 2:
{
lean_object* v_dateformat_4357_; lean_object* v_symbols_4358_; lean_object* v_extendedDayPeriodNarrow_4359_; lean_object* v___x_4360_; 
v_dateformat_4357_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4357_);
lean_dec_ref(v_config_3888_);
v_symbols_4358_ = lean_ctor_get(v_dateformat_4357_, 1);
lean_inc_ref(v_symbols_4358_);
lean_dec_ref(v_dateformat_4357_);
v_extendedDayPeriodNarrow_4359_ = lean_ctor_get(v_symbols_4358_, 24);
lean_inc_ref(v_extendedDayPeriodNarrow_4359_);
lean_dec_ref(v_symbols_4358_);
v___x_4360_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodNarrow_4359_, v_a_3890_);
lean_dec_ref(v_extendedDayPeriodNarrow_4359_);
return v___x_4360_;
}
default: 
{
lean_object* v_dateformat_4361_; lean_object* v_symbols_4362_; lean_object* v_extendedDayPeriodShort_4363_; lean_object* v___x_4364_; 
v_dateformat_4361_ = lean_ctor_get(v_config_3888_, 0);
lean_inc_ref(v_dateformat_4361_);
lean_dec_ref(v_config_3888_);
v_symbols_4362_ = lean_ctor_get(v_dateformat_4361_, 1);
lean_inc_ref(v_symbols_4362_);
lean_dec_ref(v_dateformat_4361_);
v_extendedDayPeriodShort_4363_ = lean_ctor_get(v_symbols_4362_, 22);
lean_inc_ref(v_extendedDayPeriodShort_4363_);
lean_dec_ref(v_symbols_4362_);
v___x_4364_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodShort_4363_, v_a_3890_);
lean_dec_ref(v_extendedDayPeriodShort_4363_);
return v___x_4364_;
}
}
}
case 19:
{
lean_object* v_presentation_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
lean_dec_ref(v_config_3888_);
v_presentation_4365_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4365_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4366_ = lean_unsigned_to_nat(1u);
v___x_4367_ = lean_unsigned_to_nat(12u);
v___x_4368_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4368_, 0, v_presentation_4365_);
v___x_4369_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4366_, v___x_4367_, v___x_4368_, v_a_3890_);
return v___x_4369_;
}
case 20:
{
lean_object* v_presentation_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
lean_dec_ref(v_config_3888_);
v_presentation_4370_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4370_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4371_ = lean_unsigned_to_nat(0u);
v___x_4372_ = lean_unsigned_to_nat(11u);
v___x_4373_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4373_, 0, v_presentation_4370_);
v___x_4374_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4371_, v___x_4372_, v___x_4373_, v_a_3890_);
return v___x_4374_;
}
case 21:
{
lean_object* v_presentation_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
lean_dec_ref(v_config_3888_);
v_presentation_4375_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4375_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4376_ = lean_unsigned_to_nat(1u);
v___x_4377_ = lean_unsigned_to_nat(24u);
v___x_4378_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4378_, 0, v_presentation_4375_);
v___x_4379_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4376_, v___x_4377_, v___x_4378_, v_a_3890_);
return v___x_4379_;
}
case 22:
{
lean_object* v_presentation_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
lean_dec_ref(v_config_3888_);
v_presentation_4380_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4380_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4381_ = lean_unsigned_to_nat(0u);
v___x_4382_ = lean_unsigned_to_nat(23u);
v___x_4383_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4383_, 0, v_presentation_4380_);
v___x_4384_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4381_, v___x_4382_, v___x_4383_, v_a_3890_);
return v___x_4384_;
}
case 23:
{
lean_object* v_presentation_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
lean_dec_ref(v_config_3888_);
v_presentation_4385_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4385_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4386_ = lean_unsigned_to_nat(0u);
v___x_4387_ = lean_unsigned_to_nat(59u);
v___x_4388_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4388_, 0, v_presentation_4385_);
v___x_4389_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4386_, v___x_4387_, v___x_4388_, v_a_3890_);
return v___x_4389_;
}
case 24:
{
uint8_t v_allowLeapSeconds_4390_; 
v_allowLeapSeconds_4390_ = lean_ctor_get_uint8(v_config_3888_, sizeof(void*)*1);
lean_dec_ref(v_config_3888_);
if (v_allowLeapSeconds_4390_ == 0)
{
lean_object* v_presentation_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v_presentation_4391_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4391_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4392_ = lean_unsigned_to_nat(0u);
v___x_4393_ = lean_unsigned_to_nat(59u);
v___x_4394_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4394_, 0, v_presentation_4391_);
v___x_4395_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4392_, v___x_4393_, v___x_4394_, v_a_3890_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_pos_4396_; lean_object* v_res_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
v_pos_4396_ = lean_ctor_get(v___x_4395_, 0);
v_res_4397_ = lean_ctor_get(v___x_4395_, 1);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4395_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_res_4397_);
lean_inc(v_pos_4396_);
lean_dec(v___x_4395_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_pos_4396_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_res_4397_);
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
return v___x_4395_;
}
}
else
{
lean_object* v_presentation_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_presentation_4405_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4405_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4406_ = lean_unsigned_to_nat(0u);
v___x_4407_ = lean_unsigned_to_nat(60u);
v___x_4408_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4408_, 0, v_presentation_4405_);
v___x_4409_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4406_, v___x_4407_, v___x_4408_, v_a_3890_);
return v___x_4409_;
}
}
case 25:
{
lean_object* v_presentation_4410_; 
lean_dec_ref(v_config_3888_);
v_presentation_4410_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4410_);
lean_dec_ref_known(v_x_3889_, 1);
if (lean_obj_tag(v_presentation_4410_) == 0)
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4411_ = lean_unsigned_to_nat(0u);
v___x_4412_ = lean_unsigned_to_nat(999999999u);
v___x_4413_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7));
v___x_4414_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4411_, v___x_4412_, v___x_4413_, v_a_3890_);
return v___x_4414_;
}
else
{
lean_object* v_digits_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v_digits_4415_ = lean_ctor_get(v_presentation_4410_, 0);
lean_inc(v_digits_4415_);
lean_dec_ref_known(v_presentation_4410_, 1);
v___x_4416_ = lean_unsigned_to_nat(0u);
v___x_4417_ = lean_unsigned_to_nat(999999999u);
v___x_4418_ = lean_unsigned_to_nat(9u);
v___x_4419_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed), 3, 2);
lean_closure_set(v___x_4419_, 0, v_digits_4415_);
lean_closure_set(v___x_4419_, 1, v___x_4418_);
v___x_4420_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4416_, v___x_4417_, v___x_4419_, v_a_3890_);
return v___x_4420_;
}
}
case 26:
{
lean_object* v_presentation_4421_; lean_object* v___x_4422_; 
lean_dec_ref(v_config_3888_);
v_presentation_4421_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4421_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4422_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4421_, v_a_3890_);
lean_dec(v_presentation_4421_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_pos_4423_; lean_object* v_res_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4432_; 
v_pos_4423_ = lean_ctor_get(v___x_4422_, 0);
v_res_4424_ = lean_ctor_get(v___x_4422_, 1);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4426_ = v___x_4422_;
v_isShared_4427_ = v_isSharedCheck_4432_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_res_4424_);
lean_inc(v_pos_4423_);
lean_dec(v___x_4422_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4432_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4428_; lean_object* v___x_4430_; 
v___x_4428_ = lean_nat_to_int(v_res_4424_);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 1, v___x_4428_);
v___x_4430_ = v___x_4426_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_pos_4423_);
lean_ctor_set(v_reuseFailAlloc_4431_, 1, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
else
{
lean_object* v_pos_4433_; lean_object* v_err_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
v_pos_4433_ = lean_ctor_get(v___x_4422_, 0);
v_err_4434_ = lean_ctor_get(v___x_4422_, 1);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4422_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_err_4434_);
lean_inc(v_pos_4433_);
lean_dec(v___x_4422_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_pos_4433_);
lean_ctor_set(v_reuseFailAlloc_4440_, 1, v_err_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
case 27:
{
lean_object* v_presentation_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
lean_dec_ref(v_config_3888_);
v_presentation_4442_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4442_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4443_ = lean_unsigned_to_nat(0u);
v___x_4444_ = lean_unsigned_to_nat(999999999u);
v___x_4445_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4445_, 0, v_presentation_4442_);
v___x_4446_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4443_, v___x_4444_, v___x_4445_, v_a_3890_);
return v___x_4446_;
}
case 28:
{
lean_object* v_presentation_4447_; lean_object* v___x_4448_; 
lean_dec_ref(v_config_3888_);
v_presentation_4447_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_presentation_4447_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_4448_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4447_, v_a_3890_);
lean_dec(v_presentation_4447_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v_pos_4449_; lean_object* v_res_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4458_; 
v_pos_4449_ = lean_ctor_get(v___x_4448_, 0);
v_res_4450_ = lean_ctor_get(v___x_4448_, 1);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4452_ = v___x_4448_;
v_isShared_4453_ = v_isSharedCheck_4458_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_res_4450_);
lean_inc(v_pos_4449_);
lean_dec(v___x_4448_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4458_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4454_; lean_object* v___x_4456_; 
v___x_4454_ = lean_nat_to_int(v_res_4450_);
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 1, v___x_4454_);
v___x_4456_ = v___x_4452_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_pos_4449_);
lean_ctor_set(v_reuseFailAlloc_4457_, 1, v___x_4454_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
else
{
lean_object* v_pos_4459_; lean_object* v_err_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
v_pos_4459_ = lean_ctor_get(v___x_4448_, 0);
v_err_4460_ = lean_ctor_get(v___x_4448_, 1);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4448_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_err_4460_);
lean_inc(v_pos_4459_);
lean_dec(v___x_4448_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_pos_4459_);
lean_ctor_set(v_reuseFailAlloc_4466_, 1, v_err_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
case 29:
{
uint8_t v_presentation_4468_; 
lean_dec_ref(v_config_3888_);
v_presentation_4468_ = lean_ctor_get_uint8(v_x_3889_, 0);
lean_dec_ref_known(v_x_3889_, 0);
if (v_presentation_4468_ == 0)
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
v___x_4470_ = l_Std_Internal_Parsec_String_pstring(v___x_4469_, v_a_3890_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_pos_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
v_pos_4471_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4478_ == 0)
{
lean_object* v_unused_4479_; 
v_unused_4479_ = lean_ctor_get(v___x_4470_, 1);
lean_dec(v_unused_4479_);
v___x_4473_ = v___x_4470_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_pos_4471_);
lean_dec(v___x_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 1, v___x_4469_);
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_pos_4471_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v___x_4469_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
else
{
return v___x_4470_;
}
}
else
{
lean_object* v___x_4480_; 
v___x_4480_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3890_);
return v___x_4480_;
}
}
case 32:
{
uint8_t v_presentation_4481_; 
lean_dec_ref(v_config_3888_);
v_presentation_4481_ = lean_ctor_get_uint8(v_x_3889_, 0);
lean_dec_ref_known(v_x_3889_, 0);
if (v_presentation_4481_ == 0)
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4483_ = l_Std_Internal_Parsec_String_pstring(v___x_4482_, v_a_3890_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_pos_4484_; uint8_t v___x_4485_; uint8_t v___x_4486_; uint8_t v___x_4487_; lean_object* v___x_4488_; 
v_pos_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_pos_4484_);
lean_dec_ref_known(v___x_4483_, 2);
v___x_4485_ = 2;
v___x_4486_ = 1;
v___x_4487_ = 1;
v___x_4488_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4485_, v___x_4486_, v___x_4487_, v_pos_4484_);
return v___x_4488_;
}
else
{
lean_object* v_pos_4489_; lean_object* v_err_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
v_pos_4489_ = lean_ctor_get(v___x_4483_, 0);
v_err_4490_ = lean_ctor_get(v___x_4483_, 1);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4483_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_err_4490_);
lean_inc(v_pos_4489_);
lean_dec(v___x_4483_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_pos_4489_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v_err_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
else
{
lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4498_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4499_ = l_Std_Internal_Parsec_String_pstring(v___x_4498_, v_a_3890_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_pos_4500_; uint8_t v___x_4501_; uint8_t v___x_4502_; uint8_t v___x_4503_; lean_object* v___x_4504_; 
v_pos_4500_ = lean_ctor_get(v___x_4499_, 0);
lean_inc(v_pos_4500_);
lean_dec_ref_known(v___x_4499_, 2);
v___x_4501_ = 0;
v___x_4502_ = 2;
v___x_4503_ = 1;
v___x_4504_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4501_, v___x_4502_, v___x_4503_, v_pos_4500_);
return v___x_4504_;
}
else
{
lean_object* v_pos_4505_; lean_object* v_err_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
v_pos_4505_ = lean_ctor_get(v___x_4499_, 0);
v_err_4506_ = lean_ctor_get(v___x_4499_, 1);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4499_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_err_4506_);
lean_inc(v_pos_4505_);
lean_dec(v___x_4499_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_pos_4505_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_err_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
}
case 33:
{
uint8_t v_presentation_4514_; 
lean_dec_ref(v_config_3888_);
v_presentation_4514_ = lean_ctor_get_uint8(v_x_3889_, 0);
lean_dec_ref_known(v_x_3889_, 0);
switch(v_presentation_4514_)
{
case 0:
{
uint8_t v___x_4515_; uint8_t v___x_4516_; uint8_t v___x_4517_; lean_object* v___x_4518_; 
v___x_4515_ = 2;
v___x_4516_ = 1;
v___x_4517_ = 0;
lean_inc_ref(v_a_3890_);
v___x_4518_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4515_, v___x_4516_, v___x_4517_, v_a_3890_);
v___y_3892_ = v___x_4518_;
goto v___jp_3891_;
}
case 1:
{
uint8_t v___x_4519_; uint8_t v___x_4520_; uint8_t v___x_4521_; lean_object* v___x_4522_; 
v___x_4519_ = 0;
v___x_4520_ = 1;
v___x_4521_ = 0;
lean_inc_ref(v_a_3890_);
v___x_4522_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4519_, v___x_4520_, v___x_4521_, v_a_3890_);
v___y_3892_ = v___x_4522_;
goto v___jp_3891_;
}
case 2:
{
uint8_t v___x_4523_; uint8_t v___x_4524_; uint8_t v___x_4525_; lean_object* v___x_4526_; 
v___x_4523_ = 0;
v___x_4524_ = 1;
v___x_4525_ = 1;
lean_inc_ref(v_a_3890_);
v___x_4526_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4523_, v___x_4524_, v___x_4525_, v_a_3890_);
v___y_3892_ = v___x_4526_;
goto v___jp_3891_;
}
case 3:
{
uint8_t v___x_4527_; uint8_t v___x_4528_; uint8_t v___x_4529_; lean_object* v___x_4530_; 
v___x_4527_ = 0;
v___x_4528_ = 2;
v___x_4529_ = 0;
lean_inc_ref(v_a_3890_);
v___x_4530_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4527_, v___x_4528_, v___x_4529_, v_a_3890_);
v___y_3892_ = v___x_4530_;
goto v___jp_3891_;
}
default: 
{
uint8_t v___x_4531_; uint8_t v___x_4532_; uint8_t v___x_4533_; lean_object* v___x_4534_; 
v___x_4531_ = 0;
v___x_4532_ = 2;
v___x_4533_ = 1;
lean_inc_ref(v_a_3890_);
v___x_4534_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4531_, v___x_4532_, v___x_4533_, v_a_3890_);
v___y_3892_ = v___x_4534_;
goto v___jp_3891_;
}
}
}
case 34:
{
uint8_t v_presentation_4535_; 
lean_dec_ref(v_config_3888_);
v_presentation_4535_ = lean_ctor_get_uint8(v_x_3889_, 0);
lean_dec_ref_known(v_x_3889_, 0);
switch(v_presentation_4535_)
{
case 0:
{
uint8_t v___x_4536_; uint8_t v___x_4537_; uint8_t v___x_4538_; lean_object* v___x_4539_; 
v___x_4536_ = 2;
v___x_4537_ = 1;
v___x_4538_ = 0;
v___x_4539_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4536_, v___x_4537_, v___x_4538_, v_a_3890_);
return v___x_4539_;
}
case 1:
{
uint8_t v___x_4540_; uint8_t v___x_4541_; uint8_t v___x_4542_; lean_object* v___x_4543_; 
v___x_4540_ = 0;
v___x_4541_ = 1;
v___x_4542_ = 0;
v___x_4543_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4540_, v___x_4541_, v___x_4542_, v_a_3890_);
return v___x_4543_;
}
case 2:
{
uint8_t v___x_4544_; uint8_t v___x_4545_; uint8_t v___x_4546_; lean_object* v___x_4547_; 
v___x_4544_ = 0;
v___x_4545_ = 2;
v___x_4546_ = 1;
v___x_4547_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4544_, v___x_4545_, v___x_4546_, v_a_3890_);
return v___x_4547_;
}
case 3:
{
uint8_t v___x_4548_; uint8_t v___x_4549_; uint8_t v___x_4550_; lean_object* v___x_4551_; 
v___x_4548_ = 0;
v___x_4549_ = 2;
v___x_4550_ = 0;
v___x_4551_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4548_, v___x_4549_, v___x_4550_, v_a_3890_);
return v___x_4551_;
}
default: 
{
uint8_t v___x_4552_; uint8_t v___x_4553_; lean_object* v___x_4554_; 
v___x_4552_ = 0;
v___x_4553_ = 1;
v___x_4554_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4552_, v___x_4552_, v___x_4553_, v_a_3890_);
return v___x_4554_;
}
}
}
case 35:
{
uint8_t v_presentation_4555_; 
lean_dec_ref(v_config_3888_);
v_presentation_4555_ = lean_ctor_get_uint8(v_x_3889_, 0);
lean_dec_ref_known(v_x_3889_, 0);
switch(v_presentation_4555_)
{
case 0:
{
uint8_t v___x_4556_; uint8_t v___x_4557_; uint8_t v___x_4558_; lean_object* v___x_4559_; 
v___x_4556_ = 0;
v___x_4557_ = 1;
v___x_4558_ = 0;
v___x_4559_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4556_, v___x_4557_, v___x_4558_, v_a_3890_);
return v___x_4559_;
}
case 1:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4560_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4561_ = l_Std_Internal_Parsec_String_pstring(v___x_4560_, v_a_3890_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_pos_4562_; uint8_t v___x_4563_; uint8_t v___x_4564_; uint8_t v___x_4565_; lean_object* v___x_4566_; 
v_pos_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc_n(v_pos_4562_, 2);
lean_dec_ref_known(v___x_4561_, 2);
v___x_4563_ = 0;
v___x_4564_ = 1;
v___x_4565_ = 1;
v___x_4566_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4563_, v___x_4564_, v___x_4565_, v_pos_4562_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_dec(v_pos_4562_);
return v___x_4566_;
}
else
{
lean_object* v_pos_4567_; lean_object* v_snd_4568_; lean_object* v_snd_4569_; uint8_t v_decide_4570_; 
v_pos_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_pos_4567_);
v_snd_4568_ = lean_ctor_get(v_pos_4562_, 1);
lean_inc(v_snd_4568_);
lean_dec(v_pos_4562_);
v_snd_4569_ = lean_ctor_get(v_pos_4567_, 1);
v_decide_4570_ = lean_nat_dec_eq(v_snd_4568_, v_snd_4569_);
lean_dec(v_snd_4568_);
if (v_decide_4570_ == 0)
{
lean_dec(v_pos_4567_);
return v___x_4566_;
}
else
{
lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4578_; 
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4578_ == 0)
{
lean_object* v_unused_4579_; lean_object* v_unused_4580_; 
v_unused_4579_ = lean_ctor_get(v___x_4566_, 1);
lean_dec(v_unused_4579_);
v_unused_4580_ = lean_ctor_get(v___x_4566_, 0);
lean_dec(v_unused_4580_);
v___x_4572_ = v___x_4566_;
v_isShared_4573_ = v_isSharedCheck_4578_;
goto v_resetjp_4571_;
}
else
{
lean_dec(v___x_4566_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4578_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4574_; lean_object* v___x_4576_; 
v___x_4574_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4573_ == 0)
{
lean_ctor_set_tag(v___x_4572_, 0);
lean_ctor_set(v___x_4572_, 1, v___x_4574_);
v___x_4576_ = v___x_4572_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_pos_4567_);
lean_ctor_set(v_reuseFailAlloc_4577_, 1, v___x_4574_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
}
else
{
lean_object* v_pos_4581_; lean_object* v_err_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4589_; 
v_pos_4581_ = lean_ctor_get(v___x_4561_, 0);
v_err_4582_ = lean_ctor_get(v___x_4561_, 1);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4584_ = v___x_4561_;
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_err_4582_);
lean_inc(v_pos_4581_);
lean_dec(v___x_4561_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
if (v_isShared_4585_ == 0)
{
v___x_4587_ = v___x_4584_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_pos_4581_);
lean_ctor_set(v_reuseFailAlloc_4588_, 1, v_err_4582_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
default: 
{
lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4590_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
lean_inc_ref(v_a_3890_);
v___x_4591_ = l_Std_Internal_Parsec_String_pstring(v___x_4590_, v_a_3890_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_pos_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4600_; 
lean_dec_ref(v_a_3890_);
v_pos_4592_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4600_ == 0)
{
lean_object* v_unused_4601_; 
v_unused_4601_ = lean_ctor_get(v___x_4591_, 1);
lean_dec(v_unused_4601_);
v___x_4594_ = v___x_4591_;
v_isShared_4595_ = v_isSharedCheck_4600_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_pos_4592_);
lean_dec(v___x_4591_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4600_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4596_; lean_object* v___x_4598_; 
v___x_4596_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 1, v___x_4596_);
v___x_4598_ = v___x_4594_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_pos_4592_);
lean_ctor_set(v_reuseFailAlloc_4599_, 1, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
else
{
lean_object* v_pos_4602_; lean_object* v_err_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4616_; 
v_pos_4602_ = lean_ctor_get(v___x_4591_, 0);
v_err_4603_ = lean_ctor_get(v___x_4591_, 1);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4605_ = v___x_4591_;
v_isShared_4606_ = v_isSharedCheck_4616_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_err_4603_);
lean_inc(v_pos_4602_);
lean_dec(v___x_4591_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4616_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v_snd_4607_; lean_object* v_snd_4608_; uint8_t v_decide_4609_; 
v_snd_4607_ = lean_ctor_get(v_a_3890_, 1);
lean_inc(v_snd_4607_);
lean_dec_ref(v_a_3890_);
v_snd_4608_ = lean_ctor_get(v_pos_4602_, 1);
v_decide_4609_ = lean_nat_dec_eq(v_snd_4607_, v_snd_4608_);
lean_dec(v_snd_4607_);
if (v_decide_4609_ == 0)
{
lean_object* v___x_4611_; 
if (v_isShared_4606_ == 0)
{
v___x_4611_ = v___x_4605_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_pos_4602_);
lean_ctor_set(v_reuseFailAlloc_4612_, 1, v_err_4603_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
else
{
uint8_t v___x_4613_; uint8_t v___x_4614_; lean_object* v___x_4615_; 
lean_del_object(v___x_4605_);
lean_dec(v_err_4603_);
v___x_4613_ = 0;
v___x_4614_ = 2;
v___x_4615_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4613_, v___x_4614_, v_decide_4609_, v_pos_4602_);
return v___x_4615_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_4617_; 
lean_dec_ref(v_x_3889_);
lean_dec_ref(v_config_3888_);
v___x_4617_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3890_);
return v___x_4617_;
}
}
v___jp_3891_:
{
if (lean_obj_tag(v___y_3892_) == 0)
{
lean_dec_ref(v_a_3890_);
return v___y_3892_;
}
else
{
lean_object* v_pos_3893_; lean_object* v_snd_3894_; lean_object* v_snd_3895_; uint8_t v_decide_3896_; 
v_pos_3893_ = lean_ctor_get(v___y_3892_, 0);
v_snd_3894_ = lean_ctor_get(v_a_3890_, 1);
lean_inc(v_snd_3894_);
lean_dec_ref(v_a_3890_);
v_snd_3895_ = lean_ctor_get(v_pos_3893_, 1);
v_decide_3896_ = lean_nat_dec_eq(v_snd_3894_, v_snd_3895_);
lean_dec(v_snd_3894_);
if (v_decide_3896_ == 0)
{
return v___y_3892_;
}
else
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
lean_inc(v_pos_3893_);
lean_dec_ref_known(v___y_3892_, 2);
v___x_3897_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
v___x_3898_ = l_Std_Internal_Parsec_String_pstring(v___x_3897_, v_pos_3893_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_pos_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3907_; 
v_pos_3899_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; 
v_unused_3908_ = lean_ctor_get(v___x_3898_, 1);
lean_dec(v_unused_3908_);
v___x_3901_ = v___x_3898_;
v_isShared_3902_ = v_isSharedCheck_3907_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_pos_3899_);
lean_dec(v___x_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3907_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
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
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_pos_3899_);
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
lean_object* v_pos_3909_; lean_object* v_err_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
v_pos_3909_ = lean_ctor_get(v___x_3898_, 0);
v_err_3910_ = lean_ctor_get(v___x_3898_, 1);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3898_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_err_3910_);
lean_inc(v_pos_3909_);
lean_dec(v___x_3898_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_pos_3909_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v_err_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(lean_object* v_dateformat_4618_, lean_object* v_date_4619_, lean_object* v_part_4620_){
_start:
{
if (lean_obj_tag(v_part_4620_) == 0)
{
lean_object* v_val_4621_; 
lean_dec_ref(v_date_4619_);
v_val_4621_ = lean_ctor_get(v_part_4620_, 0);
lean_inc_ref(v_val_4621_);
lean_dec_ref_known(v_part_4620_, 1);
return v_val_4621_;
}
else
{
lean_object* v_modifier_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v_modifier_4622_ = lean_ctor_get(v_part_4620_, 0);
lean_inc_ref(v_modifier_4622_);
lean_dec_ref_known(v_part_4620_, 1);
v___x_4623_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_4622_, v_dateformat_4618_, v_date_4619_);
v___x_4624_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_4618_, v_modifier_4622_, v___x_4623_);
return v___x_4624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate___boxed(lean_object* v_dateformat_4625_, lean_object* v_date_4626_, lean_object* v_part_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_4625_, v_date_4626_, v_part_4627_);
lean_dec_ref(v_dateformat_4625_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter___redArg(lean_object* v_x_4629_, lean_object* v_h__1_4630_, lean_object* v_h__2_4631_, lean_object* v_h__3_4632_){
_start:
{
if (lean_obj_tag(v_x_4629_) == 0)
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
lean_dec(v_h__2_4631_);
lean_dec(v_h__1_4630_);
v___x_4633_ = lean_box(0);
v___x_4634_ = lean_apply_1(v_h__3_4632_, v___x_4633_);
return v___x_4634_;
}
else
{
lean_object* v_head_4635_; 
lean_dec(v_h__3_4632_);
v_head_4635_ = lean_ctor_get(v_x_4629_, 0);
lean_inc(v_head_4635_);
if (lean_obj_tag(v_head_4635_) == 0)
{
lean_object* v_tail_4636_; lean_object* v_val_4637_; lean_object* v___x_4638_; 
lean_dec(v_h__1_4630_);
v_tail_4636_ = lean_ctor_get(v_x_4629_, 1);
lean_inc(v_tail_4636_);
lean_dec_ref_known(v_x_4629_, 2);
v_val_4637_ = lean_ctor_get(v_head_4635_, 0);
lean_inc_ref(v_val_4637_);
lean_dec_ref_known(v_head_4635_, 1);
v___x_4638_ = lean_apply_2(v_h__2_4631_, v_val_4637_, v_tail_4636_);
return v___x_4638_;
}
else
{
lean_object* v_tail_4639_; lean_object* v_modifier_4640_; lean_object* v___x_4641_; 
lean_dec(v_h__2_4631_);
v_tail_4639_ = lean_ctor_get(v_x_4629_, 1);
lean_inc(v_tail_4639_);
lean_dec_ref_known(v_x_4629_, 2);
v_modifier_4640_ = lean_ctor_get(v_head_4635_, 0);
lean_inc_ref(v_modifier_4640_);
lean_dec_ref_known(v_head_4635_, 1);
v___x_4641_ = lean_apply_2(v_h__1_4630_, v_modifier_4640_, v_tail_4639_);
return v___x_4641_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter(lean_object* v_motive_4642_, lean_object* v_x_4643_, lean_object* v_h__1_4644_, lean_object* v_h__2_4645_, lean_object* v_h__3_4646_){
_start:
{
if (lean_obj_tag(v_x_4643_) == 0)
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
lean_dec(v_h__2_4645_);
lean_dec(v_h__1_4644_);
v___x_4647_ = lean_box(0);
v___x_4648_ = lean_apply_1(v_h__3_4646_, v___x_4647_);
return v___x_4648_;
}
else
{
lean_object* v_head_4649_; 
lean_dec(v_h__3_4646_);
v_head_4649_ = lean_ctor_get(v_x_4643_, 0);
lean_inc(v_head_4649_);
if (lean_obj_tag(v_head_4649_) == 0)
{
lean_object* v_tail_4650_; lean_object* v_val_4651_; lean_object* v___x_4652_; 
lean_dec(v_h__1_4644_);
v_tail_4650_ = lean_ctor_get(v_x_4643_, 1);
lean_inc(v_tail_4650_);
lean_dec_ref_known(v_x_4643_, 2);
v_val_4651_ = lean_ctor_get(v_head_4649_, 0);
lean_inc_ref(v_val_4651_);
lean_dec_ref_known(v_head_4649_, 1);
v___x_4652_ = lean_apply_2(v_h__2_4645_, v_val_4651_, v_tail_4650_);
return v___x_4652_;
}
else
{
lean_object* v_tail_4653_; lean_object* v_modifier_4654_; lean_object* v___x_4655_; 
lean_dec(v_h__2_4645_);
v_tail_4653_ = lean_ctor_get(v_x_4643_, 1);
lean_inc(v_tail_4653_);
lean_dec_ref_known(v_x_4643_, 2);
v_modifier_4654_ = lean_ctor_get(v_head_4649_, 0);
lean_inc_ref(v_modifier_4654_);
lean_dec_ref_known(v_head_4649_, 1);
v___x_4655_ = lean_apply_2(v_h__1_4644_, v_modifier_4654_, v_tail_4653_);
return v___x_4655_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object* v_date_4656_, lean_object* v_modifier_4657_, lean_object* v_data_4658_){
_start:
{
switch(lean_obj_tag(v_modifier_4657_))
{
case 0:
{
lean_object* v_y_4659_; lean_object* v_u_4660_; lean_object* v_Y_4661_; lean_object* v_D_4662_; lean_object* v_M_4663_; lean_object* v_L_4664_; lean_object* v_d_4665_; lean_object* v_Q_4666_; lean_object* v_q_4667_; lean_object* v_w_4668_; lean_object* v_W_4669_; lean_object* v_E_4670_; lean_object* v_e_4671_; lean_object* v_c_4672_; lean_object* v_F_4673_; lean_object* v_a_4674_; lean_object* v_b_4675_; lean_object* v_B_4676_; lean_object* v_h_4677_; lean_object* v_K_4678_; lean_object* v_k_4679_; lean_object* v_H_4680_; lean_object* v_m_4681_; lean_object* v_s_4682_; lean_object* v_S_4683_; lean_object* v_A_4684_; lean_object* v_n_4685_; lean_object* v_N_4686_; lean_object* v_V_4687_; lean_object* v_z_4688_; lean_object* v_zabbrev_4689_; lean_object* v_v_4690_; lean_object* v_O_4691_; lean_object* v_X_4692_; lean_object* v_x_4693_; lean_object* v_Z_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4702_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_y_4659_ = lean_ctor_get(v_date_4656_, 1);
v_u_4660_ = lean_ctor_get(v_date_4656_, 2);
v_Y_4661_ = lean_ctor_get(v_date_4656_, 3);
v_D_4662_ = lean_ctor_get(v_date_4656_, 4);
v_M_4663_ = lean_ctor_get(v_date_4656_, 5);
v_L_4664_ = lean_ctor_get(v_date_4656_, 6);
v_d_4665_ = lean_ctor_get(v_date_4656_, 7);
v_Q_4666_ = lean_ctor_get(v_date_4656_, 8);
v_q_4667_ = lean_ctor_get(v_date_4656_, 9);
v_w_4668_ = lean_ctor_get(v_date_4656_, 10);
v_W_4669_ = lean_ctor_get(v_date_4656_, 11);
v_E_4670_ = lean_ctor_get(v_date_4656_, 12);
v_e_4671_ = lean_ctor_get(v_date_4656_, 13);
v_c_4672_ = lean_ctor_get(v_date_4656_, 14);
v_F_4673_ = lean_ctor_get(v_date_4656_, 15);
v_a_4674_ = lean_ctor_get(v_date_4656_, 16);
v_b_4675_ = lean_ctor_get(v_date_4656_, 17);
v_B_4676_ = lean_ctor_get(v_date_4656_, 18);
v_h_4677_ = lean_ctor_get(v_date_4656_, 19);
v_K_4678_ = lean_ctor_get(v_date_4656_, 20);
v_k_4679_ = lean_ctor_get(v_date_4656_, 21);
v_H_4680_ = lean_ctor_get(v_date_4656_, 22);
v_m_4681_ = lean_ctor_get(v_date_4656_, 23);
v_s_4682_ = lean_ctor_get(v_date_4656_, 24);
v_S_4683_ = lean_ctor_get(v_date_4656_, 25);
v_A_4684_ = lean_ctor_get(v_date_4656_, 26);
v_n_4685_ = lean_ctor_get(v_date_4656_, 27);
v_N_4686_ = lean_ctor_get(v_date_4656_, 28);
v_V_4687_ = lean_ctor_get(v_date_4656_, 29);
v_z_4688_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_4689_ = lean_ctor_get(v_date_4656_, 31);
v_v_4690_ = lean_ctor_get(v_date_4656_, 32);
v_O_4691_ = lean_ctor_get(v_date_4656_, 33);
v_X_4692_ = lean_ctor_get(v_date_4656_, 34);
v_x_4693_ = lean_ctor_get(v_date_4656_, 35);
v_Z_4694_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_4702_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_4702_ == 0)
{
lean_object* v_unused_4703_; 
v_unused_4703_ = lean_ctor_get(v_date_4656_, 0);
lean_dec(v_unused_4703_);
v___x_4696_ = v_date_4656_;
v_isShared_4697_ = v_isSharedCheck_4702_;
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
lean_inc(v_y_4659_);
lean_dec(v_date_4656_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4702_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4698_; lean_object* v___x_4700_; 
v___x_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4698_, 0, v_data_4658_);
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 0, v___x_4698_);
v___x_4700_ = v___x_4696_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4701_, 1, v_y_4659_);
lean_ctor_set(v_reuseFailAlloc_4701_, 2, v_u_4660_);
lean_ctor_set(v_reuseFailAlloc_4701_, 3, v_Y_4661_);
lean_ctor_set(v_reuseFailAlloc_4701_, 4, v_D_4662_);
lean_ctor_set(v_reuseFailAlloc_4701_, 5, v_M_4663_);
lean_ctor_set(v_reuseFailAlloc_4701_, 6, v_L_4664_);
lean_ctor_set(v_reuseFailAlloc_4701_, 7, v_d_4665_);
lean_ctor_set(v_reuseFailAlloc_4701_, 8, v_Q_4666_);
lean_ctor_set(v_reuseFailAlloc_4701_, 9, v_q_4667_);
lean_ctor_set(v_reuseFailAlloc_4701_, 10, v_w_4668_);
lean_ctor_set(v_reuseFailAlloc_4701_, 11, v_W_4669_);
lean_ctor_set(v_reuseFailAlloc_4701_, 12, v_E_4670_);
lean_ctor_set(v_reuseFailAlloc_4701_, 13, v_e_4671_);
lean_ctor_set(v_reuseFailAlloc_4701_, 14, v_c_4672_);
lean_ctor_set(v_reuseFailAlloc_4701_, 15, v_F_4673_);
lean_ctor_set(v_reuseFailAlloc_4701_, 16, v_a_4674_);
lean_ctor_set(v_reuseFailAlloc_4701_, 17, v_b_4675_);
lean_ctor_set(v_reuseFailAlloc_4701_, 18, v_B_4676_);
lean_ctor_set(v_reuseFailAlloc_4701_, 19, v_h_4677_);
lean_ctor_set(v_reuseFailAlloc_4701_, 20, v_K_4678_);
lean_ctor_set(v_reuseFailAlloc_4701_, 21, v_k_4679_);
lean_ctor_set(v_reuseFailAlloc_4701_, 22, v_H_4680_);
lean_ctor_set(v_reuseFailAlloc_4701_, 23, v_m_4681_);
lean_ctor_set(v_reuseFailAlloc_4701_, 24, v_s_4682_);
lean_ctor_set(v_reuseFailAlloc_4701_, 25, v_S_4683_);
lean_ctor_set(v_reuseFailAlloc_4701_, 26, v_A_4684_);
lean_ctor_set(v_reuseFailAlloc_4701_, 27, v_n_4685_);
lean_ctor_set(v_reuseFailAlloc_4701_, 28, v_N_4686_);
lean_ctor_set(v_reuseFailAlloc_4701_, 29, v_V_4687_);
lean_ctor_set(v_reuseFailAlloc_4701_, 30, v_z_4688_);
lean_ctor_set(v_reuseFailAlloc_4701_, 31, v_zabbrev_4689_);
lean_ctor_set(v_reuseFailAlloc_4701_, 32, v_v_4690_);
lean_ctor_set(v_reuseFailAlloc_4701_, 33, v_O_4691_);
lean_ctor_set(v_reuseFailAlloc_4701_, 34, v_X_4692_);
lean_ctor_set(v_reuseFailAlloc_4701_, 35, v_x_4693_);
lean_ctor_set(v_reuseFailAlloc_4701_, 36, v_Z_4694_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
case 1:
{
lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4754_; 
v_isSharedCheck_4754_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_4754_ == 0)
{
lean_object* v_unused_4755_; 
v_unused_4755_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_4755_);
v___x_4705_ = v_modifier_4657_;
v_isShared_4706_ = v_isSharedCheck_4754_;
goto v_resetjp_4704_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4754_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v_G_4707_; lean_object* v_y_4708_; lean_object* v_Y_4709_; lean_object* v_D_4710_; lean_object* v_M_4711_; lean_object* v_L_4712_; lean_object* v_d_4713_; lean_object* v_Q_4714_; lean_object* v_q_4715_; lean_object* v_w_4716_; lean_object* v_W_4717_; lean_object* v_E_4718_; lean_object* v_e_4719_; lean_object* v_c_4720_; lean_object* v_F_4721_; lean_object* v_a_4722_; lean_object* v_b_4723_; lean_object* v_B_4724_; lean_object* v_h_4725_; lean_object* v_K_4726_; lean_object* v_k_4727_; lean_object* v_H_4728_; lean_object* v_m_4729_; lean_object* v_s_4730_; lean_object* v_S_4731_; lean_object* v_A_4732_; lean_object* v_n_4733_; lean_object* v_N_4734_; lean_object* v_V_4735_; lean_object* v_z_4736_; lean_object* v_zabbrev_4737_; lean_object* v_v_4738_; lean_object* v_O_4739_; lean_object* v_X_4740_; lean_object* v_x_4741_; lean_object* v_Z_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4752_; 
v_G_4707_ = lean_ctor_get(v_date_4656_, 0);
v_y_4708_ = lean_ctor_get(v_date_4656_, 1);
v_Y_4709_ = lean_ctor_get(v_date_4656_, 3);
v_D_4710_ = lean_ctor_get(v_date_4656_, 4);
v_M_4711_ = lean_ctor_get(v_date_4656_, 5);
v_L_4712_ = lean_ctor_get(v_date_4656_, 6);
v_d_4713_ = lean_ctor_get(v_date_4656_, 7);
v_Q_4714_ = lean_ctor_get(v_date_4656_, 8);
v_q_4715_ = lean_ctor_get(v_date_4656_, 9);
v_w_4716_ = lean_ctor_get(v_date_4656_, 10);
v_W_4717_ = lean_ctor_get(v_date_4656_, 11);
v_E_4718_ = lean_ctor_get(v_date_4656_, 12);
v_e_4719_ = lean_ctor_get(v_date_4656_, 13);
v_c_4720_ = lean_ctor_get(v_date_4656_, 14);
v_F_4721_ = lean_ctor_get(v_date_4656_, 15);
v_a_4722_ = lean_ctor_get(v_date_4656_, 16);
v_b_4723_ = lean_ctor_get(v_date_4656_, 17);
v_B_4724_ = lean_ctor_get(v_date_4656_, 18);
v_h_4725_ = lean_ctor_get(v_date_4656_, 19);
v_K_4726_ = lean_ctor_get(v_date_4656_, 20);
v_k_4727_ = lean_ctor_get(v_date_4656_, 21);
v_H_4728_ = lean_ctor_get(v_date_4656_, 22);
v_m_4729_ = lean_ctor_get(v_date_4656_, 23);
v_s_4730_ = lean_ctor_get(v_date_4656_, 24);
v_S_4731_ = lean_ctor_get(v_date_4656_, 25);
v_A_4732_ = lean_ctor_get(v_date_4656_, 26);
v_n_4733_ = lean_ctor_get(v_date_4656_, 27);
v_N_4734_ = lean_ctor_get(v_date_4656_, 28);
v_V_4735_ = lean_ctor_get(v_date_4656_, 29);
v_z_4736_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_4737_ = lean_ctor_get(v_date_4656_, 31);
v_v_4738_ = lean_ctor_get(v_date_4656_, 32);
v_O_4739_ = lean_ctor_get(v_date_4656_, 33);
v_X_4740_ = lean_ctor_get(v_date_4656_, 34);
v_x_4741_ = lean_ctor_get(v_date_4656_, 35);
v_Z_4742_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_4752_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_4752_ == 0)
{
lean_object* v_unused_4753_; 
v_unused_4753_ = lean_ctor_get(v_date_4656_, 2);
lean_dec(v_unused_4753_);
v___x_4744_ = v_date_4656_;
v_isShared_4745_ = v_isSharedCheck_4752_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_Z_4742_);
lean_inc(v_x_4741_);
lean_inc(v_X_4740_);
lean_inc(v_O_4739_);
lean_inc(v_v_4738_);
lean_inc(v_zabbrev_4737_);
lean_inc(v_z_4736_);
lean_inc(v_V_4735_);
lean_inc(v_N_4734_);
lean_inc(v_n_4733_);
lean_inc(v_A_4732_);
lean_inc(v_S_4731_);
lean_inc(v_s_4730_);
lean_inc(v_m_4729_);
lean_inc(v_H_4728_);
lean_inc(v_k_4727_);
lean_inc(v_K_4726_);
lean_inc(v_h_4725_);
lean_inc(v_B_4724_);
lean_inc(v_b_4723_);
lean_inc(v_a_4722_);
lean_inc(v_F_4721_);
lean_inc(v_c_4720_);
lean_inc(v_e_4719_);
lean_inc(v_E_4718_);
lean_inc(v_W_4717_);
lean_inc(v_w_4716_);
lean_inc(v_q_4715_);
lean_inc(v_Q_4714_);
lean_inc(v_d_4713_);
lean_inc(v_L_4712_);
lean_inc(v_M_4711_);
lean_inc(v_D_4710_);
lean_inc(v_Y_4709_);
lean_inc(v_y_4708_);
lean_inc(v_G_4707_);
lean_dec(v_date_4656_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4752_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 0, v_data_4658_);
v___x_4747_ = v___x_4705_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_data_4658_);
v___x_4747_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_object* v___x_4749_; 
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 2, v___x_4747_);
v___x_4749_ = v___x_4744_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_G_4707_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_y_4708_);
lean_ctor_set(v_reuseFailAlloc_4750_, 2, v___x_4747_);
lean_ctor_set(v_reuseFailAlloc_4750_, 3, v_Y_4709_);
lean_ctor_set(v_reuseFailAlloc_4750_, 4, v_D_4710_);
lean_ctor_set(v_reuseFailAlloc_4750_, 5, v_M_4711_);
lean_ctor_set(v_reuseFailAlloc_4750_, 6, v_L_4712_);
lean_ctor_set(v_reuseFailAlloc_4750_, 7, v_d_4713_);
lean_ctor_set(v_reuseFailAlloc_4750_, 8, v_Q_4714_);
lean_ctor_set(v_reuseFailAlloc_4750_, 9, v_q_4715_);
lean_ctor_set(v_reuseFailAlloc_4750_, 10, v_w_4716_);
lean_ctor_set(v_reuseFailAlloc_4750_, 11, v_W_4717_);
lean_ctor_set(v_reuseFailAlloc_4750_, 12, v_E_4718_);
lean_ctor_set(v_reuseFailAlloc_4750_, 13, v_e_4719_);
lean_ctor_set(v_reuseFailAlloc_4750_, 14, v_c_4720_);
lean_ctor_set(v_reuseFailAlloc_4750_, 15, v_F_4721_);
lean_ctor_set(v_reuseFailAlloc_4750_, 16, v_a_4722_);
lean_ctor_set(v_reuseFailAlloc_4750_, 17, v_b_4723_);
lean_ctor_set(v_reuseFailAlloc_4750_, 18, v_B_4724_);
lean_ctor_set(v_reuseFailAlloc_4750_, 19, v_h_4725_);
lean_ctor_set(v_reuseFailAlloc_4750_, 20, v_K_4726_);
lean_ctor_set(v_reuseFailAlloc_4750_, 21, v_k_4727_);
lean_ctor_set(v_reuseFailAlloc_4750_, 22, v_H_4728_);
lean_ctor_set(v_reuseFailAlloc_4750_, 23, v_m_4729_);
lean_ctor_set(v_reuseFailAlloc_4750_, 24, v_s_4730_);
lean_ctor_set(v_reuseFailAlloc_4750_, 25, v_S_4731_);
lean_ctor_set(v_reuseFailAlloc_4750_, 26, v_A_4732_);
lean_ctor_set(v_reuseFailAlloc_4750_, 27, v_n_4733_);
lean_ctor_set(v_reuseFailAlloc_4750_, 28, v_N_4734_);
lean_ctor_set(v_reuseFailAlloc_4750_, 29, v_V_4735_);
lean_ctor_set(v_reuseFailAlloc_4750_, 30, v_z_4736_);
lean_ctor_set(v_reuseFailAlloc_4750_, 31, v_zabbrev_4737_);
lean_ctor_set(v_reuseFailAlloc_4750_, 32, v_v_4738_);
lean_ctor_set(v_reuseFailAlloc_4750_, 33, v_O_4739_);
lean_ctor_set(v_reuseFailAlloc_4750_, 34, v_X_4740_);
lean_ctor_set(v_reuseFailAlloc_4750_, 35, v_x_4741_);
lean_ctor_set(v_reuseFailAlloc_4750_, 36, v_Z_4742_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
case 2:
{
lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4806_; 
v_isSharedCheck_4806_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_4806_ == 0)
{
lean_object* v_unused_4807_; 
v_unused_4807_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_4807_);
v___x_4757_ = v_modifier_4657_;
v_isShared_4758_ = v_isSharedCheck_4806_;
goto v_resetjp_4756_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4806_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v_G_4759_; lean_object* v_u_4760_; lean_object* v_Y_4761_; lean_object* v_D_4762_; lean_object* v_M_4763_; lean_object* v_L_4764_; lean_object* v_d_4765_; lean_object* v_Q_4766_; lean_object* v_q_4767_; lean_object* v_w_4768_; lean_object* v_W_4769_; lean_object* v_E_4770_; lean_object* v_e_4771_; lean_object* v_c_4772_; lean_object* v_F_4773_; lean_object* v_a_4774_; lean_object* v_b_4775_; lean_object* v_B_4776_; lean_object* v_h_4777_; lean_object* v_K_4778_; lean_object* v_k_4779_; lean_object* v_H_4780_; lean_object* v_m_4781_; lean_object* v_s_4782_; lean_object* v_S_4783_; lean_object* v_A_4784_; lean_object* v_n_4785_; lean_object* v_N_4786_; lean_object* v_V_4787_; lean_object* v_z_4788_; lean_object* v_zabbrev_4789_; lean_object* v_v_4790_; lean_object* v_O_4791_; lean_object* v_X_4792_; lean_object* v_x_4793_; lean_object* v_Z_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4804_; 
v_G_4759_ = lean_ctor_get(v_date_4656_, 0);
v_u_4760_ = lean_ctor_get(v_date_4656_, 2);
v_Y_4761_ = lean_ctor_get(v_date_4656_, 3);
v_D_4762_ = lean_ctor_get(v_date_4656_, 4);
v_M_4763_ = lean_ctor_get(v_date_4656_, 5);
v_L_4764_ = lean_ctor_get(v_date_4656_, 6);
v_d_4765_ = lean_ctor_get(v_date_4656_, 7);
v_Q_4766_ = lean_ctor_get(v_date_4656_, 8);
v_q_4767_ = lean_ctor_get(v_date_4656_, 9);
v_w_4768_ = lean_ctor_get(v_date_4656_, 10);
v_W_4769_ = lean_ctor_get(v_date_4656_, 11);
v_E_4770_ = lean_ctor_get(v_date_4656_, 12);
v_e_4771_ = lean_ctor_get(v_date_4656_, 13);
v_c_4772_ = lean_ctor_get(v_date_4656_, 14);
v_F_4773_ = lean_ctor_get(v_date_4656_, 15);
v_a_4774_ = lean_ctor_get(v_date_4656_, 16);
v_b_4775_ = lean_ctor_get(v_date_4656_, 17);
v_B_4776_ = lean_ctor_get(v_date_4656_, 18);
v_h_4777_ = lean_ctor_get(v_date_4656_, 19);
v_K_4778_ = lean_ctor_get(v_date_4656_, 20);
v_k_4779_ = lean_ctor_get(v_date_4656_, 21);
v_H_4780_ = lean_ctor_get(v_date_4656_, 22);
v_m_4781_ = lean_ctor_get(v_date_4656_, 23);
v_s_4782_ = lean_ctor_get(v_date_4656_, 24);
v_S_4783_ = lean_ctor_get(v_date_4656_, 25);
v_A_4784_ = lean_ctor_get(v_date_4656_, 26);
v_n_4785_ = lean_ctor_get(v_date_4656_, 27);
v_N_4786_ = lean_ctor_get(v_date_4656_, 28);
v_V_4787_ = lean_ctor_get(v_date_4656_, 29);
v_z_4788_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_4789_ = lean_ctor_get(v_date_4656_, 31);
v_v_4790_ = lean_ctor_get(v_date_4656_, 32);
v_O_4791_ = lean_ctor_get(v_date_4656_, 33);
v_X_4792_ = lean_ctor_get(v_date_4656_, 34);
v_x_4793_ = lean_ctor_get(v_date_4656_, 35);
v_Z_4794_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_4804_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_4804_ == 0)
{
lean_object* v_unused_4805_; 
v_unused_4805_ = lean_ctor_get(v_date_4656_, 1);
lean_dec(v_unused_4805_);
v___x_4796_ = v_date_4656_;
v_isShared_4797_ = v_isSharedCheck_4804_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_Z_4794_);
lean_inc(v_x_4793_);
lean_inc(v_X_4792_);
lean_inc(v_O_4791_);
lean_inc(v_v_4790_);
lean_inc(v_zabbrev_4789_);
lean_inc(v_z_4788_);
lean_inc(v_V_4787_);
lean_inc(v_N_4786_);
lean_inc(v_n_4785_);
lean_inc(v_A_4784_);
lean_inc(v_S_4783_);
lean_inc(v_s_4782_);
lean_inc(v_m_4781_);
lean_inc(v_H_4780_);
lean_inc(v_k_4779_);
lean_inc(v_K_4778_);
lean_inc(v_h_4777_);
lean_inc(v_B_4776_);
lean_inc(v_b_4775_);
lean_inc(v_a_4774_);
lean_inc(v_F_4773_);
lean_inc(v_c_4772_);
lean_inc(v_e_4771_);
lean_inc(v_E_4770_);
lean_inc(v_W_4769_);
lean_inc(v_w_4768_);
lean_inc(v_q_4767_);
lean_inc(v_Q_4766_);
lean_inc(v_d_4765_);
lean_inc(v_L_4764_);
lean_inc(v_M_4763_);
lean_inc(v_D_4762_);
lean_inc(v_Y_4761_);
lean_inc(v_u_4760_);
lean_inc(v_G_4759_);
lean_dec(v_date_4656_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4804_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4758_ == 0)
{
lean_ctor_set_tag(v___x_4757_, 1);
lean_ctor_set(v___x_4757_, 0, v_data_4658_);
v___x_4799_ = v___x_4757_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_data_4658_);
v___x_4799_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
lean_object* v___x_4801_; 
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 1, v___x_4799_);
v___x_4801_ = v___x_4796_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_G_4759_);
lean_ctor_set(v_reuseFailAlloc_4802_, 1, v___x_4799_);
lean_ctor_set(v_reuseFailAlloc_4802_, 2, v_u_4760_);
lean_ctor_set(v_reuseFailAlloc_4802_, 3, v_Y_4761_);
lean_ctor_set(v_reuseFailAlloc_4802_, 4, v_D_4762_);
lean_ctor_set(v_reuseFailAlloc_4802_, 5, v_M_4763_);
lean_ctor_set(v_reuseFailAlloc_4802_, 6, v_L_4764_);
lean_ctor_set(v_reuseFailAlloc_4802_, 7, v_d_4765_);
lean_ctor_set(v_reuseFailAlloc_4802_, 8, v_Q_4766_);
lean_ctor_set(v_reuseFailAlloc_4802_, 9, v_q_4767_);
lean_ctor_set(v_reuseFailAlloc_4802_, 10, v_w_4768_);
lean_ctor_set(v_reuseFailAlloc_4802_, 11, v_W_4769_);
lean_ctor_set(v_reuseFailAlloc_4802_, 12, v_E_4770_);
lean_ctor_set(v_reuseFailAlloc_4802_, 13, v_e_4771_);
lean_ctor_set(v_reuseFailAlloc_4802_, 14, v_c_4772_);
lean_ctor_set(v_reuseFailAlloc_4802_, 15, v_F_4773_);
lean_ctor_set(v_reuseFailAlloc_4802_, 16, v_a_4774_);
lean_ctor_set(v_reuseFailAlloc_4802_, 17, v_b_4775_);
lean_ctor_set(v_reuseFailAlloc_4802_, 18, v_B_4776_);
lean_ctor_set(v_reuseFailAlloc_4802_, 19, v_h_4777_);
lean_ctor_set(v_reuseFailAlloc_4802_, 20, v_K_4778_);
lean_ctor_set(v_reuseFailAlloc_4802_, 21, v_k_4779_);
lean_ctor_set(v_reuseFailAlloc_4802_, 22, v_H_4780_);
lean_ctor_set(v_reuseFailAlloc_4802_, 23, v_m_4781_);
lean_ctor_set(v_reuseFailAlloc_4802_, 24, v_s_4782_);
lean_ctor_set(v_reuseFailAlloc_4802_, 25, v_S_4783_);
lean_ctor_set(v_reuseFailAlloc_4802_, 26, v_A_4784_);
lean_ctor_set(v_reuseFailAlloc_4802_, 27, v_n_4785_);
lean_ctor_set(v_reuseFailAlloc_4802_, 28, v_N_4786_);
lean_ctor_set(v_reuseFailAlloc_4802_, 29, v_V_4787_);
lean_ctor_set(v_reuseFailAlloc_4802_, 30, v_z_4788_);
lean_ctor_set(v_reuseFailAlloc_4802_, 31, v_zabbrev_4789_);
lean_ctor_set(v_reuseFailAlloc_4802_, 32, v_v_4790_);
lean_ctor_set(v_reuseFailAlloc_4802_, 33, v_O_4791_);
lean_ctor_set(v_reuseFailAlloc_4802_, 34, v_X_4792_);
lean_ctor_set(v_reuseFailAlloc_4802_, 35, v_x_4793_);
lean_ctor_set(v_reuseFailAlloc_4802_, 36, v_Z_4794_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
}
case 3:
{
lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4858_; 
v_isSharedCheck_4858_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_4858_ == 0)
{
lean_object* v_unused_4859_; 
v_unused_4859_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_4859_);
v___x_4809_ = v_modifier_4657_;
v_isShared_4810_ = v_isSharedCheck_4858_;
goto v_resetjp_4808_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4858_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v_G_4811_; lean_object* v_y_4812_; lean_object* v_u_4813_; lean_object* v_Y_4814_; lean_object* v_M_4815_; lean_object* v_L_4816_; lean_object* v_d_4817_; lean_object* v_Q_4818_; lean_object* v_q_4819_; lean_object* v_w_4820_; lean_object* v_W_4821_; lean_object* v_E_4822_; lean_object* v_e_4823_; lean_object* v_c_4824_; lean_object* v_F_4825_; lean_object* v_a_4826_; lean_object* v_b_4827_; lean_object* v_B_4828_; lean_object* v_h_4829_; lean_object* v_K_4830_; lean_object* v_k_4831_; lean_object* v_H_4832_; lean_object* v_m_4833_; lean_object* v_s_4834_; lean_object* v_S_4835_; lean_object* v_A_4836_; lean_object* v_n_4837_; lean_object* v_N_4838_; lean_object* v_V_4839_; lean_object* v_z_4840_; lean_object* v_zabbrev_4841_; lean_object* v_v_4842_; lean_object* v_O_4843_; lean_object* v_X_4844_; lean_object* v_x_4845_; lean_object* v_Z_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4856_; 
v_G_4811_ = lean_ctor_get(v_date_4656_, 0);
v_y_4812_ = lean_ctor_get(v_date_4656_, 1);
v_u_4813_ = lean_ctor_get(v_date_4656_, 2);
v_Y_4814_ = lean_ctor_get(v_date_4656_, 3);
v_M_4815_ = lean_ctor_get(v_date_4656_, 5);
v_L_4816_ = lean_ctor_get(v_date_4656_, 6);
v_d_4817_ = lean_ctor_get(v_date_4656_, 7);
v_Q_4818_ = lean_ctor_get(v_date_4656_, 8);
v_q_4819_ = lean_ctor_get(v_date_4656_, 9);
v_w_4820_ = lean_ctor_get(v_date_4656_, 10);
v_W_4821_ = lean_ctor_get(v_date_4656_, 11);
v_E_4822_ = lean_ctor_get(v_date_4656_, 12);
v_e_4823_ = lean_ctor_get(v_date_4656_, 13);
v_c_4824_ = lean_ctor_get(v_date_4656_, 14);
v_F_4825_ = lean_ctor_get(v_date_4656_, 15);
v_a_4826_ = lean_ctor_get(v_date_4656_, 16);
v_b_4827_ = lean_ctor_get(v_date_4656_, 17);
v_B_4828_ = lean_ctor_get(v_date_4656_, 18);
v_h_4829_ = lean_ctor_get(v_date_4656_, 19);
v_K_4830_ = lean_ctor_get(v_date_4656_, 20);
v_k_4831_ = lean_ctor_get(v_date_4656_, 21);
v_H_4832_ = lean_ctor_get(v_date_4656_, 22);
v_m_4833_ = lean_ctor_get(v_date_4656_, 23);
v_s_4834_ = lean_ctor_get(v_date_4656_, 24);
v_S_4835_ = lean_ctor_get(v_date_4656_, 25);
v_A_4836_ = lean_ctor_get(v_date_4656_, 26);
v_n_4837_ = lean_ctor_get(v_date_4656_, 27);
v_N_4838_ = lean_ctor_get(v_date_4656_, 28);
v_V_4839_ = lean_ctor_get(v_date_4656_, 29);
v_z_4840_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_4841_ = lean_ctor_get(v_date_4656_, 31);
v_v_4842_ = lean_ctor_get(v_date_4656_, 32);
v_O_4843_ = lean_ctor_get(v_date_4656_, 33);
v_X_4844_ = lean_ctor_get(v_date_4656_, 34);
v_x_4845_ = lean_ctor_get(v_date_4656_, 35);
v_Z_4846_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_4856_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_4856_ == 0)
{
lean_object* v_unused_4857_; 
v_unused_4857_ = lean_ctor_get(v_date_4656_, 4);
lean_dec(v_unused_4857_);
v___x_4848_ = v_date_4656_;
v_isShared_4849_ = v_isSharedCheck_4856_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_Z_4846_);
lean_inc(v_x_4845_);
lean_inc(v_X_4844_);
lean_inc(v_O_4843_);
lean_inc(v_v_4842_);
lean_inc(v_zabbrev_4841_);
lean_inc(v_z_4840_);
lean_inc(v_V_4839_);
lean_inc(v_N_4838_);
lean_inc(v_n_4837_);
lean_inc(v_A_4836_);
lean_inc(v_S_4835_);
lean_inc(v_s_4834_);
lean_inc(v_m_4833_);
lean_inc(v_H_4832_);
lean_inc(v_k_4831_);
lean_inc(v_K_4830_);
lean_inc(v_h_4829_);
lean_inc(v_B_4828_);
lean_inc(v_b_4827_);
lean_inc(v_a_4826_);
lean_inc(v_F_4825_);
lean_inc(v_c_4824_);
lean_inc(v_e_4823_);
lean_inc(v_E_4822_);
lean_inc(v_W_4821_);
lean_inc(v_w_4820_);
lean_inc(v_q_4819_);
lean_inc(v_Q_4818_);
lean_inc(v_d_4817_);
lean_inc(v_L_4816_);
lean_inc(v_M_4815_);
lean_inc(v_Y_4814_);
lean_inc(v_u_4813_);
lean_inc(v_y_4812_);
lean_inc(v_G_4811_);
lean_dec(v_date_4656_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4856_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4810_ == 0)
{
lean_ctor_set_tag(v___x_4809_, 1);
lean_ctor_set(v___x_4809_, 0, v_data_4658_);
v___x_4851_ = v___x_4809_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_data_4658_);
v___x_4851_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
lean_object* v___x_4853_; 
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 4, v___x_4851_);
v___x_4853_ = v___x_4848_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_G_4811_);
lean_ctor_set(v_reuseFailAlloc_4854_, 1, v_y_4812_);
lean_ctor_set(v_reuseFailAlloc_4854_, 2, v_u_4813_);
lean_ctor_set(v_reuseFailAlloc_4854_, 3, v_Y_4814_);
lean_ctor_set(v_reuseFailAlloc_4854_, 4, v___x_4851_);
lean_ctor_set(v_reuseFailAlloc_4854_, 5, v_M_4815_);
lean_ctor_set(v_reuseFailAlloc_4854_, 6, v_L_4816_);
lean_ctor_set(v_reuseFailAlloc_4854_, 7, v_d_4817_);
lean_ctor_set(v_reuseFailAlloc_4854_, 8, v_Q_4818_);
lean_ctor_set(v_reuseFailAlloc_4854_, 9, v_q_4819_);
lean_ctor_set(v_reuseFailAlloc_4854_, 10, v_w_4820_);
lean_ctor_set(v_reuseFailAlloc_4854_, 11, v_W_4821_);
lean_ctor_set(v_reuseFailAlloc_4854_, 12, v_E_4822_);
lean_ctor_set(v_reuseFailAlloc_4854_, 13, v_e_4823_);
lean_ctor_set(v_reuseFailAlloc_4854_, 14, v_c_4824_);
lean_ctor_set(v_reuseFailAlloc_4854_, 15, v_F_4825_);
lean_ctor_set(v_reuseFailAlloc_4854_, 16, v_a_4826_);
lean_ctor_set(v_reuseFailAlloc_4854_, 17, v_b_4827_);
lean_ctor_set(v_reuseFailAlloc_4854_, 18, v_B_4828_);
lean_ctor_set(v_reuseFailAlloc_4854_, 19, v_h_4829_);
lean_ctor_set(v_reuseFailAlloc_4854_, 20, v_K_4830_);
lean_ctor_set(v_reuseFailAlloc_4854_, 21, v_k_4831_);
lean_ctor_set(v_reuseFailAlloc_4854_, 22, v_H_4832_);
lean_ctor_set(v_reuseFailAlloc_4854_, 23, v_m_4833_);
lean_ctor_set(v_reuseFailAlloc_4854_, 24, v_s_4834_);
lean_ctor_set(v_reuseFailAlloc_4854_, 25, v_S_4835_);
lean_ctor_set(v_reuseFailAlloc_4854_, 26, v_A_4836_);
lean_ctor_set(v_reuseFailAlloc_4854_, 27, v_n_4837_);
lean_ctor_set(v_reuseFailAlloc_4854_, 28, v_N_4838_);
lean_ctor_set(v_reuseFailAlloc_4854_, 29, v_V_4839_);
lean_ctor_set(v_reuseFailAlloc_4854_, 30, v_z_4840_);
lean_ctor_set(v_reuseFailAlloc_4854_, 31, v_zabbrev_4841_);
lean_ctor_set(v_reuseFailAlloc_4854_, 32, v_v_4842_);
lean_ctor_set(v_reuseFailAlloc_4854_, 33, v_O_4843_);
lean_ctor_set(v_reuseFailAlloc_4854_, 34, v_X_4844_);
lean_ctor_set(v_reuseFailAlloc_4854_, 35, v_x_4845_);
lean_ctor_set(v_reuseFailAlloc_4854_, 36, v_Z_4846_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
case 4:
{
lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4910_; 
v_isSharedCheck_4910_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_4910_ == 0)
{
lean_object* v_unused_4911_; 
v_unused_4911_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_4911_);
v___x_4861_ = v_modifier_4657_;
v_isShared_4862_ = v_isSharedCheck_4910_;
goto v_resetjp_4860_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4910_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v_G_4863_; lean_object* v_y_4864_; lean_object* v_u_4865_; lean_object* v_Y_4866_; lean_object* v_D_4867_; lean_object* v_L_4868_; lean_object* v_d_4869_; lean_object* v_Q_4870_; lean_object* v_q_4871_; lean_object* v_w_4872_; lean_object* v_W_4873_; lean_object* v_E_4874_; lean_object* v_e_4875_; lean_object* v_c_4876_; lean_object* v_F_4877_; lean_object* v_a_4878_; lean_object* v_b_4879_; lean_object* v_B_4880_; lean_object* v_h_4881_; lean_object* v_K_4882_; lean_object* v_k_4883_; lean_object* v_H_4884_; lean_object* v_m_4885_; lean_object* v_s_4886_; lean_object* v_S_4887_; lean_object* v_A_4888_; lean_object* v_n_4889_; lean_object* v_N_4890_; lean_object* v_V_4891_; lean_object* v_z_4892_; lean_object* v_zabbrev_4893_; lean_object* v_v_4894_; lean_object* v_O_4895_; lean_object* v_X_4896_; lean_object* v_x_4897_; lean_object* v_Z_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4908_; 
v_G_4863_ = lean_ctor_get(v_date_4656_, 0);
v_y_4864_ = lean_ctor_get(v_date_4656_, 1);
v_u_4865_ = lean_ctor_get(v_date_4656_, 2);
v_Y_4866_ = lean_ctor_get(v_date_4656_, 3);
v_D_4867_ = lean_ctor_get(v_date_4656_, 4);
v_L_4868_ = lean_ctor_get(v_date_4656_, 6);
v_d_4869_ = lean_ctor_get(v_date_4656_, 7);
v_Q_4870_ = lean_ctor_get(v_date_4656_, 8);
v_q_4871_ = lean_ctor_get(v_date_4656_, 9);
v_w_4872_ = lean_ctor_get(v_date_4656_, 10);
v_W_4873_ = lean_ctor_get(v_date_4656_, 11);
v_E_4874_ = lean_ctor_get(v_date_4656_, 12);
v_e_4875_ = lean_ctor_get(v_date_4656_, 13);
v_c_4876_ = lean_ctor_get(v_date_4656_, 14);
v_F_4877_ = lean_ctor_get(v_date_4656_, 15);
v_a_4878_ = lean_ctor_get(v_date_4656_, 16);
v_b_4879_ = lean_ctor_get(v_date_4656_, 17);
v_B_4880_ = lean_ctor_get(v_date_4656_, 18);
v_h_4881_ = lean_ctor_get(v_date_4656_, 19);
v_K_4882_ = lean_ctor_get(v_date_4656_, 20);
v_k_4883_ = lean_ctor_get(v_date_4656_, 21);
v_H_4884_ = lean_ctor_get(v_date_4656_, 22);
v_m_4885_ = lean_ctor_get(v_date_4656_, 23);
v_s_4886_ = lean_ctor_get(v_date_4656_, 24);
v_S_4887_ = lean_ctor_get(v_date_4656_, 25);
v_A_4888_ = lean_ctor_get(v_date_4656_, 26);
v_n_4889_ = lean_ctor_get(v_date_4656_, 27);
v_N_4890_ = lean_ctor_get(v_date_4656_, 28);
v_V_4891_ = lean_ctor_get(v_date_4656_, 29);
v_z_4892_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_4893_ = lean_ctor_get(v_date_4656_, 31);
v_v_4894_ = lean_ctor_get(v_date_4656_, 32);
v_O_4895_ = lean_ctor_get(v_date_4656_, 33);
v_X_4896_ = lean_ctor_get(v_date_4656_, 34);
v_x_4897_ = lean_ctor_get(v_date_4656_, 35);
v_Z_4898_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_4908_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_4908_ == 0)
{
lean_object* v_unused_4909_; 
v_unused_4909_ = lean_ctor_get(v_date_4656_, 5);
lean_dec(v_unused_4909_);
v___x_4900_ = v_date_4656_;
v_isShared_4901_ = v_isSharedCheck_4908_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_Z_4898_);
lean_inc(v_x_4897_);
lean_inc(v_X_4896_);
lean_inc(v_O_4895_);
lean_inc(v_v_4894_);
lean_inc(v_zabbrev_4893_);
lean_inc(v_z_4892_);
lean_inc(v_V_4891_);
lean_inc(v_N_4890_);
lean_inc(v_n_4889_);
lean_inc(v_A_4888_);
lean_inc(v_S_4887_);
lean_inc(v_s_4886_);
lean_inc(v_m_4885_);
lean_inc(v_H_4884_);
lean_inc(v_k_4883_);
lean_inc(v_K_4882_);
lean_inc(v_h_4881_);
lean_inc(v_B_4880_);
lean_inc(v_b_4879_);
lean_inc(v_a_4878_);
lean_inc(v_F_4877_);
lean_inc(v_c_4876_);
lean_inc(v_e_4875_);
lean_inc(v_E_4874_);
lean_inc(v_W_4873_);
lean_inc(v_w_4872_);
lean_inc(v_q_4871_);
lean_inc(v_Q_4870_);
lean_inc(v_d_4869_);
lean_inc(v_L_4868_);
lean_inc(v_D_4867_);
lean_inc(v_Y_4866_);
lean_inc(v_u_4865_);
lean_inc(v_y_4864_);
lean_inc(v_G_4863_);
lean_dec(v_date_4656_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4908_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4862_ == 0)
{
lean_ctor_set_tag(v___x_4861_, 1);
lean_ctor_set(v___x_4861_, 0, v_data_4658_);
v___x_4903_ = v___x_4861_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_data_4658_);
v___x_4903_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
lean_object* v___x_4905_; 
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 5, v___x_4903_);
v___x_4905_ = v___x_4900_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_G_4863_);
lean_ctor_set(v_reuseFailAlloc_4906_, 1, v_y_4864_);
lean_ctor_set(v_reuseFailAlloc_4906_, 2, v_u_4865_);
lean_ctor_set(v_reuseFailAlloc_4906_, 3, v_Y_4866_);
lean_ctor_set(v_reuseFailAlloc_4906_, 4, v_D_4867_);
lean_ctor_set(v_reuseFailAlloc_4906_, 5, v___x_4903_);
lean_ctor_set(v_reuseFailAlloc_4906_, 6, v_L_4868_);
lean_ctor_set(v_reuseFailAlloc_4906_, 7, v_d_4869_);
lean_ctor_set(v_reuseFailAlloc_4906_, 8, v_Q_4870_);
lean_ctor_set(v_reuseFailAlloc_4906_, 9, v_q_4871_);
lean_ctor_set(v_reuseFailAlloc_4906_, 10, v_w_4872_);
lean_ctor_set(v_reuseFailAlloc_4906_, 11, v_W_4873_);
lean_ctor_set(v_reuseFailAlloc_4906_, 12, v_E_4874_);
lean_ctor_set(v_reuseFailAlloc_4906_, 13, v_e_4875_);
lean_ctor_set(v_reuseFailAlloc_4906_, 14, v_c_4876_);
lean_ctor_set(v_reuseFailAlloc_4906_, 15, v_F_4877_);
lean_ctor_set(v_reuseFailAlloc_4906_, 16, v_a_4878_);
lean_ctor_set(v_reuseFailAlloc_4906_, 17, v_b_4879_);
lean_ctor_set(v_reuseFailAlloc_4906_, 18, v_B_4880_);
lean_ctor_set(v_reuseFailAlloc_4906_, 19, v_h_4881_);
lean_ctor_set(v_reuseFailAlloc_4906_, 20, v_K_4882_);
lean_ctor_set(v_reuseFailAlloc_4906_, 21, v_k_4883_);
lean_ctor_set(v_reuseFailAlloc_4906_, 22, v_H_4884_);
lean_ctor_set(v_reuseFailAlloc_4906_, 23, v_m_4885_);
lean_ctor_set(v_reuseFailAlloc_4906_, 24, v_s_4886_);
lean_ctor_set(v_reuseFailAlloc_4906_, 25, v_S_4887_);
lean_ctor_set(v_reuseFailAlloc_4906_, 26, v_A_4888_);
lean_ctor_set(v_reuseFailAlloc_4906_, 27, v_n_4889_);
lean_ctor_set(v_reuseFailAlloc_4906_, 28, v_N_4890_);
lean_ctor_set(v_reuseFailAlloc_4906_, 29, v_V_4891_);
lean_ctor_set(v_reuseFailAlloc_4906_, 30, v_z_4892_);
lean_ctor_set(v_reuseFailAlloc_4906_, 31, v_zabbrev_4893_);
lean_ctor_set(v_reuseFailAlloc_4906_, 32, v_v_4894_);
lean_ctor_set(v_reuseFailAlloc_4906_, 33, v_O_4895_);
lean_ctor_set(v_reuseFailAlloc_4906_, 34, v_X_4896_);
lean_ctor_set(v_reuseFailAlloc_4906_, 35, v_x_4897_);
lean_ctor_set(v_reuseFailAlloc_4906_, 36, v_Z_4898_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
}
case 5:
{
lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4962_; 
v_isSharedCheck_4962_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_4962_ == 0)
{
lean_object* v_unused_4963_; 
v_unused_4963_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_4963_);
v___x_4913_ = v_modifier_4657_;
v_isShared_4914_ = v_isSharedCheck_4962_;
goto v_resetjp_4912_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4962_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v_G_4915_; lean_object* v_y_4916_; lean_object* v_u_4917_; lean_object* v_Y_4918_; lean_object* v_D_4919_; lean_object* v_M_4920_; lean_object* v_d_4921_; lean_object* v_Q_4922_; lean_object* v_q_4923_; lean_object* v_w_4924_; lean_object* v_W_4925_; lean_object* v_E_4926_; lean_object* v_e_4927_; lean_object* v_c_4928_; lean_object* v_F_4929_; lean_object* v_a_4930_; lean_object* v_b_4931_; lean_object* v_B_4932_; lean_object* v_h_4933_; lean_object* v_K_4934_; lean_object* v_k_4935_; lean_object* v_H_4936_; lean_object* v_m_4937_; lean_object* v_s_4938_; lean_object* v_S_4939_; lean_object* v_A_4940_; lean_object* v_n_4941_; lean_object* v_N_4942_; lean_object* v_V_4943_; lean_object* v_z_4944_; lean_object* v_zabbrev_4945_; lean_object* v_v_4946_; lean_object* v_O_4947_; lean_object* v_X_4948_; lean_object* v_x_4949_; lean_object* v_Z_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4960_; 
v_G_4915_ = lean_ctor_get(v_date_4656_, 0);
v_y_4916_ = lean_ctor_get(v_date_4656_, 1);
v_u_4917_ = lean_ctor_get(v_date_4656_, 2);
v_Y_4918_ = lean_ctor_get(v_date_4656_, 3);
v_D_4919_ = lean_ctor_get(v_date_4656_, 4);
v_M_4920_ = lean_ctor_get(v_date_4656_, 5);
v_d_4921_ = lean_ctor_get(v_date_4656_, 7);
v_Q_4922_ = lean_ctor_get(v_date_4656_, 8);
v_q_4923_ = lean_ctor_get(v_date_4656_, 9);
v_w_4924_ = lean_ctor_get(v_date_4656_, 10);
v_W_4925_ = lean_ctor_get(v_date_4656_, 11);
v_E_4926_ = lean_ctor_get(v_date_4656_, 12);
v_e_4927_ = lean_ctor_get(v_date_4656_, 13);
v_c_4928_ = lean_ctor_get(v_date_4656_, 14);
v_F_4929_ = lean_ctor_get(v_date_4656_, 15);
v_a_4930_ = lean_ctor_get(v_date_4656_, 16);
v_b_4931_ = lean_ctor_get(v_date_4656_, 17);
v_B_4932_ = lean_ctor_get(v_date_4656_, 18);
v_h_4933_ = lean_ctor_get(v_date_4656_, 19);
v_K_4934_ = lean_ctor_get(v_date_4656_, 20);
v_k_4935_ = lean_ctor_get(v_date_4656_, 21);
v_H_4936_ = lean_ctor_get(v_date_4656_, 22);
v_m_4937_ = lean_ctor_get(v_date_4656_, 23);
v_s_4938_ = lean_ctor_get(v_date_4656_, 24);
v_S_4939_ = lean_ctor_get(v_date_4656_, 25);
v_A_4940_ = lean_ctor_get(v_date_4656_, 26);
v_n_4941_ = lean_ctor_get(v_date_4656_, 27);
v_N_4942_ = lean_ctor_get(v_date_4656_, 28);
v_V_4943_ = lean_ctor_get(v_date_4656_, 29);
v_z_4944_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_4945_ = lean_ctor_get(v_date_4656_, 31);
v_v_4946_ = lean_ctor_get(v_date_4656_, 32);
v_O_4947_ = lean_ctor_get(v_date_4656_, 33);
v_X_4948_ = lean_ctor_get(v_date_4656_, 34);
v_x_4949_ = lean_ctor_get(v_date_4656_, 35);
v_Z_4950_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_4960_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_4960_ == 0)
{
lean_object* v_unused_4961_; 
v_unused_4961_ = lean_ctor_get(v_date_4656_, 6);
lean_dec(v_unused_4961_);
v___x_4952_ = v_date_4656_;
v_isShared_4953_ = v_isSharedCheck_4960_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_Z_4950_);
lean_inc(v_x_4949_);
lean_inc(v_X_4948_);
lean_inc(v_O_4947_);
lean_inc(v_v_4946_);
lean_inc(v_zabbrev_4945_);
lean_inc(v_z_4944_);
lean_inc(v_V_4943_);
lean_inc(v_N_4942_);
lean_inc(v_n_4941_);
lean_inc(v_A_4940_);
lean_inc(v_S_4939_);
lean_inc(v_s_4938_);
lean_inc(v_m_4937_);
lean_inc(v_H_4936_);
lean_inc(v_k_4935_);
lean_inc(v_K_4934_);
lean_inc(v_h_4933_);
lean_inc(v_B_4932_);
lean_inc(v_b_4931_);
lean_inc(v_a_4930_);
lean_inc(v_F_4929_);
lean_inc(v_c_4928_);
lean_inc(v_e_4927_);
lean_inc(v_E_4926_);
lean_inc(v_W_4925_);
lean_inc(v_w_4924_);
lean_inc(v_q_4923_);
lean_inc(v_Q_4922_);
lean_inc(v_d_4921_);
lean_inc(v_M_4920_);
lean_inc(v_D_4919_);
lean_inc(v_Y_4918_);
lean_inc(v_u_4917_);
lean_inc(v_y_4916_);
lean_inc(v_G_4915_);
lean_dec(v_date_4656_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4960_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4914_ == 0)
{
lean_ctor_set_tag(v___x_4913_, 1);
lean_ctor_set(v___x_4913_, 0, v_data_4658_);
v___x_4955_ = v___x_4913_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_data_4658_);
v___x_4955_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
lean_object* v___x_4957_; 
if (v_isShared_4953_ == 0)
{
lean_ctor_set(v___x_4952_, 6, v___x_4955_);
v___x_4957_ = v___x_4952_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_G_4915_);
lean_ctor_set(v_reuseFailAlloc_4958_, 1, v_y_4916_);
lean_ctor_set(v_reuseFailAlloc_4958_, 2, v_u_4917_);
lean_ctor_set(v_reuseFailAlloc_4958_, 3, v_Y_4918_);
lean_ctor_set(v_reuseFailAlloc_4958_, 4, v_D_4919_);
lean_ctor_set(v_reuseFailAlloc_4958_, 5, v_M_4920_);
lean_ctor_set(v_reuseFailAlloc_4958_, 6, v___x_4955_);
lean_ctor_set(v_reuseFailAlloc_4958_, 7, v_d_4921_);
lean_ctor_set(v_reuseFailAlloc_4958_, 8, v_Q_4922_);
lean_ctor_set(v_reuseFailAlloc_4958_, 9, v_q_4923_);
lean_ctor_set(v_reuseFailAlloc_4958_, 10, v_w_4924_);
lean_ctor_set(v_reuseFailAlloc_4958_, 11, v_W_4925_);
lean_ctor_set(v_reuseFailAlloc_4958_, 12, v_E_4926_);
lean_ctor_set(v_reuseFailAlloc_4958_, 13, v_e_4927_);
lean_ctor_set(v_reuseFailAlloc_4958_, 14, v_c_4928_);
lean_ctor_set(v_reuseFailAlloc_4958_, 15, v_F_4929_);
lean_ctor_set(v_reuseFailAlloc_4958_, 16, v_a_4930_);
lean_ctor_set(v_reuseFailAlloc_4958_, 17, v_b_4931_);
lean_ctor_set(v_reuseFailAlloc_4958_, 18, v_B_4932_);
lean_ctor_set(v_reuseFailAlloc_4958_, 19, v_h_4933_);
lean_ctor_set(v_reuseFailAlloc_4958_, 20, v_K_4934_);
lean_ctor_set(v_reuseFailAlloc_4958_, 21, v_k_4935_);
lean_ctor_set(v_reuseFailAlloc_4958_, 22, v_H_4936_);
lean_ctor_set(v_reuseFailAlloc_4958_, 23, v_m_4937_);
lean_ctor_set(v_reuseFailAlloc_4958_, 24, v_s_4938_);
lean_ctor_set(v_reuseFailAlloc_4958_, 25, v_S_4939_);
lean_ctor_set(v_reuseFailAlloc_4958_, 26, v_A_4940_);
lean_ctor_set(v_reuseFailAlloc_4958_, 27, v_n_4941_);
lean_ctor_set(v_reuseFailAlloc_4958_, 28, v_N_4942_);
lean_ctor_set(v_reuseFailAlloc_4958_, 29, v_V_4943_);
lean_ctor_set(v_reuseFailAlloc_4958_, 30, v_z_4944_);
lean_ctor_set(v_reuseFailAlloc_4958_, 31, v_zabbrev_4945_);
lean_ctor_set(v_reuseFailAlloc_4958_, 32, v_v_4946_);
lean_ctor_set(v_reuseFailAlloc_4958_, 33, v_O_4947_);
lean_ctor_set(v_reuseFailAlloc_4958_, 34, v_X_4948_);
lean_ctor_set(v_reuseFailAlloc_4958_, 35, v_x_4949_);
lean_ctor_set(v_reuseFailAlloc_4958_, 36, v_Z_4950_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
}
case 6:
{
lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_5014_; 
v_isSharedCheck_5014_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5014_ == 0)
{
lean_object* v_unused_5015_; 
v_unused_5015_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5015_);
v___x_4965_ = v_modifier_4657_;
v_isShared_4966_ = v_isSharedCheck_5014_;
goto v_resetjp_4964_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_5014_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v_G_4967_; lean_object* v_y_4968_; lean_object* v_u_4969_; lean_object* v_Y_4970_; lean_object* v_D_4971_; lean_object* v_M_4972_; lean_object* v_L_4973_; lean_object* v_Q_4974_; lean_object* v_q_4975_; lean_object* v_w_4976_; lean_object* v_W_4977_; lean_object* v_E_4978_; lean_object* v_e_4979_; lean_object* v_c_4980_; lean_object* v_F_4981_; lean_object* v_a_4982_; lean_object* v_b_4983_; lean_object* v_B_4984_; lean_object* v_h_4985_; lean_object* v_K_4986_; lean_object* v_k_4987_; lean_object* v_H_4988_; lean_object* v_m_4989_; lean_object* v_s_4990_; lean_object* v_S_4991_; lean_object* v_A_4992_; lean_object* v_n_4993_; lean_object* v_N_4994_; lean_object* v_V_4995_; lean_object* v_z_4996_; lean_object* v_zabbrev_4997_; lean_object* v_v_4998_; lean_object* v_O_4999_; lean_object* v_X_5000_; lean_object* v_x_5001_; lean_object* v_Z_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5012_; 
v_G_4967_ = lean_ctor_get(v_date_4656_, 0);
v_y_4968_ = lean_ctor_get(v_date_4656_, 1);
v_u_4969_ = lean_ctor_get(v_date_4656_, 2);
v_Y_4970_ = lean_ctor_get(v_date_4656_, 3);
v_D_4971_ = lean_ctor_get(v_date_4656_, 4);
v_M_4972_ = lean_ctor_get(v_date_4656_, 5);
v_L_4973_ = lean_ctor_get(v_date_4656_, 6);
v_Q_4974_ = lean_ctor_get(v_date_4656_, 8);
v_q_4975_ = lean_ctor_get(v_date_4656_, 9);
v_w_4976_ = lean_ctor_get(v_date_4656_, 10);
v_W_4977_ = lean_ctor_get(v_date_4656_, 11);
v_E_4978_ = lean_ctor_get(v_date_4656_, 12);
v_e_4979_ = lean_ctor_get(v_date_4656_, 13);
v_c_4980_ = lean_ctor_get(v_date_4656_, 14);
v_F_4981_ = lean_ctor_get(v_date_4656_, 15);
v_a_4982_ = lean_ctor_get(v_date_4656_, 16);
v_b_4983_ = lean_ctor_get(v_date_4656_, 17);
v_B_4984_ = lean_ctor_get(v_date_4656_, 18);
v_h_4985_ = lean_ctor_get(v_date_4656_, 19);
v_K_4986_ = lean_ctor_get(v_date_4656_, 20);
v_k_4987_ = lean_ctor_get(v_date_4656_, 21);
v_H_4988_ = lean_ctor_get(v_date_4656_, 22);
v_m_4989_ = lean_ctor_get(v_date_4656_, 23);
v_s_4990_ = lean_ctor_get(v_date_4656_, 24);
v_S_4991_ = lean_ctor_get(v_date_4656_, 25);
v_A_4992_ = lean_ctor_get(v_date_4656_, 26);
v_n_4993_ = lean_ctor_get(v_date_4656_, 27);
v_N_4994_ = lean_ctor_get(v_date_4656_, 28);
v_V_4995_ = lean_ctor_get(v_date_4656_, 29);
v_z_4996_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_4997_ = lean_ctor_get(v_date_4656_, 31);
v_v_4998_ = lean_ctor_get(v_date_4656_, 32);
v_O_4999_ = lean_ctor_get(v_date_4656_, 33);
v_X_5000_ = lean_ctor_get(v_date_4656_, 34);
v_x_5001_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5002_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5012_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5012_ == 0)
{
lean_object* v_unused_5013_; 
v_unused_5013_ = lean_ctor_get(v_date_4656_, 7);
lean_dec(v_unused_5013_);
v___x_5004_ = v_date_4656_;
v_isShared_5005_ = v_isSharedCheck_5012_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_Z_5002_);
lean_inc(v_x_5001_);
lean_inc(v_X_5000_);
lean_inc(v_O_4999_);
lean_inc(v_v_4998_);
lean_inc(v_zabbrev_4997_);
lean_inc(v_z_4996_);
lean_inc(v_V_4995_);
lean_inc(v_N_4994_);
lean_inc(v_n_4993_);
lean_inc(v_A_4992_);
lean_inc(v_S_4991_);
lean_inc(v_s_4990_);
lean_inc(v_m_4989_);
lean_inc(v_H_4988_);
lean_inc(v_k_4987_);
lean_inc(v_K_4986_);
lean_inc(v_h_4985_);
lean_inc(v_B_4984_);
lean_inc(v_b_4983_);
lean_inc(v_a_4982_);
lean_inc(v_F_4981_);
lean_inc(v_c_4980_);
lean_inc(v_e_4979_);
lean_inc(v_E_4978_);
lean_inc(v_W_4977_);
lean_inc(v_w_4976_);
lean_inc(v_q_4975_);
lean_inc(v_Q_4974_);
lean_inc(v_L_4973_);
lean_inc(v_M_4972_);
lean_inc(v_D_4971_);
lean_inc(v_Y_4970_);
lean_inc(v_u_4969_);
lean_inc(v_y_4968_);
lean_inc(v_G_4967_);
lean_dec(v_date_4656_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5012_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_4966_ == 0)
{
lean_ctor_set_tag(v___x_4965_, 1);
lean_ctor_set(v___x_4965_, 0, v_data_4658_);
v___x_5007_ = v___x_4965_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_data_4658_);
v___x_5007_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
lean_object* v___x_5009_; 
if (v_isShared_5005_ == 0)
{
lean_ctor_set(v___x_5004_, 7, v___x_5007_);
v___x_5009_ = v___x_5004_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_G_4967_);
lean_ctor_set(v_reuseFailAlloc_5010_, 1, v_y_4968_);
lean_ctor_set(v_reuseFailAlloc_5010_, 2, v_u_4969_);
lean_ctor_set(v_reuseFailAlloc_5010_, 3, v_Y_4970_);
lean_ctor_set(v_reuseFailAlloc_5010_, 4, v_D_4971_);
lean_ctor_set(v_reuseFailAlloc_5010_, 5, v_M_4972_);
lean_ctor_set(v_reuseFailAlloc_5010_, 6, v_L_4973_);
lean_ctor_set(v_reuseFailAlloc_5010_, 7, v___x_5007_);
lean_ctor_set(v_reuseFailAlloc_5010_, 8, v_Q_4974_);
lean_ctor_set(v_reuseFailAlloc_5010_, 9, v_q_4975_);
lean_ctor_set(v_reuseFailAlloc_5010_, 10, v_w_4976_);
lean_ctor_set(v_reuseFailAlloc_5010_, 11, v_W_4977_);
lean_ctor_set(v_reuseFailAlloc_5010_, 12, v_E_4978_);
lean_ctor_set(v_reuseFailAlloc_5010_, 13, v_e_4979_);
lean_ctor_set(v_reuseFailAlloc_5010_, 14, v_c_4980_);
lean_ctor_set(v_reuseFailAlloc_5010_, 15, v_F_4981_);
lean_ctor_set(v_reuseFailAlloc_5010_, 16, v_a_4982_);
lean_ctor_set(v_reuseFailAlloc_5010_, 17, v_b_4983_);
lean_ctor_set(v_reuseFailAlloc_5010_, 18, v_B_4984_);
lean_ctor_set(v_reuseFailAlloc_5010_, 19, v_h_4985_);
lean_ctor_set(v_reuseFailAlloc_5010_, 20, v_K_4986_);
lean_ctor_set(v_reuseFailAlloc_5010_, 21, v_k_4987_);
lean_ctor_set(v_reuseFailAlloc_5010_, 22, v_H_4988_);
lean_ctor_set(v_reuseFailAlloc_5010_, 23, v_m_4989_);
lean_ctor_set(v_reuseFailAlloc_5010_, 24, v_s_4990_);
lean_ctor_set(v_reuseFailAlloc_5010_, 25, v_S_4991_);
lean_ctor_set(v_reuseFailAlloc_5010_, 26, v_A_4992_);
lean_ctor_set(v_reuseFailAlloc_5010_, 27, v_n_4993_);
lean_ctor_set(v_reuseFailAlloc_5010_, 28, v_N_4994_);
lean_ctor_set(v_reuseFailAlloc_5010_, 29, v_V_4995_);
lean_ctor_set(v_reuseFailAlloc_5010_, 30, v_z_4996_);
lean_ctor_set(v_reuseFailAlloc_5010_, 31, v_zabbrev_4997_);
lean_ctor_set(v_reuseFailAlloc_5010_, 32, v_v_4998_);
lean_ctor_set(v_reuseFailAlloc_5010_, 33, v_O_4999_);
lean_ctor_set(v_reuseFailAlloc_5010_, 34, v_X_5000_);
lean_ctor_set(v_reuseFailAlloc_5010_, 35, v_x_5001_);
lean_ctor_set(v_reuseFailAlloc_5010_, 36, v_Z_5002_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
}
}
case 7:
{
lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5066_; 
v_isSharedCheck_5066_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5066_ == 0)
{
lean_object* v_unused_5067_; 
v_unused_5067_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5067_);
v___x_5017_ = v_modifier_4657_;
v_isShared_5018_ = v_isSharedCheck_5066_;
goto v_resetjp_5016_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5066_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v_G_5019_; lean_object* v_y_5020_; lean_object* v_u_5021_; lean_object* v_Y_5022_; lean_object* v_D_5023_; lean_object* v_M_5024_; lean_object* v_L_5025_; lean_object* v_d_5026_; lean_object* v_q_5027_; lean_object* v_w_5028_; lean_object* v_W_5029_; lean_object* v_E_5030_; lean_object* v_e_5031_; lean_object* v_c_5032_; lean_object* v_F_5033_; lean_object* v_a_5034_; lean_object* v_b_5035_; lean_object* v_B_5036_; lean_object* v_h_5037_; lean_object* v_K_5038_; lean_object* v_k_5039_; lean_object* v_H_5040_; lean_object* v_m_5041_; lean_object* v_s_5042_; lean_object* v_S_5043_; lean_object* v_A_5044_; lean_object* v_n_5045_; lean_object* v_N_5046_; lean_object* v_V_5047_; lean_object* v_z_5048_; lean_object* v_zabbrev_5049_; lean_object* v_v_5050_; lean_object* v_O_5051_; lean_object* v_X_5052_; lean_object* v_x_5053_; lean_object* v_Z_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5064_; 
v_G_5019_ = lean_ctor_get(v_date_4656_, 0);
v_y_5020_ = lean_ctor_get(v_date_4656_, 1);
v_u_5021_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5022_ = lean_ctor_get(v_date_4656_, 3);
v_D_5023_ = lean_ctor_get(v_date_4656_, 4);
v_M_5024_ = lean_ctor_get(v_date_4656_, 5);
v_L_5025_ = lean_ctor_get(v_date_4656_, 6);
v_d_5026_ = lean_ctor_get(v_date_4656_, 7);
v_q_5027_ = lean_ctor_get(v_date_4656_, 9);
v_w_5028_ = lean_ctor_get(v_date_4656_, 10);
v_W_5029_ = lean_ctor_get(v_date_4656_, 11);
v_E_5030_ = lean_ctor_get(v_date_4656_, 12);
v_e_5031_ = lean_ctor_get(v_date_4656_, 13);
v_c_5032_ = lean_ctor_get(v_date_4656_, 14);
v_F_5033_ = lean_ctor_get(v_date_4656_, 15);
v_a_5034_ = lean_ctor_get(v_date_4656_, 16);
v_b_5035_ = lean_ctor_get(v_date_4656_, 17);
v_B_5036_ = lean_ctor_get(v_date_4656_, 18);
v_h_5037_ = lean_ctor_get(v_date_4656_, 19);
v_K_5038_ = lean_ctor_get(v_date_4656_, 20);
v_k_5039_ = lean_ctor_get(v_date_4656_, 21);
v_H_5040_ = lean_ctor_get(v_date_4656_, 22);
v_m_5041_ = lean_ctor_get(v_date_4656_, 23);
v_s_5042_ = lean_ctor_get(v_date_4656_, 24);
v_S_5043_ = lean_ctor_get(v_date_4656_, 25);
v_A_5044_ = lean_ctor_get(v_date_4656_, 26);
v_n_5045_ = lean_ctor_get(v_date_4656_, 27);
v_N_5046_ = lean_ctor_get(v_date_4656_, 28);
v_V_5047_ = lean_ctor_get(v_date_4656_, 29);
v_z_5048_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5049_ = lean_ctor_get(v_date_4656_, 31);
v_v_5050_ = lean_ctor_get(v_date_4656_, 32);
v_O_5051_ = lean_ctor_get(v_date_4656_, 33);
v_X_5052_ = lean_ctor_get(v_date_4656_, 34);
v_x_5053_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5054_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5064_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5064_ == 0)
{
lean_object* v_unused_5065_; 
v_unused_5065_ = lean_ctor_get(v_date_4656_, 8);
lean_dec(v_unused_5065_);
v___x_5056_ = v_date_4656_;
v_isShared_5057_ = v_isSharedCheck_5064_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_Z_5054_);
lean_inc(v_x_5053_);
lean_inc(v_X_5052_);
lean_inc(v_O_5051_);
lean_inc(v_v_5050_);
lean_inc(v_zabbrev_5049_);
lean_inc(v_z_5048_);
lean_inc(v_V_5047_);
lean_inc(v_N_5046_);
lean_inc(v_n_5045_);
lean_inc(v_A_5044_);
lean_inc(v_S_5043_);
lean_inc(v_s_5042_);
lean_inc(v_m_5041_);
lean_inc(v_H_5040_);
lean_inc(v_k_5039_);
lean_inc(v_K_5038_);
lean_inc(v_h_5037_);
lean_inc(v_B_5036_);
lean_inc(v_b_5035_);
lean_inc(v_a_5034_);
lean_inc(v_F_5033_);
lean_inc(v_c_5032_);
lean_inc(v_e_5031_);
lean_inc(v_E_5030_);
lean_inc(v_W_5029_);
lean_inc(v_w_5028_);
lean_inc(v_q_5027_);
lean_inc(v_d_5026_);
lean_inc(v_L_5025_);
lean_inc(v_M_5024_);
lean_inc(v_D_5023_);
lean_inc(v_Y_5022_);
lean_inc(v_u_5021_);
lean_inc(v_y_5020_);
lean_inc(v_G_5019_);
lean_dec(v_date_4656_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5064_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5059_; 
if (v_isShared_5018_ == 0)
{
lean_ctor_set_tag(v___x_5017_, 1);
lean_ctor_set(v___x_5017_, 0, v_data_4658_);
v___x_5059_ = v___x_5017_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_data_4658_);
v___x_5059_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
lean_object* v___x_5061_; 
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 8, v___x_5059_);
v___x_5061_ = v___x_5056_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_G_5019_);
lean_ctor_set(v_reuseFailAlloc_5062_, 1, v_y_5020_);
lean_ctor_set(v_reuseFailAlloc_5062_, 2, v_u_5021_);
lean_ctor_set(v_reuseFailAlloc_5062_, 3, v_Y_5022_);
lean_ctor_set(v_reuseFailAlloc_5062_, 4, v_D_5023_);
lean_ctor_set(v_reuseFailAlloc_5062_, 5, v_M_5024_);
lean_ctor_set(v_reuseFailAlloc_5062_, 6, v_L_5025_);
lean_ctor_set(v_reuseFailAlloc_5062_, 7, v_d_5026_);
lean_ctor_set(v_reuseFailAlloc_5062_, 8, v___x_5059_);
lean_ctor_set(v_reuseFailAlloc_5062_, 9, v_q_5027_);
lean_ctor_set(v_reuseFailAlloc_5062_, 10, v_w_5028_);
lean_ctor_set(v_reuseFailAlloc_5062_, 11, v_W_5029_);
lean_ctor_set(v_reuseFailAlloc_5062_, 12, v_E_5030_);
lean_ctor_set(v_reuseFailAlloc_5062_, 13, v_e_5031_);
lean_ctor_set(v_reuseFailAlloc_5062_, 14, v_c_5032_);
lean_ctor_set(v_reuseFailAlloc_5062_, 15, v_F_5033_);
lean_ctor_set(v_reuseFailAlloc_5062_, 16, v_a_5034_);
lean_ctor_set(v_reuseFailAlloc_5062_, 17, v_b_5035_);
lean_ctor_set(v_reuseFailAlloc_5062_, 18, v_B_5036_);
lean_ctor_set(v_reuseFailAlloc_5062_, 19, v_h_5037_);
lean_ctor_set(v_reuseFailAlloc_5062_, 20, v_K_5038_);
lean_ctor_set(v_reuseFailAlloc_5062_, 21, v_k_5039_);
lean_ctor_set(v_reuseFailAlloc_5062_, 22, v_H_5040_);
lean_ctor_set(v_reuseFailAlloc_5062_, 23, v_m_5041_);
lean_ctor_set(v_reuseFailAlloc_5062_, 24, v_s_5042_);
lean_ctor_set(v_reuseFailAlloc_5062_, 25, v_S_5043_);
lean_ctor_set(v_reuseFailAlloc_5062_, 26, v_A_5044_);
lean_ctor_set(v_reuseFailAlloc_5062_, 27, v_n_5045_);
lean_ctor_set(v_reuseFailAlloc_5062_, 28, v_N_5046_);
lean_ctor_set(v_reuseFailAlloc_5062_, 29, v_V_5047_);
lean_ctor_set(v_reuseFailAlloc_5062_, 30, v_z_5048_);
lean_ctor_set(v_reuseFailAlloc_5062_, 31, v_zabbrev_5049_);
lean_ctor_set(v_reuseFailAlloc_5062_, 32, v_v_5050_);
lean_ctor_set(v_reuseFailAlloc_5062_, 33, v_O_5051_);
lean_ctor_set(v_reuseFailAlloc_5062_, 34, v_X_5052_);
lean_ctor_set(v_reuseFailAlloc_5062_, 35, v_x_5053_);
lean_ctor_set(v_reuseFailAlloc_5062_, 36, v_Z_5054_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
}
}
case 8:
{
lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5118_; 
v_isSharedCheck_5118_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5118_ == 0)
{
lean_object* v_unused_5119_; 
v_unused_5119_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5119_);
v___x_5069_ = v_modifier_4657_;
v_isShared_5070_ = v_isSharedCheck_5118_;
goto v_resetjp_5068_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5118_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v_G_5071_; lean_object* v_y_5072_; lean_object* v_u_5073_; lean_object* v_Y_5074_; lean_object* v_D_5075_; lean_object* v_M_5076_; lean_object* v_L_5077_; lean_object* v_d_5078_; lean_object* v_Q_5079_; lean_object* v_w_5080_; lean_object* v_W_5081_; lean_object* v_E_5082_; lean_object* v_e_5083_; lean_object* v_c_5084_; lean_object* v_F_5085_; lean_object* v_a_5086_; lean_object* v_b_5087_; lean_object* v_B_5088_; lean_object* v_h_5089_; lean_object* v_K_5090_; lean_object* v_k_5091_; lean_object* v_H_5092_; lean_object* v_m_5093_; lean_object* v_s_5094_; lean_object* v_S_5095_; lean_object* v_A_5096_; lean_object* v_n_5097_; lean_object* v_N_5098_; lean_object* v_V_5099_; lean_object* v_z_5100_; lean_object* v_zabbrev_5101_; lean_object* v_v_5102_; lean_object* v_O_5103_; lean_object* v_X_5104_; lean_object* v_x_5105_; lean_object* v_Z_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5116_; 
v_G_5071_ = lean_ctor_get(v_date_4656_, 0);
v_y_5072_ = lean_ctor_get(v_date_4656_, 1);
v_u_5073_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5074_ = lean_ctor_get(v_date_4656_, 3);
v_D_5075_ = lean_ctor_get(v_date_4656_, 4);
v_M_5076_ = lean_ctor_get(v_date_4656_, 5);
v_L_5077_ = lean_ctor_get(v_date_4656_, 6);
v_d_5078_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5079_ = lean_ctor_get(v_date_4656_, 8);
v_w_5080_ = lean_ctor_get(v_date_4656_, 10);
v_W_5081_ = lean_ctor_get(v_date_4656_, 11);
v_E_5082_ = lean_ctor_get(v_date_4656_, 12);
v_e_5083_ = lean_ctor_get(v_date_4656_, 13);
v_c_5084_ = lean_ctor_get(v_date_4656_, 14);
v_F_5085_ = lean_ctor_get(v_date_4656_, 15);
v_a_5086_ = lean_ctor_get(v_date_4656_, 16);
v_b_5087_ = lean_ctor_get(v_date_4656_, 17);
v_B_5088_ = lean_ctor_get(v_date_4656_, 18);
v_h_5089_ = lean_ctor_get(v_date_4656_, 19);
v_K_5090_ = lean_ctor_get(v_date_4656_, 20);
v_k_5091_ = lean_ctor_get(v_date_4656_, 21);
v_H_5092_ = lean_ctor_get(v_date_4656_, 22);
v_m_5093_ = lean_ctor_get(v_date_4656_, 23);
v_s_5094_ = lean_ctor_get(v_date_4656_, 24);
v_S_5095_ = lean_ctor_get(v_date_4656_, 25);
v_A_5096_ = lean_ctor_get(v_date_4656_, 26);
v_n_5097_ = lean_ctor_get(v_date_4656_, 27);
v_N_5098_ = lean_ctor_get(v_date_4656_, 28);
v_V_5099_ = lean_ctor_get(v_date_4656_, 29);
v_z_5100_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5101_ = lean_ctor_get(v_date_4656_, 31);
v_v_5102_ = lean_ctor_get(v_date_4656_, 32);
v_O_5103_ = lean_ctor_get(v_date_4656_, 33);
v_X_5104_ = lean_ctor_get(v_date_4656_, 34);
v_x_5105_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5106_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5116_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5116_ == 0)
{
lean_object* v_unused_5117_; 
v_unused_5117_ = lean_ctor_get(v_date_4656_, 9);
lean_dec(v_unused_5117_);
v___x_5108_ = v_date_4656_;
v_isShared_5109_ = v_isSharedCheck_5116_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_Z_5106_);
lean_inc(v_x_5105_);
lean_inc(v_X_5104_);
lean_inc(v_O_5103_);
lean_inc(v_v_5102_);
lean_inc(v_zabbrev_5101_);
lean_inc(v_z_5100_);
lean_inc(v_V_5099_);
lean_inc(v_N_5098_);
lean_inc(v_n_5097_);
lean_inc(v_A_5096_);
lean_inc(v_S_5095_);
lean_inc(v_s_5094_);
lean_inc(v_m_5093_);
lean_inc(v_H_5092_);
lean_inc(v_k_5091_);
lean_inc(v_K_5090_);
lean_inc(v_h_5089_);
lean_inc(v_B_5088_);
lean_inc(v_b_5087_);
lean_inc(v_a_5086_);
lean_inc(v_F_5085_);
lean_inc(v_c_5084_);
lean_inc(v_e_5083_);
lean_inc(v_E_5082_);
lean_inc(v_W_5081_);
lean_inc(v_w_5080_);
lean_inc(v_Q_5079_);
lean_inc(v_d_5078_);
lean_inc(v_L_5077_);
lean_inc(v_M_5076_);
lean_inc(v_D_5075_);
lean_inc(v_Y_5074_);
lean_inc(v_u_5073_);
lean_inc(v_y_5072_);
lean_inc(v_G_5071_);
lean_dec(v_date_4656_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5116_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5111_; 
if (v_isShared_5070_ == 0)
{
lean_ctor_set_tag(v___x_5069_, 1);
lean_ctor_set(v___x_5069_, 0, v_data_4658_);
v___x_5111_ = v___x_5069_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_data_4658_);
v___x_5111_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
lean_object* v___x_5113_; 
if (v_isShared_5109_ == 0)
{
lean_ctor_set(v___x_5108_, 9, v___x_5111_);
v___x_5113_ = v___x_5108_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_G_5071_);
lean_ctor_set(v_reuseFailAlloc_5114_, 1, v_y_5072_);
lean_ctor_set(v_reuseFailAlloc_5114_, 2, v_u_5073_);
lean_ctor_set(v_reuseFailAlloc_5114_, 3, v_Y_5074_);
lean_ctor_set(v_reuseFailAlloc_5114_, 4, v_D_5075_);
lean_ctor_set(v_reuseFailAlloc_5114_, 5, v_M_5076_);
lean_ctor_set(v_reuseFailAlloc_5114_, 6, v_L_5077_);
lean_ctor_set(v_reuseFailAlloc_5114_, 7, v_d_5078_);
lean_ctor_set(v_reuseFailAlloc_5114_, 8, v_Q_5079_);
lean_ctor_set(v_reuseFailAlloc_5114_, 9, v___x_5111_);
lean_ctor_set(v_reuseFailAlloc_5114_, 10, v_w_5080_);
lean_ctor_set(v_reuseFailAlloc_5114_, 11, v_W_5081_);
lean_ctor_set(v_reuseFailAlloc_5114_, 12, v_E_5082_);
lean_ctor_set(v_reuseFailAlloc_5114_, 13, v_e_5083_);
lean_ctor_set(v_reuseFailAlloc_5114_, 14, v_c_5084_);
lean_ctor_set(v_reuseFailAlloc_5114_, 15, v_F_5085_);
lean_ctor_set(v_reuseFailAlloc_5114_, 16, v_a_5086_);
lean_ctor_set(v_reuseFailAlloc_5114_, 17, v_b_5087_);
lean_ctor_set(v_reuseFailAlloc_5114_, 18, v_B_5088_);
lean_ctor_set(v_reuseFailAlloc_5114_, 19, v_h_5089_);
lean_ctor_set(v_reuseFailAlloc_5114_, 20, v_K_5090_);
lean_ctor_set(v_reuseFailAlloc_5114_, 21, v_k_5091_);
lean_ctor_set(v_reuseFailAlloc_5114_, 22, v_H_5092_);
lean_ctor_set(v_reuseFailAlloc_5114_, 23, v_m_5093_);
lean_ctor_set(v_reuseFailAlloc_5114_, 24, v_s_5094_);
lean_ctor_set(v_reuseFailAlloc_5114_, 25, v_S_5095_);
lean_ctor_set(v_reuseFailAlloc_5114_, 26, v_A_5096_);
lean_ctor_set(v_reuseFailAlloc_5114_, 27, v_n_5097_);
lean_ctor_set(v_reuseFailAlloc_5114_, 28, v_N_5098_);
lean_ctor_set(v_reuseFailAlloc_5114_, 29, v_V_5099_);
lean_ctor_set(v_reuseFailAlloc_5114_, 30, v_z_5100_);
lean_ctor_set(v_reuseFailAlloc_5114_, 31, v_zabbrev_5101_);
lean_ctor_set(v_reuseFailAlloc_5114_, 32, v_v_5102_);
lean_ctor_set(v_reuseFailAlloc_5114_, 33, v_O_5103_);
lean_ctor_set(v_reuseFailAlloc_5114_, 34, v_X_5104_);
lean_ctor_set(v_reuseFailAlloc_5114_, 35, v_x_5105_);
lean_ctor_set(v_reuseFailAlloc_5114_, 36, v_Z_5106_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
return v___x_5113_;
}
}
}
}
}
case 9:
{
lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5170_; 
v_isSharedCheck_5170_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5170_ == 0)
{
lean_object* v_unused_5171_; 
v_unused_5171_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5171_);
v___x_5121_ = v_modifier_4657_;
v_isShared_5122_ = v_isSharedCheck_5170_;
goto v_resetjp_5120_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5170_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v_G_5123_; lean_object* v_y_5124_; lean_object* v_u_5125_; lean_object* v_D_5126_; lean_object* v_M_5127_; lean_object* v_L_5128_; lean_object* v_d_5129_; lean_object* v_Q_5130_; lean_object* v_q_5131_; lean_object* v_w_5132_; lean_object* v_W_5133_; lean_object* v_E_5134_; lean_object* v_e_5135_; lean_object* v_c_5136_; lean_object* v_F_5137_; lean_object* v_a_5138_; lean_object* v_b_5139_; lean_object* v_B_5140_; lean_object* v_h_5141_; lean_object* v_K_5142_; lean_object* v_k_5143_; lean_object* v_H_5144_; lean_object* v_m_5145_; lean_object* v_s_5146_; lean_object* v_S_5147_; lean_object* v_A_5148_; lean_object* v_n_5149_; lean_object* v_N_5150_; lean_object* v_V_5151_; lean_object* v_z_5152_; lean_object* v_zabbrev_5153_; lean_object* v_v_5154_; lean_object* v_O_5155_; lean_object* v_X_5156_; lean_object* v_x_5157_; lean_object* v_Z_5158_; lean_object* v___x_5160_; uint8_t v_isShared_5161_; uint8_t v_isSharedCheck_5168_; 
v_G_5123_ = lean_ctor_get(v_date_4656_, 0);
v_y_5124_ = lean_ctor_get(v_date_4656_, 1);
v_u_5125_ = lean_ctor_get(v_date_4656_, 2);
v_D_5126_ = lean_ctor_get(v_date_4656_, 4);
v_M_5127_ = lean_ctor_get(v_date_4656_, 5);
v_L_5128_ = lean_ctor_get(v_date_4656_, 6);
v_d_5129_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5130_ = lean_ctor_get(v_date_4656_, 8);
v_q_5131_ = lean_ctor_get(v_date_4656_, 9);
v_w_5132_ = lean_ctor_get(v_date_4656_, 10);
v_W_5133_ = lean_ctor_get(v_date_4656_, 11);
v_E_5134_ = lean_ctor_get(v_date_4656_, 12);
v_e_5135_ = lean_ctor_get(v_date_4656_, 13);
v_c_5136_ = lean_ctor_get(v_date_4656_, 14);
v_F_5137_ = lean_ctor_get(v_date_4656_, 15);
v_a_5138_ = lean_ctor_get(v_date_4656_, 16);
v_b_5139_ = lean_ctor_get(v_date_4656_, 17);
v_B_5140_ = lean_ctor_get(v_date_4656_, 18);
v_h_5141_ = lean_ctor_get(v_date_4656_, 19);
v_K_5142_ = lean_ctor_get(v_date_4656_, 20);
v_k_5143_ = lean_ctor_get(v_date_4656_, 21);
v_H_5144_ = lean_ctor_get(v_date_4656_, 22);
v_m_5145_ = lean_ctor_get(v_date_4656_, 23);
v_s_5146_ = lean_ctor_get(v_date_4656_, 24);
v_S_5147_ = lean_ctor_get(v_date_4656_, 25);
v_A_5148_ = lean_ctor_get(v_date_4656_, 26);
v_n_5149_ = lean_ctor_get(v_date_4656_, 27);
v_N_5150_ = lean_ctor_get(v_date_4656_, 28);
v_V_5151_ = lean_ctor_get(v_date_4656_, 29);
v_z_5152_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5153_ = lean_ctor_get(v_date_4656_, 31);
v_v_5154_ = lean_ctor_get(v_date_4656_, 32);
v_O_5155_ = lean_ctor_get(v_date_4656_, 33);
v_X_5156_ = lean_ctor_get(v_date_4656_, 34);
v_x_5157_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5158_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5168_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5168_ == 0)
{
lean_object* v_unused_5169_; 
v_unused_5169_ = lean_ctor_get(v_date_4656_, 3);
lean_dec(v_unused_5169_);
v___x_5160_ = v_date_4656_;
v_isShared_5161_ = v_isSharedCheck_5168_;
goto v_resetjp_5159_;
}
else
{
lean_inc(v_Z_5158_);
lean_inc(v_x_5157_);
lean_inc(v_X_5156_);
lean_inc(v_O_5155_);
lean_inc(v_v_5154_);
lean_inc(v_zabbrev_5153_);
lean_inc(v_z_5152_);
lean_inc(v_V_5151_);
lean_inc(v_N_5150_);
lean_inc(v_n_5149_);
lean_inc(v_A_5148_);
lean_inc(v_S_5147_);
lean_inc(v_s_5146_);
lean_inc(v_m_5145_);
lean_inc(v_H_5144_);
lean_inc(v_k_5143_);
lean_inc(v_K_5142_);
lean_inc(v_h_5141_);
lean_inc(v_B_5140_);
lean_inc(v_b_5139_);
lean_inc(v_a_5138_);
lean_inc(v_F_5137_);
lean_inc(v_c_5136_);
lean_inc(v_e_5135_);
lean_inc(v_E_5134_);
lean_inc(v_W_5133_);
lean_inc(v_w_5132_);
lean_inc(v_q_5131_);
lean_inc(v_Q_5130_);
lean_inc(v_d_5129_);
lean_inc(v_L_5128_);
lean_inc(v_M_5127_);
lean_inc(v_D_5126_);
lean_inc(v_u_5125_);
lean_inc(v_y_5124_);
lean_inc(v_G_5123_);
lean_dec(v_date_4656_);
v___x_5160_ = lean_box(0);
v_isShared_5161_ = v_isSharedCheck_5168_;
goto v_resetjp_5159_;
}
v_resetjp_5159_:
{
lean_object* v___x_5163_; 
if (v_isShared_5122_ == 0)
{
lean_ctor_set_tag(v___x_5121_, 1);
lean_ctor_set(v___x_5121_, 0, v_data_4658_);
v___x_5163_ = v___x_5121_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_data_4658_);
v___x_5163_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
lean_object* v___x_5165_; 
if (v_isShared_5161_ == 0)
{
lean_ctor_set(v___x_5160_, 3, v___x_5163_);
v___x_5165_ = v___x_5160_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v_G_5123_);
lean_ctor_set(v_reuseFailAlloc_5166_, 1, v_y_5124_);
lean_ctor_set(v_reuseFailAlloc_5166_, 2, v_u_5125_);
lean_ctor_set(v_reuseFailAlloc_5166_, 3, v___x_5163_);
lean_ctor_set(v_reuseFailAlloc_5166_, 4, v_D_5126_);
lean_ctor_set(v_reuseFailAlloc_5166_, 5, v_M_5127_);
lean_ctor_set(v_reuseFailAlloc_5166_, 6, v_L_5128_);
lean_ctor_set(v_reuseFailAlloc_5166_, 7, v_d_5129_);
lean_ctor_set(v_reuseFailAlloc_5166_, 8, v_Q_5130_);
lean_ctor_set(v_reuseFailAlloc_5166_, 9, v_q_5131_);
lean_ctor_set(v_reuseFailAlloc_5166_, 10, v_w_5132_);
lean_ctor_set(v_reuseFailAlloc_5166_, 11, v_W_5133_);
lean_ctor_set(v_reuseFailAlloc_5166_, 12, v_E_5134_);
lean_ctor_set(v_reuseFailAlloc_5166_, 13, v_e_5135_);
lean_ctor_set(v_reuseFailAlloc_5166_, 14, v_c_5136_);
lean_ctor_set(v_reuseFailAlloc_5166_, 15, v_F_5137_);
lean_ctor_set(v_reuseFailAlloc_5166_, 16, v_a_5138_);
lean_ctor_set(v_reuseFailAlloc_5166_, 17, v_b_5139_);
lean_ctor_set(v_reuseFailAlloc_5166_, 18, v_B_5140_);
lean_ctor_set(v_reuseFailAlloc_5166_, 19, v_h_5141_);
lean_ctor_set(v_reuseFailAlloc_5166_, 20, v_K_5142_);
lean_ctor_set(v_reuseFailAlloc_5166_, 21, v_k_5143_);
lean_ctor_set(v_reuseFailAlloc_5166_, 22, v_H_5144_);
lean_ctor_set(v_reuseFailAlloc_5166_, 23, v_m_5145_);
lean_ctor_set(v_reuseFailAlloc_5166_, 24, v_s_5146_);
lean_ctor_set(v_reuseFailAlloc_5166_, 25, v_S_5147_);
lean_ctor_set(v_reuseFailAlloc_5166_, 26, v_A_5148_);
lean_ctor_set(v_reuseFailAlloc_5166_, 27, v_n_5149_);
lean_ctor_set(v_reuseFailAlloc_5166_, 28, v_N_5150_);
lean_ctor_set(v_reuseFailAlloc_5166_, 29, v_V_5151_);
lean_ctor_set(v_reuseFailAlloc_5166_, 30, v_z_5152_);
lean_ctor_set(v_reuseFailAlloc_5166_, 31, v_zabbrev_5153_);
lean_ctor_set(v_reuseFailAlloc_5166_, 32, v_v_5154_);
lean_ctor_set(v_reuseFailAlloc_5166_, 33, v_O_5155_);
lean_ctor_set(v_reuseFailAlloc_5166_, 34, v_X_5156_);
lean_ctor_set(v_reuseFailAlloc_5166_, 35, v_x_5157_);
lean_ctor_set(v_reuseFailAlloc_5166_, 36, v_Z_5158_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
}
}
}
case 10:
{
lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5222_; 
v_isSharedCheck_5222_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5222_ == 0)
{
lean_object* v_unused_5223_; 
v_unused_5223_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5223_);
v___x_5173_ = v_modifier_4657_;
v_isShared_5174_ = v_isSharedCheck_5222_;
goto v_resetjp_5172_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5222_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v_G_5175_; lean_object* v_y_5176_; lean_object* v_u_5177_; lean_object* v_Y_5178_; lean_object* v_D_5179_; lean_object* v_M_5180_; lean_object* v_L_5181_; lean_object* v_d_5182_; lean_object* v_Q_5183_; lean_object* v_q_5184_; lean_object* v_W_5185_; lean_object* v_E_5186_; lean_object* v_e_5187_; lean_object* v_c_5188_; lean_object* v_F_5189_; lean_object* v_a_5190_; lean_object* v_b_5191_; lean_object* v_B_5192_; lean_object* v_h_5193_; lean_object* v_K_5194_; lean_object* v_k_5195_; lean_object* v_H_5196_; lean_object* v_m_5197_; lean_object* v_s_5198_; lean_object* v_S_5199_; lean_object* v_A_5200_; lean_object* v_n_5201_; lean_object* v_N_5202_; lean_object* v_V_5203_; lean_object* v_z_5204_; lean_object* v_zabbrev_5205_; lean_object* v_v_5206_; lean_object* v_O_5207_; lean_object* v_X_5208_; lean_object* v_x_5209_; lean_object* v_Z_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5220_; 
v_G_5175_ = lean_ctor_get(v_date_4656_, 0);
v_y_5176_ = lean_ctor_get(v_date_4656_, 1);
v_u_5177_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5178_ = lean_ctor_get(v_date_4656_, 3);
v_D_5179_ = lean_ctor_get(v_date_4656_, 4);
v_M_5180_ = lean_ctor_get(v_date_4656_, 5);
v_L_5181_ = lean_ctor_get(v_date_4656_, 6);
v_d_5182_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5183_ = lean_ctor_get(v_date_4656_, 8);
v_q_5184_ = lean_ctor_get(v_date_4656_, 9);
v_W_5185_ = lean_ctor_get(v_date_4656_, 11);
v_E_5186_ = lean_ctor_get(v_date_4656_, 12);
v_e_5187_ = lean_ctor_get(v_date_4656_, 13);
v_c_5188_ = lean_ctor_get(v_date_4656_, 14);
v_F_5189_ = lean_ctor_get(v_date_4656_, 15);
v_a_5190_ = lean_ctor_get(v_date_4656_, 16);
v_b_5191_ = lean_ctor_get(v_date_4656_, 17);
v_B_5192_ = lean_ctor_get(v_date_4656_, 18);
v_h_5193_ = lean_ctor_get(v_date_4656_, 19);
v_K_5194_ = lean_ctor_get(v_date_4656_, 20);
v_k_5195_ = lean_ctor_get(v_date_4656_, 21);
v_H_5196_ = lean_ctor_get(v_date_4656_, 22);
v_m_5197_ = lean_ctor_get(v_date_4656_, 23);
v_s_5198_ = lean_ctor_get(v_date_4656_, 24);
v_S_5199_ = lean_ctor_get(v_date_4656_, 25);
v_A_5200_ = lean_ctor_get(v_date_4656_, 26);
v_n_5201_ = lean_ctor_get(v_date_4656_, 27);
v_N_5202_ = lean_ctor_get(v_date_4656_, 28);
v_V_5203_ = lean_ctor_get(v_date_4656_, 29);
v_z_5204_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5205_ = lean_ctor_get(v_date_4656_, 31);
v_v_5206_ = lean_ctor_get(v_date_4656_, 32);
v_O_5207_ = lean_ctor_get(v_date_4656_, 33);
v_X_5208_ = lean_ctor_get(v_date_4656_, 34);
v_x_5209_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5210_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5220_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5220_ == 0)
{
lean_object* v_unused_5221_; 
v_unused_5221_ = lean_ctor_get(v_date_4656_, 10);
lean_dec(v_unused_5221_);
v___x_5212_ = v_date_4656_;
v_isShared_5213_ = v_isSharedCheck_5220_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_Z_5210_);
lean_inc(v_x_5209_);
lean_inc(v_X_5208_);
lean_inc(v_O_5207_);
lean_inc(v_v_5206_);
lean_inc(v_zabbrev_5205_);
lean_inc(v_z_5204_);
lean_inc(v_V_5203_);
lean_inc(v_N_5202_);
lean_inc(v_n_5201_);
lean_inc(v_A_5200_);
lean_inc(v_S_5199_);
lean_inc(v_s_5198_);
lean_inc(v_m_5197_);
lean_inc(v_H_5196_);
lean_inc(v_k_5195_);
lean_inc(v_K_5194_);
lean_inc(v_h_5193_);
lean_inc(v_B_5192_);
lean_inc(v_b_5191_);
lean_inc(v_a_5190_);
lean_inc(v_F_5189_);
lean_inc(v_c_5188_);
lean_inc(v_e_5187_);
lean_inc(v_E_5186_);
lean_inc(v_W_5185_);
lean_inc(v_q_5184_);
lean_inc(v_Q_5183_);
lean_inc(v_d_5182_);
lean_inc(v_L_5181_);
lean_inc(v_M_5180_);
lean_inc(v_D_5179_);
lean_inc(v_Y_5178_);
lean_inc(v_u_5177_);
lean_inc(v_y_5176_);
lean_inc(v_G_5175_);
lean_dec(v_date_4656_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5220_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5174_ == 0)
{
lean_ctor_set_tag(v___x_5173_, 1);
lean_ctor_set(v___x_5173_, 0, v_data_4658_);
v___x_5215_ = v___x_5173_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_data_4658_);
v___x_5215_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
lean_object* v___x_5217_; 
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 10, v___x_5215_);
v___x_5217_ = v___x_5212_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_G_5175_);
lean_ctor_set(v_reuseFailAlloc_5218_, 1, v_y_5176_);
lean_ctor_set(v_reuseFailAlloc_5218_, 2, v_u_5177_);
lean_ctor_set(v_reuseFailAlloc_5218_, 3, v_Y_5178_);
lean_ctor_set(v_reuseFailAlloc_5218_, 4, v_D_5179_);
lean_ctor_set(v_reuseFailAlloc_5218_, 5, v_M_5180_);
lean_ctor_set(v_reuseFailAlloc_5218_, 6, v_L_5181_);
lean_ctor_set(v_reuseFailAlloc_5218_, 7, v_d_5182_);
lean_ctor_set(v_reuseFailAlloc_5218_, 8, v_Q_5183_);
lean_ctor_set(v_reuseFailAlloc_5218_, 9, v_q_5184_);
lean_ctor_set(v_reuseFailAlloc_5218_, 10, v___x_5215_);
lean_ctor_set(v_reuseFailAlloc_5218_, 11, v_W_5185_);
lean_ctor_set(v_reuseFailAlloc_5218_, 12, v_E_5186_);
lean_ctor_set(v_reuseFailAlloc_5218_, 13, v_e_5187_);
lean_ctor_set(v_reuseFailAlloc_5218_, 14, v_c_5188_);
lean_ctor_set(v_reuseFailAlloc_5218_, 15, v_F_5189_);
lean_ctor_set(v_reuseFailAlloc_5218_, 16, v_a_5190_);
lean_ctor_set(v_reuseFailAlloc_5218_, 17, v_b_5191_);
lean_ctor_set(v_reuseFailAlloc_5218_, 18, v_B_5192_);
lean_ctor_set(v_reuseFailAlloc_5218_, 19, v_h_5193_);
lean_ctor_set(v_reuseFailAlloc_5218_, 20, v_K_5194_);
lean_ctor_set(v_reuseFailAlloc_5218_, 21, v_k_5195_);
lean_ctor_set(v_reuseFailAlloc_5218_, 22, v_H_5196_);
lean_ctor_set(v_reuseFailAlloc_5218_, 23, v_m_5197_);
lean_ctor_set(v_reuseFailAlloc_5218_, 24, v_s_5198_);
lean_ctor_set(v_reuseFailAlloc_5218_, 25, v_S_5199_);
lean_ctor_set(v_reuseFailAlloc_5218_, 26, v_A_5200_);
lean_ctor_set(v_reuseFailAlloc_5218_, 27, v_n_5201_);
lean_ctor_set(v_reuseFailAlloc_5218_, 28, v_N_5202_);
lean_ctor_set(v_reuseFailAlloc_5218_, 29, v_V_5203_);
lean_ctor_set(v_reuseFailAlloc_5218_, 30, v_z_5204_);
lean_ctor_set(v_reuseFailAlloc_5218_, 31, v_zabbrev_5205_);
lean_ctor_set(v_reuseFailAlloc_5218_, 32, v_v_5206_);
lean_ctor_set(v_reuseFailAlloc_5218_, 33, v_O_5207_);
lean_ctor_set(v_reuseFailAlloc_5218_, 34, v_X_5208_);
lean_ctor_set(v_reuseFailAlloc_5218_, 35, v_x_5209_);
lean_ctor_set(v_reuseFailAlloc_5218_, 36, v_Z_5210_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
}
}
case 11:
{
lean_object* v___x_5225_; uint8_t v_isShared_5226_; uint8_t v_isSharedCheck_5274_; 
v_isSharedCheck_5274_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5274_ == 0)
{
lean_object* v_unused_5275_; 
v_unused_5275_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5275_);
v___x_5225_ = v_modifier_4657_;
v_isShared_5226_ = v_isSharedCheck_5274_;
goto v_resetjp_5224_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5225_ = lean_box(0);
v_isShared_5226_ = v_isSharedCheck_5274_;
goto v_resetjp_5224_;
}
v_resetjp_5224_:
{
lean_object* v_G_5227_; lean_object* v_y_5228_; lean_object* v_u_5229_; lean_object* v_Y_5230_; lean_object* v_D_5231_; lean_object* v_M_5232_; lean_object* v_L_5233_; lean_object* v_d_5234_; lean_object* v_Q_5235_; lean_object* v_q_5236_; lean_object* v_w_5237_; lean_object* v_E_5238_; lean_object* v_e_5239_; lean_object* v_c_5240_; lean_object* v_F_5241_; lean_object* v_a_5242_; lean_object* v_b_5243_; lean_object* v_B_5244_; lean_object* v_h_5245_; lean_object* v_K_5246_; lean_object* v_k_5247_; lean_object* v_H_5248_; lean_object* v_m_5249_; lean_object* v_s_5250_; lean_object* v_S_5251_; lean_object* v_A_5252_; lean_object* v_n_5253_; lean_object* v_N_5254_; lean_object* v_V_5255_; lean_object* v_z_5256_; lean_object* v_zabbrev_5257_; lean_object* v_v_5258_; lean_object* v_O_5259_; lean_object* v_X_5260_; lean_object* v_x_5261_; lean_object* v_Z_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5272_; 
v_G_5227_ = lean_ctor_get(v_date_4656_, 0);
v_y_5228_ = lean_ctor_get(v_date_4656_, 1);
v_u_5229_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5230_ = lean_ctor_get(v_date_4656_, 3);
v_D_5231_ = lean_ctor_get(v_date_4656_, 4);
v_M_5232_ = lean_ctor_get(v_date_4656_, 5);
v_L_5233_ = lean_ctor_get(v_date_4656_, 6);
v_d_5234_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5235_ = lean_ctor_get(v_date_4656_, 8);
v_q_5236_ = lean_ctor_get(v_date_4656_, 9);
v_w_5237_ = lean_ctor_get(v_date_4656_, 10);
v_E_5238_ = lean_ctor_get(v_date_4656_, 12);
v_e_5239_ = lean_ctor_get(v_date_4656_, 13);
v_c_5240_ = lean_ctor_get(v_date_4656_, 14);
v_F_5241_ = lean_ctor_get(v_date_4656_, 15);
v_a_5242_ = lean_ctor_get(v_date_4656_, 16);
v_b_5243_ = lean_ctor_get(v_date_4656_, 17);
v_B_5244_ = lean_ctor_get(v_date_4656_, 18);
v_h_5245_ = lean_ctor_get(v_date_4656_, 19);
v_K_5246_ = lean_ctor_get(v_date_4656_, 20);
v_k_5247_ = lean_ctor_get(v_date_4656_, 21);
v_H_5248_ = lean_ctor_get(v_date_4656_, 22);
v_m_5249_ = lean_ctor_get(v_date_4656_, 23);
v_s_5250_ = lean_ctor_get(v_date_4656_, 24);
v_S_5251_ = lean_ctor_get(v_date_4656_, 25);
v_A_5252_ = lean_ctor_get(v_date_4656_, 26);
v_n_5253_ = lean_ctor_get(v_date_4656_, 27);
v_N_5254_ = lean_ctor_get(v_date_4656_, 28);
v_V_5255_ = lean_ctor_get(v_date_4656_, 29);
v_z_5256_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5257_ = lean_ctor_get(v_date_4656_, 31);
v_v_5258_ = lean_ctor_get(v_date_4656_, 32);
v_O_5259_ = lean_ctor_get(v_date_4656_, 33);
v_X_5260_ = lean_ctor_get(v_date_4656_, 34);
v_x_5261_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5262_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5272_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5272_ == 0)
{
lean_object* v_unused_5273_; 
v_unused_5273_ = lean_ctor_get(v_date_4656_, 11);
lean_dec(v_unused_5273_);
v___x_5264_ = v_date_4656_;
v_isShared_5265_ = v_isSharedCheck_5272_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_Z_5262_);
lean_inc(v_x_5261_);
lean_inc(v_X_5260_);
lean_inc(v_O_5259_);
lean_inc(v_v_5258_);
lean_inc(v_zabbrev_5257_);
lean_inc(v_z_5256_);
lean_inc(v_V_5255_);
lean_inc(v_N_5254_);
lean_inc(v_n_5253_);
lean_inc(v_A_5252_);
lean_inc(v_S_5251_);
lean_inc(v_s_5250_);
lean_inc(v_m_5249_);
lean_inc(v_H_5248_);
lean_inc(v_k_5247_);
lean_inc(v_K_5246_);
lean_inc(v_h_5245_);
lean_inc(v_B_5244_);
lean_inc(v_b_5243_);
lean_inc(v_a_5242_);
lean_inc(v_F_5241_);
lean_inc(v_c_5240_);
lean_inc(v_e_5239_);
lean_inc(v_E_5238_);
lean_inc(v_w_5237_);
lean_inc(v_q_5236_);
lean_inc(v_Q_5235_);
lean_inc(v_d_5234_);
lean_inc(v_L_5233_);
lean_inc(v_M_5232_);
lean_inc(v_D_5231_);
lean_inc(v_Y_5230_);
lean_inc(v_u_5229_);
lean_inc(v_y_5228_);
lean_inc(v_G_5227_);
lean_dec(v_date_4656_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5272_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5267_; 
if (v_isShared_5226_ == 0)
{
lean_ctor_set_tag(v___x_5225_, 1);
lean_ctor_set(v___x_5225_, 0, v_data_4658_);
v___x_5267_ = v___x_5225_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_data_4658_);
v___x_5267_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
lean_object* v___x_5269_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 11, v___x_5267_);
v___x_5269_ = v___x_5264_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5270_; 
v_reuseFailAlloc_5270_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5270_, 0, v_G_5227_);
lean_ctor_set(v_reuseFailAlloc_5270_, 1, v_y_5228_);
lean_ctor_set(v_reuseFailAlloc_5270_, 2, v_u_5229_);
lean_ctor_set(v_reuseFailAlloc_5270_, 3, v_Y_5230_);
lean_ctor_set(v_reuseFailAlloc_5270_, 4, v_D_5231_);
lean_ctor_set(v_reuseFailAlloc_5270_, 5, v_M_5232_);
lean_ctor_set(v_reuseFailAlloc_5270_, 6, v_L_5233_);
lean_ctor_set(v_reuseFailAlloc_5270_, 7, v_d_5234_);
lean_ctor_set(v_reuseFailAlloc_5270_, 8, v_Q_5235_);
lean_ctor_set(v_reuseFailAlloc_5270_, 9, v_q_5236_);
lean_ctor_set(v_reuseFailAlloc_5270_, 10, v_w_5237_);
lean_ctor_set(v_reuseFailAlloc_5270_, 11, v___x_5267_);
lean_ctor_set(v_reuseFailAlloc_5270_, 12, v_E_5238_);
lean_ctor_set(v_reuseFailAlloc_5270_, 13, v_e_5239_);
lean_ctor_set(v_reuseFailAlloc_5270_, 14, v_c_5240_);
lean_ctor_set(v_reuseFailAlloc_5270_, 15, v_F_5241_);
lean_ctor_set(v_reuseFailAlloc_5270_, 16, v_a_5242_);
lean_ctor_set(v_reuseFailAlloc_5270_, 17, v_b_5243_);
lean_ctor_set(v_reuseFailAlloc_5270_, 18, v_B_5244_);
lean_ctor_set(v_reuseFailAlloc_5270_, 19, v_h_5245_);
lean_ctor_set(v_reuseFailAlloc_5270_, 20, v_K_5246_);
lean_ctor_set(v_reuseFailAlloc_5270_, 21, v_k_5247_);
lean_ctor_set(v_reuseFailAlloc_5270_, 22, v_H_5248_);
lean_ctor_set(v_reuseFailAlloc_5270_, 23, v_m_5249_);
lean_ctor_set(v_reuseFailAlloc_5270_, 24, v_s_5250_);
lean_ctor_set(v_reuseFailAlloc_5270_, 25, v_S_5251_);
lean_ctor_set(v_reuseFailAlloc_5270_, 26, v_A_5252_);
lean_ctor_set(v_reuseFailAlloc_5270_, 27, v_n_5253_);
lean_ctor_set(v_reuseFailAlloc_5270_, 28, v_N_5254_);
lean_ctor_set(v_reuseFailAlloc_5270_, 29, v_V_5255_);
lean_ctor_set(v_reuseFailAlloc_5270_, 30, v_z_5256_);
lean_ctor_set(v_reuseFailAlloc_5270_, 31, v_zabbrev_5257_);
lean_ctor_set(v_reuseFailAlloc_5270_, 32, v_v_5258_);
lean_ctor_set(v_reuseFailAlloc_5270_, 33, v_O_5259_);
lean_ctor_set(v_reuseFailAlloc_5270_, 34, v_X_5260_);
lean_ctor_set(v_reuseFailAlloc_5270_, 35, v_x_5261_);
lean_ctor_set(v_reuseFailAlloc_5270_, 36, v_Z_5262_);
v___x_5269_ = v_reuseFailAlloc_5270_;
goto v_reusejp_5268_;
}
v_reusejp_5268_:
{
return v___x_5269_;
}
}
}
}
}
case 12:
{
lean_object* v_G_5276_; lean_object* v_y_5277_; lean_object* v_u_5278_; lean_object* v_Y_5279_; lean_object* v_D_5280_; lean_object* v_M_5281_; lean_object* v_L_5282_; lean_object* v_d_5283_; lean_object* v_Q_5284_; lean_object* v_q_5285_; lean_object* v_w_5286_; lean_object* v_W_5287_; lean_object* v_e_5288_; lean_object* v_c_5289_; lean_object* v_F_5290_; lean_object* v_a_5291_; lean_object* v_b_5292_; lean_object* v_B_5293_; lean_object* v_h_5294_; lean_object* v_K_5295_; lean_object* v_k_5296_; lean_object* v_H_5297_; lean_object* v_m_5298_; lean_object* v_s_5299_; lean_object* v_S_5300_; lean_object* v_A_5301_; lean_object* v_n_5302_; lean_object* v_N_5303_; lean_object* v_V_5304_; lean_object* v_z_5305_; lean_object* v_zabbrev_5306_; lean_object* v_v_5307_; lean_object* v_O_5308_; lean_object* v_X_5309_; lean_object* v_x_5310_; lean_object* v_Z_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5319_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_G_5276_ = lean_ctor_get(v_date_4656_, 0);
v_y_5277_ = lean_ctor_get(v_date_4656_, 1);
v_u_5278_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5279_ = lean_ctor_get(v_date_4656_, 3);
v_D_5280_ = lean_ctor_get(v_date_4656_, 4);
v_M_5281_ = lean_ctor_get(v_date_4656_, 5);
v_L_5282_ = lean_ctor_get(v_date_4656_, 6);
v_d_5283_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5284_ = lean_ctor_get(v_date_4656_, 8);
v_q_5285_ = lean_ctor_get(v_date_4656_, 9);
v_w_5286_ = lean_ctor_get(v_date_4656_, 10);
v_W_5287_ = lean_ctor_get(v_date_4656_, 11);
v_e_5288_ = lean_ctor_get(v_date_4656_, 13);
v_c_5289_ = lean_ctor_get(v_date_4656_, 14);
v_F_5290_ = lean_ctor_get(v_date_4656_, 15);
v_a_5291_ = lean_ctor_get(v_date_4656_, 16);
v_b_5292_ = lean_ctor_get(v_date_4656_, 17);
v_B_5293_ = lean_ctor_get(v_date_4656_, 18);
v_h_5294_ = lean_ctor_get(v_date_4656_, 19);
v_K_5295_ = lean_ctor_get(v_date_4656_, 20);
v_k_5296_ = lean_ctor_get(v_date_4656_, 21);
v_H_5297_ = lean_ctor_get(v_date_4656_, 22);
v_m_5298_ = lean_ctor_get(v_date_4656_, 23);
v_s_5299_ = lean_ctor_get(v_date_4656_, 24);
v_S_5300_ = lean_ctor_get(v_date_4656_, 25);
v_A_5301_ = lean_ctor_get(v_date_4656_, 26);
v_n_5302_ = lean_ctor_get(v_date_4656_, 27);
v_N_5303_ = lean_ctor_get(v_date_4656_, 28);
v_V_5304_ = lean_ctor_get(v_date_4656_, 29);
v_z_5305_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5306_ = lean_ctor_get(v_date_4656_, 31);
v_v_5307_ = lean_ctor_get(v_date_4656_, 32);
v_O_5308_ = lean_ctor_get(v_date_4656_, 33);
v_X_5309_ = lean_ctor_get(v_date_4656_, 34);
v_x_5310_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5311_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5319_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5319_ == 0)
{
lean_object* v_unused_5320_; 
v_unused_5320_ = lean_ctor_get(v_date_4656_, 12);
lean_dec(v_unused_5320_);
v___x_5313_ = v_date_4656_;
v_isShared_5314_ = v_isSharedCheck_5319_;
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
lean_inc(v_c_5289_);
lean_inc(v_e_5288_);
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
lean_dec(v_date_4656_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5319_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5315_; lean_object* v___x_5317_; 
v___x_5315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5315_, 0, v_data_4658_);
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 12, v___x_5315_);
v___x_5317_ = v___x_5313_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_G_5276_);
lean_ctor_set(v_reuseFailAlloc_5318_, 1, v_y_5277_);
lean_ctor_set(v_reuseFailAlloc_5318_, 2, v_u_5278_);
lean_ctor_set(v_reuseFailAlloc_5318_, 3, v_Y_5279_);
lean_ctor_set(v_reuseFailAlloc_5318_, 4, v_D_5280_);
lean_ctor_set(v_reuseFailAlloc_5318_, 5, v_M_5281_);
lean_ctor_set(v_reuseFailAlloc_5318_, 6, v_L_5282_);
lean_ctor_set(v_reuseFailAlloc_5318_, 7, v_d_5283_);
lean_ctor_set(v_reuseFailAlloc_5318_, 8, v_Q_5284_);
lean_ctor_set(v_reuseFailAlloc_5318_, 9, v_q_5285_);
lean_ctor_set(v_reuseFailAlloc_5318_, 10, v_w_5286_);
lean_ctor_set(v_reuseFailAlloc_5318_, 11, v_W_5287_);
lean_ctor_set(v_reuseFailAlloc_5318_, 12, v___x_5315_);
lean_ctor_set(v_reuseFailAlloc_5318_, 13, v_e_5288_);
lean_ctor_set(v_reuseFailAlloc_5318_, 14, v_c_5289_);
lean_ctor_set(v_reuseFailAlloc_5318_, 15, v_F_5290_);
lean_ctor_set(v_reuseFailAlloc_5318_, 16, v_a_5291_);
lean_ctor_set(v_reuseFailAlloc_5318_, 17, v_b_5292_);
lean_ctor_set(v_reuseFailAlloc_5318_, 18, v_B_5293_);
lean_ctor_set(v_reuseFailAlloc_5318_, 19, v_h_5294_);
lean_ctor_set(v_reuseFailAlloc_5318_, 20, v_K_5295_);
lean_ctor_set(v_reuseFailAlloc_5318_, 21, v_k_5296_);
lean_ctor_set(v_reuseFailAlloc_5318_, 22, v_H_5297_);
lean_ctor_set(v_reuseFailAlloc_5318_, 23, v_m_5298_);
lean_ctor_set(v_reuseFailAlloc_5318_, 24, v_s_5299_);
lean_ctor_set(v_reuseFailAlloc_5318_, 25, v_S_5300_);
lean_ctor_set(v_reuseFailAlloc_5318_, 26, v_A_5301_);
lean_ctor_set(v_reuseFailAlloc_5318_, 27, v_n_5302_);
lean_ctor_set(v_reuseFailAlloc_5318_, 28, v_N_5303_);
lean_ctor_set(v_reuseFailAlloc_5318_, 29, v_V_5304_);
lean_ctor_set(v_reuseFailAlloc_5318_, 30, v_z_5305_);
lean_ctor_set(v_reuseFailAlloc_5318_, 31, v_zabbrev_5306_);
lean_ctor_set(v_reuseFailAlloc_5318_, 32, v_v_5307_);
lean_ctor_set(v_reuseFailAlloc_5318_, 33, v_O_5308_);
lean_ctor_set(v_reuseFailAlloc_5318_, 34, v_X_5309_);
lean_ctor_set(v_reuseFailAlloc_5318_, 35, v_x_5310_);
lean_ctor_set(v_reuseFailAlloc_5318_, 36, v_Z_5311_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
case 13:
{
lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5371_; 
v_isSharedCheck_5371_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; 
v_unused_5372_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5372_);
v___x_5322_ = v_modifier_4657_;
v_isShared_5323_ = v_isSharedCheck_5371_;
goto v_resetjp_5321_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5371_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v_G_5324_; lean_object* v_y_5325_; lean_object* v_u_5326_; lean_object* v_Y_5327_; lean_object* v_D_5328_; lean_object* v_M_5329_; lean_object* v_L_5330_; lean_object* v_d_5331_; lean_object* v_Q_5332_; lean_object* v_q_5333_; lean_object* v_w_5334_; lean_object* v_W_5335_; lean_object* v_E_5336_; lean_object* v_c_5337_; lean_object* v_F_5338_; lean_object* v_a_5339_; lean_object* v_b_5340_; lean_object* v_B_5341_; lean_object* v_h_5342_; lean_object* v_K_5343_; lean_object* v_k_5344_; lean_object* v_H_5345_; lean_object* v_m_5346_; lean_object* v_s_5347_; lean_object* v_S_5348_; lean_object* v_A_5349_; lean_object* v_n_5350_; lean_object* v_N_5351_; lean_object* v_V_5352_; lean_object* v_z_5353_; lean_object* v_zabbrev_5354_; lean_object* v_v_5355_; lean_object* v_O_5356_; lean_object* v_X_5357_; lean_object* v_x_5358_; lean_object* v_Z_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5369_; 
v_G_5324_ = lean_ctor_get(v_date_4656_, 0);
v_y_5325_ = lean_ctor_get(v_date_4656_, 1);
v_u_5326_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5327_ = lean_ctor_get(v_date_4656_, 3);
v_D_5328_ = lean_ctor_get(v_date_4656_, 4);
v_M_5329_ = lean_ctor_get(v_date_4656_, 5);
v_L_5330_ = lean_ctor_get(v_date_4656_, 6);
v_d_5331_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5332_ = lean_ctor_get(v_date_4656_, 8);
v_q_5333_ = lean_ctor_get(v_date_4656_, 9);
v_w_5334_ = lean_ctor_get(v_date_4656_, 10);
v_W_5335_ = lean_ctor_get(v_date_4656_, 11);
v_E_5336_ = lean_ctor_get(v_date_4656_, 12);
v_c_5337_ = lean_ctor_get(v_date_4656_, 14);
v_F_5338_ = lean_ctor_get(v_date_4656_, 15);
v_a_5339_ = lean_ctor_get(v_date_4656_, 16);
v_b_5340_ = lean_ctor_get(v_date_4656_, 17);
v_B_5341_ = lean_ctor_get(v_date_4656_, 18);
v_h_5342_ = lean_ctor_get(v_date_4656_, 19);
v_K_5343_ = lean_ctor_get(v_date_4656_, 20);
v_k_5344_ = lean_ctor_get(v_date_4656_, 21);
v_H_5345_ = lean_ctor_get(v_date_4656_, 22);
v_m_5346_ = lean_ctor_get(v_date_4656_, 23);
v_s_5347_ = lean_ctor_get(v_date_4656_, 24);
v_S_5348_ = lean_ctor_get(v_date_4656_, 25);
v_A_5349_ = lean_ctor_get(v_date_4656_, 26);
v_n_5350_ = lean_ctor_get(v_date_4656_, 27);
v_N_5351_ = lean_ctor_get(v_date_4656_, 28);
v_V_5352_ = lean_ctor_get(v_date_4656_, 29);
v_z_5353_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5354_ = lean_ctor_get(v_date_4656_, 31);
v_v_5355_ = lean_ctor_get(v_date_4656_, 32);
v_O_5356_ = lean_ctor_get(v_date_4656_, 33);
v_X_5357_ = lean_ctor_get(v_date_4656_, 34);
v_x_5358_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5359_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5369_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5369_ == 0)
{
lean_object* v_unused_5370_; 
v_unused_5370_ = lean_ctor_get(v_date_4656_, 13);
lean_dec(v_unused_5370_);
v___x_5361_ = v_date_4656_;
v_isShared_5362_ = v_isSharedCheck_5369_;
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
lean_inc(v_B_5341_);
lean_inc(v_b_5340_);
lean_inc(v_a_5339_);
lean_inc(v_F_5338_);
lean_inc(v_c_5337_);
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
lean_dec(v_date_4656_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5369_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v___x_5364_; 
if (v_isShared_5323_ == 0)
{
lean_ctor_set_tag(v___x_5322_, 1);
lean_ctor_set(v___x_5322_, 0, v_data_4658_);
v___x_5364_ = v___x_5322_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_data_4658_);
v___x_5364_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
lean_object* v___x_5366_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 13, v___x_5364_);
v___x_5366_ = v___x_5361_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_G_5324_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v_y_5325_);
lean_ctor_set(v_reuseFailAlloc_5367_, 2, v_u_5326_);
lean_ctor_set(v_reuseFailAlloc_5367_, 3, v_Y_5327_);
lean_ctor_set(v_reuseFailAlloc_5367_, 4, v_D_5328_);
lean_ctor_set(v_reuseFailAlloc_5367_, 5, v_M_5329_);
lean_ctor_set(v_reuseFailAlloc_5367_, 6, v_L_5330_);
lean_ctor_set(v_reuseFailAlloc_5367_, 7, v_d_5331_);
lean_ctor_set(v_reuseFailAlloc_5367_, 8, v_Q_5332_);
lean_ctor_set(v_reuseFailAlloc_5367_, 9, v_q_5333_);
lean_ctor_set(v_reuseFailAlloc_5367_, 10, v_w_5334_);
lean_ctor_set(v_reuseFailAlloc_5367_, 11, v_W_5335_);
lean_ctor_set(v_reuseFailAlloc_5367_, 12, v_E_5336_);
lean_ctor_set(v_reuseFailAlloc_5367_, 13, v___x_5364_);
lean_ctor_set(v_reuseFailAlloc_5367_, 14, v_c_5337_);
lean_ctor_set(v_reuseFailAlloc_5367_, 15, v_F_5338_);
lean_ctor_set(v_reuseFailAlloc_5367_, 16, v_a_5339_);
lean_ctor_set(v_reuseFailAlloc_5367_, 17, v_b_5340_);
lean_ctor_set(v_reuseFailAlloc_5367_, 18, v_B_5341_);
lean_ctor_set(v_reuseFailAlloc_5367_, 19, v_h_5342_);
lean_ctor_set(v_reuseFailAlloc_5367_, 20, v_K_5343_);
lean_ctor_set(v_reuseFailAlloc_5367_, 21, v_k_5344_);
lean_ctor_set(v_reuseFailAlloc_5367_, 22, v_H_5345_);
lean_ctor_set(v_reuseFailAlloc_5367_, 23, v_m_5346_);
lean_ctor_set(v_reuseFailAlloc_5367_, 24, v_s_5347_);
lean_ctor_set(v_reuseFailAlloc_5367_, 25, v_S_5348_);
lean_ctor_set(v_reuseFailAlloc_5367_, 26, v_A_5349_);
lean_ctor_set(v_reuseFailAlloc_5367_, 27, v_n_5350_);
lean_ctor_set(v_reuseFailAlloc_5367_, 28, v_N_5351_);
lean_ctor_set(v_reuseFailAlloc_5367_, 29, v_V_5352_);
lean_ctor_set(v_reuseFailAlloc_5367_, 30, v_z_5353_);
lean_ctor_set(v_reuseFailAlloc_5367_, 31, v_zabbrev_5354_);
lean_ctor_set(v_reuseFailAlloc_5367_, 32, v_v_5355_);
lean_ctor_set(v_reuseFailAlloc_5367_, 33, v_O_5356_);
lean_ctor_set(v_reuseFailAlloc_5367_, 34, v_X_5357_);
lean_ctor_set(v_reuseFailAlloc_5367_, 35, v_x_5358_);
lean_ctor_set(v_reuseFailAlloc_5367_, 36, v_Z_5359_);
v___x_5366_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
return v___x_5366_;
}
}
}
}
}
case 14:
{
lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5423_; 
v_isSharedCheck_5423_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5423_ == 0)
{
lean_object* v_unused_5424_; 
v_unused_5424_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5424_);
v___x_5374_ = v_modifier_4657_;
v_isShared_5375_ = v_isSharedCheck_5423_;
goto v_resetjp_5373_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5423_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
lean_object* v_G_5376_; lean_object* v_y_5377_; lean_object* v_u_5378_; lean_object* v_Y_5379_; lean_object* v_D_5380_; lean_object* v_M_5381_; lean_object* v_L_5382_; lean_object* v_d_5383_; lean_object* v_Q_5384_; lean_object* v_q_5385_; lean_object* v_w_5386_; lean_object* v_W_5387_; lean_object* v_E_5388_; lean_object* v_e_5389_; lean_object* v_F_5390_; lean_object* v_a_5391_; lean_object* v_b_5392_; lean_object* v_B_5393_; lean_object* v_h_5394_; lean_object* v_K_5395_; lean_object* v_k_5396_; lean_object* v_H_5397_; lean_object* v_m_5398_; lean_object* v_s_5399_; lean_object* v_S_5400_; lean_object* v_A_5401_; lean_object* v_n_5402_; lean_object* v_N_5403_; lean_object* v_V_5404_; lean_object* v_z_5405_; lean_object* v_zabbrev_5406_; lean_object* v_v_5407_; lean_object* v_O_5408_; lean_object* v_X_5409_; lean_object* v_x_5410_; lean_object* v_Z_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5421_; 
v_G_5376_ = lean_ctor_get(v_date_4656_, 0);
v_y_5377_ = lean_ctor_get(v_date_4656_, 1);
v_u_5378_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5379_ = lean_ctor_get(v_date_4656_, 3);
v_D_5380_ = lean_ctor_get(v_date_4656_, 4);
v_M_5381_ = lean_ctor_get(v_date_4656_, 5);
v_L_5382_ = lean_ctor_get(v_date_4656_, 6);
v_d_5383_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5384_ = lean_ctor_get(v_date_4656_, 8);
v_q_5385_ = lean_ctor_get(v_date_4656_, 9);
v_w_5386_ = lean_ctor_get(v_date_4656_, 10);
v_W_5387_ = lean_ctor_get(v_date_4656_, 11);
v_E_5388_ = lean_ctor_get(v_date_4656_, 12);
v_e_5389_ = lean_ctor_get(v_date_4656_, 13);
v_F_5390_ = lean_ctor_get(v_date_4656_, 15);
v_a_5391_ = lean_ctor_get(v_date_4656_, 16);
v_b_5392_ = lean_ctor_get(v_date_4656_, 17);
v_B_5393_ = lean_ctor_get(v_date_4656_, 18);
v_h_5394_ = lean_ctor_get(v_date_4656_, 19);
v_K_5395_ = lean_ctor_get(v_date_4656_, 20);
v_k_5396_ = lean_ctor_get(v_date_4656_, 21);
v_H_5397_ = lean_ctor_get(v_date_4656_, 22);
v_m_5398_ = lean_ctor_get(v_date_4656_, 23);
v_s_5399_ = lean_ctor_get(v_date_4656_, 24);
v_S_5400_ = lean_ctor_get(v_date_4656_, 25);
v_A_5401_ = lean_ctor_get(v_date_4656_, 26);
v_n_5402_ = lean_ctor_get(v_date_4656_, 27);
v_N_5403_ = lean_ctor_get(v_date_4656_, 28);
v_V_5404_ = lean_ctor_get(v_date_4656_, 29);
v_z_5405_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5406_ = lean_ctor_get(v_date_4656_, 31);
v_v_5407_ = lean_ctor_get(v_date_4656_, 32);
v_O_5408_ = lean_ctor_get(v_date_4656_, 33);
v_X_5409_ = lean_ctor_get(v_date_4656_, 34);
v_x_5410_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5411_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5421_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5421_ == 0)
{
lean_object* v_unused_5422_; 
v_unused_5422_ = lean_ctor_get(v_date_4656_, 14);
lean_dec(v_unused_5422_);
v___x_5413_ = v_date_4656_;
v_isShared_5414_ = v_isSharedCheck_5421_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_Z_5411_);
lean_inc(v_x_5410_);
lean_inc(v_X_5409_);
lean_inc(v_O_5408_);
lean_inc(v_v_5407_);
lean_inc(v_zabbrev_5406_);
lean_inc(v_z_5405_);
lean_inc(v_V_5404_);
lean_inc(v_N_5403_);
lean_inc(v_n_5402_);
lean_inc(v_A_5401_);
lean_inc(v_S_5400_);
lean_inc(v_s_5399_);
lean_inc(v_m_5398_);
lean_inc(v_H_5397_);
lean_inc(v_k_5396_);
lean_inc(v_K_5395_);
lean_inc(v_h_5394_);
lean_inc(v_B_5393_);
lean_inc(v_b_5392_);
lean_inc(v_a_5391_);
lean_inc(v_F_5390_);
lean_inc(v_e_5389_);
lean_inc(v_E_5388_);
lean_inc(v_W_5387_);
lean_inc(v_w_5386_);
lean_inc(v_q_5385_);
lean_inc(v_Q_5384_);
lean_inc(v_d_5383_);
lean_inc(v_L_5382_);
lean_inc(v_M_5381_);
lean_inc(v_D_5380_);
lean_inc(v_Y_5379_);
lean_inc(v_u_5378_);
lean_inc(v_y_5377_);
lean_inc(v_G_5376_);
lean_dec(v_date_4656_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5421_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5416_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set_tag(v___x_5374_, 1);
lean_ctor_set(v___x_5374_, 0, v_data_4658_);
v___x_5416_ = v___x_5374_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v_data_4658_);
v___x_5416_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
lean_object* v___x_5418_; 
if (v_isShared_5414_ == 0)
{
lean_ctor_set(v___x_5413_, 14, v___x_5416_);
v___x_5418_ = v___x_5413_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_G_5376_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v_y_5377_);
lean_ctor_set(v_reuseFailAlloc_5419_, 2, v_u_5378_);
lean_ctor_set(v_reuseFailAlloc_5419_, 3, v_Y_5379_);
lean_ctor_set(v_reuseFailAlloc_5419_, 4, v_D_5380_);
lean_ctor_set(v_reuseFailAlloc_5419_, 5, v_M_5381_);
lean_ctor_set(v_reuseFailAlloc_5419_, 6, v_L_5382_);
lean_ctor_set(v_reuseFailAlloc_5419_, 7, v_d_5383_);
lean_ctor_set(v_reuseFailAlloc_5419_, 8, v_Q_5384_);
lean_ctor_set(v_reuseFailAlloc_5419_, 9, v_q_5385_);
lean_ctor_set(v_reuseFailAlloc_5419_, 10, v_w_5386_);
lean_ctor_set(v_reuseFailAlloc_5419_, 11, v_W_5387_);
lean_ctor_set(v_reuseFailAlloc_5419_, 12, v_E_5388_);
lean_ctor_set(v_reuseFailAlloc_5419_, 13, v_e_5389_);
lean_ctor_set(v_reuseFailAlloc_5419_, 14, v___x_5416_);
lean_ctor_set(v_reuseFailAlloc_5419_, 15, v_F_5390_);
lean_ctor_set(v_reuseFailAlloc_5419_, 16, v_a_5391_);
lean_ctor_set(v_reuseFailAlloc_5419_, 17, v_b_5392_);
lean_ctor_set(v_reuseFailAlloc_5419_, 18, v_B_5393_);
lean_ctor_set(v_reuseFailAlloc_5419_, 19, v_h_5394_);
lean_ctor_set(v_reuseFailAlloc_5419_, 20, v_K_5395_);
lean_ctor_set(v_reuseFailAlloc_5419_, 21, v_k_5396_);
lean_ctor_set(v_reuseFailAlloc_5419_, 22, v_H_5397_);
lean_ctor_set(v_reuseFailAlloc_5419_, 23, v_m_5398_);
lean_ctor_set(v_reuseFailAlloc_5419_, 24, v_s_5399_);
lean_ctor_set(v_reuseFailAlloc_5419_, 25, v_S_5400_);
lean_ctor_set(v_reuseFailAlloc_5419_, 26, v_A_5401_);
lean_ctor_set(v_reuseFailAlloc_5419_, 27, v_n_5402_);
lean_ctor_set(v_reuseFailAlloc_5419_, 28, v_N_5403_);
lean_ctor_set(v_reuseFailAlloc_5419_, 29, v_V_5404_);
lean_ctor_set(v_reuseFailAlloc_5419_, 30, v_z_5405_);
lean_ctor_set(v_reuseFailAlloc_5419_, 31, v_zabbrev_5406_);
lean_ctor_set(v_reuseFailAlloc_5419_, 32, v_v_5407_);
lean_ctor_set(v_reuseFailAlloc_5419_, 33, v_O_5408_);
lean_ctor_set(v_reuseFailAlloc_5419_, 34, v_X_5409_);
lean_ctor_set(v_reuseFailAlloc_5419_, 35, v_x_5410_);
lean_ctor_set(v_reuseFailAlloc_5419_, 36, v_Z_5411_);
v___x_5418_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
return v___x_5418_;
}
}
}
}
}
case 15:
{
lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5475_; 
v_isSharedCheck_5475_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5475_ == 0)
{
lean_object* v_unused_5476_; 
v_unused_5476_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5476_);
v___x_5426_ = v_modifier_4657_;
v_isShared_5427_ = v_isSharedCheck_5475_;
goto v_resetjp_5425_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5475_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v_G_5428_; lean_object* v_y_5429_; lean_object* v_u_5430_; lean_object* v_Y_5431_; lean_object* v_D_5432_; lean_object* v_M_5433_; lean_object* v_L_5434_; lean_object* v_d_5435_; lean_object* v_Q_5436_; lean_object* v_q_5437_; lean_object* v_w_5438_; lean_object* v_W_5439_; lean_object* v_E_5440_; lean_object* v_e_5441_; lean_object* v_c_5442_; lean_object* v_a_5443_; lean_object* v_b_5444_; lean_object* v_B_5445_; lean_object* v_h_5446_; lean_object* v_K_5447_; lean_object* v_k_5448_; lean_object* v_H_5449_; lean_object* v_m_5450_; lean_object* v_s_5451_; lean_object* v_S_5452_; lean_object* v_A_5453_; lean_object* v_n_5454_; lean_object* v_N_5455_; lean_object* v_V_5456_; lean_object* v_z_5457_; lean_object* v_zabbrev_5458_; lean_object* v_v_5459_; lean_object* v_O_5460_; lean_object* v_X_5461_; lean_object* v_x_5462_; lean_object* v_Z_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5473_; 
v_G_5428_ = lean_ctor_get(v_date_4656_, 0);
v_y_5429_ = lean_ctor_get(v_date_4656_, 1);
v_u_5430_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5431_ = lean_ctor_get(v_date_4656_, 3);
v_D_5432_ = lean_ctor_get(v_date_4656_, 4);
v_M_5433_ = lean_ctor_get(v_date_4656_, 5);
v_L_5434_ = lean_ctor_get(v_date_4656_, 6);
v_d_5435_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5436_ = lean_ctor_get(v_date_4656_, 8);
v_q_5437_ = lean_ctor_get(v_date_4656_, 9);
v_w_5438_ = lean_ctor_get(v_date_4656_, 10);
v_W_5439_ = lean_ctor_get(v_date_4656_, 11);
v_E_5440_ = lean_ctor_get(v_date_4656_, 12);
v_e_5441_ = lean_ctor_get(v_date_4656_, 13);
v_c_5442_ = lean_ctor_get(v_date_4656_, 14);
v_a_5443_ = lean_ctor_get(v_date_4656_, 16);
v_b_5444_ = lean_ctor_get(v_date_4656_, 17);
v_B_5445_ = lean_ctor_get(v_date_4656_, 18);
v_h_5446_ = lean_ctor_get(v_date_4656_, 19);
v_K_5447_ = lean_ctor_get(v_date_4656_, 20);
v_k_5448_ = lean_ctor_get(v_date_4656_, 21);
v_H_5449_ = lean_ctor_get(v_date_4656_, 22);
v_m_5450_ = lean_ctor_get(v_date_4656_, 23);
v_s_5451_ = lean_ctor_get(v_date_4656_, 24);
v_S_5452_ = lean_ctor_get(v_date_4656_, 25);
v_A_5453_ = lean_ctor_get(v_date_4656_, 26);
v_n_5454_ = lean_ctor_get(v_date_4656_, 27);
v_N_5455_ = lean_ctor_get(v_date_4656_, 28);
v_V_5456_ = lean_ctor_get(v_date_4656_, 29);
v_z_5457_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5458_ = lean_ctor_get(v_date_4656_, 31);
v_v_5459_ = lean_ctor_get(v_date_4656_, 32);
v_O_5460_ = lean_ctor_get(v_date_4656_, 33);
v_X_5461_ = lean_ctor_get(v_date_4656_, 34);
v_x_5462_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5463_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5473_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5473_ == 0)
{
lean_object* v_unused_5474_; 
v_unused_5474_ = lean_ctor_get(v_date_4656_, 15);
lean_dec(v_unused_5474_);
v___x_5465_ = v_date_4656_;
v_isShared_5466_ = v_isSharedCheck_5473_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_Z_5463_);
lean_inc(v_x_5462_);
lean_inc(v_X_5461_);
lean_inc(v_O_5460_);
lean_inc(v_v_5459_);
lean_inc(v_zabbrev_5458_);
lean_inc(v_z_5457_);
lean_inc(v_V_5456_);
lean_inc(v_N_5455_);
lean_inc(v_n_5454_);
lean_inc(v_A_5453_);
lean_inc(v_S_5452_);
lean_inc(v_s_5451_);
lean_inc(v_m_5450_);
lean_inc(v_H_5449_);
lean_inc(v_k_5448_);
lean_inc(v_K_5447_);
lean_inc(v_h_5446_);
lean_inc(v_B_5445_);
lean_inc(v_b_5444_);
lean_inc(v_a_5443_);
lean_inc(v_c_5442_);
lean_inc(v_e_5441_);
lean_inc(v_E_5440_);
lean_inc(v_W_5439_);
lean_inc(v_w_5438_);
lean_inc(v_q_5437_);
lean_inc(v_Q_5436_);
lean_inc(v_d_5435_);
lean_inc(v_L_5434_);
lean_inc(v_M_5433_);
lean_inc(v_D_5432_);
lean_inc(v_Y_5431_);
lean_inc(v_u_5430_);
lean_inc(v_y_5429_);
lean_inc(v_G_5428_);
lean_dec(v_date_4656_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5473_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5427_ == 0)
{
lean_ctor_set_tag(v___x_5426_, 1);
lean_ctor_set(v___x_5426_, 0, v_data_4658_);
v___x_5468_ = v___x_5426_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_data_4658_);
v___x_5468_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
lean_object* v___x_5470_; 
if (v_isShared_5466_ == 0)
{
lean_ctor_set(v___x_5465_, 15, v___x_5468_);
v___x_5470_ = v___x_5465_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_G_5428_);
lean_ctor_set(v_reuseFailAlloc_5471_, 1, v_y_5429_);
lean_ctor_set(v_reuseFailAlloc_5471_, 2, v_u_5430_);
lean_ctor_set(v_reuseFailAlloc_5471_, 3, v_Y_5431_);
lean_ctor_set(v_reuseFailAlloc_5471_, 4, v_D_5432_);
lean_ctor_set(v_reuseFailAlloc_5471_, 5, v_M_5433_);
lean_ctor_set(v_reuseFailAlloc_5471_, 6, v_L_5434_);
lean_ctor_set(v_reuseFailAlloc_5471_, 7, v_d_5435_);
lean_ctor_set(v_reuseFailAlloc_5471_, 8, v_Q_5436_);
lean_ctor_set(v_reuseFailAlloc_5471_, 9, v_q_5437_);
lean_ctor_set(v_reuseFailAlloc_5471_, 10, v_w_5438_);
lean_ctor_set(v_reuseFailAlloc_5471_, 11, v_W_5439_);
lean_ctor_set(v_reuseFailAlloc_5471_, 12, v_E_5440_);
lean_ctor_set(v_reuseFailAlloc_5471_, 13, v_e_5441_);
lean_ctor_set(v_reuseFailAlloc_5471_, 14, v_c_5442_);
lean_ctor_set(v_reuseFailAlloc_5471_, 15, v___x_5468_);
lean_ctor_set(v_reuseFailAlloc_5471_, 16, v_a_5443_);
lean_ctor_set(v_reuseFailAlloc_5471_, 17, v_b_5444_);
lean_ctor_set(v_reuseFailAlloc_5471_, 18, v_B_5445_);
lean_ctor_set(v_reuseFailAlloc_5471_, 19, v_h_5446_);
lean_ctor_set(v_reuseFailAlloc_5471_, 20, v_K_5447_);
lean_ctor_set(v_reuseFailAlloc_5471_, 21, v_k_5448_);
lean_ctor_set(v_reuseFailAlloc_5471_, 22, v_H_5449_);
lean_ctor_set(v_reuseFailAlloc_5471_, 23, v_m_5450_);
lean_ctor_set(v_reuseFailAlloc_5471_, 24, v_s_5451_);
lean_ctor_set(v_reuseFailAlloc_5471_, 25, v_S_5452_);
lean_ctor_set(v_reuseFailAlloc_5471_, 26, v_A_5453_);
lean_ctor_set(v_reuseFailAlloc_5471_, 27, v_n_5454_);
lean_ctor_set(v_reuseFailAlloc_5471_, 28, v_N_5455_);
lean_ctor_set(v_reuseFailAlloc_5471_, 29, v_V_5456_);
lean_ctor_set(v_reuseFailAlloc_5471_, 30, v_z_5457_);
lean_ctor_set(v_reuseFailAlloc_5471_, 31, v_zabbrev_5458_);
lean_ctor_set(v_reuseFailAlloc_5471_, 32, v_v_5459_);
lean_ctor_set(v_reuseFailAlloc_5471_, 33, v_O_5460_);
lean_ctor_set(v_reuseFailAlloc_5471_, 34, v_X_5461_);
lean_ctor_set(v_reuseFailAlloc_5471_, 35, v_x_5462_);
lean_ctor_set(v_reuseFailAlloc_5471_, 36, v_Z_5463_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
}
}
case 16:
{
lean_object* v_G_5477_; lean_object* v_y_5478_; lean_object* v_u_5479_; lean_object* v_Y_5480_; lean_object* v_D_5481_; lean_object* v_M_5482_; lean_object* v_L_5483_; lean_object* v_d_5484_; lean_object* v_Q_5485_; lean_object* v_q_5486_; lean_object* v_w_5487_; lean_object* v_W_5488_; lean_object* v_E_5489_; lean_object* v_e_5490_; lean_object* v_c_5491_; lean_object* v_F_5492_; lean_object* v_b_5493_; lean_object* v_B_5494_; lean_object* v_h_5495_; lean_object* v_K_5496_; lean_object* v_k_5497_; lean_object* v_H_5498_; lean_object* v_m_5499_; lean_object* v_s_5500_; lean_object* v_S_5501_; lean_object* v_A_5502_; lean_object* v_n_5503_; lean_object* v_N_5504_; lean_object* v_V_5505_; lean_object* v_z_5506_; lean_object* v_zabbrev_5507_; lean_object* v_v_5508_; lean_object* v_O_5509_; lean_object* v_X_5510_; lean_object* v_x_5511_; lean_object* v_Z_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5520_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_G_5477_ = lean_ctor_get(v_date_4656_, 0);
v_y_5478_ = lean_ctor_get(v_date_4656_, 1);
v_u_5479_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5480_ = lean_ctor_get(v_date_4656_, 3);
v_D_5481_ = lean_ctor_get(v_date_4656_, 4);
v_M_5482_ = lean_ctor_get(v_date_4656_, 5);
v_L_5483_ = lean_ctor_get(v_date_4656_, 6);
v_d_5484_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5485_ = lean_ctor_get(v_date_4656_, 8);
v_q_5486_ = lean_ctor_get(v_date_4656_, 9);
v_w_5487_ = lean_ctor_get(v_date_4656_, 10);
v_W_5488_ = lean_ctor_get(v_date_4656_, 11);
v_E_5489_ = lean_ctor_get(v_date_4656_, 12);
v_e_5490_ = lean_ctor_get(v_date_4656_, 13);
v_c_5491_ = lean_ctor_get(v_date_4656_, 14);
v_F_5492_ = lean_ctor_get(v_date_4656_, 15);
v_b_5493_ = lean_ctor_get(v_date_4656_, 17);
v_B_5494_ = lean_ctor_get(v_date_4656_, 18);
v_h_5495_ = lean_ctor_get(v_date_4656_, 19);
v_K_5496_ = lean_ctor_get(v_date_4656_, 20);
v_k_5497_ = lean_ctor_get(v_date_4656_, 21);
v_H_5498_ = lean_ctor_get(v_date_4656_, 22);
v_m_5499_ = lean_ctor_get(v_date_4656_, 23);
v_s_5500_ = lean_ctor_get(v_date_4656_, 24);
v_S_5501_ = lean_ctor_get(v_date_4656_, 25);
v_A_5502_ = lean_ctor_get(v_date_4656_, 26);
v_n_5503_ = lean_ctor_get(v_date_4656_, 27);
v_N_5504_ = lean_ctor_get(v_date_4656_, 28);
v_V_5505_ = lean_ctor_get(v_date_4656_, 29);
v_z_5506_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5507_ = lean_ctor_get(v_date_4656_, 31);
v_v_5508_ = lean_ctor_get(v_date_4656_, 32);
v_O_5509_ = lean_ctor_get(v_date_4656_, 33);
v_X_5510_ = lean_ctor_get(v_date_4656_, 34);
v_x_5511_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5512_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5520_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5520_ == 0)
{
lean_object* v_unused_5521_; 
v_unused_5521_ = lean_ctor_get(v_date_4656_, 16);
lean_dec(v_unused_5521_);
v___x_5514_ = v_date_4656_;
v_isShared_5515_ = v_isSharedCheck_5520_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_Z_5512_);
lean_inc(v_x_5511_);
lean_inc(v_X_5510_);
lean_inc(v_O_5509_);
lean_inc(v_v_5508_);
lean_inc(v_zabbrev_5507_);
lean_inc(v_z_5506_);
lean_inc(v_V_5505_);
lean_inc(v_N_5504_);
lean_inc(v_n_5503_);
lean_inc(v_A_5502_);
lean_inc(v_S_5501_);
lean_inc(v_s_5500_);
lean_inc(v_m_5499_);
lean_inc(v_H_5498_);
lean_inc(v_k_5497_);
lean_inc(v_K_5496_);
lean_inc(v_h_5495_);
lean_inc(v_B_5494_);
lean_inc(v_b_5493_);
lean_inc(v_F_5492_);
lean_inc(v_c_5491_);
lean_inc(v_e_5490_);
lean_inc(v_E_5489_);
lean_inc(v_W_5488_);
lean_inc(v_w_5487_);
lean_inc(v_q_5486_);
lean_inc(v_Q_5485_);
lean_inc(v_d_5484_);
lean_inc(v_L_5483_);
lean_inc(v_M_5482_);
lean_inc(v_D_5481_);
lean_inc(v_Y_5480_);
lean_inc(v_u_5479_);
lean_inc(v_y_5478_);
lean_inc(v_G_5477_);
lean_dec(v_date_4656_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5520_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5516_; lean_object* v___x_5518_; 
v___x_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5516_, 0, v_data_4658_);
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 16, v___x_5516_);
v___x_5518_ = v___x_5514_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_G_5477_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v_y_5478_);
lean_ctor_set(v_reuseFailAlloc_5519_, 2, v_u_5479_);
lean_ctor_set(v_reuseFailAlloc_5519_, 3, v_Y_5480_);
lean_ctor_set(v_reuseFailAlloc_5519_, 4, v_D_5481_);
lean_ctor_set(v_reuseFailAlloc_5519_, 5, v_M_5482_);
lean_ctor_set(v_reuseFailAlloc_5519_, 6, v_L_5483_);
lean_ctor_set(v_reuseFailAlloc_5519_, 7, v_d_5484_);
lean_ctor_set(v_reuseFailAlloc_5519_, 8, v_Q_5485_);
lean_ctor_set(v_reuseFailAlloc_5519_, 9, v_q_5486_);
lean_ctor_set(v_reuseFailAlloc_5519_, 10, v_w_5487_);
lean_ctor_set(v_reuseFailAlloc_5519_, 11, v_W_5488_);
lean_ctor_set(v_reuseFailAlloc_5519_, 12, v_E_5489_);
lean_ctor_set(v_reuseFailAlloc_5519_, 13, v_e_5490_);
lean_ctor_set(v_reuseFailAlloc_5519_, 14, v_c_5491_);
lean_ctor_set(v_reuseFailAlloc_5519_, 15, v_F_5492_);
lean_ctor_set(v_reuseFailAlloc_5519_, 16, v___x_5516_);
lean_ctor_set(v_reuseFailAlloc_5519_, 17, v_b_5493_);
lean_ctor_set(v_reuseFailAlloc_5519_, 18, v_B_5494_);
lean_ctor_set(v_reuseFailAlloc_5519_, 19, v_h_5495_);
lean_ctor_set(v_reuseFailAlloc_5519_, 20, v_K_5496_);
lean_ctor_set(v_reuseFailAlloc_5519_, 21, v_k_5497_);
lean_ctor_set(v_reuseFailAlloc_5519_, 22, v_H_5498_);
lean_ctor_set(v_reuseFailAlloc_5519_, 23, v_m_5499_);
lean_ctor_set(v_reuseFailAlloc_5519_, 24, v_s_5500_);
lean_ctor_set(v_reuseFailAlloc_5519_, 25, v_S_5501_);
lean_ctor_set(v_reuseFailAlloc_5519_, 26, v_A_5502_);
lean_ctor_set(v_reuseFailAlloc_5519_, 27, v_n_5503_);
lean_ctor_set(v_reuseFailAlloc_5519_, 28, v_N_5504_);
lean_ctor_set(v_reuseFailAlloc_5519_, 29, v_V_5505_);
lean_ctor_set(v_reuseFailAlloc_5519_, 30, v_z_5506_);
lean_ctor_set(v_reuseFailAlloc_5519_, 31, v_zabbrev_5507_);
lean_ctor_set(v_reuseFailAlloc_5519_, 32, v_v_5508_);
lean_ctor_set(v_reuseFailAlloc_5519_, 33, v_O_5509_);
lean_ctor_set(v_reuseFailAlloc_5519_, 34, v_X_5510_);
lean_ctor_set(v_reuseFailAlloc_5519_, 35, v_x_5511_);
lean_ctor_set(v_reuseFailAlloc_5519_, 36, v_Z_5512_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
case 17:
{
lean_object* v_G_5522_; lean_object* v_y_5523_; lean_object* v_u_5524_; lean_object* v_Y_5525_; lean_object* v_D_5526_; lean_object* v_M_5527_; lean_object* v_L_5528_; lean_object* v_d_5529_; lean_object* v_Q_5530_; lean_object* v_q_5531_; lean_object* v_w_5532_; lean_object* v_W_5533_; lean_object* v_E_5534_; lean_object* v_e_5535_; lean_object* v_c_5536_; lean_object* v_F_5537_; lean_object* v_a_5538_; lean_object* v_B_5539_; lean_object* v_h_5540_; lean_object* v_K_5541_; lean_object* v_k_5542_; lean_object* v_H_5543_; lean_object* v_m_5544_; lean_object* v_s_5545_; lean_object* v_S_5546_; lean_object* v_A_5547_; lean_object* v_n_5548_; lean_object* v_N_5549_; lean_object* v_V_5550_; lean_object* v_z_5551_; lean_object* v_zabbrev_5552_; lean_object* v_v_5553_; lean_object* v_O_5554_; lean_object* v_X_5555_; lean_object* v_x_5556_; lean_object* v_Z_5557_; lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5565_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_G_5522_ = lean_ctor_get(v_date_4656_, 0);
v_y_5523_ = lean_ctor_get(v_date_4656_, 1);
v_u_5524_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5525_ = lean_ctor_get(v_date_4656_, 3);
v_D_5526_ = lean_ctor_get(v_date_4656_, 4);
v_M_5527_ = lean_ctor_get(v_date_4656_, 5);
v_L_5528_ = lean_ctor_get(v_date_4656_, 6);
v_d_5529_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5530_ = lean_ctor_get(v_date_4656_, 8);
v_q_5531_ = lean_ctor_get(v_date_4656_, 9);
v_w_5532_ = lean_ctor_get(v_date_4656_, 10);
v_W_5533_ = lean_ctor_get(v_date_4656_, 11);
v_E_5534_ = lean_ctor_get(v_date_4656_, 12);
v_e_5535_ = lean_ctor_get(v_date_4656_, 13);
v_c_5536_ = lean_ctor_get(v_date_4656_, 14);
v_F_5537_ = lean_ctor_get(v_date_4656_, 15);
v_a_5538_ = lean_ctor_get(v_date_4656_, 16);
v_B_5539_ = lean_ctor_get(v_date_4656_, 18);
v_h_5540_ = lean_ctor_get(v_date_4656_, 19);
v_K_5541_ = lean_ctor_get(v_date_4656_, 20);
v_k_5542_ = lean_ctor_get(v_date_4656_, 21);
v_H_5543_ = lean_ctor_get(v_date_4656_, 22);
v_m_5544_ = lean_ctor_get(v_date_4656_, 23);
v_s_5545_ = lean_ctor_get(v_date_4656_, 24);
v_S_5546_ = lean_ctor_get(v_date_4656_, 25);
v_A_5547_ = lean_ctor_get(v_date_4656_, 26);
v_n_5548_ = lean_ctor_get(v_date_4656_, 27);
v_N_5549_ = lean_ctor_get(v_date_4656_, 28);
v_V_5550_ = lean_ctor_get(v_date_4656_, 29);
v_z_5551_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5552_ = lean_ctor_get(v_date_4656_, 31);
v_v_5553_ = lean_ctor_get(v_date_4656_, 32);
v_O_5554_ = lean_ctor_get(v_date_4656_, 33);
v_X_5555_ = lean_ctor_get(v_date_4656_, 34);
v_x_5556_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5557_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5565_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5565_ == 0)
{
lean_object* v_unused_5566_; 
v_unused_5566_ = lean_ctor_get(v_date_4656_, 17);
lean_dec(v_unused_5566_);
v___x_5559_ = v_date_4656_;
v_isShared_5560_ = v_isSharedCheck_5565_;
goto v_resetjp_5558_;
}
else
{
lean_inc(v_Z_5557_);
lean_inc(v_x_5556_);
lean_inc(v_X_5555_);
lean_inc(v_O_5554_);
lean_inc(v_v_5553_);
lean_inc(v_zabbrev_5552_);
lean_inc(v_z_5551_);
lean_inc(v_V_5550_);
lean_inc(v_N_5549_);
lean_inc(v_n_5548_);
lean_inc(v_A_5547_);
lean_inc(v_S_5546_);
lean_inc(v_s_5545_);
lean_inc(v_m_5544_);
lean_inc(v_H_5543_);
lean_inc(v_k_5542_);
lean_inc(v_K_5541_);
lean_inc(v_h_5540_);
lean_inc(v_B_5539_);
lean_inc(v_a_5538_);
lean_inc(v_F_5537_);
lean_inc(v_c_5536_);
lean_inc(v_e_5535_);
lean_inc(v_E_5534_);
lean_inc(v_W_5533_);
lean_inc(v_w_5532_);
lean_inc(v_q_5531_);
lean_inc(v_Q_5530_);
lean_inc(v_d_5529_);
lean_inc(v_L_5528_);
lean_inc(v_M_5527_);
lean_inc(v_D_5526_);
lean_inc(v_Y_5525_);
lean_inc(v_u_5524_);
lean_inc(v_y_5523_);
lean_inc(v_G_5522_);
lean_dec(v_date_4656_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5565_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v___x_5561_; lean_object* v___x_5563_; 
v___x_5561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5561_, 0, v_data_4658_);
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 17, v___x_5561_);
v___x_5563_ = v___x_5559_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_G_5522_);
lean_ctor_set(v_reuseFailAlloc_5564_, 1, v_y_5523_);
lean_ctor_set(v_reuseFailAlloc_5564_, 2, v_u_5524_);
lean_ctor_set(v_reuseFailAlloc_5564_, 3, v_Y_5525_);
lean_ctor_set(v_reuseFailAlloc_5564_, 4, v_D_5526_);
lean_ctor_set(v_reuseFailAlloc_5564_, 5, v_M_5527_);
lean_ctor_set(v_reuseFailAlloc_5564_, 6, v_L_5528_);
lean_ctor_set(v_reuseFailAlloc_5564_, 7, v_d_5529_);
lean_ctor_set(v_reuseFailAlloc_5564_, 8, v_Q_5530_);
lean_ctor_set(v_reuseFailAlloc_5564_, 9, v_q_5531_);
lean_ctor_set(v_reuseFailAlloc_5564_, 10, v_w_5532_);
lean_ctor_set(v_reuseFailAlloc_5564_, 11, v_W_5533_);
lean_ctor_set(v_reuseFailAlloc_5564_, 12, v_E_5534_);
lean_ctor_set(v_reuseFailAlloc_5564_, 13, v_e_5535_);
lean_ctor_set(v_reuseFailAlloc_5564_, 14, v_c_5536_);
lean_ctor_set(v_reuseFailAlloc_5564_, 15, v_F_5537_);
lean_ctor_set(v_reuseFailAlloc_5564_, 16, v_a_5538_);
lean_ctor_set(v_reuseFailAlloc_5564_, 17, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5564_, 18, v_B_5539_);
lean_ctor_set(v_reuseFailAlloc_5564_, 19, v_h_5540_);
lean_ctor_set(v_reuseFailAlloc_5564_, 20, v_K_5541_);
lean_ctor_set(v_reuseFailAlloc_5564_, 21, v_k_5542_);
lean_ctor_set(v_reuseFailAlloc_5564_, 22, v_H_5543_);
lean_ctor_set(v_reuseFailAlloc_5564_, 23, v_m_5544_);
lean_ctor_set(v_reuseFailAlloc_5564_, 24, v_s_5545_);
lean_ctor_set(v_reuseFailAlloc_5564_, 25, v_S_5546_);
lean_ctor_set(v_reuseFailAlloc_5564_, 26, v_A_5547_);
lean_ctor_set(v_reuseFailAlloc_5564_, 27, v_n_5548_);
lean_ctor_set(v_reuseFailAlloc_5564_, 28, v_N_5549_);
lean_ctor_set(v_reuseFailAlloc_5564_, 29, v_V_5550_);
lean_ctor_set(v_reuseFailAlloc_5564_, 30, v_z_5551_);
lean_ctor_set(v_reuseFailAlloc_5564_, 31, v_zabbrev_5552_);
lean_ctor_set(v_reuseFailAlloc_5564_, 32, v_v_5553_);
lean_ctor_set(v_reuseFailAlloc_5564_, 33, v_O_5554_);
lean_ctor_set(v_reuseFailAlloc_5564_, 34, v_X_5555_);
lean_ctor_set(v_reuseFailAlloc_5564_, 35, v_x_5556_);
lean_ctor_set(v_reuseFailAlloc_5564_, 36, v_Z_5557_);
v___x_5563_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
return v___x_5563_;
}
}
}
case 18:
{
lean_object* v_G_5567_; lean_object* v_y_5568_; lean_object* v_u_5569_; lean_object* v_Y_5570_; lean_object* v_D_5571_; lean_object* v_M_5572_; lean_object* v_L_5573_; lean_object* v_d_5574_; lean_object* v_Q_5575_; lean_object* v_q_5576_; lean_object* v_w_5577_; lean_object* v_W_5578_; lean_object* v_E_5579_; lean_object* v_e_5580_; lean_object* v_c_5581_; lean_object* v_F_5582_; lean_object* v_a_5583_; lean_object* v_b_5584_; lean_object* v_h_5585_; lean_object* v_K_5586_; lean_object* v_k_5587_; lean_object* v_H_5588_; lean_object* v_m_5589_; lean_object* v_s_5590_; lean_object* v_S_5591_; lean_object* v_A_5592_; lean_object* v_n_5593_; lean_object* v_N_5594_; lean_object* v_V_5595_; lean_object* v_z_5596_; lean_object* v_zabbrev_5597_; lean_object* v_v_5598_; lean_object* v_O_5599_; lean_object* v_X_5600_; lean_object* v_x_5601_; lean_object* v_Z_5602_; lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5610_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_G_5567_ = lean_ctor_get(v_date_4656_, 0);
v_y_5568_ = lean_ctor_get(v_date_4656_, 1);
v_u_5569_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5570_ = lean_ctor_get(v_date_4656_, 3);
v_D_5571_ = lean_ctor_get(v_date_4656_, 4);
v_M_5572_ = lean_ctor_get(v_date_4656_, 5);
v_L_5573_ = lean_ctor_get(v_date_4656_, 6);
v_d_5574_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5575_ = lean_ctor_get(v_date_4656_, 8);
v_q_5576_ = lean_ctor_get(v_date_4656_, 9);
v_w_5577_ = lean_ctor_get(v_date_4656_, 10);
v_W_5578_ = lean_ctor_get(v_date_4656_, 11);
v_E_5579_ = lean_ctor_get(v_date_4656_, 12);
v_e_5580_ = lean_ctor_get(v_date_4656_, 13);
v_c_5581_ = lean_ctor_get(v_date_4656_, 14);
v_F_5582_ = lean_ctor_get(v_date_4656_, 15);
v_a_5583_ = lean_ctor_get(v_date_4656_, 16);
v_b_5584_ = lean_ctor_get(v_date_4656_, 17);
v_h_5585_ = lean_ctor_get(v_date_4656_, 19);
v_K_5586_ = lean_ctor_get(v_date_4656_, 20);
v_k_5587_ = lean_ctor_get(v_date_4656_, 21);
v_H_5588_ = lean_ctor_get(v_date_4656_, 22);
v_m_5589_ = lean_ctor_get(v_date_4656_, 23);
v_s_5590_ = lean_ctor_get(v_date_4656_, 24);
v_S_5591_ = lean_ctor_get(v_date_4656_, 25);
v_A_5592_ = lean_ctor_get(v_date_4656_, 26);
v_n_5593_ = lean_ctor_get(v_date_4656_, 27);
v_N_5594_ = lean_ctor_get(v_date_4656_, 28);
v_V_5595_ = lean_ctor_get(v_date_4656_, 29);
v_z_5596_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5597_ = lean_ctor_get(v_date_4656_, 31);
v_v_5598_ = lean_ctor_get(v_date_4656_, 32);
v_O_5599_ = lean_ctor_get(v_date_4656_, 33);
v_X_5600_ = lean_ctor_get(v_date_4656_, 34);
v_x_5601_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5602_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5610_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5610_ == 0)
{
lean_object* v_unused_5611_; 
v_unused_5611_ = lean_ctor_get(v_date_4656_, 18);
lean_dec(v_unused_5611_);
v___x_5604_ = v_date_4656_;
v_isShared_5605_ = v_isSharedCheck_5610_;
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
lean_inc(v_K_5586_);
lean_inc(v_h_5585_);
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
lean_dec(v_date_4656_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5610_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
lean_object* v___x_5606_; lean_object* v___x_5608_; 
v___x_5606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5606_, 0, v_data_4658_);
if (v_isShared_5605_ == 0)
{
lean_ctor_set(v___x_5604_, 18, v___x_5606_);
v___x_5608_ = v___x_5604_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_G_5567_);
lean_ctor_set(v_reuseFailAlloc_5609_, 1, v_y_5568_);
lean_ctor_set(v_reuseFailAlloc_5609_, 2, v_u_5569_);
lean_ctor_set(v_reuseFailAlloc_5609_, 3, v_Y_5570_);
lean_ctor_set(v_reuseFailAlloc_5609_, 4, v_D_5571_);
lean_ctor_set(v_reuseFailAlloc_5609_, 5, v_M_5572_);
lean_ctor_set(v_reuseFailAlloc_5609_, 6, v_L_5573_);
lean_ctor_set(v_reuseFailAlloc_5609_, 7, v_d_5574_);
lean_ctor_set(v_reuseFailAlloc_5609_, 8, v_Q_5575_);
lean_ctor_set(v_reuseFailAlloc_5609_, 9, v_q_5576_);
lean_ctor_set(v_reuseFailAlloc_5609_, 10, v_w_5577_);
lean_ctor_set(v_reuseFailAlloc_5609_, 11, v_W_5578_);
lean_ctor_set(v_reuseFailAlloc_5609_, 12, v_E_5579_);
lean_ctor_set(v_reuseFailAlloc_5609_, 13, v_e_5580_);
lean_ctor_set(v_reuseFailAlloc_5609_, 14, v_c_5581_);
lean_ctor_set(v_reuseFailAlloc_5609_, 15, v_F_5582_);
lean_ctor_set(v_reuseFailAlloc_5609_, 16, v_a_5583_);
lean_ctor_set(v_reuseFailAlloc_5609_, 17, v_b_5584_);
lean_ctor_set(v_reuseFailAlloc_5609_, 18, v___x_5606_);
lean_ctor_set(v_reuseFailAlloc_5609_, 19, v_h_5585_);
lean_ctor_set(v_reuseFailAlloc_5609_, 20, v_K_5586_);
lean_ctor_set(v_reuseFailAlloc_5609_, 21, v_k_5587_);
lean_ctor_set(v_reuseFailAlloc_5609_, 22, v_H_5588_);
lean_ctor_set(v_reuseFailAlloc_5609_, 23, v_m_5589_);
lean_ctor_set(v_reuseFailAlloc_5609_, 24, v_s_5590_);
lean_ctor_set(v_reuseFailAlloc_5609_, 25, v_S_5591_);
lean_ctor_set(v_reuseFailAlloc_5609_, 26, v_A_5592_);
lean_ctor_set(v_reuseFailAlloc_5609_, 27, v_n_5593_);
lean_ctor_set(v_reuseFailAlloc_5609_, 28, v_N_5594_);
lean_ctor_set(v_reuseFailAlloc_5609_, 29, v_V_5595_);
lean_ctor_set(v_reuseFailAlloc_5609_, 30, v_z_5596_);
lean_ctor_set(v_reuseFailAlloc_5609_, 31, v_zabbrev_5597_);
lean_ctor_set(v_reuseFailAlloc_5609_, 32, v_v_5598_);
lean_ctor_set(v_reuseFailAlloc_5609_, 33, v_O_5599_);
lean_ctor_set(v_reuseFailAlloc_5609_, 34, v_X_5600_);
lean_ctor_set(v_reuseFailAlloc_5609_, 35, v_x_5601_);
lean_ctor_set(v_reuseFailAlloc_5609_, 36, v_Z_5602_);
v___x_5608_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
return v___x_5608_;
}
}
}
case 19:
{
lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5662_; 
v_isSharedCheck_5662_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5662_ == 0)
{
lean_object* v_unused_5663_; 
v_unused_5663_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5663_);
v___x_5613_ = v_modifier_4657_;
v_isShared_5614_ = v_isSharedCheck_5662_;
goto v_resetjp_5612_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5662_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v_G_5615_; lean_object* v_y_5616_; lean_object* v_u_5617_; lean_object* v_Y_5618_; lean_object* v_D_5619_; lean_object* v_M_5620_; lean_object* v_L_5621_; lean_object* v_d_5622_; lean_object* v_Q_5623_; lean_object* v_q_5624_; lean_object* v_w_5625_; lean_object* v_W_5626_; lean_object* v_E_5627_; lean_object* v_e_5628_; lean_object* v_c_5629_; lean_object* v_F_5630_; lean_object* v_a_5631_; lean_object* v_b_5632_; lean_object* v_B_5633_; lean_object* v_K_5634_; lean_object* v_k_5635_; lean_object* v_H_5636_; lean_object* v_m_5637_; lean_object* v_s_5638_; lean_object* v_S_5639_; lean_object* v_A_5640_; lean_object* v_n_5641_; lean_object* v_N_5642_; lean_object* v_V_5643_; lean_object* v_z_5644_; lean_object* v_zabbrev_5645_; lean_object* v_v_5646_; lean_object* v_O_5647_; lean_object* v_X_5648_; lean_object* v_x_5649_; lean_object* v_Z_5650_; lean_object* v___x_5652_; uint8_t v_isShared_5653_; uint8_t v_isSharedCheck_5660_; 
v_G_5615_ = lean_ctor_get(v_date_4656_, 0);
v_y_5616_ = lean_ctor_get(v_date_4656_, 1);
v_u_5617_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5618_ = lean_ctor_get(v_date_4656_, 3);
v_D_5619_ = lean_ctor_get(v_date_4656_, 4);
v_M_5620_ = lean_ctor_get(v_date_4656_, 5);
v_L_5621_ = lean_ctor_get(v_date_4656_, 6);
v_d_5622_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5623_ = lean_ctor_get(v_date_4656_, 8);
v_q_5624_ = lean_ctor_get(v_date_4656_, 9);
v_w_5625_ = lean_ctor_get(v_date_4656_, 10);
v_W_5626_ = lean_ctor_get(v_date_4656_, 11);
v_E_5627_ = lean_ctor_get(v_date_4656_, 12);
v_e_5628_ = lean_ctor_get(v_date_4656_, 13);
v_c_5629_ = lean_ctor_get(v_date_4656_, 14);
v_F_5630_ = lean_ctor_get(v_date_4656_, 15);
v_a_5631_ = lean_ctor_get(v_date_4656_, 16);
v_b_5632_ = lean_ctor_get(v_date_4656_, 17);
v_B_5633_ = lean_ctor_get(v_date_4656_, 18);
v_K_5634_ = lean_ctor_get(v_date_4656_, 20);
v_k_5635_ = lean_ctor_get(v_date_4656_, 21);
v_H_5636_ = lean_ctor_get(v_date_4656_, 22);
v_m_5637_ = lean_ctor_get(v_date_4656_, 23);
v_s_5638_ = lean_ctor_get(v_date_4656_, 24);
v_S_5639_ = lean_ctor_get(v_date_4656_, 25);
v_A_5640_ = lean_ctor_get(v_date_4656_, 26);
v_n_5641_ = lean_ctor_get(v_date_4656_, 27);
v_N_5642_ = lean_ctor_get(v_date_4656_, 28);
v_V_5643_ = lean_ctor_get(v_date_4656_, 29);
v_z_5644_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5645_ = lean_ctor_get(v_date_4656_, 31);
v_v_5646_ = lean_ctor_get(v_date_4656_, 32);
v_O_5647_ = lean_ctor_get(v_date_4656_, 33);
v_X_5648_ = lean_ctor_get(v_date_4656_, 34);
v_x_5649_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5650_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5660_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5660_ == 0)
{
lean_object* v_unused_5661_; 
v_unused_5661_ = lean_ctor_get(v_date_4656_, 19);
lean_dec(v_unused_5661_);
v___x_5652_ = v_date_4656_;
v_isShared_5653_ = v_isSharedCheck_5660_;
goto v_resetjp_5651_;
}
else
{
lean_inc(v_Z_5650_);
lean_inc(v_x_5649_);
lean_inc(v_X_5648_);
lean_inc(v_O_5647_);
lean_inc(v_v_5646_);
lean_inc(v_zabbrev_5645_);
lean_inc(v_z_5644_);
lean_inc(v_V_5643_);
lean_inc(v_N_5642_);
lean_inc(v_n_5641_);
lean_inc(v_A_5640_);
lean_inc(v_S_5639_);
lean_inc(v_s_5638_);
lean_inc(v_m_5637_);
lean_inc(v_H_5636_);
lean_inc(v_k_5635_);
lean_inc(v_K_5634_);
lean_inc(v_B_5633_);
lean_inc(v_b_5632_);
lean_inc(v_a_5631_);
lean_inc(v_F_5630_);
lean_inc(v_c_5629_);
lean_inc(v_e_5628_);
lean_inc(v_E_5627_);
lean_inc(v_W_5626_);
lean_inc(v_w_5625_);
lean_inc(v_q_5624_);
lean_inc(v_Q_5623_);
lean_inc(v_d_5622_);
lean_inc(v_L_5621_);
lean_inc(v_M_5620_);
lean_inc(v_D_5619_);
lean_inc(v_Y_5618_);
lean_inc(v_u_5617_);
lean_inc(v_y_5616_);
lean_inc(v_G_5615_);
lean_dec(v_date_4656_);
v___x_5652_ = lean_box(0);
v_isShared_5653_ = v_isSharedCheck_5660_;
goto v_resetjp_5651_;
}
v_resetjp_5651_:
{
lean_object* v___x_5655_; 
if (v_isShared_5614_ == 0)
{
lean_ctor_set_tag(v___x_5613_, 1);
lean_ctor_set(v___x_5613_, 0, v_data_4658_);
v___x_5655_ = v___x_5613_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_data_4658_);
v___x_5655_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
lean_object* v___x_5657_; 
if (v_isShared_5653_ == 0)
{
lean_ctor_set(v___x_5652_, 19, v___x_5655_);
v___x_5657_ = v___x_5652_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5658_; 
v_reuseFailAlloc_5658_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_G_5615_);
lean_ctor_set(v_reuseFailAlloc_5658_, 1, v_y_5616_);
lean_ctor_set(v_reuseFailAlloc_5658_, 2, v_u_5617_);
lean_ctor_set(v_reuseFailAlloc_5658_, 3, v_Y_5618_);
lean_ctor_set(v_reuseFailAlloc_5658_, 4, v_D_5619_);
lean_ctor_set(v_reuseFailAlloc_5658_, 5, v_M_5620_);
lean_ctor_set(v_reuseFailAlloc_5658_, 6, v_L_5621_);
lean_ctor_set(v_reuseFailAlloc_5658_, 7, v_d_5622_);
lean_ctor_set(v_reuseFailAlloc_5658_, 8, v_Q_5623_);
lean_ctor_set(v_reuseFailAlloc_5658_, 9, v_q_5624_);
lean_ctor_set(v_reuseFailAlloc_5658_, 10, v_w_5625_);
lean_ctor_set(v_reuseFailAlloc_5658_, 11, v_W_5626_);
lean_ctor_set(v_reuseFailAlloc_5658_, 12, v_E_5627_);
lean_ctor_set(v_reuseFailAlloc_5658_, 13, v_e_5628_);
lean_ctor_set(v_reuseFailAlloc_5658_, 14, v_c_5629_);
lean_ctor_set(v_reuseFailAlloc_5658_, 15, v_F_5630_);
lean_ctor_set(v_reuseFailAlloc_5658_, 16, v_a_5631_);
lean_ctor_set(v_reuseFailAlloc_5658_, 17, v_b_5632_);
lean_ctor_set(v_reuseFailAlloc_5658_, 18, v_B_5633_);
lean_ctor_set(v_reuseFailAlloc_5658_, 19, v___x_5655_);
lean_ctor_set(v_reuseFailAlloc_5658_, 20, v_K_5634_);
lean_ctor_set(v_reuseFailAlloc_5658_, 21, v_k_5635_);
lean_ctor_set(v_reuseFailAlloc_5658_, 22, v_H_5636_);
lean_ctor_set(v_reuseFailAlloc_5658_, 23, v_m_5637_);
lean_ctor_set(v_reuseFailAlloc_5658_, 24, v_s_5638_);
lean_ctor_set(v_reuseFailAlloc_5658_, 25, v_S_5639_);
lean_ctor_set(v_reuseFailAlloc_5658_, 26, v_A_5640_);
lean_ctor_set(v_reuseFailAlloc_5658_, 27, v_n_5641_);
lean_ctor_set(v_reuseFailAlloc_5658_, 28, v_N_5642_);
lean_ctor_set(v_reuseFailAlloc_5658_, 29, v_V_5643_);
lean_ctor_set(v_reuseFailAlloc_5658_, 30, v_z_5644_);
lean_ctor_set(v_reuseFailAlloc_5658_, 31, v_zabbrev_5645_);
lean_ctor_set(v_reuseFailAlloc_5658_, 32, v_v_5646_);
lean_ctor_set(v_reuseFailAlloc_5658_, 33, v_O_5647_);
lean_ctor_set(v_reuseFailAlloc_5658_, 34, v_X_5648_);
lean_ctor_set(v_reuseFailAlloc_5658_, 35, v_x_5649_);
lean_ctor_set(v_reuseFailAlloc_5658_, 36, v_Z_5650_);
v___x_5657_ = v_reuseFailAlloc_5658_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
return v___x_5657_;
}
}
}
}
}
case 20:
{
lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5714_; 
v_isSharedCheck_5714_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5714_ == 0)
{
lean_object* v_unused_5715_; 
v_unused_5715_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5715_);
v___x_5665_ = v_modifier_4657_;
v_isShared_5666_ = v_isSharedCheck_5714_;
goto v_resetjp_5664_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5714_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v_G_5667_; lean_object* v_y_5668_; lean_object* v_u_5669_; lean_object* v_Y_5670_; lean_object* v_D_5671_; lean_object* v_M_5672_; lean_object* v_L_5673_; lean_object* v_d_5674_; lean_object* v_Q_5675_; lean_object* v_q_5676_; lean_object* v_w_5677_; lean_object* v_W_5678_; lean_object* v_E_5679_; lean_object* v_e_5680_; lean_object* v_c_5681_; lean_object* v_F_5682_; lean_object* v_a_5683_; lean_object* v_b_5684_; lean_object* v_B_5685_; lean_object* v_h_5686_; lean_object* v_k_5687_; lean_object* v_H_5688_; lean_object* v_m_5689_; lean_object* v_s_5690_; lean_object* v_S_5691_; lean_object* v_A_5692_; lean_object* v_n_5693_; lean_object* v_N_5694_; lean_object* v_V_5695_; lean_object* v_z_5696_; lean_object* v_zabbrev_5697_; lean_object* v_v_5698_; lean_object* v_O_5699_; lean_object* v_X_5700_; lean_object* v_x_5701_; lean_object* v_Z_5702_; lean_object* v___x_5704_; uint8_t v_isShared_5705_; uint8_t v_isSharedCheck_5712_; 
v_G_5667_ = lean_ctor_get(v_date_4656_, 0);
v_y_5668_ = lean_ctor_get(v_date_4656_, 1);
v_u_5669_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5670_ = lean_ctor_get(v_date_4656_, 3);
v_D_5671_ = lean_ctor_get(v_date_4656_, 4);
v_M_5672_ = lean_ctor_get(v_date_4656_, 5);
v_L_5673_ = lean_ctor_get(v_date_4656_, 6);
v_d_5674_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5675_ = lean_ctor_get(v_date_4656_, 8);
v_q_5676_ = lean_ctor_get(v_date_4656_, 9);
v_w_5677_ = lean_ctor_get(v_date_4656_, 10);
v_W_5678_ = lean_ctor_get(v_date_4656_, 11);
v_E_5679_ = lean_ctor_get(v_date_4656_, 12);
v_e_5680_ = lean_ctor_get(v_date_4656_, 13);
v_c_5681_ = lean_ctor_get(v_date_4656_, 14);
v_F_5682_ = lean_ctor_get(v_date_4656_, 15);
v_a_5683_ = lean_ctor_get(v_date_4656_, 16);
v_b_5684_ = lean_ctor_get(v_date_4656_, 17);
v_B_5685_ = lean_ctor_get(v_date_4656_, 18);
v_h_5686_ = lean_ctor_get(v_date_4656_, 19);
v_k_5687_ = lean_ctor_get(v_date_4656_, 21);
v_H_5688_ = lean_ctor_get(v_date_4656_, 22);
v_m_5689_ = lean_ctor_get(v_date_4656_, 23);
v_s_5690_ = lean_ctor_get(v_date_4656_, 24);
v_S_5691_ = lean_ctor_get(v_date_4656_, 25);
v_A_5692_ = lean_ctor_get(v_date_4656_, 26);
v_n_5693_ = lean_ctor_get(v_date_4656_, 27);
v_N_5694_ = lean_ctor_get(v_date_4656_, 28);
v_V_5695_ = lean_ctor_get(v_date_4656_, 29);
v_z_5696_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5697_ = lean_ctor_get(v_date_4656_, 31);
v_v_5698_ = lean_ctor_get(v_date_4656_, 32);
v_O_5699_ = lean_ctor_get(v_date_4656_, 33);
v_X_5700_ = lean_ctor_get(v_date_4656_, 34);
v_x_5701_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5702_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5712_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5712_ == 0)
{
lean_object* v_unused_5713_; 
v_unused_5713_ = lean_ctor_get(v_date_4656_, 20);
lean_dec(v_unused_5713_);
v___x_5704_ = v_date_4656_;
v_isShared_5705_ = v_isSharedCheck_5712_;
goto v_resetjp_5703_;
}
else
{
lean_inc(v_Z_5702_);
lean_inc(v_x_5701_);
lean_inc(v_X_5700_);
lean_inc(v_O_5699_);
lean_inc(v_v_5698_);
lean_inc(v_zabbrev_5697_);
lean_inc(v_z_5696_);
lean_inc(v_V_5695_);
lean_inc(v_N_5694_);
lean_inc(v_n_5693_);
lean_inc(v_A_5692_);
lean_inc(v_S_5691_);
lean_inc(v_s_5690_);
lean_inc(v_m_5689_);
lean_inc(v_H_5688_);
lean_inc(v_k_5687_);
lean_inc(v_h_5686_);
lean_inc(v_B_5685_);
lean_inc(v_b_5684_);
lean_inc(v_a_5683_);
lean_inc(v_F_5682_);
lean_inc(v_c_5681_);
lean_inc(v_e_5680_);
lean_inc(v_E_5679_);
lean_inc(v_W_5678_);
lean_inc(v_w_5677_);
lean_inc(v_q_5676_);
lean_inc(v_Q_5675_);
lean_inc(v_d_5674_);
lean_inc(v_L_5673_);
lean_inc(v_M_5672_);
lean_inc(v_D_5671_);
lean_inc(v_Y_5670_);
lean_inc(v_u_5669_);
lean_inc(v_y_5668_);
lean_inc(v_G_5667_);
lean_dec(v_date_4656_);
v___x_5704_ = lean_box(0);
v_isShared_5705_ = v_isSharedCheck_5712_;
goto v_resetjp_5703_;
}
v_resetjp_5703_:
{
lean_object* v___x_5707_; 
if (v_isShared_5666_ == 0)
{
lean_ctor_set_tag(v___x_5665_, 1);
lean_ctor_set(v___x_5665_, 0, v_data_4658_);
v___x_5707_ = v___x_5665_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5711_; 
v_reuseFailAlloc_5711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5711_, 0, v_data_4658_);
v___x_5707_ = v_reuseFailAlloc_5711_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
lean_object* v___x_5709_; 
if (v_isShared_5705_ == 0)
{
lean_ctor_set(v___x_5704_, 20, v___x_5707_);
v___x_5709_ = v___x_5704_;
goto v_reusejp_5708_;
}
else
{
lean_object* v_reuseFailAlloc_5710_; 
v_reuseFailAlloc_5710_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5710_, 0, v_G_5667_);
lean_ctor_set(v_reuseFailAlloc_5710_, 1, v_y_5668_);
lean_ctor_set(v_reuseFailAlloc_5710_, 2, v_u_5669_);
lean_ctor_set(v_reuseFailAlloc_5710_, 3, v_Y_5670_);
lean_ctor_set(v_reuseFailAlloc_5710_, 4, v_D_5671_);
lean_ctor_set(v_reuseFailAlloc_5710_, 5, v_M_5672_);
lean_ctor_set(v_reuseFailAlloc_5710_, 6, v_L_5673_);
lean_ctor_set(v_reuseFailAlloc_5710_, 7, v_d_5674_);
lean_ctor_set(v_reuseFailAlloc_5710_, 8, v_Q_5675_);
lean_ctor_set(v_reuseFailAlloc_5710_, 9, v_q_5676_);
lean_ctor_set(v_reuseFailAlloc_5710_, 10, v_w_5677_);
lean_ctor_set(v_reuseFailAlloc_5710_, 11, v_W_5678_);
lean_ctor_set(v_reuseFailAlloc_5710_, 12, v_E_5679_);
lean_ctor_set(v_reuseFailAlloc_5710_, 13, v_e_5680_);
lean_ctor_set(v_reuseFailAlloc_5710_, 14, v_c_5681_);
lean_ctor_set(v_reuseFailAlloc_5710_, 15, v_F_5682_);
lean_ctor_set(v_reuseFailAlloc_5710_, 16, v_a_5683_);
lean_ctor_set(v_reuseFailAlloc_5710_, 17, v_b_5684_);
lean_ctor_set(v_reuseFailAlloc_5710_, 18, v_B_5685_);
lean_ctor_set(v_reuseFailAlloc_5710_, 19, v_h_5686_);
lean_ctor_set(v_reuseFailAlloc_5710_, 20, v___x_5707_);
lean_ctor_set(v_reuseFailAlloc_5710_, 21, v_k_5687_);
lean_ctor_set(v_reuseFailAlloc_5710_, 22, v_H_5688_);
lean_ctor_set(v_reuseFailAlloc_5710_, 23, v_m_5689_);
lean_ctor_set(v_reuseFailAlloc_5710_, 24, v_s_5690_);
lean_ctor_set(v_reuseFailAlloc_5710_, 25, v_S_5691_);
lean_ctor_set(v_reuseFailAlloc_5710_, 26, v_A_5692_);
lean_ctor_set(v_reuseFailAlloc_5710_, 27, v_n_5693_);
lean_ctor_set(v_reuseFailAlloc_5710_, 28, v_N_5694_);
lean_ctor_set(v_reuseFailAlloc_5710_, 29, v_V_5695_);
lean_ctor_set(v_reuseFailAlloc_5710_, 30, v_z_5696_);
lean_ctor_set(v_reuseFailAlloc_5710_, 31, v_zabbrev_5697_);
lean_ctor_set(v_reuseFailAlloc_5710_, 32, v_v_5698_);
lean_ctor_set(v_reuseFailAlloc_5710_, 33, v_O_5699_);
lean_ctor_set(v_reuseFailAlloc_5710_, 34, v_X_5700_);
lean_ctor_set(v_reuseFailAlloc_5710_, 35, v_x_5701_);
lean_ctor_set(v_reuseFailAlloc_5710_, 36, v_Z_5702_);
v___x_5709_ = v_reuseFailAlloc_5710_;
goto v_reusejp_5708_;
}
v_reusejp_5708_:
{
return v___x_5709_;
}
}
}
}
}
case 21:
{
lean_object* v___x_5717_; uint8_t v_isShared_5718_; uint8_t v_isSharedCheck_5766_; 
v_isSharedCheck_5766_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5766_ == 0)
{
lean_object* v_unused_5767_; 
v_unused_5767_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5767_);
v___x_5717_ = v_modifier_4657_;
v_isShared_5718_ = v_isSharedCheck_5766_;
goto v_resetjp_5716_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5717_ = lean_box(0);
v_isShared_5718_ = v_isSharedCheck_5766_;
goto v_resetjp_5716_;
}
v_resetjp_5716_:
{
lean_object* v_G_5719_; lean_object* v_y_5720_; lean_object* v_u_5721_; lean_object* v_Y_5722_; lean_object* v_D_5723_; lean_object* v_M_5724_; lean_object* v_L_5725_; lean_object* v_d_5726_; lean_object* v_Q_5727_; lean_object* v_q_5728_; lean_object* v_w_5729_; lean_object* v_W_5730_; lean_object* v_E_5731_; lean_object* v_e_5732_; lean_object* v_c_5733_; lean_object* v_F_5734_; lean_object* v_a_5735_; lean_object* v_b_5736_; lean_object* v_B_5737_; lean_object* v_h_5738_; lean_object* v_K_5739_; lean_object* v_H_5740_; lean_object* v_m_5741_; lean_object* v_s_5742_; lean_object* v_S_5743_; lean_object* v_A_5744_; lean_object* v_n_5745_; lean_object* v_N_5746_; lean_object* v_V_5747_; lean_object* v_z_5748_; lean_object* v_zabbrev_5749_; lean_object* v_v_5750_; lean_object* v_O_5751_; lean_object* v_X_5752_; lean_object* v_x_5753_; lean_object* v_Z_5754_; lean_object* v___x_5756_; uint8_t v_isShared_5757_; uint8_t v_isSharedCheck_5764_; 
v_G_5719_ = lean_ctor_get(v_date_4656_, 0);
v_y_5720_ = lean_ctor_get(v_date_4656_, 1);
v_u_5721_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5722_ = lean_ctor_get(v_date_4656_, 3);
v_D_5723_ = lean_ctor_get(v_date_4656_, 4);
v_M_5724_ = lean_ctor_get(v_date_4656_, 5);
v_L_5725_ = lean_ctor_get(v_date_4656_, 6);
v_d_5726_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5727_ = lean_ctor_get(v_date_4656_, 8);
v_q_5728_ = lean_ctor_get(v_date_4656_, 9);
v_w_5729_ = lean_ctor_get(v_date_4656_, 10);
v_W_5730_ = lean_ctor_get(v_date_4656_, 11);
v_E_5731_ = lean_ctor_get(v_date_4656_, 12);
v_e_5732_ = lean_ctor_get(v_date_4656_, 13);
v_c_5733_ = lean_ctor_get(v_date_4656_, 14);
v_F_5734_ = lean_ctor_get(v_date_4656_, 15);
v_a_5735_ = lean_ctor_get(v_date_4656_, 16);
v_b_5736_ = lean_ctor_get(v_date_4656_, 17);
v_B_5737_ = lean_ctor_get(v_date_4656_, 18);
v_h_5738_ = lean_ctor_get(v_date_4656_, 19);
v_K_5739_ = lean_ctor_get(v_date_4656_, 20);
v_H_5740_ = lean_ctor_get(v_date_4656_, 22);
v_m_5741_ = lean_ctor_get(v_date_4656_, 23);
v_s_5742_ = lean_ctor_get(v_date_4656_, 24);
v_S_5743_ = lean_ctor_get(v_date_4656_, 25);
v_A_5744_ = lean_ctor_get(v_date_4656_, 26);
v_n_5745_ = lean_ctor_get(v_date_4656_, 27);
v_N_5746_ = lean_ctor_get(v_date_4656_, 28);
v_V_5747_ = lean_ctor_get(v_date_4656_, 29);
v_z_5748_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5749_ = lean_ctor_get(v_date_4656_, 31);
v_v_5750_ = lean_ctor_get(v_date_4656_, 32);
v_O_5751_ = lean_ctor_get(v_date_4656_, 33);
v_X_5752_ = lean_ctor_get(v_date_4656_, 34);
v_x_5753_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5754_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5764_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5764_ == 0)
{
lean_object* v_unused_5765_; 
v_unused_5765_ = lean_ctor_get(v_date_4656_, 21);
lean_dec(v_unused_5765_);
v___x_5756_ = v_date_4656_;
v_isShared_5757_ = v_isSharedCheck_5764_;
goto v_resetjp_5755_;
}
else
{
lean_inc(v_Z_5754_);
lean_inc(v_x_5753_);
lean_inc(v_X_5752_);
lean_inc(v_O_5751_);
lean_inc(v_v_5750_);
lean_inc(v_zabbrev_5749_);
lean_inc(v_z_5748_);
lean_inc(v_V_5747_);
lean_inc(v_N_5746_);
lean_inc(v_n_5745_);
lean_inc(v_A_5744_);
lean_inc(v_S_5743_);
lean_inc(v_s_5742_);
lean_inc(v_m_5741_);
lean_inc(v_H_5740_);
lean_inc(v_K_5739_);
lean_inc(v_h_5738_);
lean_inc(v_B_5737_);
lean_inc(v_b_5736_);
lean_inc(v_a_5735_);
lean_inc(v_F_5734_);
lean_inc(v_c_5733_);
lean_inc(v_e_5732_);
lean_inc(v_E_5731_);
lean_inc(v_W_5730_);
lean_inc(v_w_5729_);
lean_inc(v_q_5728_);
lean_inc(v_Q_5727_);
lean_inc(v_d_5726_);
lean_inc(v_L_5725_);
lean_inc(v_M_5724_);
lean_inc(v_D_5723_);
lean_inc(v_Y_5722_);
lean_inc(v_u_5721_);
lean_inc(v_y_5720_);
lean_inc(v_G_5719_);
lean_dec(v_date_4656_);
v___x_5756_ = lean_box(0);
v_isShared_5757_ = v_isSharedCheck_5764_;
goto v_resetjp_5755_;
}
v_resetjp_5755_:
{
lean_object* v___x_5759_; 
if (v_isShared_5718_ == 0)
{
lean_ctor_set_tag(v___x_5717_, 1);
lean_ctor_set(v___x_5717_, 0, v_data_4658_);
v___x_5759_ = v___x_5717_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_data_4658_);
v___x_5759_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
lean_object* v___x_5761_; 
if (v_isShared_5757_ == 0)
{
lean_ctor_set(v___x_5756_, 21, v___x_5759_);
v___x_5761_ = v___x_5756_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5762_; 
v_reuseFailAlloc_5762_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5762_, 0, v_G_5719_);
lean_ctor_set(v_reuseFailAlloc_5762_, 1, v_y_5720_);
lean_ctor_set(v_reuseFailAlloc_5762_, 2, v_u_5721_);
lean_ctor_set(v_reuseFailAlloc_5762_, 3, v_Y_5722_);
lean_ctor_set(v_reuseFailAlloc_5762_, 4, v_D_5723_);
lean_ctor_set(v_reuseFailAlloc_5762_, 5, v_M_5724_);
lean_ctor_set(v_reuseFailAlloc_5762_, 6, v_L_5725_);
lean_ctor_set(v_reuseFailAlloc_5762_, 7, v_d_5726_);
lean_ctor_set(v_reuseFailAlloc_5762_, 8, v_Q_5727_);
lean_ctor_set(v_reuseFailAlloc_5762_, 9, v_q_5728_);
lean_ctor_set(v_reuseFailAlloc_5762_, 10, v_w_5729_);
lean_ctor_set(v_reuseFailAlloc_5762_, 11, v_W_5730_);
lean_ctor_set(v_reuseFailAlloc_5762_, 12, v_E_5731_);
lean_ctor_set(v_reuseFailAlloc_5762_, 13, v_e_5732_);
lean_ctor_set(v_reuseFailAlloc_5762_, 14, v_c_5733_);
lean_ctor_set(v_reuseFailAlloc_5762_, 15, v_F_5734_);
lean_ctor_set(v_reuseFailAlloc_5762_, 16, v_a_5735_);
lean_ctor_set(v_reuseFailAlloc_5762_, 17, v_b_5736_);
lean_ctor_set(v_reuseFailAlloc_5762_, 18, v_B_5737_);
lean_ctor_set(v_reuseFailAlloc_5762_, 19, v_h_5738_);
lean_ctor_set(v_reuseFailAlloc_5762_, 20, v_K_5739_);
lean_ctor_set(v_reuseFailAlloc_5762_, 21, v___x_5759_);
lean_ctor_set(v_reuseFailAlloc_5762_, 22, v_H_5740_);
lean_ctor_set(v_reuseFailAlloc_5762_, 23, v_m_5741_);
lean_ctor_set(v_reuseFailAlloc_5762_, 24, v_s_5742_);
lean_ctor_set(v_reuseFailAlloc_5762_, 25, v_S_5743_);
lean_ctor_set(v_reuseFailAlloc_5762_, 26, v_A_5744_);
lean_ctor_set(v_reuseFailAlloc_5762_, 27, v_n_5745_);
lean_ctor_set(v_reuseFailAlloc_5762_, 28, v_N_5746_);
lean_ctor_set(v_reuseFailAlloc_5762_, 29, v_V_5747_);
lean_ctor_set(v_reuseFailAlloc_5762_, 30, v_z_5748_);
lean_ctor_set(v_reuseFailAlloc_5762_, 31, v_zabbrev_5749_);
lean_ctor_set(v_reuseFailAlloc_5762_, 32, v_v_5750_);
lean_ctor_set(v_reuseFailAlloc_5762_, 33, v_O_5751_);
lean_ctor_set(v_reuseFailAlloc_5762_, 34, v_X_5752_);
lean_ctor_set(v_reuseFailAlloc_5762_, 35, v_x_5753_);
lean_ctor_set(v_reuseFailAlloc_5762_, 36, v_Z_5754_);
v___x_5761_ = v_reuseFailAlloc_5762_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
return v___x_5761_;
}
}
}
}
}
case 22:
{
lean_object* v___x_5769_; uint8_t v_isShared_5770_; uint8_t v_isSharedCheck_5818_; 
v_isSharedCheck_5818_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5818_ == 0)
{
lean_object* v_unused_5819_; 
v_unused_5819_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5819_);
v___x_5769_ = v_modifier_4657_;
v_isShared_5770_ = v_isSharedCheck_5818_;
goto v_resetjp_5768_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5769_ = lean_box(0);
v_isShared_5770_ = v_isSharedCheck_5818_;
goto v_resetjp_5768_;
}
v_resetjp_5768_:
{
lean_object* v_G_5771_; lean_object* v_y_5772_; lean_object* v_u_5773_; lean_object* v_Y_5774_; lean_object* v_D_5775_; lean_object* v_M_5776_; lean_object* v_L_5777_; lean_object* v_d_5778_; lean_object* v_Q_5779_; lean_object* v_q_5780_; lean_object* v_w_5781_; lean_object* v_W_5782_; lean_object* v_E_5783_; lean_object* v_e_5784_; lean_object* v_c_5785_; lean_object* v_F_5786_; lean_object* v_a_5787_; lean_object* v_b_5788_; lean_object* v_B_5789_; lean_object* v_h_5790_; lean_object* v_K_5791_; lean_object* v_k_5792_; lean_object* v_m_5793_; lean_object* v_s_5794_; lean_object* v_S_5795_; lean_object* v_A_5796_; lean_object* v_n_5797_; lean_object* v_N_5798_; lean_object* v_V_5799_; lean_object* v_z_5800_; lean_object* v_zabbrev_5801_; lean_object* v_v_5802_; lean_object* v_O_5803_; lean_object* v_X_5804_; lean_object* v_x_5805_; lean_object* v_Z_5806_; lean_object* v___x_5808_; uint8_t v_isShared_5809_; uint8_t v_isSharedCheck_5816_; 
v_G_5771_ = lean_ctor_get(v_date_4656_, 0);
v_y_5772_ = lean_ctor_get(v_date_4656_, 1);
v_u_5773_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5774_ = lean_ctor_get(v_date_4656_, 3);
v_D_5775_ = lean_ctor_get(v_date_4656_, 4);
v_M_5776_ = lean_ctor_get(v_date_4656_, 5);
v_L_5777_ = lean_ctor_get(v_date_4656_, 6);
v_d_5778_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5779_ = lean_ctor_get(v_date_4656_, 8);
v_q_5780_ = lean_ctor_get(v_date_4656_, 9);
v_w_5781_ = lean_ctor_get(v_date_4656_, 10);
v_W_5782_ = lean_ctor_get(v_date_4656_, 11);
v_E_5783_ = lean_ctor_get(v_date_4656_, 12);
v_e_5784_ = lean_ctor_get(v_date_4656_, 13);
v_c_5785_ = lean_ctor_get(v_date_4656_, 14);
v_F_5786_ = lean_ctor_get(v_date_4656_, 15);
v_a_5787_ = lean_ctor_get(v_date_4656_, 16);
v_b_5788_ = lean_ctor_get(v_date_4656_, 17);
v_B_5789_ = lean_ctor_get(v_date_4656_, 18);
v_h_5790_ = lean_ctor_get(v_date_4656_, 19);
v_K_5791_ = lean_ctor_get(v_date_4656_, 20);
v_k_5792_ = lean_ctor_get(v_date_4656_, 21);
v_m_5793_ = lean_ctor_get(v_date_4656_, 23);
v_s_5794_ = lean_ctor_get(v_date_4656_, 24);
v_S_5795_ = lean_ctor_get(v_date_4656_, 25);
v_A_5796_ = lean_ctor_get(v_date_4656_, 26);
v_n_5797_ = lean_ctor_get(v_date_4656_, 27);
v_N_5798_ = lean_ctor_get(v_date_4656_, 28);
v_V_5799_ = lean_ctor_get(v_date_4656_, 29);
v_z_5800_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5801_ = lean_ctor_get(v_date_4656_, 31);
v_v_5802_ = lean_ctor_get(v_date_4656_, 32);
v_O_5803_ = lean_ctor_get(v_date_4656_, 33);
v_X_5804_ = lean_ctor_get(v_date_4656_, 34);
v_x_5805_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5806_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5816_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5816_ == 0)
{
lean_object* v_unused_5817_; 
v_unused_5817_ = lean_ctor_get(v_date_4656_, 22);
lean_dec(v_unused_5817_);
v___x_5808_ = v_date_4656_;
v_isShared_5809_ = v_isSharedCheck_5816_;
goto v_resetjp_5807_;
}
else
{
lean_inc(v_Z_5806_);
lean_inc(v_x_5805_);
lean_inc(v_X_5804_);
lean_inc(v_O_5803_);
lean_inc(v_v_5802_);
lean_inc(v_zabbrev_5801_);
lean_inc(v_z_5800_);
lean_inc(v_V_5799_);
lean_inc(v_N_5798_);
lean_inc(v_n_5797_);
lean_inc(v_A_5796_);
lean_inc(v_S_5795_);
lean_inc(v_s_5794_);
lean_inc(v_m_5793_);
lean_inc(v_k_5792_);
lean_inc(v_K_5791_);
lean_inc(v_h_5790_);
lean_inc(v_B_5789_);
lean_inc(v_b_5788_);
lean_inc(v_a_5787_);
lean_inc(v_F_5786_);
lean_inc(v_c_5785_);
lean_inc(v_e_5784_);
lean_inc(v_E_5783_);
lean_inc(v_W_5782_);
lean_inc(v_w_5781_);
lean_inc(v_q_5780_);
lean_inc(v_Q_5779_);
lean_inc(v_d_5778_);
lean_inc(v_L_5777_);
lean_inc(v_M_5776_);
lean_inc(v_D_5775_);
lean_inc(v_Y_5774_);
lean_inc(v_u_5773_);
lean_inc(v_y_5772_);
lean_inc(v_G_5771_);
lean_dec(v_date_4656_);
v___x_5808_ = lean_box(0);
v_isShared_5809_ = v_isSharedCheck_5816_;
goto v_resetjp_5807_;
}
v_resetjp_5807_:
{
lean_object* v___x_5811_; 
if (v_isShared_5770_ == 0)
{
lean_ctor_set_tag(v___x_5769_, 1);
lean_ctor_set(v___x_5769_, 0, v_data_4658_);
v___x_5811_ = v___x_5769_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5815_; 
v_reuseFailAlloc_5815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5815_, 0, v_data_4658_);
v___x_5811_ = v_reuseFailAlloc_5815_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
lean_object* v___x_5813_; 
if (v_isShared_5809_ == 0)
{
lean_ctor_set(v___x_5808_, 22, v___x_5811_);
v___x_5813_ = v___x_5808_;
goto v_reusejp_5812_;
}
else
{
lean_object* v_reuseFailAlloc_5814_; 
v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5814_, 0, v_G_5771_);
lean_ctor_set(v_reuseFailAlloc_5814_, 1, v_y_5772_);
lean_ctor_set(v_reuseFailAlloc_5814_, 2, v_u_5773_);
lean_ctor_set(v_reuseFailAlloc_5814_, 3, v_Y_5774_);
lean_ctor_set(v_reuseFailAlloc_5814_, 4, v_D_5775_);
lean_ctor_set(v_reuseFailAlloc_5814_, 5, v_M_5776_);
lean_ctor_set(v_reuseFailAlloc_5814_, 6, v_L_5777_);
lean_ctor_set(v_reuseFailAlloc_5814_, 7, v_d_5778_);
lean_ctor_set(v_reuseFailAlloc_5814_, 8, v_Q_5779_);
lean_ctor_set(v_reuseFailAlloc_5814_, 9, v_q_5780_);
lean_ctor_set(v_reuseFailAlloc_5814_, 10, v_w_5781_);
lean_ctor_set(v_reuseFailAlloc_5814_, 11, v_W_5782_);
lean_ctor_set(v_reuseFailAlloc_5814_, 12, v_E_5783_);
lean_ctor_set(v_reuseFailAlloc_5814_, 13, v_e_5784_);
lean_ctor_set(v_reuseFailAlloc_5814_, 14, v_c_5785_);
lean_ctor_set(v_reuseFailAlloc_5814_, 15, v_F_5786_);
lean_ctor_set(v_reuseFailAlloc_5814_, 16, v_a_5787_);
lean_ctor_set(v_reuseFailAlloc_5814_, 17, v_b_5788_);
lean_ctor_set(v_reuseFailAlloc_5814_, 18, v_B_5789_);
lean_ctor_set(v_reuseFailAlloc_5814_, 19, v_h_5790_);
lean_ctor_set(v_reuseFailAlloc_5814_, 20, v_K_5791_);
lean_ctor_set(v_reuseFailAlloc_5814_, 21, v_k_5792_);
lean_ctor_set(v_reuseFailAlloc_5814_, 22, v___x_5811_);
lean_ctor_set(v_reuseFailAlloc_5814_, 23, v_m_5793_);
lean_ctor_set(v_reuseFailAlloc_5814_, 24, v_s_5794_);
lean_ctor_set(v_reuseFailAlloc_5814_, 25, v_S_5795_);
lean_ctor_set(v_reuseFailAlloc_5814_, 26, v_A_5796_);
lean_ctor_set(v_reuseFailAlloc_5814_, 27, v_n_5797_);
lean_ctor_set(v_reuseFailAlloc_5814_, 28, v_N_5798_);
lean_ctor_set(v_reuseFailAlloc_5814_, 29, v_V_5799_);
lean_ctor_set(v_reuseFailAlloc_5814_, 30, v_z_5800_);
lean_ctor_set(v_reuseFailAlloc_5814_, 31, v_zabbrev_5801_);
lean_ctor_set(v_reuseFailAlloc_5814_, 32, v_v_5802_);
lean_ctor_set(v_reuseFailAlloc_5814_, 33, v_O_5803_);
lean_ctor_set(v_reuseFailAlloc_5814_, 34, v_X_5804_);
lean_ctor_set(v_reuseFailAlloc_5814_, 35, v_x_5805_);
lean_ctor_set(v_reuseFailAlloc_5814_, 36, v_Z_5806_);
v___x_5813_ = v_reuseFailAlloc_5814_;
goto v_reusejp_5812_;
}
v_reusejp_5812_:
{
return v___x_5813_;
}
}
}
}
}
case 23:
{
lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5870_; 
v_isSharedCheck_5870_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5870_ == 0)
{
lean_object* v_unused_5871_; 
v_unused_5871_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5871_);
v___x_5821_ = v_modifier_4657_;
v_isShared_5822_ = v_isSharedCheck_5870_;
goto v_resetjp_5820_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5821_ = lean_box(0);
v_isShared_5822_ = v_isSharedCheck_5870_;
goto v_resetjp_5820_;
}
v_resetjp_5820_:
{
lean_object* v_G_5823_; lean_object* v_y_5824_; lean_object* v_u_5825_; lean_object* v_Y_5826_; lean_object* v_D_5827_; lean_object* v_M_5828_; lean_object* v_L_5829_; lean_object* v_d_5830_; lean_object* v_Q_5831_; lean_object* v_q_5832_; lean_object* v_w_5833_; lean_object* v_W_5834_; lean_object* v_E_5835_; lean_object* v_e_5836_; lean_object* v_c_5837_; lean_object* v_F_5838_; lean_object* v_a_5839_; lean_object* v_b_5840_; lean_object* v_B_5841_; lean_object* v_h_5842_; lean_object* v_K_5843_; lean_object* v_k_5844_; lean_object* v_H_5845_; lean_object* v_s_5846_; lean_object* v_S_5847_; lean_object* v_A_5848_; lean_object* v_n_5849_; lean_object* v_N_5850_; lean_object* v_V_5851_; lean_object* v_z_5852_; lean_object* v_zabbrev_5853_; lean_object* v_v_5854_; lean_object* v_O_5855_; lean_object* v_X_5856_; lean_object* v_x_5857_; lean_object* v_Z_5858_; lean_object* v___x_5860_; uint8_t v_isShared_5861_; uint8_t v_isSharedCheck_5868_; 
v_G_5823_ = lean_ctor_get(v_date_4656_, 0);
v_y_5824_ = lean_ctor_get(v_date_4656_, 1);
v_u_5825_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5826_ = lean_ctor_get(v_date_4656_, 3);
v_D_5827_ = lean_ctor_get(v_date_4656_, 4);
v_M_5828_ = lean_ctor_get(v_date_4656_, 5);
v_L_5829_ = lean_ctor_get(v_date_4656_, 6);
v_d_5830_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5831_ = lean_ctor_get(v_date_4656_, 8);
v_q_5832_ = lean_ctor_get(v_date_4656_, 9);
v_w_5833_ = lean_ctor_get(v_date_4656_, 10);
v_W_5834_ = lean_ctor_get(v_date_4656_, 11);
v_E_5835_ = lean_ctor_get(v_date_4656_, 12);
v_e_5836_ = lean_ctor_get(v_date_4656_, 13);
v_c_5837_ = lean_ctor_get(v_date_4656_, 14);
v_F_5838_ = lean_ctor_get(v_date_4656_, 15);
v_a_5839_ = lean_ctor_get(v_date_4656_, 16);
v_b_5840_ = lean_ctor_get(v_date_4656_, 17);
v_B_5841_ = lean_ctor_get(v_date_4656_, 18);
v_h_5842_ = lean_ctor_get(v_date_4656_, 19);
v_K_5843_ = lean_ctor_get(v_date_4656_, 20);
v_k_5844_ = lean_ctor_get(v_date_4656_, 21);
v_H_5845_ = lean_ctor_get(v_date_4656_, 22);
v_s_5846_ = lean_ctor_get(v_date_4656_, 24);
v_S_5847_ = lean_ctor_get(v_date_4656_, 25);
v_A_5848_ = lean_ctor_get(v_date_4656_, 26);
v_n_5849_ = lean_ctor_get(v_date_4656_, 27);
v_N_5850_ = lean_ctor_get(v_date_4656_, 28);
v_V_5851_ = lean_ctor_get(v_date_4656_, 29);
v_z_5852_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5853_ = lean_ctor_get(v_date_4656_, 31);
v_v_5854_ = lean_ctor_get(v_date_4656_, 32);
v_O_5855_ = lean_ctor_get(v_date_4656_, 33);
v_X_5856_ = lean_ctor_get(v_date_4656_, 34);
v_x_5857_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5858_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5868_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5868_ == 0)
{
lean_object* v_unused_5869_; 
v_unused_5869_ = lean_ctor_get(v_date_4656_, 23);
lean_dec(v_unused_5869_);
v___x_5860_ = v_date_4656_;
v_isShared_5861_ = v_isSharedCheck_5868_;
goto v_resetjp_5859_;
}
else
{
lean_inc(v_Z_5858_);
lean_inc(v_x_5857_);
lean_inc(v_X_5856_);
lean_inc(v_O_5855_);
lean_inc(v_v_5854_);
lean_inc(v_zabbrev_5853_);
lean_inc(v_z_5852_);
lean_inc(v_V_5851_);
lean_inc(v_N_5850_);
lean_inc(v_n_5849_);
lean_inc(v_A_5848_);
lean_inc(v_S_5847_);
lean_inc(v_s_5846_);
lean_inc(v_H_5845_);
lean_inc(v_k_5844_);
lean_inc(v_K_5843_);
lean_inc(v_h_5842_);
lean_inc(v_B_5841_);
lean_inc(v_b_5840_);
lean_inc(v_a_5839_);
lean_inc(v_F_5838_);
lean_inc(v_c_5837_);
lean_inc(v_e_5836_);
lean_inc(v_E_5835_);
lean_inc(v_W_5834_);
lean_inc(v_w_5833_);
lean_inc(v_q_5832_);
lean_inc(v_Q_5831_);
lean_inc(v_d_5830_);
lean_inc(v_L_5829_);
lean_inc(v_M_5828_);
lean_inc(v_D_5827_);
lean_inc(v_Y_5826_);
lean_inc(v_u_5825_);
lean_inc(v_y_5824_);
lean_inc(v_G_5823_);
lean_dec(v_date_4656_);
v___x_5860_ = lean_box(0);
v_isShared_5861_ = v_isSharedCheck_5868_;
goto v_resetjp_5859_;
}
v_resetjp_5859_:
{
lean_object* v___x_5863_; 
if (v_isShared_5822_ == 0)
{
lean_ctor_set_tag(v___x_5821_, 1);
lean_ctor_set(v___x_5821_, 0, v_data_4658_);
v___x_5863_ = v___x_5821_;
goto v_reusejp_5862_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_data_4658_);
v___x_5863_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5862_;
}
v_reusejp_5862_:
{
lean_object* v___x_5865_; 
if (v_isShared_5861_ == 0)
{
lean_ctor_set(v___x_5860_, 23, v___x_5863_);
v___x_5865_ = v___x_5860_;
goto v_reusejp_5864_;
}
else
{
lean_object* v_reuseFailAlloc_5866_; 
v_reuseFailAlloc_5866_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_G_5823_);
lean_ctor_set(v_reuseFailAlloc_5866_, 1, v_y_5824_);
lean_ctor_set(v_reuseFailAlloc_5866_, 2, v_u_5825_);
lean_ctor_set(v_reuseFailAlloc_5866_, 3, v_Y_5826_);
lean_ctor_set(v_reuseFailAlloc_5866_, 4, v_D_5827_);
lean_ctor_set(v_reuseFailAlloc_5866_, 5, v_M_5828_);
lean_ctor_set(v_reuseFailAlloc_5866_, 6, v_L_5829_);
lean_ctor_set(v_reuseFailAlloc_5866_, 7, v_d_5830_);
lean_ctor_set(v_reuseFailAlloc_5866_, 8, v_Q_5831_);
lean_ctor_set(v_reuseFailAlloc_5866_, 9, v_q_5832_);
lean_ctor_set(v_reuseFailAlloc_5866_, 10, v_w_5833_);
lean_ctor_set(v_reuseFailAlloc_5866_, 11, v_W_5834_);
lean_ctor_set(v_reuseFailAlloc_5866_, 12, v_E_5835_);
lean_ctor_set(v_reuseFailAlloc_5866_, 13, v_e_5836_);
lean_ctor_set(v_reuseFailAlloc_5866_, 14, v_c_5837_);
lean_ctor_set(v_reuseFailAlloc_5866_, 15, v_F_5838_);
lean_ctor_set(v_reuseFailAlloc_5866_, 16, v_a_5839_);
lean_ctor_set(v_reuseFailAlloc_5866_, 17, v_b_5840_);
lean_ctor_set(v_reuseFailAlloc_5866_, 18, v_B_5841_);
lean_ctor_set(v_reuseFailAlloc_5866_, 19, v_h_5842_);
lean_ctor_set(v_reuseFailAlloc_5866_, 20, v_K_5843_);
lean_ctor_set(v_reuseFailAlloc_5866_, 21, v_k_5844_);
lean_ctor_set(v_reuseFailAlloc_5866_, 22, v_H_5845_);
lean_ctor_set(v_reuseFailAlloc_5866_, 23, v___x_5863_);
lean_ctor_set(v_reuseFailAlloc_5866_, 24, v_s_5846_);
lean_ctor_set(v_reuseFailAlloc_5866_, 25, v_S_5847_);
lean_ctor_set(v_reuseFailAlloc_5866_, 26, v_A_5848_);
lean_ctor_set(v_reuseFailAlloc_5866_, 27, v_n_5849_);
lean_ctor_set(v_reuseFailAlloc_5866_, 28, v_N_5850_);
lean_ctor_set(v_reuseFailAlloc_5866_, 29, v_V_5851_);
lean_ctor_set(v_reuseFailAlloc_5866_, 30, v_z_5852_);
lean_ctor_set(v_reuseFailAlloc_5866_, 31, v_zabbrev_5853_);
lean_ctor_set(v_reuseFailAlloc_5866_, 32, v_v_5854_);
lean_ctor_set(v_reuseFailAlloc_5866_, 33, v_O_5855_);
lean_ctor_set(v_reuseFailAlloc_5866_, 34, v_X_5856_);
lean_ctor_set(v_reuseFailAlloc_5866_, 35, v_x_5857_);
lean_ctor_set(v_reuseFailAlloc_5866_, 36, v_Z_5858_);
v___x_5865_ = v_reuseFailAlloc_5866_;
goto v_reusejp_5864_;
}
v_reusejp_5864_:
{
return v___x_5865_;
}
}
}
}
}
case 24:
{
lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5922_; 
v_isSharedCheck_5922_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5922_ == 0)
{
lean_object* v_unused_5923_; 
v_unused_5923_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5923_);
v___x_5873_ = v_modifier_4657_;
v_isShared_5874_ = v_isSharedCheck_5922_;
goto v_resetjp_5872_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5922_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v_G_5875_; lean_object* v_y_5876_; lean_object* v_u_5877_; lean_object* v_Y_5878_; lean_object* v_D_5879_; lean_object* v_M_5880_; lean_object* v_L_5881_; lean_object* v_d_5882_; lean_object* v_Q_5883_; lean_object* v_q_5884_; lean_object* v_w_5885_; lean_object* v_W_5886_; lean_object* v_E_5887_; lean_object* v_e_5888_; lean_object* v_c_5889_; lean_object* v_F_5890_; lean_object* v_a_5891_; lean_object* v_b_5892_; lean_object* v_B_5893_; lean_object* v_h_5894_; lean_object* v_K_5895_; lean_object* v_k_5896_; lean_object* v_H_5897_; lean_object* v_m_5898_; lean_object* v_S_5899_; lean_object* v_A_5900_; lean_object* v_n_5901_; lean_object* v_N_5902_; lean_object* v_V_5903_; lean_object* v_z_5904_; lean_object* v_zabbrev_5905_; lean_object* v_v_5906_; lean_object* v_O_5907_; lean_object* v_X_5908_; lean_object* v_x_5909_; lean_object* v_Z_5910_; lean_object* v___x_5912_; uint8_t v_isShared_5913_; uint8_t v_isSharedCheck_5920_; 
v_G_5875_ = lean_ctor_get(v_date_4656_, 0);
v_y_5876_ = lean_ctor_get(v_date_4656_, 1);
v_u_5877_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5878_ = lean_ctor_get(v_date_4656_, 3);
v_D_5879_ = lean_ctor_get(v_date_4656_, 4);
v_M_5880_ = lean_ctor_get(v_date_4656_, 5);
v_L_5881_ = lean_ctor_get(v_date_4656_, 6);
v_d_5882_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5883_ = lean_ctor_get(v_date_4656_, 8);
v_q_5884_ = lean_ctor_get(v_date_4656_, 9);
v_w_5885_ = lean_ctor_get(v_date_4656_, 10);
v_W_5886_ = lean_ctor_get(v_date_4656_, 11);
v_E_5887_ = lean_ctor_get(v_date_4656_, 12);
v_e_5888_ = lean_ctor_get(v_date_4656_, 13);
v_c_5889_ = lean_ctor_get(v_date_4656_, 14);
v_F_5890_ = lean_ctor_get(v_date_4656_, 15);
v_a_5891_ = lean_ctor_get(v_date_4656_, 16);
v_b_5892_ = lean_ctor_get(v_date_4656_, 17);
v_B_5893_ = lean_ctor_get(v_date_4656_, 18);
v_h_5894_ = lean_ctor_get(v_date_4656_, 19);
v_K_5895_ = lean_ctor_get(v_date_4656_, 20);
v_k_5896_ = lean_ctor_get(v_date_4656_, 21);
v_H_5897_ = lean_ctor_get(v_date_4656_, 22);
v_m_5898_ = lean_ctor_get(v_date_4656_, 23);
v_S_5899_ = lean_ctor_get(v_date_4656_, 25);
v_A_5900_ = lean_ctor_get(v_date_4656_, 26);
v_n_5901_ = lean_ctor_get(v_date_4656_, 27);
v_N_5902_ = lean_ctor_get(v_date_4656_, 28);
v_V_5903_ = lean_ctor_get(v_date_4656_, 29);
v_z_5904_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5905_ = lean_ctor_get(v_date_4656_, 31);
v_v_5906_ = lean_ctor_get(v_date_4656_, 32);
v_O_5907_ = lean_ctor_get(v_date_4656_, 33);
v_X_5908_ = lean_ctor_get(v_date_4656_, 34);
v_x_5909_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5910_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5920_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5920_ == 0)
{
lean_object* v_unused_5921_; 
v_unused_5921_ = lean_ctor_get(v_date_4656_, 24);
lean_dec(v_unused_5921_);
v___x_5912_ = v_date_4656_;
v_isShared_5913_ = v_isSharedCheck_5920_;
goto v_resetjp_5911_;
}
else
{
lean_inc(v_Z_5910_);
lean_inc(v_x_5909_);
lean_inc(v_X_5908_);
lean_inc(v_O_5907_);
lean_inc(v_v_5906_);
lean_inc(v_zabbrev_5905_);
lean_inc(v_z_5904_);
lean_inc(v_V_5903_);
lean_inc(v_N_5902_);
lean_inc(v_n_5901_);
lean_inc(v_A_5900_);
lean_inc(v_S_5899_);
lean_inc(v_m_5898_);
lean_inc(v_H_5897_);
lean_inc(v_k_5896_);
lean_inc(v_K_5895_);
lean_inc(v_h_5894_);
lean_inc(v_B_5893_);
lean_inc(v_b_5892_);
lean_inc(v_a_5891_);
lean_inc(v_F_5890_);
lean_inc(v_c_5889_);
lean_inc(v_e_5888_);
lean_inc(v_E_5887_);
lean_inc(v_W_5886_);
lean_inc(v_w_5885_);
lean_inc(v_q_5884_);
lean_inc(v_Q_5883_);
lean_inc(v_d_5882_);
lean_inc(v_L_5881_);
lean_inc(v_M_5880_);
lean_inc(v_D_5879_);
lean_inc(v_Y_5878_);
lean_inc(v_u_5877_);
lean_inc(v_y_5876_);
lean_inc(v_G_5875_);
lean_dec(v_date_4656_);
v___x_5912_ = lean_box(0);
v_isShared_5913_ = v_isSharedCheck_5920_;
goto v_resetjp_5911_;
}
v_resetjp_5911_:
{
lean_object* v___x_5915_; 
if (v_isShared_5874_ == 0)
{
lean_ctor_set_tag(v___x_5873_, 1);
lean_ctor_set(v___x_5873_, 0, v_data_4658_);
v___x_5915_ = v___x_5873_;
goto v_reusejp_5914_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_data_4658_);
v___x_5915_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5914_;
}
v_reusejp_5914_:
{
lean_object* v___x_5917_; 
if (v_isShared_5913_ == 0)
{
lean_ctor_set(v___x_5912_, 24, v___x_5915_);
v___x_5917_ = v___x_5912_;
goto v_reusejp_5916_;
}
else
{
lean_object* v_reuseFailAlloc_5918_; 
v_reuseFailAlloc_5918_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5918_, 0, v_G_5875_);
lean_ctor_set(v_reuseFailAlloc_5918_, 1, v_y_5876_);
lean_ctor_set(v_reuseFailAlloc_5918_, 2, v_u_5877_);
lean_ctor_set(v_reuseFailAlloc_5918_, 3, v_Y_5878_);
lean_ctor_set(v_reuseFailAlloc_5918_, 4, v_D_5879_);
lean_ctor_set(v_reuseFailAlloc_5918_, 5, v_M_5880_);
lean_ctor_set(v_reuseFailAlloc_5918_, 6, v_L_5881_);
lean_ctor_set(v_reuseFailAlloc_5918_, 7, v_d_5882_);
lean_ctor_set(v_reuseFailAlloc_5918_, 8, v_Q_5883_);
lean_ctor_set(v_reuseFailAlloc_5918_, 9, v_q_5884_);
lean_ctor_set(v_reuseFailAlloc_5918_, 10, v_w_5885_);
lean_ctor_set(v_reuseFailAlloc_5918_, 11, v_W_5886_);
lean_ctor_set(v_reuseFailAlloc_5918_, 12, v_E_5887_);
lean_ctor_set(v_reuseFailAlloc_5918_, 13, v_e_5888_);
lean_ctor_set(v_reuseFailAlloc_5918_, 14, v_c_5889_);
lean_ctor_set(v_reuseFailAlloc_5918_, 15, v_F_5890_);
lean_ctor_set(v_reuseFailAlloc_5918_, 16, v_a_5891_);
lean_ctor_set(v_reuseFailAlloc_5918_, 17, v_b_5892_);
lean_ctor_set(v_reuseFailAlloc_5918_, 18, v_B_5893_);
lean_ctor_set(v_reuseFailAlloc_5918_, 19, v_h_5894_);
lean_ctor_set(v_reuseFailAlloc_5918_, 20, v_K_5895_);
lean_ctor_set(v_reuseFailAlloc_5918_, 21, v_k_5896_);
lean_ctor_set(v_reuseFailAlloc_5918_, 22, v_H_5897_);
lean_ctor_set(v_reuseFailAlloc_5918_, 23, v_m_5898_);
lean_ctor_set(v_reuseFailAlloc_5918_, 24, v___x_5915_);
lean_ctor_set(v_reuseFailAlloc_5918_, 25, v_S_5899_);
lean_ctor_set(v_reuseFailAlloc_5918_, 26, v_A_5900_);
lean_ctor_set(v_reuseFailAlloc_5918_, 27, v_n_5901_);
lean_ctor_set(v_reuseFailAlloc_5918_, 28, v_N_5902_);
lean_ctor_set(v_reuseFailAlloc_5918_, 29, v_V_5903_);
lean_ctor_set(v_reuseFailAlloc_5918_, 30, v_z_5904_);
lean_ctor_set(v_reuseFailAlloc_5918_, 31, v_zabbrev_5905_);
lean_ctor_set(v_reuseFailAlloc_5918_, 32, v_v_5906_);
lean_ctor_set(v_reuseFailAlloc_5918_, 33, v_O_5907_);
lean_ctor_set(v_reuseFailAlloc_5918_, 34, v_X_5908_);
lean_ctor_set(v_reuseFailAlloc_5918_, 35, v_x_5909_);
lean_ctor_set(v_reuseFailAlloc_5918_, 36, v_Z_5910_);
v___x_5917_ = v_reuseFailAlloc_5918_;
goto v_reusejp_5916_;
}
v_reusejp_5916_:
{
return v___x_5917_;
}
}
}
}
}
case 25:
{
lean_object* v___x_5925_; uint8_t v_isShared_5926_; uint8_t v_isSharedCheck_5974_; 
v_isSharedCheck_5974_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_5974_ == 0)
{
lean_object* v_unused_5975_; 
v_unused_5975_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_5975_);
v___x_5925_ = v_modifier_4657_;
v_isShared_5926_ = v_isSharedCheck_5974_;
goto v_resetjp_5924_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5925_ = lean_box(0);
v_isShared_5926_ = v_isSharedCheck_5974_;
goto v_resetjp_5924_;
}
v_resetjp_5924_:
{
lean_object* v_G_5927_; lean_object* v_y_5928_; lean_object* v_u_5929_; lean_object* v_Y_5930_; lean_object* v_D_5931_; lean_object* v_M_5932_; lean_object* v_L_5933_; lean_object* v_d_5934_; lean_object* v_Q_5935_; lean_object* v_q_5936_; lean_object* v_w_5937_; lean_object* v_W_5938_; lean_object* v_E_5939_; lean_object* v_e_5940_; lean_object* v_c_5941_; lean_object* v_F_5942_; lean_object* v_a_5943_; lean_object* v_b_5944_; lean_object* v_B_5945_; lean_object* v_h_5946_; lean_object* v_K_5947_; lean_object* v_k_5948_; lean_object* v_H_5949_; lean_object* v_m_5950_; lean_object* v_s_5951_; lean_object* v_A_5952_; lean_object* v_n_5953_; lean_object* v_N_5954_; lean_object* v_V_5955_; lean_object* v_z_5956_; lean_object* v_zabbrev_5957_; lean_object* v_v_5958_; lean_object* v_O_5959_; lean_object* v_X_5960_; lean_object* v_x_5961_; lean_object* v_Z_5962_; lean_object* v___x_5964_; uint8_t v_isShared_5965_; uint8_t v_isSharedCheck_5972_; 
v_G_5927_ = lean_ctor_get(v_date_4656_, 0);
v_y_5928_ = lean_ctor_get(v_date_4656_, 1);
v_u_5929_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5930_ = lean_ctor_get(v_date_4656_, 3);
v_D_5931_ = lean_ctor_get(v_date_4656_, 4);
v_M_5932_ = lean_ctor_get(v_date_4656_, 5);
v_L_5933_ = lean_ctor_get(v_date_4656_, 6);
v_d_5934_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5935_ = lean_ctor_get(v_date_4656_, 8);
v_q_5936_ = lean_ctor_get(v_date_4656_, 9);
v_w_5937_ = lean_ctor_get(v_date_4656_, 10);
v_W_5938_ = lean_ctor_get(v_date_4656_, 11);
v_E_5939_ = lean_ctor_get(v_date_4656_, 12);
v_e_5940_ = lean_ctor_get(v_date_4656_, 13);
v_c_5941_ = lean_ctor_get(v_date_4656_, 14);
v_F_5942_ = lean_ctor_get(v_date_4656_, 15);
v_a_5943_ = lean_ctor_get(v_date_4656_, 16);
v_b_5944_ = lean_ctor_get(v_date_4656_, 17);
v_B_5945_ = lean_ctor_get(v_date_4656_, 18);
v_h_5946_ = lean_ctor_get(v_date_4656_, 19);
v_K_5947_ = lean_ctor_get(v_date_4656_, 20);
v_k_5948_ = lean_ctor_get(v_date_4656_, 21);
v_H_5949_ = lean_ctor_get(v_date_4656_, 22);
v_m_5950_ = lean_ctor_get(v_date_4656_, 23);
v_s_5951_ = lean_ctor_get(v_date_4656_, 24);
v_A_5952_ = lean_ctor_get(v_date_4656_, 26);
v_n_5953_ = lean_ctor_get(v_date_4656_, 27);
v_N_5954_ = lean_ctor_get(v_date_4656_, 28);
v_V_5955_ = lean_ctor_get(v_date_4656_, 29);
v_z_5956_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_5957_ = lean_ctor_get(v_date_4656_, 31);
v_v_5958_ = lean_ctor_get(v_date_4656_, 32);
v_O_5959_ = lean_ctor_get(v_date_4656_, 33);
v_X_5960_ = lean_ctor_get(v_date_4656_, 34);
v_x_5961_ = lean_ctor_get(v_date_4656_, 35);
v_Z_5962_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_5972_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_5972_ == 0)
{
lean_object* v_unused_5973_; 
v_unused_5973_ = lean_ctor_get(v_date_4656_, 25);
lean_dec(v_unused_5973_);
v___x_5964_ = v_date_4656_;
v_isShared_5965_ = v_isSharedCheck_5972_;
goto v_resetjp_5963_;
}
else
{
lean_inc(v_Z_5962_);
lean_inc(v_x_5961_);
lean_inc(v_X_5960_);
lean_inc(v_O_5959_);
lean_inc(v_v_5958_);
lean_inc(v_zabbrev_5957_);
lean_inc(v_z_5956_);
lean_inc(v_V_5955_);
lean_inc(v_N_5954_);
lean_inc(v_n_5953_);
lean_inc(v_A_5952_);
lean_inc(v_s_5951_);
lean_inc(v_m_5950_);
lean_inc(v_H_5949_);
lean_inc(v_k_5948_);
lean_inc(v_K_5947_);
lean_inc(v_h_5946_);
lean_inc(v_B_5945_);
lean_inc(v_b_5944_);
lean_inc(v_a_5943_);
lean_inc(v_F_5942_);
lean_inc(v_c_5941_);
lean_inc(v_e_5940_);
lean_inc(v_E_5939_);
lean_inc(v_W_5938_);
lean_inc(v_w_5937_);
lean_inc(v_q_5936_);
lean_inc(v_Q_5935_);
lean_inc(v_d_5934_);
lean_inc(v_L_5933_);
lean_inc(v_M_5932_);
lean_inc(v_D_5931_);
lean_inc(v_Y_5930_);
lean_inc(v_u_5929_);
lean_inc(v_y_5928_);
lean_inc(v_G_5927_);
lean_dec(v_date_4656_);
v___x_5964_ = lean_box(0);
v_isShared_5965_ = v_isSharedCheck_5972_;
goto v_resetjp_5963_;
}
v_resetjp_5963_:
{
lean_object* v___x_5967_; 
if (v_isShared_5926_ == 0)
{
lean_ctor_set_tag(v___x_5925_, 1);
lean_ctor_set(v___x_5925_, 0, v_data_4658_);
v___x_5967_ = v___x_5925_;
goto v_reusejp_5966_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v_data_4658_);
v___x_5967_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5966_;
}
v_reusejp_5966_:
{
lean_object* v___x_5969_; 
if (v_isShared_5965_ == 0)
{
lean_ctor_set(v___x_5964_, 25, v___x_5967_);
v___x_5969_ = v___x_5964_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_G_5927_);
lean_ctor_set(v_reuseFailAlloc_5970_, 1, v_y_5928_);
lean_ctor_set(v_reuseFailAlloc_5970_, 2, v_u_5929_);
lean_ctor_set(v_reuseFailAlloc_5970_, 3, v_Y_5930_);
lean_ctor_set(v_reuseFailAlloc_5970_, 4, v_D_5931_);
lean_ctor_set(v_reuseFailAlloc_5970_, 5, v_M_5932_);
lean_ctor_set(v_reuseFailAlloc_5970_, 6, v_L_5933_);
lean_ctor_set(v_reuseFailAlloc_5970_, 7, v_d_5934_);
lean_ctor_set(v_reuseFailAlloc_5970_, 8, v_Q_5935_);
lean_ctor_set(v_reuseFailAlloc_5970_, 9, v_q_5936_);
lean_ctor_set(v_reuseFailAlloc_5970_, 10, v_w_5937_);
lean_ctor_set(v_reuseFailAlloc_5970_, 11, v_W_5938_);
lean_ctor_set(v_reuseFailAlloc_5970_, 12, v_E_5939_);
lean_ctor_set(v_reuseFailAlloc_5970_, 13, v_e_5940_);
lean_ctor_set(v_reuseFailAlloc_5970_, 14, v_c_5941_);
lean_ctor_set(v_reuseFailAlloc_5970_, 15, v_F_5942_);
lean_ctor_set(v_reuseFailAlloc_5970_, 16, v_a_5943_);
lean_ctor_set(v_reuseFailAlloc_5970_, 17, v_b_5944_);
lean_ctor_set(v_reuseFailAlloc_5970_, 18, v_B_5945_);
lean_ctor_set(v_reuseFailAlloc_5970_, 19, v_h_5946_);
lean_ctor_set(v_reuseFailAlloc_5970_, 20, v_K_5947_);
lean_ctor_set(v_reuseFailAlloc_5970_, 21, v_k_5948_);
lean_ctor_set(v_reuseFailAlloc_5970_, 22, v_H_5949_);
lean_ctor_set(v_reuseFailAlloc_5970_, 23, v_m_5950_);
lean_ctor_set(v_reuseFailAlloc_5970_, 24, v_s_5951_);
lean_ctor_set(v_reuseFailAlloc_5970_, 25, v___x_5967_);
lean_ctor_set(v_reuseFailAlloc_5970_, 26, v_A_5952_);
lean_ctor_set(v_reuseFailAlloc_5970_, 27, v_n_5953_);
lean_ctor_set(v_reuseFailAlloc_5970_, 28, v_N_5954_);
lean_ctor_set(v_reuseFailAlloc_5970_, 29, v_V_5955_);
lean_ctor_set(v_reuseFailAlloc_5970_, 30, v_z_5956_);
lean_ctor_set(v_reuseFailAlloc_5970_, 31, v_zabbrev_5957_);
lean_ctor_set(v_reuseFailAlloc_5970_, 32, v_v_5958_);
lean_ctor_set(v_reuseFailAlloc_5970_, 33, v_O_5959_);
lean_ctor_set(v_reuseFailAlloc_5970_, 34, v_X_5960_);
lean_ctor_set(v_reuseFailAlloc_5970_, 35, v_x_5961_);
lean_ctor_set(v_reuseFailAlloc_5970_, 36, v_Z_5962_);
v___x_5969_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
return v___x_5969_;
}
}
}
}
}
case 26:
{
lean_object* v___x_5977_; uint8_t v_isShared_5978_; uint8_t v_isSharedCheck_6026_; 
v_isSharedCheck_6026_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_6026_ == 0)
{
lean_object* v_unused_6027_; 
v_unused_6027_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_6027_);
v___x_5977_ = v_modifier_4657_;
v_isShared_5978_ = v_isSharedCheck_6026_;
goto v_resetjp_5976_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_5977_ = lean_box(0);
v_isShared_5978_ = v_isSharedCheck_6026_;
goto v_resetjp_5976_;
}
v_resetjp_5976_:
{
lean_object* v_G_5979_; lean_object* v_y_5980_; lean_object* v_u_5981_; lean_object* v_Y_5982_; lean_object* v_D_5983_; lean_object* v_M_5984_; lean_object* v_L_5985_; lean_object* v_d_5986_; lean_object* v_Q_5987_; lean_object* v_q_5988_; lean_object* v_w_5989_; lean_object* v_W_5990_; lean_object* v_E_5991_; lean_object* v_e_5992_; lean_object* v_c_5993_; lean_object* v_F_5994_; lean_object* v_a_5995_; lean_object* v_b_5996_; lean_object* v_B_5997_; lean_object* v_h_5998_; lean_object* v_K_5999_; lean_object* v_k_6000_; lean_object* v_H_6001_; lean_object* v_m_6002_; lean_object* v_s_6003_; lean_object* v_S_6004_; lean_object* v_n_6005_; lean_object* v_N_6006_; lean_object* v_V_6007_; lean_object* v_z_6008_; lean_object* v_zabbrev_6009_; lean_object* v_v_6010_; lean_object* v_O_6011_; lean_object* v_X_6012_; lean_object* v_x_6013_; lean_object* v_Z_6014_; lean_object* v___x_6016_; uint8_t v_isShared_6017_; uint8_t v_isSharedCheck_6024_; 
v_G_5979_ = lean_ctor_get(v_date_4656_, 0);
v_y_5980_ = lean_ctor_get(v_date_4656_, 1);
v_u_5981_ = lean_ctor_get(v_date_4656_, 2);
v_Y_5982_ = lean_ctor_get(v_date_4656_, 3);
v_D_5983_ = lean_ctor_get(v_date_4656_, 4);
v_M_5984_ = lean_ctor_get(v_date_4656_, 5);
v_L_5985_ = lean_ctor_get(v_date_4656_, 6);
v_d_5986_ = lean_ctor_get(v_date_4656_, 7);
v_Q_5987_ = lean_ctor_get(v_date_4656_, 8);
v_q_5988_ = lean_ctor_get(v_date_4656_, 9);
v_w_5989_ = lean_ctor_get(v_date_4656_, 10);
v_W_5990_ = lean_ctor_get(v_date_4656_, 11);
v_E_5991_ = lean_ctor_get(v_date_4656_, 12);
v_e_5992_ = lean_ctor_get(v_date_4656_, 13);
v_c_5993_ = lean_ctor_get(v_date_4656_, 14);
v_F_5994_ = lean_ctor_get(v_date_4656_, 15);
v_a_5995_ = lean_ctor_get(v_date_4656_, 16);
v_b_5996_ = lean_ctor_get(v_date_4656_, 17);
v_B_5997_ = lean_ctor_get(v_date_4656_, 18);
v_h_5998_ = lean_ctor_get(v_date_4656_, 19);
v_K_5999_ = lean_ctor_get(v_date_4656_, 20);
v_k_6000_ = lean_ctor_get(v_date_4656_, 21);
v_H_6001_ = lean_ctor_get(v_date_4656_, 22);
v_m_6002_ = lean_ctor_get(v_date_4656_, 23);
v_s_6003_ = lean_ctor_get(v_date_4656_, 24);
v_S_6004_ = lean_ctor_get(v_date_4656_, 25);
v_n_6005_ = lean_ctor_get(v_date_4656_, 27);
v_N_6006_ = lean_ctor_get(v_date_4656_, 28);
v_V_6007_ = lean_ctor_get(v_date_4656_, 29);
v_z_6008_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_6009_ = lean_ctor_get(v_date_4656_, 31);
v_v_6010_ = lean_ctor_get(v_date_4656_, 32);
v_O_6011_ = lean_ctor_get(v_date_4656_, 33);
v_X_6012_ = lean_ctor_get(v_date_4656_, 34);
v_x_6013_ = lean_ctor_get(v_date_4656_, 35);
v_Z_6014_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_6024_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6024_ == 0)
{
lean_object* v_unused_6025_; 
v_unused_6025_ = lean_ctor_get(v_date_4656_, 26);
lean_dec(v_unused_6025_);
v___x_6016_ = v_date_4656_;
v_isShared_6017_ = v_isSharedCheck_6024_;
goto v_resetjp_6015_;
}
else
{
lean_inc(v_Z_6014_);
lean_inc(v_x_6013_);
lean_inc(v_X_6012_);
lean_inc(v_O_6011_);
lean_inc(v_v_6010_);
lean_inc(v_zabbrev_6009_);
lean_inc(v_z_6008_);
lean_inc(v_V_6007_);
lean_inc(v_N_6006_);
lean_inc(v_n_6005_);
lean_inc(v_S_6004_);
lean_inc(v_s_6003_);
lean_inc(v_m_6002_);
lean_inc(v_H_6001_);
lean_inc(v_k_6000_);
lean_inc(v_K_5999_);
lean_inc(v_h_5998_);
lean_inc(v_B_5997_);
lean_inc(v_b_5996_);
lean_inc(v_a_5995_);
lean_inc(v_F_5994_);
lean_inc(v_c_5993_);
lean_inc(v_e_5992_);
lean_inc(v_E_5991_);
lean_inc(v_W_5990_);
lean_inc(v_w_5989_);
lean_inc(v_q_5988_);
lean_inc(v_Q_5987_);
lean_inc(v_d_5986_);
lean_inc(v_L_5985_);
lean_inc(v_M_5984_);
lean_inc(v_D_5983_);
lean_inc(v_Y_5982_);
lean_inc(v_u_5981_);
lean_inc(v_y_5980_);
lean_inc(v_G_5979_);
lean_dec(v_date_4656_);
v___x_6016_ = lean_box(0);
v_isShared_6017_ = v_isSharedCheck_6024_;
goto v_resetjp_6015_;
}
v_resetjp_6015_:
{
lean_object* v___x_6019_; 
if (v_isShared_5978_ == 0)
{
lean_ctor_set_tag(v___x_5977_, 1);
lean_ctor_set(v___x_5977_, 0, v_data_4658_);
v___x_6019_ = v___x_5977_;
goto v_reusejp_6018_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_data_4658_);
v___x_6019_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6018_;
}
v_reusejp_6018_:
{
lean_object* v___x_6021_; 
if (v_isShared_6017_ == 0)
{
lean_ctor_set(v___x_6016_, 26, v___x_6019_);
v___x_6021_ = v___x_6016_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_G_5979_);
lean_ctor_set(v_reuseFailAlloc_6022_, 1, v_y_5980_);
lean_ctor_set(v_reuseFailAlloc_6022_, 2, v_u_5981_);
lean_ctor_set(v_reuseFailAlloc_6022_, 3, v_Y_5982_);
lean_ctor_set(v_reuseFailAlloc_6022_, 4, v_D_5983_);
lean_ctor_set(v_reuseFailAlloc_6022_, 5, v_M_5984_);
lean_ctor_set(v_reuseFailAlloc_6022_, 6, v_L_5985_);
lean_ctor_set(v_reuseFailAlloc_6022_, 7, v_d_5986_);
lean_ctor_set(v_reuseFailAlloc_6022_, 8, v_Q_5987_);
lean_ctor_set(v_reuseFailAlloc_6022_, 9, v_q_5988_);
lean_ctor_set(v_reuseFailAlloc_6022_, 10, v_w_5989_);
lean_ctor_set(v_reuseFailAlloc_6022_, 11, v_W_5990_);
lean_ctor_set(v_reuseFailAlloc_6022_, 12, v_E_5991_);
lean_ctor_set(v_reuseFailAlloc_6022_, 13, v_e_5992_);
lean_ctor_set(v_reuseFailAlloc_6022_, 14, v_c_5993_);
lean_ctor_set(v_reuseFailAlloc_6022_, 15, v_F_5994_);
lean_ctor_set(v_reuseFailAlloc_6022_, 16, v_a_5995_);
lean_ctor_set(v_reuseFailAlloc_6022_, 17, v_b_5996_);
lean_ctor_set(v_reuseFailAlloc_6022_, 18, v_B_5997_);
lean_ctor_set(v_reuseFailAlloc_6022_, 19, v_h_5998_);
lean_ctor_set(v_reuseFailAlloc_6022_, 20, v_K_5999_);
lean_ctor_set(v_reuseFailAlloc_6022_, 21, v_k_6000_);
lean_ctor_set(v_reuseFailAlloc_6022_, 22, v_H_6001_);
lean_ctor_set(v_reuseFailAlloc_6022_, 23, v_m_6002_);
lean_ctor_set(v_reuseFailAlloc_6022_, 24, v_s_6003_);
lean_ctor_set(v_reuseFailAlloc_6022_, 25, v_S_6004_);
lean_ctor_set(v_reuseFailAlloc_6022_, 26, v___x_6019_);
lean_ctor_set(v_reuseFailAlloc_6022_, 27, v_n_6005_);
lean_ctor_set(v_reuseFailAlloc_6022_, 28, v_N_6006_);
lean_ctor_set(v_reuseFailAlloc_6022_, 29, v_V_6007_);
lean_ctor_set(v_reuseFailAlloc_6022_, 30, v_z_6008_);
lean_ctor_set(v_reuseFailAlloc_6022_, 31, v_zabbrev_6009_);
lean_ctor_set(v_reuseFailAlloc_6022_, 32, v_v_6010_);
lean_ctor_set(v_reuseFailAlloc_6022_, 33, v_O_6011_);
lean_ctor_set(v_reuseFailAlloc_6022_, 34, v_X_6012_);
lean_ctor_set(v_reuseFailAlloc_6022_, 35, v_x_6013_);
lean_ctor_set(v_reuseFailAlloc_6022_, 36, v_Z_6014_);
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
}
case 27:
{
lean_object* v___x_6029_; uint8_t v_isShared_6030_; uint8_t v_isSharedCheck_6078_; 
v_isSharedCheck_6078_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_6078_ == 0)
{
lean_object* v_unused_6079_; 
v_unused_6079_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_6079_);
v___x_6029_ = v_modifier_4657_;
v_isShared_6030_ = v_isSharedCheck_6078_;
goto v_resetjp_6028_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_6029_ = lean_box(0);
v_isShared_6030_ = v_isSharedCheck_6078_;
goto v_resetjp_6028_;
}
v_resetjp_6028_:
{
lean_object* v_G_6031_; lean_object* v_y_6032_; lean_object* v_u_6033_; lean_object* v_Y_6034_; lean_object* v_D_6035_; lean_object* v_M_6036_; lean_object* v_L_6037_; lean_object* v_d_6038_; lean_object* v_Q_6039_; lean_object* v_q_6040_; lean_object* v_w_6041_; lean_object* v_W_6042_; lean_object* v_E_6043_; lean_object* v_e_6044_; lean_object* v_c_6045_; lean_object* v_F_6046_; lean_object* v_a_6047_; lean_object* v_b_6048_; lean_object* v_B_6049_; lean_object* v_h_6050_; lean_object* v_K_6051_; lean_object* v_k_6052_; lean_object* v_H_6053_; lean_object* v_m_6054_; lean_object* v_s_6055_; lean_object* v_S_6056_; lean_object* v_A_6057_; lean_object* v_N_6058_; lean_object* v_V_6059_; lean_object* v_z_6060_; lean_object* v_zabbrev_6061_; lean_object* v_v_6062_; lean_object* v_O_6063_; lean_object* v_X_6064_; lean_object* v_x_6065_; lean_object* v_Z_6066_; lean_object* v___x_6068_; uint8_t v_isShared_6069_; uint8_t v_isSharedCheck_6076_; 
v_G_6031_ = lean_ctor_get(v_date_4656_, 0);
v_y_6032_ = lean_ctor_get(v_date_4656_, 1);
v_u_6033_ = lean_ctor_get(v_date_4656_, 2);
v_Y_6034_ = lean_ctor_get(v_date_4656_, 3);
v_D_6035_ = lean_ctor_get(v_date_4656_, 4);
v_M_6036_ = lean_ctor_get(v_date_4656_, 5);
v_L_6037_ = lean_ctor_get(v_date_4656_, 6);
v_d_6038_ = lean_ctor_get(v_date_4656_, 7);
v_Q_6039_ = lean_ctor_get(v_date_4656_, 8);
v_q_6040_ = lean_ctor_get(v_date_4656_, 9);
v_w_6041_ = lean_ctor_get(v_date_4656_, 10);
v_W_6042_ = lean_ctor_get(v_date_4656_, 11);
v_E_6043_ = lean_ctor_get(v_date_4656_, 12);
v_e_6044_ = lean_ctor_get(v_date_4656_, 13);
v_c_6045_ = lean_ctor_get(v_date_4656_, 14);
v_F_6046_ = lean_ctor_get(v_date_4656_, 15);
v_a_6047_ = lean_ctor_get(v_date_4656_, 16);
v_b_6048_ = lean_ctor_get(v_date_4656_, 17);
v_B_6049_ = lean_ctor_get(v_date_4656_, 18);
v_h_6050_ = lean_ctor_get(v_date_4656_, 19);
v_K_6051_ = lean_ctor_get(v_date_4656_, 20);
v_k_6052_ = lean_ctor_get(v_date_4656_, 21);
v_H_6053_ = lean_ctor_get(v_date_4656_, 22);
v_m_6054_ = lean_ctor_get(v_date_4656_, 23);
v_s_6055_ = lean_ctor_get(v_date_4656_, 24);
v_S_6056_ = lean_ctor_get(v_date_4656_, 25);
v_A_6057_ = lean_ctor_get(v_date_4656_, 26);
v_N_6058_ = lean_ctor_get(v_date_4656_, 28);
v_V_6059_ = lean_ctor_get(v_date_4656_, 29);
v_z_6060_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_6061_ = lean_ctor_get(v_date_4656_, 31);
v_v_6062_ = lean_ctor_get(v_date_4656_, 32);
v_O_6063_ = lean_ctor_get(v_date_4656_, 33);
v_X_6064_ = lean_ctor_get(v_date_4656_, 34);
v_x_6065_ = lean_ctor_get(v_date_4656_, 35);
v_Z_6066_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_6076_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6076_ == 0)
{
lean_object* v_unused_6077_; 
v_unused_6077_ = lean_ctor_get(v_date_4656_, 27);
lean_dec(v_unused_6077_);
v___x_6068_ = v_date_4656_;
v_isShared_6069_ = v_isSharedCheck_6076_;
goto v_resetjp_6067_;
}
else
{
lean_inc(v_Z_6066_);
lean_inc(v_x_6065_);
lean_inc(v_X_6064_);
lean_inc(v_O_6063_);
lean_inc(v_v_6062_);
lean_inc(v_zabbrev_6061_);
lean_inc(v_z_6060_);
lean_inc(v_V_6059_);
lean_inc(v_N_6058_);
lean_inc(v_A_6057_);
lean_inc(v_S_6056_);
lean_inc(v_s_6055_);
lean_inc(v_m_6054_);
lean_inc(v_H_6053_);
lean_inc(v_k_6052_);
lean_inc(v_K_6051_);
lean_inc(v_h_6050_);
lean_inc(v_B_6049_);
lean_inc(v_b_6048_);
lean_inc(v_a_6047_);
lean_inc(v_F_6046_);
lean_inc(v_c_6045_);
lean_inc(v_e_6044_);
lean_inc(v_E_6043_);
lean_inc(v_W_6042_);
lean_inc(v_w_6041_);
lean_inc(v_q_6040_);
lean_inc(v_Q_6039_);
lean_inc(v_d_6038_);
lean_inc(v_L_6037_);
lean_inc(v_M_6036_);
lean_inc(v_D_6035_);
lean_inc(v_Y_6034_);
lean_inc(v_u_6033_);
lean_inc(v_y_6032_);
lean_inc(v_G_6031_);
lean_dec(v_date_4656_);
v___x_6068_ = lean_box(0);
v_isShared_6069_ = v_isSharedCheck_6076_;
goto v_resetjp_6067_;
}
v_resetjp_6067_:
{
lean_object* v___x_6071_; 
if (v_isShared_6030_ == 0)
{
lean_ctor_set_tag(v___x_6029_, 1);
lean_ctor_set(v___x_6029_, 0, v_data_4658_);
v___x_6071_ = v___x_6029_;
goto v_reusejp_6070_;
}
else
{
lean_object* v_reuseFailAlloc_6075_; 
v_reuseFailAlloc_6075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6075_, 0, v_data_4658_);
v___x_6071_ = v_reuseFailAlloc_6075_;
goto v_reusejp_6070_;
}
v_reusejp_6070_:
{
lean_object* v___x_6073_; 
if (v_isShared_6069_ == 0)
{
lean_ctor_set(v___x_6068_, 27, v___x_6071_);
v___x_6073_ = v___x_6068_;
goto v_reusejp_6072_;
}
else
{
lean_object* v_reuseFailAlloc_6074_; 
v_reuseFailAlloc_6074_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_G_6031_);
lean_ctor_set(v_reuseFailAlloc_6074_, 1, v_y_6032_);
lean_ctor_set(v_reuseFailAlloc_6074_, 2, v_u_6033_);
lean_ctor_set(v_reuseFailAlloc_6074_, 3, v_Y_6034_);
lean_ctor_set(v_reuseFailAlloc_6074_, 4, v_D_6035_);
lean_ctor_set(v_reuseFailAlloc_6074_, 5, v_M_6036_);
lean_ctor_set(v_reuseFailAlloc_6074_, 6, v_L_6037_);
lean_ctor_set(v_reuseFailAlloc_6074_, 7, v_d_6038_);
lean_ctor_set(v_reuseFailAlloc_6074_, 8, v_Q_6039_);
lean_ctor_set(v_reuseFailAlloc_6074_, 9, v_q_6040_);
lean_ctor_set(v_reuseFailAlloc_6074_, 10, v_w_6041_);
lean_ctor_set(v_reuseFailAlloc_6074_, 11, v_W_6042_);
lean_ctor_set(v_reuseFailAlloc_6074_, 12, v_E_6043_);
lean_ctor_set(v_reuseFailAlloc_6074_, 13, v_e_6044_);
lean_ctor_set(v_reuseFailAlloc_6074_, 14, v_c_6045_);
lean_ctor_set(v_reuseFailAlloc_6074_, 15, v_F_6046_);
lean_ctor_set(v_reuseFailAlloc_6074_, 16, v_a_6047_);
lean_ctor_set(v_reuseFailAlloc_6074_, 17, v_b_6048_);
lean_ctor_set(v_reuseFailAlloc_6074_, 18, v_B_6049_);
lean_ctor_set(v_reuseFailAlloc_6074_, 19, v_h_6050_);
lean_ctor_set(v_reuseFailAlloc_6074_, 20, v_K_6051_);
lean_ctor_set(v_reuseFailAlloc_6074_, 21, v_k_6052_);
lean_ctor_set(v_reuseFailAlloc_6074_, 22, v_H_6053_);
lean_ctor_set(v_reuseFailAlloc_6074_, 23, v_m_6054_);
lean_ctor_set(v_reuseFailAlloc_6074_, 24, v_s_6055_);
lean_ctor_set(v_reuseFailAlloc_6074_, 25, v_S_6056_);
lean_ctor_set(v_reuseFailAlloc_6074_, 26, v_A_6057_);
lean_ctor_set(v_reuseFailAlloc_6074_, 27, v___x_6071_);
lean_ctor_set(v_reuseFailAlloc_6074_, 28, v_N_6058_);
lean_ctor_set(v_reuseFailAlloc_6074_, 29, v_V_6059_);
lean_ctor_set(v_reuseFailAlloc_6074_, 30, v_z_6060_);
lean_ctor_set(v_reuseFailAlloc_6074_, 31, v_zabbrev_6061_);
lean_ctor_set(v_reuseFailAlloc_6074_, 32, v_v_6062_);
lean_ctor_set(v_reuseFailAlloc_6074_, 33, v_O_6063_);
lean_ctor_set(v_reuseFailAlloc_6074_, 34, v_X_6064_);
lean_ctor_set(v_reuseFailAlloc_6074_, 35, v_x_6065_);
lean_ctor_set(v_reuseFailAlloc_6074_, 36, v_Z_6066_);
v___x_6073_ = v_reuseFailAlloc_6074_;
goto v_reusejp_6072_;
}
v_reusejp_6072_:
{
return v___x_6073_;
}
}
}
}
}
case 28:
{
lean_object* v___x_6081_; uint8_t v_isShared_6082_; uint8_t v_isSharedCheck_6130_; 
v_isSharedCheck_6130_ = !lean_is_exclusive(v_modifier_4657_);
if (v_isSharedCheck_6130_ == 0)
{
lean_object* v_unused_6131_; 
v_unused_6131_ = lean_ctor_get(v_modifier_4657_, 0);
lean_dec(v_unused_6131_);
v___x_6081_ = v_modifier_4657_;
v_isShared_6082_ = v_isSharedCheck_6130_;
goto v_resetjp_6080_;
}
else
{
lean_dec(v_modifier_4657_);
v___x_6081_ = lean_box(0);
v_isShared_6082_ = v_isSharedCheck_6130_;
goto v_resetjp_6080_;
}
v_resetjp_6080_:
{
lean_object* v_G_6083_; lean_object* v_y_6084_; lean_object* v_u_6085_; lean_object* v_Y_6086_; lean_object* v_D_6087_; lean_object* v_M_6088_; lean_object* v_L_6089_; lean_object* v_d_6090_; lean_object* v_Q_6091_; lean_object* v_q_6092_; lean_object* v_w_6093_; lean_object* v_W_6094_; lean_object* v_E_6095_; lean_object* v_e_6096_; lean_object* v_c_6097_; lean_object* v_F_6098_; lean_object* v_a_6099_; lean_object* v_b_6100_; lean_object* v_B_6101_; lean_object* v_h_6102_; lean_object* v_K_6103_; lean_object* v_k_6104_; lean_object* v_H_6105_; lean_object* v_m_6106_; lean_object* v_s_6107_; lean_object* v_S_6108_; lean_object* v_A_6109_; lean_object* v_n_6110_; lean_object* v_V_6111_; lean_object* v_z_6112_; lean_object* v_zabbrev_6113_; lean_object* v_v_6114_; lean_object* v_O_6115_; lean_object* v_X_6116_; lean_object* v_x_6117_; lean_object* v_Z_6118_; lean_object* v___x_6120_; uint8_t v_isShared_6121_; uint8_t v_isSharedCheck_6128_; 
v_G_6083_ = lean_ctor_get(v_date_4656_, 0);
v_y_6084_ = lean_ctor_get(v_date_4656_, 1);
v_u_6085_ = lean_ctor_get(v_date_4656_, 2);
v_Y_6086_ = lean_ctor_get(v_date_4656_, 3);
v_D_6087_ = lean_ctor_get(v_date_4656_, 4);
v_M_6088_ = lean_ctor_get(v_date_4656_, 5);
v_L_6089_ = lean_ctor_get(v_date_4656_, 6);
v_d_6090_ = lean_ctor_get(v_date_4656_, 7);
v_Q_6091_ = lean_ctor_get(v_date_4656_, 8);
v_q_6092_ = lean_ctor_get(v_date_4656_, 9);
v_w_6093_ = lean_ctor_get(v_date_4656_, 10);
v_W_6094_ = lean_ctor_get(v_date_4656_, 11);
v_E_6095_ = lean_ctor_get(v_date_4656_, 12);
v_e_6096_ = lean_ctor_get(v_date_4656_, 13);
v_c_6097_ = lean_ctor_get(v_date_4656_, 14);
v_F_6098_ = lean_ctor_get(v_date_4656_, 15);
v_a_6099_ = lean_ctor_get(v_date_4656_, 16);
v_b_6100_ = lean_ctor_get(v_date_4656_, 17);
v_B_6101_ = lean_ctor_get(v_date_4656_, 18);
v_h_6102_ = lean_ctor_get(v_date_4656_, 19);
v_K_6103_ = lean_ctor_get(v_date_4656_, 20);
v_k_6104_ = lean_ctor_get(v_date_4656_, 21);
v_H_6105_ = lean_ctor_get(v_date_4656_, 22);
v_m_6106_ = lean_ctor_get(v_date_4656_, 23);
v_s_6107_ = lean_ctor_get(v_date_4656_, 24);
v_S_6108_ = lean_ctor_get(v_date_4656_, 25);
v_A_6109_ = lean_ctor_get(v_date_4656_, 26);
v_n_6110_ = lean_ctor_get(v_date_4656_, 27);
v_V_6111_ = lean_ctor_get(v_date_4656_, 29);
v_z_6112_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_6113_ = lean_ctor_get(v_date_4656_, 31);
v_v_6114_ = lean_ctor_get(v_date_4656_, 32);
v_O_6115_ = lean_ctor_get(v_date_4656_, 33);
v_X_6116_ = lean_ctor_get(v_date_4656_, 34);
v_x_6117_ = lean_ctor_get(v_date_4656_, 35);
v_Z_6118_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_6128_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6128_ == 0)
{
lean_object* v_unused_6129_; 
v_unused_6129_ = lean_ctor_get(v_date_4656_, 28);
lean_dec(v_unused_6129_);
v___x_6120_ = v_date_4656_;
v_isShared_6121_ = v_isSharedCheck_6128_;
goto v_resetjp_6119_;
}
else
{
lean_inc(v_Z_6118_);
lean_inc(v_x_6117_);
lean_inc(v_X_6116_);
lean_inc(v_O_6115_);
lean_inc(v_v_6114_);
lean_inc(v_zabbrev_6113_);
lean_inc(v_z_6112_);
lean_inc(v_V_6111_);
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
lean_dec(v_date_4656_);
v___x_6120_ = lean_box(0);
v_isShared_6121_ = v_isSharedCheck_6128_;
goto v_resetjp_6119_;
}
v_resetjp_6119_:
{
lean_object* v___x_6123_; 
if (v_isShared_6082_ == 0)
{
lean_ctor_set_tag(v___x_6081_, 1);
lean_ctor_set(v___x_6081_, 0, v_data_4658_);
v___x_6123_ = v___x_6081_;
goto v_reusejp_6122_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_data_4658_);
v___x_6123_ = v_reuseFailAlloc_6127_;
goto v_reusejp_6122_;
}
v_reusejp_6122_:
{
lean_object* v___x_6125_; 
if (v_isShared_6121_ == 0)
{
lean_ctor_set(v___x_6120_, 28, v___x_6123_);
v___x_6125_ = v___x_6120_;
goto v_reusejp_6124_;
}
else
{
lean_object* v_reuseFailAlloc_6126_; 
v_reuseFailAlloc_6126_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6126_, 0, v_G_6083_);
lean_ctor_set(v_reuseFailAlloc_6126_, 1, v_y_6084_);
lean_ctor_set(v_reuseFailAlloc_6126_, 2, v_u_6085_);
lean_ctor_set(v_reuseFailAlloc_6126_, 3, v_Y_6086_);
lean_ctor_set(v_reuseFailAlloc_6126_, 4, v_D_6087_);
lean_ctor_set(v_reuseFailAlloc_6126_, 5, v_M_6088_);
lean_ctor_set(v_reuseFailAlloc_6126_, 6, v_L_6089_);
lean_ctor_set(v_reuseFailAlloc_6126_, 7, v_d_6090_);
lean_ctor_set(v_reuseFailAlloc_6126_, 8, v_Q_6091_);
lean_ctor_set(v_reuseFailAlloc_6126_, 9, v_q_6092_);
lean_ctor_set(v_reuseFailAlloc_6126_, 10, v_w_6093_);
lean_ctor_set(v_reuseFailAlloc_6126_, 11, v_W_6094_);
lean_ctor_set(v_reuseFailAlloc_6126_, 12, v_E_6095_);
lean_ctor_set(v_reuseFailAlloc_6126_, 13, v_e_6096_);
lean_ctor_set(v_reuseFailAlloc_6126_, 14, v_c_6097_);
lean_ctor_set(v_reuseFailAlloc_6126_, 15, v_F_6098_);
lean_ctor_set(v_reuseFailAlloc_6126_, 16, v_a_6099_);
lean_ctor_set(v_reuseFailAlloc_6126_, 17, v_b_6100_);
lean_ctor_set(v_reuseFailAlloc_6126_, 18, v_B_6101_);
lean_ctor_set(v_reuseFailAlloc_6126_, 19, v_h_6102_);
lean_ctor_set(v_reuseFailAlloc_6126_, 20, v_K_6103_);
lean_ctor_set(v_reuseFailAlloc_6126_, 21, v_k_6104_);
lean_ctor_set(v_reuseFailAlloc_6126_, 22, v_H_6105_);
lean_ctor_set(v_reuseFailAlloc_6126_, 23, v_m_6106_);
lean_ctor_set(v_reuseFailAlloc_6126_, 24, v_s_6107_);
lean_ctor_set(v_reuseFailAlloc_6126_, 25, v_S_6108_);
lean_ctor_set(v_reuseFailAlloc_6126_, 26, v_A_6109_);
lean_ctor_set(v_reuseFailAlloc_6126_, 27, v_n_6110_);
lean_ctor_set(v_reuseFailAlloc_6126_, 28, v___x_6123_);
lean_ctor_set(v_reuseFailAlloc_6126_, 29, v_V_6111_);
lean_ctor_set(v_reuseFailAlloc_6126_, 30, v_z_6112_);
lean_ctor_set(v_reuseFailAlloc_6126_, 31, v_zabbrev_6113_);
lean_ctor_set(v_reuseFailAlloc_6126_, 32, v_v_6114_);
lean_ctor_set(v_reuseFailAlloc_6126_, 33, v_O_6115_);
lean_ctor_set(v_reuseFailAlloc_6126_, 34, v_X_6116_);
lean_ctor_set(v_reuseFailAlloc_6126_, 35, v_x_6117_);
lean_ctor_set(v_reuseFailAlloc_6126_, 36, v_Z_6118_);
v___x_6125_ = v_reuseFailAlloc_6126_;
goto v_reusejp_6124_;
}
v_reusejp_6124_:
{
return v___x_6125_;
}
}
}
}
}
case 29:
{
lean_object* v_G_6132_; lean_object* v_y_6133_; lean_object* v_u_6134_; lean_object* v_Y_6135_; lean_object* v_D_6136_; lean_object* v_M_6137_; lean_object* v_L_6138_; lean_object* v_d_6139_; lean_object* v_Q_6140_; lean_object* v_q_6141_; lean_object* v_w_6142_; lean_object* v_W_6143_; lean_object* v_E_6144_; lean_object* v_e_6145_; lean_object* v_c_6146_; lean_object* v_F_6147_; lean_object* v_a_6148_; lean_object* v_b_6149_; lean_object* v_B_6150_; lean_object* v_h_6151_; lean_object* v_K_6152_; lean_object* v_k_6153_; lean_object* v_H_6154_; lean_object* v_m_6155_; lean_object* v_s_6156_; lean_object* v_S_6157_; lean_object* v_A_6158_; lean_object* v_n_6159_; lean_object* v_N_6160_; lean_object* v_z_6161_; lean_object* v_zabbrev_6162_; lean_object* v_v_6163_; lean_object* v_O_6164_; lean_object* v_X_6165_; lean_object* v_x_6166_; lean_object* v_Z_6167_; lean_object* v___x_6169_; uint8_t v_isShared_6170_; uint8_t v_isSharedCheck_6175_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_G_6132_ = lean_ctor_get(v_date_4656_, 0);
v_y_6133_ = lean_ctor_get(v_date_4656_, 1);
v_u_6134_ = lean_ctor_get(v_date_4656_, 2);
v_Y_6135_ = lean_ctor_get(v_date_4656_, 3);
v_D_6136_ = lean_ctor_get(v_date_4656_, 4);
v_M_6137_ = lean_ctor_get(v_date_4656_, 5);
v_L_6138_ = lean_ctor_get(v_date_4656_, 6);
v_d_6139_ = lean_ctor_get(v_date_4656_, 7);
v_Q_6140_ = lean_ctor_get(v_date_4656_, 8);
v_q_6141_ = lean_ctor_get(v_date_4656_, 9);
v_w_6142_ = lean_ctor_get(v_date_4656_, 10);
v_W_6143_ = lean_ctor_get(v_date_4656_, 11);
v_E_6144_ = lean_ctor_get(v_date_4656_, 12);
v_e_6145_ = lean_ctor_get(v_date_4656_, 13);
v_c_6146_ = lean_ctor_get(v_date_4656_, 14);
v_F_6147_ = lean_ctor_get(v_date_4656_, 15);
v_a_6148_ = lean_ctor_get(v_date_4656_, 16);
v_b_6149_ = lean_ctor_get(v_date_4656_, 17);
v_B_6150_ = lean_ctor_get(v_date_4656_, 18);
v_h_6151_ = lean_ctor_get(v_date_4656_, 19);
v_K_6152_ = lean_ctor_get(v_date_4656_, 20);
v_k_6153_ = lean_ctor_get(v_date_4656_, 21);
v_H_6154_ = lean_ctor_get(v_date_4656_, 22);
v_m_6155_ = lean_ctor_get(v_date_4656_, 23);
v_s_6156_ = lean_ctor_get(v_date_4656_, 24);
v_S_6157_ = lean_ctor_get(v_date_4656_, 25);
v_A_6158_ = lean_ctor_get(v_date_4656_, 26);
v_n_6159_ = lean_ctor_get(v_date_4656_, 27);
v_N_6160_ = lean_ctor_get(v_date_4656_, 28);
v_z_6161_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_6162_ = lean_ctor_get(v_date_4656_, 31);
v_v_6163_ = lean_ctor_get(v_date_4656_, 32);
v_O_6164_ = lean_ctor_get(v_date_4656_, 33);
v_X_6165_ = lean_ctor_get(v_date_4656_, 34);
v_x_6166_ = lean_ctor_get(v_date_4656_, 35);
v_Z_6167_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_6175_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6175_ == 0)
{
lean_object* v_unused_6176_; 
v_unused_6176_ = lean_ctor_get(v_date_4656_, 29);
lean_dec(v_unused_6176_);
v___x_6169_ = v_date_4656_;
v_isShared_6170_ = v_isSharedCheck_6175_;
goto v_resetjp_6168_;
}
else
{
lean_inc(v_Z_6167_);
lean_inc(v_x_6166_);
lean_inc(v_X_6165_);
lean_inc(v_O_6164_);
lean_inc(v_v_6163_);
lean_inc(v_zabbrev_6162_);
lean_inc(v_z_6161_);
lean_inc(v_N_6160_);
lean_inc(v_n_6159_);
lean_inc(v_A_6158_);
lean_inc(v_S_6157_);
lean_inc(v_s_6156_);
lean_inc(v_m_6155_);
lean_inc(v_H_6154_);
lean_inc(v_k_6153_);
lean_inc(v_K_6152_);
lean_inc(v_h_6151_);
lean_inc(v_B_6150_);
lean_inc(v_b_6149_);
lean_inc(v_a_6148_);
lean_inc(v_F_6147_);
lean_inc(v_c_6146_);
lean_inc(v_e_6145_);
lean_inc(v_E_6144_);
lean_inc(v_W_6143_);
lean_inc(v_w_6142_);
lean_inc(v_q_6141_);
lean_inc(v_Q_6140_);
lean_inc(v_d_6139_);
lean_inc(v_L_6138_);
lean_inc(v_M_6137_);
lean_inc(v_D_6136_);
lean_inc(v_Y_6135_);
lean_inc(v_u_6134_);
lean_inc(v_y_6133_);
lean_inc(v_G_6132_);
lean_dec(v_date_4656_);
v___x_6169_ = lean_box(0);
v_isShared_6170_ = v_isSharedCheck_6175_;
goto v_resetjp_6168_;
}
v_resetjp_6168_:
{
lean_object* v___x_6171_; lean_object* v___x_6173_; 
v___x_6171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6171_, 0, v_data_4658_);
if (v_isShared_6170_ == 0)
{
lean_ctor_set(v___x_6169_, 29, v___x_6171_);
v___x_6173_ = v___x_6169_;
goto v_reusejp_6172_;
}
else
{
lean_object* v_reuseFailAlloc_6174_; 
v_reuseFailAlloc_6174_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6174_, 0, v_G_6132_);
lean_ctor_set(v_reuseFailAlloc_6174_, 1, v_y_6133_);
lean_ctor_set(v_reuseFailAlloc_6174_, 2, v_u_6134_);
lean_ctor_set(v_reuseFailAlloc_6174_, 3, v_Y_6135_);
lean_ctor_set(v_reuseFailAlloc_6174_, 4, v_D_6136_);
lean_ctor_set(v_reuseFailAlloc_6174_, 5, v_M_6137_);
lean_ctor_set(v_reuseFailAlloc_6174_, 6, v_L_6138_);
lean_ctor_set(v_reuseFailAlloc_6174_, 7, v_d_6139_);
lean_ctor_set(v_reuseFailAlloc_6174_, 8, v_Q_6140_);
lean_ctor_set(v_reuseFailAlloc_6174_, 9, v_q_6141_);
lean_ctor_set(v_reuseFailAlloc_6174_, 10, v_w_6142_);
lean_ctor_set(v_reuseFailAlloc_6174_, 11, v_W_6143_);
lean_ctor_set(v_reuseFailAlloc_6174_, 12, v_E_6144_);
lean_ctor_set(v_reuseFailAlloc_6174_, 13, v_e_6145_);
lean_ctor_set(v_reuseFailAlloc_6174_, 14, v_c_6146_);
lean_ctor_set(v_reuseFailAlloc_6174_, 15, v_F_6147_);
lean_ctor_set(v_reuseFailAlloc_6174_, 16, v_a_6148_);
lean_ctor_set(v_reuseFailAlloc_6174_, 17, v_b_6149_);
lean_ctor_set(v_reuseFailAlloc_6174_, 18, v_B_6150_);
lean_ctor_set(v_reuseFailAlloc_6174_, 19, v_h_6151_);
lean_ctor_set(v_reuseFailAlloc_6174_, 20, v_K_6152_);
lean_ctor_set(v_reuseFailAlloc_6174_, 21, v_k_6153_);
lean_ctor_set(v_reuseFailAlloc_6174_, 22, v_H_6154_);
lean_ctor_set(v_reuseFailAlloc_6174_, 23, v_m_6155_);
lean_ctor_set(v_reuseFailAlloc_6174_, 24, v_s_6156_);
lean_ctor_set(v_reuseFailAlloc_6174_, 25, v_S_6157_);
lean_ctor_set(v_reuseFailAlloc_6174_, 26, v_A_6158_);
lean_ctor_set(v_reuseFailAlloc_6174_, 27, v_n_6159_);
lean_ctor_set(v_reuseFailAlloc_6174_, 28, v_N_6160_);
lean_ctor_set(v_reuseFailAlloc_6174_, 29, v___x_6171_);
lean_ctor_set(v_reuseFailAlloc_6174_, 30, v_z_6161_);
lean_ctor_set(v_reuseFailAlloc_6174_, 31, v_zabbrev_6162_);
lean_ctor_set(v_reuseFailAlloc_6174_, 32, v_v_6163_);
lean_ctor_set(v_reuseFailAlloc_6174_, 33, v_O_6164_);
lean_ctor_set(v_reuseFailAlloc_6174_, 34, v_X_6165_);
lean_ctor_set(v_reuseFailAlloc_6174_, 35, v_x_6166_);
lean_ctor_set(v_reuseFailAlloc_6174_, 36, v_Z_6167_);
v___x_6173_ = v_reuseFailAlloc_6174_;
goto v_reusejp_6172_;
}
v_reusejp_6172_:
{
return v___x_6173_;
}
}
}
case 30:
{
uint8_t v_presentation_6177_; 
v_presentation_6177_ = lean_ctor_get_uint8(v_modifier_4657_, 0);
lean_dec_ref_known(v_modifier_4657_, 0);
if (v_presentation_6177_ == 0)
{
lean_object* v_G_6178_; lean_object* v_y_6179_; lean_object* v_u_6180_; lean_object* v_Y_6181_; lean_object* v_D_6182_; lean_object* v_M_6183_; lean_object* v_L_6184_; lean_object* v_d_6185_; lean_object* v_Q_6186_; lean_object* v_q_6187_; lean_object* v_w_6188_; lean_object* v_W_6189_; lean_object* v_E_6190_; lean_object* v_e_6191_; lean_object* v_c_6192_; lean_object* v_F_6193_; lean_object* v_a_6194_; lean_object* v_b_6195_; lean_object* v_B_6196_; lean_object* v_h_6197_; lean_object* v_K_6198_; lean_object* v_k_6199_; lean_object* v_H_6200_; lean_object* v_m_6201_; lean_object* v_s_6202_; lean_object* v_S_6203_; lean_object* v_A_6204_; lean_object* v_n_6205_; lean_object* v_N_6206_; lean_object* v_V_6207_; lean_object* v_z_6208_; lean_object* v_v_6209_; lean_object* v_O_6210_; lean_object* v_X_6211_; lean_object* v_x_6212_; lean_object* v_Z_6213_; lean_object* v___x_6215_; uint8_t v_isShared_6216_; uint8_t v_isSharedCheck_6221_; 
v_G_6178_ = lean_ctor_get(v_date_4656_, 0);
v_y_6179_ = lean_ctor_get(v_date_4656_, 1);
v_u_6180_ = lean_ctor_get(v_date_4656_, 2);
v_Y_6181_ = lean_ctor_get(v_date_4656_, 3);
v_D_6182_ = lean_ctor_get(v_date_4656_, 4);
v_M_6183_ = lean_ctor_get(v_date_4656_, 5);
v_L_6184_ = lean_ctor_get(v_date_4656_, 6);
v_d_6185_ = lean_ctor_get(v_date_4656_, 7);
v_Q_6186_ = lean_ctor_get(v_date_4656_, 8);
v_q_6187_ = lean_ctor_get(v_date_4656_, 9);
v_w_6188_ = lean_ctor_get(v_date_4656_, 10);
v_W_6189_ = lean_ctor_get(v_date_4656_, 11);
v_E_6190_ = lean_ctor_get(v_date_4656_, 12);
v_e_6191_ = lean_ctor_get(v_date_4656_, 13);
v_c_6192_ = lean_ctor_get(v_date_4656_, 14);
v_F_6193_ = lean_ctor_get(v_date_4656_, 15);
v_a_6194_ = lean_ctor_get(v_date_4656_, 16);
v_b_6195_ = lean_ctor_get(v_date_4656_, 17);
v_B_6196_ = lean_ctor_get(v_date_4656_, 18);
v_h_6197_ = lean_ctor_get(v_date_4656_, 19);
v_K_6198_ = lean_ctor_get(v_date_4656_, 20);
v_k_6199_ = lean_ctor_get(v_date_4656_, 21);
v_H_6200_ = lean_ctor_get(v_date_4656_, 22);
v_m_6201_ = lean_ctor_get(v_date_4656_, 23);
v_s_6202_ = lean_ctor_get(v_date_4656_, 24);
v_S_6203_ = lean_ctor_get(v_date_4656_, 25);
v_A_6204_ = lean_ctor_get(v_date_4656_, 26);
v_n_6205_ = lean_ctor_get(v_date_4656_, 27);
v_N_6206_ = lean_ctor_get(v_date_4656_, 28);
v_V_6207_ = lean_ctor_get(v_date_4656_, 29);
v_z_6208_ = lean_ctor_get(v_date_4656_, 30);
v_v_6209_ = lean_ctor_get(v_date_4656_, 32);
v_O_6210_ = lean_ctor_get(v_date_4656_, 33);
v_X_6211_ = lean_ctor_get(v_date_4656_, 34);
v_x_6212_ = lean_ctor_get(v_date_4656_, 35);
v_Z_6213_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_6221_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6221_ == 0)
{
lean_object* v_unused_6222_; 
v_unused_6222_ = lean_ctor_get(v_date_4656_, 31);
lean_dec(v_unused_6222_);
v___x_6215_ = v_date_4656_;
v_isShared_6216_ = v_isSharedCheck_6221_;
goto v_resetjp_6214_;
}
else
{
lean_inc(v_Z_6213_);
lean_inc(v_x_6212_);
lean_inc(v_X_6211_);
lean_inc(v_O_6210_);
lean_inc(v_v_6209_);
lean_inc(v_z_6208_);
lean_inc(v_V_6207_);
lean_inc(v_N_6206_);
lean_inc(v_n_6205_);
lean_inc(v_A_6204_);
lean_inc(v_S_6203_);
lean_inc(v_s_6202_);
lean_inc(v_m_6201_);
lean_inc(v_H_6200_);
lean_inc(v_k_6199_);
lean_inc(v_K_6198_);
lean_inc(v_h_6197_);
lean_inc(v_B_6196_);
lean_inc(v_b_6195_);
lean_inc(v_a_6194_);
lean_inc(v_F_6193_);
lean_inc(v_c_6192_);
lean_inc(v_e_6191_);
lean_inc(v_E_6190_);
lean_inc(v_W_6189_);
lean_inc(v_w_6188_);
lean_inc(v_q_6187_);
lean_inc(v_Q_6186_);
lean_inc(v_d_6185_);
lean_inc(v_L_6184_);
lean_inc(v_M_6183_);
lean_inc(v_D_6182_);
lean_inc(v_Y_6181_);
lean_inc(v_u_6180_);
lean_inc(v_y_6179_);
lean_inc(v_G_6178_);
lean_dec(v_date_4656_);
v___x_6215_ = lean_box(0);
v_isShared_6216_ = v_isSharedCheck_6221_;
goto v_resetjp_6214_;
}
v_resetjp_6214_:
{
lean_object* v___x_6217_; lean_object* v___x_6219_; 
v___x_6217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6217_, 0, v_data_4658_);
if (v_isShared_6216_ == 0)
{
lean_ctor_set(v___x_6215_, 31, v___x_6217_);
v___x_6219_ = v___x_6215_;
goto v_reusejp_6218_;
}
else
{
lean_object* v_reuseFailAlloc_6220_; 
v_reuseFailAlloc_6220_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6220_, 0, v_G_6178_);
lean_ctor_set(v_reuseFailAlloc_6220_, 1, v_y_6179_);
lean_ctor_set(v_reuseFailAlloc_6220_, 2, v_u_6180_);
lean_ctor_set(v_reuseFailAlloc_6220_, 3, v_Y_6181_);
lean_ctor_set(v_reuseFailAlloc_6220_, 4, v_D_6182_);
lean_ctor_set(v_reuseFailAlloc_6220_, 5, v_M_6183_);
lean_ctor_set(v_reuseFailAlloc_6220_, 6, v_L_6184_);
lean_ctor_set(v_reuseFailAlloc_6220_, 7, v_d_6185_);
lean_ctor_set(v_reuseFailAlloc_6220_, 8, v_Q_6186_);
lean_ctor_set(v_reuseFailAlloc_6220_, 9, v_q_6187_);
lean_ctor_set(v_reuseFailAlloc_6220_, 10, v_w_6188_);
lean_ctor_set(v_reuseFailAlloc_6220_, 11, v_W_6189_);
lean_ctor_set(v_reuseFailAlloc_6220_, 12, v_E_6190_);
lean_ctor_set(v_reuseFailAlloc_6220_, 13, v_e_6191_);
lean_ctor_set(v_reuseFailAlloc_6220_, 14, v_c_6192_);
lean_ctor_set(v_reuseFailAlloc_6220_, 15, v_F_6193_);
lean_ctor_set(v_reuseFailAlloc_6220_, 16, v_a_6194_);
lean_ctor_set(v_reuseFailAlloc_6220_, 17, v_b_6195_);
lean_ctor_set(v_reuseFailAlloc_6220_, 18, v_B_6196_);
lean_ctor_set(v_reuseFailAlloc_6220_, 19, v_h_6197_);
lean_ctor_set(v_reuseFailAlloc_6220_, 20, v_K_6198_);
lean_ctor_set(v_reuseFailAlloc_6220_, 21, v_k_6199_);
lean_ctor_set(v_reuseFailAlloc_6220_, 22, v_H_6200_);
lean_ctor_set(v_reuseFailAlloc_6220_, 23, v_m_6201_);
lean_ctor_set(v_reuseFailAlloc_6220_, 24, v_s_6202_);
lean_ctor_set(v_reuseFailAlloc_6220_, 25, v_S_6203_);
lean_ctor_set(v_reuseFailAlloc_6220_, 26, v_A_6204_);
lean_ctor_set(v_reuseFailAlloc_6220_, 27, v_n_6205_);
lean_ctor_set(v_reuseFailAlloc_6220_, 28, v_N_6206_);
lean_ctor_set(v_reuseFailAlloc_6220_, 29, v_V_6207_);
lean_ctor_set(v_reuseFailAlloc_6220_, 30, v_z_6208_);
lean_ctor_set(v_reuseFailAlloc_6220_, 31, v___x_6217_);
lean_ctor_set(v_reuseFailAlloc_6220_, 32, v_v_6209_);
lean_ctor_set(v_reuseFailAlloc_6220_, 33, v_O_6210_);
lean_ctor_set(v_reuseFailAlloc_6220_, 34, v_X_6211_);
lean_ctor_set(v_reuseFailAlloc_6220_, 35, v_x_6212_);
lean_ctor_set(v_reuseFailAlloc_6220_, 36, v_Z_6213_);
v___x_6219_ = v_reuseFailAlloc_6220_;
goto v_reusejp_6218_;
}
v_reusejp_6218_:
{
return v___x_6219_;
}
}
}
else
{
lean_object* v_G_6223_; lean_object* v_y_6224_; lean_object* v_u_6225_; lean_object* v_Y_6226_; lean_object* v_D_6227_; lean_object* v_M_6228_; lean_object* v_L_6229_; lean_object* v_d_6230_; lean_object* v_Q_6231_; lean_object* v_q_6232_; lean_object* v_w_6233_; lean_object* v_W_6234_; lean_object* v_E_6235_; lean_object* v_e_6236_; lean_object* v_c_6237_; lean_object* v_F_6238_; lean_object* v_a_6239_; lean_object* v_b_6240_; lean_object* v_B_6241_; lean_object* v_h_6242_; lean_object* v_K_6243_; lean_object* v_k_6244_; lean_object* v_H_6245_; lean_object* v_m_6246_; lean_object* v_s_6247_; lean_object* v_S_6248_; lean_object* v_A_6249_; lean_object* v_n_6250_; lean_object* v_N_6251_; lean_object* v_V_6252_; lean_object* v_zabbrev_6253_; lean_object* v_v_6254_; lean_object* v_O_6255_; lean_object* v_X_6256_; lean_object* v_x_6257_; lean_object* v_Z_6258_; lean_object* v___x_6260_; uint8_t v_isShared_6261_; uint8_t v_isSharedCheck_6266_; 
v_G_6223_ = lean_ctor_get(v_date_4656_, 0);
v_y_6224_ = lean_ctor_get(v_date_4656_, 1);
v_u_6225_ = lean_ctor_get(v_date_4656_, 2);
v_Y_6226_ = lean_ctor_get(v_date_4656_, 3);
v_D_6227_ = lean_ctor_get(v_date_4656_, 4);
v_M_6228_ = lean_ctor_get(v_date_4656_, 5);
v_L_6229_ = lean_ctor_get(v_date_4656_, 6);
v_d_6230_ = lean_ctor_get(v_date_4656_, 7);
v_Q_6231_ = lean_ctor_get(v_date_4656_, 8);
v_q_6232_ = lean_ctor_get(v_date_4656_, 9);
v_w_6233_ = lean_ctor_get(v_date_4656_, 10);
v_W_6234_ = lean_ctor_get(v_date_4656_, 11);
v_E_6235_ = lean_ctor_get(v_date_4656_, 12);
v_e_6236_ = lean_ctor_get(v_date_4656_, 13);
v_c_6237_ = lean_ctor_get(v_date_4656_, 14);
v_F_6238_ = lean_ctor_get(v_date_4656_, 15);
v_a_6239_ = lean_ctor_get(v_date_4656_, 16);
v_b_6240_ = lean_ctor_get(v_date_4656_, 17);
v_B_6241_ = lean_ctor_get(v_date_4656_, 18);
v_h_6242_ = lean_ctor_get(v_date_4656_, 19);
v_K_6243_ = lean_ctor_get(v_date_4656_, 20);
v_k_6244_ = lean_ctor_get(v_date_4656_, 21);
v_H_6245_ = lean_ctor_get(v_date_4656_, 22);
v_m_6246_ = lean_ctor_get(v_date_4656_, 23);
v_s_6247_ = lean_ctor_get(v_date_4656_, 24);
v_S_6248_ = lean_ctor_get(v_date_4656_, 25);
v_A_6249_ = lean_ctor_get(v_date_4656_, 26);
v_n_6250_ = lean_ctor_get(v_date_4656_, 27);
v_N_6251_ = lean_ctor_get(v_date_4656_, 28);
v_V_6252_ = lean_ctor_get(v_date_4656_, 29);
v_zabbrev_6253_ = lean_ctor_get(v_date_4656_, 31);
v_v_6254_ = lean_ctor_get(v_date_4656_, 32);
v_O_6255_ = lean_ctor_get(v_date_4656_, 33);
v_X_6256_ = lean_ctor_get(v_date_4656_, 34);
v_x_6257_ = lean_ctor_get(v_date_4656_, 35);
v_Z_6258_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_6266_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6266_ == 0)
{
lean_object* v_unused_6267_; 
v_unused_6267_ = lean_ctor_get(v_date_4656_, 30);
lean_dec(v_unused_6267_);
v___x_6260_ = v_date_4656_;
v_isShared_6261_ = v_isSharedCheck_6266_;
goto v_resetjp_6259_;
}
else
{
lean_inc(v_Z_6258_);
lean_inc(v_x_6257_);
lean_inc(v_X_6256_);
lean_inc(v_O_6255_);
lean_inc(v_v_6254_);
lean_inc(v_zabbrev_6253_);
lean_inc(v_V_6252_);
lean_inc(v_N_6251_);
lean_inc(v_n_6250_);
lean_inc(v_A_6249_);
lean_inc(v_S_6248_);
lean_inc(v_s_6247_);
lean_inc(v_m_6246_);
lean_inc(v_H_6245_);
lean_inc(v_k_6244_);
lean_inc(v_K_6243_);
lean_inc(v_h_6242_);
lean_inc(v_B_6241_);
lean_inc(v_b_6240_);
lean_inc(v_a_6239_);
lean_inc(v_F_6238_);
lean_inc(v_c_6237_);
lean_inc(v_e_6236_);
lean_inc(v_E_6235_);
lean_inc(v_W_6234_);
lean_inc(v_w_6233_);
lean_inc(v_q_6232_);
lean_inc(v_Q_6231_);
lean_inc(v_d_6230_);
lean_inc(v_L_6229_);
lean_inc(v_M_6228_);
lean_inc(v_D_6227_);
lean_inc(v_Y_6226_);
lean_inc(v_u_6225_);
lean_inc(v_y_6224_);
lean_inc(v_G_6223_);
lean_dec(v_date_4656_);
v___x_6260_ = lean_box(0);
v_isShared_6261_ = v_isSharedCheck_6266_;
goto v_resetjp_6259_;
}
v_resetjp_6259_:
{
lean_object* v___x_6262_; lean_object* v___x_6264_; 
v___x_6262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6262_, 0, v_data_4658_);
if (v_isShared_6261_ == 0)
{
lean_ctor_set(v___x_6260_, 30, v___x_6262_);
v___x_6264_ = v___x_6260_;
goto v_reusejp_6263_;
}
else
{
lean_object* v_reuseFailAlloc_6265_; 
v_reuseFailAlloc_6265_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6265_, 0, v_G_6223_);
lean_ctor_set(v_reuseFailAlloc_6265_, 1, v_y_6224_);
lean_ctor_set(v_reuseFailAlloc_6265_, 2, v_u_6225_);
lean_ctor_set(v_reuseFailAlloc_6265_, 3, v_Y_6226_);
lean_ctor_set(v_reuseFailAlloc_6265_, 4, v_D_6227_);
lean_ctor_set(v_reuseFailAlloc_6265_, 5, v_M_6228_);
lean_ctor_set(v_reuseFailAlloc_6265_, 6, v_L_6229_);
lean_ctor_set(v_reuseFailAlloc_6265_, 7, v_d_6230_);
lean_ctor_set(v_reuseFailAlloc_6265_, 8, v_Q_6231_);
lean_ctor_set(v_reuseFailAlloc_6265_, 9, v_q_6232_);
lean_ctor_set(v_reuseFailAlloc_6265_, 10, v_w_6233_);
lean_ctor_set(v_reuseFailAlloc_6265_, 11, v_W_6234_);
lean_ctor_set(v_reuseFailAlloc_6265_, 12, v_E_6235_);
lean_ctor_set(v_reuseFailAlloc_6265_, 13, v_e_6236_);
lean_ctor_set(v_reuseFailAlloc_6265_, 14, v_c_6237_);
lean_ctor_set(v_reuseFailAlloc_6265_, 15, v_F_6238_);
lean_ctor_set(v_reuseFailAlloc_6265_, 16, v_a_6239_);
lean_ctor_set(v_reuseFailAlloc_6265_, 17, v_b_6240_);
lean_ctor_set(v_reuseFailAlloc_6265_, 18, v_B_6241_);
lean_ctor_set(v_reuseFailAlloc_6265_, 19, v_h_6242_);
lean_ctor_set(v_reuseFailAlloc_6265_, 20, v_K_6243_);
lean_ctor_set(v_reuseFailAlloc_6265_, 21, v_k_6244_);
lean_ctor_set(v_reuseFailAlloc_6265_, 22, v_H_6245_);
lean_ctor_set(v_reuseFailAlloc_6265_, 23, v_m_6246_);
lean_ctor_set(v_reuseFailAlloc_6265_, 24, v_s_6247_);
lean_ctor_set(v_reuseFailAlloc_6265_, 25, v_S_6248_);
lean_ctor_set(v_reuseFailAlloc_6265_, 26, v_A_6249_);
lean_ctor_set(v_reuseFailAlloc_6265_, 27, v_n_6250_);
lean_ctor_set(v_reuseFailAlloc_6265_, 28, v_N_6251_);
lean_ctor_set(v_reuseFailAlloc_6265_, 29, v_V_6252_);
lean_ctor_set(v_reuseFailAlloc_6265_, 30, v___x_6262_);
lean_ctor_set(v_reuseFailAlloc_6265_, 31, v_zabbrev_6253_);
lean_ctor_set(v_reuseFailAlloc_6265_, 32, v_v_6254_);
lean_ctor_set(v_reuseFailAlloc_6265_, 33, v_O_6255_);
lean_ctor_set(v_reuseFailAlloc_6265_, 34, v_X_6256_);
lean_ctor_set(v_reuseFailAlloc_6265_, 35, v_x_6257_);
lean_ctor_set(v_reuseFailAlloc_6265_, 36, v_Z_6258_);
v___x_6264_ = v_reuseFailAlloc_6265_;
goto v_reusejp_6263_;
}
v_reusejp_6263_:
{
return v___x_6264_;
}
}
}
}
case 31:
{
lean_object* v_G_6268_; lean_object* v_y_6269_; lean_object* v_u_6270_; lean_object* v_Y_6271_; lean_object* v_D_6272_; lean_object* v_M_6273_; lean_object* v_L_6274_; lean_object* v_d_6275_; lean_object* v_Q_6276_; lean_object* v_q_6277_; lean_object* v_w_6278_; lean_object* v_W_6279_; lean_object* v_E_6280_; lean_object* v_e_6281_; lean_object* v_c_6282_; lean_object* v_F_6283_; lean_object* v_a_6284_; lean_object* v_b_6285_; lean_object* v_B_6286_; lean_object* v_h_6287_; lean_object* v_K_6288_; lean_object* v_k_6289_; lean_object* v_H_6290_; lean_object* v_m_6291_; lean_object* v_s_6292_; lean_object* v_S_6293_; lean_object* v_A_6294_; lean_object* v_n_6295_; lean_object* v_N_6296_; lean_object* v_V_6297_; lean_object* v_z_6298_; lean_object* v_zabbrev_6299_; lean_object* v_O_6300_; lean_object* v_X_6301_; lean_object* v_x_6302_; lean_object* v_Z_6303_; lean_object* v___x_6305_; uint8_t v_isShared_6306_; uint8_t v_isSharedCheck_6311_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_G_6268_ = lean_ctor_get(v_date_4656_, 0);
v_y_6269_ = lean_ctor_get(v_date_4656_, 1);
v_u_6270_ = lean_ctor_get(v_date_4656_, 2);
v_Y_6271_ = lean_ctor_get(v_date_4656_, 3);
v_D_6272_ = lean_ctor_get(v_date_4656_, 4);
v_M_6273_ = lean_ctor_get(v_date_4656_, 5);
v_L_6274_ = lean_ctor_get(v_date_4656_, 6);
v_d_6275_ = lean_ctor_get(v_date_4656_, 7);
v_Q_6276_ = lean_ctor_get(v_date_4656_, 8);
v_q_6277_ = lean_ctor_get(v_date_4656_, 9);
v_w_6278_ = lean_ctor_get(v_date_4656_, 10);
v_W_6279_ = lean_ctor_get(v_date_4656_, 11);
v_E_6280_ = lean_ctor_get(v_date_4656_, 12);
v_e_6281_ = lean_ctor_get(v_date_4656_, 13);
v_c_6282_ = lean_ctor_get(v_date_4656_, 14);
v_F_6283_ = lean_ctor_get(v_date_4656_, 15);
v_a_6284_ = lean_ctor_get(v_date_4656_, 16);
v_b_6285_ = lean_ctor_get(v_date_4656_, 17);
v_B_6286_ = lean_ctor_get(v_date_4656_, 18);
v_h_6287_ = lean_ctor_get(v_date_4656_, 19);
v_K_6288_ = lean_ctor_get(v_date_4656_, 20);
v_k_6289_ = lean_ctor_get(v_date_4656_, 21);
v_H_6290_ = lean_ctor_get(v_date_4656_, 22);
v_m_6291_ = lean_ctor_get(v_date_4656_, 23);
v_s_6292_ = lean_ctor_get(v_date_4656_, 24);
v_S_6293_ = lean_ctor_get(v_date_4656_, 25);
v_A_6294_ = lean_ctor_get(v_date_4656_, 26);
v_n_6295_ = lean_ctor_get(v_date_4656_, 27);
v_N_6296_ = lean_ctor_get(v_date_4656_, 28);
v_V_6297_ = lean_ctor_get(v_date_4656_, 29);
v_z_6298_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_6299_ = lean_ctor_get(v_date_4656_, 31);
v_O_6300_ = lean_ctor_get(v_date_4656_, 33);
v_X_6301_ = lean_ctor_get(v_date_4656_, 34);
v_x_6302_ = lean_ctor_get(v_date_4656_, 35);
v_Z_6303_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_6311_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6311_ == 0)
{
lean_object* v_unused_6312_; 
v_unused_6312_ = lean_ctor_get(v_date_4656_, 32);
lean_dec(v_unused_6312_);
v___x_6305_ = v_date_4656_;
v_isShared_6306_ = v_isSharedCheck_6311_;
goto v_resetjp_6304_;
}
else
{
lean_inc(v_Z_6303_);
lean_inc(v_x_6302_);
lean_inc(v_X_6301_);
lean_inc(v_O_6300_);
lean_inc(v_zabbrev_6299_);
lean_inc(v_z_6298_);
lean_inc(v_V_6297_);
lean_inc(v_N_6296_);
lean_inc(v_n_6295_);
lean_inc(v_A_6294_);
lean_inc(v_S_6293_);
lean_inc(v_s_6292_);
lean_inc(v_m_6291_);
lean_inc(v_H_6290_);
lean_inc(v_k_6289_);
lean_inc(v_K_6288_);
lean_inc(v_h_6287_);
lean_inc(v_B_6286_);
lean_inc(v_b_6285_);
lean_inc(v_a_6284_);
lean_inc(v_F_6283_);
lean_inc(v_c_6282_);
lean_inc(v_e_6281_);
lean_inc(v_E_6280_);
lean_inc(v_W_6279_);
lean_inc(v_w_6278_);
lean_inc(v_q_6277_);
lean_inc(v_Q_6276_);
lean_inc(v_d_6275_);
lean_inc(v_L_6274_);
lean_inc(v_M_6273_);
lean_inc(v_D_6272_);
lean_inc(v_Y_6271_);
lean_inc(v_u_6270_);
lean_inc(v_y_6269_);
lean_inc(v_G_6268_);
lean_dec(v_date_4656_);
v___x_6305_ = lean_box(0);
v_isShared_6306_ = v_isSharedCheck_6311_;
goto v_resetjp_6304_;
}
v_resetjp_6304_:
{
lean_object* v___x_6307_; lean_object* v___x_6309_; 
v___x_6307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6307_, 0, v_data_4658_);
if (v_isShared_6306_ == 0)
{
lean_ctor_set(v___x_6305_, 32, v___x_6307_);
v___x_6309_ = v___x_6305_;
goto v_reusejp_6308_;
}
else
{
lean_object* v_reuseFailAlloc_6310_; 
v_reuseFailAlloc_6310_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_G_6268_);
lean_ctor_set(v_reuseFailAlloc_6310_, 1, v_y_6269_);
lean_ctor_set(v_reuseFailAlloc_6310_, 2, v_u_6270_);
lean_ctor_set(v_reuseFailAlloc_6310_, 3, v_Y_6271_);
lean_ctor_set(v_reuseFailAlloc_6310_, 4, v_D_6272_);
lean_ctor_set(v_reuseFailAlloc_6310_, 5, v_M_6273_);
lean_ctor_set(v_reuseFailAlloc_6310_, 6, v_L_6274_);
lean_ctor_set(v_reuseFailAlloc_6310_, 7, v_d_6275_);
lean_ctor_set(v_reuseFailAlloc_6310_, 8, v_Q_6276_);
lean_ctor_set(v_reuseFailAlloc_6310_, 9, v_q_6277_);
lean_ctor_set(v_reuseFailAlloc_6310_, 10, v_w_6278_);
lean_ctor_set(v_reuseFailAlloc_6310_, 11, v_W_6279_);
lean_ctor_set(v_reuseFailAlloc_6310_, 12, v_E_6280_);
lean_ctor_set(v_reuseFailAlloc_6310_, 13, v_e_6281_);
lean_ctor_set(v_reuseFailAlloc_6310_, 14, v_c_6282_);
lean_ctor_set(v_reuseFailAlloc_6310_, 15, v_F_6283_);
lean_ctor_set(v_reuseFailAlloc_6310_, 16, v_a_6284_);
lean_ctor_set(v_reuseFailAlloc_6310_, 17, v_b_6285_);
lean_ctor_set(v_reuseFailAlloc_6310_, 18, v_B_6286_);
lean_ctor_set(v_reuseFailAlloc_6310_, 19, v_h_6287_);
lean_ctor_set(v_reuseFailAlloc_6310_, 20, v_K_6288_);
lean_ctor_set(v_reuseFailAlloc_6310_, 21, v_k_6289_);
lean_ctor_set(v_reuseFailAlloc_6310_, 22, v_H_6290_);
lean_ctor_set(v_reuseFailAlloc_6310_, 23, v_m_6291_);
lean_ctor_set(v_reuseFailAlloc_6310_, 24, v_s_6292_);
lean_ctor_set(v_reuseFailAlloc_6310_, 25, v_S_6293_);
lean_ctor_set(v_reuseFailAlloc_6310_, 26, v_A_6294_);
lean_ctor_set(v_reuseFailAlloc_6310_, 27, v_n_6295_);
lean_ctor_set(v_reuseFailAlloc_6310_, 28, v_N_6296_);
lean_ctor_set(v_reuseFailAlloc_6310_, 29, v_V_6297_);
lean_ctor_set(v_reuseFailAlloc_6310_, 30, v_z_6298_);
lean_ctor_set(v_reuseFailAlloc_6310_, 31, v_zabbrev_6299_);
lean_ctor_set(v_reuseFailAlloc_6310_, 32, v___x_6307_);
lean_ctor_set(v_reuseFailAlloc_6310_, 33, v_O_6300_);
lean_ctor_set(v_reuseFailAlloc_6310_, 34, v_X_6301_);
lean_ctor_set(v_reuseFailAlloc_6310_, 35, v_x_6302_);
lean_ctor_set(v_reuseFailAlloc_6310_, 36, v_Z_6303_);
v___x_6309_ = v_reuseFailAlloc_6310_;
goto v_reusejp_6308_;
}
v_reusejp_6308_:
{
return v___x_6309_;
}
}
}
case 32:
{
lean_object* v_G_6313_; lean_object* v_y_6314_; lean_object* v_u_6315_; lean_object* v_Y_6316_; lean_object* v_D_6317_; lean_object* v_M_6318_; lean_object* v_L_6319_; lean_object* v_d_6320_; lean_object* v_Q_6321_; lean_object* v_q_6322_; lean_object* v_w_6323_; lean_object* v_W_6324_; lean_object* v_E_6325_; lean_object* v_e_6326_; lean_object* v_c_6327_; lean_object* v_F_6328_; lean_object* v_a_6329_; lean_object* v_b_6330_; lean_object* v_B_6331_; lean_object* v_h_6332_; lean_object* v_K_6333_; lean_object* v_k_6334_; lean_object* v_H_6335_; lean_object* v_m_6336_; lean_object* v_s_6337_; lean_object* v_S_6338_; lean_object* v_A_6339_; lean_object* v_n_6340_; lean_object* v_N_6341_; lean_object* v_V_6342_; lean_object* v_z_6343_; lean_object* v_zabbrev_6344_; lean_object* v_v_6345_; lean_object* v_X_6346_; lean_object* v_x_6347_; lean_object* v_Z_6348_; lean_object* v___x_6350_; uint8_t v_isShared_6351_; uint8_t v_isSharedCheck_6356_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_G_6313_ = lean_ctor_get(v_date_4656_, 0);
v_y_6314_ = lean_ctor_get(v_date_4656_, 1);
v_u_6315_ = lean_ctor_get(v_date_4656_, 2);
v_Y_6316_ = lean_ctor_get(v_date_4656_, 3);
v_D_6317_ = lean_ctor_get(v_date_4656_, 4);
v_M_6318_ = lean_ctor_get(v_date_4656_, 5);
v_L_6319_ = lean_ctor_get(v_date_4656_, 6);
v_d_6320_ = lean_ctor_get(v_date_4656_, 7);
v_Q_6321_ = lean_ctor_get(v_date_4656_, 8);
v_q_6322_ = lean_ctor_get(v_date_4656_, 9);
v_w_6323_ = lean_ctor_get(v_date_4656_, 10);
v_W_6324_ = lean_ctor_get(v_date_4656_, 11);
v_E_6325_ = lean_ctor_get(v_date_4656_, 12);
v_e_6326_ = lean_ctor_get(v_date_4656_, 13);
v_c_6327_ = lean_ctor_get(v_date_4656_, 14);
v_F_6328_ = lean_ctor_get(v_date_4656_, 15);
v_a_6329_ = lean_ctor_get(v_date_4656_, 16);
v_b_6330_ = lean_ctor_get(v_date_4656_, 17);
v_B_6331_ = lean_ctor_get(v_date_4656_, 18);
v_h_6332_ = lean_ctor_get(v_date_4656_, 19);
v_K_6333_ = lean_ctor_get(v_date_4656_, 20);
v_k_6334_ = lean_ctor_get(v_date_4656_, 21);
v_H_6335_ = lean_ctor_get(v_date_4656_, 22);
v_m_6336_ = lean_ctor_get(v_date_4656_, 23);
v_s_6337_ = lean_ctor_get(v_date_4656_, 24);
v_S_6338_ = lean_ctor_get(v_date_4656_, 25);
v_A_6339_ = lean_ctor_get(v_date_4656_, 26);
v_n_6340_ = lean_ctor_get(v_date_4656_, 27);
v_N_6341_ = lean_ctor_get(v_date_4656_, 28);
v_V_6342_ = lean_ctor_get(v_date_4656_, 29);
v_z_6343_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_6344_ = lean_ctor_get(v_date_4656_, 31);
v_v_6345_ = lean_ctor_get(v_date_4656_, 32);
v_X_6346_ = lean_ctor_get(v_date_4656_, 34);
v_x_6347_ = lean_ctor_get(v_date_4656_, 35);
v_Z_6348_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_6356_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6356_ == 0)
{
lean_object* v_unused_6357_; 
v_unused_6357_ = lean_ctor_get(v_date_4656_, 33);
lean_dec(v_unused_6357_);
v___x_6350_ = v_date_4656_;
v_isShared_6351_ = v_isSharedCheck_6356_;
goto v_resetjp_6349_;
}
else
{
lean_inc(v_Z_6348_);
lean_inc(v_x_6347_);
lean_inc(v_X_6346_);
lean_inc(v_v_6345_);
lean_inc(v_zabbrev_6344_);
lean_inc(v_z_6343_);
lean_inc(v_V_6342_);
lean_inc(v_N_6341_);
lean_inc(v_n_6340_);
lean_inc(v_A_6339_);
lean_inc(v_S_6338_);
lean_inc(v_s_6337_);
lean_inc(v_m_6336_);
lean_inc(v_H_6335_);
lean_inc(v_k_6334_);
lean_inc(v_K_6333_);
lean_inc(v_h_6332_);
lean_inc(v_B_6331_);
lean_inc(v_b_6330_);
lean_inc(v_a_6329_);
lean_inc(v_F_6328_);
lean_inc(v_c_6327_);
lean_inc(v_e_6326_);
lean_inc(v_E_6325_);
lean_inc(v_W_6324_);
lean_inc(v_w_6323_);
lean_inc(v_q_6322_);
lean_inc(v_Q_6321_);
lean_inc(v_d_6320_);
lean_inc(v_L_6319_);
lean_inc(v_M_6318_);
lean_inc(v_D_6317_);
lean_inc(v_Y_6316_);
lean_inc(v_u_6315_);
lean_inc(v_y_6314_);
lean_inc(v_G_6313_);
lean_dec(v_date_4656_);
v___x_6350_ = lean_box(0);
v_isShared_6351_ = v_isSharedCheck_6356_;
goto v_resetjp_6349_;
}
v_resetjp_6349_:
{
lean_object* v___x_6352_; lean_object* v___x_6354_; 
v___x_6352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6352_, 0, v_data_4658_);
if (v_isShared_6351_ == 0)
{
lean_ctor_set(v___x_6350_, 33, v___x_6352_);
v___x_6354_ = v___x_6350_;
goto v_reusejp_6353_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_G_6313_);
lean_ctor_set(v_reuseFailAlloc_6355_, 1, v_y_6314_);
lean_ctor_set(v_reuseFailAlloc_6355_, 2, v_u_6315_);
lean_ctor_set(v_reuseFailAlloc_6355_, 3, v_Y_6316_);
lean_ctor_set(v_reuseFailAlloc_6355_, 4, v_D_6317_);
lean_ctor_set(v_reuseFailAlloc_6355_, 5, v_M_6318_);
lean_ctor_set(v_reuseFailAlloc_6355_, 6, v_L_6319_);
lean_ctor_set(v_reuseFailAlloc_6355_, 7, v_d_6320_);
lean_ctor_set(v_reuseFailAlloc_6355_, 8, v_Q_6321_);
lean_ctor_set(v_reuseFailAlloc_6355_, 9, v_q_6322_);
lean_ctor_set(v_reuseFailAlloc_6355_, 10, v_w_6323_);
lean_ctor_set(v_reuseFailAlloc_6355_, 11, v_W_6324_);
lean_ctor_set(v_reuseFailAlloc_6355_, 12, v_E_6325_);
lean_ctor_set(v_reuseFailAlloc_6355_, 13, v_e_6326_);
lean_ctor_set(v_reuseFailAlloc_6355_, 14, v_c_6327_);
lean_ctor_set(v_reuseFailAlloc_6355_, 15, v_F_6328_);
lean_ctor_set(v_reuseFailAlloc_6355_, 16, v_a_6329_);
lean_ctor_set(v_reuseFailAlloc_6355_, 17, v_b_6330_);
lean_ctor_set(v_reuseFailAlloc_6355_, 18, v_B_6331_);
lean_ctor_set(v_reuseFailAlloc_6355_, 19, v_h_6332_);
lean_ctor_set(v_reuseFailAlloc_6355_, 20, v_K_6333_);
lean_ctor_set(v_reuseFailAlloc_6355_, 21, v_k_6334_);
lean_ctor_set(v_reuseFailAlloc_6355_, 22, v_H_6335_);
lean_ctor_set(v_reuseFailAlloc_6355_, 23, v_m_6336_);
lean_ctor_set(v_reuseFailAlloc_6355_, 24, v_s_6337_);
lean_ctor_set(v_reuseFailAlloc_6355_, 25, v_S_6338_);
lean_ctor_set(v_reuseFailAlloc_6355_, 26, v_A_6339_);
lean_ctor_set(v_reuseFailAlloc_6355_, 27, v_n_6340_);
lean_ctor_set(v_reuseFailAlloc_6355_, 28, v_N_6341_);
lean_ctor_set(v_reuseFailAlloc_6355_, 29, v_V_6342_);
lean_ctor_set(v_reuseFailAlloc_6355_, 30, v_z_6343_);
lean_ctor_set(v_reuseFailAlloc_6355_, 31, v_zabbrev_6344_);
lean_ctor_set(v_reuseFailAlloc_6355_, 32, v_v_6345_);
lean_ctor_set(v_reuseFailAlloc_6355_, 33, v___x_6352_);
lean_ctor_set(v_reuseFailAlloc_6355_, 34, v_X_6346_);
lean_ctor_set(v_reuseFailAlloc_6355_, 35, v_x_6347_);
lean_ctor_set(v_reuseFailAlloc_6355_, 36, v_Z_6348_);
v___x_6354_ = v_reuseFailAlloc_6355_;
goto v_reusejp_6353_;
}
v_reusejp_6353_:
{
return v___x_6354_;
}
}
}
case 33:
{
lean_object* v_G_6358_; lean_object* v_y_6359_; lean_object* v_u_6360_; lean_object* v_Y_6361_; lean_object* v_D_6362_; lean_object* v_M_6363_; lean_object* v_L_6364_; lean_object* v_d_6365_; lean_object* v_Q_6366_; lean_object* v_q_6367_; lean_object* v_w_6368_; lean_object* v_W_6369_; lean_object* v_E_6370_; lean_object* v_e_6371_; lean_object* v_c_6372_; lean_object* v_F_6373_; lean_object* v_a_6374_; lean_object* v_b_6375_; lean_object* v_B_6376_; lean_object* v_h_6377_; lean_object* v_K_6378_; lean_object* v_k_6379_; lean_object* v_H_6380_; lean_object* v_m_6381_; lean_object* v_s_6382_; lean_object* v_S_6383_; lean_object* v_A_6384_; lean_object* v_n_6385_; lean_object* v_N_6386_; lean_object* v_V_6387_; lean_object* v_z_6388_; lean_object* v_zabbrev_6389_; lean_object* v_v_6390_; lean_object* v_O_6391_; lean_object* v_x_6392_; lean_object* v_Z_6393_; lean_object* v___x_6395_; uint8_t v_isShared_6396_; uint8_t v_isSharedCheck_6401_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_G_6358_ = lean_ctor_get(v_date_4656_, 0);
v_y_6359_ = lean_ctor_get(v_date_4656_, 1);
v_u_6360_ = lean_ctor_get(v_date_4656_, 2);
v_Y_6361_ = lean_ctor_get(v_date_4656_, 3);
v_D_6362_ = lean_ctor_get(v_date_4656_, 4);
v_M_6363_ = lean_ctor_get(v_date_4656_, 5);
v_L_6364_ = lean_ctor_get(v_date_4656_, 6);
v_d_6365_ = lean_ctor_get(v_date_4656_, 7);
v_Q_6366_ = lean_ctor_get(v_date_4656_, 8);
v_q_6367_ = lean_ctor_get(v_date_4656_, 9);
v_w_6368_ = lean_ctor_get(v_date_4656_, 10);
v_W_6369_ = lean_ctor_get(v_date_4656_, 11);
v_E_6370_ = lean_ctor_get(v_date_4656_, 12);
v_e_6371_ = lean_ctor_get(v_date_4656_, 13);
v_c_6372_ = lean_ctor_get(v_date_4656_, 14);
v_F_6373_ = lean_ctor_get(v_date_4656_, 15);
v_a_6374_ = lean_ctor_get(v_date_4656_, 16);
v_b_6375_ = lean_ctor_get(v_date_4656_, 17);
v_B_6376_ = lean_ctor_get(v_date_4656_, 18);
v_h_6377_ = lean_ctor_get(v_date_4656_, 19);
v_K_6378_ = lean_ctor_get(v_date_4656_, 20);
v_k_6379_ = lean_ctor_get(v_date_4656_, 21);
v_H_6380_ = lean_ctor_get(v_date_4656_, 22);
v_m_6381_ = lean_ctor_get(v_date_4656_, 23);
v_s_6382_ = lean_ctor_get(v_date_4656_, 24);
v_S_6383_ = lean_ctor_get(v_date_4656_, 25);
v_A_6384_ = lean_ctor_get(v_date_4656_, 26);
v_n_6385_ = lean_ctor_get(v_date_4656_, 27);
v_N_6386_ = lean_ctor_get(v_date_4656_, 28);
v_V_6387_ = lean_ctor_get(v_date_4656_, 29);
v_z_6388_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_6389_ = lean_ctor_get(v_date_4656_, 31);
v_v_6390_ = lean_ctor_get(v_date_4656_, 32);
v_O_6391_ = lean_ctor_get(v_date_4656_, 33);
v_x_6392_ = lean_ctor_get(v_date_4656_, 35);
v_Z_6393_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_6401_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6401_ == 0)
{
lean_object* v_unused_6402_; 
v_unused_6402_ = lean_ctor_get(v_date_4656_, 34);
lean_dec(v_unused_6402_);
v___x_6395_ = v_date_4656_;
v_isShared_6396_ = v_isSharedCheck_6401_;
goto v_resetjp_6394_;
}
else
{
lean_inc(v_Z_6393_);
lean_inc(v_x_6392_);
lean_inc(v_O_6391_);
lean_inc(v_v_6390_);
lean_inc(v_zabbrev_6389_);
lean_inc(v_z_6388_);
lean_inc(v_V_6387_);
lean_inc(v_N_6386_);
lean_inc(v_n_6385_);
lean_inc(v_A_6384_);
lean_inc(v_S_6383_);
lean_inc(v_s_6382_);
lean_inc(v_m_6381_);
lean_inc(v_H_6380_);
lean_inc(v_k_6379_);
lean_inc(v_K_6378_);
lean_inc(v_h_6377_);
lean_inc(v_B_6376_);
lean_inc(v_b_6375_);
lean_inc(v_a_6374_);
lean_inc(v_F_6373_);
lean_inc(v_c_6372_);
lean_inc(v_e_6371_);
lean_inc(v_E_6370_);
lean_inc(v_W_6369_);
lean_inc(v_w_6368_);
lean_inc(v_q_6367_);
lean_inc(v_Q_6366_);
lean_inc(v_d_6365_);
lean_inc(v_L_6364_);
lean_inc(v_M_6363_);
lean_inc(v_D_6362_);
lean_inc(v_Y_6361_);
lean_inc(v_u_6360_);
lean_inc(v_y_6359_);
lean_inc(v_G_6358_);
lean_dec(v_date_4656_);
v___x_6395_ = lean_box(0);
v_isShared_6396_ = v_isSharedCheck_6401_;
goto v_resetjp_6394_;
}
v_resetjp_6394_:
{
lean_object* v___x_6397_; lean_object* v___x_6399_; 
v___x_6397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6397_, 0, v_data_4658_);
if (v_isShared_6396_ == 0)
{
lean_ctor_set(v___x_6395_, 34, v___x_6397_);
v___x_6399_ = v___x_6395_;
goto v_reusejp_6398_;
}
else
{
lean_object* v_reuseFailAlloc_6400_; 
v_reuseFailAlloc_6400_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6400_, 0, v_G_6358_);
lean_ctor_set(v_reuseFailAlloc_6400_, 1, v_y_6359_);
lean_ctor_set(v_reuseFailAlloc_6400_, 2, v_u_6360_);
lean_ctor_set(v_reuseFailAlloc_6400_, 3, v_Y_6361_);
lean_ctor_set(v_reuseFailAlloc_6400_, 4, v_D_6362_);
lean_ctor_set(v_reuseFailAlloc_6400_, 5, v_M_6363_);
lean_ctor_set(v_reuseFailAlloc_6400_, 6, v_L_6364_);
lean_ctor_set(v_reuseFailAlloc_6400_, 7, v_d_6365_);
lean_ctor_set(v_reuseFailAlloc_6400_, 8, v_Q_6366_);
lean_ctor_set(v_reuseFailAlloc_6400_, 9, v_q_6367_);
lean_ctor_set(v_reuseFailAlloc_6400_, 10, v_w_6368_);
lean_ctor_set(v_reuseFailAlloc_6400_, 11, v_W_6369_);
lean_ctor_set(v_reuseFailAlloc_6400_, 12, v_E_6370_);
lean_ctor_set(v_reuseFailAlloc_6400_, 13, v_e_6371_);
lean_ctor_set(v_reuseFailAlloc_6400_, 14, v_c_6372_);
lean_ctor_set(v_reuseFailAlloc_6400_, 15, v_F_6373_);
lean_ctor_set(v_reuseFailAlloc_6400_, 16, v_a_6374_);
lean_ctor_set(v_reuseFailAlloc_6400_, 17, v_b_6375_);
lean_ctor_set(v_reuseFailAlloc_6400_, 18, v_B_6376_);
lean_ctor_set(v_reuseFailAlloc_6400_, 19, v_h_6377_);
lean_ctor_set(v_reuseFailAlloc_6400_, 20, v_K_6378_);
lean_ctor_set(v_reuseFailAlloc_6400_, 21, v_k_6379_);
lean_ctor_set(v_reuseFailAlloc_6400_, 22, v_H_6380_);
lean_ctor_set(v_reuseFailAlloc_6400_, 23, v_m_6381_);
lean_ctor_set(v_reuseFailAlloc_6400_, 24, v_s_6382_);
lean_ctor_set(v_reuseFailAlloc_6400_, 25, v_S_6383_);
lean_ctor_set(v_reuseFailAlloc_6400_, 26, v_A_6384_);
lean_ctor_set(v_reuseFailAlloc_6400_, 27, v_n_6385_);
lean_ctor_set(v_reuseFailAlloc_6400_, 28, v_N_6386_);
lean_ctor_set(v_reuseFailAlloc_6400_, 29, v_V_6387_);
lean_ctor_set(v_reuseFailAlloc_6400_, 30, v_z_6388_);
lean_ctor_set(v_reuseFailAlloc_6400_, 31, v_zabbrev_6389_);
lean_ctor_set(v_reuseFailAlloc_6400_, 32, v_v_6390_);
lean_ctor_set(v_reuseFailAlloc_6400_, 33, v_O_6391_);
lean_ctor_set(v_reuseFailAlloc_6400_, 34, v___x_6397_);
lean_ctor_set(v_reuseFailAlloc_6400_, 35, v_x_6392_);
lean_ctor_set(v_reuseFailAlloc_6400_, 36, v_Z_6393_);
v___x_6399_ = v_reuseFailAlloc_6400_;
goto v_reusejp_6398_;
}
v_reusejp_6398_:
{
return v___x_6399_;
}
}
}
case 34:
{
lean_object* v_G_6403_; lean_object* v_y_6404_; lean_object* v_u_6405_; lean_object* v_Y_6406_; lean_object* v_D_6407_; lean_object* v_M_6408_; lean_object* v_L_6409_; lean_object* v_d_6410_; lean_object* v_Q_6411_; lean_object* v_q_6412_; lean_object* v_w_6413_; lean_object* v_W_6414_; lean_object* v_E_6415_; lean_object* v_e_6416_; lean_object* v_c_6417_; lean_object* v_F_6418_; lean_object* v_a_6419_; lean_object* v_b_6420_; lean_object* v_B_6421_; lean_object* v_h_6422_; lean_object* v_K_6423_; lean_object* v_k_6424_; lean_object* v_H_6425_; lean_object* v_m_6426_; lean_object* v_s_6427_; lean_object* v_S_6428_; lean_object* v_A_6429_; lean_object* v_n_6430_; lean_object* v_N_6431_; lean_object* v_V_6432_; lean_object* v_z_6433_; lean_object* v_zabbrev_6434_; lean_object* v_v_6435_; lean_object* v_O_6436_; lean_object* v_X_6437_; lean_object* v_Z_6438_; lean_object* v___x_6440_; uint8_t v_isShared_6441_; uint8_t v_isSharedCheck_6446_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_G_6403_ = lean_ctor_get(v_date_4656_, 0);
v_y_6404_ = lean_ctor_get(v_date_4656_, 1);
v_u_6405_ = lean_ctor_get(v_date_4656_, 2);
v_Y_6406_ = lean_ctor_get(v_date_4656_, 3);
v_D_6407_ = lean_ctor_get(v_date_4656_, 4);
v_M_6408_ = lean_ctor_get(v_date_4656_, 5);
v_L_6409_ = lean_ctor_get(v_date_4656_, 6);
v_d_6410_ = lean_ctor_get(v_date_4656_, 7);
v_Q_6411_ = lean_ctor_get(v_date_4656_, 8);
v_q_6412_ = lean_ctor_get(v_date_4656_, 9);
v_w_6413_ = lean_ctor_get(v_date_4656_, 10);
v_W_6414_ = lean_ctor_get(v_date_4656_, 11);
v_E_6415_ = lean_ctor_get(v_date_4656_, 12);
v_e_6416_ = lean_ctor_get(v_date_4656_, 13);
v_c_6417_ = lean_ctor_get(v_date_4656_, 14);
v_F_6418_ = lean_ctor_get(v_date_4656_, 15);
v_a_6419_ = lean_ctor_get(v_date_4656_, 16);
v_b_6420_ = lean_ctor_get(v_date_4656_, 17);
v_B_6421_ = lean_ctor_get(v_date_4656_, 18);
v_h_6422_ = lean_ctor_get(v_date_4656_, 19);
v_K_6423_ = lean_ctor_get(v_date_4656_, 20);
v_k_6424_ = lean_ctor_get(v_date_4656_, 21);
v_H_6425_ = lean_ctor_get(v_date_4656_, 22);
v_m_6426_ = lean_ctor_get(v_date_4656_, 23);
v_s_6427_ = lean_ctor_get(v_date_4656_, 24);
v_S_6428_ = lean_ctor_get(v_date_4656_, 25);
v_A_6429_ = lean_ctor_get(v_date_4656_, 26);
v_n_6430_ = lean_ctor_get(v_date_4656_, 27);
v_N_6431_ = lean_ctor_get(v_date_4656_, 28);
v_V_6432_ = lean_ctor_get(v_date_4656_, 29);
v_z_6433_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_6434_ = lean_ctor_get(v_date_4656_, 31);
v_v_6435_ = lean_ctor_get(v_date_4656_, 32);
v_O_6436_ = lean_ctor_get(v_date_4656_, 33);
v_X_6437_ = lean_ctor_get(v_date_4656_, 34);
v_Z_6438_ = lean_ctor_get(v_date_4656_, 36);
v_isSharedCheck_6446_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6446_ == 0)
{
lean_object* v_unused_6447_; 
v_unused_6447_ = lean_ctor_get(v_date_4656_, 35);
lean_dec(v_unused_6447_);
v___x_6440_ = v_date_4656_;
v_isShared_6441_ = v_isSharedCheck_6446_;
goto v_resetjp_6439_;
}
else
{
lean_inc(v_Z_6438_);
lean_inc(v_X_6437_);
lean_inc(v_O_6436_);
lean_inc(v_v_6435_);
lean_inc(v_zabbrev_6434_);
lean_inc(v_z_6433_);
lean_inc(v_V_6432_);
lean_inc(v_N_6431_);
lean_inc(v_n_6430_);
lean_inc(v_A_6429_);
lean_inc(v_S_6428_);
lean_inc(v_s_6427_);
lean_inc(v_m_6426_);
lean_inc(v_H_6425_);
lean_inc(v_k_6424_);
lean_inc(v_K_6423_);
lean_inc(v_h_6422_);
lean_inc(v_B_6421_);
lean_inc(v_b_6420_);
lean_inc(v_a_6419_);
lean_inc(v_F_6418_);
lean_inc(v_c_6417_);
lean_inc(v_e_6416_);
lean_inc(v_E_6415_);
lean_inc(v_W_6414_);
lean_inc(v_w_6413_);
lean_inc(v_q_6412_);
lean_inc(v_Q_6411_);
lean_inc(v_d_6410_);
lean_inc(v_L_6409_);
lean_inc(v_M_6408_);
lean_inc(v_D_6407_);
lean_inc(v_Y_6406_);
lean_inc(v_u_6405_);
lean_inc(v_y_6404_);
lean_inc(v_G_6403_);
lean_dec(v_date_4656_);
v___x_6440_ = lean_box(0);
v_isShared_6441_ = v_isSharedCheck_6446_;
goto v_resetjp_6439_;
}
v_resetjp_6439_:
{
lean_object* v___x_6442_; lean_object* v___x_6444_; 
v___x_6442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6442_, 0, v_data_4658_);
if (v_isShared_6441_ == 0)
{
lean_ctor_set(v___x_6440_, 35, v___x_6442_);
v___x_6444_ = v___x_6440_;
goto v_reusejp_6443_;
}
else
{
lean_object* v_reuseFailAlloc_6445_; 
v_reuseFailAlloc_6445_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6445_, 0, v_G_6403_);
lean_ctor_set(v_reuseFailAlloc_6445_, 1, v_y_6404_);
lean_ctor_set(v_reuseFailAlloc_6445_, 2, v_u_6405_);
lean_ctor_set(v_reuseFailAlloc_6445_, 3, v_Y_6406_);
lean_ctor_set(v_reuseFailAlloc_6445_, 4, v_D_6407_);
lean_ctor_set(v_reuseFailAlloc_6445_, 5, v_M_6408_);
lean_ctor_set(v_reuseFailAlloc_6445_, 6, v_L_6409_);
lean_ctor_set(v_reuseFailAlloc_6445_, 7, v_d_6410_);
lean_ctor_set(v_reuseFailAlloc_6445_, 8, v_Q_6411_);
lean_ctor_set(v_reuseFailAlloc_6445_, 9, v_q_6412_);
lean_ctor_set(v_reuseFailAlloc_6445_, 10, v_w_6413_);
lean_ctor_set(v_reuseFailAlloc_6445_, 11, v_W_6414_);
lean_ctor_set(v_reuseFailAlloc_6445_, 12, v_E_6415_);
lean_ctor_set(v_reuseFailAlloc_6445_, 13, v_e_6416_);
lean_ctor_set(v_reuseFailAlloc_6445_, 14, v_c_6417_);
lean_ctor_set(v_reuseFailAlloc_6445_, 15, v_F_6418_);
lean_ctor_set(v_reuseFailAlloc_6445_, 16, v_a_6419_);
lean_ctor_set(v_reuseFailAlloc_6445_, 17, v_b_6420_);
lean_ctor_set(v_reuseFailAlloc_6445_, 18, v_B_6421_);
lean_ctor_set(v_reuseFailAlloc_6445_, 19, v_h_6422_);
lean_ctor_set(v_reuseFailAlloc_6445_, 20, v_K_6423_);
lean_ctor_set(v_reuseFailAlloc_6445_, 21, v_k_6424_);
lean_ctor_set(v_reuseFailAlloc_6445_, 22, v_H_6425_);
lean_ctor_set(v_reuseFailAlloc_6445_, 23, v_m_6426_);
lean_ctor_set(v_reuseFailAlloc_6445_, 24, v_s_6427_);
lean_ctor_set(v_reuseFailAlloc_6445_, 25, v_S_6428_);
lean_ctor_set(v_reuseFailAlloc_6445_, 26, v_A_6429_);
lean_ctor_set(v_reuseFailAlloc_6445_, 27, v_n_6430_);
lean_ctor_set(v_reuseFailAlloc_6445_, 28, v_N_6431_);
lean_ctor_set(v_reuseFailAlloc_6445_, 29, v_V_6432_);
lean_ctor_set(v_reuseFailAlloc_6445_, 30, v_z_6433_);
lean_ctor_set(v_reuseFailAlloc_6445_, 31, v_zabbrev_6434_);
lean_ctor_set(v_reuseFailAlloc_6445_, 32, v_v_6435_);
lean_ctor_set(v_reuseFailAlloc_6445_, 33, v_O_6436_);
lean_ctor_set(v_reuseFailAlloc_6445_, 34, v_X_6437_);
lean_ctor_set(v_reuseFailAlloc_6445_, 35, v___x_6442_);
lean_ctor_set(v_reuseFailAlloc_6445_, 36, v_Z_6438_);
v___x_6444_ = v_reuseFailAlloc_6445_;
goto v_reusejp_6443_;
}
v_reusejp_6443_:
{
return v___x_6444_;
}
}
}
default: 
{
lean_object* v_G_6448_; lean_object* v_y_6449_; lean_object* v_u_6450_; lean_object* v_Y_6451_; lean_object* v_D_6452_; lean_object* v_M_6453_; lean_object* v_L_6454_; lean_object* v_d_6455_; lean_object* v_Q_6456_; lean_object* v_q_6457_; lean_object* v_w_6458_; lean_object* v_W_6459_; lean_object* v_E_6460_; lean_object* v_e_6461_; lean_object* v_c_6462_; lean_object* v_F_6463_; lean_object* v_a_6464_; lean_object* v_b_6465_; lean_object* v_B_6466_; lean_object* v_h_6467_; lean_object* v_K_6468_; lean_object* v_k_6469_; lean_object* v_H_6470_; lean_object* v_m_6471_; lean_object* v_s_6472_; lean_object* v_S_6473_; lean_object* v_A_6474_; lean_object* v_n_6475_; lean_object* v_N_6476_; lean_object* v_V_6477_; lean_object* v_z_6478_; lean_object* v_zabbrev_6479_; lean_object* v_v_6480_; lean_object* v_O_6481_; lean_object* v_X_6482_; lean_object* v_x_6483_; lean_object* v___x_6485_; uint8_t v_isShared_6486_; uint8_t v_isSharedCheck_6491_; 
lean_dec_ref_known(v_modifier_4657_, 0);
v_G_6448_ = lean_ctor_get(v_date_4656_, 0);
v_y_6449_ = lean_ctor_get(v_date_4656_, 1);
v_u_6450_ = lean_ctor_get(v_date_4656_, 2);
v_Y_6451_ = lean_ctor_get(v_date_4656_, 3);
v_D_6452_ = lean_ctor_get(v_date_4656_, 4);
v_M_6453_ = lean_ctor_get(v_date_4656_, 5);
v_L_6454_ = lean_ctor_get(v_date_4656_, 6);
v_d_6455_ = lean_ctor_get(v_date_4656_, 7);
v_Q_6456_ = lean_ctor_get(v_date_4656_, 8);
v_q_6457_ = lean_ctor_get(v_date_4656_, 9);
v_w_6458_ = lean_ctor_get(v_date_4656_, 10);
v_W_6459_ = lean_ctor_get(v_date_4656_, 11);
v_E_6460_ = lean_ctor_get(v_date_4656_, 12);
v_e_6461_ = lean_ctor_get(v_date_4656_, 13);
v_c_6462_ = lean_ctor_get(v_date_4656_, 14);
v_F_6463_ = lean_ctor_get(v_date_4656_, 15);
v_a_6464_ = lean_ctor_get(v_date_4656_, 16);
v_b_6465_ = lean_ctor_get(v_date_4656_, 17);
v_B_6466_ = lean_ctor_get(v_date_4656_, 18);
v_h_6467_ = lean_ctor_get(v_date_4656_, 19);
v_K_6468_ = lean_ctor_get(v_date_4656_, 20);
v_k_6469_ = lean_ctor_get(v_date_4656_, 21);
v_H_6470_ = lean_ctor_get(v_date_4656_, 22);
v_m_6471_ = lean_ctor_get(v_date_4656_, 23);
v_s_6472_ = lean_ctor_get(v_date_4656_, 24);
v_S_6473_ = lean_ctor_get(v_date_4656_, 25);
v_A_6474_ = lean_ctor_get(v_date_4656_, 26);
v_n_6475_ = lean_ctor_get(v_date_4656_, 27);
v_N_6476_ = lean_ctor_get(v_date_4656_, 28);
v_V_6477_ = lean_ctor_get(v_date_4656_, 29);
v_z_6478_ = lean_ctor_get(v_date_4656_, 30);
v_zabbrev_6479_ = lean_ctor_get(v_date_4656_, 31);
v_v_6480_ = lean_ctor_get(v_date_4656_, 32);
v_O_6481_ = lean_ctor_get(v_date_4656_, 33);
v_X_6482_ = lean_ctor_get(v_date_4656_, 34);
v_x_6483_ = lean_ctor_get(v_date_4656_, 35);
v_isSharedCheck_6491_ = !lean_is_exclusive(v_date_4656_);
if (v_isSharedCheck_6491_ == 0)
{
lean_object* v_unused_6492_; 
v_unused_6492_ = lean_ctor_get(v_date_4656_, 36);
lean_dec(v_unused_6492_);
v___x_6485_ = v_date_4656_;
v_isShared_6486_ = v_isSharedCheck_6491_;
goto v_resetjp_6484_;
}
else
{
lean_inc(v_x_6483_);
lean_inc(v_X_6482_);
lean_inc(v_O_6481_);
lean_inc(v_v_6480_);
lean_inc(v_zabbrev_6479_);
lean_inc(v_z_6478_);
lean_inc(v_V_6477_);
lean_inc(v_N_6476_);
lean_inc(v_n_6475_);
lean_inc(v_A_6474_);
lean_inc(v_S_6473_);
lean_inc(v_s_6472_);
lean_inc(v_m_6471_);
lean_inc(v_H_6470_);
lean_inc(v_k_6469_);
lean_inc(v_K_6468_);
lean_inc(v_h_6467_);
lean_inc(v_B_6466_);
lean_inc(v_b_6465_);
lean_inc(v_a_6464_);
lean_inc(v_F_6463_);
lean_inc(v_c_6462_);
lean_inc(v_e_6461_);
lean_inc(v_E_6460_);
lean_inc(v_W_6459_);
lean_inc(v_w_6458_);
lean_inc(v_q_6457_);
lean_inc(v_Q_6456_);
lean_inc(v_d_6455_);
lean_inc(v_L_6454_);
lean_inc(v_M_6453_);
lean_inc(v_D_6452_);
lean_inc(v_Y_6451_);
lean_inc(v_u_6450_);
lean_inc(v_y_6449_);
lean_inc(v_G_6448_);
lean_dec(v_date_4656_);
v___x_6485_ = lean_box(0);
v_isShared_6486_ = v_isSharedCheck_6491_;
goto v_resetjp_6484_;
}
v_resetjp_6484_:
{
lean_object* v___x_6487_; lean_object* v___x_6489_; 
v___x_6487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6487_, 0, v_data_4658_);
if (v_isShared_6486_ == 0)
{
lean_ctor_set(v___x_6485_, 36, v___x_6487_);
v___x_6489_ = v___x_6485_;
goto v_reusejp_6488_;
}
else
{
lean_object* v_reuseFailAlloc_6490_; 
v_reuseFailAlloc_6490_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6490_, 0, v_G_6448_);
lean_ctor_set(v_reuseFailAlloc_6490_, 1, v_y_6449_);
lean_ctor_set(v_reuseFailAlloc_6490_, 2, v_u_6450_);
lean_ctor_set(v_reuseFailAlloc_6490_, 3, v_Y_6451_);
lean_ctor_set(v_reuseFailAlloc_6490_, 4, v_D_6452_);
lean_ctor_set(v_reuseFailAlloc_6490_, 5, v_M_6453_);
lean_ctor_set(v_reuseFailAlloc_6490_, 6, v_L_6454_);
lean_ctor_set(v_reuseFailAlloc_6490_, 7, v_d_6455_);
lean_ctor_set(v_reuseFailAlloc_6490_, 8, v_Q_6456_);
lean_ctor_set(v_reuseFailAlloc_6490_, 9, v_q_6457_);
lean_ctor_set(v_reuseFailAlloc_6490_, 10, v_w_6458_);
lean_ctor_set(v_reuseFailAlloc_6490_, 11, v_W_6459_);
lean_ctor_set(v_reuseFailAlloc_6490_, 12, v_E_6460_);
lean_ctor_set(v_reuseFailAlloc_6490_, 13, v_e_6461_);
lean_ctor_set(v_reuseFailAlloc_6490_, 14, v_c_6462_);
lean_ctor_set(v_reuseFailAlloc_6490_, 15, v_F_6463_);
lean_ctor_set(v_reuseFailAlloc_6490_, 16, v_a_6464_);
lean_ctor_set(v_reuseFailAlloc_6490_, 17, v_b_6465_);
lean_ctor_set(v_reuseFailAlloc_6490_, 18, v_B_6466_);
lean_ctor_set(v_reuseFailAlloc_6490_, 19, v_h_6467_);
lean_ctor_set(v_reuseFailAlloc_6490_, 20, v_K_6468_);
lean_ctor_set(v_reuseFailAlloc_6490_, 21, v_k_6469_);
lean_ctor_set(v_reuseFailAlloc_6490_, 22, v_H_6470_);
lean_ctor_set(v_reuseFailAlloc_6490_, 23, v_m_6471_);
lean_ctor_set(v_reuseFailAlloc_6490_, 24, v_s_6472_);
lean_ctor_set(v_reuseFailAlloc_6490_, 25, v_S_6473_);
lean_ctor_set(v_reuseFailAlloc_6490_, 26, v_A_6474_);
lean_ctor_set(v_reuseFailAlloc_6490_, 27, v_n_6475_);
lean_ctor_set(v_reuseFailAlloc_6490_, 28, v_N_6476_);
lean_ctor_set(v_reuseFailAlloc_6490_, 29, v_V_6477_);
lean_ctor_set(v_reuseFailAlloc_6490_, 30, v_z_6478_);
lean_ctor_set(v_reuseFailAlloc_6490_, 31, v_zabbrev_6479_);
lean_ctor_set(v_reuseFailAlloc_6490_, 32, v_v_6480_);
lean_ctor_set(v_reuseFailAlloc_6490_, 33, v_O_6481_);
lean_ctor_set(v_reuseFailAlloc_6490_, 34, v_X_6482_);
lean_ctor_set(v_reuseFailAlloc_6490_, 35, v_x_6483_);
lean_ctor_set(v_reuseFailAlloc_6490_, 36, v___x_6487_);
v___x_6489_ = v_reuseFailAlloc_6490_;
goto v_reusejp_6488_;
}
v_reusejp_6488_:
{
return v___x_6489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object* v_year_6493_, uint8_t v_x_6494_){
_start:
{
if (v_x_6494_ == 0)
{
lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6495_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6496_ = lean_int_add(v_year_6493_, v___x_6495_);
v___x_6497_ = lean_int_neg(v___x_6496_);
lean_dec(v___x_6496_);
return v___x_6497_;
}
else
{
lean_inc(v_year_6493_);
return v_year_6493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object* v_year_6498_, lean_object* v_x_6499_){
_start:
{
uint8_t v_x_42__boxed_6500_; lean_object* v_res_6501_; 
v_x_42__boxed_6500_ = lean_unbox(v_x_6499_);
v_res_6501_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6498_, v_x_42__boxed_6500_);
lean_dec(v_year_6498_);
return v_res_6501_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t v_x_6502_){
_start:
{
switch(v_x_6502_)
{
case 1:
{
uint8_t v___x_6503_; 
v___x_6503_ = 1;
return v___x_6503_;
}
case 2:
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object* v_x_6506_){
_start:
{
uint8_t v_x_28__boxed_6507_; uint8_t v_res_6508_; lean_object* v_r_6509_; 
v_x_28__boxed_6507_ = lean_unbox(v_x_6506_);
v_res_6508_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_28__boxed_6507_);
v_r_6509_ = lean_box(v_res_6508_);
return v_r_6509_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(uint8_t v_x_6510_){
_start:
{
switch(v_x_6510_)
{
case 3:
{
uint8_t v___x_6511_; 
v___x_6511_ = 1;
return v___x_6511_;
}
case 4:
{
uint8_t v___x_6512_; 
v___x_6512_ = 1;
return v___x_6512_;
}
case 5:
{
uint8_t v___x_6513_; 
v___x_6513_ = 1;
return v___x_6513_;
}
default: 
{
uint8_t v___x_6514_; 
v___x_6514_ = 0;
return v___x_6514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object* v_x_6515_){
_start:
{
uint8_t v_x_38__boxed_6516_; uint8_t v_res_6517_; lean_object* v_r_6518_; 
v_x_38__boxed_6516_ = lean_unbox(v_x_6515_);
v_res_6517_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_x_38__boxed_6516_);
v_r_6518_ = lean_box(v_res_6517_);
return v_r_6518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object* v_val_6519_, lean_object* v_x_6520_){
_start:
{
lean_inc_ref(v_val_6519_);
return v_val_6519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object* v_val_6521_, lean_object* v_x_6522_){
_start:
{
lean_object* v_res_6523_; 
v_res_6523_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v_val_6521_, v_x_6522_);
lean_dec_ref(v_val_6521_);
return v_res_6523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object* v___y_6524_, lean_object* v_00___6525_){
_start:
{
uint8_t v___x_6526_; lean_object* v___x_6527_; 
v___x_6526_ = 1;
v___x_6527_ = l_Std_Time_TimeZone_Offset_toIsoString(v___y_6524_, v___x_6526_);
return v___x_6527_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1(void){
_start:
{
lean_object* v___x_6530_; lean_object* v___x_6531_; 
v___x_6530_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6531_ = lean_int_neg(v___x_6530_);
return v___x_6531_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2(void){
_start:
{
lean_object* v___x_6532_; lean_object* v___x_6533_; 
v___x_6532_ = lean_unsigned_to_nat(1000000u);
v___x_6533_ = lean_nat_to_int(v___x_6532_);
return v___x_6533_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3(void){
_start:
{
lean_object* v___x_6534_; lean_object* v___x_6535_; lean_object* v___x_6536_; 
v___x_6534_ = lean_unsigned_to_nat(1000000000u);
v___x_6535_ = lean_unsigned_to_nat(0u);
v___x_6536_ = lean_nat_mod(v___x_6535_, v___x_6534_);
return v___x_6536_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4(void){
_start:
{
lean_object* v___x_6537_; lean_object* v___x_6538_; 
v___x_6537_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3);
v___x_6538_ = lean_nat_to_int(v___x_6537_);
return v___x_6538_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5(void){
_start:
{
lean_object* v___x_6539_; uint8_t v___x_6540_; lean_object* v___x_6541_; 
v___x_6539_ = lean_unsigned_to_nat(0u);
v___x_6540_ = 1;
v___x_6541_ = l_Std_Time_Second_instOfNatOrdinal(v___x_6540_, v___x_6539_);
return v___x_6541_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6(void){
_start:
{
lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; 
v___x_6542_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3);
v___x_6543_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6544_ = lean_int_add(v___x_6543_, v___x_6542_);
return v___x_6544_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7(void){
_start:
{
lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; 
v___x_6545_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6546_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6547_ = lean_int_sub(v___x_6546_, v___x_6545_);
return v___x_6547_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8(void){
_start:
{
lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v_range_6550_; 
v___x_6548_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6549_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7);
v_range_6550_ = lean_int_add(v___x_6549_, v___x_6548_);
return v_range_6550_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9(void){
_start:
{
lean_object* v___x_6551_; lean_object* v___x_6552_; 
v___x_6551_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6552_ = lean_int_sub(v___x_6551_, v___x_6551_);
return v___x_6552_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10(void){
_start:
{
lean_object* v_range_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; 
v_range_6553_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6554_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9);
v___x_6555_ = lean_int_emod(v___x_6554_, v_range_6553_);
return v___x_6555_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11(void){
_start:
{
lean_object* v_range_6556_; lean_object* v___x_6557_; lean_object* v___x_6558_; 
v_range_6556_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6557_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10);
v___x_6558_ = lean_int_add(v___x_6557_, v_range_6556_);
return v___x_6558_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12(void){
_start:
{
lean_object* v_range_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; 
v_range_6559_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6560_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11);
v___x_6561_ = lean_int_emod(v___x_6560_, v_range_6559_);
return v___x_6561_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13(void){
_start:
{
lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; 
v___x_6562_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6563_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12);
v___x_6564_ = lean_int_add(v___x_6563_, v___x_6562_);
return v___x_6564_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14(void){
_start:
{
lean_object* v___x_6565_; lean_object* v___x_6566_; 
v___x_6565_ = lean_unsigned_to_nat(30u);
v___x_6566_ = lean_nat_to_int(v___x_6565_);
return v___x_6566_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15(void){
_start:
{
lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6569_; 
v___x_6567_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14);
v___x_6568_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6569_ = lean_int_add(v___x_6568_, v___x_6567_);
return v___x_6569_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16(void){
_start:
{
lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; 
v___x_6570_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6571_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6572_ = lean_int_sub(v___x_6571_, v___x_6570_);
return v___x_6572_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17(void){
_start:
{
lean_object* v___x_6573_; lean_object* v___x_6574_; lean_object* v_range_6575_; 
v___x_6573_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6574_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v_range_6575_ = lean_int_add(v___x_6574_, v___x_6573_);
return v_range_6575_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18(void){
_start:
{
lean_object* v___x_6576_; lean_object* v___x_6577_; lean_object* v___x_6578_; 
v___x_6576_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6577_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6578_ = lean_int_sub(v___x_6577_, v___x_6576_);
return v___x_6578_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19(void){
_start:
{
lean_object* v_range_6579_; lean_object* v___x_6580_; lean_object* v___x_6581_; 
v_range_6579_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6580_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6581_ = lean_int_emod(v___x_6580_, v_range_6579_);
return v___x_6581_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20(void){
_start:
{
lean_object* v_range_6582_; lean_object* v___x_6583_; lean_object* v___x_6584_; 
v_range_6582_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6583_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19);
v___x_6584_ = lean_int_add(v___x_6583_, v_range_6582_);
return v___x_6584_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21(void){
_start:
{
lean_object* v_range_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; 
v_range_6585_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6586_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20);
v___x_6587_ = lean_int_emod(v___x_6586_, v_range_6585_);
return v___x_6587_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22(void){
_start:
{
lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v___x_6590_; 
v___x_6588_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6589_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21);
v___x_6590_ = lean_int_add(v___x_6589_, v___x_6588_);
return v___x_6590_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23(void){
_start:
{
lean_object* v___x_6591_; lean_object* v___x_6592_; 
v___x_6591_ = lean_unsigned_to_nat(11u);
v___x_6592_ = lean_nat_to_int(v___x_6591_);
return v___x_6592_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24(void){
_start:
{
lean_object* v___x_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; 
v___x_6593_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23);
v___x_6594_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6595_ = lean_int_add(v___x_6594_, v___x_6593_);
return v___x_6595_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25(void){
_start:
{
lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; 
v___x_6596_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6597_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6598_ = lean_int_sub(v___x_6597_, v___x_6596_);
return v___x_6598_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26(void){
_start:
{
lean_object* v___x_6599_; lean_object* v___x_6600_; lean_object* v_range_6601_; 
v___x_6599_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6600_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25);
v_range_6601_ = lean_int_add(v___x_6600_, v___x_6599_);
return v_range_6601_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27(void){
_start:
{
lean_object* v_range_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; 
v_range_6602_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6603_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6604_ = lean_int_emod(v___x_6603_, v_range_6602_);
return v___x_6604_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28(void){
_start:
{
lean_object* v_range_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; 
v_range_6605_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6606_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27);
v___x_6607_ = lean_int_add(v___x_6606_, v_range_6605_);
return v___x_6607_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29(void){
_start:
{
lean_object* v_range_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; 
v_range_6608_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6609_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28);
v___x_6610_ = lean_int_emod(v___x_6609_, v_range_6608_);
return v___x_6610_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30(void){
_start:
{
lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; 
v___x_6611_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6612_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29);
v___x_6613_ = lean_int_add(v___x_6612_, v___x_6611_);
return v___x_6613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object* v_builder_6614_, lean_object* v_aw_6615_){
_start:
{
lean_object* v___y_6617_; lean_object* v___y_6618_; lean_object* v___y_6657_; lean_object* v___y_6658_; lean_object* v___y_6661_; lean_object* v___y_6662_; lean_object* v___y_6663_; lean_object* v___y_6664_; lean_object* v___y_6665_; uint8_t v___y_6666_; lean_object* v___y_6674_; lean_object* v___y_6675_; lean_object* v___y_6676_; lean_object* v___y_6677_; uint8_t v___y_6678_; lean_object* v___y_6679_; uint8_t v___y_6680_; lean_object* v___y_6682_; lean_object* v___y_6683_; lean_object* v___y_6684_; lean_object* v___y_6685_; lean_object* v___y_6686_; lean_object* v_G_6698_; lean_object* v_y_6699_; lean_object* v_u_6700_; lean_object* v_Y_6701_; lean_object* v_M_6702_; lean_object* v_L_6703_; lean_object* v_d_6704_; lean_object* v_a_6705_; lean_object* v_b_6706_; lean_object* v_B_6707_; lean_object* v_h_6708_; lean_object* v_K_6709_; lean_object* v_k_6710_; lean_object* v_H_6711_; lean_object* v_m_6712_; lean_object* v_s_6713_; lean_object* v_S_6714_; lean_object* v_A_6715_; lean_object* v_n_6716_; lean_object* v_N_6717_; lean_object* v_V_6718_; lean_object* v_z_6719_; lean_object* v_zabbrev_6720_; lean_object* v_v_6721_; lean_object* v_O_6722_; lean_object* v_X_6723_; lean_object* v_x_6724_; lean_object* v_Z_6725_; lean_object* v___y_6727_; lean_object* v___y_6728_; lean_object* v___y_6729_; lean_object* v___y_6730_; lean_object* v___y_6731_; lean_object* v___y_6732_; lean_object* v___y_6733_; lean_object* v___y_6734_; lean_object* v___y_6743_; lean_object* v___y_6744_; lean_object* v___y_6745_; lean_object* v___y_6746_; lean_object* v___y_6747_; lean_object* v___y_6748_; lean_object* v___y_6749_; lean_object* v___y_6754_; lean_object* v___y_6755_; lean_object* v___y_6756_; lean_object* v___y_6757_; lean_object* v___y_6758_; lean_object* v___y_6759_; lean_object* v___y_6763_; lean_object* v___y_6764_; lean_object* v___y_6765_; lean_object* v___y_6766_; lean_object* v___y_6767_; lean_object* v___y_6771_; lean_object* v___y_6772_; lean_object* v___y_6773_; lean_object* v___y_6774_; lean_object* v___y_6782_; lean_object* v___y_6783_; lean_object* v___y_6784_; lean_object* v___y_6785_; uint8_t v_val_6786_; lean_object* v___y_6794_; lean_object* v___y_6795_; lean_object* v___y_6796_; lean_object* v___y_6797_; lean_object* v___y_6807_; lean_object* v___y_6808_; lean_object* v___y_6809_; uint8_t v___y_6810_; lean_object* v___y_6817_; lean_object* v___y_6818_; lean_object* v___y_6819_; lean_object* v___y_6824_; lean_object* v___y_6825_; lean_object* v___y_6829_; lean_object* v___y_6830_; lean_object* v___y_6831_; lean_object* v___y_6838_; lean_object* v___y_6839_; lean_object* v___y_6840_; lean_object* v___y_6845_; 
v_G_6698_ = lean_ctor_get(v_builder_6614_, 0);
lean_inc(v_G_6698_);
v_y_6699_ = lean_ctor_get(v_builder_6614_, 1);
lean_inc(v_y_6699_);
v_u_6700_ = lean_ctor_get(v_builder_6614_, 2);
lean_inc(v_u_6700_);
v_Y_6701_ = lean_ctor_get(v_builder_6614_, 3);
lean_inc(v_Y_6701_);
v_M_6702_ = lean_ctor_get(v_builder_6614_, 5);
lean_inc(v_M_6702_);
v_L_6703_ = lean_ctor_get(v_builder_6614_, 6);
lean_inc(v_L_6703_);
v_d_6704_ = lean_ctor_get(v_builder_6614_, 7);
lean_inc(v_d_6704_);
v_a_6705_ = lean_ctor_get(v_builder_6614_, 16);
lean_inc(v_a_6705_);
v_b_6706_ = lean_ctor_get(v_builder_6614_, 17);
lean_inc(v_b_6706_);
v_B_6707_ = lean_ctor_get(v_builder_6614_, 18);
lean_inc(v_B_6707_);
v_h_6708_ = lean_ctor_get(v_builder_6614_, 19);
lean_inc(v_h_6708_);
v_K_6709_ = lean_ctor_get(v_builder_6614_, 20);
lean_inc(v_K_6709_);
v_k_6710_ = lean_ctor_get(v_builder_6614_, 21);
lean_inc(v_k_6710_);
v_H_6711_ = lean_ctor_get(v_builder_6614_, 22);
lean_inc(v_H_6711_);
v_m_6712_ = lean_ctor_get(v_builder_6614_, 23);
lean_inc(v_m_6712_);
v_s_6713_ = lean_ctor_get(v_builder_6614_, 24);
lean_inc(v_s_6713_);
v_S_6714_ = lean_ctor_get(v_builder_6614_, 25);
lean_inc(v_S_6714_);
v_A_6715_ = lean_ctor_get(v_builder_6614_, 26);
lean_inc(v_A_6715_);
v_n_6716_ = lean_ctor_get(v_builder_6614_, 27);
lean_inc(v_n_6716_);
v_N_6717_ = lean_ctor_get(v_builder_6614_, 28);
lean_inc(v_N_6717_);
v_V_6718_ = lean_ctor_get(v_builder_6614_, 29);
lean_inc(v_V_6718_);
v_z_6719_ = lean_ctor_get(v_builder_6614_, 30);
lean_inc(v_z_6719_);
v_zabbrev_6720_ = lean_ctor_get(v_builder_6614_, 31);
lean_inc(v_zabbrev_6720_);
v_v_6721_ = lean_ctor_get(v_builder_6614_, 32);
lean_inc(v_v_6721_);
v_O_6722_ = lean_ctor_get(v_builder_6614_, 33);
lean_inc(v_O_6722_);
v_X_6723_ = lean_ctor_get(v_builder_6614_, 34);
lean_inc(v_X_6723_);
v_x_6724_ = lean_ctor_get(v_builder_6614_, 35);
lean_inc(v_x_6724_);
v_Z_6725_ = lean_ctor_get(v_builder_6614_, 36);
lean_inc(v_Z_6725_);
lean_dec_ref(v_builder_6614_);
if (lean_obj_tag(v_O_6722_) == 0)
{
if (lean_obj_tag(v_X_6723_) == 0)
{
if (lean_obj_tag(v_x_6724_) == 0)
{
if (lean_obj_tag(v_Z_6725_) == 0)
{
lean_object* v___x_6852_; 
v___x_6852_ = l_Std_Time_TimeZone_Offset_zero;
v___y_6845_ = v___x_6852_;
goto v___jp_6844_;
}
else
{
lean_object* v_val_6853_; 
v_val_6853_ = lean_ctor_get(v_Z_6725_, 0);
lean_inc(v_val_6853_);
lean_dec_ref_known(v_Z_6725_, 1);
v___y_6845_ = v_val_6853_;
goto v___jp_6844_;
}
}
else
{
lean_object* v_val_6854_; 
lean_dec(v_Z_6725_);
v_val_6854_ = lean_ctor_get(v_x_6724_, 0);
lean_inc(v_val_6854_);
lean_dec_ref_known(v_x_6724_, 1);
v___y_6845_ = v_val_6854_;
goto v___jp_6844_;
}
}
else
{
lean_object* v_val_6855_; 
lean_dec(v_Z_6725_);
lean_dec(v_x_6724_);
v_val_6855_ = lean_ctor_get(v_X_6723_, 0);
lean_inc(v_val_6855_);
lean_dec_ref_known(v_X_6723_, 1);
v___y_6845_ = v_val_6855_;
goto v___jp_6844_;
}
}
else
{
lean_object* v_val_6856_; 
lean_dec(v_Z_6725_);
lean_dec(v_x_6724_);
lean_dec(v_X_6723_);
v_val_6856_ = lean_ctor_get(v_O_6722_, 0);
lean_inc(v_val_6856_);
lean_dec_ref_known(v_O_6722_, 1);
v___y_6845_ = v_val_6856_;
goto v___jp_6844_;
}
v___jp_6616_:
{
if (lean_obj_tag(v___y_6617_) == 0)
{
lean_object* v___x_6619_; 
lean_dec_ref(v___y_6618_);
v___x_6619_ = lean_box(0);
return v___x_6619_;
}
else
{
lean_object* v_val_6620_; lean_object* v___x_6622_; uint8_t v_isShared_6623_; uint8_t v_isSharedCheck_6655_; 
v_val_6620_ = lean_ctor_get(v___y_6617_, 0);
v_isSharedCheck_6655_ = !lean_is_exclusive(v___y_6617_);
if (v_isSharedCheck_6655_ == 0)
{
v___x_6622_ = v___y_6617_;
v_isShared_6623_ = v_isSharedCheck_6655_;
goto v_resetjp_6621_;
}
else
{
lean_inc(v_val_6620_);
lean_dec(v___y_6617_);
v___x_6622_ = lean_box(0);
v_isShared_6623_ = v_isSharedCheck_6655_;
goto v_resetjp_6621_;
}
v_resetjp_6621_:
{
lean_object* v_offset_6624_; lean_object* v_name_6625_; lean_object* v_abbreviation_6626_; uint8_t v_isDST_6627_; uint8_t v___x_6628_; uint8_t v___x_6629_; lean_object* v_ltt_6630_; lean_object* v___x_6631_; lean_object* v___x_6632_; lean_object* v___x_6633_; lean_object* v_wt_6634_; lean_object* v_ltt_6635_; lean_object* v_tz_6636_; lean_object* v_offset_6637_; lean_object* v_second_6638_; lean_object* v_nano_6639_; lean_object* v___f_6640_; lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6653_; 
v_offset_6624_ = lean_ctor_get(v___y_6618_, 0);
lean_inc(v_offset_6624_);
v_name_6625_ = lean_ctor_get(v___y_6618_, 1);
lean_inc_ref(v_name_6625_);
v_abbreviation_6626_ = lean_ctor_get(v___y_6618_, 2);
lean_inc_ref(v_abbreviation_6626_);
v_isDST_6627_ = lean_ctor_get_uint8(v___y_6618_, sizeof(void*)*3);
lean_dec_ref(v___y_6618_);
v___x_6628_ = 0;
v___x_6629_ = 1;
v_ltt_6630_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6630_, 0, v_offset_6624_);
lean_ctor_set(v_ltt_6630_, 1, v_abbreviation_6626_);
lean_ctor_set(v_ltt_6630_, 2, v_name_6625_);
lean_ctor_set_uint8(v_ltt_6630_, sizeof(void*)*3, v_isDST_6627_);
lean_ctor_set_uint8(v_ltt_6630_, sizeof(void*)*3 + 1, v___x_6628_);
lean_ctor_set_uint8(v_ltt_6630_, sizeof(void*)*3 + 2, v___x_6629_);
v___x_6631_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6632_ = lean_box(0);
v___x_6633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6633_, 0, v_ltt_6630_);
lean_ctor_set(v___x_6633_, 1, v___x_6631_);
lean_ctor_set(v___x_6633_, 2, v___x_6632_);
lean_inc(v_val_6620_);
v_wt_6634_ = l_Std_Time_PlainDateTime_toWallTime(v_val_6620_);
lean_inc_ref(v___x_6633_);
v_ltt_6635_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_6633_, v_wt_6634_);
v_tz_6636_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_6635_);
lean_dec_ref(v_ltt_6635_);
v_offset_6637_ = lean_ctor_get(v_tz_6636_, 0);
lean_inc(v_offset_6637_);
v_second_6638_ = lean_ctor_get(v_wt_6634_, 0);
lean_inc(v_second_6638_);
v_nano_6639_ = lean_ctor_get(v_wt_6634_, 1);
lean_inc(v_nano_6639_);
lean_dec_ref(v_wt_6634_);
v___f_6640_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6640_, 0, v_val_6620_);
v___x_6641_ = lean_mk_thunk(v___f_6640_);
v___x_6642_ = lean_int_neg(v_offset_6637_);
lean_dec(v_offset_6637_);
v___x_6643_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1);
v___x_6644_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6645_ = lean_int_mul(v_second_6638_, v___x_6644_);
lean_dec(v_second_6638_);
v___x_6646_ = lean_int_add(v___x_6645_, v_nano_6639_);
lean_dec(v_nano_6639_);
lean_dec(v___x_6645_);
v___x_6647_ = lean_int_mul(v___x_6642_, v___x_6644_);
lean_dec(v___x_6642_);
v___x_6648_ = lean_int_add(v___x_6647_, v___x_6643_);
lean_dec(v___x_6647_);
v___x_6649_ = lean_int_add(v___x_6646_, v___x_6648_);
lean_dec(v___x_6648_);
lean_dec(v___x_6646_);
v___x_6650_ = l_Std_Time_Duration_ofNanoseconds(v___x_6649_);
lean_dec(v___x_6649_);
v___x_6651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6651_, 0, v___x_6641_);
lean_ctor_set(v___x_6651_, 1, v___x_6650_);
lean_ctor_set(v___x_6651_, 2, v___x_6633_);
lean_ctor_set(v___x_6651_, 3, v_tz_6636_);
if (v_isShared_6623_ == 0)
{
lean_ctor_set(v___x_6622_, 0, v___x_6651_);
v___x_6653_ = v___x_6622_;
goto v_reusejp_6652_;
}
else
{
lean_object* v_reuseFailAlloc_6654_; 
v_reuseFailAlloc_6654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6654_, 0, v___x_6651_);
v___x_6653_ = v_reuseFailAlloc_6654_;
goto v_reusejp_6652_;
}
v_reusejp_6652_:
{
return v___x_6653_;
}
}
}
}
v___jp_6656_:
{
if (lean_obj_tag(v_aw_6615_) == 0)
{
lean_object* v_a_6659_; 
lean_dec_ref(v___y_6657_);
v_a_6659_ = lean_ctor_get(v_aw_6615_, 0);
lean_inc_ref(v_a_6659_);
lean_dec_ref_known(v_aw_6615_, 1);
v___y_6617_ = v___y_6658_;
v___y_6618_ = v_a_6659_;
goto v___jp_6616_;
}
else
{
v___y_6617_ = v___y_6658_;
v___y_6618_ = v___y_6657_;
goto v___jp_6616_;
}
}
v___jp_6660_:
{
lean_object* v___x_6667_; uint8_t v___x_6668_; 
v___x_6667_ = l_Std_Time_Month_Ordinal_days(v___y_6666_, v___y_6665_);
v___x_6668_ = lean_int_dec_le(v___y_6663_, v___x_6667_);
lean_dec(v___x_6667_);
if (v___x_6668_ == 0)
{
lean_object* v___x_6669_; 
lean_dec(v___y_6665_);
lean_dec_ref(v___y_6664_);
lean_dec(v___y_6663_);
lean_dec(v___y_6661_);
v___x_6669_ = lean_box(0);
v___y_6657_ = v___y_6662_;
v___y_6658_ = v___x_6669_;
goto v___jp_6656_;
}
else
{
lean_object* v_date_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; 
v_date_6670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_date_6670_, 0, v___y_6661_);
lean_ctor_set(v_date_6670_, 1, v___y_6665_);
lean_ctor_set(v_date_6670_, 2, v___y_6663_);
v___x_6671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6671_, 0, v_date_6670_);
lean_ctor_set(v___x_6671_, 1, v___y_6664_);
v___x_6672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6672_, 0, v___x_6671_);
v___y_6657_ = v___y_6662_;
v___y_6658_ = v___x_6672_;
goto v___jp_6656_;
}
}
v___jp_6673_:
{
if (v___y_6678_ == 0)
{
v___y_6661_ = v___y_6676_;
v___y_6662_ = v___y_6675_;
v___y_6663_ = v___y_6674_;
v___y_6664_ = v___y_6677_;
v___y_6665_ = v___y_6679_;
v___y_6666_ = v___y_6678_;
goto v___jp_6660_;
}
else
{
v___y_6661_ = v___y_6676_;
v___y_6662_ = v___y_6675_;
v___y_6663_ = v___y_6674_;
v___y_6664_ = v___y_6677_;
v___y_6665_ = v___y_6679_;
v___y_6666_ = v___y_6680_;
goto v___jp_6660_;
}
}
v___jp_6681_:
{
lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; uint8_t v___x_6690_; lean_object* v___x_6691_; lean_object* v___x_6692_; uint8_t v___x_6693_; 
v___x_6687_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_6688_ = lean_int_mod(v___y_6684_, v___x_6687_);
v___x_6689_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6690_ = lean_int_dec_eq(v___x_6688_, v___x_6689_);
lean_dec(v___x_6688_);
v___x_6691_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6692_ = lean_int_mod(v___y_6684_, v___x_6691_);
v___x_6693_ = lean_int_dec_eq(v___x_6692_, v___x_6689_);
lean_dec(v___x_6692_);
if (v___x_6693_ == 0)
{
uint8_t v___x_6694_; 
v___x_6694_ = 1;
v___y_6674_ = v___y_6682_;
v___y_6675_ = v___y_6683_;
v___y_6676_ = v___y_6684_;
v___y_6677_ = v___y_6686_;
v___y_6678_ = v___x_6690_;
v___y_6679_ = v___y_6685_;
v___y_6680_ = v___x_6694_;
goto v___jp_6673_;
}
else
{
lean_object* v___x_6695_; lean_object* v___x_6696_; uint8_t v___x_6697_; 
v___x_6695_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_6696_ = lean_int_mod(v___y_6684_, v___x_6695_);
v___x_6697_ = lean_int_dec_eq(v___x_6696_, v___x_6689_);
lean_dec(v___x_6696_);
v___y_6674_ = v___y_6682_;
v___y_6675_ = v___y_6683_;
v___y_6676_ = v___y_6684_;
v___y_6677_ = v___y_6686_;
v___y_6678_ = v___x_6690_;
v___y_6679_ = v___y_6685_;
v___y_6680_ = v___x_6697_;
goto v___jp_6673_;
}
}
v___jp_6726_:
{
if (lean_obj_tag(v_N_6717_) == 0)
{
if (lean_obj_tag(v_A_6715_) == 0)
{
lean_object* v___x_6735_; 
v___x_6735_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6735_, 0, v___y_6732_);
lean_ctor_set(v___x_6735_, 1, v___y_6731_);
lean_ctor_set(v___x_6735_, 2, v___y_6730_);
lean_ctor_set(v___x_6735_, 3, v___y_6734_);
v___y_6682_ = v___y_6729_;
v___y_6683_ = v___y_6728_;
v___y_6684_ = v___y_6727_;
v___y_6685_ = v___y_6733_;
v___y_6686_ = v___x_6735_;
goto v___jp_6681_;
}
else
{
lean_object* v_val_6736_; lean_object* v___x_6737_; lean_object* v___x_6738_; lean_object* v___x_6739_; 
lean_dec(v___y_6734_);
lean_dec(v___y_6732_);
lean_dec(v___y_6731_);
lean_dec(v___y_6730_);
v_val_6736_ = lean_ctor_get(v_A_6715_, 0);
lean_inc(v_val_6736_);
lean_dec_ref_known(v_A_6715_, 1);
v___x_6737_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2);
v___x_6738_ = lean_int_mul(v_val_6736_, v___x_6737_);
lean_dec(v_val_6736_);
v___x_6739_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_6738_);
lean_dec(v___x_6738_);
v___y_6682_ = v___y_6729_;
v___y_6683_ = v___y_6728_;
v___y_6684_ = v___y_6727_;
v___y_6685_ = v___y_6733_;
v___y_6686_ = v___x_6739_;
goto v___jp_6681_;
}
}
else
{
lean_object* v_val_6740_; lean_object* v___x_6741_; 
lean_dec(v___y_6734_);
lean_dec(v___y_6732_);
lean_dec(v___y_6731_);
lean_dec(v___y_6730_);
lean_dec(v_A_6715_);
v_val_6740_ = lean_ctor_get(v_N_6717_, 0);
lean_inc(v_val_6740_);
lean_dec_ref_known(v_N_6717_, 1);
v___x_6741_ = l_Std_Time_PlainTime_ofNanoseconds(v_val_6740_);
lean_dec(v_val_6740_);
v___y_6682_ = v___y_6729_;
v___y_6683_ = v___y_6728_;
v___y_6684_ = v___y_6727_;
v___y_6685_ = v___y_6733_;
v___y_6686_ = v___x_6741_;
goto v___jp_6681_;
}
}
v___jp_6742_:
{
if (lean_obj_tag(v_n_6716_) == 0)
{
if (lean_obj_tag(v_S_6714_) == 0)
{
lean_object* v___x_6750_; 
v___x_6750_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4);
v___y_6727_ = v___y_6745_;
v___y_6728_ = v___y_6744_;
v___y_6729_ = v___y_6743_;
v___y_6730_ = v___y_6749_;
v___y_6731_ = v___y_6747_;
v___y_6732_ = v___y_6746_;
v___y_6733_ = v___y_6748_;
v___y_6734_ = v___x_6750_;
goto v___jp_6726_;
}
else
{
lean_object* v_val_6751_; 
v_val_6751_ = lean_ctor_get(v_S_6714_, 0);
lean_inc(v_val_6751_);
lean_dec_ref_known(v_S_6714_, 1);
v___y_6727_ = v___y_6745_;
v___y_6728_ = v___y_6744_;
v___y_6729_ = v___y_6743_;
v___y_6730_ = v___y_6749_;
v___y_6731_ = v___y_6747_;
v___y_6732_ = v___y_6746_;
v___y_6733_ = v___y_6748_;
v___y_6734_ = v_val_6751_;
goto v___jp_6726_;
}
}
else
{
lean_object* v_val_6752_; 
lean_dec(v_S_6714_);
v_val_6752_ = lean_ctor_get(v_n_6716_, 0);
lean_inc(v_val_6752_);
lean_dec_ref_known(v_n_6716_, 1);
v___y_6727_ = v___y_6745_;
v___y_6728_ = v___y_6744_;
v___y_6729_ = v___y_6743_;
v___y_6730_ = v___y_6749_;
v___y_6731_ = v___y_6747_;
v___y_6732_ = v___y_6746_;
v___y_6733_ = v___y_6748_;
v___y_6734_ = v_val_6752_;
goto v___jp_6726_;
}
}
v___jp_6753_:
{
if (lean_obj_tag(v_s_6713_) == 0)
{
lean_object* v___x_6760_; 
v___x_6760_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v___y_6743_ = v___y_6756_;
v___y_6744_ = v___y_6755_;
v___y_6745_ = v___y_6754_;
v___y_6746_ = v___y_6757_;
v___y_6747_ = v___y_6759_;
v___y_6748_ = v___y_6758_;
v___y_6749_ = v___x_6760_;
goto v___jp_6742_;
}
else
{
lean_object* v_val_6761_; 
v_val_6761_ = lean_ctor_get(v_s_6713_, 0);
lean_inc(v_val_6761_);
lean_dec_ref_known(v_s_6713_, 1);
v___y_6743_ = v___y_6756_;
v___y_6744_ = v___y_6755_;
v___y_6745_ = v___y_6754_;
v___y_6746_ = v___y_6757_;
v___y_6747_ = v___y_6759_;
v___y_6748_ = v___y_6758_;
v___y_6749_ = v_val_6761_;
goto v___jp_6742_;
}
}
v___jp_6762_:
{
if (lean_obj_tag(v_m_6712_) == 0)
{
lean_object* v___x_6768_; 
v___x_6768_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13);
v___y_6754_ = v___y_6765_;
v___y_6755_ = v___y_6764_;
v___y_6756_ = v___y_6763_;
v___y_6757_ = v___y_6767_;
v___y_6758_ = v___y_6766_;
v___y_6759_ = v___x_6768_;
goto v___jp_6753_;
}
else
{
lean_object* v_val_6769_; 
v_val_6769_ = lean_ctor_get(v_m_6712_, 0);
lean_inc(v_val_6769_);
lean_dec_ref_known(v_m_6712_, 1);
v___y_6754_ = v___y_6765_;
v___y_6755_ = v___y_6764_;
v___y_6756_ = v___y_6763_;
v___y_6757_ = v___y_6767_;
v___y_6758_ = v___y_6766_;
v___y_6759_ = v_val_6769_;
goto v___jp_6753_;
}
}
v___jp_6770_:
{
if (lean_obj_tag(v_k_6710_) == 0)
{
if (lean_obj_tag(v_H_6711_) == 0)
{
lean_object* v___x_6775_; 
v___x_6775_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6763_ = v___y_6773_;
v___y_6764_ = v___y_6772_;
v___y_6765_ = v___y_6771_;
v___y_6766_ = v___y_6774_;
v___y_6767_ = v___x_6775_;
goto v___jp_6762_;
}
else
{
lean_object* v_val_6776_; 
v_val_6776_ = lean_ctor_get(v_H_6711_, 0);
lean_inc(v_val_6776_);
lean_dec_ref_known(v_H_6711_, 1);
v___y_6763_ = v___y_6773_;
v___y_6764_ = v___y_6772_;
v___y_6765_ = v___y_6771_;
v___y_6766_ = v___y_6774_;
v___y_6767_ = v_val_6776_;
goto v___jp_6762_;
}
}
else
{
if (lean_obj_tag(v_H_6711_) == 0)
{
lean_object* v_val_6777_; lean_object* v___x_6778_; lean_object* v___x_6779_; 
v_val_6777_ = lean_ctor_get(v_k_6710_, 0);
lean_inc(v_val_6777_);
lean_dec_ref_known(v_k_6710_, 1);
v___x_6778_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_6779_ = lean_int_add(v_val_6777_, v___x_6778_);
lean_dec(v_val_6777_);
v___y_6763_ = v___y_6773_;
v___y_6764_ = v___y_6772_;
v___y_6765_ = v___y_6771_;
v___y_6766_ = v___y_6774_;
v___y_6767_ = v___x_6779_;
goto v___jp_6762_;
}
else
{
lean_object* v_val_6780_; 
lean_dec_ref_known(v_k_6710_, 1);
v_val_6780_ = lean_ctor_get(v_H_6711_, 0);
lean_inc(v_val_6780_);
lean_dec_ref_known(v_H_6711_, 1);
v___y_6763_ = v___y_6773_;
v___y_6764_ = v___y_6772_;
v___y_6765_ = v___y_6771_;
v___y_6766_ = v___y_6774_;
v___y_6767_ = v_val_6780_;
goto v___jp_6762_;
}
}
}
v___jp_6781_:
{
if (lean_obj_tag(v_h_6708_) == 0)
{
if (lean_obj_tag(v_K_6709_) == 0)
{
v___y_6771_ = v___y_6784_;
v___y_6772_ = v___y_6783_;
v___y_6773_ = v___y_6782_;
v___y_6774_ = v___y_6785_;
goto v___jp_6770_;
}
else
{
lean_object* v_val_6787_; lean_object* v___x_6788_; lean_object* v___x_6789_; lean_object* v___x_6790_; 
lean_dec(v_H_6711_);
lean_dec(v_k_6710_);
v_val_6787_ = lean_ctor_get(v_K_6709_, 0);
lean_inc(v_val_6787_);
lean_dec_ref_known(v_K_6709_, 1);
v___x_6788_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6789_ = lean_int_add(v_val_6787_, v___x_6788_);
lean_dec(v_val_6787_);
v___x_6790_ = l_Std_Time_HourMarker_toAbsolute(v_val_6786_, v___x_6789_);
lean_dec(v___x_6789_);
v___y_6763_ = v___y_6782_;
v___y_6764_ = v___y_6783_;
v___y_6765_ = v___y_6784_;
v___y_6766_ = v___y_6785_;
v___y_6767_ = v___x_6790_;
goto v___jp_6762_;
}
}
else
{
lean_object* v_val_6791_; lean_object* v___x_6792_; 
lean_dec(v_H_6711_);
lean_dec(v_k_6710_);
lean_dec(v_K_6709_);
v_val_6791_ = lean_ctor_get(v_h_6708_, 0);
lean_inc(v_val_6791_);
lean_dec_ref_known(v_h_6708_, 1);
v___x_6792_ = l_Std_Time_HourMarker_toAbsolute(v_val_6786_, v_val_6791_);
lean_dec(v_val_6791_);
v___y_6763_ = v___y_6782_;
v___y_6764_ = v___y_6783_;
v___y_6765_ = v___y_6784_;
v___y_6766_ = v___y_6785_;
v___y_6767_ = v___x_6792_;
goto v___jp_6762_;
}
}
v___jp_6793_:
{
if (lean_obj_tag(v_a_6705_) == 0)
{
if (lean_obj_tag(v_b_6706_) == 0)
{
if (lean_obj_tag(v_B_6707_) == 0)
{
lean_dec(v_K_6709_);
lean_dec(v_h_6708_);
v___y_6771_ = v___y_6797_;
v___y_6772_ = v___y_6794_;
v___y_6773_ = v___y_6795_;
v___y_6774_ = v___y_6796_;
goto v___jp_6770_;
}
else
{
lean_object* v_val_6798_; uint8_t v___x_6799_; uint8_t v___x_6800_; 
v_val_6798_ = lean_ctor_get(v_B_6707_, 0);
lean_inc(v_val_6798_);
lean_dec_ref_known(v_B_6707_, 1);
v___x_6799_ = lean_unbox(v_val_6798_);
lean_dec(v_val_6798_);
v___x_6800_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v___x_6799_);
v___y_6782_ = v___y_6795_;
v___y_6783_ = v___y_6794_;
v___y_6784_ = v___y_6797_;
v___y_6785_ = v___y_6796_;
v_val_6786_ = v___x_6800_;
goto v___jp_6781_;
}
}
else
{
lean_object* v_val_6801_; uint8_t v___x_6802_; uint8_t v___x_6803_; 
lean_dec(v_B_6707_);
v_val_6801_ = lean_ctor_get(v_b_6706_, 0);
lean_inc(v_val_6801_);
lean_dec_ref_known(v_b_6706_, 1);
v___x_6802_ = lean_unbox(v_val_6801_);
lean_dec(v_val_6801_);
v___x_6803_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v___x_6802_);
v___y_6782_ = v___y_6795_;
v___y_6783_ = v___y_6794_;
v___y_6784_ = v___y_6797_;
v___y_6785_ = v___y_6796_;
v_val_6786_ = v___x_6803_;
goto v___jp_6781_;
}
}
else
{
lean_object* v_val_6804_; uint8_t v___x_6805_; 
lean_dec(v_B_6707_);
lean_dec(v_b_6706_);
v_val_6804_ = lean_ctor_get(v_a_6705_, 0);
lean_inc(v_val_6804_);
lean_dec_ref_known(v_a_6705_, 1);
v___x_6805_ = lean_unbox(v_val_6804_);
lean_dec(v_val_6804_);
v___y_6782_ = v___y_6795_;
v___y_6783_ = v___y_6794_;
v___y_6784_ = v___y_6797_;
v___y_6785_ = v___y_6796_;
v_val_6786_ = v___x_6805_;
goto v___jp_6781_;
}
}
v___jp_6806_:
{
if (lean_obj_tag(v_u_6700_) == 0)
{
if (lean_obj_tag(v_y_6699_) == 0)
{
if (lean_obj_tag(v_Y_6701_) == 0)
{
lean_object* v___x_6811_; 
v___x_6811_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6794_ = v___y_6808_;
v___y_6795_ = v___y_6807_;
v___y_6796_ = v___y_6809_;
v___y_6797_ = v___x_6811_;
goto v___jp_6793_;
}
else
{
lean_object* v_val_6812_; 
v_val_6812_ = lean_ctor_get(v_Y_6701_, 0);
lean_inc(v_val_6812_);
lean_dec_ref_known(v_Y_6701_, 1);
v___y_6794_ = v___y_6808_;
v___y_6795_ = v___y_6807_;
v___y_6796_ = v___y_6809_;
v___y_6797_ = v_val_6812_;
goto v___jp_6793_;
}
}
else
{
lean_object* v_val_6813_; lean_object* v___x_6814_; 
lean_dec(v_Y_6701_);
v_val_6813_ = lean_ctor_get(v_y_6699_, 0);
lean_inc(v_val_6813_);
lean_dec_ref_known(v_y_6699_, 1);
v___x_6814_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6813_, v___y_6810_);
lean_dec(v_val_6813_);
v___y_6794_ = v___y_6808_;
v___y_6795_ = v___y_6807_;
v___y_6796_ = v___y_6809_;
v___y_6797_ = v___x_6814_;
goto v___jp_6793_;
}
}
else
{
lean_object* v_val_6815_; 
lean_dec(v_Y_6701_);
lean_dec(v_y_6699_);
v_val_6815_ = lean_ctor_get(v_u_6700_, 0);
lean_inc(v_val_6815_);
lean_dec_ref_known(v_u_6700_, 1);
v___y_6794_ = v___y_6808_;
v___y_6795_ = v___y_6807_;
v___y_6796_ = v___y_6809_;
v___y_6797_ = v_val_6815_;
goto v___jp_6793_;
}
}
v___jp_6816_:
{
if (lean_obj_tag(v_G_6698_) == 0)
{
uint8_t v___x_6820_; 
v___x_6820_ = 1;
v___y_6807_ = v___y_6819_;
v___y_6808_ = v___y_6817_;
v___y_6809_ = v___y_6818_;
v___y_6810_ = v___x_6820_;
goto v___jp_6806_;
}
else
{
lean_object* v_val_6821_; uint8_t v___x_6822_; 
v_val_6821_ = lean_ctor_get(v_G_6698_, 0);
lean_inc(v_val_6821_);
lean_dec_ref_known(v_G_6698_, 1);
v___x_6822_ = lean_unbox(v_val_6821_);
lean_dec(v_val_6821_);
v___y_6807_ = v___y_6819_;
v___y_6808_ = v___y_6817_;
v___y_6809_ = v___y_6818_;
v___y_6810_ = v___x_6822_;
goto v___jp_6806_;
}
}
v___jp_6823_:
{
if (lean_obj_tag(v_d_6704_) == 0)
{
lean_object* v___x_6826_; 
v___x_6826_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22);
v___y_6817_ = v___y_6824_;
v___y_6818_ = v___y_6825_;
v___y_6819_ = v___x_6826_;
goto v___jp_6816_;
}
else
{
lean_object* v_val_6827_; 
v_val_6827_ = lean_ctor_get(v_d_6704_, 0);
lean_inc(v_val_6827_);
lean_dec_ref_known(v_d_6704_, 1);
v___y_6817_ = v___y_6824_;
v___y_6818_ = v___y_6825_;
v___y_6819_ = v_val_6827_;
goto v___jp_6816_;
}
}
v___jp_6828_:
{
uint8_t v___x_6832_; lean_object* v_tz_6833_; 
v___x_6832_ = 0;
v_tz_6833_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tz_6833_, 0, v___y_6830_);
lean_ctor_set(v_tz_6833_, 1, v___y_6829_);
lean_ctor_set(v_tz_6833_, 2, v___y_6831_);
lean_ctor_set_uint8(v_tz_6833_, sizeof(void*)*3, v___x_6832_);
if (lean_obj_tag(v_M_6702_) == 0)
{
if (lean_obj_tag(v_L_6703_) == 0)
{
lean_object* v___x_6834_; 
v___x_6834_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30);
v___y_6824_ = v_tz_6833_;
v___y_6825_ = v___x_6834_;
goto v___jp_6823_;
}
else
{
lean_object* v_val_6835_; 
v_val_6835_ = lean_ctor_get(v_L_6703_, 0);
lean_inc(v_val_6835_);
lean_dec_ref_known(v_L_6703_, 1);
v___y_6824_ = v_tz_6833_;
v___y_6825_ = v_val_6835_;
goto v___jp_6823_;
}
}
else
{
lean_object* v_val_6836_; 
lean_dec(v_L_6703_);
v_val_6836_ = lean_ctor_get(v_M_6702_, 0);
lean_inc(v_val_6836_);
lean_dec_ref_known(v_M_6702_, 1);
v___y_6824_ = v_tz_6833_;
v___y_6825_ = v_val_6836_;
goto v___jp_6823_;
}
}
v___jp_6837_:
{
if (lean_obj_tag(v_zabbrev_6720_) == 0)
{
lean_object* v___x_6841_; lean_object* v___x_6842_; 
v___x_6841_ = lean_box(0);
v___x_6842_ = lean_apply_1(v___y_6838_, v___x_6841_);
v___y_6829_ = v___y_6840_;
v___y_6830_ = v___y_6839_;
v___y_6831_ = v___x_6842_;
goto v___jp_6828_;
}
else
{
lean_object* v_val_6843_; 
lean_dec_ref(v___y_6838_);
v_val_6843_ = lean_ctor_get(v_zabbrev_6720_, 0);
lean_inc(v_val_6843_);
lean_dec_ref_known(v_zabbrev_6720_, 1);
v___y_6829_ = v___y_6840_;
v___y_6830_ = v___y_6839_;
v___y_6831_ = v_val_6843_;
goto v___jp_6828_;
}
}
v___jp_6844_:
{
lean_object* v___f_6846_; 
lean_inc(v___y_6845_);
v___f_6846_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1), 2, 1);
lean_closure_set(v___f_6846_, 0, v___y_6845_);
if (lean_obj_tag(v_V_6718_) == 0)
{
if (lean_obj_tag(v_v_6721_) == 0)
{
if (lean_obj_tag(v_z_6719_) == 0)
{
lean_object* v___x_6847_; lean_object* v___x_6848_; 
v___x_6847_ = lean_box(0);
lean_inc(v___y_6845_);
v___x_6848_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(v___y_6845_, v___x_6847_);
v___y_6838_ = v___f_6846_;
v___y_6839_ = v___y_6845_;
v___y_6840_ = v___x_6848_;
goto v___jp_6837_;
}
else
{
lean_object* v_val_6849_; 
v_val_6849_ = lean_ctor_get(v_z_6719_, 0);
lean_inc(v_val_6849_);
lean_dec_ref_known(v_z_6719_, 1);
v___y_6838_ = v___f_6846_;
v___y_6839_ = v___y_6845_;
v___y_6840_ = v_val_6849_;
goto v___jp_6837_;
}
}
else
{
lean_object* v_val_6850_; 
lean_dec(v_z_6719_);
v_val_6850_ = lean_ctor_get(v_v_6721_, 0);
lean_inc(v_val_6850_);
lean_dec_ref_known(v_v_6721_, 1);
v___y_6838_ = v___f_6846_;
v___y_6839_ = v___y_6845_;
v___y_6840_ = v_val_6850_;
goto v___jp_6837_;
}
}
else
{
lean_object* v_val_6851_; 
lean_dec(v_v_6721_);
lean_dec(v_z_6719_);
v_val_6851_ = lean_ctor_get(v_V_6718_, 0);
lean_inc(v_val_6851_);
lean_dec_ref_known(v_V_6718_, 1);
v___y_6838_ = v___f_6846_;
v___y_6839_ = v___y_6845_;
v___y_6840_ = v_val_6851_;
goto v___jp_6837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object* v_date_6857_, lean_object* v_config_6858_, lean_object* v_mod_6859_, lean_object* v_a_6860_){
_start:
{
if (lean_obj_tag(v_mod_6859_) == 0)
{
lean_object* v_val_6861_; lean_object* v___x_6862_; 
lean_dec_ref(v_config_6858_);
v_val_6861_ = lean_ctor_get(v_mod_6859_, 0);
lean_inc_ref(v_val_6861_);
lean_dec_ref_known(v_mod_6859_, 1);
v___x_6862_ = l_Std_Internal_Parsec_String_pstring(v_val_6861_, v_a_6860_);
if (lean_obj_tag(v___x_6862_) == 0)
{
lean_object* v_pos_6863_; lean_object* v___x_6865_; uint8_t v_isShared_6866_; uint8_t v_isSharedCheck_6870_; 
v_pos_6863_ = lean_ctor_get(v___x_6862_, 0);
v_isSharedCheck_6870_ = !lean_is_exclusive(v___x_6862_);
if (v_isSharedCheck_6870_ == 0)
{
lean_object* v_unused_6871_; 
v_unused_6871_ = lean_ctor_get(v___x_6862_, 1);
lean_dec(v_unused_6871_);
v___x_6865_ = v___x_6862_;
v_isShared_6866_ = v_isSharedCheck_6870_;
goto v_resetjp_6864_;
}
else
{
lean_inc(v_pos_6863_);
lean_dec(v___x_6862_);
v___x_6865_ = lean_box(0);
v_isShared_6866_ = v_isSharedCheck_6870_;
goto v_resetjp_6864_;
}
v_resetjp_6864_:
{
lean_object* v___x_6868_; 
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 1, v_date_6857_);
v___x_6868_ = v___x_6865_;
goto v_reusejp_6867_;
}
else
{
lean_object* v_reuseFailAlloc_6869_; 
v_reuseFailAlloc_6869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6869_, 0, v_pos_6863_);
lean_ctor_set(v_reuseFailAlloc_6869_, 1, v_date_6857_);
v___x_6868_ = v_reuseFailAlloc_6869_;
goto v_reusejp_6867_;
}
v_reusejp_6867_:
{
return v___x_6868_;
}
}
}
else
{
lean_object* v_pos_6872_; lean_object* v_err_6873_; lean_object* v___x_6875_; uint8_t v_isShared_6876_; uint8_t v_isSharedCheck_6880_; 
lean_dec_ref(v_date_6857_);
v_pos_6872_ = lean_ctor_get(v___x_6862_, 0);
v_err_6873_ = lean_ctor_get(v___x_6862_, 1);
v_isSharedCheck_6880_ = !lean_is_exclusive(v___x_6862_);
if (v_isSharedCheck_6880_ == 0)
{
v___x_6875_ = v___x_6862_;
v_isShared_6876_ = v_isSharedCheck_6880_;
goto v_resetjp_6874_;
}
else
{
lean_inc(v_err_6873_);
lean_inc(v_pos_6872_);
lean_dec(v___x_6862_);
v___x_6875_ = lean_box(0);
v_isShared_6876_ = v_isSharedCheck_6880_;
goto v_resetjp_6874_;
}
v_resetjp_6874_:
{
lean_object* v___x_6878_; 
if (v_isShared_6876_ == 0)
{
v___x_6878_ = v___x_6875_;
goto v_reusejp_6877_;
}
else
{
lean_object* v_reuseFailAlloc_6879_; 
v_reuseFailAlloc_6879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6879_, 0, v_pos_6872_);
lean_ctor_set(v_reuseFailAlloc_6879_, 1, v_err_6873_);
v___x_6878_ = v_reuseFailAlloc_6879_;
goto v_reusejp_6877_;
}
v_reusejp_6877_:
{
return v___x_6878_;
}
}
}
}
else
{
lean_object* v_modifier_6881_; lean_object* v___x_6882_; 
v_modifier_6881_ = lean_ctor_get(v_mod_6859_, 0);
lean_inc_ref_n(v_modifier_6881_, 2);
lean_dec_ref_known(v_mod_6859_, 1);
v___x_6882_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6858_, v_modifier_6881_, v_a_6860_);
if (lean_obj_tag(v___x_6882_) == 0)
{
lean_object* v_pos_6883_; lean_object* v_res_6884_; lean_object* v___x_6886_; uint8_t v_isShared_6887_; uint8_t v_isSharedCheck_6892_; 
v_pos_6883_ = lean_ctor_get(v___x_6882_, 0);
v_res_6884_ = lean_ctor_get(v___x_6882_, 1);
v_isSharedCheck_6892_ = !lean_is_exclusive(v___x_6882_);
if (v_isSharedCheck_6892_ == 0)
{
v___x_6886_ = v___x_6882_;
v_isShared_6887_ = v_isSharedCheck_6892_;
goto v_resetjp_6885_;
}
else
{
lean_inc(v_res_6884_);
lean_inc(v_pos_6883_);
lean_dec(v___x_6882_);
v___x_6886_ = lean_box(0);
v_isShared_6887_ = v_isSharedCheck_6892_;
goto v_resetjp_6885_;
}
v_resetjp_6885_:
{
lean_object* v___x_6888_; lean_object* v___x_6890_; 
v___x_6888_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(v_date_6857_, v_modifier_6881_, v_res_6884_);
if (v_isShared_6887_ == 0)
{
lean_ctor_set(v___x_6886_, 1, v___x_6888_);
v___x_6890_ = v___x_6886_;
goto v_reusejp_6889_;
}
else
{
lean_object* v_reuseFailAlloc_6891_; 
v_reuseFailAlloc_6891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6891_, 0, v_pos_6883_);
lean_ctor_set(v_reuseFailAlloc_6891_, 1, v___x_6888_);
v___x_6890_ = v_reuseFailAlloc_6891_;
goto v_reusejp_6889_;
}
v_reusejp_6889_:
{
return v___x_6890_;
}
}
}
else
{
lean_object* v_pos_6893_; lean_object* v_err_6894_; lean_object* v___x_6896_; uint8_t v_isShared_6897_; uint8_t v_isSharedCheck_6901_; 
lean_dec_ref(v_modifier_6881_);
lean_dec_ref(v_date_6857_);
v_pos_6893_ = lean_ctor_get(v___x_6882_, 0);
v_err_6894_ = lean_ctor_get(v___x_6882_, 1);
v_isSharedCheck_6901_ = !lean_is_exclusive(v___x_6882_);
if (v_isSharedCheck_6901_ == 0)
{
v___x_6896_ = v___x_6882_;
v_isShared_6897_ = v_isSharedCheck_6901_;
goto v_resetjp_6895_;
}
else
{
lean_inc(v_err_6894_);
lean_inc(v_pos_6893_);
lean_dec(v___x_6882_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object* v_input_6902_, lean_object* v_config_6903_){
_start:
{
lean_object* v___x_6904_; lean_object* v___x_6905_; 
v___x_6904_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6905_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6904_, v_input_6902_);
if (lean_obj_tag(v___x_6905_) == 0)
{
lean_object* v_a_6906_; lean_object* v___x_6908_; uint8_t v_isShared_6909_; uint8_t v_isSharedCheck_6913_; 
lean_dec_ref(v_config_6903_);
v_a_6906_ = lean_ctor_get(v___x_6905_, 0);
v_isSharedCheck_6913_ = !lean_is_exclusive(v___x_6905_);
if (v_isSharedCheck_6913_ == 0)
{
v___x_6908_ = v___x_6905_;
v_isShared_6909_ = v_isSharedCheck_6913_;
goto v_resetjp_6907_;
}
else
{
lean_inc(v_a_6906_);
lean_dec(v___x_6905_);
v___x_6908_ = lean_box(0);
v_isShared_6909_ = v_isSharedCheck_6913_;
goto v_resetjp_6907_;
}
v_resetjp_6907_:
{
lean_object* v___x_6911_; 
if (v_isShared_6909_ == 0)
{
v___x_6911_ = v___x_6908_;
goto v_reusejp_6910_;
}
else
{
lean_object* v_reuseFailAlloc_6912_; 
v_reuseFailAlloc_6912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6912_, 0, v_a_6906_);
v___x_6911_ = v_reuseFailAlloc_6912_;
goto v_reusejp_6910_;
}
v_reusejp_6910_:
{
return v___x_6911_;
}
}
}
else
{
lean_object* v_a_6914_; lean_object* v___x_6916_; uint8_t v_isShared_6917_; uint8_t v_isSharedCheck_6922_; 
v_a_6914_ = lean_ctor_get(v___x_6905_, 0);
v_isSharedCheck_6922_ = !lean_is_exclusive(v___x_6905_);
if (v_isSharedCheck_6922_ == 0)
{
v___x_6916_ = v___x_6905_;
v_isShared_6917_ = v_isSharedCheck_6922_;
goto v_resetjp_6915_;
}
else
{
lean_inc(v_a_6914_);
lean_dec(v___x_6905_);
v___x_6916_ = lean_box(0);
v_isShared_6917_ = v_isSharedCheck_6922_;
goto v_resetjp_6915_;
}
v_resetjp_6915_:
{
lean_object* v___x_6918_; lean_object* v___x_6920_; 
v___x_6918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6918_, 0, v_config_6903_);
lean_ctor_set(v___x_6918_, 1, v_a_6914_);
if (v_isShared_6917_ == 0)
{
lean_ctor_set(v___x_6916_, 0, v___x_6918_);
v___x_6920_ = v___x_6916_;
goto v_reusejp_6919_;
}
else
{
lean_object* v_reuseFailAlloc_6921_; 
v_reuseFailAlloc_6921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6921_, 0, v___x_6918_);
v___x_6920_ = v_reuseFailAlloc_6921_;
goto v_reusejp_6919_;
}
v_reusejp_6919_:
{
return v___x_6920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object* v_tz_6923_, lean_object* v_input_6924_, lean_object* v_config_6925_){
_start:
{
lean_object* v___x_6926_; 
v___x_6926_ = l_Std_Time_GenericFormat_spec___redArg(v_input_6924_, v_config_6925_);
return v___x_6926_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object* v_tz_6927_, lean_object* v_input_6928_, lean_object* v_config_6929_){
_start:
{
lean_object* v_res_6930_; 
v_res_6930_ = l_Std_Time_GenericFormat_spec(v_tz_6927_, v_input_6928_, v_config_6929_);
lean_dec(v_tz_6927_);
return v_res_6930_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(lean_object* v_msg_6931_){
_start:
{
lean_object* v___x_6932_; lean_object* v___x_6933_; 
v___x_6932_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
v___x_6933_ = lean_panic_fn_borrowed(v___x_6932_, v_msg_6931_);
return v___x_6933_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object* v_tz_6934_, lean_object* v_msg_6935_){
_start:
{
lean_object* v___x_6936_; 
v___x_6936_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v_msg_6935_);
return v___x_6936_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object* v_tz_6937_, lean_object* v_msg_6938_){
_start:
{
lean_object* v_res_6939_; 
v_res_6939_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6937_, v_msg_6938_);
lean_dec(v_tz_6937_);
return v_res_6939_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object* v_tz_6942_, lean_object* v_input_6943_, lean_object* v_config_6944_){
_start:
{
lean_object* v___x_6945_; lean_object* v___x_6946_; 
v___x_6945_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6946_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6945_, v_input_6943_);
if (lean_obj_tag(v___x_6946_) == 0)
{
lean_object* v_a_6947_; lean_object* v___x_6948_; lean_object* v___x_6949_; lean_object* v___x_6950_; lean_object* v___x_6951_; lean_object* v___x_6952_; lean_object* v___x_6953_; 
lean_dec_ref(v_config_6944_);
v_a_6947_ = lean_ctor_get(v___x_6946_, 0);
lean_inc(v_a_6947_);
lean_dec_ref_known(v___x_6946_, 1);
v___x_6948_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6949_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__1));
v___x_6950_ = lean_unsigned_to_nat(1071u);
v___x_6951_ = lean_unsigned_to_nat(18u);
v___x_6952_ = l_mkPanicMessageWithDecl(v___x_6948_, v___x_6949_, v___x_6950_, v___x_6951_, v_a_6947_);
lean_dec(v_a_6947_);
v___x_6953_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v___x_6952_);
return v___x_6953_;
}
else
{
lean_object* v_a_6954_; lean_object* v___x_6955_; 
v_a_6954_ = lean_ctor_get(v___x_6946_, 0);
lean_inc(v_a_6954_);
lean_dec_ref_known(v___x_6946_, 1);
v___x_6955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6955_, 0, v_config_6944_);
lean_ctor_set(v___x_6955_, 1, v_a_6954_);
return v___x_6955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object* v_tz_6956_, lean_object* v_input_6957_, lean_object* v_config_6958_){
_start:
{
lean_object* v_res_6959_; 
v_res_6959_ = l_Std_Time_GenericFormat_spec_x21(v_tz_6956_, v_input_6957_, v_config_6958_);
lean_dec(v_tz_6956_);
return v_res_6959_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(lean_object* v_x_6960_, lean_object* v_x_6961_){
_start:
{
if (lean_obj_tag(v_x_6961_) == 0)
{
return v_x_6960_;
}
else
{
lean_object* v_head_6962_; lean_object* v_tail_6963_; lean_object* v___x_6964_; 
v_head_6962_ = lean_ctor_get(v_x_6961_, 0);
v_tail_6963_ = lean_ctor_get(v_x_6961_, 1);
v___x_6964_ = lean_string_append(v_x_6960_, v_head_6962_);
v_x_6960_ = v___x_6964_;
v_x_6961_ = v_tail_6963_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1___boxed(lean_object* v_x_6966_, lean_object* v_x_6967_){
_start:
{
lean_object* v_res_6968_; 
v_res_6968_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v_x_6966_, v_x_6967_);
lean_dec(v_x_6967_);
return v_res_6968_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(lean_object* v_tz_6969_, lean_object* v_timestamp_6970_, lean_object* v___x_6971_, lean_object* v_x_6972_){
_start:
{
lean_object* v_offset_6973_; lean_object* v_second_6974_; lean_object* v_nano_6975_; lean_object* v___x_6976_; lean_object* v___x_6977_; lean_object* v___x_6978_; lean_object* v___x_6979_; lean_object* v___x_6980_; lean_object* v___x_6981_; lean_object* v___x_6982_; lean_object* v___x_6983_; lean_object* v___x_6984_; 
v_offset_6973_ = lean_ctor_get(v_tz_6969_, 0);
v_second_6974_ = lean_ctor_get(v_timestamp_6970_, 0);
v_nano_6975_ = lean_ctor_get(v_timestamp_6970_, 1);
v___x_6976_ = lean_nat_to_int(v___x_6971_);
v___x_6977_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6978_ = lean_int_mul(v_second_6974_, v___x_6977_);
v___x_6979_ = lean_int_add(v___x_6978_, v_nano_6975_);
lean_dec(v___x_6978_);
v___x_6980_ = lean_int_mul(v_offset_6973_, v___x_6977_);
v___x_6981_ = lean_int_add(v___x_6980_, v___x_6976_);
lean_dec(v___x_6976_);
lean_dec(v___x_6980_);
v___x_6982_ = lean_int_add(v___x_6979_, v___x_6981_);
lean_dec(v___x_6981_);
lean_dec(v___x_6979_);
v___x_6983_ = l_Std_Time_Duration_ofNanoseconds(v___x_6982_);
lean_dec(v___x_6982_);
v___x_6984_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_6983_);
return v___x_6984_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed(lean_object* v_tz_6985_, lean_object* v_timestamp_6986_, lean_object* v___x_6987_, lean_object* v_x_6988_){
_start:
{
lean_object* v_res_6989_; 
v_res_6989_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(v_tz_6985_, v_timestamp_6986_, v___x_6987_, v_x_6988_);
lean_dec_ref(v_timestamp_6986_);
lean_dec_ref(v_tz_6985_);
return v_res_6989_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(lean_object* v_aw_6990_, lean_object* v_date_6991_, lean_object* v_dateformat_6992_, lean_object* v_a_6993_, lean_object* v_a_6994_){
_start:
{
if (lean_obj_tag(v_a_6993_) == 0)
{
lean_object* v___x_6995_; 
lean_dec_ref(v_date_6991_);
v___x_6995_ = l_List_reverse___redArg(v_a_6994_);
return v___x_6995_;
}
else
{
lean_object* v_head_6996_; lean_object* v_tail_6997_; lean_object* v___x_6999_; uint8_t v_isShared_7000_; uint8_t v_isSharedCheck_7026_; 
v_head_6996_ = lean_ctor_get(v_a_6993_, 0);
v_tail_6997_ = lean_ctor_get(v_a_6993_, 1);
v_isSharedCheck_7026_ = !lean_is_exclusive(v_a_6993_);
if (v_isSharedCheck_7026_ == 0)
{
v___x_6999_ = v_a_6993_;
v_isShared_7000_ = v_isSharedCheck_7026_;
goto v_resetjp_6998_;
}
else
{
lean_inc(v_tail_6997_);
lean_inc(v_head_6996_);
lean_dec(v_a_6993_);
v___x_6999_ = lean_box(0);
v_isShared_7000_ = v_isSharedCheck_7026_;
goto v_resetjp_6998_;
}
v_resetjp_6998_:
{
lean_object* v___y_7002_; 
if (lean_obj_tag(v_aw_6990_) == 0)
{
lean_object* v_a_7007_; lean_object* v_offset_7008_; lean_object* v_name_7009_; lean_object* v_abbreviation_7010_; uint8_t v_isDST_7011_; lean_object* v_timestamp_7012_; uint8_t v___x_7013_; uint8_t v___x_7014_; lean_object* v_ltt_7015_; lean_object* v___x_7016_; lean_object* v___x_7017_; lean_object* v___x_7018_; lean_object* v___x_7019_; lean_object* v_tz_7020_; lean_object* v___f_7021_; lean_object* v___x_7022_; lean_object* v___x_7023_; lean_object* v___x_7024_; 
v_a_7007_ = lean_ctor_get(v_aw_6990_, 0);
v_offset_7008_ = lean_ctor_get(v_a_7007_, 0);
v_name_7009_ = lean_ctor_get(v_a_7007_, 1);
v_abbreviation_7010_ = lean_ctor_get(v_a_7007_, 2);
v_isDST_7011_ = lean_ctor_get_uint8(v_a_7007_, sizeof(void*)*3);
v_timestamp_7012_ = lean_ctor_get(v_date_6991_, 1);
v___x_7013_ = 0;
v___x_7014_ = 1;
lean_inc_ref(v_name_7009_);
lean_inc_ref(v_abbreviation_7010_);
lean_inc(v_offset_7008_);
v_ltt_7015_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_7015_, 0, v_offset_7008_);
lean_ctor_set(v_ltt_7015_, 1, v_abbreviation_7010_);
lean_ctor_set(v_ltt_7015_, 2, v_name_7009_);
lean_ctor_set_uint8(v_ltt_7015_, sizeof(void*)*3, v_isDST_7011_);
lean_ctor_set_uint8(v_ltt_7015_, sizeof(void*)*3 + 1, v___x_7013_);
lean_ctor_set_uint8(v_ltt_7015_, sizeof(void*)*3 + 2, v___x_7014_);
v___x_7016_ = lean_unsigned_to_nat(0u);
v___x_7017_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_7018_ = lean_box(0);
v___x_7019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_7019_, 0, v_ltt_7015_);
lean_ctor_set(v___x_7019_, 1, v___x_7017_);
lean_ctor_set(v___x_7019_, 2, v___x_7018_);
lean_inc_ref(v___x_7019_);
v_tz_7020_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_7019_, v_timestamp_7012_);
lean_inc_ref_n(v_timestamp_7012_, 2);
lean_inc_ref(v_tz_7020_);
v___f_7021_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_7021_, 0, v_tz_7020_);
lean_closure_set(v___f_7021_, 1, v_timestamp_7012_);
lean_closure_set(v___f_7021_, 2, v___x_7016_);
v___x_7022_ = lean_mk_thunk(v___f_7021_);
v___x_7023_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_7023_, 0, v___x_7022_);
lean_ctor_set(v___x_7023_, 1, v_timestamp_7012_);
lean_ctor_set(v___x_7023_, 2, v___x_7019_);
lean_ctor_set(v___x_7023_, 3, v_tz_7020_);
v___x_7024_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6992_, v___x_7023_, v_head_6996_);
v___y_7002_ = v___x_7024_;
goto v___jp_7001_;
}
else
{
lean_object* v___x_7025_; 
lean_inc_ref(v_date_6991_);
v___x_7025_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6992_, v_date_6991_, v_head_6996_);
v___y_7002_ = v___x_7025_;
goto v___jp_7001_;
}
v___jp_7001_:
{
lean_object* v___x_7004_; 
if (v_isShared_7000_ == 0)
{
lean_ctor_set(v___x_6999_, 1, v_a_6994_);
lean_ctor_set(v___x_6999_, 0, v___y_7002_);
v___x_7004_ = v___x_6999_;
goto v_reusejp_7003_;
}
else
{
lean_object* v_reuseFailAlloc_7006_; 
v_reuseFailAlloc_7006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7006_, 0, v___y_7002_);
lean_ctor_set(v_reuseFailAlloc_7006_, 1, v_a_6994_);
v___x_7004_ = v_reuseFailAlloc_7006_;
goto v_reusejp_7003_;
}
v_reusejp_7003_:
{
v_a_6993_ = v_tail_6997_;
v_a_6994_ = v___x_7004_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___boxed(lean_object* v_aw_7027_, lean_object* v_date_7028_, lean_object* v_dateformat_7029_, lean_object* v_a_7030_, lean_object* v_a_7031_){
_start:
{
lean_object* v_res_7032_; 
v_res_7032_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_7027_, v_date_7028_, v_dateformat_7029_, v_a_7030_, v_a_7031_);
lean_dec_ref(v_dateformat_7029_);
lean_dec(v_aw_7027_);
return v_res_7032_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object* v_aw_7033_, lean_object* v_format_7034_, lean_object* v_date_7035_){
_start:
{
lean_object* v_config_7036_; lean_object* v_string_7037_; lean_object* v_dateformat_7038_; lean_object* v___x_7039_; lean_object* v___x_7040_; lean_object* v___x_7041_; lean_object* v___x_7042_; 
v_config_7036_ = lean_ctor_get(v_format_7034_, 0);
lean_inc_ref(v_config_7036_);
v_string_7037_ = lean_ctor_get(v_format_7034_, 1);
lean_inc(v_string_7037_);
lean_dec_ref(v_format_7034_);
v_dateformat_7038_ = lean_ctor_get(v_config_7036_, 0);
lean_inc_ref(v_dateformat_7038_);
lean_dec_ref(v_config_7036_);
v___x_7039_ = lean_box(0);
v___x_7040_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_7033_, v_date_7035_, v_dateformat_7038_, v_string_7037_, v___x_7039_);
lean_dec_ref(v_dateformat_7038_);
v___x_7041_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_7042_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v___x_7041_, v___x_7040_);
lean_dec(v___x_7040_);
return v___x_7042_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object* v_aw_7043_, lean_object* v_format_7044_, lean_object* v_date_7045_){
_start:
{
lean_object* v_res_7046_; 
v_res_7046_ = l_Std_Time_GenericFormat_format(v_aw_7043_, v_format_7044_, v_date_7045_);
lean_dec(v_aw_7043_);
return v_res_7046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object* v_config_7050_, lean_object* v_aw_7051_, lean_object* v_builder_7052_, lean_object* v_x_7053_, lean_object* v_a_7054_){
_start:
{
if (lean_obj_tag(v_x_7053_) == 0)
{
lean_object* v___x_7055_; 
lean_dec_ref(v_config_7050_);
v___x_7055_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_7052_, v_aw_7051_);
if (lean_obj_tag(v___x_7055_) == 0)
{
lean_object* v___x_7056_; lean_object* v___x_7057_; 
v___x_7056_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1));
v___x_7057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7057_, 0, v_a_7054_);
lean_ctor_set(v___x_7057_, 1, v___x_7056_);
return v___x_7057_;
}
else
{
lean_object* v_val_7058_; lean_object* v___x_7059_; 
v_val_7058_ = lean_ctor_get(v___x_7055_, 0);
lean_inc(v_val_7058_);
lean_dec_ref_known(v___x_7055_, 1);
v___x_7059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7059_, 0, v_a_7054_);
lean_ctor_set(v___x_7059_, 1, v_val_7058_);
return v___x_7059_;
}
}
else
{
lean_object* v_head_7060_; lean_object* v_tail_7061_; lean_object* v___x_7062_; 
v_head_7060_ = lean_ctor_get(v_x_7053_, 0);
lean_inc(v_head_7060_);
v_tail_7061_ = lean_ctor_get(v_x_7053_, 1);
lean_inc(v_tail_7061_);
lean_dec_ref_known(v_x_7053_, 2);
lean_inc_ref(v_config_7050_);
v___x_7062_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(v_builder_7052_, v_config_7050_, v_head_7060_, v_a_7054_);
if (lean_obj_tag(v___x_7062_) == 0)
{
lean_object* v_pos_7063_; lean_object* v_res_7064_; 
v_pos_7063_ = lean_ctor_get(v___x_7062_, 0);
lean_inc(v_pos_7063_);
v_res_7064_ = lean_ctor_get(v___x_7062_, 1);
lean_inc(v_res_7064_);
lean_dec_ref_known(v___x_7062_, 2);
v_builder_7052_ = v_res_7064_;
v_x_7053_ = v_tail_7061_;
v_a_7054_ = v_pos_7063_;
goto _start;
}
else
{
lean_object* v_pos_7066_; lean_object* v_err_7067_; lean_object* v___x_7069_; uint8_t v_isShared_7070_; uint8_t v_isSharedCheck_7074_; 
lean_dec(v_tail_7061_);
lean_dec(v_aw_7051_);
lean_dec_ref(v_config_7050_);
v_pos_7066_ = lean_ctor_get(v___x_7062_, 0);
v_err_7067_ = lean_ctor_get(v___x_7062_, 1);
v_isSharedCheck_7074_ = !lean_is_exclusive(v___x_7062_);
if (v_isSharedCheck_7074_ == 0)
{
v___x_7069_ = v___x_7062_;
v_isShared_7070_ = v_isSharedCheck_7074_;
goto v_resetjp_7068_;
}
else
{
lean_inc(v_err_7067_);
lean_inc(v_pos_7066_);
lean_dec(v___x_7062_);
v___x_7069_ = lean_box(0);
v_isShared_7070_ = v_isSharedCheck_7074_;
goto v_resetjp_7068_;
}
v_resetjp_7068_:
{
lean_object* v___x_7072_; 
if (v_isShared_7070_ == 0)
{
v___x_7072_ = v___x_7069_;
goto v_reusejp_7071_;
}
else
{
lean_object* v_reuseFailAlloc_7073_; 
v_reuseFailAlloc_7073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7073_, 0, v_pos_7066_);
lean_ctor_set(v_reuseFailAlloc_7073_, 1, v_err_7067_);
v___x_7072_ = v_reuseFailAlloc_7073_;
goto v_reusejp_7071_;
}
v_reusejp_7071_:
{
return v___x_7072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object* v_format_7077_, lean_object* v_config_7078_, lean_object* v_aw_7079_, lean_object* v_a_7080_){
_start:
{
lean_object* v___x_7081_; lean_object* v___x_7082_; 
v___x_7081_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0));
v___x_7082_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(v_config_7078_, v_aw_7079_, v___x_7081_, v_format_7077_, v_a_7080_);
return v___x_7082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object* v_config_7086_, lean_object* v_format_7087_, lean_object* v_func_7088_, lean_object* v_a_7089_){
_start:
{
if (lean_obj_tag(v_format_7087_) == 0)
{
lean_dec_ref(v_config_7086_);
if (lean_obj_tag(v_func_7088_) == 0)
{
lean_object* v___x_7090_; lean_object* v___x_7091_; 
v___x_7090_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1));
v___x_7091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7091_, 0, v_a_7089_);
lean_ctor_set(v___x_7091_, 1, v___x_7090_);
return v___x_7091_;
}
else
{
lean_object* v_val_7092_; lean_object* v_fst_7093_; lean_object* v_snd_7094_; lean_object* v___x_7095_; uint8_t v_decide_7096_; 
v_val_7092_ = lean_ctor_get(v_func_7088_, 0);
lean_inc(v_val_7092_);
lean_dec_ref_known(v_func_7088_, 1);
v_fst_7093_ = lean_ctor_get(v_a_7089_, 0);
v_snd_7094_ = lean_ctor_get(v_a_7089_, 1);
v___x_7095_ = lean_string_utf8_byte_size(v_fst_7093_);
v_decide_7096_ = lean_nat_dec_eq(v_snd_7094_, v___x_7095_);
if (v_decide_7096_ == 0)
{
lean_object* v___x_7097_; lean_object* v___x_7098_; 
lean_dec(v_val_7092_);
v___x_7097_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
v___x_7098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7098_, 0, v_a_7089_);
lean_ctor_set(v___x_7098_, 1, v___x_7097_);
return v___x_7098_;
}
else
{
lean_object* v___x_7099_; 
v___x_7099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7099_, 0, v_a_7089_);
lean_ctor_set(v___x_7099_, 1, v_val_7092_);
return v___x_7099_;
}
}
}
else
{
lean_object* v_head_7100_; 
v_head_7100_ = lean_ctor_get(v_format_7087_, 0);
lean_inc(v_head_7100_);
if (lean_obj_tag(v_head_7100_) == 0)
{
lean_object* v_tail_7101_; lean_object* v_val_7102_; lean_object* v___x_7103_; 
v_tail_7101_ = lean_ctor_get(v_format_7087_, 1);
lean_inc(v_tail_7101_);
lean_dec_ref_known(v_format_7087_, 2);
v_val_7102_ = lean_ctor_get(v_head_7100_, 0);
lean_inc_ref(v_val_7102_);
lean_dec_ref_known(v_head_7100_, 1);
v___x_7103_ = l_Std_Internal_Parsec_String_pstring(v_val_7102_, v_a_7089_);
if (lean_obj_tag(v___x_7103_) == 0)
{
lean_object* v_pos_7104_; 
v_pos_7104_ = lean_ctor_get(v___x_7103_, 0);
lean_inc(v_pos_7104_);
lean_dec_ref_known(v___x_7103_, 2);
v_format_7087_ = v_tail_7101_;
v_a_7089_ = v_pos_7104_;
goto _start;
}
else
{
lean_object* v_pos_7106_; lean_object* v_err_7107_; lean_object* v___x_7109_; uint8_t v_isShared_7110_; uint8_t v_isSharedCheck_7114_; 
lean_dec(v_tail_7101_);
lean_dec(v_func_7088_);
lean_dec_ref(v_config_7086_);
v_pos_7106_ = lean_ctor_get(v___x_7103_, 0);
v_err_7107_ = lean_ctor_get(v___x_7103_, 1);
v_isSharedCheck_7114_ = !lean_is_exclusive(v___x_7103_);
if (v_isSharedCheck_7114_ == 0)
{
v___x_7109_ = v___x_7103_;
v_isShared_7110_ = v_isSharedCheck_7114_;
goto v_resetjp_7108_;
}
else
{
lean_inc(v_err_7107_);
lean_inc(v_pos_7106_);
lean_dec(v___x_7103_);
v___x_7109_ = lean_box(0);
v_isShared_7110_ = v_isSharedCheck_7114_;
goto v_resetjp_7108_;
}
v_resetjp_7108_:
{
lean_object* v___x_7112_; 
if (v_isShared_7110_ == 0)
{
v___x_7112_ = v___x_7109_;
goto v_reusejp_7111_;
}
else
{
lean_object* v_reuseFailAlloc_7113_; 
v_reuseFailAlloc_7113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7113_, 0, v_pos_7106_);
lean_ctor_set(v_reuseFailAlloc_7113_, 1, v_err_7107_);
v___x_7112_ = v_reuseFailAlloc_7113_;
goto v_reusejp_7111_;
}
v_reusejp_7111_:
{
return v___x_7112_;
}
}
}
}
else
{
lean_object* v_tail_7115_; lean_object* v_modifier_7116_; lean_object* v___x_7117_; 
v_tail_7115_ = lean_ctor_get(v_format_7087_, 1);
lean_inc(v_tail_7115_);
lean_dec_ref_known(v_format_7087_, 2);
v_modifier_7116_ = lean_ctor_get(v_head_7100_, 0);
lean_inc_ref(v_modifier_7116_);
lean_dec_ref_known(v_head_7100_, 1);
lean_inc_ref(v_config_7086_);
v___x_7117_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_7086_, v_modifier_7116_, v_a_7089_);
if (lean_obj_tag(v___x_7117_) == 0)
{
lean_object* v_pos_7118_; lean_object* v_res_7119_; lean_object* v___x_7120_; 
v_pos_7118_ = lean_ctor_get(v___x_7117_, 0);
lean_inc(v_pos_7118_);
v_res_7119_ = lean_ctor_get(v___x_7117_, 1);
lean_inc(v_res_7119_);
lean_dec_ref_known(v___x_7117_, 2);
v___x_7120_ = lean_apply_1(v_func_7088_, v_res_7119_);
v_format_7087_ = v_tail_7115_;
v_func_7088_ = v___x_7120_;
v_a_7089_ = v_pos_7118_;
goto _start;
}
else
{
lean_object* v_pos_7122_; lean_object* v_err_7123_; lean_object* v___x_7125_; uint8_t v_isShared_7126_; uint8_t v_isSharedCheck_7130_; 
lean_dec(v_tail_7115_);
lean_dec(v_func_7088_);
lean_dec_ref(v_config_7086_);
v_pos_7122_ = lean_ctor_get(v___x_7117_, 0);
v_err_7123_ = lean_ctor_get(v___x_7117_, 1);
v_isSharedCheck_7130_ = !lean_is_exclusive(v___x_7117_);
if (v_isSharedCheck_7130_ == 0)
{
v___x_7125_ = v___x_7117_;
v_isShared_7126_ = v_isSharedCheck_7130_;
goto v_resetjp_7124_;
}
else
{
lean_inc(v_err_7123_);
lean_inc(v_pos_7122_);
lean_dec(v___x_7117_);
v___x_7125_ = lean_box(0);
v_isShared_7126_ = v_isSharedCheck_7130_;
goto v_resetjp_7124_;
}
v_resetjp_7124_:
{
lean_object* v___x_7128_; 
if (v_isShared_7126_ == 0)
{
v___x_7128_ = v___x_7125_;
goto v_reusejp_7127_;
}
else
{
lean_object* v_reuseFailAlloc_7129_; 
v_reuseFailAlloc_7129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7129_, 0, v_pos_7122_);
lean_ctor_set(v_reuseFailAlloc_7129_, 1, v_err_7123_);
v___x_7128_ = v_reuseFailAlloc_7129_;
goto v_reusejp_7127_;
}
v_reusejp_7127_:
{
return v___x_7128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object* v_00_u03b1_7131_, lean_object* v_config_7132_, lean_object* v_format_7133_, lean_object* v_func_7134_, lean_object* v_a_7135_){
_start:
{
lean_object* v___x_7136_; 
v___x_7136_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7132_, v_format_7133_, v_func_7134_, v_a_7135_);
return v___x_7136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object* v_format_7137_, lean_object* v_config_7138_, lean_object* v_func_7139_, lean_object* v_a_7140_){
_start:
{
lean_object* v___x_7141_; 
v___x_7141_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7138_, v_format_7137_, v_func_7139_, v_a_7140_);
return v___x_7141_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object* v_00_u03b1_7142_, lean_object* v_format_7143_, lean_object* v_config_7144_, lean_object* v_func_7145_, lean_object* v_a_7146_){
_start:
{
lean_object* v___x_7147_; 
v___x_7147_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7144_, v_format_7143_, v_func_7145_, v_a_7146_);
return v___x_7147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object* v_string_7148_, lean_object* v_config_7149_, lean_object* v_aw_7150_, lean_object* v___y_7151_){
_start:
{
lean_object* v___x_7152_; 
v___x_7152_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(v_string_7148_, v_config_7149_, v_aw_7150_, v___y_7151_);
if (lean_obj_tag(v___x_7152_) == 0)
{
lean_object* v_pos_7153_; lean_object* v_fst_7154_; lean_object* v_snd_7155_; lean_object* v___x_7156_; uint8_t v_decide_7157_; 
v_pos_7153_ = lean_ctor_get(v___x_7152_, 0);
lean_inc(v_pos_7153_);
v_fst_7154_ = lean_ctor_get(v_pos_7153_, 0);
v_snd_7155_ = lean_ctor_get(v_pos_7153_, 1);
v___x_7156_ = lean_string_utf8_byte_size(v_fst_7154_);
v_decide_7157_ = lean_nat_dec_eq(v_snd_7155_, v___x_7156_);
if (v_decide_7157_ == 0)
{
lean_object* v___x_7159_; uint8_t v_isShared_7160_; uint8_t v_isSharedCheck_7165_; 
v_isSharedCheck_7165_ = !lean_is_exclusive(v___x_7152_);
if (v_isSharedCheck_7165_ == 0)
{
lean_object* v_unused_7166_; lean_object* v_unused_7167_; 
v_unused_7166_ = lean_ctor_get(v___x_7152_, 1);
lean_dec(v_unused_7166_);
v_unused_7167_ = lean_ctor_get(v___x_7152_, 0);
lean_dec(v_unused_7167_);
v___x_7159_ = v___x_7152_;
v_isShared_7160_ = v_isSharedCheck_7165_;
goto v_resetjp_7158_;
}
else
{
lean_dec(v___x_7152_);
v___x_7159_ = lean_box(0);
v_isShared_7160_ = v_isSharedCheck_7165_;
goto v_resetjp_7158_;
}
v_resetjp_7158_:
{
lean_object* v___x_7161_; lean_object* v___x_7163_; 
v___x_7161_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_7160_ == 0)
{
lean_ctor_set_tag(v___x_7159_, 1);
lean_ctor_set(v___x_7159_, 1, v___x_7161_);
v___x_7163_ = v___x_7159_;
goto v_reusejp_7162_;
}
else
{
lean_object* v_reuseFailAlloc_7164_; 
v_reuseFailAlloc_7164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7164_, 0, v_pos_7153_);
lean_ctor_set(v_reuseFailAlloc_7164_, 1, v___x_7161_);
v___x_7163_ = v_reuseFailAlloc_7164_;
goto v_reusejp_7162_;
}
v_reusejp_7162_:
{
return v___x_7163_;
}
}
}
else
{
lean_dec(v_pos_7153_);
return v___x_7152_;
}
}
else
{
return v___x_7152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object* v_aw_7168_, lean_object* v_format_7169_, lean_object* v_input_7170_){
_start:
{
lean_object* v_config_7171_; lean_object* v_string_7172_; lean_object* v___f_7173_; lean_object* v___x_7174_; 
v_config_7171_ = lean_ctor_get(v_format_7169_, 0);
lean_inc_ref(v_config_7171_);
v_string_7172_ = lean_ctor_get(v_format_7169_, 1);
lean_inc(v_string_7172_);
lean_dec_ref(v_format_7169_);
v___f_7173_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parse___lam__0), 4, 3);
lean_closure_set(v___f_7173_, 0, v_string_7172_);
lean_closure_set(v___f_7173_, 1, v_config_7171_);
lean_closure_set(v___f_7173_, 2, v_aw_7168_);
v___x_7174_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7173_, v_input_7170_);
return v___x_7174_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object* v_msg_7175_){
_start:
{
lean_object* v___x_7176_; lean_object* v___x_7177_; 
v___x_7176_ = l_Std_Time_instInhabitedDateTime;
v___x_7177_ = lean_panic_fn_borrowed(v___x_7176_, v_msg_7175_);
return v___x_7177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object* v_aw_7179_, lean_object* v_format_7180_, lean_object* v_input_7181_){
_start:
{
lean_object* v___x_7182_; 
v___x_7182_ = l_Std_Time_GenericFormat_parse(v_aw_7179_, v_format_7180_, v_input_7181_);
if (lean_obj_tag(v___x_7182_) == 0)
{
lean_object* v_a_7183_; lean_object* v___x_7184_; lean_object* v___x_7185_; lean_object* v___x_7186_; lean_object* v___x_7187_; lean_object* v___x_7188_; lean_object* v___x_7189_; 
v_a_7183_ = lean_ctor_get(v___x_7182_, 0);
lean_inc(v_a_7183_);
lean_dec_ref_known(v___x_7182_, 1);
v___x_7184_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7185_ = ((lean_object*)(l_Std_Time_GenericFormat_parse_x21___closed__0));
v___x_7186_ = lean_unsigned_to_nat(1124u);
v___x_7187_ = lean_unsigned_to_nat(18u);
v___x_7188_ = l_mkPanicMessageWithDecl(v___x_7184_, v___x_7185_, v___x_7186_, v___x_7187_, v_a_7183_);
lean_dec(v_a_7183_);
v___x_7189_ = l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(v___x_7188_);
return v___x_7189_;
}
else
{
lean_object* v_a_7190_; 
v_a_7190_ = lean_ctor_get(v___x_7182_, 0);
lean_inc(v_a_7190_);
lean_dec_ref_known(v___x_7182_, 1);
return v_a_7190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object* v_config_7191_, lean_object* v_string_7192_, lean_object* v_builder_7193_, lean_object* v___y_7194_){
_start:
{
lean_object* v___x_7195_; 
v___x_7195_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7191_, v_string_7192_, v_builder_7193_, v___y_7194_);
return v___x_7195_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object* v_format_7196_, lean_object* v_builder_7197_, lean_object* v_input_7198_){
_start:
{
lean_object* v_config_7199_; lean_object* v_string_7200_; lean_object* v___f_7201_; lean_object* v___x_7202_; 
v_config_7199_ = lean_ctor_get(v_format_7196_, 0);
lean_inc_ref(v_config_7199_);
v_string_7200_ = lean_ctor_get(v_format_7196_, 1);
lean_inc(v_string_7200_);
lean_dec_ref(v_format_7196_);
v___f_7201_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0), 4, 3);
lean_closure_set(v___f_7201_, 0, v_config_7199_);
lean_closure_set(v___f_7201_, 1, v_string_7200_);
lean_closure_set(v___f_7201_, 2, v_builder_7197_);
v___x_7202_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7201_, v_input_7198_);
return v___x_7202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object* v_aw_7203_, lean_object* v_00_u03b1_7204_, lean_object* v_format_7205_, lean_object* v_builder_7206_, lean_object* v_input_7207_){
_start:
{
lean_object* v___x_7208_; 
v___x_7208_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7205_, v_builder_7206_, v_input_7207_);
return v___x_7208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object* v_aw_7209_, lean_object* v_00_u03b1_7210_, lean_object* v_format_7211_, lean_object* v_builder_7212_, lean_object* v_input_7213_){
_start:
{
lean_object* v_res_7214_; 
v_res_7214_ = l_Std_Time_GenericFormat_parseBuilder(v_aw_7209_, v_00_u03b1_7210_, v_format_7211_, v_builder_7212_, v_input_7213_);
lean_dec(v_aw_7209_);
return v_res_7214_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object* v_inst_7216_, lean_object* v_format_7217_, lean_object* v_builder_7218_, lean_object* v_input_7219_){
_start:
{
lean_object* v___x_7220_; 
v___x_7220_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7217_, v_builder_7218_, v_input_7219_);
if (lean_obj_tag(v___x_7220_) == 0)
{
lean_object* v_a_7221_; lean_object* v___x_7222_; lean_object* v___x_7223_; lean_object* v___x_7224_; lean_object* v___x_7225_; lean_object* v___x_7226_; lean_object* v___x_7227_; 
v_a_7221_ = lean_ctor_get(v___x_7220_, 0);
lean_inc(v_a_7221_);
lean_dec_ref_known(v___x_7220_, 1);
v___x_7222_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7223_ = ((lean_object*)(l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0));
v___x_7224_ = lean_unsigned_to_nat(1138u);
v___x_7225_ = lean_unsigned_to_nat(18u);
v___x_7226_ = l_mkPanicMessageWithDecl(v___x_7222_, v___x_7223_, v___x_7224_, v___x_7225_, v_a_7221_);
lean_dec(v_a_7221_);
v___x_7227_ = l_panic___redArg(v_inst_7216_, v___x_7226_);
return v___x_7227_;
}
else
{
lean_object* v_a_7228_; 
v_a_7228_ = lean_ctor_get(v___x_7220_, 0);
lean_inc(v_a_7228_);
lean_dec_ref_known(v___x_7220_, 1);
return v_a_7228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object* v_inst_7229_, lean_object* v_format_7230_, lean_object* v_builder_7231_, lean_object* v_input_7232_){
_start:
{
lean_object* v_res_7233_; 
v_res_7233_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7229_, v_format_7230_, v_builder_7231_, v_input_7232_);
lean_dec(v_inst_7229_);
return v_res_7233_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object* v_00_u03b1_7234_, lean_object* v_aw_7235_, lean_object* v_inst_7236_, lean_object* v_format_7237_, lean_object* v_builder_7238_, lean_object* v_input_7239_){
_start:
{
lean_object* v___x_7240_; 
v___x_7240_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7236_, v_format_7237_, v_builder_7238_, v_input_7239_);
return v___x_7240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object* v_00_u03b1_7241_, lean_object* v_aw_7242_, lean_object* v_inst_7243_, lean_object* v_format_7244_, lean_object* v_builder_7245_, lean_object* v_input_7246_){
_start:
{
lean_object* v_res_7247_; 
v_res_7247_ = l_Std_Time_GenericFormat_parseBuilder_x21(v_00_u03b1_7241_, v_aw_7242_, v_inst_7243_, v_format_7244_, v_builder_7245_, v_input_7246_);
lean_dec(v_inst_7243_);
lean_dec(v_aw_7242_);
return v_res_7247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object* v_getInfo_7248_, lean_object* v_dateformat_7249_, lean_object* v_data_7250_, lean_object* v_format_7251_){
_start:
{
if (lean_obj_tag(v_format_7251_) == 0)
{
lean_object* v___x_7252_; 
lean_dec_ref(v_getInfo_7248_);
v___x_7252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7252_, 0, v_data_7250_);
return v___x_7252_;
}
else
{
lean_object* v_head_7253_; 
v_head_7253_ = lean_ctor_get(v_format_7251_, 0);
lean_inc(v_head_7253_);
if (lean_obj_tag(v_head_7253_) == 0)
{
lean_object* v_tail_7254_; lean_object* v_val_7255_; lean_object* v___x_7256_; 
v_tail_7254_ = lean_ctor_get(v_format_7251_, 1);
lean_inc(v_tail_7254_);
lean_dec_ref_known(v_format_7251_, 2);
v_val_7255_ = lean_ctor_get(v_head_7253_, 0);
lean_inc_ref(v_val_7255_);
lean_dec_ref_known(v_head_7253_, 1);
v___x_7256_ = lean_string_append(v_data_7250_, v_val_7255_);
lean_dec_ref(v_val_7255_);
v_data_7250_ = v___x_7256_;
v_format_7251_ = v_tail_7254_;
goto _start;
}
else
{
lean_object* v_tail_7258_; lean_object* v_modifier_7259_; lean_object* v___x_7260_; 
v_tail_7258_ = lean_ctor_get(v_format_7251_, 1);
lean_inc(v_tail_7258_);
lean_dec_ref_known(v_format_7251_, 2);
v_modifier_7259_ = lean_ctor_get(v_head_7253_, 0);
lean_inc_ref_n(v_modifier_7259_, 2);
lean_dec_ref_known(v_head_7253_, 1);
lean_inc_ref(v_getInfo_7248_);
v___x_7260_ = lean_apply_1(v_getInfo_7248_, v_modifier_7259_);
if (lean_obj_tag(v___x_7260_) == 0)
{
lean_object* v___x_7261_; 
lean_dec_ref(v_modifier_7259_);
lean_dec(v_tail_7258_);
lean_dec_ref(v_data_7250_);
lean_dec_ref(v_getInfo_7248_);
v___x_7261_ = lean_box(0);
return v___x_7261_;
}
else
{
lean_object* v_val_7262_; lean_object* v___x_7263_; lean_object* v___x_7264_; 
v_val_7262_ = lean_ctor_get(v___x_7260_, 0);
lean_inc(v_val_7262_);
lean_dec_ref_known(v___x_7260_, 1);
v___x_7263_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7249_, v_modifier_7259_, v_val_7262_);
v___x_7264_ = lean_string_append(v_data_7250_, v___x_7263_);
lean_dec_ref(v___x_7263_);
v_data_7250_ = v___x_7264_;
v_format_7251_ = v_tail_7258_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go___boxed(lean_object* v_getInfo_7266_, lean_object* v_dateformat_7267_, lean_object* v_data_7268_, lean_object* v_format_7269_){
_start:
{
lean_object* v_res_7270_; 
v_res_7270_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7266_, v_dateformat_7267_, v_data_7268_, v_format_7269_);
lean_dec_ref(v_dateformat_7267_);
return v_res_7270_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object* v_format_7271_, lean_object* v_getInfo_7272_){
_start:
{
lean_object* v_config_7273_; lean_object* v_string_7274_; lean_object* v_dateformat_7275_; lean_object* v___x_7276_; lean_object* v___x_7277_; 
v_config_7273_ = lean_ctor_get(v_format_7271_, 0);
lean_inc_ref(v_config_7273_);
v_string_7274_ = lean_ctor_get(v_format_7271_, 1);
lean_inc(v_string_7274_);
lean_dec_ref(v_format_7271_);
v_dateformat_7275_ = lean_ctor_get(v_config_7273_, 0);
lean_inc_ref(v_dateformat_7275_);
lean_dec_ref(v_config_7273_);
v___x_7276_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_7277_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7272_, v_dateformat_7275_, v___x_7276_, v_string_7274_);
lean_dec_ref(v_dateformat_7275_);
return v___x_7277_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object* v_aw_7278_, lean_object* v_format_7279_, lean_object* v_getInfo_7280_){
_start:
{
lean_object* v___x_7281_; 
v___x_7281_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7279_, v_getInfo_7280_);
return v___x_7281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object* v_aw_7282_, lean_object* v_format_7283_, lean_object* v_getInfo_7284_){
_start:
{
lean_object* v_res_7285_; 
v_res_7285_ = l_Std_Time_GenericFormat_formatGeneric(v_aw_7282_, v_format_7283_, v_getInfo_7284_);
lean_dec(v_aw_7282_);
return v_res_7285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object* v_dateformat_7286_, lean_object* v_data_7287_, lean_object* v_format_7288_){
_start:
{
if (lean_obj_tag(v_format_7288_) == 0)
{
lean_dec_ref(v_dateformat_7286_);
return v_data_7287_;
}
else
{
lean_object* v_head_7289_; 
v_head_7289_ = lean_ctor_get(v_format_7288_, 0);
lean_inc(v_head_7289_);
if (lean_obj_tag(v_head_7289_) == 0)
{
lean_object* v_tail_7290_; lean_object* v_val_7291_; lean_object* v___x_7292_; 
v_tail_7290_ = lean_ctor_get(v_format_7288_, 1);
lean_inc(v_tail_7290_);
lean_dec_ref_known(v_format_7288_, 2);
v_val_7291_ = lean_ctor_get(v_head_7289_, 0);
lean_inc_ref(v_val_7291_);
lean_dec_ref_known(v_head_7289_, 1);
v___x_7292_ = lean_string_append(v_data_7287_, v_val_7291_);
lean_dec_ref(v_val_7291_);
v_data_7287_ = v___x_7292_;
v_format_7288_ = v_tail_7290_;
goto _start;
}
else
{
lean_object* v_tail_7294_; lean_object* v_modifier_7295_; lean_object* v___f_7296_; 
v_tail_7294_ = lean_ctor_get(v_format_7288_, 1);
lean_inc(v_tail_7294_);
lean_dec_ref_known(v_format_7288_, 2);
v_modifier_7295_ = lean_ctor_get(v_head_7289_, 0);
lean_inc_ref(v_modifier_7295_);
lean_dec_ref_known(v_head_7289_, 1);
v___f_7296_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0), 5, 4);
lean_closure_set(v___f_7296_, 0, v_dateformat_7286_);
lean_closure_set(v___f_7296_, 1, v_modifier_7295_);
lean_closure_set(v___f_7296_, 2, v_data_7287_);
lean_closure_set(v___f_7296_, 3, v_tail_7294_);
return v___f_7296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object* v_dateformat_7297_, lean_object* v_modifier_7298_, lean_object* v_data_7299_, lean_object* v_tail_7300_, lean_object* v___y_7301_){
_start:
{
lean_object* v___x_7302_; lean_object* v___x_7303_; lean_object* v___x_7304_; 
v___x_7302_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7297_, v_modifier_7298_, v___y_7301_);
v___x_7303_ = lean_string_append(v_data_7299_, v___x_7302_);
lean_dec_ref(v___x_7302_);
v___x_7304_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7297_, v___x_7303_, v_tail_7300_);
return v___x_7304_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object* v_format_7305_){
_start:
{
lean_object* v_config_7306_; lean_object* v_string_7307_; lean_object* v_dateformat_7308_; lean_object* v___x_7309_; lean_object* v___x_7310_; 
v_config_7306_ = lean_ctor_get(v_format_7305_, 0);
lean_inc_ref(v_config_7306_);
v_string_7307_ = lean_ctor_get(v_format_7305_, 1);
lean_inc(v_string_7307_);
lean_dec_ref(v_format_7305_);
v_dateformat_7308_ = lean_ctor_get(v_config_7306_, 0);
lean_inc_ref(v_dateformat_7308_);
lean_dec_ref(v_config_7306_);
v___x_7309_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_7310_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7308_, v___x_7309_, v_string_7307_);
return v___x_7310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object* v_aw_7311_, lean_object* v_format_7312_){
_start:
{
lean_object* v___x_7313_; 
v___x_7313_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v_format_7312_);
return v___x_7313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object* v_aw_7314_, lean_object* v_format_7315_){
_start:
{
lean_object* v_res_7316_; 
v_res_7316_ = l_Std_Time_GenericFormat_formatBuilder(v_aw_7314_, v_format_7315_);
lean_dec(v_aw_7314_);
return v_res_7316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instFormatGenericFormatFormatTypeString(lean_object* v_aw_7317_){
_start:
{
lean_object* v___x_7318_; lean_object* v___x_7319_; lean_object* v___x_7320_; 
lean_inc(v_aw_7317_);
v___x_7318_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_formatBuilder___boxed), 2, 1);
lean_closure_set(v___x_7318_, 0, v_aw_7317_);
v___x_7319_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___boxed), 5, 1);
lean_closure_set(v___x_7319_, 0, v_aw_7317_);
v___x_7320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7320_, 0, v___x_7318_);
lean_ctor_set(v___x_7320_, 1, v___x_7319_);
return v___x_7320_;
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
