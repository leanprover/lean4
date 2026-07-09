// Lean compiler output
// Module: Std.Time.Format.Modifier
// Imports: public import Std.Time.Zoned import Init.Data.String.Search
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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Text_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprText_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Text.short"};
static const lean_object* l_Std_Time_instReprText_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprText_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprText_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprText_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprText_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprText_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprText_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Std.Time.Text.full"};
static const lean_object* l_Std_Time_instReprText_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprText_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprText_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprText_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprText_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprText_repr___closed__3_value;
static const lean_string_object l_Std_Time_instReprText_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Time.Text.narrow"};
static const lean_object* l_Std_Time_instReprText_repr___closed__4 = (const lean_object*)&l_Std_Time_instReprText_repr___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprText_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprText_repr___closed__4_value)}};
static const lean_object* l_Std_Time_instReprText_repr___closed__5 = (const lean_object*)&l_Std_Time_instReprText_repr___closed__5_value;
static const lean_string_object l_Std_Time_instReprText_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Time.Text.twoLetterShort"};
static const lean_object* l_Std_Time_instReprText_repr___closed__6 = (const lean_object*)&l_Std_Time_instReprText_repr___closed__6_value;
static const lean_ctor_object l_Std_Time_instReprText_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprText_repr___closed__6_value)}};
static const lean_object* l_Std_Time_instReprText_repr___closed__7 = (const lean_object*)&l_Std_Time_instReprText_repr___closed__7_value;
static lean_once_cell_t l_Std_Time_instReprText_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprText_repr___closed__8;
static lean_once_cell_t l_Std_Time_instReprText_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprText_repr___closed__9;
LEAN_EXPORT lean_object* l_Std_Time_instReprText_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprText_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprText_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprText___closed__0 = (const lean_object*)&l_Std_Time_instReprText___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprText = (const lean_object*)&l_Std_Time_instReprText___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedText_default;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedText;
static const lean_ctor_object l_Std_Time_Text_classify___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Text_classify___closed__0 = (const lean_object*)&l_Std_Time_Text_classify___closed__0_value;
static const lean_ctor_object l_Std_Time_Text_classify___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_Text_classify___closed__1 = (const lean_object*)&l_Std_Time_Text_classify___closed__1_value;
static const lean_ctor_object l_Std_Time_Text_classify___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Text_classify___closed__2 = (const lean_object*)&l_Std_Time_Text_classify___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Text_classify(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_classify___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprNumber_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_instReprNumber_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_instReprNumber_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "padding"};
static const lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprNumber_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprNumber_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_instReprNumber_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprNumber_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_instReprNumber_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_instReprNumber_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_instReprNumber_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__8_value;
static lean_once_cell_t l_Std_Time_instReprNumber_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__9;
static lean_once_cell_t l_Std_Time_instReprNumber_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__10;
static const lean_ctor_object l_Std_Time_instReprNumber_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Time_instReprNumber_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_instReprNumber_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_instReprNumber_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprNumber_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprNumber___closed__0 = (const lean_object*)&l_Std_Time_instReprNumber___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprNumber = (const lean_object*)&l_Std_Time_instReprNumber___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedNumber_default;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedNumber;
LEAN_EXPORT lean_object* l_Std_Time_classifyNumberText(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Fraction_nano_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Fraction_nano_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Fraction_truncated_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Fraction_truncated_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprFraction_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Fraction.nano"};
static const lean_object* l_Std_Time_instReprFraction_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprFraction_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprFraction_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprFraction_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprFraction_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprFraction_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprFraction_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Time.Fraction.truncated"};
static const lean_object* l_Std_Time_instReprFraction_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprFraction_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprFraction_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprFraction_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprFraction_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprFraction_repr___closed__3_value;
static const lean_ctor_object l_Std_Time_instReprFraction_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprFraction_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprFraction_repr___closed__4 = (const lean_object*)&l_Std_Time_instReprFraction_repr___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprFraction_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprFraction_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprFraction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprFraction_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprFraction___closed__0 = (const lean_object*)&l_Std_Time_instReprFraction___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprFraction = (const lean_object*)&l_Std_Time_instReprFraction___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedFraction_default;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedFraction;
static const lean_ctor_object l_Std_Time_Fraction_classify___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Fraction_classify___closed__0 = (const lean_object*)&l_Std_Time_Fraction_classify___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Fraction_classify(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_any_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_any_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_twoDigit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_twoDigit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_fourDigit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_fourDigit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_extended_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_extended_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprYear_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.Year.fourDigit"};
static const lean_object* l_Std_Time_instReprYear_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprYear_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprYear_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprYear_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprYear_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprYear_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprYear_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Year.twoDigit"};
static const lean_object* l_Std_Time_instReprYear_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprYear_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprYear_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprYear_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprYear_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprYear_repr___closed__3_value;
static const lean_string_object l_Std_Time_instReprYear_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Std.Time.Year.any"};
static const lean_object* l_Std_Time_instReprYear_repr___closed__4 = (const lean_object*)&l_Std_Time_instReprYear_repr___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprYear_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprYear_repr___closed__4_value)}};
static const lean_object* l_Std_Time_instReprYear_repr___closed__5 = (const lean_object*)&l_Std_Time_instReprYear_repr___closed__5_value;
static const lean_string_object l_Std_Time_instReprYear_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Year.extended"};
static const lean_object* l_Std_Time_instReprYear_repr___closed__6 = (const lean_object*)&l_Std_Time_instReprYear_repr___closed__6_value;
static const lean_ctor_object l_Std_Time_instReprYear_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprYear_repr___closed__6_value)}};
static const lean_object* l_Std_Time_instReprYear_repr___closed__7 = (const lean_object*)&l_Std_Time_instReprYear_repr___closed__7_value;
static const lean_ctor_object l_Std_Time_instReprYear_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprYear_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprYear_repr___closed__8 = (const lean_object*)&l_Std_Time_instReprYear_repr___closed__8_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprYear_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprYear_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprYear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprYear_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprYear___closed__0 = (const lean_object*)&l_Std_Time_instReprYear___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprYear = (const lean_object*)&l_Std_Time_instReprYear___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedYear_default;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedYear;
static const lean_ctor_object l_Std_Time_Year_classify___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Year_classify___closed__0 = (const lean_object*)&l_Std_Time_Year_classify___closed__0_value;
static const lean_ctor_object l_Std_Time_Year_classify___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_Year_classify___closed__1 = (const lean_object*)&l_Std_Time_Year_classify___closed__1_value;
static const lean_ctor_object l_Std_Time_Year_classify___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Year_classify___closed__2 = (const lean_object*)&l_Std_Time_Year_classify___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Year_classify(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprZoneId_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.ZoneId.unknown"};
static const lean_object* l_Std_Time_instReprZoneId_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprZoneId_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprZoneId_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprZoneId_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprZoneId_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprZoneId_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprZoneId_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.ZoneId.short"};
static const lean_object* l_Std_Time_instReprZoneId_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprZoneId_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprZoneId_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprZoneId_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprZoneId_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprZoneId_repr___closed__3_value;
static const lean_string_object l_Std_Time_instReprZoneId_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Time.ZoneId.full"};
static const lean_object* l_Std_Time_instReprZoneId_repr___closed__4 = (const lean_object*)&l_Std_Time_instReprZoneId_repr___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprZoneId_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprZoneId_repr___closed__4_value)}};
static const lean_object* l_Std_Time_instReprZoneId_repr___closed__5 = (const lean_object*)&l_Std_Time_instReprZoneId_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprZoneId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprZoneId_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprZoneId___closed__0 = (const lean_object*)&l_Std_Time_instReprZoneId___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprZoneId = (const lean_object*)&l_Std_Time_instReprZoneId___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedZoneId_default;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedZoneId;
static const lean_ctor_object l_Std_Time_ZoneId_classify___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_ZoneId_classify___closed__0 = (const lean_object*)&l_Std_Time_ZoneId_classify___closed__0_value;
static const lean_ctor_object l_Std_Time_ZoneId_classify___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_ZoneId_classify___closed__1 = (const lean_object*)&l_Std_Time_ZoneId_classify___closed__1_value;
static const lean_ctor_object l_Std_Time_ZoneId_classify___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_ZoneId_classify___closed__2 = (const lean_object*)&l_Std_Time_ZoneId_classify___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprZoneName_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.ZoneName.short"};
static const lean_object* l_Std_Time_instReprZoneName_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprZoneName_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprZoneName_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprZoneName_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprZoneName_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprZoneName_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprZoneName_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.ZoneName.full"};
static const lean_object* l_Std_Time_instReprZoneName_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprZoneName_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprZoneName_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprZoneName_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprZoneName_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprZoneName_repr___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprZoneName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprZoneName_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprZoneName___closed__0 = (const lean_object*)&l_Std_Time_instReprZoneName___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprZoneName = (const lean_object*)&l_Std_Time_instReprZoneName___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedZoneName_default;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedZoneName;
static const lean_ctor_object l_Std_Time_ZoneName_classify___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_ZoneName_classify___closed__0 = (const lean_object*)&l_Std_Time_ZoneName_classify___closed__0_value;
static const lean_ctor_object l_Std_Time_ZoneName_classify___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_ZoneName_classify___closed__1 = (const lean_object*)&l_Std_Time_ZoneName_classify___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprOffsetX_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.OffsetX.hour"};
static const lean_object* l_Std_Time_instReprOffsetX_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprOffsetX_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprOffsetX_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprOffsetX_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Time.OffsetX.hourMinute"};
static const lean_object* l_Std_Time_instReprOffsetX_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprOffsetX_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprOffsetX_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__3_value;
static const lean_string_object l_Std_Time_instReprOffsetX_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Std.Time.OffsetX.hourMinuteColon"};
static const lean_object* l_Std_Time_instReprOffsetX_repr___closed__4 = (const lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprOffsetX_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__4_value)}};
static const lean_object* l_Std_Time_instReprOffsetX_repr___closed__5 = (const lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__5_value;
static const lean_string_object l_Std_Time_instReprOffsetX_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.Time.OffsetX.hourMinuteSecond"};
static const lean_object* l_Std_Time_instReprOffsetX_repr___closed__6 = (const lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__6_value;
static const lean_ctor_object l_Std_Time_instReprOffsetX_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__6_value)}};
static const lean_object* l_Std_Time_instReprOffsetX_repr___closed__7 = (const lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__7_value;
static const lean_string_object l_Std_Time_instReprOffsetX_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Time.OffsetX.hourMinuteSecondColon"};
static const lean_object* l_Std_Time_instReprOffsetX_repr___closed__8 = (const lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__8_value;
static const lean_ctor_object l_Std_Time_instReprOffsetX_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__8_value)}};
static const lean_object* l_Std_Time_instReprOffsetX_repr___closed__9 = (const lean_object*)&l_Std_Time_instReprOffsetX_repr___closed__9_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprOffsetX___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprOffsetX_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprOffsetX___closed__0 = (const lean_object*)&l_Std_Time_instReprOffsetX___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprOffsetX = (const lean_object*)&l_Std_Time_instReprOffsetX___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedOffsetX_default;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedOffsetX;
static const lean_ctor_object l_Std_Time_OffsetX_classify___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Std_Time_OffsetX_classify___closed__0 = (const lean_object*)&l_Std_Time_OffsetX_classify___closed__0_value;
static const lean_ctor_object l_Std_Time_OffsetX_classify___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Std_Time_OffsetX_classify___closed__1 = (const lean_object*)&l_Std_Time_OffsetX_classify___closed__1_value;
static const lean_ctor_object l_Std_Time_OffsetX_classify___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_OffsetX_classify___closed__2 = (const lean_object*)&l_Std_Time_OffsetX_classify___closed__2_value;
static const lean_ctor_object l_Std_Time_OffsetX_classify___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_OffsetX_classify___closed__3 = (const lean_object*)&l_Std_Time_OffsetX_classify___closed__3_value;
static const lean_ctor_object l_Std_Time_OffsetX_classify___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_OffsetX_classify___closed__4 = (const lean_object*)&l_Std_Time_OffsetX_classify___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprOffsetO_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.OffsetO.short"};
static const lean_object* l_Std_Time_instReprOffsetO_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprOffsetO_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprOffsetO_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprOffsetO_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprOffsetO_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprOffsetO_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprOffsetO_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.OffsetO.full"};
static const lean_object* l_Std_Time_instReprOffsetO_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprOffsetO_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprOffsetO_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprOffsetO_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprOffsetO_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprOffsetO_repr___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprOffsetO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprOffsetO_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprOffsetO___closed__0 = (const lean_object*)&l_Std_Time_instReprOffsetO___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprOffsetO = (const lean_object*)&l_Std_Time_instReprOffsetO___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedOffsetO_default;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedOffsetO;
static const lean_ctor_object l_Std_Time_OffsetO_classify___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_OffsetO_classify___closed__0 = (const lean_object*)&l_Std_Time_OffsetO_classify___closed__0_value;
static const lean_ctor_object l_Std_Time_OffsetO_classify___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_OffsetO_classify___closed__1 = (const lean_object*)&l_Std_Time_OffsetO_classify___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprOffsetZ_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Time.OffsetZ.hourMinute"};
static const lean_object* l_Std_Time_instReprOffsetZ_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprOffsetZ_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprOffsetZ_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprOffsetZ_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprOffsetZ_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprOffsetZ_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprOffsetZ_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.OffsetZ.full"};
static const lean_object* l_Std_Time_instReprOffsetZ_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprOffsetZ_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprOffsetZ_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprOffsetZ_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprOffsetZ_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprOffsetZ_repr___closed__3_value;
static const lean_string_object l_Std_Time_instReprOffsetZ_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Time.OffsetZ.hourMinuteSecondColon"};
static const lean_object* l_Std_Time_instReprOffsetZ_repr___closed__4 = (const lean_object*)&l_Std_Time_instReprOffsetZ_repr___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprOffsetZ_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprOffsetZ_repr___closed__4_value)}};
static const lean_object* l_Std_Time_instReprOffsetZ_repr___closed__5 = (const lean_object*)&l_Std_Time_instReprOffsetZ_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprOffsetZ___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprOffsetZ_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprOffsetZ___closed__0 = (const lean_object*)&l_Std_Time_instReprOffsetZ___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprOffsetZ = (const lean_object*)&l_Std_Time_instReprOffsetZ___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedOffsetZ_default;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedOffsetZ;
static const lean_ctor_object l_Std_Time_OffsetZ_classify___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_OffsetZ_classify___closed__0 = (const lean_object*)&l_Std_Time_OffsetZ_classify___closed__0_value;
static const lean_ctor_object l_Std_Time_OffsetZ_classify___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_OffsetZ_classify___closed__1 = (const lean_object*)&l_Std_Time_OffsetZ_classify___closed__1_value;
static const lean_ctor_object l_Std_Time_OffsetZ_classify___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_OffsetZ_classify___closed__2 = (const lean_object*)&l_Std_Time_OffsetZ_classify___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprDayPeriod_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.DayPeriod.am"};
static const lean_object* l_Std_Time_instReprDayPeriod_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriod_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprDayPeriod_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprDayPeriod_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.DayPeriod.pm"};
static const lean_object* l_Std_Time_instReprDayPeriod_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriod_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprDayPeriod_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__3_value;
static const lean_string_object l_Std_Time_instReprDayPeriod_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.DayPeriod.noon"};
static const lean_object* l_Std_Time_instReprDayPeriod_repr___closed__4 = (const lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriod_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__4_value)}};
static const lean_object* l_Std_Time_instReprDayPeriod_repr___closed__5 = (const lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__5_value;
static const lean_string_object l_Std_Time_instReprDayPeriod_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Time.DayPeriod.midnight"};
static const lean_object* l_Std_Time_instReprDayPeriod_repr___closed__6 = (const lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__6_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriod_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__6_value)}};
static const lean_object* l_Std_Time_instReprDayPeriod_repr___closed__7 = (const lean_object*)&l_Std_Time_instReprDayPeriod_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprDayPeriod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprDayPeriod_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprDayPeriod___closed__0 = (const lean_object*)&l_Std_Time_instReprDayPeriod___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprDayPeriod = (const lean_object*)&l_Std_Time_instReprDayPeriod___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedDayPeriod_default;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedDayPeriod;
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Time.ExtendedDayPeriod.midnight"};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Std.Time.ExtendedDayPeriod.night"};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__3_value;
static const lean_string_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Time.ExtendedDayPeriod.morning"};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__4 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__4_value)}};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__5 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__5_value;
static const lean_string_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Time.ExtendedDayPeriod.noon"};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__6 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__6_value;
static const lean_ctor_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__6_value)}};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__7 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__7_value;
static const lean_string_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Time.ExtendedDayPeriod.afternoon"};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__8 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__8_value;
static const lean_ctor_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__8_value)}};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__9 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__9_value;
static const lean_string_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Time.ExtendedDayPeriod.evening"};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__10 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__10_value;
static const lean_ctor_object l_Std_Time_instReprExtendedDayPeriod_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__10_value)}};
static const lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___closed__11 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprExtendedDayPeriod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprExtendedDayPeriod_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprExtendedDayPeriod___closed__0 = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprExtendedDayPeriod = (const lean_object*)&l_Std_Time_instReprExtendedDayPeriod___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedExtendedDayPeriod_default;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedExtendedDayPeriod;
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Sum.inl "};
static const lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__0 = (const lean_object*)&l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__0_value)}};
static const lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__1 = (const lean_object*)&l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__1_value;
static const lean_string_object l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Sum.inr "};
static const lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__2 = (const lean_object*)&l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__2_value)}};
static const lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__3 = (const lean_object*)&l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.G"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__2_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.u"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__3_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__3_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__4 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__5 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__5_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.y"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__6 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__6_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__6_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__7 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__7_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__8 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__8_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.D"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__9 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__9_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__9_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__10 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__10_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__11 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__11_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.M"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__12 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__12_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__12_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__13 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__13_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__14 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__14_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.L"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__15 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__15_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__15_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__16 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__16_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__17 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__17_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.d"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__18 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__18_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__18_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__19 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__19_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__20 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__20_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Q"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__21 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__21_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__21_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__22 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__22_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__22_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__23 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__23_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.q"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__24 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__24_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__24_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__25 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__25_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__25_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__26 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__26_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Y"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__27 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__27_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__27_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__28 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__28_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__28_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__29 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__29_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.w"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__30 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__30_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__30_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__31 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__31_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__31_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__32 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__32_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.W"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__33 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__33_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__33_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__34 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__34_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__34_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__35 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__35_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.E"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__36 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__36_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__36_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__37 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__37_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__37_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__38 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__38_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.e"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__39 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__39_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__39_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__40 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__40_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__40_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__41 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__41_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.c"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__42 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__42_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__42_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__43 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__43_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__43_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__44 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__44_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.F"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__45 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__45_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__45_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__46 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__46_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__46_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__47 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__47_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.a"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__48 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__48_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__48_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__49 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__49_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__49_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__50 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__50_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.b"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__51 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__51_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__51_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__52 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__52_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__52_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__53 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__53_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.B"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__54 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__54_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__54_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__55 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__55_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__55_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__56 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__56_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.h"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__57 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__57_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__57_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__58 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__58_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__58_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__59 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__59_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.K"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__60 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__60_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__60_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__61 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__61_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__61_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__62 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__62_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.k"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__63 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__63_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__63_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__64 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__64_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__64_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__65 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__65_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.H"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__66 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__66_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__66_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__67 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__67_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__67_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__68 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__68_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.m"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__69 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__69_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__69_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__70 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__70_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__70_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__71 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__71_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.s"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__72 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__72_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__72_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__73 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__73_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__73_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__74 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__74_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.S"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__75 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__75_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__75_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__76 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__76_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__76_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__77 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__77_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.A"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__78 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__78_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__78_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__79 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__79_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__79_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__80 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__80_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.n"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__81 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__81_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__81_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__82 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__82_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__82_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__83 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__83_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.N"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__84 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__84_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__84_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__85 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__85_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__85_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__86 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__86_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.V"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__87 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__87_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__87_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__88 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__88_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__88_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__89 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__89_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.z"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__90 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__90_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__90_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__91 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__91_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__91_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__92 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__92_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.v"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__93 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__93_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__93_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__94 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__94_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__94_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__95 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__95_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.O"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__96 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__96_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__96_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__97 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__97_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__97_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__98 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__98_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.X"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__99 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__99_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__99_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__100 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__100_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__100_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__101 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__101_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.x"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__102 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__102_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__102_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__103 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__103_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__103_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__104 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__104_value;
static const lean_string_object l_Std_Time_instReprModifier_repr___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Z"};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__105 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__105_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__105_value)}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__106 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__106_value;
static const lean_ctor_object l_Std_Time_instReprModifier_repr___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprModifier_repr___closed__106_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprModifier_repr___closed__107 = (const lean_object*)&l_Std_Time_instReprModifier_repr___closed__107_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprModifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprModifier_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprModifier___closed__0 = (const lean_object*)&l_Std_Time_instReprModifier___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprModifier = (const lean_object*)&l_Std_Time_instReprModifier___closed__0_value;
static const lean_ctor_object l_Std_Time_instInhabitedModifier_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_instInhabitedModifier_default___closed__0 = (const lean_object*)&l_Std_Time_instInhabitedModifier_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instInhabitedModifier_default = (const lean_object*)&l_Std_Time_instInhabitedModifier_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instInhabitedModifier = (const lean_object*)&l_Std_Time_instInhabitedModifier_default___closed__0_value;
static const lean_string_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "invalid quantity of characters for '"};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0_value;
static const lean_string_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1_value;
static const lean_string_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Text_classify___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseText___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseText___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___boxed(lean_object*);
static const lean_ctor_object l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___boxed(lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Fraction_classify, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Year_classify, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_OffsetX_classify___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_OffsetZ_classify___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_OffsetO_classify___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "': must be 1 or 2"};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 29}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 29}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_classifyNumberText, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText(lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___boxed(lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__7(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__8(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__9(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__10(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__11(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__12(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__13(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__14(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__15(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__16(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__17(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__18(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__20(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__22(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__23(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__24(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__25(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__26(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__27(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__28(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__29(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__30(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31___boxed(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0_value;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_parseModifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__0 = (const lean_object*)&l_Std_Time_parseModifier___closed__0_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__1 = (const lean_object*)&l_Std_Time_parseModifier___closed__1_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__2 = (const lean_object*)&l_Std_Time_parseModifier___closed__2_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__3 = (const lean_object*)&l_Std_Time_parseModifier___closed__3_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__4 = (const lean_object*)&l_Std_Time_parseModifier___closed__4_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__5 = (const lean_object*)&l_Std_Time_parseModifier___closed__5_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__6, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__6 = (const lean_object*)&l_Std_Time_parseModifier___closed__6_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__7, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__7 = (const lean_object*)&l_Std_Time_parseModifier___closed__7_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__8, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__8 = (const lean_object*)&l_Std_Time_parseModifier___closed__8_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__9, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__9 = (const lean_object*)&l_Std_Time_parseModifier___closed__9_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__10, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__10 = (const lean_object*)&l_Std_Time_parseModifier___closed__10_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__11, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__11 = (const lean_object*)&l_Std_Time_parseModifier___closed__11_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__12, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__12 = (const lean_object*)&l_Std_Time_parseModifier___closed__12_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__13, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__13 = (const lean_object*)&l_Std_Time_parseModifier___closed__13_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__14, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__14 = (const lean_object*)&l_Std_Time_parseModifier___closed__14_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__15, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__15 = (const lean_object*)&l_Std_Time_parseModifier___closed__15_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__16, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__16 = (const lean_object*)&l_Std_Time_parseModifier___closed__16_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__17, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__17 = (const lean_object*)&l_Std_Time_parseModifier___closed__17_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__18, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__18 = (const lean_object*)&l_Std_Time_parseModifier___closed__18_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__19___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__19 = (const lean_object*)&l_Std_Time_parseModifier___closed__19_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__20, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__20 = (const lean_object*)&l_Std_Time_parseModifier___closed__20_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__21 = (const lean_object*)&l_Std_Time_parseModifier___closed__21_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__21, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__22 = (const lean_object*)&l_Std_Time_parseModifier___closed__22_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__22, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__23 = (const lean_object*)&l_Std_Time_parseModifier___closed__23_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__23, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__24 = (const lean_object*)&l_Std_Time_parseModifier___closed__24_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__24, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__25 = (const lean_object*)&l_Std_Time_parseModifier___closed__25_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l_Std_Time_parseModifier___closed__26 = (const lean_object*)&l_Std_Time_parseModifier___closed__26_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__25, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__27 = (const lean_object*)&l_Std_Time_parseModifier___closed__27_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__26, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__28 = (const lean_object*)&l_Std_Time_parseModifier___closed__28_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__27, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__29 = (const lean_object*)&l_Std_Time_parseModifier___closed__29_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))} };
static const lean_object* l_Std_Time_parseModifier___closed__30 = (const lean_object*)&l_Std_Time_parseModifier___closed__30_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__28, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__31 = (const lean_object*)&l_Std_Time_parseModifier___closed__31_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__29, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__32 = (const lean_object*)&l_Std_Time_parseModifier___closed__32_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__30, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__33 = (const lean_object*)&l_Std_Time_parseModifier___closed__33_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__31___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__34 = (const lean_object*)&l_Std_Time_parseModifier___closed__34_value;
LEAN_EXPORT lean_object* l_Std_Time_parseModifier(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Std_Time_Text_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_toCtorIdx(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Std_Time_Text_ctorIdx(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_toCtorIdx___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_4__boxed_12_; lean_object* v_res_13_; 
v_x_4__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_Std_Time_Text_toCtorIdx(v_x_4__boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___redArg(lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___redArg___boxed(lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_Time_Text_ctorElim___redArg(v_k_15_);
lean_dec(v_k_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, uint8_t v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_inc(v_k_21_);
return v_k_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
uint8_t v_t_boxed_27_; lean_object* v_res_28_; 
v_t_boxed_27_ = lean_unbox(v_t_24_);
v_res_28_ = l_Std_Time_Text_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_boxed_27_, v_h_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___redArg(lean_object* v_short_29_){
_start:
{
lean_inc(v_short_29_);
return v_short_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___redArg___boxed(lean_object* v_short_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Time_Text_short_elim___redArg(v_short_30_);
lean_dec(v_short_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim(lean_object* v_motive_32_, uint8_t v_t_33_, lean_object* v_h_34_, lean_object* v_short_35_){
_start:
{
lean_inc(v_short_35_);
return v_short_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_short_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = l_Std_Time_Text_short_elim(v_motive_36_, v_t_boxed_40_, v_h_38_, v_short_39_);
lean_dec(v_short_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___redArg(lean_object* v_full_42_){
_start:
{
lean_inc(v_full_42_);
return v_full_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___redArg___boxed(lean_object* v_full_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Time_Text_full_elim___redArg(v_full_43_);
lean_dec(v_full_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_full_48_){
_start:
{
lean_inc(v_full_48_);
return v_full_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_full_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Std_Time_Text_full_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_full_52_);
lean_dec(v_full_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___redArg(lean_object* v_narrow_55_){
_start:
{
lean_inc(v_narrow_55_);
return v_narrow_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___redArg___boxed(lean_object* v_narrow_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Time_Text_narrow_elim___redArg(v_narrow_56_);
lean_dec(v_narrow_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_narrow_61_){
_start:
{
lean_inc(v_narrow_61_);
return v_narrow_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_narrow_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_Std_Time_Text_narrow_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_narrow_65_);
lean_dec(v_narrow_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___redArg(lean_object* v_twoLetterShort_68_){
_start:
{
lean_inc(v_twoLetterShort_68_);
return v_twoLetterShort_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___redArg___boxed(lean_object* v_twoLetterShort_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_Time_Text_twoLetterShort_elim___redArg(v_twoLetterShort_69_);
lean_dec(v_twoLetterShort_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_twoLetterShort_74_){
_start:
{
lean_inc(v_twoLetterShort_74_);
return v_twoLetterShort_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_twoLetterShort_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_Std_Time_Text_twoLetterShort_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_twoLetterShort_78_);
lean_dec(v_twoLetterShort_78_);
return v_res_80_;
}
}
static lean_object* _init_l_Std_Time_instReprText_repr___closed__8(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(2u);
v___x_94_ = lean_nat_to_int(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Std_Time_instReprText_repr___closed__9(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_nat_to_int(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprText_repr(uint8_t v_x_97_, lean_object* v_prec_98_){
_start:
{
lean_object* v___y_100_; lean_object* v___y_107_; lean_object* v___y_114_; lean_object* v___y_121_; 
switch(v_x_97_)
{
case 0:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1024u);
v___x_128_ = lean_nat_dec_le(v___x_127_, v_prec_98_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_100_ = v___x_129_;
goto v___jp_99_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_100_ = v___x_130_;
goto v___jp_99_;
}
}
case 1:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1024u);
v___x_132_ = lean_nat_dec_le(v___x_131_, v_prec_98_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_107_ = v___x_133_;
goto v___jp_106_;
}
else
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_107_ = v___x_134_;
goto v___jp_106_;
}
}
case 2:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(1024u);
v___x_136_ = lean_nat_dec_le(v___x_135_, v_prec_98_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_114_ = v___x_137_;
goto v___jp_113_;
}
else
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_114_ = v___x_138_;
goto v___jp_113_;
}
}
default: 
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(1024u);
v___x_140_ = lean_nat_dec_le(v___x_139_, v_prec_98_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_121_ = v___x_141_;
goto v___jp_120_;
}
else
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_121_ = v___x_142_;
goto v___jp_120_;
}
}
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_101_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__1));
lean_inc(v___y_100_);
v___x_102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_102_, 0, v___y_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = 0;
v___x_104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*1, v___x_103_);
v___x_105_ = l_Repr_addAppParen(v___x_104_, v_prec_98_);
return v___x_105_;
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_108_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__3));
lean_inc(v___y_107_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___y_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
v___x_112_ = l_Repr_addAppParen(v___x_111_, v_prec_98_);
return v___x_112_;
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_115_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__5));
lean_inc(v___y_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___y_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
v___x_119_ = l_Repr_addAppParen(v___x_118_, v_prec_98_);
return v___x_119_;
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_122_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__7));
lean_inc(v___y_121_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___y_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = l_Repr_addAppParen(v___x_125_, v_prec_98_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprText_repr___boxed(lean_object* v_x_143_, lean_object* v_prec_144_){
_start:
{
uint8_t v_x_233__boxed_145_; lean_object* v_res_146_; 
v_x_233__boxed_145_ = lean_unbox(v_x_143_);
v_res_146_ = l_Std_Time_instReprText_repr(v_x_233__boxed_145_, v_prec_144_);
lean_dec(v_prec_144_);
return v_res_146_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedText_default(void){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedText(void){
_start:
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_classify(lean_object* v_num_160_){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(4u);
v___x_162_ = lean_nat_dec_lt(v_num_160_, v___x_161_);
if (v___x_162_ == 0)
{
uint8_t v___x_163_; 
v___x_163_ = lean_nat_dec_eq(v_num_160_, v___x_161_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(5u);
v___x_165_ = lean_nat_dec_eq(v_num_160_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = ((lean_object*)(l_Std_Time_Text_classify___closed__0));
return v___x_167_;
}
}
else
{
lean_object* v___x_168_; 
v___x_168_ = ((lean_object*)(l_Std_Time_Text_classify___closed__1));
return v___x_168_;
}
}
else
{
lean_object* v___x_169_; 
v___x_169_ = ((lean_object*)(l_Std_Time_Text_classify___closed__2));
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_classify___boxed(lean_object* v_num_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_Time_Text_classify(v_num_170_);
lean_dec(v_num_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprNumber_repr_spec__0(lean_object* v_a_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_nat_to_int(v_a_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Time_instReprNumber_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(11u);
v___x_188_ = lean_nat_to_int(v___x_187_);
return v___x_188_;
}
}
static lean_object* _init_l_Std_Time_instReprNumber_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__0));
v___x_191_ = lean_string_length(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_Std_Time_instReprNumber_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_obj_once(&l_Std_Time_instReprNumber_repr___redArg___closed__9, &l_Std_Time_instReprNumber_repr___redArg___closed__9_once, _init_l_Std_Time_instReprNumber_repr___redArg___closed__9);
v___x_193_ = lean_nat_to_int(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr___redArg(lean_object* v_x_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_199_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__6));
v___x_200_ = lean_obj_once(&l_Std_Time_instReprNumber_repr___redArg___closed__7, &l_Std_Time_instReprNumber_repr___redArg___closed__7_once, _init_l_Std_Time_instReprNumber_repr___redArg___closed__7);
v___x_201_ = l_Nat_reprFast(v_x_198_);
v___x_202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
v___x_203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_200_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = 0;
v___x_205_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*1, v___x_204_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_199_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_obj_once(&l_Std_Time_instReprNumber_repr___redArg___closed__10, &l_Std_Time_instReprNumber_repr___redArg___closed__10_once, _init_l_Std_Time_instReprNumber_repr___redArg___closed__10);
v___x_208_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__11));
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_206_);
v___x_210_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__12));
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_207_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*1, v___x_204_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr(lean_object* v_x_214_, lean_object* v_prec_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_Time_instReprNumber_repr___redArg(v_x_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr___boxed(lean_object* v_x_217_, lean_object* v_prec_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_Time_instReprNumber_repr(v_x_217_, v_prec_218_);
lean_dec(v_prec_218_);
return v_res_219_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedNumber_default(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_unsigned_to_nat(0u);
return v___x_222_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedNumber(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(0u);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyNumberText(lean_object* v_x_224_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(3u);
v___x_226_ = lean_nat_dec_lt(v_x_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_Time_Text_classify(v_x_224_);
lean_dec(v_x_224_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; 
v___x_228_ = lean_box(0);
return v___x_228_;
}
else
{
lean_object* v_val_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
v_val_229_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_237_ == 0)
{
v___x_231_ = v___x_227_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_val_229_);
lean_dec(v___x_227_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v_val_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v_x_224_);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx(lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(0u);
return v___x_241_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = lean_unsigned_to_nat(1u);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx___boxed(lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_Time_Fraction_ctorIdx(v_x_243_);
lean_dec(v_x_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim___redArg(lean_object* v_t_245_, lean_object* v_k_246_){
_start:
{
if (lean_obj_tag(v_t_245_) == 0)
{
return v_k_246_;
}
else
{
lean_object* v_digits_247_; lean_object* v___x_248_; 
v_digits_247_ = lean_ctor_get(v_t_245_, 0);
lean_inc(v_digits_247_);
lean_dec_ref_known(v_t_245_, 1);
v___x_248_ = lean_apply_1(v_k_246_, v_digits_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim(lean_object* v_motive_249_, lean_object* v_ctorIdx_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_k_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_251_, v_k_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim___boxed(lean_object* v_motive_255_, lean_object* v_ctorIdx_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_k_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_Time_Fraction_ctorElim(v_motive_255_, v_ctorIdx_256_, v_t_257_, v_h_258_, v_k_259_);
lean_dec(v_ctorIdx_256_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_nano_elim___redArg(lean_object* v_t_261_, lean_object* v_nano_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_261_, v_nano_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_nano_elim(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_nano_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_265_, v_nano_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_truncated_elim___redArg(lean_object* v_t_269_, lean_object* v_truncated_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_269_, v_truncated_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_truncated_elim(lean_object* v_motive_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_truncated_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_273_, v_truncated_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFraction_repr(lean_object* v_x_286_, lean_object* v_prec_287_){
_start:
{
lean_object* v___y_289_; 
if (lean_obj_tag(v_x_286_) == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1024u);
v___x_296_ = lean_nat_dec_le(v___x_295_, v_prec_287_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_289_ = v___x_297_;
goto v___jp_288_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_289_ = v___x_298_;
goto v___jp_288_;
}
}
else
{
lean_object* v_digits_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_319_; 
v_digits_299_ = lean_ctor_get(v_x_286_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_286_);
if (v_isSharedCheck_319_ == 0)
{
v___x_301_ = v_x_286_;
v_isShared_302_ = v_isSharedCheck_319_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_digits_299_);
lean_dec(v_x_286_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_319_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___y_304_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1024u);
v___x_316_ = lean_nat_dec_le(v___x_315_, v_prec_287_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_304_ = v___x_317_;
goto v___jp_303_;
}
else
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_304_ = v___x_318_;
goto v___jp_303_;
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_305_ = ((lean_object*)(l_Std_Time_instReprFraction_repr___closed__4));
v___x_306_ = l_Nat_reprFast(v_digits_299_);
if (v_isShared_302_ == 0)
{
lean_ctor_set_tag(v___x_301_, 3);
lean_ctor_set(v___x_301_, 0, v___x_306_);
v___x_308_ = v___x_301_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_314_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_305_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
lean_inc(v___y_304_);
v___x_310_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_310_, 0, v___y_304_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = 0;
v___x_312_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*1, v___x_311_);
v___x_313_ = l_Repr_addAppParen(v___x_312_, v_prec_287_);
return v___x_313_;
}
}
}
}
v___jp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_290_ = ((lean_object*)(l_Std_Time_instReprFraction_repr___closed__1));
lean_inc(v___y_289_);
v___x_291_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_291_, 0, v___y_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = 0;
v___x_293_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*1, v___x_292_);
v___x_294_ = l_Repr_addAppParen(v___x_293_, v_prec_287_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFraction_repr___boxed(lean_object* v_x_320_, lean_object* v_prec_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_Time_instReprFraction_repr(v_x_320_, v_prec_321_);
lean_dec(v_prec_321_);
return v_res_322_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFraction_default(void){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(0);
return v___x_325_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFraction(void){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_box(0);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_classify(lean_object* v_nat_329_){
_start:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(9u);
v___x_331_ = lean_nat_dec_lt(v_nat_329_, v___x_330_);
if (v___x_331_ == 0)
{
uint8_t v___x_332_; 
v___x_332_ = lean_nat_dec_eq(v_nat_329_, v___x_330_);
lean_dec(v_nat_329_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_box(0);
return v___x_333_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = ((lean_object*)(l_Std_Time_Fraction_classify___closed__0));
return v___x_334_;
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v_nat_329_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx(lean_object* v_x_337_){
_start:
{
switch(lean_obj_tag(v_x_337_))
{
case 0:
{
lean_object* v___x_338_; 
v___x_338_ = lean_unsigned_to_nat(0u);
return v___x_338_;
}
case 1:
{
lean_object* v___x_339_; 
v___x_339_ = lean_unsigned_to_nat(1u);
return v___x_339_;
}
case 2:
{
lean_object* v___x_340_; 
v___x_340_ = lean_unsigned_to_nat(2u);
return v___x_340_;
}
default: 
{
lean_object* v___x_341_; 
v___x_341_ = lean_unsigned_to_nat(3u);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx___boxed(lean_object* v_x_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_Time_Year_ctorIdx(v_x_342_);
lean_dec(v_x_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim___redArg(lean_object* v_t_344_, lean_object* v_k_345_){
_start:
{
if (lean_obj_tag(v_t_344_) == 3)
{
lean_object* v_num_346_; lean_object* v___x_347_; 
v_num_346_ = lean_ctor_get(v_t_344_, 0);
lean_inc(v_num_346_);
lean_dec_ref_known(v_t_344_, 1);
v___x_347_ = lean_apply_1(v_k_345_, v_num_346_);
return v___x_347_;
}
else
{
lean_dec(v_t_344_);
return v_k_345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim(lean_object* v_motive_348_, lean_object* v_ctorIdx_349_, lean_object* v_t_350_, lean_object* v_h_351_, lean_object* v_k_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Std_Time_Year_ctorElim___redArg(v_t_350_, v_k_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim___boxed(lean_object* v_motive_354_, lean_object* v_ctorIdx_355_, lean_object* v_t_356_, lean_object* v_h_357_, lean_object* v_k_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_Time_Year_ctorElim(v_motive_354_, v_ctorIdx_355_, v_t_356_, v_h_357_, v_k_358_);
lean_dec(v_ctorIdx_355_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_any_elim___redArg(lean_object* v_t_360_, lean_object* v_any_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_Time_Year_ctorElim___redArg(v_t_360_, v_any_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_any_elim(lean_object* v_motive_363_, lean_object* v_t_364_, lean_object* v_h_365_, lean_object* v_any_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Std_Time_Year_ctorElim___redArg(v_t_364_, v_any_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_twoDigit_elim___redArg(lean_object* v_t_368_, lean_object* v_twoDigit_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_Time_Year_ctorElim___redArg(v_t_368_, v_twoDigit_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_twoDigit_elim(lean_object* v_motive_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_twoDigit_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Std_Time_Year_ctorElim___redArg(v_t_372_, v_twoDigit_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_fourDigit_elim___redArg(lean_object* v_t_376_, lean_object* v_fourDigit_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_Time_Year_ctorElim___redArg(v_t_376_, v_fourDigit_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_fourDigit_elim(lean_object* v_motive_379_, lean_object* v_t_380_, lean_object* v_h_381_, lean_object* v_fourDigit_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_Time_Year_ctorElim___redArg(v_t_380_, v_fourDigit_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_extended_elim___redArg(lean_object* v_t_384_, lean_object* v_extended_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_Time_Year_ctorElim___redArg(v_t_384_, v_extended_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_extended_elim(lean_object* v_motive_387_, lean_object* v_t_388_, lean_object* v_h_389_, lean_object* v_extended_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Std_Time_Year_ctorElim___redArg(v_t_388_, v_extended_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprYear_repr(lean_object* v_x_407_, lean_object* v_prec_408_){
_start:
{
lean_object* v___y_410_; lean_object* v___y_417_; lean_object* v___y_424_; 
switch(lean_obj_tag(v_x_407_))
{
case 0:
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(1024u);
v___x_431_ = lean_nat_dec_le(v___x_430_, v_prec_408_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_424_ = v___x_432_;
goto v___jp_423_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_424_ = v___x_433_;
goto v___jp_423_;
}
}
case 1:
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(1024u);
v___x_435_ = lean_nat_dec_le(v___x_434_, v_prec_408_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_417_ = v___x_436_;
goto v___jp_416_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_417_ = v___x_437_;
goto v___jp_416_;
}
}
case 2:
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(1024u);
v___x_439_ = lean_nat_dec_le(v___x_438_, v_prec_408_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_410_ = v___x_440_;
goto v___jp_409_;
}
else
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_410_ = v___x_441_;
goto v___jp_409_;
}
}
default: 
{
lean_object* v_num_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_462_; 
v_num_442_ = lean_ctor_get(v_x_407_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_x_407_);
if (v_isSharedCheck_462_ == 0)
{
v___x_444_ = v_x_407_;
v_isShared_445_ = v_isSharedCheck_462_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_num_442_);
lean_dec(v_x_407_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_462_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___y_447_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(1024u);
v___x_459_ = lean_nat_dec_le(v___x_458_, v_prec_408_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
v___x_460_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_447_ = v___x_460_;
goto v___jp_446_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_447_ = v___x_461_;
goto v___jp_446_;
}
v___jp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_448_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__8));
v___x_449_ = l_Nat_reprFast(v_num_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_449_);
v___x_451_ = v___x_444_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_457_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_448_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
lean_inc(v___y_447_);
v___x_453_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_453_, 0, v___y_447_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = 0;
v___x_455_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*1, v___x_454_);
v___x_456_ = l_Repr_addAppParen(v___x_455_, v_prec_408_);
return v___x_456_;
}
}
}
}
}
v___jp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_411_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__1));
lean_inc(v___y_410_);
v___x_412_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_412_, 0, v___y_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = 0;
v___x_414_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*1, v___x_413_);
v___x_415_ = l_Repr_addAppParen(v___x_414_, v_prec_408_);
return v___x_415_;
}
v___jp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_418_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__3));
lean_inc(v___y_417_);
v___x_419_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_419_, 0, v___y_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = 0;
v___x_421_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_421_, sizeof(void*)*1, v___x_420_);
v___x_422_ = l_Repr_addAppParen(v___x_421_, v_prec_408_);
return v___x_422_;
}
v___jp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_425_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__5));
lean_inc(v___y_424_);
v___x_426_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_426_, 0, v___y_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = 0;
v___x_428_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*1, v___x_427_);
v___x_429_ = l_Repr_addAppParen(v___x_428_, v_prec_408_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprYear_repr___boxed(lean_object* v_x_463_, lean_object* v_prec_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_Time_instReprYear_repr(v_x_463_, v_prec_464_);
lean_dec(v_prec_464_);
return v_res_465_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedYear_default(void){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_box(0);
return v___x_468_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedYear(void){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lean_box(0);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_classify(lean_object* v_num_476_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_dec_eq(v_num_476_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(2u);
v___x_483_ = lean_nat_dec_eq(v_num_476_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(4u);
v___x_485_ = lean_nat_dec_eq(v_num_476_, v___x_484_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; 
v___x_486_ = lean_nat_dec_lt(v___x_484_, v_num_476_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(3u);
v___x_488_ = lean_nat_dec_eq(v_num_476_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v_num_476_);
v___x_489_ = lean_box(0);
return v___x_489_;
}
else
{
goto v___jp_477_;
}
}
else
{
goto v___jp_477_;
}
}
else
{
lean_object* v___x_490_; 
lean_dec(v_num_476_);
v___x_490_ = ((lean_object*)(l_Std_Time_Year_classify___closed__0));
return v___x_490_;
}
}
else
{
lean_object* v___x_491_; 
lean_dec(v_num_476_);
v___x_491_ = ((lean_object*)(l_Std_Time_Year_classify___closed__1));
return v___x_491_;
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v_num_476_);
v___x_492_ = ((lean_object*)(l_Std_Time_Year_classify___closed__2));
return v___x_492_;
}
v___jp_477_:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_478_, 0, v_num_476_);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx(uint8_t v_x_493_){
_start:
{
switch(v_x_493_)
{
case 0:
{
lean_object* v___x_494_; 
v___x_494_ = lean_unsigned_to_nat(0u);
return v___x_494_;
}
case 1:
{
lean_object* v___x_495_; 
v___x_495_ = lean_unsigned_to_nat(1u);
return v___x_495_;
}
default: 
{
lean_object* v___x_496_; 
v___x_496_ = lean_unsigned_to_nat(2u);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx___boxed(lean_object* v_x_497_){
_start:
{
uint8_t v_x_boxed_498_; lean_object* v_res_499_; 
v_x_boxed_498_ = lean_unbox(v_x_497_);
v_res_499_ = l_Std_Time_ZoneId_ctorIdx(v_x_boxed_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_toCtorIdx(uint8_t v_x_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_Time_ZoneId_ctorIdx(v_x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_toCtorIdx___boxed(lean_object* v_x_502_){
_start:
{
uint8_t v_x_4__boxed_503_; lean_object* v_res_504_; 
v_x_4__boxed_503_ = lean_unbox(v_x_502_);
v_res_504_ = l_Std_Time_ZoneId_toCtorIdx(v_x_4__boxed_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___redArg(lean_object* v_k_505_){
_start:
{
lean_inc(v_k_505_);
return v_k_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___redArg___boxed(lean_object* v_k_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_Time_ZoneId_ctorElim___redArg(v_k_506_);
lean_dec(v_k_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim(lean_object* v_motive_508_, lean_object* v_ctorIdx_509_, uint8_t v_t_510_, lean_object* v_h_511_, lean_object* v_k_512_){
_start:
{
lean_inc(v_k_512_);
return v_k_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___boxed(lean_object* v_motive_513_, lean_object* v_ctorIdx_514_, lean_object* v_t_515_, lean_object* v_h_516_, lean_object* v_k_517_){
_start:
{
uint8_t v_t_boxed_518_; lean_object* v_res_519_; 
v_t_boxed_518_ = lean_unbox(v_t_515_);
v_res_519_ = l_Std_Time_ZoneId_ctorElim(v_motive_513_, v_ctorIdx_514_, v_t_boxed_518_, v_h_516_, v_k_517_);
lean_dec(v_k_517_);
lean_dec(v_ctorIdx_514_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg(lean_object* v_unknown_520_){
_start:
{
lean_inc(v_unknown_520_);
return v_unknown_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg___boxed(lean_object* v_unknown_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_Time_ZoneId_unknown_elim___redArg(v_unknown_521_);
lean_dec(v_unknown_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim(lean_object* v_motive_523_, uint8_t v_t_524_, lean_object* v_h_525_, lean_object* v_unknown_526_){
_start:
{
lean_inc(v_unknown_526_);
return v_unknown_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___boxed(lean_object* v_motive_527_, lean_object* v_t_528_, lean_object* v_h_529_, lean_object* v_unknown_530_){
_start:
{
uint8_t v_t_boxed_531_; lean_object* v_res_532_; 
v_t_boxed_531_ = lean_unbox(v_t_528_);
v_res_532_ = l_Std_Time_ZoneId_unknown_elim(v_motive_527_, v_t_boxed_531_, v_h_529_, v_unknown_530_);
lean_dec(v_unknown_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg(lean_object* v_short_533_){
_start:
{
lean_inc(v_short_533_);
return v_short_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg___boxed(lean_object* v_short_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_Time_ZoneId_short_elim___redArg(v_short_534_);
lean_dec(v_short_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim(lean_object* v_motive_536_, uint8_t v_t_537_, lean_object* v_h_538_, lean_object* v_short_539_){
_start:
{
lean_inc(v_short_539_);
return v_short_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___boxed(lean_object* v_motive_540_, lean_object* v_t_541_, lean_object* v_h_542_, lean_object* v_short_543_){
_start:
{
uint8_t v_t_boxed_544_; lean_object* v_res_545_; 
v_t_boxed_544_ = lean_unbox(v_t_541_);
v_res_545_ = l_Std_Time_ZoneId_short_elim(v_motive_540_, v_t_boxed_544_, v_h_542_, v_short_543_);
lean_dec(v_short_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg(lean_object* v_full_546_){
_start:
{
lean_inc(v_full_546_);
return v_full_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg___boxed(lean_object* v_full_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Time_ZoneId_full_elim___redArg(v_full_547_);
lean_dec(v_full_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim(lean_object* v_motive_549_, uint8_t v_t_550_, lean_object* v_h_551_, lean_object* v_full_552_){
_start:
{
lean_inc(v_full_552_);
return v_full_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___boxed(lean_object* v_motive_553_, lean_object* v_t_554_, lean_object* v_h_555_, lean_object* v_full_556_){
_start:
{
uint8_t v_t_boxed_557_; lean_object* v_res_558_; 
v_t_boxed_557_ = lean_unbox(v_t_554_);
v_res_558_ = l_Std_Time_ZoneId_full_elim(v_motive_553_, v_t_boxed_557_, v_h_555_, v_full_556_);
lean_dec(v_full_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr(uint8_t v_x_568_, lean_object* v_prec_569_){
_start:
{
lean_object* v___y_571_; lean_object* v___y_578_; lean_object* v___y_585_; 
switch(v_x_568_)
{
case 0:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(1024u);
v___x_592_ = lean_nat_dec_le(v___x_591_, v_prec_569_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_571_ = v___x_593_;
goto v___jp_570_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_571_ = v___x_594_;
goto v___jp_570_;
}
}
case 1:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(1024u);
v___x_596_ = lean_nat_dec_le(v___x_595_, v_prec_569_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_578_ = v___x_597_;
goto v___jp_577_;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_578_ = v___x_598_;
goto v___jp_577_;
}
}
default: 
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(1024u);
v___x_600_ = lean_nat_dec_le(v___x_599_, v_prec_569_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_585_ = v___x_601_;
goto v___jp_584_;
}
else
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_585_ = v___x_602_;
goto v___jp_584_;
}
}
}
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_572_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__1));
lean_inc(v___y_571_);
v___x_573_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_573_, 0, v___y_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = 0;
v___x_575_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set_uint8(v___x_575_, sizeof(void*)*1, v___x_574_);
v___x_576_ = l_Repr_addAppParen(v___x_575_, v_prec_569_);
return v___x_576_;
}
v___jp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_579_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__3));
lean_inc(v___y_578_);
v___x_580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_580_, 0, v___y_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = 0;
v___x_582_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*1, v___x_581_);
v___x_583_ = l_Repr_addAppParen(v___x_582_, v_prec_569_);
return v___x_583_;
}
v___jp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_586_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__5));
lean_inc(v___y_585_);
v___x_587_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_587_, 0, v___y_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = 0;
v___x_589_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set_uint8(v___x_589_, sizeof(void*)*1, v___x_588_);
v___x_590_ = l_Repr_addAppParen(v___x_589_, v_prec_569_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr___boxed(lean_object* v_x_603_, lean_object* v_prec_604_){
_start:
{
uint8_t v_x_173__boxed_605_; lean_object* v_res_606_; 
v_x_173__boxed_605_ = lean_unbox(v_x_603_);
v_res_606_ = l_Std_Time_instReprZoneId_repr(v_x_173__boxed_605_, v_prec_604_);
lean_dec(v_prec_604_);
return v_res_606_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneId_default(void){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = 0;
return v___x_609_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneId(void){
_start:
{
uint8_t v___x_610_; 
v___x_610_ = 0;
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify(lean_object* v_num_620_){
_start:
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_dec_eq(v_num_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(2u);
v___x_624_ = lean_nat_dec_eq(v_num_620_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = lean_unsigned_to_nat(4u);
v___x_626_ = lean_nat_dec_eq(v_num_620_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_box(0);
return v___x_627_;
}
else
{
lean_object* v___x_628_; 
v___x_628_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__0));
return v___x_628_;
}
}
else
{
lean_object* v___x_629_; 
v___x_629_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__1));
return v___x_629_;
}
}
else
{
lean_object* v___x_630_; 
v___x_630_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__2));
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify___boxed(lean_object* v_num_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_Time_ZoneId_classify(v_num_631_);
lean_dec(v_num_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx(uint8_t v_x_633_){
_start:
{
if (v_x_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = lean_unsigned_to_nat(0u);
return v___x_634_;
}
else
{
lean_object* v___x_635_; 
v___x_635_ = lean_unsigned_to_nat(1u);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx___boxed(lean_object* v_x_636_){
_start:
{
uint8_t v_x_boxed_637_; lean_object* v_res_638_; 
v_x_boxed_637_ = lean_unbox(v_x_636_);
v_res_638_ = l_Std_Time_ZoneName_ctorIdx(v_x_boxed_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_toCtorIdx(uint8_t v_x_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_Time_ZoneName_ctorIdx(v_x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_toCtorIdx___boxed(lean_object* v_x_641_){
_start:
{
uint8_t v_x_4__boxed_642_; lean_object* v_res_643_; 
v_x_4__boxed_642_ = lean_unbox(v_x_641_);
v_res_643_ = l_Std_Time_ZoneName_toCtorIdx(v_x_4__boxed_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg(lean_object* v_k_644_){
_start:
{
lean_inc(v_k_644_);
return v_k_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg___boxed(lean_object* v_k_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_Time_ZoneName_ctorElim___redArg(v_k_645_);
lean_dec(v_k_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim(lean_object* v_motive_647_, lean_object* v_ctorIdx_648_, uint8_t v_t_649_, lean_object* v_h_650_, lean_object* v_k_651_){
_start:
{
lean_inc(v_k_651_);
return v_k_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___boxed(lean_object* v_motive_652_, lean_object* v_ctorIdx_653_, lean_object* v_t_654_, lean_object* v_h_655_, lean_object* v_k_656_){
_start:
{
uint8_t v_t_boxed_657_; lean_object* v_res_658_; 
v_t_boxed_657_ = lean_unbox(v_t_654_);
v_res_658_ = l_Std_Time_ZoneName_ctorElim(v_motive_652_, v_ctorIdx_653_, v_t_boxed_657_, v_h_655_, v_k_656_);
lean_dec(v_k_656_);
lean_dec(v_ctorIdx_653_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg(lean_object* v_short_659_){
_start:
{
lean_inc(v_short_659_);
return v_short_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg___boxed(lean_object* v_short_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_Time_ZoneName_short_elim___redArg(v_short_660_);
lean_dec(v_short_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim(lean_object* v_motive_662_, uint8_t v_t_663_, lean_object* v_h_664_, lean_object* v_short_665_){
_start:
{
lean_inc(v_short_665_);
return v_short_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___boxed(lean_object* v_motive_666_, lean_object* v_t_667_, lean_object* v_h_668_, lean_object* v_short_669_){
_start:
{
uint8_t v_t_boxed_670_; lean_object* v_res_671_; 
v_t_boxed_670_ = lean_unbox(v_t_667_);
v_res_671_ = l_Std_Time_ZoneName_short_elim(v_motive_666_, v_t_boxed_670_, v_h_668_, v_short_669_);
lean_dec(v_short_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg(lean_object* v_full_672_){
_start:
{
lean_inc(v_full_672_);
return v_full_672_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg___boxed(lean_object* v_full_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_Time_ZoneName_full_elim___redArg(v_full_673_);
lean_dec(v_full_673_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim(lean_object* v_motive_675_, uint8_t v_t_676_, lean_object* v_h_677_, lean_object* v_full_678_){
_start:
{
lean_inc(v_full_678_);
return v_full_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___boxed(lean_object* v_motive_679_, lean_object* v_t_680_, lean_object* v_h_681_, lean_object* v_full_682_){
_start:
{
uint8_t v_t_boxed_683_; lean_object* v_res_684_; 
v_t_boxed_683_ = lean_unbox(v_t_680_);
v_res_684_ = l_Std_Time_ZoneName_full_elim(v_motive_679_, v_t_boxed_683_, v_h_681_, v_full_682_);
lean_dec(v_full_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr(uint8_t v_x_691_, lean_object* v_prec_692_){
_start:
{
lean_object* v___y_694_; lean_object* v___y_701_; 
if (v_x_691_ == 0)
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(1024u);
v___x_708_ = lean_nat_dec_le(v___x_707_, v_prec_692_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_694_ = v___x_709_;
goto v___jp_693_;
}
else
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_694_ = v___x_710_;
goto v___jp_693_;
}
}
else
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = lean_unsigned_to_nat(1024u);
v___x_712_ = lean_nat_dec_le(v___x_711_, v_prec_692_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_701_ = v___x_713_;
goto v___jp_700_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_701_ = v___x_714_;
goto v___jp_700_;
}
}
v___jp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_695_ = ((lean_object*)(l_Std_Time_instReprZoneName_repr___closed__1));
lean_inc(v___y_694_);
v___x_696_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_696_, 0, v___y_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = 0;
v___x_698_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*1, v___x_697_);
v___x_699_ = l_Repr_addAppParen(v___x_698_, v_prec_692_);
return v___x_699_;
}
v___jp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_702_ = ((lean_object*)(l_Std_Time_instReprZoneName_repr___closed__3));
lean_inc(v___y_701_);
v___x_703_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_703_, 0, v___y_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = 0;
v___x_705_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*1, v___x_704_);
v___x_706_ = l_Repr_addAppParen(v___x_705_, v_prec_692_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr___boxed(lean_object* v_x_715_, lean_object* v_prec_716_){
_start:
{
uint8_t v_x_117__boxed_717_; lean_object* v_res_718_; 
v_x_117__boxed_717_ = lean_unbox(v_x_715_);
v_res_718_ = l_Std_Time_instReprZoneName_repr(v_x_117__boxed_717_, v_prec_716_);
lean_dec(v_prec_716_);
return v_res_718_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneName_default(void){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = 0;
return v___x_721_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneName(void){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = 0;
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify(uint32_t v_letter_729_, lean_object* v_num_730_){
_start:
{
uint32_t v___x_731_; uint8_t v___x_732_; 
v___x_731_ = 122;
v___x_732_ = lean_uint32_dec_eq(v_letter_729_, v___x_731_);
if (v___x_732_ == 0)
{
uint32_t v___x_733_; uint8_t v___x_734_; 
v___x_733_ = 118;
v___x_734_ = lean_uint32_dec_eq(v_letter_729_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; 
v___x_735_ = lean_box(0);
return v___x_735_;
}
else
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_dec_eq(v_num_730_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(4u);
v___x_739_ = lean_nat_dec_eq(v_num_730_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_box(0);
return v___x_740_;
}
else
{
lean_object* v___x_741_; 
v___x_741_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__0));
return v___x_741_;
}
}
else
{
lean_object* v___x_742_; 
v___x_742_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__1));
return v___x_742_;
}
}
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(4u);
v___x_744_ = lean_nat_dec_lt(v_num_730_, v___x_743_);
if (v___x_744_ == 0)
{
uint8_t v___x_745_; 
v___x_745_ = lean_nat_dec_eq(v_num_730_, v___x_743_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = lean_box(0);
return v___x_746_;
}
else
{
lean_object* v___x_747_; 
v___x_747_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__0));
return v___x_747_;
}
}
else
{
lean_object* v___x_748_; 
v___x_748_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__1));
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify___boxed(lean_object* v_letter_749_, lean_object* v_num_750_){
_start:
{
uint32_t v_letter_boxed_751_; lean_object* v_res_752_; 
v_letter_boxed_751_ = lean_unbox_uint32(v_letter_749_);
lean_dec(v_letter_749_);
v_res_752_ = l_Std_Time_ZoneName_classify(v_letter_boxed_751_, v_num_750_);
lean_dec(v_num_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx(uint8_t v_x_753_){
_start:
{
switch(v_x_753_)
{
case 0:
{
lean_object* v___x_754_; 
v___x_754_ = lean_unsigned_to_nat(0u);
return v___x_754_;
}
case 1:
{
lean_object* v___x_755_; 
v___x_755_ = lean_unsigned_to_nat(1u);
return v___x_755_;
}
case 2:
{
lean_object* v___x_756_; 
v___x_756_ = lean_unsigned_to_nat(2u);
return v___x_756_;
}
case 3:
{
lean_object* v___x_757_; 
v___x_757_ = lean_unsigned_to_nat(3u);
return v___x_757_;
}
default: 
{
lean_object* v___x_758_; 
v___x_758_ = lean_unsigned_to_nat(4u);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx___boxed(lean_object* v_x_759_){
_start:
{
uint8_t v_x_boxed_760_; lean_object* v_res_761_; 
v_x_boxed_760_ = lean_unbox(v_x_759_);
v_res_761_ = l_Std_Time_OffsetX_ctorIdx(v_x_boxed_760_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_toCtorIdx(uint8_t v_x_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_Time_OffsetX_ctorIdx(v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_toCtorIdx___boxed(lean_object* v_x_764_){
_start:
{
uint8_t v_x_4__boxed_765_; lean_object* v_res_766_; 
v_x_4__boxed_765_ = lean_unbox(v_x_764_);
v_res_766_ = l_Std_Time_OffsetX_toCtorIdx(v_x_4__boxed_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg(lean_object* v_k_767_){
_start:
{
lean_inc(v_k_767_);
return v_k_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg___boxed(lean_object* v_k_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_Time_OffsetX_ctorElim___redArg(v_k_768_);
lean_dec(v_k_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim(lean_object* v_motive_770_, lean_object* v_ctorIdx_771_, uint8_t v_t_772_, lean_object* v_h_773_, lean_object* v_k_774_){
_start:
{
lean_inc(v_k_774_);
return v_k_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___boxed(lean_object* v_motive_775_, lean_object* v_ctorIdx_776_, lean_object* v_t_777_, lean_object* v_h_778_, lean_object* v_k_779_){
_start:
{
uint8_t v_t_boxed_780_; lean_object* v_res_781_; 
v_t_boxed_780_ = lean_unbox(v_t_777_);
v_res_781_ = l_Std_Time_OffsetX_ctorElim(v_motive_775_, v_ctorIdx_776_, v_t_boxed_780_, v_h_778_, v_k_779_);
lean_dec(v_k_779_);
lean_dec(v_ctorIdx_776_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg(lean_object* v_hour_782_){
_start:
{
lean_inc(v_hour_782_);
return v_hour_782_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg___boxed(lean_object* v_hour_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_Time_OffsetX_hour_elim___redArg(v_hour_783_);
lean_dec(v_hour_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim(lean_object* v_motive_785_, uint8_t v_t_786_, lean_object* v_h_787_, lean_object* v_hour_788_){
_start:
{
lean_inc(v_hour_788_);
return v_hour_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___boxed(lean_object* v_motive_789_, lean_object* v_t_790_, lean_object* v_h_791_, lean_object* v_hour_792_){
_start:
{
uint8_t v_t_boxed_793_; lean_object* v_res_794_; 
v_t_boxed_793_ = lean_unbox(v_t_790_);
v_res_794_ = l_Std_Time_OffsetX_hour_elim(v_motive_789_, v_t_boxed_793_, v_h_791_, v_hour_792_);
lean_dec(v_hour_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg(lean_object* v_hourMinute_795_){
_start:
{
lean_inc(v_hourMinute_795_);
return v_hourMinute_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg___boxed(lean_object* v_hourMinute_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_Time_OffsetX_hourMinute_elim___redArg(v_hourMinute_796_);
lean_dec(v_hourMinute_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim(lean_object* v_motive_798_, uint8_t v_t_799_, lean_object* v_h_800_, lean_object* v_hourMinute_801_){
_start:
{
lean_inc(v_hourMinute_801_);
return v_hourMinute_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___boxed(lean_object* v_motive_802_, lean_object* v_t_803_, lean_object* v_h_804_, lean_object* v_hourMinute_805_){
_start:
{
uint8_t v_t_boxed_806_; lean_object* v_res_807_; 
v_t_boxed_806_ = lean_unbox(v_t_803_);
v_res_807_ = l_Std_Time_OffsetX_hourMinute_elim(v_motive_802_, v_t_boxed_806_, v_h_804_, v_hourMinute_805_);
lean_dec(v_hourMinute_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(lean_object* v_hourMinuteColon_808_){
_start:
{
lean_inc(v_hourMinuteColon_808_);
return v_hourMinuteColon_808_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg___boxed(lean_object* v_hourMinuteColon_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(v_hourMinuteColon_809_);
lean_dec(v_hourMinuteColon_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim(lean_object* v_motive_811_, uint8_t v_t_812_, lean_object* v_h_813_, lean_object* v_hourMinuteColon_814_){
_start:
{
lean_inc(v_hourMinuteColon_814_);
return v_hourMinuteColon_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___boxed(lean_object* v_motive_815_, lean_object* v_t_816_, lean_object* v_h_817_, lean_object* v_hourMinuteColon_818_){
_start:
{
uint8_t v_t_boxed_819_; lean_object* v_res_820_; 
v_t_boxed_819_ = lean_unbox(v_t_816_);
v_res_820_ = l_Std_Time_OffsetX_hourMinuteColon_elim(v_motive_815_, v_t_boxed_819_, v_h_817_, v_hourMinuteColon_818_);
lean_dec(v_hourMinuteColon_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(lean_object* v_hourMinuteSecond_821_){
_start:
{
lean_inc(v_hourMinuteSecond_821_);
return v_hourMinuteSecond_821_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg___boxed(lean_object* v_hourMinuteSecond_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(v_hourMinuteSecond_822_);
lean_dec(v_hourMinuteSecond_822_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim(lean_object* v_motive_824_, uint8_t v_t_825_, lean_object* v_h_826_, lean_object* v_hourMinuteSecond_827_){
_start:
{
lean_inc(v_hourMinuteSecond_827_);
return v_hourMinuteSecond_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___boxed(lean_object* v_motive_828_, lean_object* v_t_829_, lean_object* v_h_830_, lean_object* v_hourMinuteSecond_831_){
_start:
{
uint8_t v_t_boxed_832_; lean_object* v_res_833_; 
v_t_boxed_832_ = lean_unbox(v_t_829_);
v_res_833_ = l_Std_Time_OffsetX_hourMinuteSecond_elim(v_motive_828_, v_t_boxed_832_, v_h_830_, v_hourMinuteSecond_831_);
lean_dec(v_hourMinuteSecond_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(lean_object* v_hourMinuteSecondColon_834_){
_start:
{
lean_inc(v_hourMinuteSecondColon_834_);
return v_hourMinuteSecondColon_834_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg___boxed(lean_object* v_hourMinuteSecondColon_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(v_hourMinuteSecondColon_835_);
lean_dec(v_hourMinuteSecondColon_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim(lean_object* v_motive_837_, uint8_t v_t_838_, lean_object* v_h_839_, lean_object* v_hourMinuteSecondColon_840_){
_start:
{
lean_inc(v_hourMinuteSecondColon_840_);
return v_hourMinuteSecondColon_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___boxed(lean_object* v_motive_841_, lean_object* v_t_842_, lean_object* v_h_843_, lean_object* v_hourMinuteSecondColon_844_){
_start:
{
uint8_t v_t_boxed_845_; lean_object* v_res_846_; 
v_t_boxed_845_ = lean_unbox(v_t_842_);
v_res_846_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim(v_motive_841_, v_t_boxed_845_, v_h_843_, v_hourMinuteSecondColon_844_);
lean_dec(v_hourMinuteSecondColon_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr(uint8_t v_x_862_, lean_object* v_prec_863_){
_start:
{
lean_object* v___y_865_; lean_object* v___y_872_; lean_object* v___y_879_; lean_object* v___y_886_; lean_object* v___y_893_; 
switch(v_x_862_)
{
case 0:
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_unsigned_to_nat(1024u);
v___x_900_ = lean_nat_dec_le(v___x_899_, v_prec_863_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
v___x_901_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_865_ = v___x_901_;
goto v___jp_864_;
}
else
{
lean_object* v___x_902_; 
v___x_902_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_865_ = v___x_902_;
goto v___jp_864_;
}
}
case 1:
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(1024u);
v___x_904_ = lean_nat_dec_le(v___x_903_, v_prec_863_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
v___x_905_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_872_ = v___x_905_;
goto v___jp_871_;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_872_ = v___x_906_;
goto v___jp_871_;
}
}
case 2:
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_unsigned_to_nat(1024u);
v___x_908_ = lean_nat_dec_le(v___x_907_, v_prec_863_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_879_ = v___x_909_;
goto v___jp_878_;
}
else
{
lean_object* v___x_910_; 
v___x_910_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_879_ = v___x_910_;
goto v___jp_878_;
}
}
case 3:
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(1024u);
v___x_912_ = lean_nat_dec_le(v___x_911_, v_prec_863_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
v___x_913_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_886_ = v___x_913_;
goto v___jp_885_;
}
else
{
lean_object* v___x_914_; 
v___x_914_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_886_ = v___x_914_;
goto v___jp_885_;
}
}
default: 
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = lean_unsigned_to_nat(1024u);
v___x_916_ = lean_nat_dec_le(v___x_915_, v_prec_863_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
v___x_917_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_893_ = v___x_917_;
goto v___jp_892_;
}
else
{
lean_object* v___x_918_; 
v___x_918_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_893_ = v___x_918_;
goto v___jp_892_;
}
}
}
v___jp_864_:
{
lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_866_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__1));
lean_inc(v___y_865_);
v___x_867_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_867_, 0, v___y_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = 0;
v___x_869_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*1, v___x_868_);
v___x_870_ = l_Repr_addAppParen(v___x_869_, v_prec_863_);
return v___x_870_;
}
v___jp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_873_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__3));
lean_inc(v___y_872_);
v___x_874_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_874_, 0, v___y_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = 0;
v___x_876_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*1, v___x_875_);
v___x_877_ = l_Repr_addAppParen(v___x_876_, v_prec_863_);
return v___x_877_;
}
v___jp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_880_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__5));
lean_inc(v___y_879_);
v___x_881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_881_, 0, v___y_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = 0;
v___x_883_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1, v___x_882_);
v___x_884_ = l_Repr_addAppParen(v___x_883_, v_prec_863_);
return v___x_884_;
}
v___jp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_887_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__7));
lean_inc(v___y_886_);
v___x_888_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_888_, 0, v___y_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = 0;
v___x_890_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*1, v___x_889_);
v___x_891_ = l_Repr_addAppParen(v___x_890_, v_prec_863_);
return v___x_891_;
}
v___jp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_894_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__9));
lean_inc(v___y_893_);
v___x_895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_895_, 0, v___y_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = 0;
v___x_897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1, v___x_896_);
v___x_898_ = l_Repr_addAppParen(v___x_897_, v_prec_863_);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr___boxed(lean_object* v_x_919_, lean_object* v_prec_920_){
_start:
{
uint8_t v_x_285__boxed_921_; lean_object* v_res_922_; 
v_x_285__boxed_921_ = lean_unbox(v_x_919_);
v_res_922_ = l_Std_Time_instReprOffsetX_repr(v_x_285__boxed_921_, v_prec_920_);
lean_dec(v_prec_920_);
return v_res_922_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetX_default(void){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = 0;
return v___x_925_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetX(void){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = 0;
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify(lean_object* v_num_942_){
_start:
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_dec_eq(v_num_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_945_ = lean_unsigned_to_nat(2u);
v___x_946_ = lean_nat_dec_eq(v_num_942_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = lean_unsigned_to_nat(3u);
v___x_948_ = lean_nat_dec_eq(v_num_942_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_unsigned_to_nat(4u);
v___x_950_ = lean_nat_dec_eq(v_num_942_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_unsigned_to_nat(5u);
v___x_952_ = lean_nat_dec_eq(v_num_942_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
v___x_953_ = lean_box(0);
return v___x_953_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__0));
return v___x_954_;
}
}
else
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__1));
return v___x_955_;
}
}
else
{
lean_object* v___x_956_; 
v___x_956_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__2));
return v___x_956_;
}
}
else
{
lean_object* v___x_957_; 
v___x_957_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__3));
return v___x_957_;
}
}
else
{
lean_object* v___x_958_; 
v___x_958_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__4));
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify___boxed(lean_object* v_num_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Std_Time_OffsetX_classify(v_num_959_);
lean_dec(v_num_959_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx(uint8_t v_x_961_){
_start:
{
if (v_x_961_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_unsigned_to_nat(0u);
return v___x_962_;
}
else
{
lean_object* v___x_963_; 
v___x_963_ = lean_unsigned_to_nat(1u);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx___boxed(lean_object* v_x_964_){
_start:
{
uint8_t v_x_boxed_965_; lean_object* v_res_966_; 
v_x_boxed_965_ = lean_unbox(v_x_964_);
v_res_966_ = l_Std_Time_OffsetO_ctorIdx(v_x_boxed_965_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_toCtorIdx(uint8_t v_x_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_Time_OffsetO_ctorIdx(v_x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_toCtorIdx___boxed(lean_object* v_x_969_){
_start:
{
uint8_t v_x_4__boxed_970_; lean_object* v_res_971_; 
v_x_4__boxed_970_ = lean_unbox(v_x_969_);
v_res_971_ = l_Std_Time_OffsetO_toCtorIdx(v_x_4__boxed_970_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg(lean_object* v_k_972_){
_start:
{
lean_inc(v_k_972_);
return v_k_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg___boxed(lean_object* v_k_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_Time_OffsetO_ctorElim___redArg(v_k_973_);
lean_dec(v_k_973_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim(lean_object* v_motive_975_, lean_object* v_ctorIdx_976_, uint8_t v_t_977_, lean_object* v_h_978_, lean_object* v_k_979_){
_start:
{
lean_inc(v_k_979_);
return v_k_979_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___boxed(lean_object* v_motive_980_, lean_object* v_ctorIdx_981_, lean_object* v_t_982_, lean_object* v_h_983_, lean_object* v_k_984_){
_start:
{
uint8_t v_t_boxed_985_; lean_object* v_res_986_; 
v_t_boxed_985_ = lean_unbox(v_t_982_);
v_res_986_ = l_Std_Time_OffsetO_ctorElim(v_motive_980_, v_ctorIdx_981_, v_t_boxed_985_, v_h_983_, v_k_984_);
lean_dec(v_k_984_);
lean_dec(v_ctorIdx_981_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg(lean_object* v_short_987_){
_start:
{
lean_inc(v_short_987_);
return v_short_987_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg___boxed(lean_object* v_short_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_Time_OffsetO_short_elim___redArg(v_short_988_);
lean_dec(v_short_988_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim(lean_object* v_motive_990_, uint8_t v_t_991_, lean_object* v_h_992_, lean_object* v_short_993_){
_start:
{
lean_inc(v_short_993_);
return v_short_993_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___boxed(lean_object* v_motive_994_, lean_object* v_t_995_, lean_object* v_h_996_, lean_object* v_short_997_){
_start:
{
uint8_t v_t_boxed_998_; lean_object* v_res_999_; 
v_t_boxed_998_ = lean_unbox(v_t_995_);
v_res_999_ = l_Std_Time_OffsetO_short_elim(v_motive_994_, v_t_boxed_998_, v_h_996_, v_short_997_);
lean_dec(v_short_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg(lean_object* v_full_1000_){
_start:
{
lean_inc(v_full_1000_);
return v_full_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg___boxed(lean_object* v_full_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_Time_OffsetO_full_elim___redArg(v_full_1001_);
lean_dec(v_full_1001_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim(lean_object* v_motive_1003_, uint8_t v_t_1004_, lean_object* v_h_1005_, lean_object* v_full_1006_){
_start:
{
lean_inc(v_full_1006_);
return v_full_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___boxed(lean_object* v_motive_1007_, lean_object* v_t_1008_, lean_object* v_h_1009_, lean_object* v_full_1010_){
_start:
{
uint8_t v_t_boxed_1011_; lean_object* v_res_1012_; 
v_t_boxed_1011_ = lean_unbox(v_t_1008_);
v_res_1012_ = l_Std_Time_OffsetO_full_elim(v_motive_1007_, v_t_boxed_1011_, v_h_1009_, v_full_1010_);
lean_dec(v_full_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr(uint8_t v_x_1019_, lean_object* v_prec_1020_){
_start:
{
lean_object* v___y_1022_; lean_object* v___y_1029_; 
if (v_x_1019_ == 0)
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(1024u);
v___x_1036_ = lean_nat_dec_le(v___x_1035_, v_prec_1020_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1022_ = v___x_1037_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1022_ = v___x_1038_;
goto v___jp_1021_;
}
}
else
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(1024u);
v___x_1040_ = lean_nat_dec_le(v___x_1039_, v_prec_1020_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1029_ = v___x_1041_;
goto v___jp_1028_;
}
else
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1029_ = v___x_1042_;
goto v___jp_1028_;
}
}
v___jp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1023_ = ((lean_object*)(l_Std_Time_instReprOffsetO_repr___closed__1));
lean_inc(v___y_1022_);
v___x_1024_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___y_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = 0;
v___x_1026_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set_uint8(v___x_1026_, sizeof(void*)*1, v___x_1025_);
v___x_1027_ = l_Repr_addAppParen(v___x_1026_, v_prec_1020_);
return v___x_1027_;
}
v___jp_1028_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1030_ = ((lean_object*)(l_Std_Time_instReprOffsetO_repr___closed__3));
lean_inc(v___y_1029_);
v___x_1031_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___y_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = 0;
v___x_1033_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set_uint8(v___x_1033_, sizeof(void*)*1, v___x_1032_);
v___x_1034_ = l_Repr_addAppParen(v___x_1033_, v_prec_1020_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr___boxed(lean_object* v_x_1043_, lean_object* v_prec_1044_){
_start:
{
uint8_t v_x_117__boxed_1045_; lean_object* v_res_1046_; 
v_x_117__boxed_1045_ = lean_unbox(v_x_1043_);
v_res_1046_ = l_Std_Time_instReprOffsetO_repr(v_x_117__boxed_1045_, v_prec_1044_);
lean_dec(v_prec_1044_);
return v_res_1046_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetO_default(void){
_start:
{
uint8_t v___x_1049_; 
v___x_1049_ = 0;
return v___x_1049_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetO(void){
_start:
{
uint8_t v___x_1050_; 
v___x_1050_ = 0;
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify(lean_object* v_num_1057_){
_start:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_unsigned_to_nat(1u);
v___x_1059_ = lean_nat_dec_eq(v_num_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(4u);
v___x_1061_ = lean_nat_dec_eq(v_num_1057_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_box(0);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; 
v___x_1063_ = ((lean_object*)(l_Std_Time_OffsetO_classify___closed__0));
return v___x_1063_;
}
}
else
{
lean_object* v___x_1064_; 
v___x_1064_ = ((lean_object*)(l_Std_Time_OffsetO_classify___closed__1));
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify___boxed(lean_object* v_num_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_Time_OffsetO_classify(v_num_1065_);
lean_dec(v_num_1065_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx(uint8_t v_x_1067_){
_start:
{
switch(v_x_1067_)
{
case 0:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_unsigned_to_nat(0u);
return v___x_1068_;
}
case 1:
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_unsigned_to_nat(1u);
return v___x_1069_;
}
default: 
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_unsigned_to_nat(2u);
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx___boxed(lean_object* v_x_1071_){
_start:
{
uint8_t v_x_boxed_1072_; lean_object* v_res_1073_; 
v_x_boxed_1072_ = lean_unbox(v_x_1071_);
v_res_1073_ = l_Std_Time_OffsetZ_ctorIdx(v_x_boxed_1072_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_toCtorIdx(uint8_t v_x_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_Time_OffsetZ_ctorIdx(v_x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_toCtorIdx___boxed(lean_object* v_x_1076_){
_start:
{
uint8_t v_x_4__boxed_1077_; lean_object* v_res_1078_; 
v_x_4__boxed_1077_ = lean_unbox(v_x_1076_);
v_res_1078_ = l_Std_Time_OffsetZ_toCtorIdx(v_x_4__boxed_1077_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg(lean_object* v_k_1079_){
_start:
{
lean_inc(v_k_1079_);
return v_k_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg___boxed(lean_object* v_k_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_Time_OffsetZ_ctorElim___redArg(v_k_1080_);
lean_dec(v_k_1080_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim(lean_object* v_motive_1082_, lean_object* v_ctorIdx_1083_, uint8_t v_t_1084_, lean_object* v_h_1085_, lean_object* v_k_1086_){
_start:
{
lean_inc(v_k_1086_);
return v_k_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___boxed(lean_object* v_motive_1087_, lean_object* v_ctorIdx_1088_, lean_object* v_t_1089_, lean_object* v_h_1090_, lean_object* v_k_1091_){
_start:
{
uint8_t v_t_boxed_1092_; lean_object* v_res_1093_; 
v_t_boxed_1092_ = lean_unbox(v_t_1089_);
v_res_1093_ = l_Std_Time_OffsetZ_ctorElim(v_motive_1087_, v_ctorIdx_1088_, v_t_boxed_1092_, v_h_1090_, v_k_1091_);
lean_dec(v_k_1091_);
lean_dec(v_ctorIdx_1088_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg(lean_object* v_hourMinute_1094_){
_start:
{
lean_inc(v_hourMinute_1094_);
return v_hourMinute_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg___boxed(lean_object* v_hourMinute_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Std_Time_OffsetZ_hourMinute_elim___redArg(v_hourMinute_1095_);
lean_dec(v_hourMinute_1095_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim(lean_object* v_motive_1097_, uint8_t v_t_1098_, lean_object* v_h_1099_, lean_object* v_hourMinute_1100_){
_start:
{
lean_inc(v_hourMinute_1100_);
return v_hourMinute_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___boxed(lean_object* v_motive_1101_, lean_object* v_t_1102_, lean_object* v_h_1103_, lean_object* v_hourMinute_1104_){
_start:
{
uint8_t v_t_boxed_1105_; lean_object* v_res_1106_; 
v_t_boxed_1105_ = lean_unbox(v_t_1102_);
v_res_1106_ = l_Std_Time_OffsetZ_hourMinute_elim(v_motive_1101_, v_t_boxed_1105_, v_h_1103_, v_hourMinute_1104_);
lean_dec(v_hourMinute_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg(lean_object* v_full_1107_){
_start:
{
lean_inc(v_full_1107_);
return v_full_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg___boxed(lean_object* v_full_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_Time_OffsetZ_full_elim___redArg(v_full_1108_);
lean_dec(v_full_1108_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim(lean_object* v_motive_1110_, uint8_t v_t_1111_, lean_object* v_h_1112_, lean_object* v_full_1113_){
_start:
{
lean_inc(v_full_1113_);
return v_full_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___boxed(lean_object* v_motive_1114_, lean_object* v_t_1115_, lean_object* v_h_1116_, lean_object* v_full_1117_){
_start:
{
uint8_t v_t_boxed_1118_; lean_object* v_res_1119_; 
v_t_boxed_1118_ = lean_unbox(v_t_1115_);
v_res_1119_ = l_Std_Time_OffsetZ_full_elim(v_motive_1114_, v_t_boxed_1118_, v_h_1116_, v_full_1117_);
lean_dec(v_full_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(lean_object* v_hourMinuteSecondColon_1120_){
_start:
{
lean_inc(v_hourMinuteSecondColon_1120_);
return v_hourMinuteSecondColon_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg___boxed(lean_object* v_hourMinuteSecondColon_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(v_hourMinuteSecondColon_1121_);
lean_dec(v_hourMinuteSecondColon_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(lean_object* v_motive_1123_, uint8_t v_t_1124_, lean_object* v_h_1125_, lean_object* v_hourMinuteSecondColon_1126_){
_start:
{
lean_inc(v_hourMinuteSecondColon_1126_);
return v_hourMinuteSecondColon_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___boxed(lean_object* v_motive_1127_, lean_object* v_t_1128_, lean_object* v_h_1129_, lean_object* v_hourMinuteSecondColon_1130_){
_start:
{
uint8_t v_t_boxed_1131_; lean_object* v_res_1132_; 
v_t_boxed_1131_ = lean_unbox(v_t_1128_);
v_res_1132_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(v_motive_1127_, v_t_boxed_1131_, v_h_1129_, v_hourMinuteSecondColon_1130_);
lean_dec(v_hourMinuteSecondColon_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr(uint8_t v_x_1142_, lean_object* v_prec_1143_){
_start:
{
lean_object* v___y_1145_; lean_object* v___y_1152_; lean_object* v___y_1159_; 
switch(v_x_1142_)
{
case 0:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(1024u);
v___x_1166_ = lean_nat_dec_le(v___x_1165_, v_prec_1143_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1145_ = v___x_1167_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1145_ = v___x_1168_;
goto v___jp_1144_;
}
}
case 1:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_unsigned_to_nat(1024u);
v___x_1170_ = lean_nat_dec_le(v___x_1169_, v_prec_1143_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1152_ = v___x_1171_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1152_ = v___x_1172_;
goto v___jp_1151_;
}
}
default: 
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(1024u);
v___x_1174_ = lean_nat_dec_le(v___x_1173_, v_prec_1143_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1159_ = v___x_1175_;
goto v___jp_1158_;
}
else
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1159_ = v___x_1176_;
goto v___jp_1158_;
}
}
}
v___jp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1146_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__1));
lean_inc(v___y_1145_);
v___x_1147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___y_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = 0;
v___x_1149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*1, v___x_1148_);
v___x_1150_ = l_Repr_addAppParen(v___x_1149_, v_prec_1143_);
return v___x_1150_;
}
v___jp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1153_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__3));
lean_inc(v___y_1152_);
v___x_1154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___y_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = 0;
v___x_1156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*1, v___x_1155_);
v___x_1157_ = l_Repr_addAppParen(v___x_1156_, v_prec_1143_);
return v___x_1157_;
}
v___jp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1160_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__5));
lean_inc(v___y_1159_);
v___x_1161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___y_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = 0;
v___x_1163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*1, v___x_1162_);
v___x_1164_ = l_Repr_addAppParen(v___x_1163_, v_prec_1143_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr___boxed(lean_object* v_x_1177_, lean_object* v_prec_1178_){
_start:
{
uint8_t v_x_173__boxed_1179_; lean_object* v_res_1180_; 
v_x_173__boxed_1179_ = lean_unbox(v_x_1177_);
v_res_1180_ = l_Std_Time_instReprOffsetZ_repr(v_x_173__boxed_1179_, v_prec_1178_);
lean_dec(v_prec_1178_);
return v_res_1180_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetZ_default(void){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = 0;
return v___x_1183_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetZ(void){
_start:
{
uint8_t v___x_1184_; 
v___x_1184_ = 0;
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify(lean_object* v_num_1194_){
_start:
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_nat_dec_eq(v_num_1194_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_unsigned_to_nat(2u);
v___x_1200_ = lean_nat_dec_eq(v_num_1194_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = lean_unsigned_to_nat(3u);
v___x_1202_ = lean_nat_dec_eq(v_num_1194_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_unsigned_to_nat(4u);
v___x_1204_ = lean_nat_dec_eq(v_num_1194_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(5u);
v___x_1206_ = lean_nat_dec_eq(v_num_1194_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_box(0);
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; 
v___x_1208_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__1));
return v___x_1208_;
}
}
else
{
lean_object* v___x_1209_; 
v___x_1209_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__2));
return v___x_1209_;
}
}
else
{
goto v___jp_1195_;
}
}
else
{
goto v___jp_1195_;
}
}
else
{
goto v___jp_1195_;
}
v___jp_1195_:
{
lean_object* v___x_1196_; 
v___x_1196_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__0));
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify___boxed(lean_object* v_num_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_Time_OffsetZ_classify(v_num_1210_);
lean_dec(v_num_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx(uint8_t v_x_1212_){
_start:
{
switch(v_x_1212_)
{
case 0:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
return v___x_1213_;
}
case 1:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_unsigned_to_nat(1u);
return v___x_1214_;
}
case 2:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_unsigned_to_nat(2u);
return v___x_1215_;
}
default: 
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_unsigned_to_nat(3u);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx___boxed(lean_object* v_x_1217_){
_start:
{
uint8_t v_x_boxed_1218_; lean_object* v_res_1219_; 
v_x_boxed_1218_ = lean_unbox(v_x_1217_);
v_res_1219_ = l_Std_Time_DayPeriod_ctorIdx(v_x_boxed_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_toCtorIdx(uint8_t v_x_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Std_Time_DayPeriod_ctorIdx(v_x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_toCtorIdx___boxed(lean_object* v_x_1222_){
_start:
{
uint8_t v_x_4__boxed_1223_; lean_object* v_res_1224_; 
v_x_4__boxed_1223_ = lean_unbox(v_x_1222_);
v_res_1224_ = l_Std_Time_DayPeriod_toCtorIdx(v_x_4__boxed_1223_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg(lean_object* v_k_1225_){
_start:
{
lean_inc(v_k_1225_);
return v_k_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg___boxed(lean_object* v_k_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Std_Time_DayPeriod_ctorElim___redArg(v_k_1226_);
lean_dec(v_k_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim(lean_object* v_motive_1228_, lean_object* v_ctorIdx_1229_, uint8_t v_t_1230_, lean_object* v_h_1231_, lean_object* v_k_1232_){
_start:
{
lean_inc(v_k_1232_);
return v_k_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___boxed(lean_object* v_motive_1233_, lean_object* v_ctorIdx_1234_, lean_object* v_t_1235_, lean_object* v_h_1236_, lean_object* v_k_1237_){
_start:
{
uint8_t v_t_boxed_1238_; lean_object* v_res_1239_; 
v_t_boxed_1238_ = lean_unbox(v_t_1235_);
v_res_1239_ = l_Std_Time_DayPeriod_ctorElim(v_motive_1233_, v_ctorIdx_1234_, v_t_boxed_1238_, v_h_1236_, v_k_1237_);
lean_dec(v_k_1237_);
lean_dec(v_ctorIdx_1234_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg(lean_object* v_am_1240_){
_start:
{
lean_inc(v_am_1240_);
return v_am_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg___boxed(lean_object* v_am_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Std_Time_DayPeriod_am_elim___redArg(v_am_1241_);
lean_dec(v_am_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim(lean_object* v_motive_1243_, uint8_t v_t_1244_, lean_object* v_h_1245_, lean_object* v_am_1246_){
_start:
{
lean_inc(v_am_1246_);
return v_am_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___boxed(lean_object* v_motive_1247_, lean_object* v_t_1248_, lean_object* v_h_1249_, lean_object* v_am_1250_){
_start:
{
uint8_t v_t_boxed_1251_; lean_object* v_res_1252_; 
v_t_boxed_1251_ = lean_unbox(v_t_1248_);
v_res_1252_ = l_Std_Time_DayPeriod_am_elim(v_motive_1247_, v_t_boxed_1251_, v_h_1249_, v_am_1250_);
lean_dec(v_am_1250_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg(lean_object* v_pm_1253_){
_start:
{
lean_inc(v_pm_1253_);
return v_pm_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg___boxed(lean_object* v_pm_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_Time_DayPeriod_pm_elim___redArg(v_pm_1254_);
lean_dec(v_pm_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim(lean_object* v_motive_1256_, uint8_t v_t_1257_, lean_object* v_h_1258_, lean_object* v_pm_1259_){
_start:
{
lean_inc(v_pm_1259_);
return v_pm_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___boxed(lean_object* v_motive_1260_, lean_object* v_t_1261_, lean_object* v_h_1262_, lean_object* v_pm_1263_){
_start:
{
uint8_t v_t_boxed_1264_; lean_object* v_res_1265_; 
v_t_boxed_1264_ = lean_unbox(v_t_1261_);
v_res_1265_ = l_Std_Time_DayPeriod_pm_elim(v_motive_1260_, v_t_boxed_1264_, v_h_1262_, v_pm_1263_);
lean_dec(v_pm_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg(lean_object* v_noon_1266_){
_start:
{
lean_inc(v_noon_1266_);
return v_noon_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg___boxed(lean_object* v_noon_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Std_Time_DayPeriod_noon_elim___redArg(v_noon_1267_);
lean_dec(v_noon_1267_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim(lean_object* v_motive_1269_, uint8_t v_t_1270_, lean_object* v_h_1271_, lean_object* v_noon_1272_){
_start:
{
lean_inc(v_noon_1272_);
return v_noon_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___boxed(lean_object* v_motive_1273_, lean_object* v_t_1274_, lean_object* v_h_1275_, lean_object* v_noon_1276_){
_start:
{
uint8_t v_t_boxed_1277_; lean_object* v_res_1278_; 
v_t_boxed_1277_ = lean_unbox(v_t_1274_);
v_res_1278_ = l_Std_Time_DayPeriod_noon_elim(v_motive_1273_, v_t_boxed_1277_, v_h_1275_, v_noon_1276_);
lean_dec(v_noon_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg(lean_object* v_midnight_1279_){
_start:
{
lean_inc(v_midnight_1279_);
return v_midnight_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg___boxed(lean_object* v_midnight_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_Time_DayPeriod_midnight_elim___redArg(v_midnight_1280_);
lean_dec(v_midnight_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim(lean_object* v_motive_1282_, uint8_t v_t_1283_, lean_object* v_h_1284_, lean_object* v_midnight_1285_){
_start:
{
lean_inc(v_midnight_1285_);
return v_midnight_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___boxed(lean_object* v_motive_1286_, lean_object* v_t_1287_, lean_object* v_h_1288_, lean_object* v_midnight_1289_){
_start:
{
uint8_t v_t_boxed_1290_; lean_object* v_res_1291_; 
v_t_boxed_1290_ = lean_unbox(v_t_1287_);
v_res_1291_ = l_Std_Time_DayPeriod_midnight_elim(v_motive_1286_, v_t_boxed_1290_, v_h_1288_, v_midnight_1289_);
lean_dec(v_midnight_1289_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr(uint8_t v_x_1304_, lean_object* v_prec_1305_){
_start:
{
lean_object* v___y_1307_; lean_object* v___y_1314_; lean_object* v___y_1321_; lean_object* v___y_1328_; 
switch(v_x_1304_)
{
case 0:
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(1024u);
v___x_1335_ = lean_nat_dec_le(v___x_1334_, v_prec_1305_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1307_ = v___x_1336_;
goto v___jp_1306_;
}
else
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1307_ = v___x_1337_;
goto v___jp_1306_;
}
}
case 1:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = lean_unsigned_to_nat(1024u);
v___x_1339_ = lean_nat_dec_le(v___x_1338_, v_prec_1305_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1314_ = v___x_1340_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1314_ = v___x_1341_;
goto v___jp_1313_;
}
}
case 2:
{
lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = lean_unsigned_to_nat(1024u);
v___x_1343_ = lean_nat_dec_le(v___x_1342_, v_prec_1305_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1321_ = v___x_1344_;
goto v___jp_1320_;
}
else
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1321_ = v___x_1345_;
goto v___jp_1320_;
}
}
default: 
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = lean_unsigned_to_nat(1024u);
v___x_1347_ = lean_nat_dec_le(v___x_1346_, v_prec_1305_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1328_ = v___x_1348_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1328_ = v___x_1349_;
goto v___jp_1327_;
}
}
}
v___jp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1308_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__1));
lean_inc(v___y_1307_);
v___x_1309_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___y_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = 0;
v___x_1311_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*1, v___x_1310_);
v___x_1312_ = l_Repr_addAppParen(v___x_1311_, v_prec_1305_);
return v___x_1312_;
}
v___jp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1315_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__3));
lean_inc(v___y_1314_);
v___x_1316_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___y_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = 0;
v___x_1318_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set_uint8(v___x_1318_, sizeof(void*)*1, v___x_1317_);
v___x_1319_ = l_Repr_addAppParen(v___x_1318_, v_prec_1305_);
return v___x_1319_;
}
v___jp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1322_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__5));
lean_inc(v___y_1321_);
v___x_1323_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___y_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = 0;
v___x_1325_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1325_, 0, v___x_1323_);
lean_ctor_set_uint8(v___x_1325_, sizeof(void*)*1, v___x_1324_);
v___x_1326_ = l_Repr_addAppParen(v___x_1325_, v_prec_1305_);
return v___x_1326_;
}
v___jp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1329_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__7));
lean_inc(v___y_1328_);
v___x_1330_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___y_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = 0;
v___x_1332_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set_uint8(v___x_1332_, sizeof(void*)*1, v___x_1331_);
v___x_1333_ = l_Repr_addAppParen(v___x_1332_, v_prec_1305_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr___boxed(lean_object* v_x_1350_, lean_object* v_prec_1351_){
_start:
{
uint8_t v_x_229__boxed_1352_; lean_object* v_res_1353_; 
v_x_229__boxed_1352_ = lean_unbox(v_x_1350_);
v_res_1353_ = l_Std_Time_instReprDayPeriod_repr(v_x_229__boxed_1352_, v_prec_1351_);
lean_dec(v_prec_1351_);
return v_res_1353_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedDayPeriod_default(void){
_start:
{
uint8_t v___x_1356_; 
v___x_1356_ = 0;
return v___x_1356_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedDayPeriod(void){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = 0;
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx(uint8_t v_x_1358_){
_start:
{
switch(v_x_1358_)
{
case 0:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
return v___x_1359_;
}
case 1:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_unsigned_to_nat(1u);
return v___x_1360_;
}
case 2:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_unsigned_to_nat(2u);
return v___x_1361_;
}
case 3:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_unsigned_to_nat(3u);
return v___x_1362_;
}
case 4:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_unsigned_to_nat(4u);
return v___x_1363_;
}
default: 
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_unsigned_to_nat(5u);
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx___boxed(lean_object* v_x_1365_){
_start:
{
uint8_t v_x_boxed_1366_; lean_object* v_res_1367_; 
v_x_boxed_1366_ = lean_unbox(v_x_1365_);
v_res_1367_ = l_Std_Time_ExtendedDayPeriod_ctorIdx(v_x_boxed_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_toCtorIdx(uint8_t v_x_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Std_Time_ExtendedDayPeriod_ctorIdx(v_x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_toCtorIdx___boxed(lean_object* v_x_1370_){
_start:
{
uint8_t v_x_4__boxed_1371_; lean_object* v_res_1372_; 
v_x_4__boxed_1371_ = lean_unbox(v_x_1370_);
v_res_1372_ = l_Std_Time_ExtendedDayPeriod_toCtorIdx(v_x_4__boxed_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(lean_object* v_k_1373_){
_start:
{
lean_inc(v_k_1373_);
return v_k_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg___boxed(lean_object* v_k_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(v_k_1374_);
lean_dec(v_k_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim(lean_object* v_motive_1376_, lean_object* v_ctorIdx_1377_, uint8_t v_t_1378_, lean_object* v_h_1379_, lean_object* v_k_1380_){
_start:
{
lean_inc(v_k_1380_);
return v_k_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___boxed(lean_object* v_motive_1381_, lean_object* v_ctorIdx_1382_, lean_object* v_t_1383_, lean_object* v_h_1384_, lean_object* v_k_1385_){
_start:
{
uint8_t v_t_boxed_1386_; lean_object* v_res_1387_; 
v_t_boxed_1386_ = lean_unbox(v_t_1383_);
v_res_1387_ = l_Std_Time_ExtendedDayPeriod_ctorElim(v_motive_1381_, v_ctorIdx_1382_, v_t_boxed_1386_, v_h_1384_, v_k_1385_);
lean_dec(v_k_1385_);
lean_dec(v_ctorIdx_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(lean_object* v_midnight_1388_){
_start:
{
lean_inc(v_midnight_1388_);
return v_midnight_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg___boxed(lean_object* v_midnight_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(v_midnight_1389_);
lean_dec(v_midnight_1389_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim(lean_object* v_motive_1391_, uint8_t v_t_1392_, lean_object* v_h_1393_, lean_object* v_midnight_1394_){
_start:
{
lean_inc(v_midnight_1394_);
return v_midnight_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___boxed(lean_object* v_motive_1395_, lean_object* v_t_1396_, lean_object* v_h_1397_, lean_object* v_midnight_1398_){
_start:
{
uint8_t v_t_boxed_1399_; lean_object* v_res_1400_; 
v_t_boxed_1399_ = lean_unbox(v_t_1396_);
v_res_1400_ = l_Std_Time_ExtendedDayPeriod_midnight_elim(v_motive_1395_, v_t_boxed_1399_, v_h_1397_, v_midnight_1398_);
lean_dec(v_midnight_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg(lean_object* v_night_1401_){
_start:
{
lean_inc(v_night_1401_);
return v_night_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg___boxed(lean_object* v_night_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Std_Time_ExtendedDayPeriod_night_elim___redArg(v_night_1402_);
lean_dec(v_night_1402_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim(lean_object* v_motive_1404_, uint8_t v_t_1405_, lean_object* v_h_1406_, lean_object* v_night_1407_){
_start:
{
lean_inc(v_night_1407_);
return v_night_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___boxed(lean_object* v_motive_1408_, lean_object* v_t_1409_, lean_object* v_h_1410_, lean_object* v_night_1411_){
_start:
{
uint8_t v_t_boxed_1412_; lean_object* v_res_1413_; 
v_t_boxed_1412_ = lean_unbox(v_t_1409_);
v_res_1413_ = l_Std_Time_ExtendedDayPeriod_night_elim(v_motive_1408_, v_t_boxed_1412_, v_h_1410_, v_night_1411_);
lean_dec(v_night_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(lean_object* v_morning_1414_){
_start:
{
lean_inc(v_morning_1414_);
return v_morning_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg___boxed(lean_object* v_morning_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(v_morning_1415_);
lean_dec(v_morning_1415_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim(lean_object* v_motive_1417_, uint8_t v_t_1418_, lean_object* v_h_1419_, lean_object* v_morning_1420_){
_start:
{
lean_inc(v_morning_1420_);
return v_morning_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___boxed(lean_object* v_motive_1421_, lean_object* v_t_1422_, lean_object* v_h_1423_, lean_object* v_morning_1424_){
_start:
{
uint8_t v_t_boxed_1425_; lean_object* v_res_1426_; 
v_t_boxed_1425_ = lean_unbox(v_t_1422_);
v_res_1426_ = l_Std_Time_ExtendedDayPeriod_morning_elim(v_motive_1421_, v_t_boxed_1425_, v_h_1423_, v_morning_1424_);
lean_dec(v_morning_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(lean_object* v_noon_1427_){
_start:
{
lean_inc(v_noon_1427_);
return v_noon_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg___boxed(lean_object* v_noon_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(v_noon_1428_);
lean_dec(v_noon_1428_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim(lean_object* v_motive_1430_, uint8_t v_t_1431_, lean_object* v_h_1432_, lean_object* v_noon_1433_){
_start:
{
lean_inc(v_noon_1433_);
return v_noon_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___boxed(lean_object* v_motive_1434_, lean_object* v_t_1435_, lean_object* v_h_1436_, lean_object* v_noon_1437_){
_start:
{
uint8_t v_t_boxed_1438_; lean_object* v_res_1439_; 
v_t_boxed_1438_ = lean_unbox(v_t_1435_);
v_res_1439_ = l_Std_Time_ExtendedDayPeriod_noon_elim(v_motive_1434_, v_t_boxed_1438_, v_h_1436_, v_noon_1437_);
lean_dec(v_noon_1437_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(lean_object* v_afternoon_1440_){
_start:
{
lean_inc(v_afternoon_1440_);
return v_afternoon_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg___boxed(lean_object* v_afternoon_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(v_afternoon_1441_);
lean_dec(v_afternoon_1441_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim(lean_object* v_motive_1443_, uint8_t v_t_1444_, lean_object* v_h_1445_, lean_object* v_afternoon_1446_){
_start:
{
lean_inc(v_afternoon_1446_);
return v_afternoon_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___boxed(lean_object* v_motive_1447_, lean_object* v_t_1448_, lean_object* v_h_1449_, lean_object* v_afternoon_1450_){
_start:
{
uint8_t v_t_boxed_1451_; lean_object* v_res_1452_; 
v_t_boxed_1451_ = lean_unbox(v_t_1448_);
v_res_1452_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim(v_motive_1447_, v_t_boxed_1451_, v_h_1449_, v_afternoon_1450_);
lean_dec(v_afternoon_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(lean_object* v_evening_1453_){
_start:
{
lean_inc(v_evening_1453_);
return v_evening_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg___boxed(lean_object* v_evening_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(v_evening_1454_);
lean_dec(v_evening_1454_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim(lean_object* v_motive_1456_, uint8_t v_t_1457_, lean_object* v_h_1458_, lean_object* v_evening_1459_){
_start:
{
lean_inc(v_evening_1459_);
return v_evening_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___boxed(lean_object* v_motive_1460_, lean_object* v_t_1461_, lean_object* v_h_1462_, lean_object* v_evening_1463_){
_start:
{
uint8_t v_t_boxed_1464_; lean_object* v_res_1465_; 
v_t_boxed_1464_ = lean_unbox(v_t_1461_);
v_res_1465_ = l_Std_Time_ExtendedDayPeriod_evening_elim(v_motive_1460_, v_t_boxed_1464_, v_h_1462_, v_evening_1463_);
lean_dec(v_evening_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr(uint8_t v_x_1484_, lean_object* v_prec_1485_){
_start:
{
lean_object* v___y_1487_; lean_object* v___y_1494_; lean_object* v___y_1501_; lean_object* v___y_1508_; lean_object* v___y_1515_; lean_object* v___y_1522_; 
switch(v_x_1484_)
{
case 0:
{
lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1528_ = lean_unsigned_to_nat(1024u);
v___x_1529_ = lean_nat_dec_le(v___x_1528_, v_prec_1485_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1487_ = v___x_1530_;
goto v___jp_1486_;
}
else
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1487_ = v___x_1531_;
goto v___jp_1486_;
}
}
case 1:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = lean_unsigned_to_nat(1024u);
v___x_1533_ = lean_nat_dec_le(v___x_1532_, v_prec_1485_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1494_ = v___x_1534_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1494_ = v___x_1535_;
goto v___jp_1493_;
}
}
case 2:
{
lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1536_ = lean_unsigned_to_nat(1024u);
v___x_1537_ = lean_nat_dec_le(v___x_1536_, v_prec_1485_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1501_ = v___x_1538_;
goto v___jp_1500_;
}
else
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1501_ = v___x_1539_;
goto v___jp_1500_;
}
}
case 3:
{
lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1540_ = lean_unsigned_to_nat(1024u);
v___x_1541_ = lean_nat_dec_le(v___x_1540_, v_prec_1485_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1508_ = v___x_1542_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1508_ = v___x_1543_;
goto v___jp_1507_;
}
}
case 4:
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = lean_unsigned_to_nat(1024u);
v___x_1545_ = lean_nat_dec_le(v___x_1544_, v_prec_1485_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1515_ = v___x_1546_;
goto v___jp_1514_;
}
else
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1515_ = v___x_1547_;
goto v___jp_1514_;
}
}
default: 
{
lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1548_ = lean_unsigned_to_nat(1024u);
v___x_1549_ = lean_nat_dec_le(v___x_1548_, v_prec_1485_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1522_ = v___x_1550_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1522_ = v___x_1551_;
goto v___jp_1521_;
}
}
}
v___jp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1488_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__1));
lean_inc(v___y_1487_);
v___x_1489_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___y_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = 0;
v___x_1491_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*1, v___x_1490_);
v___x_1492_ = l_Repr_addAppParen(v___x_1491_, v_prec_1485_);
return v___x_1492_;
}
v___jp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1495_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__3));
lean_inc(v___y_1494_);
v___x_1496_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = 0;
v___x_1498_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*1, v___x_1497_);
v___x_1499_ = l_Repr_addAppParen(v___x_1498_, v_prec_1485_);
return v___x_1499_;
}
v___jp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1502_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__5));
lean_inc(v___y_1501_);
v___x_1503_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___y_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = 0;
v___x_1505_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set_uint8(v___x_1505_, sizeof(void*)*1, v___x_1504_);
v___x_1506_ = l_Repr_addAppParen(v___x_1505_, v_prec_1485_);
return v___x_1506_;
}
v___jp_1507_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1509_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__7));
lean_inc(v___y_1508_);
v___x_1510_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___y_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = 0;
v___x_1512_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*1, v___x_1511_);
v___x_1513_ = l_Repr_addAppParen(v___x_1512_, v_prec_1485_);
return v___x_1513_;
}
v___jp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1516_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__9));
lean_inc(v___y_1515_);
v___x_1517_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___y_1515_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = 0;
v___x_1519_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set_uint8(v___x_1519_, sizeof(void*)*1, v___x_1518_);
v___x_1520_ = l_Repr_addAppParen(v___x_1519_, v_prec_1485_);
return v___x_1520_;
}
v___jp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1523_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__11));
lean_inc(v___y_1522_);
v___x_1524_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___y_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = 0;
v___x_1526_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*1, v___x_1525_);
v___x_1527_ = l_Repr_addAppParen(v___x_1526_, v_prec_1485_);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___boxed(lean_object* v_x_1552_, lean_object* v_prec_1553_){
_start:
{
uint8_t v_x_341__boxed_1554_; lean_object* v_res_1555_; 
v_x_341__boxed_1554_ = lean_unbox(v_x_1552_);
v_res_1555_ = l_Std_Time_instReprExtendedDayPeriod_repr(v_x_341__boxed_1554_, v_prec_1553_);
lean_dec(v_prec_1553_);
return v_res_1555_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedExtendedDayPeriod_default(void){
_start:
{
uint8_t v___x_1558_; 
v___x_1558_ = 0;
return v___x_1558_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedExtendedDayPeriod(void){
_start:
{
uint8_t v___x_1559_; 
v___x_1559_ = 0;
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx(lean_object* v_x_1560_){
_start:
{
switch(lean_obj_tag(v_x_1560_))
{
case 0:
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_unsigned_to_nat(0u);
return v___x_1561_;
}
case 1:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_unsigned_to_nat(1u);
return v___x_1562_;
}
case 2:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_unsigned_to_nat(2u);
return v___x_1563_;
}
case 3:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_unsigned_to_nat(3u);
return v___x_1564_;
}
case 4:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_unsigned_to_nat(4u);
return v___x_1565_;
}
case 5:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_unsigned_to_nat(5u);
return v___x_1566_;
}
case 6:
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_unsigned_to_nat(6u);
return v___x_1567_;
}
case 7:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_unsigned_to_nat(7u);
return v___x_1568_;
}
case 8:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_unsigned_to_nat(8u);
return v___x_1569_;
}
case 9:
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_unsigned_to_nat(9u);
return v___x_1570_;
}
case 10:
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_unsigned_to_nat(10u);
return v___x_1571_;
}
case 11:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_unsigned_to_nat(11u);
return v___x_1572_;
}
case 12:
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_unsigned_to_nat(12u);
return v___x_1573_;
}
case 13:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_unsigned_to_nat(13u);
return v___x_1574_;
}
case 14:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_unsigned_to_nat(14u);
return v___x_1575_;
}
case 15:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_unsigned_to_nat(15u);
return v___x_1576_;
}
case 16:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_unsigned_to_nat(16u);
return v___x_1577_;
}
case 17:
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_unsigned_to_nat(17u);
return v___x_1578_;
}
case 18:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_unsigned_to_nat(18u);
return v___x_1579_;
}
case 19:
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_unsigned_to_nat(19u);
return v___x_1580_;
}
case 20:
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_unsigned_to_nat(20u);
return v___x_1581_;
}
case 21:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_unsigned_to_nat(21u);
return v___x_1582_;
}
case 22:
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_unsigned_to_nat(22u);
return v___x_1583_;
}
case 23:
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_unsigned_to_nat(23u);
return v___x_1584_;
}
case 24:
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_unsigned_to_nat(24u);
return v___x_1585_;
}
case 25:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_unsigned_to_nat(25u);
return v___x_1586_;
}
case 26:
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_unsigned_to_nat(26u);
return v___x_1587_;
}
case 27:
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_unsigned_to_nat(27u);
return v___x_1588_;
}
case 28:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_unsigned_to_nat(28u);
return v___x_1589_;
}
case 29:
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_unsigned_to_nat(29u);
return v___x_1590_;
}
case 30:
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_unsigned_to_nat(30u);
return v___x_1591_;
}
case 31:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_unsigned_to_nat(31u);
return v___x_1592_;
}
case 32:
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_unsigned_to_nat(32u);
return v___x_1593_;
}
case 33:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_unsigned_to_nat(33u);
return v___x_1594_;
}
case 34:
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_unsigned_to_nat(34u);
return v___x_1595_;
}
default: 
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_unsigned_to_nat(35u);
return v___x_1596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx___boxed(lean_object* v_x_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Std_Time_Modifier_ctorIdx(v_x_1597_);
lean_dec_ref(v_x_1597_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___redArg(lean_object* v_t_1599_, lean_object* v_k_1600_){
_start:
{
switch(lean_obj_tag(v_t_1599_))
{
case 0:
{
uint8_t v_presentation_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_presentation_1601_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1602_ = lean_box(v_presentation_1601_);
v___x_1603_ = lean_apply_1(v_k_1600_, v___x_1602_);
return v___x_1603_;
}
case 4:
{
lean_object* v_presentation_1604_; lean_object* v___x_1605_; 
v_presentation_1604_ = lean_ctor_get(v_t_1599_, 0);
lean_inc_ref(v_presentation_1604_);
lean_dec_ref_known(v_t_1599_, 1);
v___x_1605_ = lean_apply_1(v_k_1600_, v_presentation_1604_);
return v___x_1605_;
}
case 5:
{
lean_object* v_presentation_1606_; lean_object* v___x_1607_; 
v_presentation_1606_ = lean_ctor_get(v_t_1599_, 0);
lean_inc_ref(v_presentation_1606_);
lean_dec_ref_known(v_t_1599_, 1);
v___x_1607_ = lean_apply_1(v_k_1600_, v_presentation_1606_);
return v___x_1607_;
}
case 7:
{
lean_object* v_presentation_1608_; lean_object* v___x_1609_; 
v_presentation_1608_ = lean_ctor_get(v_t_1599_, 0);
lean_inc_ref(v_presentation_1608_);
lean_dec_ref_known(v_t_1599_, 1);
v___x_1609_ = lean_apply_1(v_k_1600_, v_presentation_1608_);
return v___x_1609_;
}
case 8:
{
lean_object* v_presentation_1610_; lean_object* v___x_1611_; 
v_presentation_1610_ = lean_ctor_get(v_t_1599_, 0);
lean_inc_ref(v_presentation_1610_);
lean_dec_ref_known(v_t_1599_, 1);
v___x_1611_ = lean_apply_1(v_k_1600_, v_presentation_1610_);
return v___x_1611_;
}
case 12:
{
uint8_t v_presentation_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_presentation_1612_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1613_ = lean_box(v_presentation_1612_);
v___x_1614_ = lean_apply_1(v_k_1600_, v___x_1613_);
return v___x_1614_;
}
case 13:
{
lean_object* v_presentation_1615_; lean_object* v___x_1616_; 
v_presentation_1615_ = lean_ctor_get(v_t_1599_, 0);
lean_inc_ref(v_presentation_1615_);
lean_dec_ref_known(v_t_1599_, 1);
v___x_1616_ = lean_apply_1(v_k_1600_, v_presentation_1615_);
return v___x_1616_;
}
case 14:
{
lean_object* v_presentation_1617_; lean_object* v___x_1618_; 
v_presentation_1617_ = lean_ctor_get(v_t_1599_, 0);
lean_inc_ref(v_presentation_1617_);
lean_dec_ref_known(v_t_1599_, 1);
v___x_1618_ = lean_apply_1(v_k_1600_, v_presentation_1617_);
return v___x_1618_;
}
case 16:
{
uint8_t v_presentation_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_presentation_1619_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1620_ = lean_box(v_presentation_1619_);
v___x_1621_ = lean_apply_1(v_k_1600_, v___x_1620_);
return v___x_1621_;
}
case 17:
{
uint8_t v_presentation_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_presentation_1622_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1623_ = lean_box(v_presentation_1622_);
v___x_1624_ = lean_apply_1(v_k_1600_, v___x_1623_);
return v___x_1624_;
}
case 18:
{
uint8_t v_presentation_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_presentation_1625_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1626_ = lean_box(v_presentation_1625_);
v___x_1627_ = lean_apply_1(v_k_1600_, v___x_1626_);
return v___x_1627_;
}
case 29:
{
uint8_t v_presentation_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_presentation_1628_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1629_ = lean_box(v_presentation_1628_);
v___x_1630_ = lean_apply_1(v_k_1600_, v___x_1629_);
return v___x_1630_;
}
case 30:
{
uint8_t v_presentation_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_presentation_1631_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1632_ = lean_box(v_presentation_1631_);
v___x_1633_ = lean_apply_1(v_k_1600_, v___x_1632_);
return v___x_1633_;
}
case 31:
{
uint8_t v_presentation_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_presentation_1634_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1635_ = lean_box(v_presentation_1634_);
v___x_1636_ = lean_apply_1(v_k_1600_, v___x_1635_);
return v___x_1636_;
}
case 32:
{
uint8_t v_presentation_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_presentation_1637_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1638_ = lean_box(v_presentation_1637_);
v___x_1639_ = lean_apply_1(v_k_1600_, v___x_1638_);
return v___x_1639_;
}
case 33:
{
uint8_t v_presentation_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_presentation_1640_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1641_ = lean_box(v_presentation_1640_);
v___x_1642_ = lean_apply_1(v_k_1600_, v___x_1641_);
return v___x_1642_;
}
case 34:
{
uint8_t v_presentation_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_presentation_1643_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1644_ = lean_box(v_presentation_1643_);
v___x_1645_ = lean_apply_1(v_k_1600_, v___x_1644_);
return v___x_1645_;
}
case 35:
{
uint8_t v_presentation_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_presentation_1646_ = lean_ctor_get_uint8(v_t_1599_, 0);
lean_dec_ref_known(v_t_1599_, 0);
v___x_1647_ = lean_box(v_presentation_1646_);
v___x_1648_ = lean_apply_1(v_k_1600_, v___x_1647_);
return v___x_1648_;
}
default: 
{
lean_object* v_presentation_1649_; lean_object* v___x_1650_; 
v_presentation_1649_ = lean_ctor_get(v_t_1599_, 0);
lean_inc(v_presentation_1649_);
lean_dec_ref(v_t_1599_);
v___x_1650_ = lean_apply_1(v_k_1600_, v_presentation_1649_);
return v___x_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim(lean_object* v_motive_1651_, lean_object* v_ctorIdx_1652_, lean_object* v_t_1653_, lean_object* v_h_1654_, lean_object* v_k_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1653_, v_k_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___boxed(lean_object* v_motive_1657_, lean_object* v_ctorIdx_1658_, lean_object* v_t_1659_, lean_object* v_h_1660_, lean_object* v_k_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Std_Time_Modifier_ctorElim(v_motive_1657_, v_ctorIdx_1658_, v_t_1659_, v_h_1660_, v_k_1661_);
lean_dec(v_ctorIdx_1658_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim___redArg(lean_object* v_t_1663_, lean_object* v_G_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1663_, v_G_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim(lean_object* v_motive_1666_, lean_object* v_t_1667_, lean_object* v_h_1668_, lean_object* v_G_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1667_, v_G_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim___redArg(lean_object* v_t_1671_, lean_object* v_u_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1671_, v_u_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim(lean_object* v_motive_1674_, lean_object* v_t_1675_, lean_object* v_h_1676_, lean_object* v_u_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1675_, v_u_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim___redArg(lean_object* v_t_1679_, lean_object* v_y_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1679_, v_y_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim(lean_object* v_motive_1682_, lean_object* v_t_1683_, lean_object* v_h_1684_, lean_object* v_y_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1683_, v_y_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim___redArg(lean_object* v_t_1687_, lean_object* v_D_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1687_, v_D_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim(lean_object* v_motive_1690_, lean_object* v_t_1691_, lean_object* v_h_1692_, lean_object* v_D_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1691_, v_D_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim___redArg(lean_object* v_t_1695_, lean_object* v_M_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1695_, v_M_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim(lean_object* v_motive_1698_, lean_object* v_t_1699_, lean_object* v_h_1700_, lean_object* v_M_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1699_, v_M_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim___redArg(lean_object* v_t_1703_, lean_object* v_L_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1703_, v_L_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim(lean_object* v_motive_1706_, lean_object* v_t_1707_, lean_object* v_h_1708_, lean_object* v_L_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1707_, v_L_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim___redArg(lean_object* v_t_1711_, lean_object* v_d_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1711_, v_d_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim(lean_object* v_motive_1714_, lean_object* v_t_1715_, lean_object* v_h_1716_, lean_object* v_d_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1715_, v_d_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim___redArg(lean_object* v_t_1719_, lean_object* v_Q_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1719_, v_Q_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim(lean_object* v_motive_1722_, lean_object* v_t_1723_, lean_object* v_h_1724_, lean_object* v_Q_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1723_, v_Q_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim___redArg(lean_object* v_t_1727_, lean_object* v_q_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1727_, v_q_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim(lean_object* v_motive_1730_, lean_object* v_t_1731_, lean_object* v_h_1732_, lean_object* v_q_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1731_, v_q_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim___redArg(lean_object* v_t_1735_, lean_object* v_Y_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1735_, v_Y_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim(lean_object* v_motive_1738_, lean_object* v_t_1739_, lean_object* v_h_1740_, lean_object* v_Y_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1739_, v_Y_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim___redArg(lean_object* v_t_1743_, lean_object* v_w_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1743_, v_w_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim(lean_object* v_motive_1746_, lean_object* v_t_1747_, lean_object* v_h_1748_, lean_object* v_w_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1747_, v_w_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim___redArg(lean_object* v_t_1751_, lean_object* v_W_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1751_, v_W_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim(lean_object* v_motive_1754_, lean_object* v_t_1755_, lean_object* v_h_1756_, lean_object* v_W_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1755_, v_W_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim___redArg(lean_object* v_t_1759_, lean_object* v_E_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1759_, v_E_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim(lean_object* v_motive_1762_, lean_object* v_t_1763_, lean_object* v_h_1764_, lean_object* v_E_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1763_, v_E_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim___redArg(lean_object* v_t_1767_, lean_object* v_e_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1767_, v_e_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim(lean_object* v_motive_1770_, lean_object* v_t_1771_, lean_object* v_h_1772_, lean_object* v_e_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1771_, v_e_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim___redArg(lean_object* v_t_1775_, lean_object* v_c_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1775_, v_c_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim(lean_object* v_motive_1778_, lean_object* v_t_1779_, lean_object* v_h_1780_, lean_object* v_c_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1779_, v_c_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim___redArg(lean_object* v_t_1783_, lean_object* v_F_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1783_, v_F_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim(lean_object* v_motive_1786_, lean_object* v_t_1787_, lean_object* v_h_1788_, lean_object* v_F_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1787_, v_F_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim___redArg(lean_object* v_t_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1791_, v_a_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim(lean_object* v_motive_1794_, lean_object* v_t_1795_, lean_object* v_h_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1795_, v_a_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim___redArg(lean_object* v_t_1799_, lean_object* v_b_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1799_, v_b_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim(lean_object* v_motive_1802_, lean_object* v_t_1803_, lean_object* v_h_1804_, lean_object* v_b_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1803_, v_b_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim___redArg(lean_object* v_t_1807_, lean_object* v_B_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1807_, v_B_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim(lean_object* v_motive_1810_, lean_object* v_t_1811_, lean_object* v_h_1812_, lean_object* v_B_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1811_, v_B_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim___redArg(lean_object* v_t_1815_, lean_object* v_h_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1815_, v_h_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim(lean_object* v_motive_1818_, lean_object* v_t_1819_, lean_object* v_h_1820_, lean_object* v_h_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1819_, v_h_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim___redArg(lean_object* v_t_1823_, lean_object* v_K_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1823_, v_K_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim(lean_object* v_motive_1826_, lean_object* v_t_1827_, lean_object* v_h_1828_, lean_object* v_K_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1827_, v_K_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim___redArg(lean_object* v_t_1831_, lean_object* v_k_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1831_, v_k_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim(lean_object* v_motive_1834_, lean_object* v_t_1835_, lean_object* v_h_1836_, lean_object* v_k_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1835_, v_k_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim___redArg(lean_object* v_t_1839_, lean_object* v_H_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1839_, v_H_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim(lean_object* v_motive_1842_, lean_object* v_t_1843_, lean_object* v_h_1844_, lean_object* v_H_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1843_, v_H_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim___redArg(lean_object* v_t_1847_, lean_object* v_m_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1847_, v_m_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim(lean_object* v_motive_1850_, lean_object* v_t_1851_, lean_object* v_h_1852_, lean_object* v_m_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1851_, v_m_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim___redArg(lean_object* v_t_1855_, lean_object* v_s_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1855_, v_s_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim(lean_object* v_motive_1858_, lean_object* v_t_1859_, lean_object* v_h_1860_, lean_object* v_s_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1859_, v_s_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim___redArg(lean_object* v_t_1863_, lean_object* v_S_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1863_, v_S_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim(lean_object* v_motive_1866_, lean_object* v_t_1867_, lean_object* v_h_1868_, lean_object* v_S_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1867_, v_S_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim___redArg(lean_object* v_t_1871_, lean_object* v_A_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1871_, v_A_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim(lean_object* v_motive_1874_, lean_object* v_t_1875_, lean_object* v_h_1876_, lean_object* v_A_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1875_, v_A_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim___redArg(lean_object* v_t_1879_, lean_object* v_n_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1879_, v_n_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim(lean_object* v_motive_1882_, lean_object* v_t_1883_, lean_object* v_h_1884_, lean_object* v_n_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1883_, v_n_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim___redArg(lean_object* v_t_1887_, lean_object* v_N_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1887_, v_N_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim(lean_object* v_motive_1890_, lean_object* v_t_1891_, lean_object* v_h_1892_, lean_object* v_N_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1891_, v_N_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim___redArg(lean_object* v_t_1895_, lean_object* v_V_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1895_, v_V_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim(lean_object* v_motive_1898_, lean_object* v_t_1899_, lean_object* v_h_1900_, lean_object* v_V_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1899_, v_V_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim___redArg(lean_object* v_t_1903_, lean_object* v_z_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1903_, v_z_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim(lean_object* v_motive_1906_, lean_object* v_t_1907_, lean_object* v_h_1908_, lean_object* v_z_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1907_, v_z_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim___redArg(lean_object* v_t_1911_, lean_object* v_v_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1911_, v_v_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim(lean_object* v_motive_1914_, lean_object* v_t_1915_, lean_object* v_h_1916_, lean_object* v_v_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1915_, v_v_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim___redArg(lean_object* v_t_1919_, lean_object* v_O_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1919_, v_O_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim(lean_object* v_motive_1922_, lean_object* v_t_1923_, lean_object* v_h_1924_, lean_object* v_O_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1923_, v_O_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim___redArg(lean_object* v_t_1927_, lean_object* v_X_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1927_, v_X_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim(lean_object* v_motive_1930_, lean_object* v_t_1931_, lean_object* v_h_1932_, lean_object* v_X_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1931_, v_X_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim___redArg(lean_object* v_t_1935_, lean_object* v_x_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1935_, v_x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim(lean_object* v_motive_1938_, lean_object* v_t_1939_, lean_object* v_h_1940_, lean_object* v_x_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1939_, v_x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim___redArg(lean_object* v_t_1943_, lean_object* v_Z_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1943_, v_Z_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim(lean_object* v_motive_1946_, lean_object* v_t_1947_, lean_object* v_h_1948_, lean_object* v_Z_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1947_, v_Z_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(lean_object* v_x_1957_, lean_object* v_x_1958_){
_start:
{
if (lean_obj_tag(v_x_1957_) == 0)
{
lean_object* v_val_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_val_1959_ = lean_ctor_get(v_x_1957_, 0);
lean_inc(v_val_1959_);
lean_dec_ref_known(v_x_1957_, 1);
v___x_1960_ = ((lean_object*)(l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__1));
v___x_1961_ = l_Std_Time_instReprNumber_repr___redArg(v_val_1959_);
v___x_1962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = l_Repr_addAppParen(v___x_1962_, v_x_1958_);
return v___x_1963_;
}
else
{
lean_object* v_val_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_val_1964_ = lean_ctor_get(v_x_1957_, 0);
lean_inc(v_val_1964_);
lean_dec_ref_known(v_x_1957_, 1);
v___x_1965_ = ((lean_object*)(l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__3));
v___x_1966_ = lean_unsigned_to_nat(1024u);
v___x_1967_ = lean_unbox(v_val_1964_);
lean_dec(v_val_1964_);
v___x_1968_ = l_Std_Time_instReprText_repr(v___x_1967_, v___x_1966_);
v___x_1969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1965_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = l_Repr_addAppParen(v___x_1969_, v_x_1958_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___boxed(lean_object* v_x_1971_, lean_object* v_x_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_x_1971_, v_x_1972_);
lean_dec(v_x_1972_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr(lean_object* v_x_2190_, lean_object* v_prec_2191_){
_start:
{
switch(lean_obj_tag(v_x_2190_))
{
case 0:
{
uint8_t v_presentation_2192_; lean_object* v___y_2194_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_presentation_2192_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2203_ = lean_unsigned_to_nat(1024u);
v___x_2204_ = lean_nat_dec_le(v___x_2203_, v_prec_2191_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; 
v___x_2205_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2194_ = v___x_2205_;
goto v___jp_2193_;
}
else
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2194_ = v___x_2206_;
goto v___jp_2193_;
}
v___jp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2195_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__2));
v___x_2196_ = lean_unsigned_to_nat(1024u);
v___x_2197_ = l_Std_Time_instReprText_repr(v_presentation_2192_, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2195_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
lean_inc(v___y_2194_);
v___x_2199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___y_2194_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = 0;
v___x_2201_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set_uint8(v___x_2201_, sizeof(void*)*1, v___x_2200_);
v___x_2202_ = l_Repr_addAppParen(v___x_2201_, v_prec_2191_);
return v___x_2202_;
}
}
case 1:
{
lean_object* v_presentation_2207_; lean_object* v___y_2209_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v_presentation_2207_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2207_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2218_ = lean_unsigned_to_nat(1024u);
v___x_2219_ = lean_nat_dec_le(v___x_2218_, v_prec_2191_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2209_ = v___x_2220_;
goto v___jp_2208_;
}
else
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2209_ = v___x_2221_;
goto v___jp_2208_;
}
v___jp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2210_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__5));
v___x_2211_ = lean_unsigned_to_nat(1024u);
v___x_2212_ = l_Std_Time_instReprYear_repr(v_presentation_2207_, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2210_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
lean_inc(v___y_2209_);
v___x_2214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___y_2209_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = 0;
v___x_2216_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*1, v___x_2215_);
v___x_2217_ = l_Repr_addAppParen(v___x_2216_, v_prec_2191_);
return v___x_2217_;
}
}
case 2:
{
lean_object* v_presentation_2222_; lean_object* v___y_2224_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v_presentation_2222_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2222_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2233_ = lean_unsigned_to_nat(1024u);
v___x_2234_ = lean_nat_dec_le(v___x_2233_, v_prec_2191_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2224_ = v___x_2235_;
goto v___jp_2223_;
}
else
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2224_ = v___x_2236_;
goto v___jp_2223_;
}
v___jp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2225_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__8));
v___x_2226_ = lean_unsigned_to_nat(1024u);
v___x_2227_ = l_Std_Time_instReprYear_repr(v_presentation_2222_, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2225_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
lean_inc(v___y_2224_);
v___x_2229_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___y_2224_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = 0;
v___x_2231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2231_, 0, v___x_2229_);
lean_ctor_set_uint8(v___x_2231_, sizeof(void*)*1, v___x_2230_);
v___x_2232_ = l_Repr_addAppParen(v___x_2231_, v_prec_2191_);
return v___x_2232_;
}
}
case 3:
{
lean_object* v_presentation_2237_; lean_object* v___y_2239_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v_presentation_2237_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2237_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2247_ = lean_unsigned_to_nat(1024u);
v___x_2248_ = lean_nat_dec_le(v___x_2247_, v_prec_2191_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; 
v___x_2249_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2239_ = v___x_2249_;
goto v___jp_2238_;
}
else
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2239_ = v___x_2250_;
goto v___jp_2238_;
}
v___jp_2238_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2240_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__11));
v___x_2241_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2237_);
v___x_2242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
lean_inc(v___y_2239_);
v___x_2243_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___y_2239_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = 0;
v___x_2245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*1, v___x_2244_);
v___x_2246_ = l_Repr_addAppParen(v___x_2245_, v_prec_2191_);
return v___x_2246_;
}
}
case 4:
{
lean_object* v_presentation_2251_; lean_object* v___y_2253_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_presentation_2251_ = lean_ctor_get(v_x_2190_, 0);
lean_inc_ref(v_presentation_2251_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2262_ = lean_unsigned_to_nat(1024u);
v___x_2263_ = lean_nat_dec_le(v___x_2262_, v_prec_2191_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; 
v___x_2264_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2253_ = v___x_2264_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2253_ = v___x_2265_;
goto v___jp_2252_;
}
v___jp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2254_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__14));
v___x_2255_ = lean_unsigned_to_nat(1024u);
v___x_2256_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2251_, v___x_2255_);
v___x_2257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2254_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
lean_inc(v___y_2253_);
v___x_2258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___y_2253_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = 0;
v___x_2260_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set_uint8(v___x_2260_, sizeof(void*)*1, v___x_2259_);
v___x_2261_ = l_Repr_addAppParen(v___x_2260_, v_prec_2191_);
return v___x_2261_;
}
}
case 5:
{
lean_object* v_presentation_2266_; lean_object* v___y_2268_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v_presentation_2266_ = lean_ctor_get(v_x_2190_, 0);
lean_inc_ref(v_presentation_2266_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2277_ = lean_unsigned_to_nat(1024u);
v___x_2278_ = lean_nat_dec_le(v___x_2277_, v_prec_2191_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2268_ = v___x_2279_;
goto v___jp_2267_;
}
else
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2268_ = v___x_2280_;
goto v___jp_2267_;
}
v___jp_2267_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2269_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__17));
v___x_2270_ = lean_unsigned_to_nat(1024u);
v___x_2271_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2266_, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2269_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
lean_inc(v___y_2268_);
v___x_2273_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___y_2268_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = 0;
v___x_2275_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*1, v___x_2274_);
v___x_2276_ = l_Repr_addAppParen(v___x_2275_, v_prec_2191_);
return v___x_2276_;
}
}
case 6:
{
lean_object* v_presentation_2281_; lean_object* v___y_2283_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v_presentation_2281_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2281_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2291_ = lean_unsigned_to_nat(1024u);
v___x_2292_ = lean_nat_dec_le(v___x_2291_, v_prec_2191_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2283_ = v___x_2293_;
goto v___jp_2282_;
}
else
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2283_ = v___x_2294_;
goto v___jp_2282_;
}
v___jp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2284_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__20));
v___x_2285_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2281_);
v___x_2286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
lean_inc(v___y_2283_);
v___x_2287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___y_2283_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = 0;
v___x_2289_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set_uint8(v___x_2289_, sizeof(void*)*1, v___x_2288_);
v___x_2290_ = l_Repr_addAppParen(v___x_2289_, v_prec_2191_);
return v___x_2290_;
}
}
case 7:
{
lean_object* v_presentation_2295_; lean_object* v___y_2297_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v_presentation_2295_ = lean_ctor_get(v_x_2190_, 0);
lean_inc_ref(v_presentation_2295_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2306_ = lean_unsigned_to_nat(1024u);
v___x_2307_ = lean_nat_dec_le(v___x_2306_, v_prec_2191_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2297_ = v___x_2308_;
goto v___jp_2296_;
}
else
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2297_ = v___x_2309_;
goto v___jp_2296_;
}
v___jp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2298_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__23));
v___x_2299_ = lean_unsigned_to_nat(1024u);
v___x_2300_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2295_, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2298_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
lean_inc(v___y_2297_);
v___x_2302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___y_2297_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = 0;
v___x_2304_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set_uint8(v___x_2304_, sizeof(void*)*1, v___x_2303_);
v___x_2305_ = l_Repr_addAppParen(v___x_2304_, v_prec_2191_);
return v___x_2305_;
}
}
case 8:
{
lean_object* v_presentation_2310_; lean_object* v___y_2312_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v_presentation_2310_ = lean_ctor_get(v_x_2190_, 0);
lean_inc_ref(v_presentation_2310_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2321_ = lean_unsigned_to_nat(1024u);
v___x_2322_ = lean_nat_dec_le(v___x_2321_, v_prec_2191_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2312_ = v___x_2323_;
goto v___jp_2311_;
}
else
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2312_ = v___x_2324_;
goto v___jp_2311_;
}
v___jp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2313_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__26));
v___x_2314_ = lean_unsigned_to_nat(1024u);
v___x_2315_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2310_, v___x_2314_);
v___x_2316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2313_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
lean_inc(v___y_2312_);
v___x_2317_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___y_2312_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = 0;
v___x_2319_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*1, v___x_2318_);
v___x_2320_ = l_Repr_addAppParen(v___x_2319_, v_prec_2191_);
return v___x_2320_;
}
}
case 9:
{
lean_object* v_presentation_2325_; lean_object* v___y_2327_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v_presentation_2325_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2325_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2336_ = lean_unsigned_to_nat(1024u);
v___x_2337_ = lean_nat_dec_le(v___x_2336_, v_prec_2191_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2327_ = v___x_2338_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2339_; 
v___x_2339_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2327_ = v___x_2339_;
goto v___jp_2326_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2328_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__29));
v___x_2329_ = lean_unsigned_to_nat(1024u);
v___x_2330_ = l_Std_Time_instReprYear_repr(v_presentation_2325_, v___x_2329_);
v___x_2331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2328_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
lean_inc(v___y_2327_);
v___x_2332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___y_2327_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = 0;
v___x_2334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*1, v___x_2333_);
v___x_2335_ = l_Repr_addAppParen(v___x_2334_, v_prec_2191_);
return v___x_2335_;
}
}
case 10:
{
lean_object* v_presentation_2340_; lean_object* v___y_2342_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_presentation_2340_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2340_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2350_ = lean_unsigned_to_nat(1024u);
v___x_2351_ = lean_nat_dec_le(v___x_2350_, v_prec_2191_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2342_ = v___x_2352_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2353_; 
v___x_2353_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2342_ = v___x_2353_;
goto v___jp_2341_;
}
v___jp_2341_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2343_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__32));
v___x_2344_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2340_);
v___x_2345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
lean_inc(v___y_2342_);
v___x_2346_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___y_2342_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = 0;
v___x_2348_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set_uint8(v___x_2348_, sizeof(void*)*1, v___x_2347_);
v___x_2349_ = l_Repr_addAppParen(v___x_2348_, v_prec_2191_);
return v___x_2349_;
}
}
case 11:
{
lean_object* v_presentation_2354_; lean_object* v___y_2356_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
v_presentation_2354_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2354_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2364_ = lean_unsigned_to_nat(1024u);
v___x_2365_ = lean_nat_dec_le(v___x_2364_, v_prec_2191_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2356_ = v___x_2366_;
goto v___jp_2355_;
}
else
{
lean_object* v___x_2367_; 
v___x_2367_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2356_ = v___x_2367_;
goto v___jp_2355_;
}
v___jp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2357_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__35));
v___x_2358_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2354_);
v___x_2359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
lean_inc(v___y_2356_);
v___x_2360_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___y_2356_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = 0;
v___x_2362_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*1, v___x_2361_);
v___x_2363_ = l_Repr_addAppParen(v___x_2362_, v_prec_2191_);
return v___x_2363_;
}
}
case 12:
{
uint8_t v_presentation_2368_; lean_object* v___y_2370_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_presentation_2368_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2379_ = lean_unsigned_to_nat(1024u);
v___x_2380_ = lean_nat_dec_le(v___x_2379_, v_prec_2191_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2370_ = v___x_2381_;
goto v___jp_2369_;
}
else
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2370_ = v___x_2382_;
goto v___jp_2369_;
}
v___jp_2369_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2371_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__38));
v___x_2372_ = lean_unsigned_to_nat(1024u);
v___x_2373_ = l_Std_Time_instReprText_repr(v_presentation_2368_, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2371_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
lean_inc(v___y_2370_);
v___x_2375_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___y_2370_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = 0;
v___x_2377_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*1, v___x_2376_);
v___x_2378_ = l_Repr_addAppParen(v___x_2377_, v_prec_2191_);
return v___x_2378_;
}
}
case 13:
{
lean_object* v_presentation_2383_; lean_object* v___y_2385_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v_presentation_2383_ = lean_ctor_get(v_x_2190_, 0);
lean_inc_ref(v_presentation_2383_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2394_ = lean_unsigned_to_nat(1024u);
v___x_2395_ = lean_nat_dec_le(v___x_2394_, v_prec_2191_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2385_ = v___x_2396_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2385_ = v___x_2397_;
goto v___jp_2384_;
}
v___jp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2386_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__41));
v___x_2387_ = lean_unsigned_to_nat(1024u);
v___x_2388_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2383_, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2386_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
lean_inc(v___y_2385_);
v___x_2390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___y_2385_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = 0;
v___x_2392_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*1, v___x_2391_);
v___x_2393_ = l_Repr_addAppParen(v___x_2392_, v_prec_2191_);
return v___x_2393_;
}
}
case 14:
{
lean_object* v_presentation_2398_; lean_object* v___y_2400_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v_presentation_2398_ = lean_ctor_get(v_x_2190_, 0);
lean_inc_ref(v_presentation_2398_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2409_ = lean_unsigned_to_nat(1024u);
v___x_2410_ = lean_nat_dec_le(v___x_2409_, v_prec_2191_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2400_ = v___x_2411_;
goto v___jp_2399_;
}
else
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2400_ = v___x_2412_;
goto v___jp_2399_;
}
v___jp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2401_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__44));
v___x_2402_ = lean_unsigned_to_nat(1024u);
v___x_2403_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2398_, v___x_2402_);
v___x_2404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2401_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
lean_inc(v___y_2400_);
v___x_2405_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___y_2400_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = 0;
v___x_2407_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*1, v___x_2406_);
v___x_2408_ = l_Repr_addAppParen(v___x_2407_, v_prec_2191_);
return v___x_2408_;
}
}
case 15:
{
lean_object* v_presentation_2413_; lean_object* v___y_2415_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_presentation_2413_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2413_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2423_ = lean_unsigned_to_nat(1024u);
v___x_2424_ = lean_nat_dec_le(v___x_2423_, v_prec_2191_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2415_ = v___x_2425_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2415_ = v___x_2426_;
goto v___jp_2414_;
}
v___jp_2414_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2416_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__47));
v___x_2417_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2413_);
v___x_2418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
lean_inc(v___y_2415_);
v___x_2419_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___y_2415_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = 0;
v___x_2421_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set_uint8(v___x_2421_, sizeof(void*)*1, v___x_2420_);
v___x_2422_ = l_Repr_addAppParen(v___x_2421_, v_prec_2191_);
return v___x_2422_;
}
}
case 16:
{
uint8_t v_presentation_2427_; lean_object* v___y_2429_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v_presentation_2427_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2438_ = lean_unsigned_to_nat(1024u);
v___x_2439_ = lean_nat_dec_le(v___x_2438_, v_prec_2191_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2429_ = v___x_2440_;
goto v___jp_2428_;
}
else
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2429_ = v___x_2441_;
goto v___jp_2428_;
}
v___jp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2430_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__50));
v___x_2431_ = lean_unsigned_to_nat(1024u);
v___x_2432_ = l_Std_Time_instReprText_repr(v_presentation_2427_, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2430_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
lean_inc(v___y_2429_);
v___x_2434_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___y_2429_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = 0;
v___x_2436_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*1, v___x_2435_);
v___x_2437_ = l_Repr_addAppParen(v___x_2436_, v_prec_2191_);
return v___x_2437_;
}
}
case 17:
{
uint8_t v_presentation_2442_; lean_object* v___y_2444_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v_presentation_2442_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2453_ = lean_unsigned_to_nat(1024u);
v___x_2454_ = lean_nat_dec_le(v___x_2453_, v_prec_2191_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2444_ = v___x_2455_;
goto v___jp_2443_;
}
else
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2444_ = v___x_2456_;
goto v___jp_2443_;
}
v___jp_2443_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2445_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__53));
v___x_2446_ = lean_unsigned_to_nat(1024u);
v___x_2447_ = l_Std_Time_instReprText_repr(v_presentation_2442_, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2445_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
lean_inc(v___y_2444_);
v___x_2449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___y_2444_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = 0;
v___x_2451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set_uint8(v___x_2451_, sizeof(void*)*1, v___x_2450_);
v___x_2452_ = l_Repr_addAppParen(v___x_2451_, v_prec_2191_);
return v___x_2452_;
}
}
case 18:
{
uint8_t v_presentation_2457_; lean_object* v___y_2459_; lean_object* v___x_2468_; uint8_t v___x_2469_; 
v_presentation_2457_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2468_ = lean_unsigned_to_nat(1024u);
v___x_2469_ = lean_nat_dec_le(v___x_2468_, v_prec_2191_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2459_ = v___x_2470_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2459_ = v___x_2471_;
goto v___jp_2458_;
}
v___jp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2460_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__56));
v___x_2461_ = lean_unsigned_to_nat(1024u);
v___x_2462_ = l_Std_Time_instReprText_repr(v_presentation_2457_, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2460_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
lean_inc(v___y_2459_);
v___x_2464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___y_2459_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = 0;
v___x_2466_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*1, v___x_2465_);
v___x_2467_ = l_Repr_addAppParen(v___x_2466_, v_prec_2191_);
return v___x_2467_;
}
}
case 19:
{
lean_object* v_presentation_2472_; lean_object* v___y_2474_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_presentation_2472_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2472_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2482_ = lean_unsigned_to_nat(1024u);
v___x_2483_ = lean_nat_dec_le(v___x_2482_, v_prec_2191_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2474_ = v___x_2484_;
goto v___jp_2473_;
}
else
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2474_ = v___x_2485_;
goto v___jp_2473_;
}
v___jp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2475_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__59));
v___x_2476_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2472_);
v___x_2477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
lean_inc(v___y_2474_);
v___x_2478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___y_2474_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = 0;
v___x_2480_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*1, v___x_2479_);
v___x_2481_ = l_Repr_addAppParen(v___x_2480_, v_prec_2191_);
return v___x_2481_;
}
}
case 20:
{
lean_object* v_presentation_2486_; lean_object* v___y_2488_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v_presentation_2486_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2486_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2496_ = lean_unsigned_to_nat(1024u);
v___x_2497_ = lean_nat_dec_le(v___x_2496_, v_prec_2191_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2488_ = v___x_2498_;
goto v___jp_2487_;
}
else
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2488_ = v___x_2499_;
goto v___jp_2487_;
}
v___jp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2489_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__62));
v___x_2490_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2486_);
v___x_2491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2489_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
lean_inc(v___y_2488_);
v___x_2492_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___y_2488_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = 0;
v___x_2494_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*1, v___x_2493_);
v___x_2495_ = l_Repr_addAppParen(v___x_2494_, v_prec_2191_);
return v___x_2495_;
}
}
case 21:
{
lean_object* v_presentation_2500_; lean_object* v___y_2502_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v_presentation_2500_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2500_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2510_ = lean_unsigned_to_nat(1024u);
v___x_2511_ = lean_nat_dec_le(v___x_2510_, v_prec_2191_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2502_ = v___x_2512_;
goto v___jp_2501_;
}
else
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2502_ = v___x_2513_;
goto v___jp_2501_;
}
v___jp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2503_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__65));
v___x_2504_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2500_);
v___x_2505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
lean_inc(v___y_2502_);
v___x_2506_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___y_2502_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = 0;
v___x_2508_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set_uint8(v___x_2508_, sizeof(void*)*1, v___x_2507_);
v___x_2509_ = l_Repr_addAppParen(v___x_2508_, v_prec_2191_);
return v___x_2509_;
}
}
case 22:
{
lean_object* v_presentation_2514_; lean_object* v___y_2516_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v_presentation_2514_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2514_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2524_ = lean_unsigned_to_nat(1024u);
v___x_2525_ = lean_nat_dec_le(v___x_2524_, v_prec_2191_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; 
v___x_2526_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2516_ = v___x_2526_;
goto v___jp_2515_;
}
else
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2516_ = v___x_2527_;
goto v___jp_2515_;
}
v___jp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2517_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__68));
v___x_2518_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2514_);
v___x_2519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
lean_inc(v___y_2516_);
v___x_2520_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___y_2516_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = 0;
v___x_2522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set_uint8(v___x_2522_, sizeof(void*)*1, v___x_2521_);
v___x_2523_ = l_Repr_addAppParen(v___x_2522_, v_prec_2191_);
return v___x_2523_;
}
}
case 23:
{
lean_object* v_presentation_2528_; lean_object* v___y_2530_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_presentation_2528_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2528_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2538_ = lean_unsigned_to_nat(1024u);
v___x_2539_ = lean_nat_dec_le(v___x_2538_, v_prec_2191_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2530_ = v___x_2540_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2541_; 
v___x_2541_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2530_ = v___x_2541_;
goto v___jp_2529_;
}
v___jp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2531_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__71));
v___x_2532_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2528_);
v___x_2533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
lean_inc(v___y_2530_);
v___x_2534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___y_2530_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = 0;
v___x_2536_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set_uint8(v___x_2536_, sizeof(void*)*1, v___x_2535_);
v___x_2537_ = l_Repr_addAppParen(v___x_2536_, v_prec_2191_);
return v___x_2537_;
}
}
case 24:
{
lean_object* v_presentation_2542_; lean_object* v___y_2544_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v_presentation_2542_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2542_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2552_ = lean_unsigned_to_nat(1024u);
v___x_2553_ = lean_nat_dec_le(v___x_2552_, v_prec_2191_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2544_ = v___x_2554_;
goto v___jp_2543_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2544_ = v___x_2555_;
goto v___jp_2543_;
}
v___jp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2545_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__74));
v___x_2546_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2542_);
v___x_2547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
lean_inc(v___y_2544_);
v___x_2548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___y_2544_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = 0;
v___x_2550_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set_uint8(v___x_2550_, sizeof(void*)*1, v___x_2549_);
v___x_2551_ = l_Repr_addAppParen(v___x_2550_, v_prec_2191_);
return v___x_2551_;
}
}
case 25:
{
lean_object* v_presentation_2556_; lean_object* v___y_2558_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v_presentation_2556_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2556_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2567_ = lean_unsigned_to_nat(1024u);
v___x_2568_ = lean_nat_dec_le(v___x_2567_, v_prec_2191_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2558_ = v___x_2569_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2570_; 
v___x_2570_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2558_ = v___x_2570_;
goto v___jp_2557_;
}
v___jp_2557_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2559_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__77));
v___x_2560_ = lean_unsigned_to_nat(1024u);
v___x_2561_ = l_Std_Time_instReprFraction_repr(v_presentation_2556_, v___x_2560_);
v___x_2562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2559_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
lean_inc(v___y_2558_);
v___x_2563_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___y_2558_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = 0;
v___x_2565_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2565_, 0, v___x_2563_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*1, v___x_2564_);
v___x_2566_ = l_Repr_addAppParen(v___x_2565_, v_prec_2191_);
return v___x_2566_;
}
}
case 26:
{
lean_object* v_presentation_2571_; lean_object* v___y_2573_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v_presentation_2571_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2571_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2581_ = lean_unsigned_to_nat(1024u);
v___x_2582_ = lean_nat_dec_le(v___x_2581_, v_prec_2191_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2573_ = v___x_2583_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2573_ = v___x_2584_;
goto v___jp_2572_;
}
v___jp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2574_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__80));
v___x_2575_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2571_);
v___x_2576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
lean_inc(v___y_2573_);
v___x_2577_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___y_2573_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = 0;
v___x_2579_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*1, v___x_2578_);
v___x_2580_ = l_Repr_addAppParen(v___x_2579_, v_prec_2191_);
return v___x_2580_;
}
}
case 27:
{
lean_object* v_presentation_2585_; lean_object* v___y_2587_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v_presentation_2585_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2585_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2595_ = lean_unsigned_to_nat(1024u);
v___x_2596_ = lean_nat_dec_le(v___x_2595_, v_prec_2191_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2587_ = v___x_2597_;
goto v___jp_2586_;
}
else
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2587_ = v___x_2598_;
goto v___jp_2586_;
}
v___jp_2586_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2588_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__83));
v___x_2589_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2585_);
v___x_2590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
lean_inc(v___y_2587_);
v___x_2591_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___y_2587_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = 0;
v___x_2593_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*1, v___x_2592_);
v___x_2594_ = l_Repr_addAppParen(v___x_2593_, v_prec_2191_);
return v___x_2594_;
}
}
case 28:
{
lean_object* v_presentation_2599_; lean_object* v___y_2601_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v_presentation_2599_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_presentation_2599_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2609_ = lean_unsigned_to_nat(1024u);
v___x_2610_ = lean_nat_dec_le(v___x_2609_, v_prec_2191_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2601_ = v___x_2611_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2601_ = v___x_2612_;
goto v___jp_2600_;
}
v___jp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2602_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__86));
v___x_2603_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2599_);
v___x_2604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
lean_inc(v___y_2601_);
v___x_2605_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___y_2601_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = 0;
v___x_2607_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set_uint8(v___x_2607_, sizeof(void*)*1, v___x_2606_);
v___x_2608_ = l_Repr_addAppParen(v___x_2607_, v_prec_2191_);
return v___x_2608_;
}
}
case 29:
{
uint8_t v_presentation_2613_; lean_object* v___y_2615_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v_presentation_2613_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2624_ = lean_unsigned_to_nat(1024u);
v___x_2625_ = lean_nat_dec_le(v___x_2624_, v_prec_2191_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2615_ = v___x_2626_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2615_ = v___x_2627_;
goto v___jp_2614_;
}
v___jp_2614_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2616_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__89));
v___x_2617_ = lean_unsigned_to_nat(1024u);
v___x_2618_ = l_Std_Time_instReprZoneId_repr(v_presentation_2613_, v___x_2617_);
v___x_2619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2616_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
lean_inc(v___y_2615_);
v___x_2620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___y_2615_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = 0;
v___x_2622_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2622_, 0, v___x_2620_);
lean_ctor_set_uint8(v___x_2622_, sizeof(void*)*1, v___x_2621_);
v___x_2623_ = l_Repr_addAppParen(v___x_2622_, v_prec_2191_);
return v___x_2623_;
}
}
case 30:
{
uint8_t v_presentation_2628_; lean_object* v___y_2630_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v_presentation_2628_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2639_ = lean_unsigned_to_nat(1024u);
v___x_2640_ = lean_nat_dec_le(v___x_2639_, v_prec_2191_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2630_ = v___x_2641_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2642_; 
v___x_2642_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2630_ = v___x_2642_;
goto v___jp_2629_;
}
v___jp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2631_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__92));
v___x_2632_ = lean_unsigned_to_nat(1024u);
v___x_2633_ = l_Std_Time_instReprZoneName_repr(v_presentation_2628_, v___x_2632_);
v___x_2634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2631_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
lean_inc(v___y_2630_);
v___x_2635_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___y_2630_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = 0;
v___x_2637_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*1, v___x_2636_);
v___x_2638_ = l_Repr_addAppParen(v___x_2637_, v_prec_2191_);
return v___x_2638_;
}
}
case 31:
{
uint8_t v_presentation_2643_; lean_object* v___y_2645_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v_presentation_2643_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2654_ = lean_unsigned_to_nat(1024u);
v___x_2655_ = lean_nat_dec_le(v___x_2654_, v_prec_2191_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2645_ = v___x_2656_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2645_ = v___x_2657_;
goto v___jp_2644_;
}
v___jp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2646_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__95));
v___x_2647_ = lean_unsigned_to_nat(1024u);
v___x_2648_ = l_Std_Time_instReprZoneName_repr(v_presentation_2643_, v___x_2647_);
v___x_2649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2646_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
lean_inc(v___y_2645_);
v___x_2650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___y_2645_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = 0;
v___x_2652_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2652_, 0, v___x_2650_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*1, v___x_2651_);
v___x_2653_ = l_Repr_addAppParen(v___x_2652_, v_prec_2191_);
return v___x_2653_;
}
}
case 32:
{
uint8_t v_presentation_2658_; lean_object* v___y_2660_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v_presentation_2658_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2669_ = lean_unsigned_to_nat(1024u);
v___x_2670_ = lean_nat_dec_le(v___x_2669_, v_prec_2191_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2660_ = v___x_2671_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2660_ = v___x_2672_;
goto v___jp_2659_;
}
v___jp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2661_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__98));
v___x_2662_ = lean_unsigned_to_nat(1024u);
v___x_2663_ = l_Std_Time_instReprOffsetO_repr(v_presentation_2658_, v___x_2662_);
v___x_2664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2661_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
lean_inc(v___y_2660_);
v___x_2665_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___y_2660_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = 0;
v___x_2667_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set_uint8(v___x_2667_, sizeof(void*)*1, v___x_2666_);
v___x_2668_ = l_Repr_addAppParen(v___x_2667_, v_prec_2191_);
return v___x_2668_;
}
}
case 33:
{
uint8_t v_presentation_2673_; lean_object* v___y_2675_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v_presentation_2673_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2684_ = lean_unsigned_to_nat(1024u);
v___x_2685_ = lean_nat_dec_le(v___x_2684_, v_prec_2191_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; 
v___x_2686_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2675_ = v___x_2686_;
goto v___jp_2674_;
}
else
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2675_ = v___x_2687_;
goto v___jp_2674_;
}
v___jp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2676_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__101));
v___x_2677_ = lean_unsigned_to_nat(1024u);
v___x_2678_ = l_Std_Time_instReprOffsetX_repr(v_presentation_2673_, v___x_2677_);
v___x_2679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2676_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
lean_inc(v___y_2675_);
v___x_2680_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___y_2675_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = 0;
v___x_2682_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set_uint8(v___x_2682_, sizeof(void*)*1, v___x_2681_);
v___x_2683_ = l_Repr_addAppParen(v___x_2682_, v_prec_2191_);
return v___x_2683_;
}
}
case 34:
{
uint8_t v_presentation_2688_; lean_object* v___y_2690_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v_presentation_2688_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2699_ = lean_unsigned_to_nat(1024u);
v___x_2700_ = lean_nat_dec_le(v___x_2699_, v_prec_2191_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2690_ = v___x_2701_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2690_ = v___x_2702_;
goto v___jp_2689_;
}
v___jp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2691_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__104));
v___x_2692_ = lean_unsigned_to_nat(1024u);
v___x_2693_ = l_Std_Time_instReprOffsetX_repr(v_presentation_2688_, v___x_2692_);
v___x_2694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2691_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
lean_inc(v___y_2690_);
v___x_2695_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___y_2690_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = 0;
v___x_2697_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set_uint8(v___x_2697_, sizeof(void*)*1, v___x_2696_);
v___x_2698_ = l_Repr_addAppParen(v___x_2697_, v_prec_2191_);
return v___x_2698_;
}
}
default: 
{
uint8_t v_presentation_2703_; lean_object* v___y_2705_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v_presentation_2703_ = lean_ctor_get_uint8(v_x_2190_, 0);
lean_dec_ref_known(v_x_2190_, 0);
v___x_2714_ = lean_unsigned_to_nat(1024u);
v___x_2715_ = lean_nat_dec_le(v___x_2714_, v_prec_2191_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2705_ = v___x_2716_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_2717_; 
v___x_2717_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2705_ = v___x_2717_;
goto v___jp_2704_;
}
v___jp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2706_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__107));
v___x_2707_ = lean_unsigned_to_nat(1024u);
v___x_2708_ = l_Std_Time_instReprOffsetZ_repr(v_presentation_2703_, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2706_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
lean_inc(v___y_2705_);
v___x_2710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___y_2705_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = 0;
v___x_2712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*1, v___x_2711_);
v___x_2713_ = l_Repr_addAppParen(v___x_2712_, v_prec_2191_);
return v___x_2713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr___boxed(lean_object* v_x_2718_, lean_object* v_prec_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Std_Time_instReprModifier_repr(v_x_2718_, v_prec_2719_);
lean_dec(v_prec_2719_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(lean_object* v_constructor_2730_, lean_object* v_classify_2731_, lean_object* v_p_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v_len_2734_; lean_object* v___x_2735_; 
v_len_2734_ = lean_string_length(v_p_2732_);
v___x_2735_ = lean_apply_1(v_classify_2731_, v_len_2734_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v___x_2736_; uint32_t v___y_2738_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec_ref(v_constructor_2730_);
v___x_2736_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2746_ = lean_unsigned_to_nat(0u);
v___x_2747_ = lean_string_utf8_byte_size(v_p_2732_);
v___x_2748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2748_, 0, v_p_2732_);
lean_ctor_set(v___x_2748_, 1, v___x_2746_);
lean_ctor_set(v___x_2748_, 2, v___x_2747_);
v___x_2749_ = l_String_Slice_Pos_get_x3f(v___x_2748_, v___x_2746_);
lean_dec_ref_known(v___x_2748_, 3);
if (lean_obj_tag(v___x_2749_) == 0)
{
uint32_t v___x_2750_; 
v___x_2750_ = 65;
v___y_2738_ = v___x_2750_;
goto v___jp_2737_;
}
else
{
lean_object* v_val_2751_; uint32_t v___x_2752_; 
v_val_2751_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_val_2751_);
lean_dec_ref_known(v___x_2749_, 1);
v___x_2752_ = lean_unbox_uint32(v_val_2751_);
lean_dec(v_val_2751_);
v___y_2738_ = v___x_2752_;
goto v___jp_2737_;
}
v___jp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2739_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2740_ = lean_string_push(v___x_2739_, v___y_2738_);
v___x_2741_ = lean_string_append(v___x_2736_, v___x_2740_);
lean_dec_ref(v___x_2740_);
v___x_2742_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_2743_ = lean_string_append(v___x_2741_, v___x_2742_);
v___x_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
v___x_2745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2745_, 0, v_a_2733_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
return v___x_2745_;
}
}
else
{
lean_object* v_val_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_dec_ref(v_p_2732_);
v_val_2753_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_val_2753_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2754_ = lean_apply_1(v_constructor_2730_, v_val_2753_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_a_2733_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
return v___x_2755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod(lean_object* v_00_u03b1_2756_, lean_object* v_constructor_2757_, lean_object* v_classify_2758_, lean_object* v_p_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2757_, v_classify_2758_, v_p_2759_, v_a_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(lean_object* v_constructor_2763_, lean_object* v_p_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseText___closed__0));
v___x_2767_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2763_, v___x_2766_, v_p_2764_, v_a_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(lean_object* v_max_2768_, lean_object* v_x_2769_){
_start:
{
uint8_t v___x_2770_; 
v___x_2770_ = lean_nat_dec_le(v_x_2769_, v_max_2768_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; 
lean_dec(v_x_2769_);
v___x_2771_ = lean_box(0);
return v___x_2771_;
}
else
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_x_2769_);
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax___boxed(lean_object* v_max_2773_, lean_object* v_x_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(v_max_2773_, v_x_2774_);
lean_dec(v_max_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(lean_object* v_x_2778_){
_start:
{
lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2779_ = lean_unsigned_to_nat(1u);
v___x_2780_ = lean_nat_dec_eq(v_x_2778_, v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_box(0);
return v___x_2781_;
}
else
{
lean_object* v___x_2782_; 
v___x_2782_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___closed__0));
return v___x_2782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___boxed(lean_object* v_x_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(v_x_2783_);
lean_dec(v_x_2783_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(lean_object* v_x_2788_){
_start:
{
lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2789_ = lean_unsigned_to_nat(6u);
v___x_2790_ = lean_nat_dec_eq(v_x_2788_, v___x_2789_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Std_Time_Text_classify(v_x_2788_);
return v___x_2791_;
}
else
{
lean_object* v___x_2792_; 
v___x_2792_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___closed__0));
return v___x_2792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___boxed(lean_object* v_x_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(v_x_2793_);
lean_dec(v_x_2793_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(lean_object* v_constructor_2796_, lean_object* v_p_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText___closed__0));
v___x_2800_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2796_, v___x_2799_, v_p_2797_, v_a_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(lean_object* v_constructor_2802_, lean_object* v_p_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction___closed__0));
v___x_2806_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2802_, v___x_2805_, v_p_2803_, v_a_2804_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(lean_object* v_constructor_2807_, lean_object* v_p_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = lean_string_length(v_p_2808_);
v___x_2811_ = lean_apply_1(v_constructor_2807_, v___x_2810_);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v_a_2809_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber___boxed(lean_object* v_constructor_2813_, lean_object* v_p_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v_constructor_2813_, v_p_2814_, v_a_2815_);
lean_dec_ref(v_p_2814_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(lean_object* v_constructor_2818_, lean_object* v_p_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear___closed__0));
v___x_2822_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2818_, v___x_2821_, v_p_2819_, v_a_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(lean_object* v_constructor_2824_, lean_object* v_p_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX___closed__0));
v___x_2828_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2824_, v___x_2827_, v_p_2825_, v_a_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(lean_object* v_constructor_2830_, lean_object* v_p_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ___closed__0));
v___x_2834_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2830_, v___x_2833_, v_p_2831_, v_a_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(lean_object* v_constructor_2836_, lean_object* v_p_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO___closed__0));
v___x_2840_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2836_, v___x_2839_, v_p_2837_, v_a_2838_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(lean_object* v_p_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2848_ = lean_string_length(v_p_2846_);
v___x_2849_ = lean_unsigned_to_nat(1u);
v___x_2850_ = lean_nat_dec_eq(v___x_2848_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2851_ = lean_unsigned_to_nat(2u);
v___x_2852_ = lean_nat_dec_eq(v___x_2848_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; uint32_t v___y_2855_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2853_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = lean_string_utf8_byte_size(v_p_2846_);
v___x_2865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2865_, 0, v_p_2846_);
lean_ctor_set(v___x_2865_, 1, v___x_2863_);
lean_ctor_set(v___x_2865_, 2, v___x_2864_);
v___x_2866_ = l_String_Slice_Pos_get_x3f(v___x_2865_, v___x_2863_);
lean_dec_ref_known(v___x_2865_, 3);
if (lean_obj_tag(v___x_2866_) == 0)
{
uint32_t v___x_2867_; 
v___x_2867_ = 65;
v___y_2855_ = v___x_2867_;
goto v___jp_2854_;
}
else
{
lean_object* v_val_2868_; uint32_t v___x_2869_; 
v_val_2868_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_val_2868_);
lean_dec_ref_known(v___x_2866_, 1);
v___x_2869_ = lean_unbox_uint32(v_val_2868_);
lean_dec(v_val_2868_);
v___y_2855_ = v___x_2869_;
goto v___jp_2854_;
}
v___jp_2854_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2856_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2857_ = lean_string_push(v___x_2856_, v___y_2855_);
v___x_2858_ = lean_string_append(v___x_2853_, v___x_2857_);
lean_dec_ref(v___x_2857_);
v___x_2859_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__0));
v___x_2860_ = lean_string_append(v___x_2858_, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
v___x_2862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2862_, 0, v_a_2847_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
return v___x_2862_;
}
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec_ref(v_p_2846_);
v___x_2870_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__1));
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v_a_2847_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
return v___x_2871_;
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec_ref(v_p_2846_);
v___x_2872_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__2));
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v_a_2847_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
return v___x_2873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(lean_object* v_constructor_2875_, lean_object* v_p_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText___closed__0));
v___x_2879_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2875_, v___x_2878_, v_p_2876_, v_a_2877_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText(lean_object* v_x_2885_){
_start:
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = lean_unsigned_to_nat(3u);
v___x_2887_ = lean_nat_dec_lt(v_x_2885_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = lean_unsigned_to_nat(6u);
v___x_2889_ = lean_nat_dec_eq(v_x_2885_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Std_Time_Text_classify(v_x_2885_);
lean_dec(v_x_2885_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_box(0);
return v___x_2891_;
}
else
{
lean_object* v_val_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2900_; 
v_val_2892_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2894_ = v___x_2890_;
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_val_2892_);
lean_dec(v___x_2890_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2896_, 0, v_val_2892_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2896_);
v___x_2898_ = v___x_2894_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v___x_2901_; 
lean_dec(v_x_2885_);
v___x_2901_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1));
return v___x_2901_;
}
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v_x_2885_);
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(lean_object* v_constructor_2905_, lean_object* v_p_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText___closed__0));
v___x_2909_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2905_, v___x_2908_, v_p_2906_, v_a_2907_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(lean_object* v_x_2914_){
_start:
{
lean_object* v___x_2915_; uint8_t v___x_2916_; 
v___x_2915_ = lean_unsigned_to_nat(1u);
v___x_2916_ = lean_nat_dec_eq(v_x_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; uint8_t v___x_2918_; 
v___x_2917_ = lean_unsigned_to_nat(6u);
v___x_2918_ = lean_nat_dec_eq(v_x_2914_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = lean_unsigned_to_nat(3u);
v___x_2920_ = lean_nat_dec_le(v___x_2919_, v_x_2914_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_box(0);
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Std_Time_Text_classify(v_x_2914_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_box(0);
return v___x_2923_;
}
else
{
lean_object* v_val_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2932_; 
v_val_2924_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2926_ = v___x_2922_;
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_val_2924_);
lean_dec(v___x_2922_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_val_2924_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2928_);
v___x_2930_ = v___x_2926_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
else
{
lean_object* v___x_2933_; 
v___x_2933_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1));
return v___x_2933_;
}
}
else
{
lean_object* v___x_2934_; 
v___x_2934_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__1));
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___boxed(lean_object* v_x_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(v_x_2935_);
lean_dec(v_x_2935_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(lean_object* v_constructor_2938_, lean_object* v_p_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText___closed__0));
v___x_2942_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2938_, v___x_2941_, v_p_2939_, v_a_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(uint8_t v_presentation_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_alloc_ctor(16, 0, 1);
lean_ctor_set_uint8(v___x_2944_, 0, v_presentation_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0___boxed(lean_object* v_presentation_2945_){
_start:
{
uint8_t v_presentation_boxed_2946_; lean_object* v_res_2947_; 
v_presentation_boxed_2946_ = lean_unbox(v_presentation_2945_);
v_res_2947_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(v_presentation_boxed_2946_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(lean_object* v_p_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___f_2951_; lean_object* v___x_2952_; 
v___f_2951_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___closed__0));
v___x_2952_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2951_, v_p_2949_, v_a_2950_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(uint8_t v_presentation_2953_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = lean_alloc_ctor(17, 0, 1);
lean_ctor_set_uint8(v___x_2954_, 0, v_presentation_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0___boxed(lean_object* v_presentation_2955_){
_start:
{
uint8_t v_presentation_boxed_2956_; lean_object* v_res_2957_; 
v_presentation_boxed_2956_ = lean_unbox(v_presentation_2955_);
v_res_2957_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(v_presentation_boxed_2956_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(lean_object* v_p_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v___f_2961_; lean_object* v___x_2962_; 
v___f_2961_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___closed__0));
v___x_2962_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2961_, v_p_2959_, v_a_2960_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(uint8_t v_presentation_2963_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_alloc_ctor(18, 0, 1);
lean_ctor_set_uint8(v___x_2964_, 0, v_presentation_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0___boxed(lean_object* v_presentation_2965_){
_start:
{
uint8_t v_presentation_boxed_2966_; lean_object* v_res_2967_; 
v_presentation_boxed_2966_ = lean_unbox(v_presentation_2965_);
v_res_2967_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(v_presentation_boxed_2966_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(lean_object* v_p_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v___f_2971_; lean_object* v___x_2972_; 
v___f_2971_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___closed__0));
v___x_2972_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2971_, v_p_2969_, v_a_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(lean_object* v_constructor_2973_, lean_object* v_p_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v___y_2977_; uint32_t v___y_2978_; lean_object* v_len_2986_; uint32_t v___y_2988_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_len_2986_ = lean_string_length(v_p_2974_);
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = lean_string_utf8_byte_size(v_p_2974_);
lean_inc_ref(v_p_2974_);
v___x_3003_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3003_, 0, v_p_2974_);
lean_ctor_set(v___x_3003_, 1, v___x_3001_);
lean_ctor_set(v___x_3003_, 2, v___x_3002_);
v___x_3004_ = l_String_Slice_Pos_get_x3f(v___x_3003_, v___x_3001_);
lean_dec_ref_known(v___x_3003_, 3);
if (lean_obj_tag(v___x_3004_) == 0)
{
uint32_t v___x_3005_; 
v___x_3005_ = 65;
v___y_2988_ = v___x_3005_;
goto v___jp_2987_;
}
else
{
lean_object* v_val_3006_; uint32_t v___x_3007_; 
v_val_3006_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_val_3006_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3007_ = lean_unbox_uint32(v_val_3006_);
lean_dec(v_val_3006_);
v___y_2988_ = v___x_3007_;
goto v___jp_2987_;
}
v___jp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2979_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2980_ = lean_string_push(v___x_2979_, v___y_2978_);
lean_inc_ref(v___y_2977_);
v___x_2981_ = lean_string_append(v___y_2977_, v___x_2980_);
lean_dec_ref(v___x_2980_);
v___x_2982_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_2983_ = lean_string_append(v___x_2981_, v___x_2982_);
v___x_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2985_, 0, v_a_2975_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
return v___x_2985_;
}
v___jp_2987_:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Std_Time_ZoneName_classify(v___y_2988_, v_len_2986_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_dec_ref(v_constructor_2973_);
v___x_2990_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2991_ = lean_unsigned_to_nat(0u);
v___x_2992_ = lean_string_utf8_byte_size(v_p_2974_);
v___x_2993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2993_, 0, v_p_2974_);
lean_ctor_set(v___x_2993_, 1, v___x_2991_);
lean_ctor_set(v___x_2993_, 2, v___x_2992_);
v___x_2994_ = l_String_Slice_Pos_get_x3f(v___x_2993_, v___x_2991_);
lean_dec_ref_known(v___x_2993_, 3);
if (lean_obj_tag(v___x_2994_) == 0)
{
uint32_t v___x_2995_; 
v___x_2995_ = 65;
v___y_2977_ = v___x_2990_;
v___y_2978_ = v___x_2995_;
goto v___jp_2976_;
}
else
{
lean_object* v_val_2996_; uint32_t v___x_2997_; 
v_val_2996_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_val_2996_);
lean_dec_ref_known(v___x_2994_, 1);
v___x_2997_ = lean_unbox_uint32(v_val_2996_);
lean_dec(v_val_2996_);
v___y_2977_ = v___x_2990_;
v___y_2978_ = v___x_2997_;
goto v___jp_2976_;
}
}
else
{
lean_object* v_val_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec_ref(v_p_2974_);
v_val_2998_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_val_2998_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2999_ = lean_apply_1(v_constructor_2973_, v_val_2998_);
v___x_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3000_, 0, v_a_2975_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
return v___x_3000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0(uint8_t v_presentation_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_alloc_ctor(35, 0, 1);
lean_ctor_set_uint8(v___x_3009_, 0, v_presentation_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0___boxed(lean_object* v_presentation_3010_){
_start:
{
uint8_t v_presentation_boxed_3011_; lean_object* v_res_3012_; 
v_presentation_boxed_3011_ = lean_unbox(v_presentation_3010_);
v_res_3012_ = l_Std_Time_parseModifier___lam__0(v_presentation_boxed_3011_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1(uint8_t v_presentation_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_alloc_ctor(34, 0, 1);
lean_ctor_set_uint8(v___x_3014_, 0, v_presentation_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1___boxed(lean_object* v_presentation_3015_){
_start:
{
uint8_t v_presentation_boxed_3016_; lean_object* v_res_3017_; 
v_presentation_boxed_3016_ = lean_unbox(v_presentation_3015_);
v_res_3017_ = l_Std_Time_parseModifier___lam__1(v_presentation_boxed_3016_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2(uint8_t v_presentation_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_alloc_ctor(33, 0, 1);
lean_ctor_set_uint8(v___x_3019_, 0, v_presentation_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2___boxed(lean_object* v_presentation_3020_){
_start:
{
uint8_t v_presentation_boxed_3021_; lean_object* v_res_3022_; 
v_presentation_boxed_3021_ = lean_unbox(v_presentation_3020_);
v_res_3022_ = l_Std_Time_parseModifier___lam__2(v_presentation_boxed_3021_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3(uint8_t v_presentation_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = lean_alloc_ctor(32, 0, 1);
lean_ctor_set_uint8(v___x_3024_, 0, v_presentation_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3___boxed(lean_object* v_presentation_3025_){
_start:
{
uint8_t v_presentation_boxed_3026_; lean_object* v_res_3027_; 
v_presentation_boxed_3026_ = lean_unbox(v_presentation_3025_);
v_res_3027_ = l_Std_Time_parseModifier___lam__3(v_presentation_boxed_3026_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4(uint8_t v_presentation_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_alloc_ctor(31, 0, 1);
lean_ctor_set_uint8(v___x_3029_, 0, v_presentation_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4___boxed(lean_object* v_presentation_3030_){
_start:
{
uint8_t v_presentation_boxed_3031_; lean_object* v_res_3032_; 
v_presentation_boxed_3031_ = lean_unbox(v_presentation_3030_);
v_res_3032_ = l_Std_Time_parseModifier___lam__4(v_presentation_boxed_3031_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5(uint8_t v_presentation_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_alloc_ctor(30, 0, 1);
lean_ctor_set_uint8(v___x_3034_, 0, v_presentation_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5___boxed(lean_object* v_presentation_3035_){
_start:
{
uint8_t v_presentation_boxed_3036_; lean_object* v_res_3037_; 
v_presentation_boxed_3036_ = lean_unbox(v_presentation_3035_);
v_res_3037_ = l_Std_Time_parseModifier___lam__5(v_presentation_boxed_3036_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__6(lean_object* v_presentation_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_alloc_ctor(28, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_presentation_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__7(lean_object* v_presentation_3040_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = lean_alloc_ctor(27, 1, 0);
lean_ctor_set(v___x_3041_, 0, v_presentation_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__8(lean_object* v_presentation_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_alloc_ctor(26, 1, 0);
lean_ctor_set(v___x_3043_, 0, v_presentation_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__9(lean_object* v_presentation_3044_){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = lean_alloc_ctor(25, 1, 0);
lean_ctor_set(v___x_3045_, 0, v_presentation_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__10(lean_object* v_presentation_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_alloc_ctor(24, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_presentation_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__11(lean_object* v_presentation_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_alloc_ctor(23, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_presentation_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__12(lean_object* v_presentation_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(v___x_3051_, 0, v_presentation_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__13(lean_object* v_presentation_3052_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_3053_, 0, v_presentation_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__14(lean_object* v_presentation_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(v___x_3055_, 0, v_presentation_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__15(lean_object* v_presentation_3056_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_alloc_ctor(19, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_presentation_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__16(lean_object* v_presentation_3058_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_presentation_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__17(lean_object* v_presentation_3060_){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_3061_, 0, v_presentation_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__18(lean_object* v_presentation_3062_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_3063_, 0, v_presentation_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19(uint8_t v_presentation_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_alloc_ctor(12, 0, 1);
lean_ctor_set_uint8(v___x_3065_, 0, v_presentation_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19___boxed(lean_object* v_presentation_3066_){
_start:
{
uint8_t v_presentation_boxed_3067_; lean_object* v_res_3068_; 
v_presentation_boxed_3067_ = lean_unbox(v_presentation_3066_);
v_res_3068_ = l_Std_Time_parseModifier___lam__19(v_presentation_boxed_3067_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__20(lean_object* v_presentation_3069_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_presentation_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__21(lean_object* v_presentation_3071_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_presentation_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__22(lean_object* v_presentation_3073_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_presentation_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__23(lean_object* v_presentation_3075_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_presentation_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__24(lean_object* v_presentation_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3078_, 0, v_presentation_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__25(lean_object* v_presentation_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3080_, 0, v_presentation_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__26(lean_object* v_presentation_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3082_, 0, v_presentation_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__27(lean_object* v_presentation_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3084_, 0, v_presentation_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__28(lean_object* v_presentation_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3086_, 0, v_presentation_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__29(lean_object* v_presentation_3087_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_presentation_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__30(lean_object* v_presentation_3089_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3090_, 0, v_presentation_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31(uint8_t v_presentation_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3092_, 0, v_presentation_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31___boxed(lean_object* v_presentation_3093_){
_start:
{
uint8_t v_presentation_boxed_3094_; lean_object* v_res_3095_; 
v_presentation_boxed_3094_ = lean_unbox(v_presentation_3093_);
v_res_3095_ = l_Std_Time_parseModifier___lam__31(v_presentation_boxed_3094_);
return v_res_3095_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1(void){
_start:
{
uint32_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = 120;
v___x_3098_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3099_ = lean_string_push(v___x_3098_, v___x_3097_);
return v___x_3099_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1);
v___x_3101_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3102_ = lean_string_append(v___x_3101_, v___x_3100_);
return v___x_3102_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3104_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2);
v___x_3105_ = lean_string_append(v___x_3104_, v___x_3103_);
return v___x_3105_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3);
v___x_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(lean_object* v_acc_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v_fst_3110_; lean_object* v_snd_3111_; lean_object* v_pos_3113_; lean_object* v_snd_3114_; lean_object* v_err_3115_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v_fst_3110_ = lean_ctor_get(v_a_3109_, 0);
v_snd_3111_ = lean_ctor_get(v_a_3109_, 1);
lean_inc(v_snd_3111_);
v___x_3119_ = lean_string_utf8_byte_size(v_fst_3110_);
v___x_3120_ = lean_nat_dec_eq(v_snd_3111_, v___x_3119_);
if (v___x_3120_ == 0)
{
uint32_t v___x_3121_; uint32_t v_c_3122_; uint8_t v___x_3123_; 
v___x_3121_ = 120;
v_c_3122_ = lean_string_utf8_get_fast(v_fst_3110_, v_snd_3111_);
v___x_3123_ = lean_uint32_dec_eq(v_c_3122_, v___x_3121_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4);
lean_inc(v_snd_3111_);
v_pos_3113_ = v_a_3109_;
v_snd_3114_ = v_snd_3111_;
v_err_3115_ = v___x_3124_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3134_; 
lean_inc(v_fst_3110_);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_a_3109_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; lean_object* v_unused_3136_; 
v_unused_3135_ = lean_ctor_get(v_a_3109_, 1);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_a_3109_, 0);
lean_dec(v_unused_3136_);
v___x_3126_ = v_a_3109_;
v_isShared_3127_ = v_isSharedCheck_3134_;
goto v_resetjp_3125_;
}
else
{
lean_dec(v_a_3109_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3134_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v_it_x27_3130_; 
v___x_3128_ = lean_string_utf8_next_fast(v_fst_3110_, v_snd_3111_);
lean_dec(v_snd_3111_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 1, v___x_3128_);
v_it_x27_3130_ = v___x_3126_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_fst_3110_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v___x_3128_);
v_it_x27_3130_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
lean_object* v___x_3131_; 
v___x_3131_ = lean_string_push(v_acc_3108_, v___x_3121_);
v_acc_3108_ = v___x_3131_;
v_a_3109_ = v_it_x27_3130_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3137_; 
v___x_3137_ = lean_box(0);
lean_inc(v_snd_3111_);
v_pos_3113_ = v_a_3109_;
v_snd_3114_ = v_snd_3111_;
v_err_3115_ = v___x_3137_;
goto v___jp_3112_;
}
v___jp_3112_:
{
uint8_t v___x_3116_; 
v___x_3116_ = lean_nat_dec_eq(v_snd_3111_, v_snd_3114_);
lean_dec(v_snd_3114_);
lean_dec(v_snd_3111_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; 
lean_dec_ref(v_acc_3108_);
lean_inc(v_err_3115_);
v___x_3117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3117_, 0, v_pos_3113_);
lean_ctor_set(v___x_3117_, 1, v_err_3115_);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3118_, 0, v_pos_3113_);
lean_ctor_set(v___x_3118_, 1, v_acc_3108_);
return v___x_3118_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0(void){
_start:
{
uint32_t v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = 89;
v___x_3139_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3140_ = lean_string_push(v___x_3139_, v___x_3138_);
return v___x_3140_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1(void){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0);
v___x_3142_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3143_ = lean_string_append(v___x_3142_, v___x_3141_);
return v___x_3143_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3145_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1);
v___x_3146_ = lean_string_append(v___x_3145_, v___x_3144_);
return v___x_3146_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3(void){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(lean_object* v_acc_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v_fst_3151_; lean_object* v_snd_3152_; lean_object* v_pos_3154_; lean_object* v_snd_3155_; lean_object* v_err_3156_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
v_fst_3151_ = lean_ctor_get(v_a_3150_, 0);
v_snd_3152_ = lean_ctor_get(v_a_3150_, 1);
lean_inc(v_snd_3152_);
v___x_3160_ = lean_string_utf8_byte_size(v_fst_3151_);
v___x_3161_ = lean_nat_dec_eq(v_snd_3152_, v___x_3160_);
if (v___x_3161_ == 0)
{
uint32_t v___x_3162_; uint32_t v_c_3163_; uint8_t v___x_3164_; 
v___x_3162_ = 89;
v_c_3163_ = lean_string_utf8_get_fast(v_fst_3151_, v_snd_3152_);
v___x_3164_ = lean_uint32_dec_eq(v_c_3163_, v___x_3162_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; 
v___x_3165_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3);
lean_inc(v_snd_3152_);
v_pos_3154_ = v_a_3150_;
v_snd_3155_ = v_snd_3152_;
v_err_3156_ = v___x_3165_;
goto v___jp_3153_;
}
else
{
lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3175_; 
lean_inc(v_fst_3151_);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_a_3150_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; lean_object* v_unused_3177_; 
v_unused_3176_ = lean_ctor_get(v_a_3150_, 1);
lean_dec(v_unused_3176_);
v_unused_3177_ = lean_ctor_get(v_a_3150_, 0);
lean_dec(v_unused_3177_);
v___x_3167_ = v_a_3150_;
v_isShared_3168_ = v_isSharedCheck_3175_;
goto v_resetjp_3166_;
}
else
{
lean_dec(v_a_3150_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3175_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v_it_x27_3171_; 
v___x_3169_ = lean_string_utf8_next_fast(v_fst_3151_, v_snd_3152_);
lean_dec(v_snd_3152_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 1, v___x_3169_);
v_it_x27_3171_ = v___x_3167_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_fst_3151_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v___x_3169_);
v_it_x27_3171_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; 
v___x_3172_ = lean_string_push(v_acc_3149_, v___x_3162_);
v_acc_3149_ = v___x_3172_;
v_a_3150_ = v_it_x27_3171_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3178_; 
v___x_3178_ = lean_box(0);
lean_inc(v_snd_3152_);
v_pos_3154_ = v_a_3150_;
v_snd_3155_ = v_snd_3152_;
v_err_3156_ = v___x_3178_;
goto v___jp_3153_;
}
v___jp_3153_:
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_nat_dec_eq(v_snd_3152_, v_snd_3155_);
lean_dec(v_snd_3155_);
lean_dec(v_snd_3152_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; 
lean_dec_ref(v_acc_3149_);
lean_inc(v_err_3156_);
v___x_3158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3158_, 0, v_pos_3154_);
lean_ctor_set(v___x_3158_, 1, v_err_3156_);
return v___x_3158_;
}
else
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_pos_3154_);
lean_ctor_set(v___x_3159_, 1, v_acc_3149_);
return v___x_3159_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0(void){
_start:
{
uint32_t v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = 110;
v___x_3180_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3181_ = lean_string_push(v___x_3180_, v___x_3179_);
return v___x_3181_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0);
v___x_3183_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3184_ = lean_string_append(v___x_3183_, v___x_3182_);
return v___x_3184_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3185_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3186_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1);
v___x_3187_ = lean_string_append(v___x_3186_, v___x_3185_);
return v___x_3187_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2);
v___x_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(lean_object* v_acc_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v_fst_3192_; lean_object* v_snd_3193_; lean_object* v_pos_3195_; lean_object* v_snd_3196_; lean_object* v_err_3197_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v_fst_3192_ = lean_ctor_get(v_a_3191_, 0);
v_snd_3193_ = lean_ctor_get(v_a_3191_, 1);
lean_inc(v_snd_3193_);
v___x_3201_ = lean_string_utf8_byte_size(v_fst_3192_);
v___x_3202_ = lean_nat_dec_eq(v_snd_3193_, v___x_3201_);
if (v___x_3202_ == 0)
{
uint32_t v___x_3203_; uint32_t v_c_3204_; uint8_t v___x_3205_; 
v___x_3203_ = 110;
v_c_3204_ = lean_string_utf8_get_fast(v_fst_3192_, v_snd_3193_);
v___x_3205_ = lean_uint32_dec_eq(v_c_3204_, v___x_3203_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3);
lean_inc(v_snd_3193_);
v_pos_3195_ = v_a_3191_;
v_snd_3196_ = v_snd_3193_;
v_err_3197_ = v___x_3206_;
goto v___jp_3194_;
}
else
{
lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3216_; 
lean_inc(v_fst_3192_);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_a_3191_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; lean_object* v_unused_3218_; 
v_unused_3217_ = lean_ctor_get(v_a_3191_, 1);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_a_3191_, 0);
lean_dec(v_unused_3218_);
v___x_3208_ = v_a_3191_;
v_isShared_3209_ = v_isSharedCheck_3216_;
goto v_resetjp_3207_;
}
else
{
lean_dec(v_a_3191_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3216_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v_it_x27_3212_; 
v___x_3210_ = lean_string_utf8_next_fast(v_fst_3192_, v_snd_3193_);
lean_dec(v_snd_3193_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___x_3210_);
v_it_x27_3212_ = v___x_3208_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_fst_3192_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3210_);
v_it_x27_3212_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3213_; 
v___x_3213_ = lean_string_push(v_acc_3190_, v___x_3203_);
v_acc_3190_ = v___x_3213_;
v_a_3191_ = v_it_x27_3212_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3219_; 
v___x_3219_ = lean_box(0);
lean_inc(v_snd_3193_);
v_pos_3195_ = v_a_3191_;
v_snd_3196_ = v_snd_3193_;
v_err_3197_ = v___x_3219_;
goto v___jp_3194_;
}
v___jp_3194_:
{
uint8_t v___x_3198_; 
v___x_3198_ = lean_nat_dec_eq(v_snd_3193_, v_snd_3196_);
lean_dec(v_snd_3196_);
lean_dec(v_snd_3193_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; 
lean_dec_ref(v_acc_3190_);
lean_inc(v_err_3197_);
v___x_3199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_pos_3195_);
lean_ctor_set(v___x_3199_, 1, v_err_3197_);
return v___x_3199_;
}
else
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v_pos_3195_);
lean_ctor_set(v___x_3200_, 1, v_acc_3190_);
return v___x_3200_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0(void){
_start:
{
uint32_t v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3220_ = 71;
v___x_3221_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3222_ = lean_string_push(v___x_3221_, v___x_3220_);
return v___x_3222_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0);
v___x_3224_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3225_ = lean_string_append(v___x_3224_, v___x_3223_);
return v___x_3225_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3227_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1);
v___x_3228_ = lean_string_append(v___x_3227_, v___x_3226_);
return v___x_3228_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2);
v___x_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(lean_object* v_acc_3231_, lean_object* v_a_3232_){
_start:
{
lean_object* v_fst_3233_; lean_object* v_snd_3234_; lean_object* v_pos_3236_; lean_object* v_snd_3237_; lean_object* v_err_3238_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v_fst_3233_ = lean_ctor_get(v_a_3232_, 0);
v_snd_3234_ = lean_ctor_get(v_a_3232_, 1);
lean_inc(v_snd_3234_);
v___x_3242_ = lean_string_utf8_byte_size(v_fst_3233_);
v___x_3243_ = lean_nat_dec_eq(v_snd_3234_, v___x_3242_);
if (v___x_3243_ == 0)
{
uint32_t v___x_3244_; uint32_t v_c_3245_; uint8_t v___x_3246_; 
v___x_3244_ = 71;
v_c_3245_ = lean_string_utf8_get_fast(v_fst_3233_, v_snd_3234_);
v___x_3246_ = lean_uint32_dec_eq(v_c_3245_, v___x_3244_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3);
lean_inc(v_snd_3234_);
v_pos_3236_ = v_a_3232_;
v_snd_3237_ = v_snd_3234_;
v_err_3238_ = v___x_3247_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3257_; 
lean_inc(v_fst_3233_);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_a_3232_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; lean_object* v_unused_3259_; 
v_unused_3258_ = lean_ctor_get(v_a_3232_, 1);
lean_dec(v_unused_3258_);
v_unused_3259_ = lean_ctor_get(v_a_3232_, 0);
lean_dec(v_unused_3259_);
v___x_3249_ = v_a_3232_;
v_isShared_3250_ = v_isSharedCheck_3257_;
goto v_resetjp_3248_;
}
else
{
lean_dec(v_a_3232_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3257_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v_it_x27_3253_; 
v___x_3251_ = lean_string_utf8_next_fast(v_fst_3233_, v_snd_3234_);
lean_dec(v_snd_3234_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v___x_3251_);
v_it_x27_3253_ = v___x_3249_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_fst_3233_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3251_);
v_it_x27_3253_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_string_push(v_acc_3231_, v___x_3244_);
v_acc_3231_ = v___x_3254_;
v_a_3232_ = v_it_x27_3253_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3260_; 
v___x_3260_ = lean_box(0);
lean_inc(v_snd_3234_);
v_pos_3236_ = v_a_3232_;
v_snd_3237_ = v_snd_3234_;
v_err_3238_ = v___x_3260_;
goto v___jp_3235_;
}
v___jp_3235_:
{
uint8_t v___x_3239_; 
v___x_3239_ = lean_nat_dec_eq(v_snd_3234_, v_snd_3237_);
lean_dec(v_snd_3237_);
lean_dec(v_snd_3234_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; 
lean_dec_ref(v_acc_3231_);
lean_inc(v_err_3238_);
v___x_3240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3240_, 0, v_pos_3236_);
lean_ctor_set(v___x_3240_, 1, v_err_3238_);
return v___x_3240_;
}
else
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v_pos_3236_);
lean_ctor_set(v___x_3241_, 1, v_acc_3231_);
return v___x_3241_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0(void){
_start:
{
uint32_t v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3261_ = 86;
v___x_3262_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3263_ = lean_string_push(v___x_3262_, v___x_3261_);
return v___x_3263_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3264_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0);
v___x_3265_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3266_ = lean_string_append(v___x_3265_, v___x_3264_);
return v___x_3266_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3268_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1);
v___x_3269_ = lean_string_append(v___x_3268_, v___x_3267_);
return v___x_3269_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2);
v___x_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(lean_object* v_acc_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v_fst_3274_; lean_object* v_snd_3275_; lean_object* v_pos_3277_; lean_object* v_snd_3278_; lean_object* v_err_3279_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v_fst_3274_ = lean_ctor_get(v_a_3273_, 0);
v_snd_3275_ = lean_ctor_get(v_a_3273_, 1);
lean_inc(v_snd_3275_);
v___x_3283_ = lean_string_utf8_byte_size(v_fst_3274_);
v___x_3284_ = lean_nat_dec_eq(v_snd_3275_, v___x_3283_);
if (v___x_3284_ == 0)
{
uint32_t v___x_3285_; uint32_t v_c_3286_; uint8_t v___x_3287_; 
v___x_3285_ = 86;
v_c_3286_ = lean_string_utf8_get_fast(v_fst_3274_, v_snd_3275_);
v___x_3287_ = lean_uint32_dec_eq(v_c_3286_, v___x_3285_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; 
v___x_3288_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3);
lean_inc(v_snd_3275_);
v_pos_3277_ = v_a_3273_;
v_snd_3278_ = v_snd_3275_;
v_err_3279_ = v___x_3288_;
goto v___jp_3276_;
}
else
{
lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3298_; 
lean_inc(v_fst_3274_);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_a_3273_);
if (v_isSharedCheck_3298_ == 0)
{
lean_object* v_unused_3299_; lean_object* v_unused_3300_; 
v_unused_3299_ = lean_ctor_get(v_a_3273_, 1);
lean_dec(v_unused_3299_);
v_unused_3300_ = lean_ctor_get(v_a_3273_, 0);
lean_dec(v_unused_3300_);
v___x_3290_ = v_a_3273_;
v_isShared_3291_ = v_isSharedCheck_3298_;
goto v_resetjp_3289_;
}
else
{
lean_dec(v_a_3273_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3298_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; lean_object* v_it_x27_3294_; 
v___x_3292_ = lean_string_utf8_next_fast(v_fst_3274_, v_snd_3275_);
lean_dec(v_snd_3275_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 1, v___x_3292_);
v_it_x27_3294_ = v___x_3290_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_fst_3274_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v___x_3292_);
v_it_x27_3294_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3295_; 
v___x_3295_ = lean_string_push(v_acc_3272_, v___x_3285_);
v_acc_3272_ = v___x_3295_;
v_a_3273_ = v_it_x27_3294_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3301_; 
v___x_3301_ = lean_box(0);
lean_inc(v_snd_3275_);
v_pos_3277_ = v_a_3273_;
v_snd_3278_ = v_snd_3275_;
v_err_3279_ = v___x_3301_;
goto v___jp_3276_;
}
v___jp_3276_:
{
uint8_t v___x_3280_; 
v___x_3280_ = lean_nat_dec_eq(v_snd_3275_, v_snd_3278_);
lean_dec(v_snd_3278_);
lean_dec(v_snd_3275_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; 
lean_dec_ref(v_acc_3272_);
lean_inc(v_err_3279_);
v___x_3281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3281_, 0, v_pos_3277_);
lean_ctor_set(v___x_3281_, 1, v_err_3279_);
return v___x_3281_;
}
else
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3282_, 0, v_pos_3277_);
lean_ctor_set(v___x_3282_, 1, v_acc_3272_);
return v___x_3282_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0(void){
_start:
{
uint32_t v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = 83;
v___x_3303_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3304_ = lean_string_push(v___x_3303_, v___x_3302_);
return v___x_3304_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0);
v___x_3306_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3307_ = lean_string_append(v___x_3306_, v___x_3305_);
return v___x_3307_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3309_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1);
v___x_3310_ = lean_string_append(v___x_3309_, v___x_3308_);
return v___x_3310_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2);
v___x_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(lean_object* v_acc_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v_fst_3315_; lean_object* v_snd_3316_; lean_object* v_pos_3318_; lean_object* v_snd_3319_; lean_object* v_err_3320_; lean_object* v___x_3324_; uint8_t v___x_3325_; 
v_fst_3315_ = lean_ctor_get(v_a_3314_, 0);
v_snd_3316_ = lean_ctor_get(v_a_3314_, 1);
lean_inc(v_snd_3316_);
v___x_3324_ = lean_string_utf8_byte_size(v_fst_3315_);
v___x_3325_ = lean_nat_dec_eq(v_snd_3316_, v___x_3324_);
if (v___x_3325_ == 0)
{
uint32_t v___x_3326_; uint32_t v_c_3327_; uint8_t v___x_3328_; 
v___x_3326_ = 83;
v_c_3327_ = lean_string_utf8_get_fast(v_fst_3315_, v_snd_3316_);
v___x_3328_ = lean_uint32_dec_eq(v_c_3327_, v___x_3326_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; 
v___x_3329_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3);
lean_inc(v_snd_3316_);
v_pos_3318_ = v_a_3314_;
v_snd_3319_ = v_snd_3316_;
v_err_3320_ = v___x_3329_;
goto v___jp_3317_;
}
else
{
lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3339_; 
lean_inc(v_fst_3315_);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_a_3314_);
if (v_isSharedCheck_3339_ == 0)
{
lean_object* v_unused_3340_; lean_object* v_unused_3341_; 
v_unused_3340_ = lean_ctor_get(v_a_3314_, 1);
lean_dec(v_unused_3340_);
v_unused_3341_ = lean_ctor_get(v_a_3314_, 0);
lean_dec(v_unused_3341_);
v___x_3331_ = v_a_3314_;
v_isShared_3332_ = v_isSharedCheck_3339_;
goto v_resetjp_3330_;
}
else
{
lean_dec(v_a_3314_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3339_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v_it_x27_3335_; 
v___x_3333_ = lean_string_utf8_next_fast(v_fst_3315_, v_snd_3316_);
lean_dec(v_snd_3316_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 1, v___x_3333_);
v_it_x27_3335_ = v___x_3331_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_fst_3315_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v___x_3333_);
v_it_x27_3335_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; 
v___x_3336_ = lean_string_push(v_acc_3313_, v___x_3326_);
v_acc_3313_ = v___x_3336_;
v_a_3314_ = v_it_x27_3335_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3342_; 
v___x_3342_ = lean_box(0);
lean_inc(v_snd_3316_);
v_pos_3318_ = v_a_3314_;
v_snd_3319_ = v_snd_3316_;
v_err_3320_ = v___x_3342_;
goto v___jp_3317_;
}
v___jp_3317_:
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_nat_dec_eq(v_snd_3316_, v_snd_3319_);
lean_dec(v_snd_3319_);
lean_dec(v_snd_3316_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; 
lean_dec_ref(v_acc_3313_);
lean_inc(v_err_3320_);
v___x_3322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3322_, 0, v_pos_3318_);
lean_ctor_set(v___x_3322_, 1, v_err_3320_);
return v___x_3322_;
}
else
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v_pos_3318_);
lean_ctor_set(v___x_3323_, 1, v_acc_3313_);
return v___x_3323_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0(void){
_start:
{
uint32_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3343_ = 104;
v___x_3344_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3345_ = lean_string_push(v___x_3344_, v___x_3343_);
return v___x_3345_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0);
v___x_3347_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3348_ = lean_string_append(v___x_3347_, v___x_3346_);
return v___x_3348_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3350_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1);
v___x_3351_ = lean_string_append(v___x_3350_, v___x_3349_);
return v___x_3351_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2);
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(lean_object* v_acc_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_fst_3356_; lean_object* v_snd_3357_; lean_object* v_pos_3359_; lean_object* v_snd_3360_; lean_object* v_err_3361_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v_fst_3356_ = lean_ctor_get(v_a_3355_, 0);
v_snd_3357_ = lean_ctor_get(v_a_3355_, 1);
lean_inc(v_snd_3357_);
v___x_3365_ = lean_string_utf8_byte_size(v_fst_3356_);
v___x_3366_ = lean_nat_dec_eq(v_snd_3357_, v___x_3365_);
if (v___x_3366_ == 0)
{
uint32_t v___x_3367_; uint32_t v_c_3368_; uint8_t v___x_3369_; 
v___x_3367_ = 104;
v_c_3368_ = lean_string_utf8_get_fast(v_fst_3356_, v_snd_3357_);
v___x_3369_ = lean_uint32_dec_eq(v_c_3368_, v___x_3367_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3);
lean_inc(v_snd_3357_);
v_pos_3359_ = v_a_3355_;
v_snd_3360_ = v_snd_3357_;
v_err_3361_ = v___x_3370_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3380_; 
lean_inc(v_fst_3356_);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_a_3355_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; lean_object* v_unused_3382_; 
v_unused_3381_ = lean_ctor_get(v_a_3355_, 1);
lean_dec(v_unused_3381_);
v_unused_3382_ = lean_ctor_get(v_a_3355_, 0);
lean_dec(v_unused_3382_);
v___x_3372_ = v_a_3355_;
v_isShared_3373_ = v_isSharedCheck_3380_;
goto v_resetjp_3371_;
}
else
{
lean_dec(v_a_3355_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3380_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; lean_object* v_it_x27_3376_; 
v___x_3374_ = lean_string_utf8_next_fast(v_fst_3356_, v_snd_3357_);
lean_dec(v_snd_3357_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 1, v___x_3374_);
v_it_x27_3376_ = v___x_3372_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_fst_3356_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v___x_3374_);
v_it_x27_3376_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_string_push(v_acc_3354_, v___x_3367_);
v_acc_3354_ = v___x_3377_;
v_a_3355_ = v_it_x27_3376_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3383_; 
v___x_3383_ = lean_box(0);
lean_inc(v_snd_3357_);
v_pos_3359_ = v_a_3355_;
v_snd_3360_ = v_snd_3357_;
v_err_3361_ = v___x_3383_;
goto v___jp_3358_;
}
v___jp_3358_:
{
uint8_t v___x_3362_; 
v___x_3362_ = lean_nat_dec_eq(v_snd_3357_, v_snd_3360_);
lean_dec(v_snd_3360_);
lean_dec(v_snd_3357_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; 
lean_dec_ref(v_acc_3354_);
lean_inc(v_err_3361_);
v___x_3363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3363_, 0, v_pos_3359_);
lean_ctor_set(v___x_3363_, 1, v_err_3361_);
return v___x_3363_;
}
else
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v_pos_3359_);
lean_ctor_set(v___x_3364_, 1, v_acc_3354_);
return v___x_3364_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0(void){
_start:
{
uint32_t v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3384_ = 81;
v___x_3385_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3386_ = lean_string_push(v___x_3385_, v___x_3384_);
return v___x_3386_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0);
v___x_3388_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3389_ = lean_string_append(v___x_3388_, v___x_3387_);
return v___x_3389_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3391_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1);
v___x_3392_ = lean_string_append(v___x_3391_, v___x_3390_);
return v___x_3392_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2);
v___x_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(lean_object* v_acc_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v_fst_3397_; lean_object* v_snd_3398_; lean_object* v_pos_3400_; lean_object* v_snd_3401_; lean_object* v_err_3402_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v_fst_3397_ = lean_ctor_get(v_a_3396_, 0);
v_snd_3398_ = lean_ctor_get(v_a_3396_, 1);
lean_inc(v_snd_3398_);
v___x_3406_ = lean_string_utf8_byte_size(v_fst_3397_);
v___x_3407_ = lean_nat_dec_eq(v_snd_3398_, v___x_3406_);
if (v___x_3407_ == 0)
{
uint32_t v___x_3408_; uint32_t v_c_3409_; uint8_t v___x_3410_; 
v___x_3408_ = 81;
v_c_3409_ = lean_string_utf8_get_fast(v_fst_3397_, v_snd_3398_);
v___x_3410_ = lean_uint32_dec_eq(v_c_3409_, v___x_3408_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3);
lean_inc(v_snd_3398_);
v_pos_3400_ = v_a_3396_;
v_snd_3401_ = v_snd_3398_;
v_err_3402_ = v___x_3411_;
goto v___jp_3399_;
}
else
{
lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3421_; 
lean_inc(v_fst_3397_);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_a_3396_);
if (v_isSharedCheck_3421_ == 0)
{
lean_object* v_unused_3422_; lean_object* v_unused_3423_; 
v_unused_3422_ = lean_ctor_get(v_a_3396_, 1);
lean_dec(v_unused_3422_);
v_unused_3423_ = lean_ctor_get(v_a_3396_, 0);
lean_dec(v_unused_3423_);
v___x_3413_ = v_a_3396_;
v_isShared_3414_ = v_isSharedCheck_3421_;
goto v_resetjp_3412_;
}
else
{
lean_dec(v_a_3396_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3421_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v_it_x27_3417_; 
v___x_3415_ = lean_string_utf8_next_fast(v_fst_3397_, v_snd_3398_);
lean_dec(v_snd_3398_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 1, v___x_3415_);
v_it_x27_3417_ = v___x_3413_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_fst_3397_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v___x_3415_);
v_it_x27_3417_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_string_push(v_acc_3395_, v___x_3408_);
v_acc_3395_ = v___x_3418_;
v_a_3396_ = v_it_x27_3417_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_box(0);
lean_inc(v_snd_3398_);
v_pos_3400_ = v_a_3396_;
v_snd_3401_ = v_snd_3398_;
v_err_3402_ = v___x_3424_;
goto v___jp_3399_;
}
v___jp_3399_:
{
uint8_t v___x_3403_; 
v___x_3403_ = lean_nat_dec_eq(v_snd_3398_, v_snd_3401_);
lean_dec(v_snd_3401_);
lean_dec(v_snd_3398_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
lean_dec_ref(v_acc_3395_);
lean_inc(v_err_3402_);
v___x_3404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3404_, 0, v_pos_3400_);
lean_ctor_set(v___x_3404_, 1, v_err_3402_);
return v___x_3404_;
}
else
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v_pos_3400_);
lean_ctor_set(v___x_3405_, 1, v_acc_3395_);
return v___x_3405_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0(void){
_start:
{
uint32_t v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = 68;
v___x_3426_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3427_ = lean_string_push(v___x_3426_, v___x_3425_);
return v___x_3427_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3428_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0);
v___x_3429_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3430_ = lean_string_append(v___x_3429_, v___x_3428_);
return v___x_3430_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2(void){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3431_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3432_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1);
v___x_3433_ = lean_string_append(v___x_3432_, v___x_3431_);
return v___x_3433_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3(void){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2);
v___x_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(lean_object* v_acc_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v_fst_3438_; lean_object* v_snd_3439_; lean_object* v_pos_3441_; lean_object* v_snd_3442_; lean_object* v_err_3443_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v_fst_3438_ = lean_ctor_get(v_a_3437_, 0);
v_snd_3439_ = lean_ctor_get(v_a_3437_, 1);
lean_inc(v_snd_3439_);
v___x_3447_ = lean_string_utf8_byte_size(v_fst_3438_);
v___x_3448_ = lean_nat_dec_eq(v_snd_3439_, v___x_3447_);
if (v___x_3448_ == 0)
{
uint32_t v___x_3449_; uint32_t v_c_3450_; uint8_t v___x_3451_; 
v___x_3449_ = 68;
v_c_3450_ = lean_string_utf8_get_fast(v_fst_3438_, v_snd_3439_);
v___x_3451_ = lean_uint32_dec_eq(v_c_3450_, v___x_3449_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3);
lean_inc(v_snd_3439_);
v_pos_3441_ = v_a_3437_;
v_snd_3442_ = v_snd_3439_;
v_err_3443_ = v___x_3452_;
goto v___jp_3440_;
}
else
{
lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3462_; 
lean_inc(v_fst_3438_);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_a_3437_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; lean_object* v_unused_3464_; 
v_unused_3463_ = lean_ctor_get(v_a_3437_, 1);
lean_dec(v_unused_3463_);
v_unused_3464_ = lean_ctor_get(v_a_3437_, 0);
lean_dec(v_unused_3464_);
v___x_3454_ = v_a_3437_;
v_isShared_3455_ = v_isSharedCheck_3462_;
goto v_resetjp_3453_;
}
else
{
lean_dec(v_a_3437_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3462_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v_it_x27_3458_; 
v___x_3456_ = lean_string_utf8_next_fast(v_fst_3438_, v_snd_3439_);
lean_dec(v_snd_3439_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 1, v___x_3456_);
v_it_x27_3458_ = v___x_3454_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_fst_3438_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v___x_3456_);
v_it_x27_3458_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; 
v___x_3459_ = lean_string_push(v_acc_3436_, v___x_3449_);
v_acc_3436_ = v___x_3459_;
v_a_3437_ = v_it_x27_3458_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3465_; 
v___x_3465_ = lean_box(0);
lean_inc(v_snd_3439_);
v_pos_3441_ = v_a_3437_;
v_snd_3442_ = v_snd_3439_;
v_err_3443_ = v___x_3465_;
goto v___jp_3440_;
}
v___jp_3440_:
{
uint8_t v___x_3444_; 
v___x_3444_ = lean_nat_dec_eq(v_snd_3439_, v_snd_3442_);
lean_dec(v_snd_3442_);
lean_dec(v_snd_3439_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; 
lean_dec_ref(v_acc_3436_);
lean_inc(v_err_3443_);
v___x_3445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3445_, 0, v_pos_3441_);
lean_ctor_set(v___x_3445_, 1, v_err_3443_);
return v___x_3445_;
}
else
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_pos_3441_);
lean_ctor_set(v___x_3446_, 1, v_acc_3436_);
return v___x_3446_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0(void){
_start:
{
uint32_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = 88;
v___x_3467_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3468_ = lean_string_push(v___x_3467_, v___x_3466_);
return v___x_3468_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0);
v___x_3470_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3471_ = lean_string_append(v___x_3470_, v___x_3469_);
return v___x_3471_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3472_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3473_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1);
v___x_3474_ = lean_string_append(v___x_3473_, v___x_3472_);
return v___x_3474_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2);
v___x_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(lean_object* v_acc_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v_fst_3479_; lean_object* v_snd_3480_; lean_object* v_pos_3482_; lean_object* v_snd_3483_; lean_object* v_err_3484_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v_fst_3479_ = lean_ctor_get(v_a_3478_, 0);
v_snd_3480_ = lean_ctor_get(v_a_3478_, 1);
lean_inc(v_snd_3480_);
v___x_3488_ = lean_string_utf8_byte_size(v_fst_3479_);
v___x_3489_ = lean_nat_dec_eq(v_snd_3480_, v___x_3488_);
if (v___x_3489_ == 0)
{
uint32_t v___x_3490_; uint32_t v_c_3491_; uint8_t v___x_3492_; 
v___x_3490_ = 88;
v_c_3491_ = lean_string_utf8_get_fast(v_fst_3479_, v_snd_3480_);
v___x_3492_ = lean_uint32_dec_eq(v_c_3491_, v___x_3490_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3);
lean_inc(v_snd_3480_);
v_pos_3482_ = v_a_3478_;
v_snd_3483_ = v_snd_3480_;
v_err_3484_ = v___x_3493_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3503_; 
lean_inc(v_fst_3479_);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_a_3478_);
if (v_isSharedCheck_3503_ == 0)
{
lean_object* v_unused_3504_; lean_object* v_unused_3505_; 
v_unused_3504_ = lean_ctor_get(v_a_3478_, 1);
lean_dec(v_unused_3504_);
v_unused_3505_ = lean_ctor_get(v_a_3478_, 0);
lean_dec(v_unused_3505_);
v___x_3495_ = v_a_3478_;
v_isShared_3496_ = v_isSharedCheck_3503_;
goto v_resetjp_3494_;
}
else
{
lean_dec(v_a_3478_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3503_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3497_; lean_object* v_it_x27_3499_; 
v___x_3497_ = lean_string_utf8_next_fast(v_fst_3479_, v_snd_3480_);
lean_dec(v_snd_3480_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 1, v___x_3497_);
v_it_x27_3499_ = v___x_3495_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_fst_3479_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v___x_3497_);
v_it_x27_3499_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; 
v___x_3500_ = lean_string_push(v_acc_3477_, v___x_3490_);
v_acc_3477_ = v___x_3500_;
v_a_3478_ = v_it_x27_3499_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_box(0);
lean_inc(v_snd_3480_);
v_pos_3482_ = v_a_3478_;
v_snd_3483_ = v_snd_3480_;
v_err_3484_ = v___x_3506_;
goto v___jp_3481_;
}
v___jp_3481_:
{
uint8_t v___x_3485_; 
v___x_3485_ = lean_nat_dec_eq(v_snd_3480_, v_snd_3483_);
lean_dec(v_snd_3483_);
lean_dec(v_snd_3480_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
lean_dec_ref(v_acc_3477_);
lean_inc(v_err_3484_);
v___x_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3486_, 0, v_pos_3482_);
lean_ctor_set(v___x_3486_, 1, v_err_3484_);
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v_pos_3482_);
lean_ctor_set(v___x_3487_, 1, v_acc_3477_);
return v___x_3487_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0(void){
_start:
{
uint32_t v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = 122;
v___x_3508_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3509_ = lean_string_push(v___x_3508_, v___x_3507_);
return v___x_3509_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0);
v___x_3511_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3512_ = lean_string_append(v___x_3511_, v___x_3510_);
return v___x_3512_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3514_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1);
v___x_3515_ = lean_string_append(v___x_3514_, v___x_3513_);
return v___x_3515_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2);
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(lean_object* v_acc_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_fst_3520_; lean_object* v_snd_3521_; lean_object* v_pos_3523_; lean_object* v_snd_3524_; lean_object* v_err_3525_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v_fst_3520_ = lean_ctor_get(v_a_3519_, 0);
v_snd_3521_ = lean_ctor_get(v_a_3519_, 1);
lean_inc(v_snd_3521_);
v___x_3529_ = lean_string_utf8_byte_size(v_fst_3520_);
v___x_3530_ = lean_nat_dec_eq(v_snd_3521_, v___x_3529_);
if (v___x_3530_ == 0)
{
uint32_t v___x_3531_; uint32_t v_c_3532_; uint8_t v___x_3533_; 
v___x_3531_ = 122;
v_c_3532_ = lean_string_utf8_get_fast(v_fst_3520_, v_snd_3521_);
v___x_3533_ = lean_uint32_dec_eq(v_c_3532_, v___x_3531_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3);
lean_inc(v_snd_3521_);
v_pos_3523_ = v_a_3519_;
v_snd_3524_ = v_snd_3521_;
v_err_3525_ = v___x_3534_;
goto v___jp_3522_;
}
else
{
lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3544_; 
lean_inc(v_fst_3520_);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_a_3519_);
if (v_isSharedCheck_3544_ == 0)
{
lean_object* v_unused_3545_; lean_object* v_unused_3546_; 
v_unused_3545_ = lean_ctor_get(v_a_3519_, 1);
lean_dec(v_unused_3545_);
v_unused_3546_ = lean_ctor_get(v_a_3519_, 0);
lean_dec(v_unused_3546_);
v___x_3536_ = v_a_3519_;
v_isShared_3537_ = v_isSharedCheck_3544_;
goto v_resetjp_3535_;
}
else
{
lean_dec(v_a_3519_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3544_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v_it_x27_3540_; 
v___x_3538_ = lean_string_utf8_next_fast(v_fst_3520_, v_snd_3521_);
lean_dec(v_snd_3521_);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 1, v___x_3538_);
v_it_x27_3540_ = v___x_3536_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_fst_3520_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3538_);
v_it_x27_3540_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v___x_3541_; 
v___x_3541_ = lean_string_push(v_acc_3518_, v___x_3531_);
v_acc_3518_ = v___x_3541_;
v_a_3519_ = v_it_x27_3540_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3547_; 
v___x_3547_ = lean_box(0);
lean_inc(v_snd_3521_);
v_pos_3523_ = v_a_3519_;
v_snd_3524_ = v_snd_3521_;
v_err_3525_ = v___x_3547_;
goto v___jp_3522_;
}
v___jp_3522_:
{
uint8_t v___x_3526_; 
v___x_3526_ = lean_nat_dec_eq(v_snd_3521_, v_snd_3524_);
lean_dec(v_snd_3524_);
lean_dec(v_snd_3521_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; 
lean_dec_ref(v_acc_3518_);
lean_inc(v_err_3525_);
v___x_3527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3527_, 0, v_pos_3523_);
lean_ctor_set(v___x_3527_, 1, v_err_3525_);
return v___x_3527_;
}
else
{
lean_object* v___x_3528_; 
v___x_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3528_, 0, v_pos_3523_);
lean_ctor_set(v___x_3528_, 1, v_acc_3518_);
return v___x_3528_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0(void){
_start:
{
uint32_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = 115;
v___x_3549_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3550_ = lean_string_push(v___x_3549_, v___x_3548_);
return v___x_3550_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0);
v___x_3552_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3553_ = lean_string_append(v___x_3552_, v___x_3551_);
return v___x_3553_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3555_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1);
v___x_3556_ = lean_string_append(v___x_3555_, v___x_3554_);
return v___x_3556_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(lean_object* v_acc_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v_fst_3561_; lean_object* v_snd_3562_; lean_object* v_pos_3564_; lean_object* v_snd_3565_; lean_object* v_err_3566_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_fst_3561_ = lean_ctor_get(v_a_3560_, 0);
v_snd_3562_ = lean_ctor_get(v_a_3560_, 1);
lean_inc(v_snd_3562_);
v___x_3570_ = lean_string_utf8_byte_size(v_fst_3561_);
v___x_3571_ = lean_nat_dec_eq(v_snd_3562_, v___x_3570_);
if (v___x_3571_ == 0)
{
uint32_t v___x_3572_; uint32_t v_c_3573_; uint8_t v___x_3574_; 
v___x_3572_ = 115;
v_c_3573_ = lean_string_utf8_get_fast(v_fst_3561_, v_snd_3562_);
v___x_3574_ = lean_uint32_dec_eq(v_c_3573_, v___x_3572_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; 
v___x_3575_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3);
lean_inc(v_snd_3562_);
v_pos_3564_ = v_a_3560_;
v_snd_3565_ = v_snd_3562_;
v_err_3566_ = v___x_3575_;
goto v___jp_3563_;
}
else
{
lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3585_; 
lean_inc(v_fst_3561_);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_a_3560_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; lean_object* v_unused_3587_; 
v_unused_3586_ = lean_ctor_get(v_a_3560_, 1);
lean_dec(v_unused_3586_);
v_unused_3587_ = lean_ctor_get(v_a_3560_, 0);
lean_dec(v_unused_3587_);
v___x_3577_ = v_a_3560_;
v_isShared_3578_ = v_isSharedCheck_3585_;
goto v_resetjp_3576_;
}
else
{
lean_dec(v_a_3560_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3585_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v_it_x27_3581_; 
v___x_3579_ = lean_string_utf8_next_fast(v_fst_3561_, v_snd_3562_);
lean_dec(v_snd_3562_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 1, v___x_3579_);
v_it_x27_3581_ = v___x_3577_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_fst_3561_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3579_);
v_it_x27_3581_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; 
v___x_3582_ = lean_string_push(v_acc_3559_, v___x_3572_);
v_acc_3559_ = v___x_3582_;
v_a_3560_ = v_it_x27_3581_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3588_; 
v___x_3588_ = lean_box(0);
lean_inc(v_snd_3562_);
v_pos_3564_ = v_a_3560_;
v_snd_3565_ = v_snd_3562_;
v_err_3566_ = v___x_3588_;
goto v___jp_3563_;
}
v___jp_3563_:
{
uint8_t v___x_3567_; 
v___x_3567_ = lean_nat_dec_eq(v_snd_3562_, v_snd_3565_);
lean_dec(v_snd_3565_);
lean_dec(v_snd_3562_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; 
lean_dec_ref(v_acc_3559_);
lean_inc(v_err_3566_);
v___x_3568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3568_, 0, v_pos_3564_);
lean_ctor_set(v___x_3568_, 1, v_err_3566_);
return v___x_3568_;
}
else
{
lean_object* v___x_3569_; 
v___x_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3569_, 0, v_pos_3564_);
lean_ctor_set(v___x_3569_, 1, v_acc_3559_);
return v___x_3569_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0(void){
_start:
{
uint32_t v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3589_ = 75;
v___x_3590_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3591_ = lean_string_push(v___x_3590_, v___x_3589_);
return v___x_3591_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1(void){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3592_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0);
v___x_3593_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3594_ = lean_string_append(v___x_3593_, v___x_3592_);
return v___x_3594_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2(void){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3596_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1);
v___x_3597_ = lean_string_append(v___x_3596_, v___x_3595_);
return v___x_3597_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3(void){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2);
v___x_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(lean_object* v_acc_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v_fst_3602_; lean_object* v_snd_3603_; lean_object* v_pos_3605_; lean_object* v_snd_3606_; lean_object* v_err_3607_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v_fst_3602_ = lean_ctor_get(v_a_3601_, 0);
v_snd_3603_ = lean_ctor_get(v_a_3601_, 1);
lean_inc(v_snd_3603_);
v___x_3611_ = lean_string_utf8_byte_size(v_fst_3602_);
v___x_3612_ = lean_nat_dec_eq(v_snd_3603_, v___x_3611_);
if (v___x_3612_ == 0)
{
uint32_t v___x_3613_; uint32_t v_c_3614_; uint8_t v___x_3615_; 
v___x_3613_ = 75;
v_c_3614_ = lean_string_utf8_get_fast(v_fst_3602_, v_snd_3603_);
v___x_3615_ = lean_uint32_dec_eq(v_c_3614_, v___x_3613_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3);
lean_inc(v_snd_3603_);
v_pos_3605_ = v_a_3601_;
v_snd_3606_ = v_snd_3603_;
v_err_3607_ = v___x_3616_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3626_; 
lean_inc(v_fst_3602_);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_a_3601_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; lean_object* v_unused_3628_; 
v_unused_3627_ = lean_ctor_get(v_a_3601_, 1);
lean_dec(v_unused_3627_);
v_unused_3628_ = lean_ctor_get(v_a_3601_, 0);
lean_dec(v_unused_3628_);
v___x_3618_ = v_a_3601_;
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
else
{
lean_dec(v_a_3601_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; lean_object* v_it_x27_3622_; 
v___x_3620_ = lean_string_utf8_next_fast(v_fst_3602_, v_snd_3603_);
lean_dec(v_snd_3603_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 1, v___x_3620_);
v_it_x27_3622_ = v___x_3618_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_fst_3602_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v___x_3620_);
v_it_x27_3622_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3623_; 
v___x_3623_ = lean_string_push(v_acc_3600_, v___x_3613_);
v_acc_3600_ = v___x_3623_;
v_a_3601_ = v_it_x27_3622_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3629_; 
v___x_3629_ = lean_box(0);
lean_inc(v_snd_3603_);
v_pos_3605_ = v_a_3601_;
v_snd_3606_ = v_snd_3603_;
v_err_3607_ = v___x_3629_;
goto v___jp_3604_;
}
v___jp_3604_:
{
uint8_t v___x_3608_; 
v___x_3608_ = lean_nat_dec_eq(v_snd_3603_, v_snd_3606_);
lean_dec(v_snd_3606_);
lean_dec(v_snd_3603_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; 
lean_dec_ref(v_acc_3600_);
lean_inc(v_err_3607_);
v___x_3609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3609_, 0, v_pos_3605_);
lean_ctor_set(v___x_3609_, 1, v_err_3607_);
return v___x_3609_;
}
else
{
lean_object* v___x_3610_; 
v___x_3610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3610_, 0, v_pos_3605_);
lean_ctor_set(v___x_3610_, 1, v_acc_3600_);
return v___x_3610_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0(void){
_start:
{
uint32_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3630_ = 101;
v___x_3631_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3632_ = lean_string_push(v___x_3631_, v___x_3630_);
return v___x_3632_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0);
v___x_3634_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3635_ = lean_string_append(v___x_3634_, v___x_3633_);
return v___x_3635_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3636_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3637_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1);
v___x_3638_ = lean_string_append(v___x_3637_, v___x_3636_);
return v___x_3638_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2);
v___x_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(lean_object* v_acc_3641_, lean_object* v_a_3642_){
_start:
{
lean_object* v_fst_3643_; lean_object* v_snd_3644_; lean_object* v_pos_3646_; lean_object* v_snd_3647_; lean_object* v_err_3648_; lean_object* v___x_3652_; uint8_t v___x_3653_; 
v_fst_3643_ = lean_ctor_get(v_a_3642_, 0);
v_snd_3644_ = lean_ctor_get(v_a_3642_, 1);
lean_inc(v_snd_3644_);
v___x_3652_ = lean_string_utf8_byte_size(v_fst_3643_);
v___x_3653_ = lean_nat_dec_eq(v_snd_3644_, v___x_3652_);
if (v___x_3653_ == 0)
{
uint32_t v___x_3654_; uint32_t v_c_3655_; uint8_t v___x_3656_; 
v___x_3654_ = 101;
v_c_3655_ = lean_string_utf8_get_fast(v_fst_3643_, v_snd_3644_);
v___x_3656_ = lean_uint32_dec_eq(v_c_3655_, v___x_3654_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; 
v___x_3657_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3);
lean_inc(v_snd_3644_);
v_pos_3646_ = v_a_3642_;
v_snd_3647_ = v_snd_3644_;
v_err_3648_ = v___x_3657_;
goto v___jp_3645_;
}
else
{
lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3667_; 
lean_inc(v_fst_3643_);
v_isSharedCheck_3667_ = !lean_is_exclusive(v_a_3642_);
if (v_isSharedCheck_3667_ == 0)
{
lean_object* v_unused_3668_; lean_object* v_unused_3669_; 
v_unused_3668_ = lean_ctor_get(v_a_3642_, 1);
lean_dec(v_unused_3668_);
v_unused_3669_ = lean_ctor_get(v_a_3642_, 0);
lean_dec(v_unused_3669_);
v___x_3659_ = v_a_3642_;
v_isShared_3660_ = v_isSharedCheck_3667_;
goto v_resetjp_3658_;
}
else
{
lean_dec(v_a_3642_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3667_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; lean_object* v_it_x27_3663_; 
v___x_3661_ = lean_string_utf8_next_fast(v_fst_3643_, v_snd_3644_);
lean_dec(v_snd_3644_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 1, v___x_3661_);
v_it_x27_3663_ = v___x_3659_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_fst_3643_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v___x_3661_);
v_it_x27_3663_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; 
v___x_3664_ = lean_string_push(v_acc_3641_, v___x_3654_);
v_acc_3641_ = v___x_3664_;
v_a_3642_ = v_it_x27_3663_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_box(0);
lean_inc(v_snd_3644_);
v_pos_3646_ = v_a_3642_;
v_snd_3647_ = v_snd_3644_;
v_err_3648_ = v___x_3670_;
goto v___jp_3645_;
}
v___jp_3645_:
{
uint8_t v___x_3649_; 
v___x_3649_ = lean_nat_dec_eq(v_snd_3644_, v_snd_3647_);
lean_dec(v_snd_3647_);
lean_dec(v_snd_3644_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; 
lean_dec_ref(v_acc_3641_);
lean_inc(v_err_3648_);
v___x_3650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3650_, 0, v_pos_3646_);
lean_ctor_set(v___x_3650_, 1, v_err_3648_);
return v___x_3650_;
}
else
{
lean_object* v___x_3651_; 
v___x_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3651_, 0, v_pos_3646_);
lean_ctor_set(v___x_3651_, 1, v_acc_3641_);
return v___x_3651_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0(void){
_start:
{
uint32_t v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3671_ = 77;
v___x_3672_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3673_ = lean_string_push(v___x_3672_, v___x_3671_);
return v___x_3673_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3674_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0);
v___x_3675_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3676_ = lean_string_append(v___x_3675_, v___x_3674_);
return v___x_3676_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2(void){
_start:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3678_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1);
v___x_3679_ = lean_string_append(v___x_3678_, v___x_3677_);
return v___x_3679_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3(void){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2);
v___x_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(lean_object* v_acc_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v_fst_3684_; lean_object* v_snd_3685_; lean_object* v_pos_3687_; lean_object* v_snd_3688_; lean_object* v_err_3689_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v_fst_3684_ = lean_ctor_get(v_a_3683_, 0);
v_snd_3685_ = lean_ctor_get(v_a_3683_, 1);
lean_inc(v_snd_3685_);
v___x_3693_ = lean_string_utf8_byte_size(v_fst_3684_);
v___x_3694_ = lean_nat_dec_eq(v_snd_3685_, v___x_3693_);
if (v___x_3694_ == 0)
{
uint32_t v___x_3695_; uint32_t v_c_3696_; uint8_t v___x_3697_; 
v___x_3695_ = 77;
v_c_3696_ = lean_string_utf8_get_fast(v_fst_3684_, v_snd_3685_);
v___x_3697_ = lean_uint32_dec_eq(v_c_3696_, v___x_3695_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; 
v___x_3698_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3);
lean_inc(v_snd_3685_);
v_pos_3687_ = v_a_3683_;
v_snd_3688_ = v_snd_3685_;
v_err_3689_ = v___x_3698_;
goto v___jp_3686_;
}
else
{
lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3708_; 
lean_inc(v_fst_3684_);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_a_3683_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; lean_object* v_unused_3710_; 
v_unused_3709_ = lean_ctor_get(v_a_3683_, 1);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_a_3683_, 0);
lean_dec(v_unused_3710_);
v___x_3700_ = v_a_3683_;
v_isShared_3701_ = v_isSharedCheck_3708_;
goto v_resetjp_3699_;
}
else
{
lean_dec(v_a_3683_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3708_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3702_; lean_object* v_it_x27_3704_; 
v___x_3702_ = lean_string_utf8_next_fast(v_fst_3684_, v_snd_3685_);
lean_dec(v_snd_3685_);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 1, v___x_3702_);
v_it_x27_3704_ = v___x_3700_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_fst_3684_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v___x_3702_);
v_it_x27_3704_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_string_push(v_acc_3682_, v___x_3695_);
v_acc_3682_ = v___x_3705_;
v_a_3683_ = v_it_x27_3704_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_box(0);
lean_inc(v_snd_3685_);
v_pos_3687_ = v_a_3683_;
v_snd_3688_ = v_snd_3685_;
v_err_3689_ = v___x_3711_;
goto v___jp_3686_;
}
v___jp_3686_:
{
uint8_t v___x_3690_; 
v___x_3690_ = lean_nat_dec_eq(v_snd_3685_, v_snd_3688_);
lean_dec(v_snd_3688_);
lean_dec(v_snd_3685_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; 
lean_dec_ref(v_acc_3682_);
lean_inc(v_err_3689_);
v___x_3691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3691_, 0, v_pos_3687_);
lean_ctor_set(v___x_3691_, 1, v_err_3689_);
return v___x_3691_;
}
else
{
lean_object* v___x_3692_; 
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_pos_3687_);
lean_ctor_set(v___x_3692_, 1, v_acc_3682_);
return v___x_3692_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0(void){
_start:
{
uint32_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = 119;
v___x_3713_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3714_ = lean_string_push(v___x_3713_, v___x_3712_);
return v___x_3714_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0);
v___x_3716_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3717_ = lean_string_append(v___x_3716_, v___x_3715_);
return v___x_3717_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3719_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1);
v___x_3720_ = lean_string_append(v___x_3719_, v___x_3718_);
return v___x_3720_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2);
v___x_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(lean_object* v_acc_3723_, lean_object* v_a_3724_){
_start:
{
lean_object* v_fst_3725_; lean_object* v_snd_3726_; lean_object* v_pos_3728_; lean_object* v_snd_3729_; lean_object* v_err_3730_; lean_object* v___x_3734_; uint8_t v___x_3735_; 
v_fst_3725_ = lean_ctor_get(v_a_3724_, 0);
v_snd_3726_ = lean_ctor_get(v_a_3724_, 1);
lean_inc(v_snd_3726_);
v___x_3734_ = lean_string_utf8_byte_size(v_fst_3725_);
v___x_3735_ = lean_nat_dec_eq(v_snd_3726_, v___x_3734_);
if (v___x_3735_ == 0)
{
uint32_t v___x_3736_; uint32_t v_c_3737_; uint8_t v___x_3738_; 
v___x_3736_ = 119;
v_c_3737_ = lean_string_utf8_get_fast(v_fst_3725_, v_snd_3726_);
v___x_3738_ = lean_uint32_dec_eq(v_c_3737_, v___x_3736_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; 
v___x_3739_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3);
lean_inc(v_snd_3726_);
v_pos_3728_ = v_a_3724_;
v_snd_3729_ = v_snd_3726_;
v_err_3730_ = v___x_3739_;
goto v___jp_3727_;
}
else
{
lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3749_; 
lean_inc(v_fst_3725_);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_a_3724_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; lean_object* v_unused_3751_; 
v_unused_3750_ = lean_ctor_get(v_a_3724_, 1);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_a_3724_, 0);
lean_dec(v_unused_3751_);
v___x_3741_ = v_a_3724_;
v_isShared_3742_ = v_isSharedCheck_3749_;
goto v_resetjp_3740_;
}
else
{
lean_dec(v_a_3724_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3749_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3743_; lean_object* v_it_x27_3745_; 
v___x_3743_ = lean_string_utf8_next_fast(v_fst_3725_, v_snd_3726_);
lean_dec(v_snd_3726_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 1, v___x_3743_);
v_it_x27_3745_ = v___x_3741_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_fst_3725_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v___x_3743_);
v_it_x27_3745_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
lean_object* v___x_3746_; 
v___x_3746_ = lean_string_push(v_acc_3723_, v___x_3736_);
v_acc_3723_ = v___x_3746_;
v_a_3724_ = v_it_x27_3745_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_box(0);
lean_inc(v_snd_3726_);
v_pos_3728_ = v_a_3724_;
v_snd_3729_ = v_snd_3726_;
v_err_3730_ = v___x_3752_;
goto v___jp_3727_;
}
v___jp_3727_:
{
uint8_t v___x_3731_; 
v___x_3731_ = lean_nat_dec_eq(v_snd_3726_, v_snd_3729_);
lean_dec(v_snd_3729_);
lean_dec(v_snd_3726_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; 
lean_dec_ref(v_acc_3723_);
lean_inc(v_err_3730_);
v___x_3732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3732_, 0, v_pos_3728_);
lean_ctor_set(v___x_3732_, 1, v_err_3730_);
return v___x_3732_;
}
else
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v_pos_3728_);
lean_ctor_set(v___x_3733_, 1, v_acc_3723_);
return v___x_3733_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0(void){
_start:
{
uint32_t v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3753_ = 100;
v___x_3754_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3755_ = lean_string_push(v___x_3754_, v___x_3753_);
return v___x_3755_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1(void){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3756_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0);
v___x_3757_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3758_ = lean_string_append(v___x_3757_, v___x_3756_);
return v___x_3758_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2(void){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3759_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3760_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1);
v___x_3761_ = lean_string_append(v___x_3760_, v___x_3759_);
return v___x_3761_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2);
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(lean_object* v_acc_3764_, lean_object* v_a_3765_){
_start:
{
lean_object* v_fst_3766_; lean_object* v_snd_3767_; lean_object* v_pos_3769_; lean_object* v_snd_3770_; lean_object* v_err_3771_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v_fst_3766_ = lean_ctor_get(v_a_3765_, 0);
v_snd_3767_ = lean_ctor_get(v_a_3765_, 1);
lean_inc(v_snd_3767_);
v___x_3775_ = lean_string_utf8_byte_size(v_fst_3766_);
v___x_3776_ = lean_nat_dec_eq(v_snd_3767_, v___x_3775_);
if (v___x_3776_ == 0)
{
uint32_t v___x_3777_; uint32_t v_c_3778_; uint8_t v___x_3779_; 
v___x_3777_ = 100;
v_c_3778_ = lean_string_utf8_get_fast(v_fst_3766_, v_snd_3767_);
v___x_3779_ = lean_uint32_dec_eq(v_c_3778_, v___x_3777_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; 
v___x_3780_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3);
lean_inc(v_snd_3767_);
v_pos_3769_ = v_a_3765_;
v_snd_3770_ = v_snd_3767_;
v_err_3771_ = v___x_3780_;
goto v___jp_3768_;
}
else
{
lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3790_; 
lean_inc(v_fst_3766_);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_a_3765_);
if (v_isSharedCheck_3790_ == 0)
{
lean_object* v_unused_3791_; lean_object* v_unused_3792_; 
v_unused_3791_ = lean_ctor_get(v_a_3765_, 1);
lean_dec(v_unused_3791_);
v_unused_3792_ = lean_ctor_get(v_a_3765_, 0);
lean_dec(v_unused_3792_);
v___x_3782_ = v_a_3765_;
v_isShared_3783_ = v_isSharedCheck_3790_;
goto v_resetjp_3781_;
}
else
{
lean_dec(v_a_3765_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3790_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; lean_object* v_it_x27_3786_; 
v___x_3784_ = lean_string_utf8_next_fast(v_fst_3766_, v_snd_3767_);
lean_dec(v_snd_3767_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v___x_3784_);
v_it_x27_3786_ = v___x_3782_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_fst_3766_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v___x_3784_);
v_it_x27_3786_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3787_; 
v___x_3787_ = lean_string_push(v_acc_3764_, v___x_3777_);
v_acc_3764_ = v___x_3787_;
v_a_3765_ = v_it_x27_3786_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_box(0);
lean_inc(v_snd_3767_);
v_pos_3769_ = v_a_3765_;
v_snd_3770_ = v_snd_3767_;
v_err_3771_ = v___x_3793_;
goto v___jp_3768_;
}
v___jp_3768_:
{
uint8_t v___x_3772_; 
v___x_3772_ = lean_nat_dec_eq(v_snd_3767_, v_snd_3770_);
lean_dec(v_snd_3770_);
lean_dec(v_snd_3767_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; 
lean_dec_ref(v_acc_3764_);
lean_inc(v_err_3771_);
v___x_3773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3773_, 0, v_pos_3769_);
lean_ctor_set(v___x_3773_, 1, v_err_3771_);
return v___x_3773_;
}
else
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_pos_3769_);
lean_ctor_set(v___x_3774_, 1, v_acc_3764_);
return v___x_3774_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0(void){
_start:
{
uint32_t v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = 99;
v___x_3795_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3796_ = lean_string_push(v___x_3795_, v___x_3794_);
return v___x_3796_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3797_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0);
v___x_3798_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3799_ = lean_string_append(v___x_3798_, v___x_3797_);
return v___x_3799_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3800_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3801_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1);
v___x_3802_ = lean_string_append(v___x_3801_, v___x_3800_);
return v___x_3802_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2);
v___x_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(lean_object* v_acc_3805_, lean_object* v_a_3806_){
_start:
{
lean_object* v_fst_3807_; lean_object* v_snd_3808_; lean_object* v_pos_3810_; lean_object* v_snd_3811_; lean_object* v_err_3812_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_fst_3807_ = lean_ctor_get(v_a_3806_, 0);
v_snd_3808_ = lean_ctor_get(v_a_3806_, 1);
lean_inc(v_snd_3808_);
v___x_3816_ = lean_string_utf8_byte_size(v_fst_3807_);
v___x_3817_ = lean_nat_dec_eq(v_snd_3808_, v___x_3816_);
if (v___x_3817_ == 0)
{
uint32_t v___x_3818_; uint32_t v_c_3819_; uint8_t v___x_3820_; 
v___x_3818_ = 99;
v_c_3819_ = lean_string_utf8_get_fast(v_fst_3807_, v_snd_3808_);
v___x_3820_ = lean_uint32_dec_eq(v_c_3819_, v___x_3818_);
if (v___x_3820_ == 0)
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3);
lean_inc(v_snd_3808_);
v_pos_3810_ = v_a_3806_;
v_snd_3811_ = v_snd_3808_;
v_err_3812_ = v___x_3821_;
goto v___jp_3809_;
}
else
{
lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3831_; 
lean_inc(v_fst_3807_);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_a_3806_);
if (v_isSharedCheck_3831_ == 0)
{
lean_object* v_unused_3832_; lean_object* v_unused_3833_; 
v_unused_3832_ = lean_ctor_get(v_a_3806_, 1);
lean_dec(v_unused_3832_);
v_unused_3833_ = lean_ctor_get(v_a_3806_, 0);
lean_dec(v_unused_3833_);
v___x_3823_ = v_a_3806_;
v_isShared_3824_ = v_isSharedCheck_3831_;
goto v_resetjp_3822_;
}
else
{
lean_dec(v_a_3806_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3831_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3825_; lean_object* v_it_x27_3827_; 
v___x_3825_ = lean_string_utf8_next_fast(v_fst_3807_, v_snd_3808_);
lean_dec(v_snd_3808_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 1, v___x_3825_);
v_it_x27_3827_ = v___x_3823_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_fst_3807_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v___x_3825_);
v_it_x27_3827_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_string_push(v_acc_3805_, v___x_3818_);
v_acc_3805_ = v___x_3828_;
v_a_3806_ = v_it_x27_3827_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_box(0);
lean_inc(v_snd_3808_);
v_pos_3810_ = v_a_3806_;
v_snd_3811_ = v_snd_3808_;
v_err_3812_ = v___x_3834_;
goto v___jp_3809_;
}
v___jp_3809_:
{
uint8_t v___x_3813_; 
v___x_3813_ = lean_nat_dec_eq(v_snd_3808_, v_snd_3811_);
lean_dec(v_snd_3811_);
lean_dec(v_snd_3808_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; 
lean_dec_ref(v_acc_3805_);
lean_inc(v_err_3812_);
v___x_3814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3814_, 0, v_pos_3810_);
lean_ctor_set(v___x_3814_, 1, v_err_3812_);
return v___x_3814_;
}
else
{
lean_object* v___x_3815_; 
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v_pos_3810_);
lean_ctor_set(v___x_3815_, 1, v_acc_3805_);
return v___x_3815_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0(void){
_start:
{
uint32_t v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3835_ = 69;
v___x_3836_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3837_ = lean_string_push(v___x_3836_, v___x_3835_);
return v___x_3837_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1(void){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3838_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0);
v___x_3839_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3840_ = lean_string_append(v___x_3839_, v___x_3838_);
return v___x_3840_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2(void){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3841_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3842_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1);
v___x_3843_ = lean_string_append(v___x_3842_, v___x_3841_);
return v___x_3843_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3(void){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3844_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2);
v___x_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(lean_object* v_acc_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v_fst_3848_; lean_object* v_snd_3849_; lean_object* v_pos_3851_; lean_object* v_snd_3852_; lean_object* v_err_3853_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v_fst_3848_ = lean_ctor_get(v_a_3847_, 0);
v_snd_3849_ = lean_ctor_get(v_a_3847_, 1);
lean_inc(v_snd_3849_);
v___x_3857_ = lean_string_utf8_byte_size(v_fst_3848_);
v___x_3858_ = lean_nat_dec_eq(v_snd_3849_, v___x_3857_);
if (v___x_3858_ == 0)
{
uint32_t v___x_3859_; uint32_t v_c_3860_; uint8_t v___x_3861_; 
v___x_3859_ = 69;
v_c_3860_ = lean_string_utf8_get_fast(v_fst_3848_, v_snd_3849_);
v___x_3861_ = lean_uint32_dec_eq(v_c_3860_, v___x_3859_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3);
lean_inc(v_snd_3849_);
v_pos_3851_ = v_a_3847_;
v_snd_3852_ = v_snd_3849_;
v_err_3853_ = v___x_3862_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3872_; 
lean_inc(v_fst_3848_);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_a_3847_);
if (v_isSharedCheck_3872_ == 0)
{
lean_object* v_unused_3873_; lean_object* v_unused_3874_; 
v_unused_3873_ = lean_ctor_get(v_a_3847_, 1);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_a_3847_, 0);
lean_dec(v_unused_3874_);
v___x_3864_ = v_a_3847_;
v_isShared_3865_ = v_isSharedCheck_3872_;
goto v_resetjp_3863_;
}
else
{
lean_dec(v_a_3847_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3872_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3866_; lean_object* v_it_x27_3868_; 
v___x_3866_ = lean_string_utf8_next_fast(v_fst_3848_, v_snd_3849_);
lean_dec(v_snd_3849_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 1, v___x_3866_);
v_it_x27_3868_ = v___x_3864_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_fst_3848_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3866_);
v_it_x27_3868_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_string_push(v_acc_3846_, v___x_3859_);
v_acc_3846_ = v___x_3869_;
v_a_3847_ = v_it_x27_3868_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3875_; 
v___x_3875_ = lean_box(0);
lean_inc(v_snd_3849_);
v_pos_3851_ = v_a_3847_;
v_snd_3852_ = v_snd_3849_;
v_err_3853_ = v___x_3875_;
goto v___jp_3850_;
}
v___jp_3850_:
{
uint8_t v___x_3854_; 
v___x_3854_ = lean_nat_dec_eq(v_snd_3849_, v_snd_3852_);
lean_dec(v_snd_3852_);
lean_dec(v_snd_3849_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; 
lean_dec_ref(v_acc_3846_);
lean_inc(v_err_3853_);
v___x_3855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3855_, 0, v_pos_3851_);
lean_ctor_set(v___x_3855_, 1, v_err_3853_);
return v___x_3855_;
}
else
{
lean_object* v___x_3856_; 
v___x_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3856_, 0, v_pos_3851_);
lean_ctor_set(v___x_3856_, 1, v_acc_3846_);
return v___x_3856_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0(void){
_start:
{
uint32_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3876_ = 97;
v___x_3877_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3878_ = lean_string_push(v___x_3877_, v___x_3876_);
return v___x_3878_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0);
v___x_3880_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3881_ = lean_string_append(v___x_3880_, v___x_3879_);
return v___x_3881_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2(void){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3882_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3883_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1);
v___x_3884_ = lean_string_append(v___x_3883_, v___x_3882_);
return v___x_3884_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2);
v___x_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(lean_object* v_acc_3887_, lean_object* v_a_3888_){
_start:
{
lean_object* v_fst_3889_; lean_object* v_snd_3890_; lean_object* v_pos_3892_; lean_object* v_snd_3893_; lean_object* v_err_3894_; lean_object* v___x_3898_; uint8_t v___x_3899_; 
v_fst_3889_ = lean_ctor_get(v_a_3888_, 0);
v_snd_3890_ = lean_ctor_get(v_a_3888_, 1);
lean_inc(v_snd_3890_);
v___x_3898_ = lean_string_utf8_byte_size(v_fst_3889_);
v___x_3899_ = lean_nat_dec_eq(v_snd_3890_, v___x_3898_);
if (v___x_3899_ == 0)
{
uint32_t v___x_3900_; uint32_t v_c_3901_; uint8_t v___x_3902_; 
v___x_3900_ = 97;
v_c_3901_ = lean_string_utf8_get_fast(v_fst_3889_, v_snd_3890_);
v___x_3902_ = lean_uint32_dec_eq(v_c_3901_, v___x_3900_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; 
v___x_3903_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3);
lean_inc(v_snd_3890_);
v_pos_3892_ = v_a_3888_;
v_snd_3893_ = v_snd_3890_;
v_err_3894_ = v___x_3903_;
goto v___jp_3891_;
}
else
{
lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3913_; 
lean_inc(v_fst_3889_);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_a_3888_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; lean_object* v_unused_3915_; 
v_unused_3914_ = lean_ctor_get(v_a_3888_, 1);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_a_3888_, 0);
lean_dec(v_unused_3915_);
v___x_3905_ = v_a_3888_;
v_isShared_3906_ = v_isSharedCheck_3913_;
goto v_resetjp_3904_;
}
else
{
lean_dec(v_a_3888_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3913_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3907_; lean_object* v_it_x27_3909_; 
v___x_3907_ = lean_string_utf8_next_fast(v_fst_3889_, v_snd_3890_);
lean_dec(v_snd_3890_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 1, v___x_3907_);
v_it_x27_3909_ = v___x_3905_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_fst_3889_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v___x_3907_);
v_it_x27_3909_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_string_push(v_acc_3887_, v___x_3900_);
v_acc_3887_ = v___x_3910_;
v_a_3888_ = v_it_x27_3909_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3916_; 
v___x_3916_ = lean_box(0);
lean_inc(v_snd_3890_);
v_pos_3892_ = v_a_3888_;
v_snd_3893_ = v_snd_3890_;
v_err_3894_ = v___x_3916_;
goto v___jp_3891_;
}
v___jp_3891_:
{
uint8_t v___x_3895_; 
v___x_3895_ = lean_nat_dec_eq(v_snd_3890_, v_snd_3893_);
lean_dec(v_snd_3893_);
lean_dec(v_snd_3890_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; 
lean_dec_ref(v_acc_3887_);
lean_inc(v_err_3894_);
v___x_3896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3896_, 0, v_pos_3892_);
lean_ctor_set(v___x_3896_, 1, v_err_3894_);
return v___x_3896_;
}
else
{
lean_object* v___x_3897_; 
v___x_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3897_, 0, v_pos_3892_);
lean_ctor_set(v___x_3897_, 1, v_acc_3887_);
return v___x_3897_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0(void){
_start:
{
uint32_t v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = 79;
v___x_3918_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3919_ = lean_string_push(v___x_3918_, v___x_3917_);
return v___x_3919_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3920_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0);
v___x_3921_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3922_ = lean_string_append(v___x_3921_, v___x_3920_);
return v___x_3922_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3923_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3924_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1);
v___x_3925_ = lean_string_append(v___x_3924_, v___x_3923_);
return v___x_3925_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3926_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2);
v___x_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(lean_object* v_acc_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v_fst_3930_; lean_object* v_snd_3931_; lean_object* v_pos_3933_; lean_object* v_snd_3934_; lean_object* v_err_3935_; lean_object* v___x_3939_; uint8_t v___x_3940_; 
v_fst_3930_ = lean_ctor_get(v_a_3929_, 0);
v_snd_3931_ = lean_ctor_get(v_a_3929_, 1);
lean_inc(v_snd_3931_);
v___x_3939_ = lean_string_utf8_byte_size(v_fst_3930_);
v___x_3940_ = lean_nat_dec_eq(v_snd_3931_, v___x_3939_);
if (v___x_3940_ == 0)
{
uint32_t v___x_3941_; uint32_t v_c_3942_; uint8_t v___x_3943_; 
v___x_3941_ = 79;
v_c_3942_ = lean_string_utf8_get_fast(v_fst_3930_, v_snd_3931_);
v___x_3943_ = lean_uint32_dec_eq(v_c_3942_, v___x_3941_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; 
v___x_3944_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3);
lean_inc(v_snd_3931_);
v_pos_3933_ = v_a_3929_;
v_snd_3934_ = v_snd_3931_;
v_err_3935_ = v___x_3944_;
goto v___jp_3932_;
}
else
{
lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3954_; 
lean_inc(v_fst_3930_);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_a_3929_);
if (v_isSharedCheck_3954_ == 0)
{
lean_object* v_unused_3955_; lean_object* v_unused_3956_; 
v_unused_3955_ = lean_ctor_get(v_a_3929_, 1);
lean_dec(v_unused_3955_);
v_unused_3956_ = lean_ctor_get(v_a_3929_, 0);
lean_dec(v_unused_3956_);
v___x_3946_ = v_a_3929_;
v_isShared_3947_ = v_isSharedCheck_3954_;
goto v_resetjp_3945_;
}
else
{
lean_dec(v_a_3929_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3954_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3948_; lean_object* v_it_x27_3950_; 
v___x_3948_ = lean_string_utf8_next_fast(v_fst_3930_, v_snd_3931_);
lean_dec(v_snd_3931_);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 1, v___x_3948_);
v_it_x27_3950_ = v___x_3946_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_fst_3930_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v___x_3948_);
v_it_x27_3950_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3951_; 
v___x_3951_ = lean_string_push(v_acc_3928_, v___x_3941_);
v_acc_3928_ = v___x_3951_;
v_a_3929_ = v_it_x27_3950_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3957_; 
v___x_3957_ = lean_box(0);
lean_inc(v_snd_3931_);
v_pos_3933_ = v_a_3929_;
v_snd_3934_ = v_snd_3931_;
v_err_3935_ = v___x_3957_;
goto v___jp_3932_;
}
v___jp_3932_:
{
uint8_t v___x_3936_; 
v___x_3936_ = lean_nat_dec_eq(v_snd_3931_, v_snd_3934_);
lean_dec(v_snd_3934_);
lean_dec(v_snd_3931_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; 
lean_dec_ref(v_acc_3928_);
lean_inc(v_err_3935_);
v___x_3937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3937_, 0, v_pos_3933_);
lean_ctor_set(v___x_3937_, 1, v_err_3935_);
return v___x_3937_;
}
else
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3938_, 0, v_pos_3933_);
lean_ctor_set(v___x_3938_, 1, v_acc_3928_);
return v___x_3938_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0(void){
_start:
{
uint32_t v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3958_ = 65;
v___x_3959_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3960_ = lean_string_push(v___x_3959_, v___x_3958_);
return v___x_3960_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0);
v___x_3962_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3963_ = lean_string_append(v___x_3962_, v___x_3961_);
return v___x_3963_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2(void){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3964_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3965_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1);
v___x_3966_ = lean_string_append(v___x_3965_, v___x_3964_);
return v___x_3966_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3(void){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2);
v___x_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(lean_object* v_acc_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_fst_3971_; lean_object* v_snd_3972_; lean_object* v_pos_3974_; lean_object* v_snd_3975_; lean_object* v_err_3976_; lean_object* v___x_3980_; uint8_t v___x_3981_; 
v_fst_3971_ = lean_ctor_get(v_a_3970_, 0);
v_snd_3972_ = lean_ctor_get(v_a_3970_, 1);
lean_inc(v_snd_3972_);
v___x_3980_ = lean_string_utf8_byte_size(v_fst_3971_);
v___x_3981_ = lean_nat_dec_eq(v_snd_3972_, v___x_3980_);
if (v___x_3981_ == 0)
{
uint32_t v___x_3982_; uint32_t v_c_3983_; uint8_t v___x_3984_; 
v___x_3982_ = 65;
v_c_3983_ = lean_string_utf8_get_fast(v_fst_3971_, v_snd_3972_);
v___x_3984_ = lean_uint32_dec_eq(v_c_3983_, v___x_3982_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3985_; 
v___x_3985_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3);
lean_inc(v_snd_3972_);
v_pos_3974_ = v_a_3970_;
v_snd_3975_ = v_snd_3972_;
v_err_3976_ = v___x_3985_;
goto v___jp_3973_;
}
else
{
lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3995_; 
lean_inc(v_fst_3971_);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_a_3970_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; lean_object* v_unused_3997_; 
v_unused_3996_ = lean_ctor_get(v_a_3970_, 1);
lean_dec(v_unused_3996_);
v_unused_3997_ = lean_ctor_get(v_a_3970_, 0);
lean_dec(v_unused_3997_);
v___x_3987_ = v_a_3970_;
v_isShared_3988_ = v_isSharedCheck_3995_;
goto v_resetjp_3986_;
}
else
{
lean_dec(v_a_3970_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3995_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v_it_x27_3991_; 
v___x_3989_ = lean_string_utf8_next_fast(v_fst_3971_, v_snd_3972_);
lean_dec(v_snd_3972_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 1, v___x_3989_);
v_it_x27_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_fst_3971_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v___x_3989_);
v_it_x27_3991_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_string_push(v_acc_3969_, v___x_3982_);
v_acc_3969_ = v___x_3992_;
v_a_3970_ = v_it_x27_3991_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_box(0);
lean_inc(v_snd_3972_);
v_pos_3974_ = v_a_3970_;
v_snd_3975_ = v_snd_3972_;
v_err_3976_ = v___x_3998_;
goto v___jp_3973_;
}
v___jp_3973_:
{
uint8_t v___x_3977_; 
v___x_3977_ = lean_nat_dec_eq(v_snd_3972_, v_snd_3975_);
lean_dec(v_snd_3975_);
lean_dec(v_snd_3972_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; 
lean_dec_ref(v_acc_3969_);
lean_inc(v_err_3976_);
v___x_3978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3978_, 0, v_pos_3974_);
lean_ctor_set(v___x_3978_, 1, v_err_3976_);
return v___x_3978_;
}
else
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3979_, 0, v_pos_3974_);
lean_ctor_set(v___x_3979_, 1, v_acc_3969_);
return v___x_3979_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0(void){
_start:
{
uint32_t v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3999_ = 76;
v___x_4000_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4001_ = lean_string_push(v___x_4000_, v___x_3999_);
return v___x_4001_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1(void){
_start:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4002_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0);
v___x_4003_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4004_ = lean_string_append(v___x_4003_, v___x_4002_);
return v___x_4004_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4006_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1);
v___x_4007_ = lean_string_append(v___x_4006_, v___x_4005_);
return v___x_4007_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3(void){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2);
v___x_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(lean_object* v_acc_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v_fst_4012_; lean_object* v_snd_4013_; lean_object* v_pos_4015_; lean_object* v_snd_4016_; lean_object* v_err_4017_; lean_object* v___x_4021_; uint8_t v___x_4022_; 
v_fst_4012_ = lean_ctor_get(v_a_4011_, 0);
v_snd_4013_ = lean_ctor_get(v_a_4011_, 1);
lean_inc(v_snd_4013_);
v___x_4021_ = lean_string_utf8_byte_size(v_fst_4012_);
v___x_4022_ = lean_nat_dec_eq(v_snd_4013_, v___x_4021_);
if (v___x_4022_ == 0)
{
uint32_t v___x_4023_; uint32_t v_c_4024_; uint8_t v___x_4025_; 
v___x_4023_ = 76;
v_c_4024_ = lean_string_utf8_get_fast(v_fst_4012_, v_snd_4013_);
v___x_4025_ = lean_uint32_dec_eq(v_c_4024_, v___x_4023_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; 
v___x_4026_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3);
lean_inc(v_snd_4013_);
v_pos_4015_ = v_a_4011_;
v_snd_4016_ = v_snd_4013_;
v_err_4017_ = v___x_4026_;
goto v___jp_4014_;
}
else
{
lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4036_; 
lean_inc(v_fst_4012_);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_a_4011_);
if (v_isSharedCheck_4036_ == 0)
{
lean_object* v_unused_4037_; lean_object* v_unused_4038_; 
v_unused_4037_ = lean_ctor_get(v_a_4011_, 1);
lean_dec(v_unused_4037_);
v_unused_4038_ = lean_ctor_get(v_a_4011_, 0);
lean_dec(v_unused_4038_);
v___x_4028_ = v_a_4011_;
v_isShared_4029_ = v_isSharedCheck_4036_;
goto v_resetjp_4027_;
}
else
{
lean_dec(v_a_4011_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4036_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4030_; lean_object* v_it_x27_4032_; 
v___x_4030_ = lean_string_utf8_next_fast(v_fst_4012_, v_snd_4013_);
lean_dec(v_snd_4013_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 1, v___x_4030_);
v_it_x27_4032_ = v___x_4028_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_fst_4012_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_4030_);
v_it_x27_4032_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
lean_object* v___x_4033_; 
v___x_4033_ = lean_string_push(v_acc_4010_, v___x_4023_);
v_acc_4010_ = v___x_4033_;
v_a_4011_ = v_it_x27_4032_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4039_; 
v___x_4039_ = lean_box(0);
lean_inc(v_snd_4013_);
v_pos_4015_ = v_a_4011_;
v_snd_4016_ = v_snd_4013_;
v_err_4017_ = v___x_4039_;
goto v___jp_4014_;
}
v___jp_4014_:
{
uint8_t v___x_4018_; 
v___x_4018_ = lean_nat_dec_eq(v_snd_4013_, v_snd_4016_);
lean_dec(v_snd_4016_);
lean_dec(v_snd_4013_);
if (v___x_4018_ == 0)
{
lean_object* v___x_4019_; 
lean_dec_ref(v_acc_4010_);
lean_inc(v_err_4017_);
v___x_4019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4019_, 0, v_pos_4015_);
lean_ctor_set(v___x_4019_, 1, v_err_4017_);
return v___x_4019_;
}
else
{
lean_object* v___x_4020_; 
v___x_4020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4020_, 0, v_pos_4015_);
lean_ctor_set(v___x_4020_, 1, v_acc_4010_);
return v___x_4020_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0(void){
_start:
{
uint32_t v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4040_ = 113;
v___x_4041_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4042_ = lean_string_push(v___x_4041_, v___x_4040_);
return v___x_4042_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1(void){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4043_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0);
v___x_4044_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4045_ = lean_string_append(v___x_4044_, v___x_4043_);
return v___x_4045_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4046_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4047_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1);
v___x_4048_ = lean_string_append(v___x_4047_, v___x_4046_);
return v___x_4048_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3(void){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2);
v___x_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(lean_object* v_acc_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v_fst_4053_; lean_object* v_snd_4054_; lean_object* v_pos_4056_; lean_object* v_snd_4057_; lean_object* v_err_4058_; lean_object* v___x_4062_; uint8_t v___x_4063_; 
v_fst_4053_ = lean_ctor_get(v_a_4052_, 0);
v_snd_4054_ = lean_ctor_get(v_a_4052_, 1);
lean_inc(v_snd_4054_);
v___x_4062_ = lean_string_utf8_byte_size(v_fst_4053_);
v___x_4063_ = lean_nat_dec_eq(v_snd_4054_, v___x_4062_);
if (v___x_4063_ == 0)
{
uint32_t v___x_4064_; uint32_t v_c_4065_; uint8_t v___x_4066_; 
v___x_4064_ = 113;
v_c_4065_ = lean_string_utf8_get_fast(v_fst_4053_, v_snd_4054_);
v___x_4066_ = lean_uint32_dec_eq(v_c_4065_, v___x_4064_);
if (v___x_4066_ == 0)
{
lean_object* v___x_4067_; 
v___x_4067_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3);
lean_inc(v_snd_4054_);
v_pos_4056_ = v_a_4052_;
v_snd_4057_ = v_snd_4054_;
v_err_4058_ = v___x_4067_;
goto v___jp_4055_;
}
else
{
lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4077_; 
lean_inc(v_fst_4053_);
v_isSharedCheck_4077_ = !lean_is_exclusive(v_a_4052_);
if (v_isSharedCheck_4077_ == 0)
{
lean_object* v_unused_4078_; lean_object* v_unused_4079_; 
v_unused_4078_ = lean_ctor_get(v_a_4052_, 1);
lean_dec(v_unused_4078_);
v_unused_4079_ = lean_ctor_get(v_a_4052_, 0);
lean_dec(v_unused_4079_);
v___x_4069_ = v_a_4052_;
v_isShared_4070_ = v_isSharedCheck_4077_;
goto v_resetjp_4068_;
}
else
{
lean_dec(v_a_4052_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4077_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; lean_object* v_it_x27_4073_; 
v___x_4071_ = lean_string_utf8_next_fast(v_fst_4053_, v_snd_4054_);
lean_dec(v_snd_4054_);
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 1, v___x_4071_);
v_it_x27_4073_ = v___x_4069_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_fst_4053_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v___x_4071_);
v_it_x27_4073_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_string_push(v_acc_4051_, v___x_4064_);
v_acc_4051_ = v___x_4074_;
v_a_4052_ = v_it_x27_4073_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_box(0);
lean_inc(v_snd_4054_);
v_pos_4056_ = v_a_4052_;
v_snd_4057_ = v_snd_4054_;
v_err_4058_ = v___x_4080_;
goto v___jp_4055_;
}
v___jp_4055_:
{
uint8_t v___x_4059_; 
v___x_4059_ = lean_nat_dec_eq(v_snd_4054_, v_snd_4057_);
lean_dec(v_snd_4057_);
lean_dec(v_snd_4054_);
if (v___x_4059_ == 0)
{
lean_object* v___x_4060_; 
lean_dec_ref(v_acc_4051_);
lean_inc(v_err_4058_);
v___x_4060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4060_, 0, v_pos_4056_);
lean_ctor_set(v___x_4060_, 1, v_err_4058_);
return v___x_4060_;
}
else
{
lean_object* v___x_4061_; 
v___x_4061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4061_, 0, v_pos_4056_);
lean_ctor_set(v___x_4061_, 1, v_acc_4051_);
return v___x_4061_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0(void){
_start:
{
uint32_t v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4081_ = 72;
v___x_4082_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4083_ = lean_string_push(v___x_4082_, v___x_4081_);
return v___x_4083_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1(void){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0);
v___x_4085_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4086_ = lean_string_append(v___x_4085_, v___x_4084_);
return v___x_4086_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2(void){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4087_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4088_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1);
v___x_4089_ = lean_string_append(v___x_4088_, v___x_4087_);
return v___x_4089_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3(void){
_start:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4090_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2);
v___x_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(lean_object* v_acc_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v_fst_4094_; lean_object* v_snd_4095_; lean_object* v_pos_4097_; lean_object* v_snd_4098_; lean_object* v_err_4099_; lean_object* v___x_4103_; uint8_t v___x_4104_; 
v_fst_4094_ = lean_ctor_get(v_a_4093_, 0);
v_snd_4095_ = lean_ctor_get(v_a_4093_, 1);
lean_inc(v_snd_4095_);
v___x_4103_ = lean_string_utf8_byte_size(v_fst_4094_);
v___x_4104_ = lean_nat_dec_eq(v_snd_4095_, v___x_4103_);
if (v___x_4104_ == 0)
{
uint32_t v___x_4105_; uint32_t v_c_4106_; uint8_t v___x_4107_; 
v___x_4105_ = 72;
v_c_4106_ = lean_string_utf8_get_fast(v_fst_4094_, v_snd_4095_);
v___x_4107_ = lean_uint32_dec_eq(v_c_4106_, v___x_4105_);
if (v___x_4107_ == 0)
{
lean_object* v___x_4108_; 
v___x_4108_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3);
lean_inc(v_snd_4095_);
v_pos_4097_ = v_a_4093_;
v_snd_4098_ = v_snd_4095_;
v_err_4099_ = v___x_4108_;
goto v___jp_4096_;
}
else
{
lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4118_; 
lean_inc(v_fst_4094_);
v_isSharedCheck_4118_ = !lean_is_exclusive(v_a_4093_);
if (v_isSharedCheck_4118_ == 0)
{
lean_object* v_unused_4119_; lean_object* v_unused_4120_; 
v_unused_4119_ = lean_ctor_get(v_a_4093_, 1);
lean_dec(v_unused_4119_);
v_unused_4120_ = lean_ctor_get(v_a_4093_, 0);
lean_dec(v_unused_4120_);
v___x_4110_ = v_a_4093_;
v_isShared_4111_ = v_isSharedCheck_4118_;
goto v_resetjp_4109_;
}
else
{
lean_dec(v_a_4093_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4118_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4112_; lean_object* v_it_x27_4114_; 
v___x_4112_ = lean_string_utf8_next_fast(v_fst_4094_, v_snd_4095_);
lean_dec(v_snd_4095_);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 1, v___x_4112_);
v_it_x27_4114_ = v___x_4110_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_fst_4094_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v___x_4112_);
v_it_x27_4114_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4115_; 
v___x_4115_ = lean_string_push(v_acc_4092_, v___x_4105_);
v_acc_4092_ = v___x_4115_;
v_a_4093_ = v_it_x27_4114_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4121_; 
v___x_4121_ = lean_box(0);
lean_inc(v_snd_4095_);
v_pos_4097_ = v_a_4093_;
v_snd_4098_ = v_snd_4095_;
v_err_4099_ = v___x_4121_;
goto v___jp_4096_;
}
v___jp_4096_:
{
uint8_t v___x_4100_; 
v___x_4100_ = lean_nat_dec_eq(v_snd_4095_, v_snd_4098_);
lean_dec(v_snd_4098_);
lean_dec(v_snd_4095_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; 
lean_dec_ref(v_acc_4092_);
lean_inc(v_err_4099_);
v___x_4101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4101_, 0, v_pos_4097_);
lean_ctor_set(v___x_4101_, 1, v_err_4099_);
return v___x_4101_;
}
else
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4102_, 0, v_pos_4097_);
lean_ctor_set(v___x_4102_, 1, v_acc_4092_);
return v___x_4102_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0(void){
_start:
{
uint32_t v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4122_ = 118;
v___x_4123_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4124_ = lean_string_push(v___x_4123_, v___x_4122_);
return v___x_4124_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1(void){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0);
v___x_4126_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4127_ = lean_string_append(v___x_4126_, v___x_4125_);
return v___x_4127_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2(void){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4128_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4129_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1);
v___x_4130_ = lean_string_append(v___x_4129_, v___x_4128_);
return v___x_4130_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3(void){
_start:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4131_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2);
v___x_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(lean_object* v_acc_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v_fst_4135_; lean_object* v_snd_4136_; lean_object* v_pos_4138_; lean_object* v_snd_4139_; lean_object* v_err_4140_; lean_object* v___x_4144_; uint8_t v___x_4145_; 
v_fst_4135_ = lean_ctor_get(v_a_4134_, 0);
v_snd_4136_ = lean_ctor_get(v_a_4134_, 1);
lean_inc(v_snd_4136_);
v___x_4144_ = lean_string_utf8_byte_size(v_fst_4135_);
v___x_4145_ = lean_nat_dec_eq(v_snd_4136_, v___x_4144_);
if (v___x_4145_ == 0)
{
uint32_t v___x_4146_; uint32_t v_c_4147_; uint8_t v___x_4148_; 
v___x_4146_ = 118;
v_c_4147_ = lean_string_utf8_get_fast(v_fst_4135_, v_snd_4136_);
v___x_4148_ = lean_uint32_dec_eq(v_c_4147_, v___x_4146_);
if (v___x_4148_ == 0)
{
lean_object* v___x_4149_; 
v___x_4149_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3);
lean_inc(v_snd_4136_);
v_pos_4138_ = v_a_4134_;
v_snd_4139_ = v_snd_4136_;
v_err_4140_ = v___x_4149_;
goto v___jp_4137_;
}
else
{
lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4159_; 
lean_inc(v_fst_4135_);
v_isSharedCheck_4159_ = !lean_is_exclusive(v_a_4134_);
if (v_isSharedCheck_4159_ == 0)
{
lean_object* v_unused_4160_; lean_object* v_unused_4161_; 
v_unused_4160_ = lean_ctor_get(v_a_4134_, 1);
lean_dec(v_unused_4160_);
v_unused_4161_ = lean_ctor_get(v_a_4134_, 0);
lean_dec(v_unused_4161_);
v___x_4151_ = v_a_4134_;
v_isShared_4152_ = v_isSharedCheck_4159_;
goto v_resetjp_4150_;
}
else
{
lean_dec(v_a_4134_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4159_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4153_; lean_object* v_it_x27_4155_; 
v___x_4153_ = lean_string_utf8_next_fast(v_fst_4135_, v_snd_4136_);
lean_dec(v_snd_4136_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 1, v___x_4153_);
v_it_x27_4155_ = v___x_4151_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_fst_4135_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v___x_4153_);
v_it_x27_4155_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
lean_object* v___x_4156_; 
v___x_4156_ = lean_string_push(v_acc_4133_, v___x_4146_);
v_acc_4133_ = v___x_4156_;
v_a_4134_ = v_it_x27_4155_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4162_; 
v___x_4162_ = lean_box(0);
lean_inc(v_snd_4136_);
v_pos_4138_ = v_a_4134_;
v_snd_4139_ = v_snd_4136_;
v_err_4140_ = v___x_4162_;
goto v___jp_4137_;
}
v___jp_4137_:
{
uint8_t v___x_4141_; 
v___x_4141_ = lean_nat_dec_eq(v_snd_4136_, v_snd_4139_);
lean_dec(v_snd_4139_);
lean_dec(v_snd_4136_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; 
lean_dec_ref(v_acc_4133_);
lean_inc(v_err_4140_);
v___x_4142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4142_, 0, v_pos_4138_);
lean_ctor_set(v___x_4142_, 1, v_err_4140_);
return v___x_4142_;
}
else
{
lean_object* v___x_4143_; 
v___x_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4143_, 0, v_pos_4138_);
lean_ctor_set(v___x_4143_, 1, v_acc_4133_);
return v___x_4143_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0(void){
_start:
{
uint32_t v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4163_ = 87;
v___x_4164_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4165_ = lean_string_push(v___x_4164_, v___x_4163_);
return v___x_4165_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1(void){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4166_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0);
v___x_4167_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4168_ = lean_string_append(v___x_4167_, v___x_4166_);
return v___x_4168_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2(void){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4169_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4170_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1);
v___x_4171_ = lean_string_append(v___x_4170_, v___x_4169_);
return v___x_4171_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3(void){
_start:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4172_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2);
v___x_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(lean_object* v_acc_4174_, lean_object* v_a_4175_){
_start:
{
lean_object* v_fst_4176_; lean_object* v_snd_4177_; lean_object* v_pos_4179_; lean_object* v_snd_4180_; lean_object* v_err_4181_; lean_object* v___x_4185_; uint8_t v___x_4186_; 
v_fst_4176_ = lean_ctor_get(v_a_4175_, 0);
v_snd_4177_ = lean_ctor_get(v_a_4175_, 1);
lean_inc(v_snd_4177_);
v___x_4185_ = lean_string_utf8_byte_size(v_fst_4176_);
v___x_4186_ = lean_nat_dec_eq(v_snd_4177_, v___x_4185_);
if (v___x_4186_ == 0)
{
uint32_t v___x_4187_; uint32_t v_c_4188_; uint8_t v___x_4189_; 
v___x_4187_ = 87;
v_c_4188_ = lean_string_utf8_get_fast(v_fst_4176_, v_snd_4177_);
v___x_4189_ = lean_uint32_dec_eq(v_c_4188_, v___x_4187_);
if (v___x_4189_ == 0)
{
lean_object* v___x_4190_; 
v___x_4190_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3);
lean_inc(v_snd_4177_);
v_pos_4179_ = v_a_4175_;
v_snd_4180_ = v_snd_4177_;
v_err_4181_ = v___x_4190_;
goto v___jp_4178_;
}
else
{
lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4200_; 
lean_inc(v_fst_4176_);
v_isSharedCheck_4200_ = !lean_is_exclusive(v_a_4175_);
if (v_isSharedCheck_4200_ == 0)
{
lean_object* v_unused_4201_; lean_object* v_unused_4202_; 
v_unused_4201_ = lean_ctor_get(v_a_4175_, 1);
lean_dec(v_unused_4201_);
v_unused_4202_ = lean_ctor_get(v_a_4175_, 0);
lean_dec(v_unused_4202_);
v___x_4192_ = v_a_4175_;
v_isShared_4193_ = v_isSharedCheck_4200_;
goto v_resetjp_4191_;
}
else
{
lean_dec(v_a_4175_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4200_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4194_; lean_object* v_it_x27_4196_; 
v___x_4194_ = lean_string_utf8_next_fast(v_fst_4176_, v_snd_4177_);
lean_dec(v_snd_4177_);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 1, v___x_4194_);
v_it_x27_4196_ = v___x_4192_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_fst_4176_);
lean_ctor_set(v_reuseFailAlloc_4199_, 1, v___x_4194_);
v_it_x27_4196_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_object* v___x_4197_; 
v___x_4197_ = lean_string_push(v_acc_4174_, v___x_4187_);
v_acc_4174_ = v___x_4197_;
v_a_4175_ = v_it_x27_4196_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4203_; 
v___x_4203_ = lean_box(0);
lean_inc(v_snd_4177_);
v_pos_4179_ = v_a_4175_;
v_snd_4180_ = v_snd_4177_;
v_err_4181_ = v___x_4203_;
goto v___jp_4178_;
}
v___jp_4178_:
{
uint8_t v___x_4182_; 
v___x_4182_ = lean_nat_dec_eq(v_snd_4177_, v_snd_4180_);
lean_dec(v_snd_4180_);
lean_dec(v_snd_4177_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4183_; 
lean_dec_ref(v_acc_4174_);
lean_inc(v_err_4181_);
v___x_4183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4183_, 0, v_pos_4179_);
lean_ctor_set(v___x_4183_, 1, v_err_4181_);
return v___x_4183_;
}
else
{
lean_object* v___x_4184_; 
v___x_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4184_, 0, v_pos_4179_);
lean_ctor_set(v___x_4184_, 1, v_acc_4174_);
return v___x_4184_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0(void){
_start:
{
uint32_t v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4204_ = 107;
v___x_4205_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4206_ = lean_string_push(v___x_4205_, v___x_4204_);
return v___x_4206_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1(void){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4207_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0);
v___x_4208_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4209_ = lean_string_append(v___x_4208_, v___x_4207_);
return v___x_4209_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2(void){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4210_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4211_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1);
v___x_4212_ = lean_string_append(v___x_4211_, v___x_4210_);
return v___x_4212_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3(void){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2);
v___x_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(lean_object* v_acc_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v_fst_4217_; lean_object* v_snd_4218_; lean_object* v_pos_4220_; lean_object* v_snd_4221_; lean_object* v_err_4222_; lean_object* v___x_4226_; uint8_t v___x_4227_; 
v_fst_4217_ = lean_ctor_get(v_a_4216_, 0);
v_snd_4218_ = lean_ctor_get(v_a_4216_, 1);
lean_inc(v_snd_4218_);
v___x_4226_ = lean_string_utf8_byte_size(v_fst_4217_);
v___x_4227_ = lean_nat_dec_eq(v_snd_4218_, v___x_4226_);
if (v___x_4227_ == 0)
{
uint32_t v___x_4228_; uint32_t v_c_4229_; uint8_t v___x_4230_; 
v___x_4228_ = 107;
v_c_4229_ = lean_string_utf8_get_fast(v_fst_4217_, v_snd_4218_);
v___x_4230_ = lean_uint32_dec_eq(v_c_4229_, v___x_4228_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3);
lean_inc(v_snd_4218_);
v_pos_4220_ = v_a_4216_;
v_snd_4221_ = v_snd_4218_;
v_err_4222_ = v___x_4231_;
goto v___jp_4219_;
}
else
{
lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4241_; 
lean_inc(v_fst_4217_);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_a_4216_);
if (v_isSharedCheck_4241_ == 0)
{
lean_object* v_unused_4242_; lean_object* v_unused_4243_; 
v_unused_4242_ = lean_ctor_get(v_a_4216_, 1);
lean_dec(v_unused_4242_);
v_unused_4243_ = lean_ctor_get(v_a_4216_, 0);
lean_dec(v_unused_4243_);
v___x_4233_ = v_a_4216_;
v_isShared_4234_ = v_isSharedCheck_4241_;
goto v_resetjp_4232_;
}
else
{
lean_dec(v_a_4216_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4241_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4235_; lean_object* v_it_x27_4237_; 
v___x_4235_ = lean_string_utf8_next_fast(v_fst_4217_, v_snd_4218_);
lean_dec(v_snd_4218_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 1, v___x_4235_);
v_it_x27_4237_ = v___x_4233_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_fst_4217_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v___x_4235_);
v_it_x27_4237_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_string_push(v_acc_4215_, v___x_4228_);
v_acc_4215_ = v___x_4238_;
v_a_4216_ = v_it_x27_4237_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4244_; 
v___x_4244_ = lean_box(0);
lean_inc(v_snd_4218_);
v_pos_4220_ = v_a_4216_;
v_snd_4221_ = v_snd_4218_;
v_err_4222_ = v___x_4244_;
goto v___jp_4219_;
}
v___jp_4219_:
{
uint8_t v___x_4223_; 
v___x_4223_ = lean_nat_dec_eq(v_snd_4218_, v_snd_4221_);
lean_dec(v_snd_4221_);
lean_dec(v_snd_4218_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; 
lean_dec_ref(v_acc_4215_);
lean_inc(v_err_4222_);
v___x_4224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4224_, 0, v_pos_4220_);
lean_ctor_set(v___x_4224_, 1, v_err_4222_);
return v___x_4224_;
}
else
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4225_, 0, v_pos_4220_);
lean_ctor_set(v___x_4225_, 1, v_acc_4215_);
return v___x_4225_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0(void){
_start:
{
uint32_t v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4245_ = 121;
v___x_4246_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4247_ = lean_string_push(v___x_4246_, v___x_4245_);
return v___x_4247_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1(void){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4248_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0);
v___x_4249_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4250_ = lean_string_append(v___x_4249_, v___x_4248_);
return v___x_4250_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2(void){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4252_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1);
v___x_4253_ = lean_string_append(v___x_4252_, v___x_4251_);
return v___x_4253_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3(void){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4254_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2);
v___x_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(lean_object* v_acc_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v_fst_4258_; lean_object* v_snd_4259_; lean_object* v_pos_4261_; lean_object* v_snd_4262_; lean_object* v_err_4263_; lean_object* v___x_4267_; uint8_t v___x_4268_; 
v_fst_4258_ = lean_ctor_get(v_a_4257_, 0);
v_snd_4259_ = lean_ctor_get(v_a_4257_, 1);
lean_inc(v_snd_4259_);
v___x_4267_ = lean_string_utf8_byte_size(v_fst_4258_);
v___x_4268_ = lean_nat_dec_eq(v_snd_4259_, v___x_4267_);
if (v___x_4268_ == 0)
{
uint32_t v___x_4269_; uint32_t v_c_4270_; uint8_t v___x_4271_; 
v___x_4269_ = 121;
v_c_4270_ = lean_string_utf8_get_fast(v_fst_4258_, v_snd_4259_);
v___x_4271_ = lean_uint32_dec_eq(v_c_4270_, v___x_4269_);
if (v___x_4271_ == 0)
{
lean_object* v___x_4272_; 
v___x_4272_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3);
lean_inc(v_snd_4259_);
v_pos_4261_ = v_a_4257_;
v_snd_4262_ = v_snd_4259_;
v_err_4263_ = v___x_4272_;
goto v___jp_4260_;
}
else
{
lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4282_; 
lean_inc(v_fst_4258_);
v_isSharedCheck_4282_ = !lean_is_exclusive(v_a_4257_);
if (v_isSharedCheck_4282_ == 0)
{
lean_object* v_unused_4283_; lean_object* v_unused_4284_; 
v_unused_4283_ = lean_ctor_get(v_a_4257_, 1);
lean_dec(v_unused_4283_);
v_unused_4284_ = lean_ctor_get(v_a_4257_, 0);
lean_dec(v_unused_4284_);
v___x_4274_ = v_a_4257_;
v_isShared_4275_ = v_isSharedCheck_4282_;
goto v_resetjp_4273_;
}
else
{
lean_dec(v_a_4257_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4282_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4276_; lean_object* v_it_x27_4278_; 
v___x_4276_ = lean_string_utf8_next_fast(v_fst_4258_, v_snd_4259_);
lean_dec(v_snd_4259_);
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 1, v___x_4276_);
v_it_x27_4278_ = v___x_4274_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_fst_4258_);
lean_ctor_set(v_reuseFailAlloc_4281_, 1, v___x_4276_);
v_it_x27_4278_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
lean_object* v___x_4279_; 
v___x_4279_ = lean_string_push(v_acc_4256_, v___x_4269_);
v_acc_4256_ = v___x_4279_;
v_a_4257_ = v_it_x27_4278_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4285_; 
v___x_4285_ = lean_box(0);
lean_inc(v_snd_4259_);
v_pos_4261_ = v_a_4257_;
v_snd_4262_ = v_snd_4259_;
v_err_4263_ = v___x_4285_;
goto v___jp_4260_;
}
v___jp_4260_:
{
uint8_t v___x_4264_; 
v___x_4264_ = lean_nat_dec_eq(v_snd_4259_, v_snd_4262_);
lean_dec(v_snd_4262_);
lean_dec(v_snd_4259_);
if (v___x_4264_ == 0)
{
lean_object* v___x_4265_; 
lean_dec_ref(v_acc_4256_);
lean_inc(v_err_4263_);
v___x_4265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4265_, 0, v_pos_4261_);
lean_ctor_set(v___x_4265_, 1, v_err_4263_);
return v___x_4265_;
}
else
{
lean_object* v___x_4266_; 
v___x_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4266_, 0, v_pos_4261_);
lean_ctor_set(v___x_4266_, 1, v_acc_4256_);
return v___x_4266_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0(void){
_start:
{
uint32_t v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4286_ = 98;
v___x_4287_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4288_ = lean_string_push(v___x_4287_, v___x_4286_);
return v___x_4288_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1(void){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4289_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0);
v___x_4290_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4291_ = lean_string_append(v___x_4290_, v___x_4289_);
return v___x_4291_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2(void){
_start:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4292_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4293_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1);
v___x_4294_ = lean_string_append(v___x_4293_, v___x_4292_);
return v___x_4294_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3(void){
_start:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4295_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2);
v___x_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(lean_object* v_acc_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v_fst_4299_; lean_object* v_snd_4300_; lean_object* v_pos_4302_; lean_object* v_snd_4303_; lean_object* v_err_4304_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v_fst_4299_ = lean_ctor_get(v_a_4298_, 0);
v_snd_4300_ = lean_ctor_get(v_a_4298_, 1);
lean_inc(v_snd_4300_);
v___x_4308_ = lean_string_utf8_byte_size(v_fst_4299_);
v___x_4309_ = lean_nat_dec_eq(v_snd_4300_, v___x_4308_);
if (v___x_4309_ == 0)
{
uint32_t v___x_4310_; uint32_t v_c_4311_; uint8_t v___x_4312_; 
v___x_4310_ = 98;
v_c_4311_ = lean_string_utf8_get_fast(v_fst_4299_, v_snd_4300_);
v___x_4312_ = lean_uint32_dec_eq(v_c_4311_, v___x_4310_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3);
lean_inc(v_snd_4300_);
v_pos_4302_ = v_a_4298_;
v_snd_4303_ = v_snd_4300_;
v_err_4304_ = v___x_4313_;
goto v___jp_4301_;
}
else
{
lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4323_; 
lean_inc(v_fst_4299_);
v_isSharedCheck_4323_ = !lean_is_exclusive(v_a_4298_);
if (v_isSharedCheck_4323_ == 0)
{
lean_object* v_unused_4324_; lean_object* v_unused_4325_; 
v_unused_4324_ = lean_ctor_get(v_a_4298_, 1);
lean_dec(v_unused_4324_);
v_unused_4325_ = lean_ctor_get(v_a_4298_, 0);
lean_dec(v_unused_4325_);
v___x_4315_ = v_a_4298_;
v_isShared_4316_ = v_isSharedCheck_4323_;
goto v_resetjp_4314_;
}
else
{
lean_dec(v_a_4298_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4323_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4317_; lean_object* v_it_x27_4319_; 
v___x_4317_ = lean_string_utf8_next_fast(v_fst_4299_, v_snd_4300_);
lean_dec(v_snd_4300_);
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 1, v___x_4317_);
v_it_x27_4319_ = v___x_4315_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_fst_4299_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v___x_4317_);
v_it_x27_4319_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4320_; 
v___x_4320_ = lean_string_push(v_acc_4297_, v___x_4310_);
v_acc_4297_ = v___x_4320_;
v_a_4298_ = v_it_x27_4319_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4326_; 
v___x_4326_ = lean_box(0);
lean_inc(v_snd_4300_);
v_pos_4302_ = v_a_4298_;
v_snd_4303_ = v_snd_4300_;
v_err_4304_ = v___x_4326_;
goto v___jp_4301_;
}
v___jp_4301_:
{
uint8_t v___x_4305_; 
v___x_4305_ = lean_nat_dec_eq(v_snd_4300_, v_snd_4303_);
lean_dec(v_snd_4303_);
lean_dec(v_snd_4300_);
if (v___x_4305_ == 0)
{
lean_object* v___x_4306_; 
lean_dec_ref(v_acc_4297_);
lean_inc(v_err_4304_);
v___x_4306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4306_, 0, v_pos_4302_);
lean_ctor_set(v___x_4306_, 1, v_err_4304_);
return v___x_4306_;
}
else
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v_pos_4302_);
lean_ctor_set(v___x_4307_, 1, v_acc_4297_);
return v___x_4307_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0(void){
_start:
{
uint32_t v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4327_ = 109;
v___x_4328_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4329_ = lean_string_push(v___x_4328_, v___x_4327_);
return v___x_4329_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1(void){
_start:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4330_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0);
v___x_4331_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4332_ = lean_string_append(v___x_4331_, v___x_4330_);
return v___x_4332_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2(void){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4333_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4334_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1);
v___x_4335_ = lean_string_append(v___x_4334_, v___x_4333_);
return v___x_4335_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3(void){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4336_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2);
v___x_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(lean_object* v_acc_4338_, lean_object* v_a_4339_){
_start:
{
lean_object* v_fst_4340_; lean_object* v_snd_4341_; lean_object* v_pos_4343_; lean_object* v_snd_4344_; lean_object* v_err_4345_; lean_object* v___x_4349_; uint8_t v___x_4350_; 
v_fst_4340_ = lean_ctor_get(v_a_4339_, 0);
v_snd_4341_ = lean_ctor_get(v_a_4339_, 1);
lean_inc(v_snd_4341_);
v___x_4349_ = lean_string_utf8_byte_size(v_fst_4340_);
v___x_4350_ = lean_nat_dec_eq(v_snd_4341_, v___x_4349_);
if (v___x_4350_ == 0)
{
uint32_t v___x_4351_; uint32_t v_c_4352_; uint8_t v___x_4353_; 
v___x_4351_ = 109;
v_c_4352_ = lean_string_utf8_get_fast(v_fst_4340_, v_snd_4341_);
v___x_4353_ = lean_uint32_dec_eq(v_c_4352_, v___x_4351_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; 
v___x_4354_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3);
lean_inc(v_snd_4341_);
v_pos_4343_ = v_a_4339_;
v_snd_4344_ = v_snd_4341_;
v_err_4345_ = v___x_4354_;
goto v___jp_4342_;
}
else
{
lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4364_; 
lean_inc(v_fst_4340_);
v_isSharedCheck_4364_ = !lean_is_exclusive(v_a_4339_);
if (v_isSharedCheck_4364_ == 0)
{
lean_object* v_unused_4365_; lean_object* v_unused_4366_; 
v_unused_4365_ = lean_ctor_get(v_a_4339_, 1);
lean_dec(v_unused_4365_);
v_unused_4366_ = lean_ctor_get(v_a_4339_, 0);
lean_dec(v_unused_4366_);
v___x_4356_ = v_a_4339_;
v_isShared_4357_ = v_isSharedCheck_4364_;
goto v_resetjp_4355_;
}
else
{
lean_dec(v_a_4339_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4364_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4358_; lean_object* v_it_x27_4360_; 
v___x_4358_ = lean_string_utf8_next_fast(v_fst_4340_, v_snd_4341_);
lean_dec(v_snd_4341_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 1, v___x_4358_);
v_it_x27_4360_ = v___x_4356_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_fst_4340_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v___x_4358_);
v_it_x27_4360_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
lean_object* v___x_4361_; 
v___x_4361_ = lean_string_push(v_acc_4338_, v___x_4351_);
v_acc_4338_ = v___x_4361_;
v_a_4339_ = v_it_x27_4360_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4367_; 
v___x_4367_ = lean_box(0);
lean_inc(v_snd_4341_);
v_pos_4343_ = v_a_4339_;
v_snd_4344_ = v_snd_4341_;
v_err_4345_ = v___x_4367_;
goto v___jp_4342_;
}
v___jp_4342_:
{
uint8_t v___x_4346_; 
v___x_4346_ = lean_nat_dec_eq(v_snd_4341_, v_snd_4344_);
lean_dec(v_snd_4344_);
lean_dec(v_snd_4341_);
if (v___x_4346_ == 0)
{
lean_object* v___x_4347_; 
lean_dec_ref(v_acc_4338_);
lean_inc(v_err_4345_);
v___x_4347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4347_, 0, v_pos_4343_);
lean_ctor_set(v___x_4347_, 1, v_err_4345_);
return v___x_4347_;
}
else
{
lean_object* v___x_4348_; 
v___x_4348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4348_, 0, v_pos_4343_);
lean_ctor_set(v___x_4348_, 1, v_acc_4338_);
return v___x_4348_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0(void){
_start:
{
uint32_t v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4368_ = 117;
v___x_4369_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4370_ = lean_string_push(v___x_4369_, v___x_4368_);
return v___x_4370_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1(void){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4371_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0);
v___x_4372_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4373_ = lean_string_append(v___x_4372_, v___x_4371_);
return v___x_4373_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2(void){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4374_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4375_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1);
v___x_4376_ = lean_string_append(v___x_4375_, v___x_4374_);
return v___x_4376_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3(void){
_start:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4377_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2);
v___x_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4377_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(lean_object* v_acc_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v_fst_4381_; lean_object* v_snd_4382_; lean_object* v_pos_4384_; lean_object* v_snd_4385_; lean_object* v_err_4386_; lean_object* v___x_4390_; uint8_t v___x_4391_; 
v_fst_4381_ = lean_ctor_get(v_a_4380_, 0);
v_snd_4382_ = lean_ctor_get(v_a_4380_, 1);
lean_inc(v_snd_4382_);
v___x_4390_ = lean_string_utf8_byte_size(v_fst_4381_);
v___x_4391_ = lean_nat_dec_eq(v_snd_4382_, v___x_4390_);
if (v___x_4391_ == 0)
{
uint32_t v___x_4392_; uint32_t v_c_4393_; uint8_t v___x_4394_; 
v___x_4392_ = 117;
v_c_4393_ = lean_string_utf8_get_fast(v_fst_4381_, v_snd_4382_);
v___x_4394_ = lean_uint32_dec_eq(v_c_4393_, v___x_4392_);
if (v___x_4394_ == 0)
{
lean_object* v___x_4395_; 
v___x_4395_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3);
lean_inc(v_snd_4382_);
v_pos_4384_ = v_a_4380_;
v_snd_4385_ = v_snd_4382_;
v_err_4386_ = v___x_4395_;
goto v___jp_4383_;
}
else
{
lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4405_; 
lean_inc(v_fst_4381_);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_a_4380_);
if (v_isSharedCheck_4405_ == 0)
{
lean_object* v_unused_4406_; lean_object* v_unused_4407_; 
v_unused_4406_ = lean_ctor_get(v_a_4380_, 1);
lean_dec(v_unused_4406_);
v_unused_4407_ = lean_ctor_get(v_a_4380_, 0);
lean_dec(v_unused_4407_);
v___x_4397_ = v_a_4380_;
v_isShared_4398_ = v_isSharedCheck_4405_;
goto v_resetjp_4396_;
}
else
{
lean_dec(v_a_4380_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4405_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4399_; lean_object* v_it_x27_4401_; 
v___x_4399_ = lean_string_utf8_next_fast(v_fst_4381_, v_snd_4382_);
lean_dec(v_snd_4382_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 1, v___x_4399_);
v_it_x27_4401_ = v___x_4397_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_fst_4381_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v___x_4399_);
v_it_x27_4401_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
lean_object* v___x_4402_; 
v___x_4402_ = lean_string_push(v_acc_4379_, v___x_4392_);
v_acc_4379_ = v___x_4402_;
v_a_4380_ = v_it_x27_4401_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4408_; 
v___x_4408_ = lean_box(0);
lean_inc(v_snd_4382_);
v_pos_4384_ = v_a_4380_;
v_snd_4385_ = v_snd_4382_;
v_err_4386_ = v___x_4408_;
goto v___jp_4383_;
}
v___jp_4383_:
{
uint8_t v___x_4387_; 
v___x_4387_ = lean_nat_dec_eq(v_snd_4382_, v_snd_4385_);
lean_dec(v_snd_4385_);
lean_dec(v_snd_4382_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; 
lean_dec_ref(v_acc_4379_);
lean_inc(v_err_4386_);
v___x_4388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4388_, 0, v_pos_4384_);
lean_ctor_set(v___x_4388_, 1, v_err_4386_);
return v___x_4388_;
}
else
{
lean_object* v___x_4389_; 
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v_pos_4384_);
lean_ctor_set(v___x_4389_, 1, v_acc_4379_);
return v___x_4389_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0(void){
_start:
{
uint32_t v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4409_ = 90;
v___x_4410_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4411_ = lean_string_push(v___x_4410_, v___x_4409_);
return v___x_4411_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4412_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0);
v___x_4413_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4414_ = lean_string_append(v___x_4413_, v___x_4412_);
return v___x_4414_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4415_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4416_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1);
v___x_4417_ = lean_string_append(v___x_4416_, v___x_4415_);
return v___x_4417_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4418_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2);
v___x_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(lean_object* v_acc_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v_fst_4422_; lean_object* v_snd_4423_; lean_object* v_pos_4425_; lean_object* v_snd_4426_; lean_object* v_err_4427_; lean_object* v___x_4431_; uint8_t v___x_4432_; 
v_fst_4422_ = lean_ctor_get(v_a_4421_, 0);
v_snd_4423_ = lean_ctor_get(v_a_4421_, 1);
lean_inc(v_snd_4423_);
v___x_4431_ = lean_string_utf8_byte_size(v_fst_4422_);
v___x_4432_ = lean_nat_dec_eq(v_snd_4423_, v___x_4431_);
if (v___x_4432_ == 0)
{
uint32_t v___x_4433_; uint32_t v_c_4434_; uint8_t v___x_4435_; 
v___x_4433_ = 90;
v_c_4434_ = lean_string_utf8_get_fast(v_fst_4422_, v_snd_4423_);
v___x_4435_ = lean_uint32_dec_eq(v_c_4434_, v___x_4433_);
if (v___x_4435_ == 0)
{
lean_object* v___x_4436_; 
v___x_4436_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3);
lean_inc(v_snd_4423_);
v_pos_4425_ = v_a_4421_;
v_snd_4426_ = v_snd_4423_;
v_err_4427_ = v___x_4436_;
goto v___jp_4424_;
}
else
{
lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4446_; 
lean_inc(v_fst_4422_);
v_isSharedCheck_4446_ = !lean_is_exclusive(v_a_4421_);
if (v_isSharedCheck_4446_ == 0)
{
lean_object* v_unused_4447_; lean_object* v_unused_4448_; 
v_unused_4447_ = lean_ctor_get(v_a_4421_, 1);
lean_dec(v_unused_4447_);
v_unused_4448_ = lean_ctor_get(v_a_4421_, 0);
lean_dec(v_unused_4448_);
v___x_4438_ = v_a_4421_;
v_isShared_4439_ = v_isSharedCheck_4446_;
goto v_resetjp_4437_;
}
else
{
lean_dec(v_a_4421_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4446_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4440_; lean_object* v_it_x27_4442_; 
v___x_4440_ = lean_string_utf8_next_fast(v_fst_4422_, v_snd_4423_);
lean_dec(v_snd_4423_);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 1, v___x_4440_);
v_it_x27_4442_ = v___x_4438_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_fst_4422_);
lean_ctor_set(v_reuseFailAlloc_4445_, 1, v___x_4440_);
v_it_x27_4442_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4443_; 
v___x_4443_ = lean_string_push(v_acc_4420_, v___x_4433_);
v_acc_4420_ = v___x_4443_;
v_a_4421_ = v_it_x27_4442_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4449_; 
v___x_4449_ = lean_box(0);
lean_inc(v_snd_4423_);
v_pos_4425_ = v_a_4421_;
v_snd_4426_ = v_snd_4423_;
v_err_4427_ = v___x_4449_;
goto v___jp_4424_;
}
v___jp_4424_:
{
uint8_t v___x_4428_; 
v___x_4428_ = lean_nat_dec_eq(v_snd_4423_, v_snd_4426_);
lean_dec(v_snd_4426_);
lean_dec(v_snd_4423_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; 
lean_dec_ref(v_acc_4420_);
lean_inc(v_err_4427_);
v___x_4429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4429_, 0, v_pos_4425_);
lean_ctor_set(v___x_4429_, 1, v_err_4427_);
return v___x_4429_;
}
else
{
lean_object* v___x_4430_; 
v___x_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4430_, 0, v_pos_4425_);
lean_ctor_set(v___x_4430_, 1, v_acc_4420_);
return v___x_4430_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0(void){
_start:
{
uint32_t v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4450_ = 78;
v___x_4451_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4452_ = lean_string_push(v___x_4451_, v___x_4450_);
return v___x_4452_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1(void){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4453_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0);
v___x_4454_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4455_ = lean_string_append(v___x_4454_, v___x_4453_);
return v___x_4455_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2(void){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4456_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4457_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1);
v___x_4458_ = lean_string_append(v___x_4457_, v___x_4456_);
return v___x_4458_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3(void){
_start:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4459_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2);
v___x_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4459_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(lean_object* v_acc_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v_fst_4463_; lean_object* v_snd_4464_; lean_object* v_pos_4466_; lean_object* v_snd_4467_; lean_object* v_err_4468_; lean_object* v___x_4472_; uint8_t v___x_4473_; 
v_fst_4463_ = lean_ctor_get(v_a_4462_, 0);
v_snd_4464_ = lean_ctor_get(v_a_4462_, 1);
lean_inc(v_snd_4464_);
v___x_4472_ = lean_string_utf8_byte_size(v_fst_4463_);
v___x_4473_ = lean_nat_dec_eq(v_snd_4464_, v___x_4472_);
if (v___x_4473_ == 0)
{
uint32_t v___x_4474_; uint32_t v_c_4475_; uint8_t v___x_4476_; 
v___x_4474_ = 78;
v_c_4475_ = lean_string_utf8_get_fast(v_fst_4463_, v_snd_4464_);
v___x_4476_ = lean_uint32_dec_eq(v_c_4475_, v___x_4474_);
if (v___x_4476_ == 0)
{
lean_object* v___x_4477_; 
v___x_4477_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3);
lean_inc(v_snd_4464_);
v_pos_4466_ = v_a_4462_;
v_snd_4467_ = v_snd_4464_;
v_err_4468_ = v___x_4477_;
goto v___jp_4465_;
}
else
{
lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4487_; 
lean_inc(v_fst_4463_);
v_isSharedCheck_4487_ = !lean_is_exclusive(v_a_4462_);
if (v_isSharedCheck_4487_ == 0)
{
lean_object* v_unused_4488_; lean_object* v_unused_4489_; 
v_unused_4488_ = lean_ctor_get(v_a_4462_, 1);
lean_dec(v_unused_4488_);
v_unused_4489_ = lean_ctor_get(v_a_4462_, 0);
lean_dec(v_unused_4489_);
v___x_4479_ = v_a_4462_;
v_isShared_4480_ = v_isSharedCheck_4487_;
goto v_resetjp_4478_;
}
else
{
lean_dec(v_a_4462_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4487_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; lean_object* v_it_x27_4483_; 
v___x_4481_ = lean_string_utf8_next_fast(v_fst_4463_, v_snd_4464_);
lean_dec(v_snd_4464_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 1, v___x_4481_);
v_it_x27_4483_ = v___x_4479_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_fst_4463_);
lean_ctor_set(v_reuseFailAlloc_4486_, 1, v___x_4481_);
v_it_x27_4483_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; 
v___x_4484_ = lean_string_push(v_acc_4461_, v___x_4474_);
v_acc_4461_ = v___x_4484_;
v_a_4462_ = v_it_x27_4483_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4490_; 
v___x_4490_ = lean_box(0);
lean_inc(v_snd_4464_);
v_pos_4466_ = v_a_4462_;
v_snd_4467_ = v_snd_4464_;
v_err_4468_ = v___x_4490_;
goto v___jp_4465_;
}
v___jp_4465_:
{
uint8_t v___x_4469_; 
v___x_4469_ = lean_nat_dec_eq(v_snd_4464_, v_snd_4467_);
lean_dec(v_snd_4467_);
lean_dec(v_snd_4464_);
if (v___x_4469_ == 0)
{
lean_object* v___x_4470_; 
lean_dec_ref(v_acc_4461_);
lean_inc(v_err_4468_);
v___x_4470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4470_, 0, v_pos_4466_);
lean_ctor_set(v___x_4470_, 1, v_err_4468_);
return v___x_4470_;
}
else
{
lean_object* v___x_4471_; 
v___x_4471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4471_, 0, v_pos_4466_);
lean_ctor_set(v___x_4471_, 1, v_acc_4461_);
return v___x_4471_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0(void){
_start:
{
uint32_t v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4491_ = 70;
v___x_4492_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4493_ = lean_string_push(v___x_4492_, v___x_4491_);
return v___x_4493_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1(void){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4494_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0);
v___x_4495_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4496_ = lean_string_append(v___x_4495_, v___x_4494_);
return v___x_4496_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2(void){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4497_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4498_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1);
v___x_4499_ = lean_string_append(v___x_4498_, v___x_4497_);
return v___x_4499_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3(void){
_start:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4500_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2);
v___x_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(lean_object* v_acc_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v_fst_4504_; lean_object* v_snd_4505_; lean_object* v_pos_4507_; lean_object* v_snd_4508_; lean_object* v_err_4509_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v_fst_4504_ = lean_ctor_get(v_a_4503_, 0);
v_snd_4505_ = lean_ctor_get(v_a_4503_, 1);
lean_inc(v_snd_4505_);
v___x_4513_ = lean_string_utf8_byte_size(v_fst_4504_);
v___x_4514_ = lean_nat_dec_eq(v_snd_4505_, v___x_4513_);
if (v___x_4514_ == 0)
{
uint32_t v___x_4515_; uint32_t v_c_4516_; uint8_t v___x_4517_; 
v___x_4515_ = 70;
v_c_4516_ = lean_string_utf8_get_fast(v_fst_4504_, v_snd_4505_);
v___x_4517_ = lean_uint32_dec_eq(v_c_4516_, v___x_4515_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; 
v___x_4518_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3);
lean_inc(v_snd_4505_);
v_pos_4507_ = v_a_4503_;
v_snd_4508_ = v_snd_4505_;
v_err_4509_ = v___x_4518_;
goto v___jp_4506_;
}
else
{
lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4528_; 
lean_inc(v_fst_4504_);
v_isSharedCheck_4528_ = !lean_is_exclusive(v_a_4503_);
if (v_isSharedCheck_4528_ == 0)
{
lean_object* v_unused_4529_; lean_object* v_unused_4530_; 
v_unused_4529_ = lean_ctor_get(v_a_4503_, 1);
lean_dec(v_unused_4529_);
v_unused_4530_ = lean_ctor_get(v_a_4503_, 0);
lean_dec(v_unused_4530_);
v___x_4520_ = v_a_4503_;
v_isShared_4521_ = v_isSharedCheck_4528_;
goto v_resetjp_4519_;
}
else
{
lean_dec(v_a_4503_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4528_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4522_; lean_object* v_it_x27_4524_; 
v___x_4522_ = lean_string_utf8_next_fast(v_fst_4504_, v_snd_4505_);
lean_dec(v_snd_4505_);
if (v_isShared_4521_ == 0)
{
lean_ctor_set(v___x_4520_, 1, v___x_4522_);
v_it_x27_4524_ = v___x_4520_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_fst_4504_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v___x_4522_);
v_it_x27_4524_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
lean_object* v___x_4525_; 
v___x_4525_ = lean_string_push(v_acc_4502_, v___x_4515_);
v_acc_4502_ = v___x_4525_;
v_a_4503_ = v_it_x27_4524_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4531_; 
v___x_4531_ = lean_box(0);
lean_inc(v_snd_4505_);
v_pos_4507_ = v_a_4503_;
v_snd_4508_ = v_snd_4505_;
v_err_4509_ = v___x_4531_;
goto v___jp_4506_;
}
v___jp_4506_:
{
uint8_t v___x_4510_; 
v___x_4510_ = lean_nat_dec_eq(v_snd_4505_, v_snd_4508_);
lean_dec(v_snd_4508_);
lean_dec(v_snd_4505_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; 
lean_dec_ref(v_acc_4502_);
lean_inc(v_err_4509_);
v___x_4511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4511_, 0, v_pos_4507_);
lean_ctor_set(v___x_4511_, 1, v_err_4509_);
return v___x_4511_;
}
else
{
lean_object* v___x_4512_; 
v___x_4512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4512_, 0, v_pos_4507_);
lean_ctor_set(v___x_4512_, 1, v_acc_4502_);
return v___x_4512_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0(void){
_start:
{
uint32_t v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = 66;
v___x_4533_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4534_ = lean_string_push(v___x_4533_, v___x_4532_);
return v___x_4534_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1(void){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0);
v___x_4536_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4537_ = lean_string_append(v___x_4536_, v___x_4535_);
return v___x_4537_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2(void){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4538_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4539_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1);
v___x_4540_ = lean_string_append(v___x_4539_, v___x_4538_);
return v___x_4540_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3(void){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2);
v___x_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(lean_object* v_acc_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v_fst_4545_; lean_object* v_snd_4546_; lean_object* v_pos_4548_; lean_object* v_snd_4549_; lean_object* v_err_4550_; lean_object* v___x_4554_; uint8_t v___x_4555_; 
v_fst_4545_ = lean_ctor_get(v_a_4544_, 0);
v_snd_4546_ = lean_ctor_get(v_a_4544_, 1);
lean_inc(v_snd_4546_);
v___x_4554_ = lean_string_utf8_byte_size(v_fst_4545_);
v___x_4555_ = lean_nat_dec_eq(v_snd_4546_, v___x_4554_);
if (v___x_4555_ == 0)
{
uint32_t v___x_4556_; uint32_t v_c_4557_; uint8_t v___x_4558_; 
v___x_4556_ = 66;
v_c_4557_ = lean_string_utf8_get_fast(v_fst_4545_, v_snd_4546_);
v___x_4558_ = lean_uint32_dec_eq(v_c_4557_, v___x_4556_);
if (v___x_4558_ == 0)
{
lean_object* v___x_4559_; 
v___x_4559_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3);
lean_inc(v_snd_4546_);
v_pos_4548_ = v_a_4544_;
v_snd_4549_ = v_snd_4546_;
v_err_4550_ = v___x_4559_;
goto v___jp_4547_;
}
else
{
lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4569_; 
lean_inc(v_fst_4545_);
v_isSharedCheck_4569_ = !lean_is_exclusive(v_a_4544_);
if (v_isSharedCheck_4569_ == 0)
{
lean_object* v_unused_4570_; lean_object* v_unused_4571_; 
v_unused_4570_ = lean_ctor_get(v_a_4544_, 1);
lean_dec(v_unused_4570_);
v_unused_4571_ = lean_ctor_get(v_a_4544_, 0);
lean_dec(v_unused_4571_);
v___x_4561_ = v_a_4544_;
v_isShared_4562_ = v_isSharedCheck_4569_;
goto v_resetjp_4560_;
}
else
{
lean_dec(v_a_4544_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4569_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4563_; lean_object* v_it_x27_4565_; 
v___x_4563_ = lean_string_utf8_next_fast(v_fst_4545_, v_snd_4546_);
lean_dec(v_snd_4546_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 1, v___x_4563_);
v_it_x27_4565_ = v___x_4561_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_fst_4545_);
lean_ctor_set(v_reuseFailAlloc_4568_, 1, v___x_4563_);
v_it_x27_4565_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
lean_object* v___x_4566_; 
v___x_4566_ = lean_string_push(v_acc_4543_, v___x_4556_);
v_acc_4543_ = v___x_4566_;
v_a_4544_ = v_it_x27_4565_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4572_; 
v___x_4572_ = lean_box(0);
lean_inc(v_snd_4546_);
v_pos_4548_ = v_a_4544_;
v_snd_4549_ = v_snd_4546_;
v_err_4550_ = v___x_4572_;
goto v___jp_4547_;
}
v___jp_4547_:
{
uint8_t v___x_4551_; 
v___x_4551_ = lean_nat_dec_eq(v_snd_4546_, v_snd_4549_);
lean_dec(v_snd_4549_);
lean_dec(v_snd_4546_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; 
lean_dec_ref(v_acc_4543_);
lean_inc(v_err_4550_);
v___x_4552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4552_, 0, v_pos_4548_);
lean_ctor_set(v___x_4552_, 1, v_err_4550_);
return v___x_4552_;
}
else
{
lean_object* v___x_4553_; 
v___x_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4553_, 0, v_pos_4548_);
lean_ctor_set(v___x_4553_, 1, v_acc_4543_);
return v___x_4553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier(lean_object* v_a_4610_){
_start:
{
lean_object* v___y_4612_; lean_object* v_fst_4615_; lean_object* v_snd_4616_; lean_object* v___f_4617_; lean_object* v_snd_4619_; lean_object* v___y_4620_; lean_object* v_pos_4621_; lean_object* v_snd_4657_; lean_object* v_pos_4658_; lean_object* v_err_4659_; lean_object* v___y_4662_; lean_object* v_snd_4663_; lean_object* v___f_4665_; lean_object* v_snd_4667_; lean_object* v___y_4668_; lean_object* v_pos_4669_; lean_object* v_snd_4698_; lean_object* v_pos_4699_; lean_object* v_err_4700_; lean_object* v___y_4703_; lean_object* v_snd_4704_; lean_object* v___f_4706_; lean_object* v_snd_4708_; lean_object* v___y_4709_; lean_object* v_pos_4710_; lean_object* v_snd_4739_; lean_object* v_pos_4740_; lean_object* v_err_4741_; lean_object* v___y_4744_; lean_object* v_snd_4745_; lean_object* v___f_4747_; lean_object* v_snd_4749_; lean_object* v___y_4750_; lean_object* v_pos_4751_; lean_object* v_snd_4780_; lean_object* v_pos_4781_; lean_object* v_err_4782_; lean_object* v___y_4785_; lean_object* v_snd_4786_; lean_object* v___f_4788_; lean_object* v_snd_4790_; lean_object* v___y_4791_; lean_object* v_pos_4792_; lean_object* v_snd_4821_; lean_object* v_pos_4822_; lean_object* v_err_4823_; lean_object* v___y_4826_; lean_object* v_snd_4827_; lean_object* v___f_4829_; lean_object* v_snd_4831_; lean_object* v___y_4832_; lean_object* v_pos_4833_; lean_object* v_snd_4862_; lean_object* v_pos_4863_; lean_object* v_err_4864_; lean_object* v___y_4867_; lean_object* v_snd_4868_; lean_object* v_snd_4871_; lean_object* v___y_4872_; lean_object* v_pos_4873_; lean_object* v_snd_4902_; lean_object* v_pos_4903_; lean_object* v_err_4904_; lean_object* v___y_4907_; lean_object* v_snd_4908_; lean_object* v___f_4910_; lean_object* v_snd_4912_; lean_object* v___y_4913_; lean_object* v_pos_4914_; lean_object* v_snd_4942_; lean_object* v_pos_4943_; lean_object* v_err_4944_; lean_object* v___y_4947_; lean_object* v_snd_4948_; lean_object* v___f_4950_; lean_object* v_snd_4952_; lean_object* v___y_4953_; lean_object* v_pos_4954_; lean_object* v_snd_4982_; lean_object* v_pos_4983_; lean_object* v_err_4984_; lean_object* v___y_4987_; lean_object* v_snd_4988_; lean_object* v___f_4990_; lean_object* v_snd_4992_; lean_object* v___y_4993_; lean_object* v_pos_4994_; lean_object* v_snd_5022_; lean_object* v_pos_5023_; lean_object* v_err_5024_; lean_object* v___y_5027_; lean_object* v_snd_5028_; lean_object* v___f_5030_; lean_object* v_snd_5032_; lean_object* v___y_5033_; lean_object* v_pos_5034_; lean_object* v_snd_5063_; lean_object* v_pos_5064_; lean_object* v_err_5065_; lean_object* v___y_5068_; lean_object* v_snd_5069_; lean_object* v___f_5071_; lean_object* v_snd_5073_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v_pos_5076_; lean_object* v_snd_5105_; lean_object* v___y_5106_; lean_object* v_pos_5107_; lean_object* v_err_5108_; lean_object* v___y_5111_; lean_object* v_snd_5112_; lean_object* v___y_5113_; lean_object* v___f_5115_; lean_object* v___y_5117_; lean_object* v_snd_5118_; lean_object* v___y_5119_; lean_object* v_pos_5120_; lean_object* v___y_5149_; lean_object* v_snd_5150_; lean_object* v_pos_5151_; lean_object* v_err_5152_; lean_object* v___y_5155_; lean_object* v___y_5156_; lean_object* v_snd_5157_; lean_object* v___f_5159_; lean_object* v_snd_5161_; lean_object* v___y_5162_; lean_object* v___y_5163_; lean_object* v_pos_5164_; lean_object* v_snd_5193_; lean_object* v___y_5194_; lean_object* v_pos_5195_; lean_object* v_err_5196_; lean_object* v___y_5199_; lean_object* v_snd_5200_; lean_object* v___y_5201_; lean_object* v___f_5203_; lean_object* v_snd_5205_; lean_object* v___y_5206_; lean_object* v___y_5207_; lean_object* v_pos_5208_; lean_object* v___y_5237_; lean_object* v_snd_5238_; lean_object* v_pos_5239_; lean_object* v_err_5240_; lean_object* v___y_5243_; lean_object* v___y_5244_; lean_object* v_snd_5245_; lean_object* v___f_5247_; lean_object* v_snd_5249_; lean_object* v___y_5250_; lean_object* v___y_5251_; lean_object* v_pos_5252_; lean_object* v_snd_5281_; lean_object* v___y_5282_; lean_object* v_pos_5283_; lean_object* v_err_5284_; lean_object* v___y_5287_; lean_object* v_snd_5288_; lean_object* v___y_5289_; lean_object* v___f_5291_; lean_object* v___y_5293_; lean_object* v_snd_5294_; lean_object* v___y_5295_; lean_object* v_pos_5296_; lean_object* v___y_5325_; lean_object* v_snd_5326_; lean_object* v_pos_5327_; lean_object* v_err_5328_; lean_object* v___y_5331_; lean_object* v___y_5332_; lean_object* v_snd_5333_; lean_object* v___y_5336_; lean_object* v_snd_5337_; lean_object* v___y_5338_; lean_object* v_pos_5339_; lean_object* v___y_5368_; lean_object* v_snd_5369_; lean_object* v_pos_5370_; lean_object* v_err_5371_; lean_object* v___y_5374_; lean_object* v___y_5375_; lean_object* v_snd_5376_; lean_object* v___y_5379_; lean_object* v_snd_5380_; lean_object* v___y_5381_; lean_object* v_pos_5382_; lean_object* v___y_5411_; lean_object* v_snd_5412_; lean_object* v_pos_5413_; lean_object* v_err_5414_; lean_object* v___y_5417_; lean_object* v___y_5418_; lean_object* v_snd_5419_; lean_object* v_snd_5422_; lean_object* v___y_5423_; lean_object* v___y_5424_; lean_object* v_pos_5425_; lean_object* v_snd_5454_; lean_object* v___y_5455_; lean_object* v_pos_5456_; lean_object* v_err_5457_; lean_object* v___y_5460_; lean_object* v_snd_5461_; lean_object* v___y_5462_; lean_object* v___f_5464_; lean_object* v_snd_5466_; lean_object* v___y_5467_; lean_object* v___y_5468_; lean_object* v___y_5469_; lean_object* v_pos_5470_; lean_object* v_snd_5499_; lean_object* v___y_5500_; lean_object* v___y_5501_; lean_object* v_pos_5502_; lean_object* v_err_5503_; lean_object* v___y_5506_; lean_object* v_snd_5507_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v___f_5511_; lean_object* v___y_5513_; lean_object* v_snd_5514_; lean_object* v___y_5515_; lean_object* v___y_5516_; lean_object* v_pos_5517_; lean_object* v___y_5546_; lean_object* v_snd_5547_; lean_object* v___y_5548_; lean_object* v_pos_5549_; lean_object* v_err_5550_; lean_object* v___y_5553_; lean_object* v___y_5554_; lean_object* v_snd_5555_; lean_object* v___y_5556_; lean_object* v___f_5558_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v_snd_5562_; lean_object* v___y_5563_; lean_object* v_pos_5564_; lean_object* v___y_5593_; lean_object* v___y_5594_; lean_object* v_snd_5595_; lean_object* v_pos_5596_; lean_object* v_err_5597_; lean_object* v___y_5600_; lean_object* v___y_5601_; lean_object* v___y_5602_; lean_object* v_snd_5603_; lean_object* v___f_5605_; lean_object* v___y_5607_; lean_object* v___y_5608_; lean_object* v___y_5609_; lean_object* v___y_5610_; lean_object* v_pos_5611_; lean_object* v___y_5640_; lean_object* v___y_5641_; lean_object* v___y_5642_; lean_object* v_pos_5643_; lean_object* v_err_5644_; lean_object* v___y_5647_; lean_object* v___y_5648_; lean_object* v___y_5649_; lean_object* v___y_5650_; lean_object* v___f_5652_; lean_object* v___y_5654_; lean_object* v_snd_5655_; lean_object* v___y_5656_; lean_object* v_pos_5657_; lean_object* v_snd_5687_; lean_object* v___y_5688_; lean_object* v_pos_5689_; lean_object* v_err_5690_; lean_object* v___y_5693_; lean_object* v___y_5694_; lean_object* v_snd_5695_; lean_object* v___f_5697_; lean_object* v___y_5699_; lean_object* v_snd_5700_; lean_object* v___y_5701_; lean_object* v_pos_5702_; lean_object* v___y_5731_; lean_object* v_snd_5732_; lean_object* v_pos_5733_; lean_object* v_err_5734_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v_snd_5739_; lean_object* v___f_5741_; lean_object* v___y_5743_; lean_object* v_snd_5744_; lean_object* v___y_5745_; lean_object* v_pos_5746_; lean_object* v___y_5775_; lean_object* v_snd_5776_; lean_object* v_pos_5777_; lean_object* v_err_5778_; lean_object* v___y_5781_; lean_object* v___y_5782_; lean_object* v_snd_5783_; lean_object* v___f_5785_; lean_object* v___y_5787_; lean_object* v___y_5788_; lean_object* v___y_5789_; lean_object* v_pos_5790_; lean_object* v___y_5819_; lean_object* v___y_5820_; lean_object* v_pos_5821_; lean_object* v_err_5822_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5827_; lean_object* v___f_5829_; lean_object* v_snd_5831_; lean_object* v___y_5832_; lean_object* v_pos_5833_; lean_object* v_snd_5863_; lean_object* v_pos_5864_; lean_object* v_err_5865_; lean_object* v___y_5868_; lean_object* v_snd_5869_; lean_object* v___f_5871_; lean_object* v_snd_5873_; lean_object* v___y_5874_; lean_object* v_pos_5875_; lean_object* v_snd_5904_; lean_object* v_pos_5905_; lean_object* v_err_5906_; lean_object* v___y_5909_; lean_object* v_snd_5910_; lean_object* v___f_5912_; lean_object* v_snd_5914_; lean_object* v___y_5915_; lean_object* v_pos_5916_; lean_object* v_snd_5945_; lean_object* v_pos_5946_; lean_object* v_err_5947_; lean_object* v___y_5950_; lean_object* v_snd_5951_; lean_object* v___f_5953_; lean_object* v_snd_5955_; lean_object* v___y_5956_; lean_object* v_pos_5957_; lean_object* v_snd_5987_; lean_object* v_pos_5988_; lean_object* v_err_5989_; lean_object* v___y_5992_; lean_object* v_snd_5993_; lean_object* v___f_5995_; lean_object* v_snd_5997_; lean_object* v___y_5998_; lean_object* v_pos_5999_; lean_object* v_snd_6028_; lean_object* v_pos_6029_; lean_object* v_err_6030_; lean_object* v___y_6033_; lean_object* v_snd_6034_; lean_object* v___f_6036_; lean_object* v_snd_6038_; lean_object* v___y_6039_; lean_object* v_pos_6040_; lean_object* v_snd_6069_; lean_object* v_pos_6070_; lean_object* v_err_6071_; lean_object* v___y_6074_; lean_object* v_snd_6075_; lean_object* v___f_6077_; lean_object* v___y_6079_; lean_object* v_pos_6080_; lean_object* v_pos_6109_; lean_object* v_err_6110_; lean_object* v___x_6112_; uint8_t v___x_6113_; 
v_fst_4615_ = lean_ctor_get(v_a_4610_, 0);
v_snd_4616_ = lean_ctor_get(v_a_4610_, 1);
lean_inc(v_snd_4616_);
v___f_4617_ = ((lean_object*)(l_Std_Time_parseModifier___closed__0));
v___f_4665_ = ((lean_object*)(l_Std_Time_parseModifier___closed__1));
v___f_4706_ = ((lean_object*)(l_Std_Time_parseModifier___closed__2));
v___f_4747_ = ((lean_object*)(l_Std_Time_parseModifier___closed__3));
v___f_4788_ = ((lean_object*)(l_Std_Time_parseModifier___closed__4));
v___f_4829_ = ((lean_object*)(l_Std_Time_parseModifier___closed__5));
v___f_4910_ = ((lean_object*)(l_Std_Time_parseModifier___closed__6));
v___f_4950_ = ((lean_object*)(l_Std_Time_parseModifier___closed__7));
v___f_4990_ = ((lean_object*)(l_Std_Time_parseModifier___closed__8));
v___f_5030_ = ((lean_object*)(l_Std_Time_parseModifier___closed__9));
v___f_5071_ = ((lean_object*)(l_Std_Time_parseModifier___closed__10));
v___f_5115_ = ((lean_object*)(l_Std_Time_parseModifier___closed__11));
v___f_5159_ = ((lean_object*)(l_Std_Time_parseModifier___closed__12));
v___f_5203_ = ((lean_object*)(l_Std_Time_parseModifier___closed__13));
v___f_5247_ = ((lean_object*)(l_Std_Time_parseModifier___closed__14));
v___f_5291_ = ((lean_object*)(l_Std_Time_parseModifier___closed__15));
v___f_5464_ = ((lean_object*)(l_Std_Time_parseModifier___closed__16));
v___f_5511_ = ((lean_object*)(l_Std_Time_parseModifier___closed__17));
v___f_5558_ = ((lean_object*)(l_Std_Time_parseModifier___closed__18));
v___f_5605_ = ((lean_object*)(l_Std_Time_parseModifier___closed__19));
v___f_5652_ = ((lean_object*)(l_Std_Time_parseModifier___closed__20));
v___f_5697_ = ((lean_object*)(l_Std_Time_parseModifier___closed__22));
v___f_5741_ = ((lean_object*)(l_Std_Time_parseModifier___closed__23));
v___f_5785_ = ((lean_object*)(l_Std_Time_parseModifier___closed__24));
v___f_5829_ = ((lean_object*)(l_Std_Time_parseModifier___closed__25));
v___f_5871_ = ((lean_object*)(l_Std_Time_parseModifier___closed__27));
v___f_5912_ = ((lean_object*)(l_Std_Time_parseModifier___closed__28));
v___f_5953_ = ((lean_object*)(l_Std_Time_parseModifier___closed__29));
v___f_5995_ = ((lean_object*)(l_Std_Time_parseModifier___closed__31));
v___f_6036_ = ((lean_object*)(l_Std_Time_parseModifier___closed__32));
v___f_6077_ = ((lean_object*)(l_Std_Time_parseModifier___closed__33));
v___x_6112_ = lean_string_utf8_byte_size(v_fst_4615_);
v___x_6113_ = lean_nat_dec_eq(v_snd_4616_, v___x_6112_);
if (v___x_6113_ == 0)
{
uint32_t v___x_6114_; uint32_t v_c_6115_; uint8_t v___x_6116_; 
v___x_6114_ = 71;
v_c_6115_ = lean_string_utf8_get_fast(v_fst_4615_, v_snd_4616_);
v___x_6116_ = lean_uint32_dec_eq(v_c_6115_, v___x_6114_);
if (v___x_6116_ == 0)
{
lean_object* v___x_6117_; 
v___x_6117_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3);
v_pos_6109_ = v_a_4610_;
v_err_6110_ = v___x_6117_;
goto v___jp_6108_;
}
else
{
lean_object* v___x_6119_; uint8_t v_isShared_6120_; uint8_t v_isSharedCheck_6134_; 
lean_inc(v_fst_4615_);
v_isSharedCheck_6134_ = !lean_is_exclusive(v_a_4610_);
if (v_isSharedCheck_6134_ == 0)
{
lean_object* v_unused_6135_; lean_object* v_unused_6136_; 
v_unused_6135_ = lean_ctor_get(v_a_4610_, 1);
lean_dec(v_unused_6135_);
v_unused_6136_ = lean_ctor_get(v_a_4610_, 0);
lean_dec(v_unused_6136_);
v___x_6119_ = v_a_4610_;
v_isShared_6120_ = v_isSharedCheck_6134_;
goto v_resetjp_6118_;
}
else
{
lean_dec(v_a_4610_);
v___x_6119_ = lean_box(0);
v_isShared_6120_ = v_isSharedCheck_6134_;
goto v_resetjp_6118_;
}
v_resetjp_6118_:
{
lean_object* v___x_6121_; lean_object* v_it_x27_6123_; 
v___x_6121_ = lean_string_utf8_next_fast(v_fst_4615_, v_snd_4616_);
if (v_isShared_6120_ == 0)
{
lean_ctor_set(v___x_6119_, 1, v___x_6121_);
v_it_x27_6123_ = v___x_6119_;
goto v_reusejp_6122_;
}
else
{
lean_object* v_reuseFailAlloc_6133_; 
v_reuseFailAlloc_6133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6133_, 0, v_fst_4615_);
lean_ctor_set(v_reuseFailAlloc_6133_, 1, v___x_6121_);
v_it_x27_6123_ = v_reuseFailAlloc_6133_;
goto v_reusejp_6122_;
}
v_reusejp_6122_:
{
lean_object* v___x_6124_; lean_object* v___x_6125_; 
v___x_6124_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0);
v___x_6125_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(v___x_6124_, v_it_x27_6123_);
if (lean_obj_tag(v___x_6125_) == 0)
{
lean_object* v_pos_6126_; lean_object* v_res_6127_; lean_object* v___f_6128_; lean_object* v___x_6129_; 
v_pos_6126_ = lean_ctor_get(v___x_6125_, 0);
lean_inc(v_pos_6126_);
v_res_6127_ = lean_ctor_get(v___x_6125_, 1);
lean_inc(v_res_6127_);
lean_dec_ref_known(v___x_6125_, 2);
v___f_6128_ = ((lean_object*)(l_Std_Time_parseModifier___closed__34));
v___x_6129_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_6128_, v_res_6127_, v_pos_6126_);
if (lean_obj_tag(v___x_6129_) == 0)
{
lean_dec(v_snd_4616_);
return v___x_6129_;
}
else
{
lean_object* v_pos_6130_; 
v_pos_6130_ = lean_ctor_get(v___x_6129_, 0);
lean_inc(v_pos_6130_);
v___y_6079_ = v___x_6129_;
v_pos_6080_ = v_pos_6130_;
goto v___jp_6078_;
}
}
else
{
lean_object* v_pos_6131_; lean_object* v_err_6132_; 
v_pos_6131_ = lean_ctor_get(v___x_6125_, 0);
lean_inc(v_pos_6131_);
v_err_6132_ = lean_ctor_get(v___x_6125_, 1);
lean_inc(v_err_6132_);
lean_dec_ref_known(v___x_6125_, 2);
v_pos_6109_ = v_pos_6131_;
v_err_6110_ = v_err_6132_;
goto v___jp_6108_;
}
}
}
}
}
else
{
lean_object* v___x_6137_; 
v___x_6137_ = lean_box(0);
v_pos_6109_ = v_a_4610_;
v_err_6110_ = v___x_6137_;
goto v___jp_6108_;
}
v___jp_4611_:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4613_ = lean_box(0);
v___x_4614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4614_, 0, v___y_4612_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
return v___x_4614_;
}
v___jp_4618_:
{
lean_object* v_fst_4622_; lean_object* v_snd_4623_; uint8_t v___x_4624_; 
v_fst_4622_ = lean_ctor_get(v_pos_4621_, 0);
v_snd_4623_ = lean_ctor_get(v_pos_4621_, 1);
v___x_4624_ = lean_nat_dec_eq(v_snd_4619_, v_snd_4623_);
lean_dec(v_snd_4619_);
if (v___x_4624_ == 0)
{
lean_dec_ref(v_pos_4621_);
return v___y_4620_;
}
else
{
lean_object* v___x_4625_; uint8_t v___x_4626_; 
lean_dec_ref(v___y_4620_);
v___x_4625_ = lean_string_utf8_byte_size(v_fst_4622_);
v___x_4626_ = lean_nat_dec_eq(v_snd_4623_, v___x_4625_);
if (v___x_4626_ == 0)
{
if (v___x_4624_ == 0)
{
v___y_4612_ = v_pos_4621_;
goto v___jp_4611_;
}
else
{
uint32_t v___x_4627_; uint32_t v_c_4628_; uint8_t v___x_4629_; 
v___x_4627_ = 90;
v_c_4628_ = lean_string_utf8_get_fast(v_fst_4622_, v_snd_4623_);
v___x_4629_ = lean_uint32_dec_eq(v_c_4628_, v___x_4627_);
if (v___x_4629_ == 0)
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3);
v___x_4631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4631_, 0, v_pos_4621_);
lean_ctor_set(v___x_4631_, 1, v___x_4630_);
return v___x_4631_;
}
else
{
lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4653_; 
lean_inc(v_snd_4623_);
lean_inc(v_fst_4622_);
v_isSharedCheck_4653_ = !lean_is_exclusive(v_pos_4621_);
if (v_isSharedCheck_4653_ == 0)
{
lean_object* v_unused_4654_; lean_object* v_unused_4655_; 
v_unused_4654_ = lean_ctor_get(v_pos_4621_, 1);
lean_dec(v_unused_4654_);
v_unused_4655_ = lean_ctor_get(v_pos_4621_, 0);
lean_dec(v_unused_4655_);
v___x_4633_ = v_pos_4621_;
v_isShared_4634_ = v_isSharedCheck_4653_;
goto v_resetjp_4632_;
}
else
{
lean_dec(v_pos_4621_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4653_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4635_; lean_object* v_it_x27_4637_; 
v___x_4635_ = lean_string_utf8_next_fast(v_fst_4622_, v_snd_4623_);
lean_dec(v_snd_4623_);
if (v_isShared_4634_ == 0)
{
lean_ctor_set(v___x_4633_, 1, v___x_4635_);
v_it_x27_4637_ = v___x_4633_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_fst_4622_);
lean_ctor_set(v_reuseFailAlloc_4652_, 1, v___x_4635_);
v_it_x27_4637_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0);
v___x_4639_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(v___x_4638_, v_it_x27_4637_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v_pos_4640_; lean_object* v_res_4641_; lean_object* v___x_4642_; 
v_pos_4640_ = lean_ctor_get(v___x_4639_, 0);
lean_inc(v_pos_4640_);
v_res_4641_ = lean_ctor_get(v___x_4639_, 1);
lean_inc(v_res_4641_);
lean_dec_ref_known(v___x_4639_, 2);
v___x_4642_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(v___f_4617_, v_res_4641_, v_pos_4640_);
return v___x_4642_;
}
else
{
lean_object* v_pos_4643_; lean_object* v_err_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
v_pos_4643_ = lean_ctor_get(v___x_4639_, 0);
v_err_4644_ = lean_ctor_get(v___x_4639_, 1);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4639_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_err_4644_);
lean_inc(v_pos_4643_);
lean_dec(v___x_4639_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_pos_4643_);
lean_ctor_set(v_reuseFailAlloc_4650_, 1, v_err_4644_);
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
}
}
}
else
{
v___y_4612_ = v_pos_4621_;
goto v___jp_4611_;
}
}
}
v___jp_4656_:
{
lean_object* v___x_4660_; 
lean_inc_ref(v_pos_4658_);
v___x_4660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4660_, 0, v_pos_4658_);
lean_ctor_set(v___x_4660_, 1, v_err_4659_);
v_snd_4619_ = v_snd_4657_;
v___y_4620_ = v___x_4660_;
v_pos_4621_ = v_pos_4658_;
goto v___jp_4618_;
}
v___jp_4661_:
{
lean_object* v___x_4664_; 
v___x_4664_ = lean_box(0);
v_snd_4657_ = v_snd_4663_;
v_pos_4658_ = v___y_4662_;
v_err_4659_ = v___x_4664_;
goto v___jp_4656_;
}
v___jp_4666_:
{
lean_object* v_fst_4670_; lean_object* v_snd_4671_; uint8_t v___x_4672_; 
v_fst_4670_ = lean_ctor_get(v_pos_4669_, 0);
v_snd_4671_ = lean_ctor_get(v_pos_4669_, 1);
lean_inc(v_snd_4671_);
v___x_4672_ = lean_nat_dec_eq(v_snd_4667_, v_snd_4671_);
lean_dec(v_snd_4667_);
if (v___x_4672_ == 0)
{
lean_dec(v_snd_4671_);
lean_dec_ref(v_pos_4669_);
return v___y_4668_;
}
else
{
lean_object* v___x_4673_; uint8_t v___x_4674_; 
lean_dec_ref(v___y_4668_);
v___x_4673_ = lean_string_utf8_byte_size(v_fst_4670_);
v___x_4674_ = lean_nat_dec_eq(v_snd_4671_, v___x_4673_);
if (v___x_4674_ == 0)
{
if (v___x_4672_ == 0)
{
v___y_4662_ = v_pos_4669_;
v_snd_4663_ = v_snd_4671_;
goto v___jp_4661_;
}
else
{
uint32_t v___x_4675_; uint32_t v_c_4676_; uint8_t v___x_4677_; 
v___x_4675_ = 120;
v_c_4676_ = lean_string_utf8_get_fast(v_fst_4670_, v_snd_4671_);
v___x_4677_ = lean_uint32_dec_eq(v_c_4676_, v___x_4675_);
if (v___x_4677_ == 0)
{
lean_object* v___x_4678_; 
v___x_4678_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4);
v_snd_4657_ = v_snd_4671_;
v_pos_4658_ = v_pos_4669_;
v_err_4659_ = v___x_4678_;
goto v___jp_4656_;
}
else
{
lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4694_; 
lean_inc(v_fst_4670_);
v_isSharedCheck_4694_ = !lean_is_exclusive(v_pos_4669_);
if (v_isSharedCheck_4694_ == 0)
{
lean_object* v_unused_4695_; lean_object* v_unused_4696_; 
v_unused_4695_ = lean_ctor_get(v_pos_4669_, 1);
lean_dec(v_unused_4695_);
v_unused_4696_ = lean_ctor_get(v_pos_4669_, 0);
lean_dec(v_unused_4696_);
v___x_4680_ = v_pos_4669_;
v_isShared_4681_ = v_isSharedCheck_4694_;
goto v_resetjp_4679_;
}
else
{
lean_dec(v_pos_4669_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4694_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4682_; lean_object* v_it_x27_4684_; 
v___x_4682_ = lean_string_utf8_next_fast(v_fst_4670_, v_snd_4671_);
if (v_isShared_4681_ == 0)
{
lean_ctor_set(v___x_4680_, 1, v___x_4682_);
v_it_x27_4684_ = v___x_4680_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_fst_4670_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v___x_4682_);
v_it_x27_4684_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4685_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1);
v___x_4686_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(v___x_4685_, v_it_x27_4684_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_pos_4687_; lean_object* v_res_4688_; lean_object* v___x_4689_; 
v_pos_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_pos_4687_);
v_res_4688_ = lean_ctor_get(v___x_4686_, 1);
lean_inc(v_res_4688_);
lean_dec_ref_known(v___x_4686_, 2);
v___x_4689_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4665_, v_res_4688_, v_pos_4687_);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_dec(v_snd_4671_);
return v___x_4689_;
}
else
{
lean_object* v_pos_4690_; 
v_pos_4690_ = lean_ctor_get(v___x_4689_, 0);
lean_inc(v_pos_4690_);
v_snd_4619_ = v_snd_4671_;
v___y_4620_ = v___x_4689_;
v_pos_4621_ = v_pos_4690_;
goto v___jp_4618_;
}
}
else
{
lean_object* v_pos_4691_; lean_object* v_err_4692_; 
v_pos_4691_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_pos_4691_);
v_err_4692_ = lean_ctor_get(v___x_4686_, 1);
lean_inc(v_err_4692_);
lean_dec_ref_known(v___x_4686_, 2);
v_snd_4657_ = v_snd_4671_;
v_pos_4658_ = v_pos_4691_;
v_err_4659_ = v_err_4692_;
goto v___jp_4656_;
}
}
}
}
}
}
else
{
v___y_4662_ = v_pos_4669_;
v_snd_4663_ = v_snd_4671_;
goto v___jp_4661_;
}
}
}
v___jp_4697_:
{
lean_object* v___x_4701_; 
lean_inc_ref(v_pos_4699_);
v___x_4701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4701_, 0, v_pos_4699_);
lean_ctor_set(v___x_4701_, 1, v_err_4700_);
v_snd_4667_ = v_snd_4698_;
v___y_4668_ = v___x_4701_;
v_pos_4669_ = v_pos_4699_;
goto v___jp_4666_;
}
v___jp_4702_:
{
lean_object* v___x_4705_; 
v___x_4705_ = lean_box(0);
v_snd_4698_ = v_snd_4704_;
v_pos_4699_ = v___y_4703_;
v_err_4700_ = v___x_4705_;
goto v___jp_4697_;
}
v___jp_4707_:
{
lean_object* v_fst_4711_; lean_object* v_snd_4712_; uint8_t v___x_4713_; 
v_fst_4711_ = lean_ctor_get(v_pos_4710_, 0);
v_snd_4712_ = lean_ctor_get(v_pos_4710_, 1);
lean_inc(v_snd_4712_);
v___x_4713_ = lean_nat_dec_eq(v_snd_4708_, v_snd_4712_);
lean_dec(v_snd_4708_);
if (v___x_4713_ == 0)
{
lean_dec(v_snd_4712_);
lean_dec_ref(v_pos_4710_);
return v___y_4709_;
}
else
{
lean_object* v___x_4714_; uint8_t v___x_4715_; 
lean_dec_ref(v___y_4709_);
v___x_4714_ = lean_string_utf8_byte_size(v_fst_4711_);
v___x_4715_ = lean_nat_dec_eq(v_snd_4712_, v___x_4714_);
if (v___x_4715_ == 0)
{
if (v___x_4713_ == 0)
{
v___y_4703_ = v_pos_4710_;
v_snd_4704_ = v_snd_4712_;
goto v___jp_4702_;
}
else
{
uint32_t v___x_4716_; uint32_t v_c_4717_; uint8_t v___x_4718_; 
v___x_4716_ = 88;
v_c_4717_ = lean_string_utf8_get_fast(v_fst_4711_, v_snd_4712_);
v___x_4718_ = lean_uint32_dec_eq(v_c_4717_, v___x_4716_);
if (v___x_4718_ == 0)
{
lean_object* v___x_4719_; 
v___x_4719_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3);
v_snd_4698_ = v_snd_4712_;
v_pos_4699_ = v_pos_4710_;
v_err_4700_ = v___x_4719_;
goto v___jp_4697_;
}
else
{
lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4735_; 
lean_inc(v_fst_4711_);
v_isSharedCheck_4735_ = !lean_is_exclusive(v_pos_4710_);
if (v_isSharedCheck_4735_ == 0)
{
lean_object* v_unused_4736_; lean_object* v_unused_4737_; 
v_unused_4736_ = lean_ctor_get(v_pos_4710_, 1);
lean_dec(v_unused_4736_);
v_unused_4737_ = lean_ctor_get(v_pos_4710_, 0);
lean_dec(v_unused_4737_);
v___x_4721_ = v_pos_4710_;
v_isShared_4722_ = v_isSharedCheck_4735_;
goto v_resetjp_4720_;
}
else
{
lean_dec(v_pos_4710_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4735_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4723_; lean_object* v_it_x27_4725_; 
v___x_4723_ = lean_string_utf8_next_fast(v_fst_4711_, v_snd_4712_);
if (v_isShared_4722_ == 0)
{
lean_ctor_set(v___x_4721_, 1, v___x_4723_);
v_it_x27_4725_ = v___x_4721_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_fst_4711_);
lean_ctor_set(v_reuseFailAlloc_4734_, 1, v___x_4723_);
v_it_x27_4725_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0);
v___x_4727_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(v___x_4726_, v_it_x27_4725_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_pos_4728_; lean_object* v_res_4729_; lean_object* v___x_4730_; 
v_pos_4728_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_pos_4728_);
v_res_4729_ = lean_ctor_get(v___x_4727_, 1);
lean_inc(v_res_4729_);
lean_dec_ref_known(v___x_4727_, 2);
v___x_4730_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4706_, v_res_4729_, v_pos_4728_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_dec(v_snd_4712_);
return v___x_4730_;
}
else
{
lean_object* v_pos_4731_; 
v_pos_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_pos_4731_);
v_snd_4667_ = v_snd_4712_;
v___y_4668_ = v___x_4730_;
v_pos_4669_ = v_pos_4731_;
goto v___jp_4666_;
}
}
else
{
lean_object* v_pos_4732_; lean_object* v_err_4733_; 
v_pos_4732_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_pos_4732_);
v_err_4733_ = lean_ctor_get(v___x_4727_, 1);
lean_inc(v_err_4733_);
lean_dec_ref_known(v___x_4727_, 2);
v_snd_4698_ = v_snd_4712_;
v_pos_4699_ = v_pos_4732_;
v_err_4700_ = v_err_4733_;
goto v___jp_4697_;
}
}
}
}
}
}
else
{
v___y_4703_ = v_pos_4710_;
v_snd_4704_ = v_snd_4712_;
goto v___jp_4702_;
}
}
}
v___jp_4738_:
{
lean_object* v___x_4742_; 
lean_inc_ref(v_pos_4740_);
v___x_4742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4742_, 0, v_pos_4740_);
lean_ctor_set(v___x_4742_, 1, v_err_4741_);
v_snd_4708_ = v_snd_4739_;
v___y_4709_ = v___x_4742_;
v_pos_4710_ = v_pos_4740_;
goto v___jp_4707_;
}
v___jp_4743_:
{
lean_object* v___x_4746_; 
v___x_4746_ = lean_box(0);
v_snd_4739_ = v_snd_4745_;
v_pos_4740_ = v___y_4744_;
v_err_4741_ = v___x_4746_;
goto v___jp_4738_;
}
v___jp_4748_:
{
lean_object* v_fst_4752_; lean_object* v_snd_4753_; uint8_t v___x_4754_; 
v_fst_4752_ = lean_ctor_get(v_pos_4751_, 0);
v_snd_4753_ = lean_ctor_get(v_pos_4751_, 1);
lean_inc(v_snd_4753_);
v___x_4754_ = lean_nat_dec_eq(v_snd_4749_, v_snd_4753_);
lean_dec(v_snd_4749_);
if (v___x_4754_ == 0)
{
lean_dec(v_snd_4753_);
lean_dec_ref(v_pos_4751_);
return v___y_4750_;
}
else
{
lean_object* v___x_4755_; uint8_t v___x_4756_; 
lean_dec_ref(v___y_4750_);
v___x_4755_ = lean_string_utf8_byte_size(v_fst_4752_);
v___x_4756_ = lean_nat_dec_eq(v_snd_4753_, v___x_4755_);
if (v___x_4756_ == 0)
{
if (v___x_4754_ == 0)
{
v___y_4744_ = v_pos_4751_;
v_snd_4745_ = v_snd_4753_;
goto v___jp_4743_;
}
else
{
uint32_t v___x_4757_; uint32_t v_c_4758_; uint8_t v___x_4759_; 
v___x_4757_ = 79;
v_c_4758_ = lean_string_utf8_get_fast(v_fst_4752_, v_snd_4753_);
v___x_4759_ = lean_uint32_dec_eq(v_c_4758_, v___x_4757_);
if (v___x_4759_ == 0)
{
lean_object* v___x_4760_; 
v___x_4760_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3);
v_snd_4739_ = v_snd_4753_;
v_pos_4740_ = v_pos_4751_;
v_err_4741_ = v___x_4760_;
goto v___jp_4738_;
}
else
{
lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4776_; 
lean_inc(v_fst_4752_);
v_isSharedCheck_4776_ = !lean_is_exclusive(v_pos_4751_);
if (v_isSharedCheck_4776_ == 0)
{
lean_object* v_unused_4777_; lean_object* v_unused_4778_; 
v_unused_4777_ = lean_ctor_get(v_pos_4751_, 1);
lean_dec(v_unused_4777_);
v_unused_4778_ = lean_ctor_get(v_pos_4751_, 0);
lean_dec(v_unused_4778_);
v___x_4762_ = v_pos_4751_;
v_isShared_4763_ = v_isSharedCheck_4776_;
goto v_resetjp_4761_;
}
else
{
lean_dec(v_pos_4751_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4776_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4764_; lean_object* v_it_x27_4766_; 
v___x_4764_ = lean_string_utf8_next_fast(v_fst_4752_, v_snd_4753_);
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 1, v___x_4764_);
v_it_x27_4766_ = v___x_4762_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_fst_4752_);
lean_ctor_set(v_reuseFailAlloc_4775_, 1, v___x_4764_);
v_it_x27_4766_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4767_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0);
v___x_4768_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(v___x_4767_, v_it_x27_4766_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_pos_4769_; lean_object* v_res_4770_; lean_object* v___x_4771_; 
v_pos_4769_ = lean_ctor_get(v___x_4768_, 0);
lean_inc(v_pos_4769_);
v_res_4770_ = lean_ctor_get(v___x_4768_, 1);
lean_inc(v_res_4770_);
lean_dec_ref_known(v___x_4768_, 2);
v___x_4771_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(v___f_4747_, v_res_4770_, v_pos_4769_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_dec(v_snd_4753_);
return v___x_4771_;
}
else
{
lean_object* v_pos_4772_; 
v_pos_4772_ = lean_ctor_get(v___x_4771_, 0);
lean_inc(v_pos_4772_);
v_snd_4708_ = v_snd_4753_;
v___y_4709_ = v___x_4771_;
v_pos_4710_ = v_pos_4772_;
goto v___jp_4707_;
}
}
else
{
lean_object* v_pos_4773_; lean_object* v_err_4774_; 
v_pos_4773_ = lean_ctor_get(v___x_4768_, 0);
lean_inc(v_pos_4773_);
v_err_4774_ = lean_ctor_get(v___x_4768_, 1);
lean_inc(v_err_4774_);
lean_dec_ref_known(v___x_4768_, 2);
v_snd_4739_ = v_snd_4753_;
v_pos_4740_ = v_pos_4773_;
v_err_4741_ = v_err_4774_;
goto v___jp_4738_;
}
}
}
}
}
}
else
{
v___y_4744_ = v_pos_4751_;
v_snd_4745_ = v_snd_4753_;
goto v___jp_4743_;
}
}
}
v___jp_4779_:
{
lean_object* v___x_4783_; 
lean_inc_ref(v_pos_4781_);
v___x_4783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4783_, 0, v_pos_4781_);
lean_ctor_set(v___x_4783_, 1, v_err_4782_);
v_snd_4749_ = v_snd_4780_;
v___y_4750_ = v___x_4783_;
v_pos_4751_ = v_pos_4781_;
goto v___jp_4748_;
}
v___jp_4784_:
{
lean_object* v___x_4787_; 
v___x_4787_ = lean_box(0);
v_snd_4780_ = v_snd_4786_;
v_pos_4781_ = v___y_4785_;
v_err_4782_ = v___x_4787_;
goto v___jp_4779_;
}
v___jp_4789_:
{
lean_object* v_fst_4793_; lean_object* v_snd_4794_; uint8_t v___x_4795_; 
v_fst_4793_ = lean_ctor_get(v_pos_4792_, 0);
v_snd_4794_ = lean_ctor_get(v_pos_4792_, 1);
lean_inc(v_snd_4794_);
v___x_4795_ = lean_nat_dec_eq(v_snd_4790_, v_snd_4794_);
lean_dec(v_snd_4790_);
if (v___x_4795_ == 0)
{
lean_dec(v_snd_4794_);
lean_dec_ref(v_pos_4792_);
return v___y_4791_;
}
else
{
lean_object* v___x_4796_; uint8_t v___x_4797_; 
lean_dec_ref(v___y_4791_);
v___x_4796_ = lean_string_utf8_byte_size(v_fst_4793_);
v___x_4797_ = lean_nat_dec_eq(v_snd_4794_, v___x_4796_);
if (v___x_4797_ == 0)
{
if (v___x_4795_ == 0)
{
v___y_4785_ = v_pos_4792_;
v_snd_4786_ = v_snd_4794_;
goto v___jp_4784_;
}
else
{
uint32_t v___x_4798_; uint32_t v_c_4799_; uint8_t v___x_4800_; 
v___x_4798_ = 118;
v_c_4799_ = lean_string_utf8_get_fast(v_fst_4793_, v_snd_4794_);
v___x_4800_ = lean_uint32_dec_eq(v_c_4799_, v___x_4798_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; 
v___x_4801_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3);
v_snd_4780_ = v_snd_4794_;
v_pos_4781_ = v_pos_4792_;
v_err_4782_ = v___x_4801_;
goto v___jp_4779_;
}
else
{
lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4817_; 
lean_inc(v_fst_4793_);
v_isSharedCheck_4817_ = !lean_is_exclusive(v_pos_4792_);
if (v_isSharedCheck_4817_ == 0)
{
lean_object* v_unused_4818_; lean_object* v_unused_4819_; 
v_unused_4818_ = lean_ctor_get(v_pos_4792_, 1);
lean_dec(v_unused_4818_);
v_unused_4819_ = lean_ctor_get(v_pos_4792_, 0);
lean_dec(v_unused_4819_);
v___x_4803_ = v_pos_4792_;
v_isShared_4804_ = v_isSharedCheck_4817_;
goto v_resetjp_4802_;
}
else
{
lean_dec(v_pos_4792_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4817_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4805_; lean_object* v_it_x27_4807_; 
v___x_4805_ = lean_string_utf8_next_fast(v_fst_4793_, v_snd_4794_);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 1, v___x_4805_);
v_it_x27_4807_ = v___x_4803_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_fst_4793_);
lean_ctor_set(v_reuseFailAlloc_4816_, 1, v___x_4805_);
v_it_x27_4807_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4808_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0);
v___x_4809_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(v___x_4808_, v_it_x27_4807_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_pos_4810_; lean_object* v_res_4811_; lean_object* v___x_4812_; 
v_pos_4810_ = lean_ctor_get(v___x_4809_, 0);
lean_inc(v_pos_4810_);
v_res_4811_ = lean_ctor_get(v___x_4809_, 1);
lean_inc(v_res_4811_);
lean_dec_ref_known(v___x_4809_, 2);
v___x_4812_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4788_, v_res_4811_, v_pos_4810_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_dec(v_snd_4794_);
return v___x_4812_;
}
else
{
lean_object* v_pos_4813_; 
v_pos_4813_ = lean_ctor_get(v___x_4812_, 0);
lean_inc(v_pos_4813_);
v_snd_4749_ = v_snd_4794_;
v___y_4750_ = v___x_4812_;
v_pos_4751_ = v_pos_4813_;
goto v___jp_4748_;
}
}
else
{
lean_object* v_pos_4814_; lean_object* v_err_4815_; 
v_pos_4814_ = lean_ctor_get(v___x_4809_, 0);
lean_inc(v_pos_4814_);
v_err_4815_ = lean_ctor_get(v___x_4809_, 1);
lean_inc(v_err_4815_);
lean_dec_ref_known(v___x_4809_, 2);
v_snd_4780_ = v_snd_4794_;
v_pos_4781_ = v_pos_4814_;
v_err_4782_ = v_err_4815_;
goto v___jp_4779_;
}
}
}
}
}
}
else
{
v___y_4785_ = v_pos_4792_;
v_snd_4786_ = v_snd_4794_;
goto v___jp_4784_;
}
}
}
v___jp_4820_:
{
lean_object* v___x_4824_; 
lean_inc_ref(v_pos_4822_);
v___x_4824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4824_, 0, v_pos_4822_);
lean_ctor_set(v___x_4824_, 1, v_err_4823_);
v_snd_4790_ = v_snd_4821_;
v___y_4791_ = v___x_4824_;
v_pos_4792_ = v_pos_4822_;
goto v___jp_4789_;
}
v___jp_4825_:
{
lean_object* v___x_4828_; 
v___x_4828_ = lean_box(0);
v_snd_4821_ = v_snd_4827_;
v_pos_4822_ = v___y_4826_;
v_err_4823_ = v___x_4828_;
goto v___jp_4820_;
}
v___jp_4830_:
{
lean_object* v_fst_4834_; lean_object* v_snd_4835_; uint8_t v___x_4836_; 
v_fst_4834_ = lean_ctor_get(v_pos_4833_, 0);
v_snd_4835_ = lean_ctor_get(v_pos_4833_, 1);
lean_inc(v_snd_4835_);
v___x_4836_ = lean_nat_dec_eq(v_snd_4831_, v_snd_4835_);
lean_dec(v_snd_4831_);
if (v___x_4836_ == 0)
{
lean_dec(v_snd_4835_);
lean_dec_ref(v_pos_4833_);
return v___y_4832_;
}
else
{
lean_object* v___x_4837_; uint8_t v___x_4838_; 
lean_dec_ref(v___y_4832_);
v___x_4837_ = lean_string_utf8_byte_size(v_fst_4834_);
v___x_4838_ = lean_nat_dec_eq(v_snd_4835_, v___x_4837_);
if (v___x_4838_ == 0)
{
if (v___x_4836_ == 0)
{
v___y_4826_ = v_pos_4833_;
v_snd_4827_ = v_snd_4835_;
goto v___jp_4825_;
}
else
{
uint32_t v___x_4839_; uint32_t v_c_4840_; uint8_t v___x_4841_; 
v___x_4839_ = 122;
v_c_4840_ = lean_string_utf8_get_fast(v_fst_4834_, v_snd_4835_);
v___x_4841_ = lean_uint32_dec_eq(v_c_4840_, v___x_4839_);
if (v___x_4841_ == 0)
{
lean_object* v___x_4842_; 
v___x_4842_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3);
v_snd_4821_ = v_snd_4835_;
v_pos_4822_ = v_pos_4833_;
v_err_4823_ = v___x_4842_;
goto v___jp_4820_;
}
else
{
lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4858_; 
lean_inc(v_fst_4834_);
v_isSharedCheck_4858_ = !lean_is_exclusive(v_pos_4833_);
if (v_isSharedCheck_4858_ == 0)
{
lean_object* v_unused_4859_; lean_object* v_unused_4860_; 
v_unused_4859_ = lean_ctor_get(v_pos_4833_, 1);
lean_dec(v_unused_4859_);
v_unused_4860_ = lean_ctor_get(v_pos_4833_, 0);
lean_dec(v_unused_4860_);
v___x_4844_ = v_pos_4833_;
v_isShared_4845_ = v_isSharedCheck_4858_;
goto v_resetjp_4843_;
}
else
{
lean_dec(v_pos_4833_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4858_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4846_; lean_object* v_it_x27_4848_; 
v___x_4846_ = lean_string_utf8_next_fast(v_fst_4834_, v_snd_4835_);
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 1, v___x_4846_);
v_it_x27_4848_ = v___x_4844_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v_fst_4834_);
lean_ctor_set(v_reuseFailAlloc_4857_, 1, v___x_4846_);
v_it_x27_4848_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4849_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0);
v___x_4850_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(v___x_4849_, v_it_x27_4848_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_pos_4851_; lean_object* v_res_4852_; lean_object* v___x_4853_; 
v_pos_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_pos_4851_);
v_res_4852_ = lean_ctor_get(v___x_4850_, 1);
lean_inc(v_res_4852_);
lean_dec_ref_known(v___x_4850_, 2);
v___x_4853_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4829_, v_res_4852_, v_pos_4851_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_dec(v_snd_4835_);
return v___x_4853_;
}
else
{
lean_object* v_pos_4854_; 
v_pos_4854_ = lean_ctor_get(v___x_4853_, 0);
lean_inc(v_pos_4854_);
v_snd_4790_ = v_snd_4835_;
v___y_4791_ = v___x_4853_;
v_pos_4792_ = v_pos_4854_;
goto v___jp_4789_;
}
}
else
{
lean_object* v_pos_4855_; lean_object* v_err_4856_; 
v_pos_4855_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_pos_4855_);
v_err_4856_ = lean_ctor_get(v___x_4850_, 1);
lean_inc(v_err_4856_);
lean_dec_ref_known(v___x_4850_, 2);
v_snd_4821_ = v_snd_4835_;
v_pos_4822_ = v_pos_4855_;
v_err_4823_ = v_err_4856_;
goto v___jp_4820_;
}
}
}
}
}
}
else
{
v___y_4826_ = v_pos_4833_;
v_snd_4827_ = v_snd_4835_;
goto v___jp_4825_;
}
}
}
v___jp_4861_:
{
lean_object* v___x_4865_; 
lean_inc_ref(v_pos_4863_);
v___x_4865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4865_, 0, v_pos_4863_);
lean_ctor_set(v___x_4865_, 1, v_err_4864_);
v_snd_4831_ = v_snd_4862_;
v___y_4832_ = v___x_4865_;
v_pos_4833_ = v_pos_4863_;
goto v___jp_4830_;
}
v___jp_4866_:
{
lean_object* v___x_4869_; 
v___x_4869_ = lean_box(0);
v_snd_4862_ = v_snd_4868_;
v_pos_4863_ = v___y_4867_;
v_err_4864_ = v___x_4869_;
goto v___jp_4861_;
}
v___jp_4870_:
{
lean_object* v_fst_4874_; lean_object* v_snd_4875_; uint8_t v___x_4876_; 
v_fst_4874_ = lean_ctor_get(v_pos_4873_, 0);
v_snd_4875_ = lean_ctor_get(v_pos_4873_, 1);
lean_inc(v_snd_4875_);
v___x_4876_ = lean_nat_dec_eq(v_snd_4871_, v_snd_4875_);
lean_dec(v_snd_4871_);
if (v___x_4876_ == 0)
{
lean_dec(v_snd_4875_);
lean_dec_ref(v_pos_4873_);
return v___y_4872_;
}
else
{
lean_object* v___x_4877_; uint8_t v___x_4878_; 
lean_dec_ref(v___y_4872_);
v___x_4877_ = lean_string_utf8_byte_size(v_fst_4874_);
v___x_4878_ = lean_nat_dec_eq(v_snd_4875_, v___x_4877_);
if (v___x_4878_ == 0)
{
if (v___x_4876_ == 0)
{
v___y_4867_ = v_pos_4873_;
v_snd_4868_ = v_snd_4875_;
goto v___jp_4866_;
}
else
{
uint32_t v___x_4879_; uint32_t v_c_4880_; uint8_t v___x_4881_; 
v___x_4879_ = 86;
v_c_4880_ = lean_string_utf8_get_fast(v_fst_4874_, v_snd_4875_);
v___x_4881_ = lean_uint32_dec_eq(v_c_4880_, v___x_4879_);
if (v___x_4881_ == 0)
{
lean_object* v___x_4882_; 
v___x_4882_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3);
v_snd_4862_ = v_snd_4875_;
v_pos_4863_ = v_pos_4873_;
v_err_4864_ = v___x_4882_;
goto v___jp_4861_;
}
else
{
lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4898_; 
lean_inc(v_fst_4874_);
v_isSharedCheck_4898_ = !lean_is_exclusive(v_pos_4873_);
if (v_isSharedCheck_4898_ == 0)
{
lean_object* v_unused_4899_; lean_object* v_unused_4900_; 
v_unused_4899_ = lean_ctor_get(v_pos_4873_, 1);
lean_dec(v_unused_4899_);
v_unused_4900_ = lean_ctor_get(v_pos_4873_, 0);
lean_dec(v_unused_4900_);
v___x_4884_ = v_pos_4873_;
v_isShared_4885_ = v_isSharedCheck_4898_;
goto v_resetjp_4883_;
}
else
{
lean_dec(v_pos_4873_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4898_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4886_; lean_object* v_it_x27_4888_; 
v___x_4886_ = lean_string_utf8_next_fast(v_fst_4874_, v_snd_4875_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 1, v___x_4886_);
v_it_x27_4888_ = v___x_4884_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_fst_4874_);
lean_ctor_set(v_reuseFailAlloc_4897_, 1, v___x_4886_);
v_it_x27_4888_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4889_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0);
v___x_4890_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(v___x_4889_, v_it_x27_4888_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_pos_4891_; lean_object* v_res_4892_; lean_object* v___x_4893_; 
v_pos_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_pos_4891_);
v_res_4892_ = lean_ctor_get(v___x_4890_, 1);
lean_inc(v_res_4892_);
lean_dec_ref_known(v___x_4890_, 2);
v___x_4893_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(v_res_4892_, v_pos_4891_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_dec(v_snd_4875_);
return v___x_4893_;
}
else
{
lean_object* v_pos_4894_; 
v_pos_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_pos_4894_);
v_snd_4831_ = v_snd_4875_;
v___y_4832_ = v___x_4893_;
v_pos_4833_ = v_pos_4894_;
goto v___jp_4830_;
}
}
else
{
lean_object* v_pos_4895_; lean_object* v_err_4896_; 
v_pos_4895_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_pos_4895_);
v_err_4896_ = lean_ctor_get(v___x_4890_, 1);
lean_inc(v_err_4896_);
lean_dec_ref_known(v___x_4890_, 2);
v_snd_4862_ = v_snd_4875_;
v_pos_4863_ = v_pos_4895_;
v_err_4864_ = v_err_4896_;
goto v___jp_4861_;
}
}
}
}
}
}
else
{
v___y_4867_ = v_pos_4873_;
v_snd_4868_ = v_snd_4875_;
goto v___jp_4866_;
}
}
}
v___jp_4901_:
{
lean_object* v___x_4905_; 
lean_inc_ref(v_pos_4903_);
v___x_4905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4905_, 0, v_pos_4903_);
lean_ctor_set(v___x_4905_, 1, v_err_4904_);
v_snd_4871_ = v_snd_4902_;
v___y_4872_ = v___x_4905_;
v_pos_4873_ = v_pos_4903_;
goto v___jp_4870_;
}
v___jp_4906_:
{
lean_object* v___x_4909_; 
v___x_4909_ = lean_box(0);
v_snd_4902_ = v_snd_4908_;
v_pos_4903_ = v___y_4907_;
v_err_4904_ = v___x_4909_;
goto v___jp_4901_;
}
v___jp_4911_:
{
lean_object* v_fst_4915_; lean_object* v_snd_4916_; uint8_t v___x_4917_; 
v_fst_4915_ = lean_ctor_get(v_pos_4914_, 0);
v_snd_4916_ = lean_ctor_get(v_pos_4914_, 1);
lean_inc(v_snd_4916_);
v___x_4917_ = lean_nat_dec_eq(v_snd_4912_, v_snd_4916_);
lean_dec(v_snd_4912_);
if (v___x_4917_ == 0)
{
lean_dec(v_snd_4916_);
lean_dec_ref(v_pos_4914_);
return v___y_4913_;
}
else
{
lean_object* v___x_4918_; uint8_t v___x_4919_; 
lean_dec_ref(v___y_4913_);
v___x_4918_ = lean_string_utf8_byte_size(v_fst_4915_);
v___x_4919_ = lean_nat_dec_eq(v_snd_4916_, v___x_4918_);
if (v___x_4919_ == 0)
{
if (v___x_4917_ == 0)
{
v___y_4907_ = v_pos_4914_;
v_snd_4908_ = v_snd_4916_;
goto v___jp_4906_;
}
else
{
uint32_t v___x_4920_; uint32_t v_c_4921_; uint8_t v___x_4922_; 
v___x_4920_ = 78;
v_c_4921_ = lean_string_utf8_get_fast(v_fst_4915_, v_snd_4916_);
v___x_4922_ = lean_uint32_dec_eq(v_c_4921_, v___x_4920_);
if (v___x_4922_ == 0)
{
lean_object* v___x_4923_; 
v___x_4923_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3);
v_snd_4902_ = v_snd_4916_;
v_pos_4903_ = v_pos_4914_;
v_err_4904_ = v___x_4923_;
goto v___jp_4901_;
}
else
{
lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4938_; 
lean_inc(v_fst_4915_);
v_isSharedCheck_4938_ = !lean_is_exclusive(v_pos_4914_);
if (v_isSharedCheck_4938_ == 0)
{
lean_object* v_unused_4939_; lean_object* v_unused_4940_; 
v_unused_4939_ = lean_ctor_get(v_pos_4914_, 1);
lean_dec(v_unused_4939_);
v_unused_4940_ = lean_ctor_get(v_pos_4914_, 0);
lean_dec(v_unused_4940_);
v___x_4925_ = v_pos_4914_;
v_isShared_4926_ = v_isSharedCheck_4938_;
goto v_resetjp_4924_;
}
else
{
lean_dec(v_pos_4914_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4938_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4927_; lean_object* v_it_x27_4929_; 
v___x_4927_ = lean_string_utf8_next_fast(v_fst_4915_, v_snd_4916_);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 1, v___x_4927_);
v_it_x27_4929_ = v___x_4925_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_fst_4915_);
lean_ctor_set(v_reuseFailAlloc_4937_, 1, v___x_4927_);
v_it_x27_4929_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; 
v___x_4930_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0);
v___x_4931_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(v___x_4930_, v_it_x27_4929_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v_pos_4932_; lean_object* v_res_4933_; lean_object* v___x_4934_; 
lean_dec(v_snd_4916_);
v_pos_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc(v_pos_4932_);
v_res_4933_ = lean_ctor_get(v___x_4931_, 1);
lean_inc(v_res_4933_);
lean_dec_ref_known(v___x_4931_, 2);
v___x_4934_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4910_, v_res_4933_, v_pos_4932_);
lean_dec(v_res_4933_);
return v___x_4934_;
}
else
{
lean_object* v_pos_4935_; lean_object* v_err_4936_; 
v_pos_4935_ = lean_ctor_get(v___x_4931_, 0);
lean_inc(v_pos_4935_);
v_err_4936_ = lean_ctor_get(v___x_4931_, 1);
lean_inc(v_err_4936_);
lean_dec_ref_known(v___x_4931_, 2);
v_snd_4902_ = v_snd_4916_;
v_pos_4903_ = v_pos_4935_;
v_err_4904_ = v_err_4936_;
goto v___jp_4901_;
}
}
}
}
}
}
else
{
v___y_4907_ = v_pos_4914_;
v_snd_4908_ = v_snd_4916_;
goto v___jp_4906_;
}
}
}
v___jp_4941_:
{
lean_object* v___x_4945_; 
lean_inc_ref(v_pos_4943_);
v___x_4945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4945_, 0, v_pos_4943_);
lean_ctor_set(v___x_4945_, 1, v_err_4944_);
v_snd_4912_ = v_snd_4942_;
v___y_4913_ = v___x_4945_;
v_pos_4914_ = v_pos_4943_;
goto v___jp_4911_;
}
v___jp_4946_:
{
lean_object* v___x_4949_; 
v___x_4949_ = lean_box(0);
v_snd_4942_ = v_snd_4948_;
v_pos_4943_ = v___y_4947_;
v_err_4944_ = v___x_4949_;
goto v___jp_4941_;
}
v___jp_4951_:
{
lean_object* v_fst_4955_; lean_object* v_snd_4956_; uint8_t v___x_4957_; 
v_fst_4955_ = lean_ctor_get(v_pos_4954_, 0);
v_snd_4956_ = lean_ctor_get(v_pos_4954_, 1);
lean_inc(v_snd_4956_);
v___x_4957_ = lean_nat_dec_eq(v_snd_4952_, v_snd_4956_);
lean_dec(v_snd_4952_);
if (v___x_4957_ == 0)
{
lean_dec(v_snd_4956_);
lean_dec_ref(v_pos_4954_);
return v___y_4953_;
}
else
{
lean_object* v___x_4958_; uint8_t v___x_4959_; 
lean_dec_ref(v___y_4953_);
v___x_4958_ = lean_string_utf8_byte_size(v_fst_4955_);
v___x_4959_ = lean_nat_dec_eq(v_snd_4956_, v___x_4958_);
if (v___x_4959_ == 0)
{
if (v___x_4957_ == 0)
{
v___y_4947_ = v_pos_4954_;
v_snd_4948_ = v_snd_4956_;
goto v___jp_4946_;
}
else
{
uint32_t v___x_4960_; uint32_t v_c_4961_; uint8_t v___x_4962_; 
v___x_4960_ = 110;
v_c_4961_ = lean_string_utf8_get_fast(v_fst_4955_, v_snd_4956_);
v___x_4962_ = lean_uint32_dec_eq(v_c_4961_, v___x_4960_);
if (v___x_4962_ == 0)
{
lean_object* v___x_4963_; 
v___x_4963_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3);
v_snd_4942_ = v_snd_4956_;
v_pos_4943_ = v_pos_4954_;
v_err_4944_ = v___x_4963_;
goto v___jp_4941_;
}
else
{
lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4978_; 
lean_inc(v_fst_4955_);
v_isSharedCheck_4978_ = !lean_is_exclusive(v_pos_4954_);
if (v_isSharedCheck_4978_ == 0)
{
lean_object* v_unused_4979_; lean_object* v_unused_4980_; 
v_unused_4979_ = lean_ctor_get(v_pos_4954_, 1);
lean_dec(v_unused_4979_);
v_unused_4980_ = lean_ctor_get(v_pos_4954_, 0);
lean_dec(v_unused_4980_);
v___x_4965_ = v_pos_4954_;
v_isShared_4966_ = v_isSharedCheck_4978_;
goto v_resetjp_4964_;
}
else
{
lean_dec(v_pos_4954_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_4978_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v___x_4967_; lean_object* v_it_x27_4969_; 
v___x_4967_ = lean_string_utf8_next_fast(v_fst_4955_, v_snd_4956_);
if (v_isShared_4966_ == 0)
{
lean_ctor_set(v___x_4965_, 1, v___x_4967_);
v_it_x27_4969_ = v___x_4965_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_fst_4955_);
lean_ctor_set(v_reuseFailAlloc_4977_, 1, v___x_4967_);
v_it_x27_4969_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4970_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0);
v___x_4971_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(v___x_4970_, v_it_x27_4969_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_pos_4972_; lean_object* v_res_4973_; lean_object* v___x_4974_; 
lean_dec(v_snd_4956_);
v_pos_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc(v_pos_4972_);
v_res_4973_ = lean_ctor_get(v___x_4971_, 1);
lean_inc(v_res_4973_);
lean_dec_ref_known(v___x_4971_, 2);
v___x_4974_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4950_, v_res_4973_, v_pos_4972_);
lean_dec(v_res_4973_);
return v___x_4974_;
}
else
{
lean_object* v_pos_4975_; lean_object* v_err_4976_; 
v_pos_4975_ = lean_ctor_get(v___x_4971_, 0);
lean_inc(v_pos_4975_);
v_err_4976_ = lean_ctor_get(v___x_4971_, 1);
lean_inc(v_err_4976_);
lean_dec_ref_known(v___x_4971_, 2);
v_snd_4942_ = v_snd_4956_;
v_pos_4943_ = v_pos_4975_;
v_err_4944_ = v_err_4976_;
goto v___jp_4941_;
}
}
}
}
}
}
else
{
v___y_4947_ = v_pos_4954_;
v_snd_4948_ = v_snd_4956_;
goto v___jp_4946_;
}
}
}
v___jp_4981_:
{
lean_object* v___x_4985_; 
lean_inc_ref(v_pos_4983_);
v___x_4985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4985_, 0, v_pos_4983_);
lean_ctor_set(v___x_4985_, 1, v_err_4984_);
v_snd_4952_ = v_snd_4982_;
v___y_4953_ = v___x_4985_;
v_pos_4954_ = v_pos_4983_;
goto v___jp_4951_;
}
v___jp_4986_:
{
lean_object* v___x_4989_; 
v___x_4989_ = lean_box(0);
v_snd_4982_ = v_snd_4988_;
v_pos_4983_ = v___y_4987_;
v_err_4984_ = v___x_4989_;
goto v___jp_4981_;
}
v___jp_4991_:
{
lean_object* v_fst_4995_; lean_object* v_snd_4996_; uint8_t v___x_4997_; 
v_fst_4995_ = lean_ctor_get(v_pos_4994_, 0);
v_snd_4996_ = lean_ctor_get(v_pos_4994_, 1);
lean_inc(v_snd_4996_);
v___x_4997_ = lean_nat_dec_eq(v_snd_4992_, v_snd_4996_);
lean_dec(v_snd_4992_);
if (v___x_4997_ == 0)
{
lean_dec(v_snd_4996_);
lean_dec_ref(v_pos_4994_);
return v___y_4993_;
}
else
{
lean_object* v___x_4998_; uint8_t v___x_4999_; 
lean_dec_ref(v___y_4993_);
v___x_4998_ = lean_string_utf8_byte_size(v_fst_4995_);
v___x_4999_ = lean_nat_dec_eq(v_snd_4996_, v___x_4998_);
if (v___x_4999_ == 0)
{
if (v___x_4997_ == 0)
{
v___y_4987_ = v_pos_4994_;
v_snd_4988_ = v_snd_4996_;
goto v___jp_4986_;
}
else
{
uint32_t v___x_5000_; uint32_t v_c_5001_; uint8_t v___x_5002_; 
v___x_5000_ = 65;
v_c_5001_ = lean_string_utf8_get_fast(v_fst_4995_, v_snd_4996_);
v___x_5002_ = lean_uint32_dec_eq(v_c_5001_, v___x_5000_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; 
v___x_5003_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3);
v_snd_4982_ = v_snd_4996_;
v_pos_4983_ = v_pos_4994_;
v_err_4984_ = v___x_5003_;
goto v___jp_4981_;
}
else
{
lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5018_; 
lean_inc(v_fst_4995_);
v_isSharedCheck_5018_ = !lean_is_exclusive(v_pos_4994_);
if (v_isSharedCheck_5018_ == 0)
{
lean_object* v_unused_5019_; lean_object* v_unused_5020_; 
v_unused_5019_ = lean_ctor_get(v_pos_4994_, 1);
lean_dec(v_unused_5019_);
v_unused_5020_ = lean_ctor_get(v_pos_4994_, 0);
lean_dec(v_unused_5020_);
v___x_5005_ = v_pos_4994_;
v_isShared_5006_ = v_isSharedCheck_5018_;
goto v_resetjp_5004_;
}
else
{
lean_dec(v_pos_4994_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5018_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5007_; lean_object* v_it_x27_5009_; 
v___x_5007_ = lean_string_utf8_next_fast(v_fst_4995_, v_snd_4996_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 1, v___x_5007_);
v_it_x27_5009_ = v___x_5005_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_fst_4995_);
lean_ctor_set(v_reuseFailAlloc_5017_, 1, v___x_5007_);
v_it_x27_5009_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5010_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0);
v___x_5011_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(v___x_5010_, v_it_x27_5009_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_pos_5012_; lean_object* v_res_5013_; lean_object* v___x_5014_; 
lean_dec(v_snd_4996_);
v_pos_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_pos_5012_);
v_res_5013_ = lean_ctor_get(v___x_5011_, 1);
lean_inc(v_res_5013_);
lean_dec_ref_known(v___x_5011_, 2);
v___x_5014_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4990_, v_res_5013_, v_pos_5012_);
lean_dec(v_res_5013_);
return v___x_5014_;
}
else
{
lean_object* v_pos_5015_; lean_object* v_err_5016_; 
v_pos_5015_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_pos_5015_);
v_err_5016_ = lean_ctor_get(v___x_5011_, 1);
lean_inc(v_err_5016_);
lean_dec_ref_known(v___x_5011_, 2);
v_snd_4982_ = v_snd_4996_;
v_pos_4983_ = v_pos_5015_;
v_err_4984_ = v_err_5016_;
goto v___jp_4981_;
}
}
}
}
}
}
else
{
v___y_4987_ = v_pos_4994_;
v_snd_4988_ = v_snd_4996_;
goto v___jp_4986_;
}
}
}
v___jp_5021_:
{
lean_object* v___x_5025_; 
lean_inc_ref(v_pos_5023_);
v___x_5025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5025_, 0, v_pos_5023_);
lean_ctor_set(v___x_5025_, 1, v_err_5024_);
v_snd_4992_ = v_snd_5022_;
v___y_4993_ = v___x_5025_;
v_pos_4994_ = v_pos_5023_;
goto v___jp_4991_;
}
v___jp_5026_:
{
lean_object* v___x_5029_; 
v___x_5029_ = lean_box(0);
v_snd_5022_ = v_snd_5028_;
v_pos_5023_ = v___y_5027_;
v_err_5024_ = v___x_5029_;
goto v___jp_5021_;
}
v___jp_5031_:
{
lean_object* v_fst_5035_; lean_object* v_snd_5036_; uint8_t v___x_5037_; 
v_fst_5035_ = lean_ctor_get(v_pos_5034_, 0);
v_snd_5036_ = lean_ctor_get(v_pos_5034_, 1);
lean_inc(v_snd_5036_);
v___x_5037_ = lean_nat_dec_eq(v_snd_5032_, v_snd_5036_);
lean_dec(v_snd_5032_);
if (v___x_5037_ == 0)
{
lean_dec(v_snd_5036_);
lean_dec_ref(v_pos_5034_);
return v___y_5033_;
}
else
{
lean_object* v___x_5038_; uint8_t v___x_5039_; 
lean_dec_ref(v___y_5033_);
v___x_5038_ = lean_string_utf8_byte_size(v_fst_5035_);
v___x_5039_ = lean_nat_dec_eq(v_snd_5036_, v___x_5038_);
if (v___x_5039_ == 0)
{
if (v___x_5037_ == 0)
{
v___y_5027_ = v_pos_5034_;
v_snd_5028_ = v_snd_5036_;
goto v___jp_5026_;
}
else
{
uint32_t v___x_5040_; uint32_t v_c_5041_; uint8_t v___x_5042_; 
v___x_5040_ = 83;
v_c_5041_ = lean_string_utf8_get_fast(v_fst_5035_, v_snd_5036_);
v___x_5042_ = lean_uint32_dec_eq(v_c_5041_, v___x_5040_);
if (v___x_5042_ == 0)
{
lean_object* v___x_5043_; 
v___x_5043_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3);
v_snd_5022_ = v_snd_5036_;
v_pos_5023_ = v_pos_5034_;
v_err_5024_ = v___x_5043_;
goto v___jp_5021_;
}
else
{
lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5059_; 
lean_inc(v_fst_5035_);
v_isSharedCheck_5059_ = !lean_is_exclusive(v_pos_5034_);
if (v_isSharedCheck_5059_ == 0)
{
lean_object* v_unused_5060_; lean_object* v_unused_5061_; 
v_unused_5060_ = lean_ctor_get(v_pos_5034_, 1);
lean_dec(v_unused_5060_);
v_unused_5061_ = lean_ctor_get(v_pos_5034_, 0);
lean_dec(v_unused_5061_);
v___x_5045_ = v_pos_5034_;
v_isShared_5046_ = v_isSharedCheck_5059_;
goto v_resetjp_5044_;
}
else
{
lean_dec(v_pos_5034_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5059_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5047_; lean_object* v_it_x27_5049_; 
v___x_5047_ = lean_string_utf8_next_fast(v_fst_5035_, v_snd_5036_);
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 1, v___x_5047_);
v_it_x27_5049_ = v___x_5045_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_fst_5035_);
lean_ctor_set(v_reuseFailAlloc_5058_, 1, v___x_5047_);
v_it_x27_5049_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5050_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0);
v___x_5051_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(v___x_5050_, v_it_x27_5049_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_pos_5052_; lean_object* v_res_5053_; lean_object* v___x_5054_; 
v_pos_5052_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_pos_5052_);
v_res_5053_ = lean_ctor_get(v___x_5051_, 1);
lean_inc(v_res_5053_);
lean_dec_ref_known(v___x_5051_, 2);
v___x_5054_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(v___f_5030_, v_res_5053_, v_pos_5052_);
if (lean_obj_tag(v___x_5054_) == 0)
{
lean_dec(v_snd_5036_);
return v___x_5054_;
}
else
{
lean_object* v_pos_5055_; 
v_pos_5055_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_pos_5055_);
v_snd_4992_ = v_snd_5036_;
v___y_4993_ = v___x_5054_;
v_pos_4994_ = v_pos_5055_;
goto v___jp_4991_;
}
}
else
{
lean_object* v_pos_5056_; lean_object* v_err_5057_; 
v_pos_5056_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_pos_5056_);
v_err_5057_ = lean_ctor_get(v___x_5051_, 1);
lean_inc(v_err_5057_);
lean_dec_ref_known(v___x_5051_, 2);
v_snd_5022_ = v_snd_5036_;
v_pos_5023_ = v_pos_5056_;
v_err_5024_ = v_err_5057_;
goto v___jp_5021_;
}
}
}
}
}
}
else
{
v___y_5027_ = v_pos_5034_;
v_snd_5028_ = v_snd_5036_;
goto v___jp_5026_;
}
}
}
v___jp_5062_:
{
lean_object* v___x_5066_; 
lean_inc_ref(v_pos_5064_);
v___x_5066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5066_, 0, v_pos_5064_);
lean_ctor_set(v___x_5066_, 1, v_err_5065_);
v_snd_5032_ = v_snd_5063_;
v___y_5033_ = v___x_5066_;
v_pos_5034_ = v_pos_5064_;
goto v___jp_5031_;
}
v___jp_5067_:
{
lean_object* v___x_5070_; 
v___x_5070_ = lean_box(0);
v_snd_5063_ = v_snd_5069_;
v_pos_5064_ = v___y_5068_;
v_err_5065_ = v___x_5070_;
goto v___jp_5062_;
}
v___jp_5072_:
{
lean_object* v_fst_5077_; lean_object* v_snd_5078_; uint8_t v___x_5079_; 
v_fst_5077_ = lean_ctor_get(v_pos_5076_, 0);
v_snd_5078_ = lean_ctor_get(v_pos_5076_, 1);
lean_inc(v_snd_5078_);
v___x_5079_ = lean_nat_dec_eq(v_snd_5073_, v_snd_5078_);
lean_dec(v_snd_5073_);
if (v___x_5079_ == 0)
{
lean_dec(v_snd_5078_);
lean_dec_ref(v_pos_5076_);
lean_dec_ref(v___y_5074_);
return v___y_5075_;
}
else
{
lean_object* v___x_5080_; uint8_t v___x_5081_; 
lean_dec_ref(v___y_5075_);
v___x_5080_ = lean_string_utf8_byte_size(v_fst_5077_);
v___x_5081_ = lean_nat_dec_eq(v_snd_5078_, v___x_5080_);
if (v___x_5081_ == 0)
{
if (v___x_5079_ == 0)
{
lean_dec_ref(v___y_5074_);
v___y_5068_ = v_pos_5076_;
v_snd_5069_ = v_snd_5078_;
goto v___jp_5067_;
}
else
{
uint32_t v___x_5082_; uint32_t v_c_5083_; uint8_t v___x_5084_; 
v___x_5082_ = 115;
v_c_5083_ = lean_string_utf8_get_fast(v_fst_5077_, v_snd_5078_);
v___x_5084_ = lean_uint32_dec_eq(v_c_5083_, v___x_5082_);
if (v___x_5084_ == 0)
{
lean_object* v___x_5085_; 
lean_dec_ref(v___y_5074_);
v___x_5085_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3);
v_snd_5063_ = v_snd_5078_;
v_pos_5064_ = v_pos_5076_;
v_err_5065_ = v___x_5085_;
goto v___jp_5062_;
}
else
{
lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5101_; 
lean_inc(v_fst_5077_);
v_isSharedCheck_5101_ = !lean_is_exclusive(v_pos_5076_);
if (v_isSharedCheck_5101_ == 0)
{
lean_object* v_unused_5102_; lean_object* v_unused_5103_; 
v_unused_5102_ = lean_ctor_get(v_pos_5076_, 1);
lean_dec(v_unused_5102_);
v_unused_5103_ = lean_ctor_get(v_pos_5076_, 0);
lean_dec(v_unused_5103_);
v___x_5087_ = v_pos_5076_;
v_isShared_5088_ = v_isSharedCheck_5101_;
goto v_resetjp_5086_;
}
else
{
lean_dec(v_pos_5076_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5101_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5089_; lean_object* v_it_x27_5091_; 
v___x_5089_ = lean_string_utf8_next_fast(v_fst_5077_, v_snd_5078_);
if (v_isShared_5088_ == 0)
{
lean_ctor_set(v___x_5087_, 1, v___x_5089_);
v_it_x27_5091_ = v___x_5087_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_fst_5077_);
lean_ctor_set(v_reuseFailAlloc_5100_, 1, v___x_5089_);
v_it_x27_5091_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5092_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0);
v___x_5093_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(v___x_5092_, v_it_x27_5091_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v_pos_5094_; lean_object* v_res_5095_; lean_object* v___x_5096_; 
v_pos_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc(v_pos_5094_);
v_res_5095_ = lean_ctor_get(v___x_5093_, 1);
lean_inc(v_res_5095_);
lean_dec_ref_known(v___x_5093_, 2);
v___x_5096_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5071_, v___y_5074_, v_res_5095_, v_pos_5094_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_dec(v_snd_5078_);
return v___x_5096_;
}
else
{
lean_object* v_pos_5097_; 
v_pos_5097_ = lean_ctor_get(v___x_5096_, 0);
lean_inc(v_pos_5097_);
v_snd_5032_ = v_snd_5078_;
v___y_5033_ = v___x_5096_;
v_pos_5034_ = v_pos_5097_;
goto v___jp_5031_;
}
}
else
{
lean_object* v_pos_5098_; lean_object* v_err_5099_; 
lean_dec_ref(v___y_5074_);
v_pos_5098_ = lean_ctor_get(v___x_5093_, 0);
lean_inc(v_pos_5098_);
v_err_5099_ = lean_ctor_get(v___x_5093_, 1);
lean_inc(v_err_5099_);
lean_dec_ref_known(v___x_5093_, 2);
v_snd_5063_ = v_snd_5078_;
v_pos_5064_ = v_pos_5098_;
v_err_5065_ = v_err_5099_;
goto v___jp_5062_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_5074_);
v___y_5068_ = v_pos_5076_;
v_snd_5069_ = v_snd_5078_;
goto v___jp_5067_;
}
}
}
v___jp_5104_:
{
lean_object* v___x_5109_; 
lean_inc_ref(v_pos_5107_);
v___x_5109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5109_, 0, v_pos_5107_);
lean_ctor_set(v___x_5109_, 1, v_err_5108_);
v_snd_5073_ = v_snd_5105_;
v___y_5074_ = v___y_5106_;
v___y_5075_ = v___x_5109_;
v_pos_5076_ = v_pos_5107_;
goto v___jp_5072_;
}
v___jp_5110_:
{
lean_object* v___x_5114_; 
v___x_5114_ = lean_box(0);
v_snd_5105_ = v_snd_5112_;
v___y_5106_ = v___y_5113_;
v_pos_5107_ = v___y_5111_;
v_err_5108_ = v___x_5114_;
goto v___jp_5104_;
}
v___jp_5116_:
{
lean_object* v_fst_5121_; lean_object* v_snd_5122_; uint8_t v___x_5123_; 
v_fst_5121_ = lean_ctor_get(v_pos_5120_, 0);
v_snd_5122_ = lean_ctor_get(v_pos_5120_, 1);
lean_inc(v_snd_5122_);
v___x_5123_ = lean_nat_dec_eq(v_snd_5118_, v_snd_5122_);
lean_dec(v_snd_5118_);
if (v___x_5123_ == 0)
{
lean_dec(v_snd_5122_);
lean_dec_ref(v_pos_5120_);
lean_dec_ref(v___y_5117_);
return v___y_5119_;
}
else
{
lean_object* v___x_5124_; uint8_t v___x_5125_; 
lean_dec_ref(v___y_5119_);
v___x_5124_ = lean_string_utf8_byte_size(v_fst_5121_);
v___x_5125_ = lean_nat_dec_eq(v_snd_5122_, v___x_5124_);
if (v___x_5125_ == 0)
{
if (v___x_5123_ == 0)
{
v___y_5111_ = v_pos_5120_;
v_snd_5112_ = v_snd_5122_;
v___y_5113_ = v___y_5117_;
goto v___jp_5110_;
}
else
{
uint32_t v___x_5126_; uint32_t v_c_5127_; uint8_t v___x_5128_; 
v___x_5126_ = 109;
v_c_5127_ = lean_string_utf8_get_fast(v_fst_5121_, v_snd_5122_);
v___x_5128_ = lean_uint32_dec_eq(v_c_5127_, v___x_5126_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; 
v___x_5129_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3);
v_snd_5105_ = v_snd_5122_;
v___y_5106_ = v___y_5117_;
v_pos_5107_ = v_pos_5120_;
v_err_5108_ = v___x_5129_;
goto v___jp_5104_;
}
else
{
lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5145_; 
lean_inc(v_fst_5121_);
v_isSharedCheck_5145_ = !lean_is_exclusive(v_pos_5120_);
if (v_isSharedCheck_5145_ == 0)
{
lean_object* v_unused_5146_; lean_object* v_unused_5147_; 
v_unused_5146_ = lean_ctor_get(v_pos_5120_, 1);
lean_dec(v_unused_5146_);
v_unused_5147_ = lean_ctor_get(v_pos_5120_, 0);
lean_dec(v_unused_5147_);
v___x_5131_ = v_pos_5120_;
v_isShared_5132_ = v_isSharedCheck_5145_;
goto v_resetjp_5130_;
}
else
{
lean_dec(v_pos_5120_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5145_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5133_; lean_object* v_it_x27_5135_; 
v___x_5133_ = lean_string_utf8_next_fast(v_fst_5121_, v_snd_5122_);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 1, v___x_5133_);
v_it_x27_5135_ = v___x_5131_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_fst_5121_);
lean_ctor_set(v_reuseFailAlloc_5144_, 1, v___x_5133_);
v_it_x27_5135_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; 
v___x_5136_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0);
v___x_5137_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(v___x_5136_, v_it_x27_5135_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v_pos_5138_; lean_object* v_res_5139_; lean_object* v___x_5140_; 
v_pos_5138_ = lean_ctor_get(v___x_5137_, 0);
lean_inc(v_pos_5138_);
v_res_5139_ = lean_ctor_get(v___x_5137_, 1);
lean_inc(v_res_5139_);
lean_dec_ref_known(v___x_5137_, 2);
lean_inc_ref(v___y_5117_);
v___x_5140_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5115_, v___y_5117_, v_res_5139_, v_pos_5138_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_dec(v_snd_5122_);
lean_dec_ref(v___y_5117_);
return v___x_5140_;
}
else
{
lean_object* v_pos_5141_; 
v_pos_5141_ = lean_ctor_get(v___x_5140_, 0);
lean_inc(v_pos_5141_);
v_snd_5073_ = v_snd_5122_;
v___y_5074_ = v___y_5117_;
v___y_5075_ = v___x_5140_;
v_pos_5076_ = v_pos_5141_;
goto v___jp_5072_;
}
}
else
{
lean_object* v_pos_5142_; lean_object* v_err_5143_; 
v_pos_5142_ = lean_ctor_get(v___x_5137_, 0);
lean_inc(v_pos_5142_);
v_err_5143_ = lean_ctor_get(v___x_5137_, 1);
lean_inc(v_err_5143_);
lean_dec_ref_known(v___x_5137_, 2);
v_snd_5105_ = v_snd_5122_;
v___y_5106_ = v___y_5117_;
v_pos_5107_ = v_pos_5142_;
v_err_5108_ = v_err_5143_;
goto v___jp_5104_;
}
}
}
}
}
}
else
{
v___y_5111_ = v_pos_5120_;
v_snd_5112_ = v_snd_5122_;
v___y_5113_ = v___y_5117_;
goto v___jp_5110_;
}
}
}
v___jp_5148_:
{
lean_object* v___x_5153_; 
lean_inc_ref(v_pos_5151_);
v___x_5153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5153_, 0, v_pos_5151_);
lean_ctor_set(v___x_5153_, 1, v_err_5152_);
v___y_5117_ = v___y_5149_;
v_snd_5118_ = v_snd_5150_;
v___y_5119_ = v___x_5153_;
v_pos_5120_ = v_pos_5151_;
goto v___jp_5116_;
}
v___jp_5154_:
{
lean_object* v___x_5158_; 
v___x_5158_ = lean_box(0);
v___y_5149_ = v___y_5155_;
v_snd_5150_ = v_snd_5157_;
v_pos_5151_ = v___y_5156_;
v_err_5152_ = v___x_5158_;
goto v___jp_5148_;
}
v___jp_5160_:
{
lean_object* v_fst_5165_; lean_object* v_snd_5166_; uint8_t v___x_5167_; 
v_fst_5165_ = lean_ctor_get(v_pos_5164_, 0);
v_snd_5166_ = lean_ctor_get(v_pos_5164_, 1);
lean_inc(v_snd_5166_);
v___x_5167_ = lean_nat_dec_eq(v_snd_5161_, v_snd_5166_);
lean_dec(v_snd_5161_);
if (v___x_5167_ == 0)
{
lean_dec(v_snd_5166_);
lean_dec_ref(v_pos_5164_);
lean_dec_ref(v___y_5162_);
return v___y_5163_;
}
else
{
lean_object* v___x_5168_; uint8_t v___x_5169_; 
lean_dec_ref(v___y_5163_);
v___x_5168_ = lean_string_utf8_byte_size(v_fst_5165_);
v___x_5169_ = lean_nat_dec_eq(v_snd_5166_, v___x_5168_);
if (v___x_5169_ == 0)
{
if (v___x_5167_ == 0)
{
v___y_5155_ = v___y_5162_;
v___y_5156_ = v_pos_5164_;
v_snd_5157_ = v_snd_5166_;
goto v___jp_5154_;
}
else
{
uint32_t v___x_5170_; uint32_t v_c_5171_; uint8_t v___x_5172_; 
v___x_5170_ = 72;
v_c_5171_ = lean_string_utf8_get_fast(v_fst_5165_, v_snd_5166_);
v___x_5172_ = lean_uint32_dec_eq(v_c_5171_, v___x_5170_);
if (v___x_5172_ == 0)
{
lean_object* v___x_5173_; 
v___x_5173_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3);
v___y_5149_ = v___y_5162_;
v_snd_5150_ = v_snd_5166_;
v_pos_5151_ = v_pos_5164_;
v_err_5152_ = v___x_5173_;
goto v___jp_5148_;
}
else
{
lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5189_; 
lean_inc(v_fst_5165_);
v_isSharedCheck_5189_ = !lean_is_exclusive(v_pos_5164_);
if (v_isSharedCheck_5189_ == 0)
{
lean_object* v_unused_5190_; lean_object* v_unused_5191_; 
v_unused_5190_ = lean_ctor_get(v_pos_5164_, 1);
lean_dec(v_unused_5190_);
v_unused_5191_ = lean_ctor_get(v_pos_5164_, 0);
lean_dec(v_unused_5191_);
v___x_5175_ = v_pos_5164_;
v_isShared_5176_ = v_isSharedCheck_5189_;
goto v_resetjp_5174_;
}
else
{
lean_dec(v_pos_5164_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5189_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5177_; lean_object* v_it_x27_5179_; 
v___x_5177_ = lean_string_utf8_next_fast(v_fst_5165_, v_snd_5166_);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 1, v___x_5177_);
v_it_x27_5179_ = v___x_5175_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_fst_5165_);
lean_ctor_set(v_reuseFailAlloc_5188_, 1, v___x_5177_);
v_it_x27_5179_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
lean_object* v___x_5180_; lean_object* v___x_5181_; 
v___x_5180_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0);
v___x_5181_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(v___x_5180_, v_it_x27_5179_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v_pos_5182_; lean_object* v_res_5183_; lean_object* v___x_5184_; 
v_pos_5182_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_pos_5182_);
v_res_5183_ = lean_ctor_get(v___x_5181_, 1);
lean_inc(v_res_5183_);
lean_dec_ref_known(v___x_5181_, 2);
lean_inc_ref(v___y_5162_);
v___x_5184_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5159_, v___y_5162_, v_res_5183_, v_pos_5182_);
if (lean_obj_tag(v___x_5184_) == 0)
{
lean_dec(v_snd_5166_);
lean_dec_ref(v___y_5162_);
return v___x_5184_;
}
else
{
lean_object* v_pos_5185_; 
v_pos_5185_ = lean_ctor_get(v___x_5184_, 0);
lean_inc(v_pos_5185_);
v___y_5117_ = v___y_5162_;
v_snd_5118_ = v_snd_5166_;
v___y_5119_ = v___x_5184_;
v_pos_5120_ = v_pos_5185_;
goto v___jp_5116_;
}
}
else
{
lean_object* v_pos_5186_; lean_object* v_err_5187_; 
v_pos_5186_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_pos_5186_);
v_err_5187_ = lean_ctor_get(v___x_5181_, 1);
lean_inc(v_err_5187_);
lean_dec_ref_known(v___x_5181_, 2);
v___y_5149_ = v___y_5162_;
v_snd_5150_ = v_snd_5166_;
v_pos_5151_ = v_pos_5186_;
v_err_5152_ = v_err_5187_;
goto v___jp_5148_;
}
}
}
}
}
}
else
{
v___y_5155_ = v___y_5162_;
v___y_5156_ = v_pos_5164_;
v_snd_5157_ = v_snd_5166_;
goto v___jp_5154_;
}
}
}
v___jp_5192_:
{
lean_object* v___x_5197_; 
lean_inc_ref(v_pos_5195_);
v___x_5197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5197_, 0, v_pos_5195_);
lean_ctor_set(v___x_5197_, 1, v_err_5196_);
v_snd_5161_ = v_snd_5193_;
v___y_5162_ = v___y_5194_;
v___y_5163_ = v___x_5197_;
v_pos_5164_ = v_pos_5195_;
goto v___jp_5160_;
}
v___jp_5198_:
{
lean_object* v___x_5202_; 
v___x_5202_ = lean_box(0);
v_snd_5193_ = v_snd_5200_;
v___y_5194_ = v___y_5201_;
v_pos_5195_ = v___y_5199_;
v_err_5196_ = v___x_5202_;
goto v___jp_5192_;
}
v___jp_5204_:
{
lean_object* v_fst_5209_; lean_object* v_snd_5210_; uint8_t v___x_5211_; 
v_fst_5209_ = lean_ctor_get(v_pos_5208_, 0);
v_snd_5210_ = lean_ctor_get(v_pos_5208_, 1);
lean_inc(v_snd_5210_);
v___x_5211_ = lean_nat_dec_eq(v_snd_5205_, v_snd_5210_);
lean_dec(v_snd_5205_);
if (v___x_5211_ == 0)
{
lean_dec(v_snd_5210_);
lean_dec_ref(v_pos_5208_);
lean_dec_ref(v___y_5206_);
return v___y_5207_;
}
else
{
lean_object* v___x_5212_; uint8_t v___x_5213_; 
lean_dec_ref(v___y_5207_);
v___x_5212_ = lean_string_utf8_byte_size(v_fst_5209_);
v___x_5213_ = lean_nat_dec_eq(v_snd_5210_, v___x_5212_);
if (v___x_5213_ == 0)
{
if (v___x_5211_ == 0)
{
v___y_5199_ = v_pos_5208_;
v_snd_5200_ = v_snd_5210_;
v___y_5201_ = v___y_5206_;
goto v___jp_5198_;
}
else
{
uint32_t v___x_5214_; uint32_t v_c_5215_; uint8_t v___x_5216_; 
v___x_5214_ = 107;
v_c_5215_ = lean_string_utf8_get_fast(v_fst_5209_, v_snd_5210_);
v___x_5216_ = lean_uint32_dec_eq(v_c_5215_, v___x_5214_);
if (v___x_5216_ == 0)
{
lean_object* v___x_5217_; 
v___x_5217_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3);
v_snd_5193_ = v_snd_5210_;
v___y_5194_ = v___y_5206_;
v_pos_5195_ = v_pos_5208_;
v_err_5196_ = v___x_5217_;
goto v___jp_5192_;
}
else
{
lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5233_; 
lean_inc(v_fst_5209_);
v_isSharedCheck_5233_ = !lean_is_exclusive(v_pos_5208_);
if (v_isSharedCheck_5233_ == 0)
{
lean_object* v_unused_5234_; lean_object* v_unused_5235_; 
v_unused_5234_ = lean_ctor_get(v_pos_5208_, 1);
lean_dec(v_unused_5234_);
v_unused_5235_ = lean_ctor_get(v_pos_5208_, 0);
lean_dec(v_unused_5235_);
v___x_5219_ = v_pos_5208_;
v_isShared_5220_ = v_isSharedCheck_5233_;
goto v_resetjp_5218_;
}
else
{
lean_dec(v_pos_5208_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5233_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5221_; lean_object* v_it_x27_5223_; 
v___x_5221_ = lean_string_utf8_next_fast(v_fst_5209_, v_snd_5210_);
if (v_isShared_5220_ == 0)
{
lean_ctor_set(v___x_5219_, 1, v___x_5221_);
v_it_x27_5223_ = v___x_5219_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_fst_5209_);
lean_ctor_set(v_reuseFailAlloc_5232_, 1, v___x_5221_);
v_it_x27_5223_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
lean_object* v___x_5224_; lean_object* v___x_5225_; 
v___x_5224_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0);
v___x_5225_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(v___x_5224_, v_it_x27_5223_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_pos_5226_; lean_object* v_res_5227_; lean_object* v___x_5228_; 
v_pos_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_pos_5226_);
v_res_5227_ = lean_ctor_get(v___x_5225_, 1);
lean_inc(v_res_5227_);
lean_dec_ref_known(v___x_5225_, 2);
lean_inc_ref(v___y_5206_);
v___x_5228_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5203_, v___y_5206_, v_res_5227_, v_pos_5226_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_dec(v_snd_5210_);
lean_dec_ref(v___y_5206_);
return v___x_5228_;
}
else
{
lean_object* v_pos_5229_; 
v_pos_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc(v_pos_5229_);
v_snd_5161_ = v_snd_5210_;
v___y_5162_ = v___y_5206_;
v___y_5163_ = v___x_5228_;
v_pos_5164_ = v_pos_5229_;
goto v___jp_5160_;
}
}
else
{
lean_object* v_pos_5230_; lean_object* v_err_5231_; 
v_pos_5230_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_pos_5230_);
v_err_5231_ = lean_ctor_get(v___x_5225_, 1);
lean_inc(v_err_5231_);
lean_dec_ref_known(v___x_5225_, 2);
v_snd_5193_ = v_snd_5210_;
v___y_5194_ = v___y_5206_;
v_pos_5195_ = v_pos_5230_;
v_err_5196_ = v_err_5231_;
goto v___jp_5192_;
}
}
}
}
}
}
else
{
v___y_5199_ = v_pos_5208_;
v_snd_5200_ = v_snd_5210_;
v___y_5201_ = v___y_5206_;
goto v___jp_5198_;
}
}
}
v___jp_5236_:
{
lean_object* v___x_5241_; 
lean_inc_ref(v_pos_5239_);
v___x_5241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5241_, 0, v_pos_5239_);
lean_ctor_set(v___x_5241_, 1, v_err_5240_);
v_snd_5205_ = v_snd_5238_;
v___y_5206_ = v___y_5237_;
v___y_5207_ = v___x_5241_;
v_pos_5208_ = v_pos_5239_;
goto v___jp_5204_;
}
v___jp_5242_:
{
lean_object* v___x_5246_; 
v___x_5246_ = lean_box(0);
v___y_5237_ = v___y_5243_;
v_snd_5238_ = v_snd_5245_;
v_pos_5239_ = v___y_5244_;
v_err_5240_ = v___x_5246_;
goto v___jp_5236_;
}
v___jp_5248_:
{
lean_object* v_fst_5253_; lean_object* v_snd_5254_; uint8_t v___x_5255_; 
v_fst_5253_ = lean_ctor_get(v_pos_5252_, 0);
v_snd_5254_ = lean_ctor_get(v_pos_5252_, 1);
lean_inc(v_snd_5254_);
v___x_5255_ = lean_nat_dec_eq(v_snd_5249_, v_snd_5254_);
lean_dec(v_snd_5249_);
if (v___x_5255_ == 0)
{
lean_dec(v_snd_5254_);
lean_dec_ref(v_pos_5252_);
lean_dec_ref(v___y_5250_);
return v___y_5251_;
}
else
{
lean_object* v___x_5256_; uint8_t v___x_5257_; 
lean_dec_ref(v___y_5251_);
v___x_5256_ = lean_string_utf8_byte_size(v_fst_5253_);
v___x_5257_ = lean_nat_dec_eq(v_snd_5254_, v___x_5256_);
if (v___x_5257_ == 0)
{
if (v___x_5255_ == 0)
{
v___y_5243_ = v___y_5250_;
v___y_5244_ = v_pos_5252_;
v_snd_5245_ = v_snd_5254_;
goto v___jp_5242_;
}
else
{
uint32_t v___x_5258_; uint32_t v_c_5259_; uint8_t v___x_5260_; 
v___x_5258_ = 75;
v_c_5259_ = lean_string_utf8_get_fast(v_fst_5253_, v_snd_5254_);
v___x_5260_ = lean_uint32_dec_eq(v_c_5259_, v___x_5258_);
if (v___x_5260_ == 0)
{
lean_object* v___x_5261_; 
v___x_5261_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3);
v___y_5237_ = v___y_5250_;
v_snd_5238_ = v_snd_5254_;
v_pos_5239_ = v_pos_5252_;
v_err_5240_ = v___x_5261_;
goto v___jp_5236_;
}
else
{
lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5277_; 
lean_inc(v_fst_5253_);
v_isSharedCheck_5277_ = !lean_is_exclusive(v_pos_5252_);
if (v_isSharedCheck_5277_ == 0)
{
lean_object* v_unused_5278_; lean_object* v_unused_5279_; 
v_unused_5278_ = lean_ctor_get(v_pos_5252_, 1);
lean_dec(v_unused_5278_);
v_unused_5279_ = lean_ctor_get(v_pos_5252_, 0);
lean_dec(v_unused_5279_);
v___x_5263_ = v_pos_5252_;
v_isShared_5264_ = v_isSharedCheck_5277_;
goto v_resetjp_5262_;
}
else
{
lean_dec(v_pos_5252_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5277_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v___x_5265_; lean_object* v_it_x27_5267_; 
v___x_5265_ = lean_string_utf8_next_fast(v_fst_5253_, v_snd_5254_);
if (v_isShared_5264_ == 0)
{
lean_ctor_set(v___x_5263_, 1, v___x_5265_);
v_it_x27_5267_ = v___x_5263_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_fst_5253_);
lean_ctor_set(v_reuseFailAlloc_5276_, 1, v___x_5265_);
v_it_x27_5267_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5268_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0);
v___x_5269_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(v___x_5268_, v_it_x27_5267_);
if (lean_obj_tag(v___x_5269_) == 0)
{
lean_object* v_pos_5270_; lean_object* v_res_5271_; lean_object* v___x_5272_; 
v_pos_5270_ = lean_ctor_get(v___x_5269_, 0);
lean_inc(v_pos_5270_);
v_res_5271_ = lean_ctor_get(v___x_5269_, 1);
lean_inc(v_res_5271_);
lean_dec_ref_known(v___x_5269_, 2);
lean_inc_ref(v___y_5250_);
v___x_5272_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5247_, v___y_5250_, v_res_5271_, v_pos_5270_);
if (lean_obj_tag(v___x_5272_) == 0)
{
lean_dec(v_snd_5254_);
lean_dec_ref(v___y_5250_);
return v___x_5272_;
}
else
{
lean_object* v_pos_5273_; 
v_pos_5273_ = lean_ctor_get(v___x_5272_, 0);
lean_inc(v_pos_5273_);
v_snd_5205_ = v_snd_5254_;
v___y_5206_ = v___y_5250_;
v___y_5207_ = v___x_5272_;
v_pos_5208_ = v_pos_5273_;
goto v___jp_5204_;
}
}
else
{
lean_object* v_pos_5274_; lean_object* v_err_5275_; 
v_pos_5274_ = lean_ctor_get(v___x_5269_, 0);
lean_inc(v_pos_5274_);
v_err_5275_ = lean_ctor_get(v___x_5269_, 1);
lean_inc(v_err_5275_);
lean_dec_ref_known(v___x_5269_, 2);
v___y_5237_ = v___y_5250_;
v_snd_5238_ = v_snd_5254_;
v_pos_5239_ = v_pos_5274_;
v_err_5240_ = v_err_5275_;
goto v___jp_5236_;
}
}
}
}
}
}
else
{
v___y_5243_ = v___y_5250_;
v___y_5244_ = v_pos_5252_;
v_snd_5245_ = v_snd_5254_;
goto v___jp_5242_;
}
}
}
v___jp_5280_:
{
lean_object* v___x_5285_; 
lean_inc_ref(v_pos_5283_);
v___x_5285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5285_, 0, v_pos_5283_);
lean_ctor_set(v___x_5285_, 1, v_err_5284_);
v_snd_5249_ = v_snd_5281_;
v___y_5250_ = v___y_5282_;
v___y_5251_ = v___x_5285_;
v_pos_5252_ = v_pos_5283_;
goto v___jp_5248_;
}
v___jp_5286_:
{
lean_object* v___x_5290_; 
v___x_5290_ = lean_box(0);
v_snd_5281_ = v_snd_5288_;
v___y_5282_ = v___y_5289_;
v_pos_5283_ = v___y_5287_;
v_err_5284_ = v___x_5290_;
goto v___jp_5280_;
}
v___jp_5292_:
{
lean_object* v_fst_5297_; lean_object* v_snd_5298_; uint8_t v___x_5299_; 
v_fst_5297_ = lean_ctor_get(v_pos_5296_, 0);
v_snd_5298_ = lean_ctor_get(v_pos_5296_, 1);
lean_inc(v_snd_5298_);
v___x_5299_ = lean_nat_dec_eq(v_snd_5294_, v_snd_5298_);
lean_dec(v_snd_5294_);
if (v___x_5299_ == 0)
{
lean_dec(v_snd_5298_);
lean_dec_ref(v_pos_5296_);
lean_dec_ref(v___y_5293_);
return v___y_5295_;
}
else
{
lean_object* v___x_5300_; uint8_t v___x_5301_; 
lean_dec_ref(v___y_5295_);
v___x_5300_ = lean_string_utf8_byte_size(v_fst_5297_);
v___x_5301_ = lean_nat_dec_eq(v_snd_5298_, v___x_5300_);
if (v___x_5301_ == 0)
{
if (v___x_5299_ == 0)
{
v___y_5287_ = v_pos_5296_;
v_snd_5288_ = v_snd_5298_;
v___y_5289_ = v___y_5293_;
goto v___jp_5286_;
}
else
{
uint32_t v___x_5302_; uint32_t v_c_5303_; uint8_t v___x_5304_; 
v___x_5302_ = 104;
v_c_5303_ = lean_string_utf8_get_fast(v_fst_5297_, v_snd_5298_);
v___x_5304_ = lean_uint32_dec_eq(v_c_5303_, v___x_5302_);
if (v___x_5304_ == 0)
{
lean_object* v___x_5305_; 
v___x_5305_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3);
v_snd_5281_ = v_snd_5298_;
v___y_5282_ = v___y_5293_;
v_pos_5283_ = v_pos_5296_;
v_err_5284_ = v___x_5305_;
goto v___jp_5280_;
}
else
{
lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5321_; 
lean_inc(v_fst_5297_);
v_isSharedCheck_5321_ = !lean_is_exclusive(v_pos_5296_);
if (v_isSharedCheck_5321_ == 0)
{
lean_object* v_unused_5322_; lean_object* v_unused_5323_; 
v_unused_5322_ = lean_ctor_get(v_pos_5296_, 1);
lean_dec(v_unused_5322_);
v_unused_5323_ = lean_ctor_get(v_pos_5296_, 0);
lean_dec(v_unused_5323_);
v___x_5307_ = v_pos_5296_;
v_isShared_5308_ = v_isSharedCheck_5321_;
goto v_resetjp_5306_;
}
else
{
lean_dec(v_pos_5296_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5321_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5309_; lean_object* v_it_x27_5311_; 
v___x_5309_ = lean_string_utf8_next_fast(v_fst_5297_, v_snd_5298_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 1, v___x_5309_);
v_it_x27_5311_ = v___x_5307_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_fst_5297_);
lean_ctor_set(v_reuseFailAlloc_5320_, 1, v___x_5309_);
v_it_x27_5311_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
lean_object* v___x_5312_; lean_object* v___x_5313_; 
v___x_5312_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0);
v___x_5313_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(v___x_5312_, v_it_x27_5311_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_pos_5314_; lean_object* v_res_5315_; lean_object* v___x_5316_; 
v_pos_5314_ = lean_ctor_get(v___x_5313_, 0);
lean_inc(v_pos_5314_);
v_res_5315_ = lean_ctor_get(v___x_5313_, 1);
lean_inc(v_res_5315_);
lean_dec_ref_known(v___x_5313_, 2);
lean_inc_ref(v___y_5293_);
v___x_5316_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5291_, v___y_5293_, v_res_5315_, v_pos_5314_);
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_dec(v_snd_5298_);
lean_dec_ref(v___y_5293_);
return v___x_5316_;
}
else
{
lean_object* v_pos_5317_; 
v_pos_5317_ = lean_ctor_get(v___x_5316_, 0);
lean_inc(v_pos_5317_);
v_snd_5249_ = v_snd_5298_;
v___y_5250_ = v___y_5293_;
v___y_5251_ = v___x_5316_;
v_pos_5252_ = v_pos_5317_;
goto v___jp_5248_;
}
}
else
{
lean_object* v_pos_5318_; lean_object* v_err_5319_; 
v_pos_5318_ = lean_ctor_get(v___x_5313_, 0);
lean_inc(v_pos_5318_);
v_err_5319_ = lean_ctor_get(v___x_5313_, 1);
lean_inc(v_err_5319_);
lean_dec_ref_known(v___x_5313_, 2);
v_snd_5281_ = v_snd_5298_;
v___y_5282_ = v___y_5293_;
v_pos_5283_ = v_pos_5318_;
v_err_5284_ = v_err_5319_;
goto v___jp_5280_;
}
}
}
}
}
}
else
{
v___y_5287_ = v_pos_5296_;
v_snd_5288_ = v_snd_5298_;
v___y_5289_ = v___y_5293_;
goto v___jp_5286_;
}
}
}
v___jp_5324_:
{
lean_object* v___x_5329_; 
lean_inc_ref(v_pos_5327_);
v___x_5329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5329_, 0, v_pos_5327_);
lean_ctor_set(v___x_5329_, 1, v_err_5328_);
v___y_5293_ = v___y_5325_;
v_snd_5294_ = v_snd_5326_;
v___y_5295_ = v___x_5329_;
v_pos_5296_ = v_pos_5327_;
goto v___jp_5292_;
}
v___jp_5330_:
{
lean_object* v___x_5334_; 
v___x_5334_ = lean_box(0);
v___y_5325_ = v___y_5331_;
v_snd_5326_ = v_snd_5333_;
v_pos_5327_ = v___y_5332_;
v_err_5328_ = v___x_5334_;
goto v___jp_5324_;
}
v___jp_5335_:
{
lean_object* v_fst_5340_; lean_object* v_snd_5341_; uint8_t v___x_5342_; 
v_fst_5340_ = lean_ctor_get(v_pos_5339_, 0);
v_snd_5341_ = lean_ctor_get(v_pos_5339_, 1);
lean_inc(v_snd_5341_);
v___x_5342_ = lean_nat_dec_eq(v_snd_5337_, v_snd_5341_);
lean_dec(v_snd_5337_);
if (v___x_5342_ == 0)
{
lean_dec(v_snd_5341_);
lean_dec_ref(v_pos_5339_);
lean_dec_ref(v___y_5336_);
return v___y_5338_;
}
else
{
lean_object* v___x_5343_; uint8_t v___x_5344_; 
lean_dec_ref(v___y_5338_);
v___x_5343_ = lean_string_utf8_byte_size(v_fst_5340_);
v___x_5344_ = lean_nat_dec_eq(v_snd_5341_, v___x_5343_);
if (v___x_5344_ == 0)
{
if (v___x_5342_ == 0)
{
v___y_5331_ = v___y_5336_;
v___y_5332_ = v_pos_5339_;
v_snd_5333_ = v_snd_5341_;
goto v___jp_5330_;
}
else
{
uint32_t v___x_5345_; uint32_t v_c_5346_; uint8_t v___x_5347_; 
v___x_5345_ = 66;
v_c_5346_ = lean_string_utf8_get_fast(v_fst_5340_, v_snd_5341_);
v___x_5347_ = lean_uint32_dec_eq(v_c_5346_, v___x_5345_);
if (v___x_5347_ == 0)
{
lean_object* v___x_5348_; 
v___x_5348_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3);
v___y_5325_ = v___y_5336_;
v_snd_5326_ = v_snd_5341_;
v_pos_5327_ = v_pos_5339_;
v_err_5328_ = v___x_5348_;
goto v___jp_5324_;
}
else
{
lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5364_; 
lean_inc(v_fst_5340_);
v_isSharedCheck_5364_ = !lean_is_exclusive(v_pos_5339_);
if (v_isSharedCheck_5364_ == 0)
{
lean_object* v_unused_5365_; lean_object* v_unused_5366_; 
v_unused_5365_ = lean_ctor_get(v_pos_5339_, 1);
lean_dec(v_unused_5365_);
v_unused_5366_ = lean_ctor_get(v_pos_5339_, 0);
lean_dec(v_unused_5366_);
v___x_5350_ = v_pos_5339_;
v_isShared_5351_ = v_isSharedCheck_5364_;
goto v_resetjp_5349_;
}
else
{
lean_dec(v_pos_5339_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5364_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5352_; lean_object* v_it_x27_5354_; 
v___x_5352_ = lean_string_utf8_next_fast(v_fst_5340_, v_snd_5341_);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 1, v___x_5352_);
v_it_x27_5354_ = v___x_5350_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_fst_5340_);
lean_ctor_set(v_reuseFailAlloc_5363_, 1, v___x_5352_);
v_it_x27_5354_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
lean_object* v___x_5355_; lean_object* v___x_5356_; 
v___x_5355_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0);
v___x_5356_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(v___x_5355_, v_it_x27_5354_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_pos_5357_; lean_object* v_res_5358_; lean_object* v___x_5359_; 
v_pos_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_pos_5357_);
v_res_5358_ = lean_ctor_get(v___x_5356_, 1);
lean_inc(v_res_5358_);
lean_dec_ref_known(v___x_5356_, 2);
v___x_5359_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(v_res_5358_, v_pos_5357_);
if (lean_obj_tag(v___x_5359_) == 0)
{
lean_dec(v_snd_5341_);
lean_dec_ref(v___y_5336_);
return v___x_5359_;
}
else
{
lean_object* v_pos_5360_; 
v_pos_5360_ = lean_ctor_get(v___x_5359_, 0);
lean_inc(v_pos_5360_);
v___y_5293_ = v___y_5336_;
v_snd_5294_ = v_snd_5341_;
v___y_5295_ = v___x_5359_;
v_pos_5296_ = v_pos_5360_;
goto v___jp_5292_;
}
}
else
{
lean_object* v_pos_5361_; lean_object* v_err_5362_; 
v_pos_5361_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_pos_5361_);
v_err_5362_ = lean_ctor_get(v___x_5356_, 1);
lean_inc(v_err_5362_);
lean_dec_ref_known(v___x_5356_, 2);
v___y_5325_ = v___y_5336_;
v_snd_5326_ = v_snd_5341_;
v_pos_5327_ = v_pos_5361_;
v_err_5328_ = v_err_5362_;
goto v___jp_5324_;
}
}
}
}
}
}
else
{
v___y_5331_ = v___y_5336_;
v___y_5332_ = v_pos_5339_;
v_snd_5333_ = v_snd_5341_;
goto v___jp_5330_;
}
}
}
v___jp_5367_:
{
lean_object* v___x_5372_; 
lean_inc_ref(v_pos_5370_);
v___x_5372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5372_, 0, v_pos_5370_);
lean_ctor_set(v___x_5372_, 1, v_err_5371_);
v___y_5336_ = v___y_5368_;
v_snd_5337_ = v_snd_5369_;
v___y_5338_ = v___x_5372_;
v_pos_5339_ = v_pos_5370_;
goto v___jp_5335_;
}
v___jp_5373_:
{
lean_object* v___x_5377_; 
v___x_5377_ = lean_box(0);
v___y_5368_ = v___y_5374_;
v_snd_5369_ = v_snd_5376_;
v_pos_5370_ = v___y_5375_;
v_err_5371_ = v___x_5377_;
goto v___jp_5367_;
}
v___jp_5378_:
{
lean_object* v_fst_5383_; lean_object* v_snd_5384_; uint8_t v___x_5385_; 
v_fst_5383_ = lean_ctor_get(v_pos_5382_, 0);
v_snd_5384_ = lean_ctor_get(v_pos_5382_, 1);
lean_inc(v_snd_5384_);
v___x_5385_ = lean_nat_dec_eq(v_snd_5380_, v_snd_5384_);
lean_dec(v_snd_5380_);
if (v___x_5385_ == 0)
{
lean_dec(v_snd_5384_);
lean_dec_ref(v_pos_5382_);
lean_dec_ref(v___y_5379_);
return v___y_5381_;
}
else
{
lean_object* v___x_5386_; uint8_t v___x_5387_; 
lean_dec_ref(v___y_5381_);
v___x_5386_ = lean_string_utf8_byte_size(v_fst_5383_);
v___x_5387_ = lean_nat_dec_eq(v_snd_5384_, v___x_5386_);
if (v___x_5387_ == 0)
{
if (v___x_5385_ == 0)
{
v___y_5374_ = v___y_5379_;
v___y_5375_ = v_pos_5382_;
v_snd_5376_ = v_snd_5384_;
goto v___jp_5373_;
}
else
{
uint32_t v___x_5388_; uint32_t v_c_5389_; uint8_t v___x_5390_; 
v___x_5388_ = 98;
v_c_5389_ = lean_string_utf8_get_fast(v_fst_5383_, v_snd_5384_);
v___x_5390_ = lean_uint32_dec_eq(v_c_5389_, v___x_5388_);
if (v___x_5390_ == 0)
{
lean_object* v___x_5391_; 
v___x_5391_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3);
v___y_5368_ = v___y_5379_;
v_snd_5369_ = v_snd_5384_;
v_pos_5370_ = v_pos_5382_;
v_err_5371_ = v___x_5391_;
goto v___jp_5367_;
}
else
{
lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5407_; 
lean_inc(v_fst_5383_);
v_isSharedCheck_5407_ = !lean_is_exclusive(v_pos_5382_);
if (v_isSharedCheck_5407_ == 0)
{
lean_object* v_unused_5408_; lean_object* v_unused_5409_; 
v_unused_5408_ = lean_ctor_get(v_pos_5382_, 1);
lean_dec(v_unused_5408_);
v_unused_5409_ = lean_ctor_get(v_pos_5382_, 0);
lean_dec(v_unused_5409_);
v___x_5393_ = v_pos_5382_;
v_isShared_5394_ = v_isSharedCheck_5407_;
goto v_resetjp_5392_;
}
else
{
lean_dec(v_pos_5382_);
v___x_5393_ = lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5407_;
goto v_resetjp_5392_;
}
v_resetjp_5392_:
{
lean_object* v___x_5395_; lean_object* v_it_x27_5397_; 
v___x_5395_ = lean_string_utf8_next_fast(v_fst_5383_, v_snd_5384_);
if (v_isShared_5394_ == 0)
{
lean_ctor_set(v___x_5393_, 1, v___x_5395_);
v_it_x27_5397_ = v___x_5393_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_fst_5383_);
lean_ctor_set(v_reuseFailAlloc_5406_, 1, v___x_5395_);
v_it_x27_5397_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; 
v___x_5398_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0);
v___x_5399_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(v___x_5398_, v_it_x27_5397_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_object* v_pos_5400_; lean_object* v_res_5401_; lean_object* v___x_5402_; 
v_pos_5400_ = lean_ctor_get(v___x_5399_, 0);
lean_inc(v_pos_5400_);
v_res_5401_ = lean_ctor_get(v___x_5399_, 1);
lean_inc(v_res_5401_);
lean_dec_ref_known(v___x_5399_, 2);
v___x_5402_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(v_res_5401_, v_pos_5400_);
if (lean_obj_tag(v___x_5402_) == 0)
{
lean_dec(v_snd_5384_);
lean_dec_ref(v___y_5379_);
return v___x_5402_;
}
else
{
lean_object* v_pos_5403_; 
v_pos_5403_ = lean_ctor_get(v___x_5402_, 0);
lean_inc(v_pos_5403_);
v___y_5336_ = v___y_5379_;
v_snd_5337_ = v_snd_5384_;
v___y_5338_ = v___x_5402_;
v_pos_5339_ = v_pos_5403_;
goto v___jp_5335_;
}
}
else
{
lean_object* v_pos_5404_; lean_object* v_err_5405_; 
v_pos_5404_ = lean_ctor_get(v___x_5399_, 0);
lean_inc(v_pos_5404_);
v_err_5405_ = lean_ctor_get(v___x_5399_, 1);
lean_inc(v_err_5405_);
lean_dec_ref_known(v___x_5399_, 2);
v___y_5368_ = v___y_5379_;
v_snd_5369_ = v_snd_5384_;
v_pos_5370_ = v_pos_5404_;
v_err_5371_ = v_err_5405_;
goto v___jp_5367_;
}
}
}
}
}
}
else
{
v___y_5374_ = v___y_5379_;
v___y_5375_ = v_pos_5382_;
v_snd_5376_ = v_snd_5384_;
goto v___jp_5373_;
}
}
}
v___jp_5410_:
{
lean_object* v___x_5415_; 
lean_inc_ref(v_pos_5413_);
v___x_5415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5415_, 0, v_pos_5413_);
lean_ctor_set(v___x_5415_, 1, v_err_5414_);
v___y_5379_ = v___y_5411_;
v_snd_5380_ = v_snd_5412_;
v___y_5381_ = v___x_5415_;
v_pos_5382_ = v_pos_5413_;
goto v___jp_5378_;
}
v___jp_5416_:
{
lean_object* v___x_5420_; 
v___x_5420_ = lean_box(0);
v___y_5411_ = v___y_5417_;
v_snd_5412_ = v_snd_5419_;
v_pos_5413_ = v___y_5418_;
v_err_5414_ = v___x_5420_;
goto v___jp_5410_;
}
v___jp_5421_:
{
lean_object* v_fst_5426_; lean_object* v_snd_5427_; uint8_t v___x_5428_; 
v_fst_5426_ = lean_ctor_get(v_pos_5425_, 0);
v_snd_5427_ = lean_ctor_get(v_pos_5425_, 1);
lean_inc(v_snd_5427_);
v___x_5428_ = lean_nat_dec_eq(v_snd_5422_, v_snd_5427_);
lean_dec(v_snd_5422_);
if (v___x_5428_ == 0)
{
lean_dec(v_snd_5427_);
lean_dec_ref(v_pos_5425_);
lean_dec_ref(v___y_5423_);
return v___y_5424_;
}
else
{
lean_object* v___x_5429_; uint8_t v___x_5430_; 
lean_dec_ref(v___y_5424_);
v___x_5429_ = lean_string_utf8_byte_size(v_fst_5426_);
v___x_5430_ = lean_nat_dec_eq(v_snd_5427_, v___x_5429_);
if (v___x_5430_ == 0)
{
if (v___x_5428_ == 0)
{
v___y_5417_ = v___y_5423_;
v___y_5418_ = v_pos_5425_;
v_snd_5419_ = v_snd_5427_;
goto v___jp_5416_;
}
else
{
uint32_t v___x_5431_; uint32_t v_c_5432_; uint8_t v___x_5433_; 
v___x_5431_ = 97;
v_c_5432_ = lean_string_utf8_get_fast(v_fst_5426_, v_snd_5427_);
v___x_5433_ = lean_uint32_dec_eq(v_c_5432_, v___x_5431_);
if (v___x_5433_ == 0)
{
lean_object* v___x_5434_; 
v___x_5434_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3);
v___y_5411_ = v___y_5423_;
v_snd_5412_ = v_snd_5427_;
v_pos_5413_ = v_pos_5425_;
v_err_5414_ = v___x_5434_;
goto v___jp_5410_;
}
else
{
lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5450_; 
lean_inc(v_fst_5426_);
v_isSharedCheck_5450_ = !lean_is_exclusive(v_pos_5425_);
if (v_isSharedCheck_5450_ == 0)
{
lean_object* v_unused_5451_; lean_object* v_unused_5452_; 
v_unused_5451_ = lean_ctor_get(v_pos_5425_, 1);
lean_dec(v_unused_5451_);
v_unused_5452_ = lean_ctor_get(v_pos_5425_, 0);
lean_dec(v_unused_5452_);
v___x_5436_ = v_pos_5425_;
v_isShared_5437_ = v_isSharedCheck_5450_;
goto v_resetjp_5435_;
}
else
{
lean_dec(v_pos_5425_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5450_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5438_; lean_object* v_it_x27_5440_; 
v___x_5438_ = lean_string_utf8_next_fast(v_fst_5426_, v_snd_5427_);
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 1, v___x_5438_);
v_it_x27_5440_ = v___x_5436_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_fst_5426_);
lean_ctor_set(v_reuseFailAlloc_5449_, 1, v___x_5438_);
v_it_x27_5440_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
lean_object* v___x_5441_; lean_object* v___x_5442_; 
v___x_5441_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0);
v___x_5442_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(v___x_5441_, v_it_x27_5440_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_pos_5443_; lean_object* v_res_5444_; lean_object* v___x_5445_; 
v_pos_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_pos_5443_);
v_res_5444_ = lean_ctor_get(v___x_5442_, 1);
lean_inc(v_res_5444_);
lean_dec_ref_known(v___x_5442_, 2);
v___x_5445_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(v_res_5444_, v_pos_5443_);
if (lean_obj_tag(v___x_5445_) == 0)
{
lean_dec(v_snd_5427_);
lean_dec_ref(v___y_5423_);
return v___x_5445_;
}
else
{
lean_object* v_pos_5446_; 
v_pos_5446_ = lean_ctor_get(v___x_5445_, 0);
lean_inc(v_pos_5446_);
v___y_5379_ = v___y_5423_;
v_snd_5380_ = v_snd_5427_;
v___y_5381_ = v___x_5445_;
v_pos_5382_ = v_pos_5446_;
goto v___jp_5378_;
}
}
else
{
lean_object* v_pos_5447_; lean_object* v_err_5448_; 
v_pos_5447_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_pos_5447_);
v_err_5448_ = lean_ctor_get(v___x_5442_, 1);
lean_inc(v_err_5448_);
lean_dec_ref_known(v___x_5442_, 2);
v___y_5411_ = v___y_5423_;
v_snd_5412_ = v_snd_5427_;
v_pos_5413_ = v_pos_5447_;
v_err_5414_ = v_err_5448_;
goto v___jp_5410_;
}
}
}
}
}
}
else
{
v___y_5417_ = v___y_5423_;
v___y_5418_ = v_pos_5425_;
v_snd_5419_ = v_snd_5427_;
goto v___jp_5416_;
}
}
}
v___jp_5453_:
{
lean_object* v___x_5458_; 
lean_inc_ref(v_pos_5456_);
v___x_5458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5458_, 0, v_pos_5456_);
lean_ctor_set(v___x_5458_, 1, v_err_5457_);
v_snd_5422_ = v_snd_5454_;
v___y_5423_ = v___y_5455_;
v___y_5424_ = v___x_5458_;
v_pos_5425_ = v_pos_5456_;
goto v___jp_5421_;
}
v___jp_5459_:
{
lean_object* v___x_5463_; 
v___x_5463_ = lean_box(0);
v_snd_5454_ = v_snd_5461_;
v___y_5455_ = v___y_5462_;
v_pos_5456_ = v___y_5460_;
v_err_5457_ = v___x_5463_;
goto v___jp_5453_;
}
v___jp_5465_:
{
lean_object* v_fst_5471_; lean_object* v_snd_5472_; uint8_t v___x_5473_; 
v_fst_5471_ = lean_ctor_get(v_pos_5470_, 0);
v_snd_5472_ = lean_ctor_get(v_pos_5470_, 1);
lean_inc(v_snd_5472_);
v___x_5473_ = lean_nat_dec_eq(v_snd_5466_, v_snd_5472_);
lean_dec(v_snd_5466_);
if (v___x_5473_ == 0)
{
lean_dec(v_snd_5472_);
lean_dec_ref(v_pos_5470_);
lean_dec_ref(v___y_5468_);
lean_dec_ref(v___y_5467_);
return v___y_5469_;
}
else
{
lean_object* v___x_5474_; uint8_t v___x_5475_; 
lean_dec_ref(v___y_5469_);
v___x_5474_ = lean_string_utf8_byte_size(v_fst_5471_);
v___x_5475_ = lean_nat_dec_eq(v_snd_5472_, v___x_5474_);
if (v___x_5475_ == 0)
{
if (v___x_5473_ == 0)
{
lean_dec_ref(v___y_5467_);
v___y_5460_ = v_pos_5470_;
v_snd_5461_ = v_snd_5472_;
v___y_5462_ = v___y_5468_;
goto v___jp_5459_;
}
else
{
uint32_t v___x_5476_; uint32_t v_c_5477_; uint8_t v___x_5478_; 
v___x_5476_ = 70;
v_c_5477_ = lean_string_utf8_get_fast(v_fst_5471_, v_snd_5472_);
v___x_5478_ = lean_uint32_dec_eq(v_c_5477_, v___x_5476_);
if (v___x_5478_ == 0)
{
lean_object* v___x_5479_; 
lean_dec_ref(v___y_5467_);
v___x_5479_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3);
v_snd_5454_ = v_snd_5472_;
v___y_5455_ = v___y_5468_;
v_pos_5456_ = v_pos_5470_;
v_err_5457_ = v___x_5479_;
goto v___jp_5453_;
}
else
{
lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5495_; 
lean_inc(v_fst_5471_);
v_isSharedCheck_5495_ = !lean_is_exclusive(v_pos_5470_);
if (v_isSharedCheck_5495_ == 0)
{
lean_object* v_unused_5496_; lean_object* v_unused_5497_; 
v_unused_5496_ = lean_ctor_get(v_pos_5470_, 1);
lean_dec(v_unused_5496_);
v_unused_5497_ = lean_ctor_get(v_pos_5470_, 0);
lean_dec(v_unused_5497_);
v___x_5481_ = v_pos_5470_;
v_isShared_5482_ = v_isSharedCheck_5495_;
goto v_resetjp_5480_;
}
else
{
lean_dec(v_pos_5470_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5495_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v___x_5483_; lean_object* v_it_x27_5485_; 
v___x_5483_ = lean_string_utf8_next_fast(v_fst_5471_, v_snd_5472_);
if (v_isShared_5482_ == 0)
{
lean_ctor_set(v___x_5481_, 1, v___x_5483_);
v_it_x27_5485_ = v___x_5481_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v_fst_5471_);
lean_ctor_set(v_reuseFailAlloc_5494_, 1, v___x_5483_);
v_it_x27_5485_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
lean_object* v___x_5486_; lean_object* v___x_5487_; 
v___x_5486_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0);
v___x_5487_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(v___x_5486_, v_it_x27_5485_);
if (lean_obj_tag(v___x_5487_) == 0)
{
lean_object* v_pos_5488_; lean_object* v_res_5489_; lean_object* v___x_5490_; 
v_pos_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_pos_5488_);
v_res_5489_ = lean_ctor_get(v___x_5487_, 1);
lean_inc(v_res_5489_);
lean_dec_ref_known(v___x_5487_, 2);
v___x_5490_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5464_, v___y_5467_, v_res_5489_, v_pos_5488_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_dec(v_snd_5472_);
lean_dec_ref(v___y_5468_);
return v___x_5490_;
}
else
{
lean_object* v_pos_5491_; 
v_pos_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_pos_5491_);
v_snd_5422_ = v_snd_5472_;
v___y_5423_ = v___y_5468_;
v___y_5424_ = v___x_5490_;
v_pos_5425_ = v_pos_5491_;
goto v___jp_5421_;
}
}
else
{
lean_object* v_pos_5492_; lean_object* v_err_5493_; 
lean_dec_ref(v___y_5467_);
v_pos_5492_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_pos_5492_);
v_err_5493_ = lean_ctor_get(v___x_5487_, 1);
lean_inc(v_err_5493_);
lean_dec_ref_known(v___x_5487_, 2);
v_snd_5454_ = v_snd_5472_;
v___y_5455_ = v___y_5468_;
v_pos_5456_ = v_pos_5492_;
v_err_5457_ = v_err_5493_;
goto v___jp_5453_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_5467_);
v___y_5460_ = v_pos_5470_;
v_snd_5461_ = v_snd_5472_;
v___y_5462_ = v___y_5468_;
goto v___jp_5459_;
}
}
}
v___jp_5498_:
{
lean_object* v___x_5504_; 
lean_inc_ref(v_pos_5502_);
v___x_5504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5504_, 0, v_pos_5502_);
lean_ctor_set(v___x_5504_, 1, v_err_5503_);
v_snd_5466_ = v_snd_5499_;
v___y_5467_ = v___y_5500_;
v___y_5468_ = v___y_5501_;
v___y_5469_ = v___x_5504_;
v_pos_5470_ = v_pos_5502_;
goto v___jp_5465_;
}
v___jp_5505_:
{
lean_object* v___x_5510_; 
v___x_5510_ = lean_box(0);
v_snd_5499_ = v_snd_5507_;
v___y_5500_ = v___y_5508_;
v___y_5501_ = v___y_5509_;
v_pos_5502_ = v___y_5506_;
v_err_5503_ = v___x_5510_;
goto v___jp_5498_;
}
v___jp_5512_:
{
lean_object* v_fst_5518_; lean_object* v_snd_5519_; uint8_t v___x_5520_; 
v_fst_5518_ = lean_ctor_get(v_pos_5517_, 0);
v_snd_5519_ = lean_ctor_get(v_pos_5517_, 1);
lean_inc(v_snd_5519_);
v___x_5520_ = lean_nat_dec_eq(v_snd_5514_, v_snd_5519_);
lean_dec(v_snd_5514_);
if (v___x_5520_ == 0)
{
lean_dec(v_snd_5519_);
lean_dec_ref(v_pos_5517_);
lean_dec_ref(v___y_5515_);
lean_dec_ref(v___y_5513_);
return v___y_5516_;
}
else
{
lean_object* v___x_5521_; uint8_t v___x_5522_; 
lean_dec_ref(v___y_5516_);
v___x_5521_ = lean_string_utf8_byte_size(v_fst_5518_);
v___x_5522_ = lean_nat_dec_eq(v_snd_5519_, v___x_5521_);
if (v___x_5522_ == 0)
{
if (v___x_5520_ == 0)
{
v___y_5506_ = v_pos_5517_;
v_snd_5507_ = v_snd_5519_;
v___y_5508_ = v___y_5513_;
v___y_5509_ = v___y_5515_;
goto v___jp_5505_;
}
else
{
uint32_t v___x_5523_; uint32_t v_c_5524_; uint8_t v___x_5525_; 
v___x_5523_ = 99;
v_c_5524_ = lean_string_utf8_get_fast(v_fst_5518_, v_snd_5519_);
v___x_5525_ = lean_uint32_dec_eq(v_c_5524_, v___x_5523_);
if (v___x_5525_ == 0)
{
lean_object* v___x_5526_; 
v___x_5526_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3);
v_snd_5499_ = v_snd_5519_;
v___y_5500_ = v___y_5513_;
v___y_5501_ = v___y_5515_;
v_pos_5502_ = v_pos_5517_;
v_err_5503_ = v___x_5526_;
goto v___jp_5498_;
}
else
{
lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5542_; 
lean_inc(v_fst_5518_);
v_isSharedCheck_5542_ = !lean_is_exclusive(v_pos_5517_);
if (v_isSharedCheck_5542_ == 0)
{
lean_object* v_unused_5543_; lean_object* v_unused_5544_; 
v_unused_5543_ = lean_ctor_get(v_pos_5517_, 1);
lean_dec(v_unused_5543_);
v_unused_5544_ = lean_ctor_get(v_pos_5517_, 0);
lean_dec(v_unused_5544_);
v___x_5528_ = v_pos_5517_;
v_isShared_5529_ = v_isSharedCheck_5542_;
goto v_resetjp_5527_;
}
else
{
lean_dec(v_pos_5517_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5542_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5530_; lean_object* v_it_x27_5532_; 
v___x_5530_ = lean_string_utf8_next_fast(v_fst_5518_, v_snd_5519_);
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 1, v___x_5530_);
v_it_x27_5532_ = v___x_5528_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_fst_5518_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v___x_5530_);
v_it_x27_5532_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
lean_object* v___x_5533_; lean_object* v___x_5534_; 
v___x_5533_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0);
v___x_5534_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(v___x_5533_, v_it_x27_5532_);
if (lean_obj_tag(v___x_5534_) == 0)
{
lean_object* v_pos_5535_; lean_object* v_res_5536_; lean_object* v___x_5537_; 
v_pos_5535_ = lean_ctor_get(v___x_5534_, 0);
lean_inc(v_pos_5535_);
v_res_5536_ = lean_ctor_get(v___x_5534_, 1);
lean_inc(v_res_5536_);
lean_dec_ref_known(v___x_5534_, 2);
v___x_5537_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(v___f_5511_, v_res_5536_, v_pos_5535_);
if (lean_obj_tag(v___x_5537_) == 0)
{
lean_dec(v_snd_5519_);
lean_dec_ref(v___y_5515_);
lean_dec_ref(v___y_5513_);
return v___x_5537_;
}
else
{
lean_object* v_pos_5538_; 
v_pos_5538_ = lean_ctor_get(v___x_5537_, 0);
lean_inc(v_pos_5538_);
v_snd_5466_ = v_snd_5519_;
v___y_5467_ = v___y_5513_;
v___y_5468_ = v___y_5515_;
v___y_5469_ = v___x_5537_;
v_pos_5470_ = v_pos_5538_;
goto v___jp_5465_;
}
}
else
{
lean_object* v_pos_5539_; lean_object* v_err_5540_; 
v_pos_5539_ = lean_ctor_get(v___x_5534_, 0);
lean_inc(v_pos_5539_);
v_err_5540_ = lean_ctor_get(v___x_5534_, 1);
lean_inc(v_err_5540_);
lean_dec_ref_known(v___x_5534_, 2);
v_snd_5499_ = v_snd_5519_;
v___y_5500_ = v___y_5513_;
v___y_5501_ = v___y_5515_;
v_pos_5502_ = v_pos_5539_;
v_err_5503_ = v_err_5540_;
goto v___jp_5498_;
}
}
}
}
}
}
else
{
v___y_5506_ = v_pos_5517_;
v_snd_5507_ = v_snd_5519_;
v___y_5508_ = v___y_5513_;
v___y_5509_ = v___y_5515_;
goto v___jp_5505_;
}
}
}
v___jp_5545_:
{
lean_object* v___x_5551_; 
lean_inc_ref(v_pos_5549_);
v___x_5551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5551_, 0, v_pos_5549_);
lean_ctor_set(v___x_5551_, 1, v_err_5550_);
v___y_5513_ = v___y_5546_;
v_snd_5514_ = v_snd_5547_;
v___y_5515_ = v___y_5548_;
v___y_5516_ = v___x_5551_;
v_pos_5517_ = v_pos_5549_;
goto v___jp_5512_;
}
v___jp_5552_:
{
lean_object* v___x_5557_; 
v___x_5557_ = lean_box(0);
v___y_5546_ = v___y_5553_;
v_snd_5547_ = v_snd_5555_;
v___y_5548_ = v___y_5556_;
v_pos_5549_ = v___y_5554_;
v_err_5550_ = v___x_5557_;
goto v___jp_5545_;
}
v___jp_5559_:
{
lean_object* v_fst_5565_; lean_object* v_snd_5566_; uint8_t v___x_5567_; 
v_fst_5565_ = lean_ctor_get(v_pos_5564_, 0);
v_snd_5566_ = lean_ctor_get(v_pos_5564_, 1);
lean_inc(v_snd_5566_);
v___x_5567_ = lean_nat_dec_eq(v_snd_5562_, v_snd_5566_);
lean_dec(v_snd_5562_);
if (v___x_5567_ == 0)
{
lean_dec(v_snd_5566_);
lean_dec_ref(v_pos_5564_);
lean_dec_ref(v___y_5561_);
lean_dec_ref(v___y_5560_);
return v___y_5563_;
}
else
{
lean_object* v___x_5568_; uint8_t v___x_5569_; 
lean_dec_ref(v___y_5563_);
v___x_5568_ = lean_string_utf8_byte_size(v_fst_5565_);
v___x_5569_ = lean_nat_dec_eq(v_snd_5566_, v___x_5568_);
if (v___x_5569_ == 0)
{
if (v___x_5567_ == 0)
{
v___y_5553_ = v___y_5560_;
v___y_5554_ = v_pos_5564_;
v_snd_5555_ = v_snd_5566_;
v___y_5556_ = v___y_5561_;
goto v___jp_5552_;
}
else
{
uint32_t v___x_5570_; uint32_t v_c_5571_; uint8_t v___x_5572_; 
v___x_5570_ = 101;
v_c_5571_ = lean_string_utf8_get_fast(v_fst_5565_, v_snd_5566_);
v___x_5572_ = lean_uint32_dec_eq(v_c_5571_, v___x_5570_);
if (v___x_5572_ == 0)
{
lean_object* v___x_5573_; 
v___x_5573_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3);
v___y_5546_ = v___y_5560_;
v_snd_5547_ = v_snd_5566_;
v___y_5548_ = v___y_5561_;
v_pos_5549_ = v_pos_5564_;
v_err_5550_ = v___x_5573_;
goto v___jp_5545_;
}
else
{
lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5589_; 
lean_inc(v_fst_5565_);
v_isSharedCheck_5589_ = !lean_is_exclusive(v_pos_5564_);
if (v_isSharedCheck_5589_ == 0)
{
lean_object* v_unused_5590_; lean_object* v_unused_5591_; 
v_unused_5590_ = lean_ctor_get(v_pos_5564_, 1);
lean_dec(v_unused_5590_);
v_unused_5591_ = lean_ctor_get(v_pos_5564_, 0);
lean_dec(v_unused_5591_);
v___x_5575_ = v_pos_5564_;
v_isShared_5576_ = v_isSharedCheck_5589_;
goto v_resetjp_5574_;
}
else
{
lean_dec(v_pos_5564_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5589_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5577_; lean_object* v_it_x27_5579_; 
v___x_5577_ = lean_string_utf8_next_fast(v_fst_5565_, v_snd_5566_);
if (v_isShared_5576_ == 0)
{
lean_ctor_set(v___x_5575_, 1, v___x_5577_);
v_it_x27_5579_ = v___x_5575_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_fst_5565_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v___x_5577_);
v_it_x27_5579_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
lean_object* v___x_5580_; lean_object* v___x_5581_; 
v___x_5580_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0);
v___x_5581_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(v___x_5580_, v_it_x27_5579_);
if (lean_obj_tag(v___x_5581_) == 0)
{
lean_object* v_pos_5582_; lean_object* v_res_5583_; lean_object* v___x_5584_; 
v_pos_5582_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_pos_5582_);
v_res_5583_ = lean_ctor_get(v___x_5581_, 1);
lean_inc(v_res_5583_);
lean_dec_ref_known(v___x_5581_, 2);
v___x_5584_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(v___f_5558_, v_res_5583_, v_pos_5582_);
if (lean_obj_tag(v___x_5584_) == 0)
{
lean_dec(v_snd_5566_);
lean_dec_ref(v___y_5561_);
lean_dec_ref(v___y_5560_);
return v___x_5584_;
}
else
{
lean_object* v_pos_5585_; 
v_pos_5585_ = lean_ctor_get(v___x_5584_, 0);
lean_inc(v_pos_5585_);
v___y_5513_ = v___y_5560_;
v_snd_5514_ = v_snd_5566_;
v___y_5515_ = v___y_5561_;
v___y_5516_ = v___x_5584_;
v_pos_5517_ = v_pos_5585_;
goto v___jp_5512_;
}
}
else
{
lean_object* v_pos_5586_; lean_object* v_err_5587_; 
v_pos_5586_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_pos_5586_);
v_err_5587_ = lean_ctor_get(v___x_5581_, 1);
lean_inc(v_err_5587_);
lean_dec_ref_known(v___x_5581_, 2);
v___y_5546_ = v___y_5560_;
v_snd_5547_ = v_snd_5566_;
v___y_5548_ = v___y_5561_;
v_pos_5549_ = v_pos_5586_;
v_err_5550_ = v_err_5587_;
goto v___jp_5545_;
}
}
}
}
}
}
else
{
v___y_5553_ = v___y_5560_;
v___y_5554_ = v_pos_5564_;
v_snd_5555_ = v_snd_5566_;
v___y_5556_ = v___y_5561_;
goto v___jp_5552_;
}
}
}
v___jp_5592_:
{
lean_object* v___x_5598_; 
lean_inc_ref(v_pos_5596_);
v___x_5598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5598_, 0, v_pos_5596_);
lean_ctor_set(v___x_5598_, 1, v_err_5597_);
v___y_5560_ = v___y_5593_;
v___y_5561_ = v___y_5594_;
v_snd_5562_ = v_snd_5595_;
v___y_5563_ = v___x_5598_;
v_pos_5564_ = v_pos_5596_;
goto v___jp_5559_;
}
v___jp_5599_:
{
lean_object* v___x_5604_; 
v___x_5604_ = lean_box(0);
v___y_5593_ = v___y_5600_;
v___y_5594_ = v___y_5601_;
v_snd_5595_ = v_snd_5603_;
v_pos_5596_ = v___y_5602_;
v_err_5597_ = v___x_5604_;
goto v___jp_5592_;
}
v___jp_5606_:
{
lean_object* v_fst_5612_; lean_object* v_snd_5613_; uint8_t v___x_5614_; 
v_fst_5612_ = lean_ctor_get(v_pos_5611_, 0);
v_snd_5613_ = lean_ctor_get(v_pos_5611_, 1);
lean_inc(v_snd_5613_);
v___x_5614_ = lean_nat_dec_eq(v___y_5609_, v_snd_5613_);
lean_dec(v___y_5609_);
if (v___x_5614_ == 0)
{
lean_dec(v_snd_5613_);
lean_dec_ref(v_pos_5611_);
lean_dec_ref(v___y_5608_);
lean_dec_ref(v___y_5607_);
return v___y_5610_;
}
else
{
lean_object* v___x_5615_; uint8_t v___x_5616_; 
lean_dec_ref(v___y_5610_);
v___x_5615_ = lean_string_utf8_byte_size(v_fst_5612_);
v___x_5616_ = lean_nat_dec_eq(v_snd_5613_, v___x_5615_);
if (v___x_5616_ == 0)
{
if (v___x_5614_ == 0)
{
v___y_5600_ = v___y_5607_;
v___y_5601_ = v___y_5608_;
v___y_5602_ = v_pos_5611_;
v_snd_5603_ = v_snd_5613_;
goto v___jp_5599_;
}
else
{
uint32_t v___x_5617_; uint32_t v_c_5618_; uint8_t v___x_5619_; 
v___x_5617_ = 69;
v_c_5618_ = lean_string_utf8_get_fast(v_fst_5612_, v_snd_5613_);
v___x_5619_ = lean_uint32_dec_eq(v_c_5618_, v___x_5617_);
if (v___x_5619_ == 0)
{
lean_object* v___x_5620_; 
v___x_5620_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3);
v___y_5593_ = v___y_5607_;
v___y_5594_ = v___y_5608_;
v_snd_5595_ = v_snd_5613_;
v_pos_5596_ = v_pos_5611_;
v_err_5597_ = v___x_5620_;
goto v___jp_5592_;
}
else
{
lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5636_; 
lean_inc(v_fst_5612_);
v_isSharedCheck_5636_ = !lean_is_exclusive(v_pos_5611_);
if (v_isSharedCheck_5636_ == 0)
{
lean_object* v_unused_5637_; lean_object* v_unused_5638_; 
v_unused_5637_ = lean_ctor_get(v_pos_5611_, 1);
lean_dec(v_unused_5637_);
v_unused_5638_ = lean_ctor_get(v_pos_5611_, 0);
lean_dec(v_unused_5638_);
v___x_5622_ = v_pos_5611_;
v_isShared_5623_ = v_isSharedCheck_5636_;
goto v_resetjp_5621_;
}
else
{
lean_dec(v_pos_5611_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5636_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v___x_5624_; lean_object* v_it_x27_5626_; 
v___x_5624_ = lean_string_utf8_next_fast(v_fst_5612_, v_snd_5613_);
if (v_isShared_5623_ == 0)
{
lean_ctor_set(v___x_5622_, 1, v___x_5624_);
v_it_x27_5626_ = v___x_5622_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_fst_5612_);
lean_ctor_set(v_reuseFailAlloc_5635_, 1, v___x_5624_);
v_it_x27_5626_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
lean_object* v___x_5627_; lean_object* v___x_5628_; 
v___x_5627_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0);
v___x_5628_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(v___x_5627_, v_it_x27_5626_);
if (lean_obj_tag(v___x_5628_) == 0)
{
lean_object* v_pos_5629_; lean_object* v_res_5630_; lean_object* v___x_5631_; 
v_pos_5629_ = lean_ctor_get(v___x_5628_, 0);
lean_inc(v_pos_5629_);
v_res_5630_ = lean_ctor_get(v___x_5628_, 1);
lean_inc(v_res_5630_);
lean_dec_ref_known(v___x_5628_, 2);
v___x_5631_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(v___f_5605_, v_res_5630_, v_pos_5629_);
if (lean_obj_tag(v___x_5631_) == 0)
{
lean_dec(v_snd_5613_);
lean_dec_ref(v___y_5608_);
lean_dec_ref(v___y_5607_);
return v___x_5631_;
}
else
{
lean_object* v_pos_5632_; 
v_pos_5632_ = lean_ctor_get(v___x_5631_, 0);
lean_inc(v_pos_5632_);
v___y_5560_ = v___y_5607_;
v___y_5561_ = v___y_5608_;
v_snd_5562_ = v_snd_5613_;
v___y_5563_ = v___x_5631_;
v_pos_5564_ = v_pos_5632_;
goto v___jp_5559_;
}
}
else
{
lean_object* v_pos_5633_; lean_object* v_err_5634_; 
v_pos_5633_ = lean_ctor_get(v___x_5628_, 0);
lean_inc(v_pos_5633_);
v_err_5634_ = lean_ctor_get(v___x_5628_, 1);
lean_inc(v_err_5634_);
lean_dec_ref_known(v___x_5628_, 2);
v___y_5593_ = v___y_5607_;
v___y_5594_ = v___y_5608_;
v_snd_5595_ = v_snd_5613_;
v_pos_5596_ = v_pos_5633_;
v_err_5597_ = v_err_5634_;
goto v___jp_5592_;
}
}
}
}
}
}
else
{
v___y_5600_ = v___y_5607_;
v___y_5601_ = v___y_5608_;
v___y_5602_ = v_pos_5611_;
v_snd_5603_ = v_snd_5613_;
goto v___jp_5599_;
}
}
}
v___jp_5639_:
{
lean_object* v___x_5645_; 
lean_inc_ref(v_pos_5643_);
v___x_5645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5645_, 0, v_pos_5643_);
lean_ctor_set(v___x_5645_, 1, v_err_5644_);
v___y_5607_ = v___y_5640_;
v___y_5608_ = v___y_5641_;
v___y_5609_ = v___y_5642_;
v___y_5610_ = v___x_5645_;
v_pos_5611_ = v_pos_5643_;
goto v___jp_5606_;
}
v___jp_5646_:
{
lean_object* v___x_5651_; 
v___x_5651_ = lean_box(0);
v___y_5640_ = v___y_5647_;
v___y_5641_ = v___y_5648_;
v___y_5642_ = v___y_5649_;
v_pos_5643_ = v___y_5650_;
v_err_5644_ = v___x_5651_;
goto v___jp_5639_;
}
v___jp_5653_:
{
lean_object* v_fst_5658_; lean_object* v_snd_5659_; uint8_t v___x_5660_; 
v_fst_5658_ = lean_ctor_get(v_pos_5657_, 0);
v_snd_5659_ = lean_ctor_get(v_pos_5657_, 1);
lean_inc(v_snd_5659_);
v___x_5660_ = lean_nat_dec_eq(v_snd_5655_, v_snd_5659_);
lean_dec(v_snd_5655_);
if (v___x_5660_ == 0)
{
lean_dec(v_snd_5659_);
lean_dec_ref(v_pos_5657_);
lean_dec_ref(v___y_5654_);
return v___y_5656_;
}
else
{
lean_object* v___x_5661_; lean_object* v___x_5662_; uint8_t v___x_5663_; 
lean_dec_ref(v___y_5656_);
v___x_5661_ = ((lean_object*)(l_Std_Time_parseModifier___closed__21));
v___x_5662_ = lean_string_utf8_byte_size(v_fst_5658_);
v___x_5663_ = lean_nat_dec_eq(v_snd_5659_, v___x_5662_);
if (v___x_5663_ == 0)
{
if (v___x_5660_ == 0)
{
v___y_5647_ = v___x_5661_;
v___y_5648_ = v___y_5654_;
v___y_5649_ = v_snd_5659_;
v___y_5650_ = v_pos_5657_;
goto v___jp_5646_;
}
else
{
uint32_t v___x_5664_; uint32_t v_c_5665_; uint8_t v___x_5666_; 
v___x_5664_ = 87;
v_c_5665_ = lean_string_utf8_get_fast(v_fst_5658_, v_snd_5659_);
v___x_5666_ = lean_uint32_dec_eq(v_c_5665_, v___x_5664_);
if (v___x_5666_ == 0)
{
lean_object* v___x_5667_; 
v___x_5667_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3);
v___y_5640_ = v___x_5661_;
v___y_5641_ = v___y_5654_;
v___y_5642_ = v_snd_5659_;
v_pos_5643_ = v_pos_5657_;
v_err_5644_ = v___x_5667_;
goto v___jp_5639_;
}
else
{
lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5683_; 
lean_inc(v_fst_5658_);
v_isSharedCheck_5683_ = !lean_is_exclusive(v_pos_5657_);
if (v_isSharedCheck_5683_ == 0)
{
lean_object* v_unused_5684_; lean_object* v_unused_5685_; 
v_unused_5684_ = lean_ctor_get(v_pos_5657_, 1);
lean_dec(v_unused_5684_);
v_unused_5685_ = lean_ctor_get(v_pos_5657_, 0);
lean_dec(v_unused_5685_);
v___x_5669_ = v_pos_5657_;
v_isShared_5670_ = v_isSharedCheck_5683_;
goto v_resetjp_5668_;
}
else
{
lean_dec(v_pos_5657_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5683_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v___x_5671_; lean_object* v_it_x27_5673_; 
v___x_5671_ = lean_string_utf8_next_fast(v_fst_5658_, v_snd_5659_);
if (v_isShared_5670_ == 0)
{
lean_ctor_set(v___x_5669_, 1, v___x_5671_);
v_it_x27_5673_ = v___x_5669_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_fst_5658_);
lean_ctor_set(v_reuseFailAlloc_5682_, 1, v___x_5671_);
v_it_x27_5673_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
lean_object* v___x_5674_; lean_object* v___x_5675_; 
v___x_5674_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0);
v___x_5675_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(v___x_5674_, v_it_x27_5673_);
if (lean_obj_tag(v___x_5675_) == 0)
{
lean_object* v_pos_5676_; lean_object* v_res_5677_; lean_object* v___x_5678_; 
v_pos_5676_ = lean_ctor_get(v___x_5675_, 0);
lean_inc(v_pos_5676_);
v_res_5677_ = lean_ctor_get(v___x_5675_, 1);
lean_inc(v_res_5677_);
lean_dec_ref_known(v___x_5675_, 2);
v___x_5678_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5652_, v___x_5661_, v_res_5677_, v_pos_5676_);
if (lean_obj_tag(v___x_5678_) == 0)
{
lean_dec(v_snd_5659_);
lean_dec_ref(v___y_5654_);
return v___x_5678_;
}
else
{
lean_object* v_pos_5679_; 
v_pos_5679_ = lean_ctor_get(v___x_5678_, 0);
lean_inc(v_pos_5679_);
v___y_5607_ = v___x_5661_;
v___y_5608_ = v___y_5654_;
v___y_5609_ = v_snd_5659_;
v___y_5610_ = v___x_5678_;
v_pos_5611_ = v_pos_5679_;
goto v___jp_5606_;
}
}
else
{
lean_object* v_pos_5680_; lean_object* v_err_5681_; 
v_pos_5680_ = lean_ctor_get(v___x_5675_, 0);
lean_inc(v_pos_5680_);
v_err_5681_ = lean_ctor_get(v___x_5675_, 1);
lean_inc(v_err_5681_);
lean_dec_ref_known(v___x_5675_, 2);
v___y_5640_ = v___x_5661_;
v___y_5641_ = v___y_5654_;
v___y_5642_ = v_snd_5659_;
v_pos_5643_ = v_pos_5680_;
v_err_5644_ = v_err_5681_;
goto v___jp_5639_;
}
}
}
}
}
}
else
{
v___y_5647_ = v___x_5661_;
v___y_5648_ = v___y_5654_;
v___y_5649_ = v_snd_5659_;
v___y_5650_ = v_pos_5657_;
goto v___jp_5646_;
}
}
}
v___jp_5686_:
{
lean_object* v___x_5691_; 
lean_inc_ref(v_pos_5689_);
v___x_5691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5691_, 0, v_pos_5689_);
lean_ctor_set(v___x_5691_, 1, v_err_5690_);
v___y_5654_ = v___y_5688_;
v_snd_5655_ = v_snd_5687_;
v___y_5656_ = v___x_5691_;
v_pos_5657_ = v_pos_5689_;
goto v___jp_5653_;
}
v___jp_5692_:
{
lean_object* v___x_5696_; 
v___x_5696_ = lean_box(0);
v_snd_5687_ = v_snd_5695_;
v___y_5688_ = v___y_5693_;
v_pos_5689_ = v___y_5694_;
v_err_5690_ = v___x_5696_;
goto v___jp_5686_;
}
v___jp_5698_:
{
lean_object* v_fst_5703_; lean_object* v_snd_5704_; uint8_t v___x_5705_; 
v_fst_5703_ = lean_ctor_get(v_pos_5702_, 0);
v_snd_5704_ = lean_ctor_get(v_pos_5702_, 1);
lean_inc(v_snd_5704_);
v___x_5705_ = lean_nat_dec_eq(v_snd_5700_, v_snd_5704_);
lean_dec(v_snd_5700_);
if (v___x_5705_ == 0)
{
lean_dec(v_snd_5704_);
lean_dec_ref(v_pos_5702_);
lean_dec_ref(v___y_5699_);
return v___y_5701_;
}
else
{
lean_object* v___x_5706_; uint8_t v___x_5707_; 
lean_dec_ref(v___y_5701_);
v___x_5706_ = lean_string_utf8_byte_size(v_fst_5703_);
v___x_5707_ = lean_nat_dec_eq(v_snd_5704_, v___x_5706_);
if (v___x_5707_ == 0)
{
if (v___x_5705_ == 0)
{
v___y_5693_ = v___y_5699_;
v___y_5694_ = v_pos_5702_;
v_snd_5695_ = v_snd_5704_;
goto v___jp_5692_;
}
else
{
uint32_t v___x_5708_; uint32_t v_c_5709_; uint8_t v___x_5710_; 
v___x_5708_ = 119;
v_c_5709_ = lean_string_utf8_get_fast(v_fst_5703_, v_snd_5704_);
v___x_5710_ = lean_uint32_dec_eq(v_c_5709_, v___x_5708_);
if (v___x_5710_ == 0)
{
lean_object* v___x_5711_; 
v___x_5711_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3);
v_snd_5687_ = v_snd_5704_;
v___y_5688_ = v___y_5699_;
v_pos_5689_ = v_pos_5702_;
v_err_5690_ = v___x_5711_;
goto v___jp_5686_;
}
else
{
lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5727_; 
lean_inc(v_fst_5703_);
v_isSharedCheck_5727_ = !lean_is_exclusive(v_pos_5702_);
if (v_isSharedCheck_5727_ == 0)
{
lean_object* v_unused_5728_; lean_object* v_unused_5729_; 
v_unused_5728_ = lean_ctor_get(v_pos_5702_, 1);
lean_dec(v_unused_5728_);
v_unused_5729_ = lean_ctor_get(v_pos_5702_, 0);
lean_dec(v_unused_5729_);
v___x_5713_ = v_pos_5702_;
v_isShared_5714_ = v_isSharedCheck_5727_;
goto v_resetjp_5712_;
}
else
{
lean_dec(v_pos_5702_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5727_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v___x_5715_; lean_object* v_it_x27_5717_; 
v___x_5715_ = lean_string_utf8_next_fast(v_fst_5703_, v_snd_5704_);
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 1, v___x_5715_);
v_it_x27_5717_ = v___x_5713_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_fst_5703_);
lean_ctor_set(v_reuseFailAlloc_5726_, 1, v___x_5715_);
v_it_x27_5717_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
lean_object* v___x_5718_; lean_object* v___x_5719_; 
v___x_5718_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0);
v___x_5719_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(v___x_5718_, v_it_x27_5717_);
if (lean_obj_tag(v___x_5719_) == 0)
{
lean_object* v_pos_5720_; lean_object* v_res_5721_; lean_object* v___x_5722_; 
v_pos_5720_ = lean_ctor_get(v___x_5719_, 0);
lean_inc(v_pos_5720_);
v_res_5721_ = lean_ctor_get(v___x_5719_, 1);
lean_inc(v_res_5721_);
lean_dec_ref_known(v___x_5719_, 2);
lean_inc_ref(v___y_5699_);
v___x_5722_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5697_, v___y_5699_, v_res_5721_, v_pos_5720_);
if (lean_obj_tag(v___x_5722_) == 0)
{
lean_dec(v_snd_5704_);
lean_dec_ref(v___y_5699_);
return v___x_5722_;
}
else
{
lean_object* v_pos_5723_; 
v_pos_5723_ = lean_ctor_get(v___x_5722_, 0);
lean_inc(v_pos_5723_);
v___y_5654_ = v___y_5699_;
v_snd_5655_ = v_snd_5704_;
v___y_5656_ = v___x_5722_;
v_pos_5657_ = v_pos_5723_;
goto v___jp_5653_;
}
}
else
{
lean_object* v_pos_5724_; lean_object* v_err_5725_; 
v_pos_5724_ = lean_ctor_get(v___x_5719_, 0);
lean_inc(v_pos_5724_);
v_err_5725_ = lean_ctor_get(v___x_5719_, 1);
lean_inc(v_err_5725_);
lean_dec_ref_known(v___x_5719_, 2);
v_snd_5687_ = v_snd_5704_;
v___y_5688_ = v___y_5699_;
v_pos_5689_ = v_pos_5724_;
v_err_5690_ = v_err_5725_;
goto v___jp_5686_;
}
}
}
}
}
}
else
{
v___y_5693_ = v___y_5699_;
v___y_5694_ = v_pos_5702_;
v_snd_5695_ = v_snd_5704_;
goto v___jp_5692_;
}
}
}
v___jp_5730_:
{
lean_object* v___x_5735_; 
lean_inc_ref(v_pos_5733_);
v___x_5735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5735_, 0, v_pos_5733_);
lean_ctor_set(v___x_5735_, 1, v_err_5734_);
v___y_5699_ = v___y_5731_;
v_snd_5700_ = v_snd_5732_;
v___y_5701_ = v___x_5735_;
v_pos_5702_ = v_pos_5733_;
goto v___jp_5698_;
}
v___jp_5736_:
{
lean_object* v___x_5740_; 
v___x_5740_ = lean_box(0);
v___y_5731_ = v___y_5737_;
v_snd_5732_ = v_snd_5739_;
v_pos_5733_ = v___y_5738_;
v_err_5734_ = v___x_5740_;
goto v___jp_5730_;
}
v___jp_5742_:
{
lean_object* v_fst_5747_; lean_object* v_snd_5748_; uint8_t v___x_5749_; 
v_fst_5747_ = lean_ctor_get(v_pos_5746_, 0);
v_snd_5748_ = lean_ctor_get(v_pos_5746_, 1);
lean_inc(v_snd_5748_);
v___x_5749_ = lean_nat_dec_eq(v_snd_5744_, v_snd_5748_);
lean_dec(v_snd_5744_);
if (v___x_5749_ == 0)
{
lean_dec(v_snd_5748_);
lean_dec_ref(v_pos_5746_);
lean_dec_ref(v___y_5743_);
return v___y_5745_;
}
else
{
lean_object* v___x_5750_; uint8_t v___x_5751_; 
lean_dec_ref(v___y_5745_);
v___x_5750_ = lean_string_utf8_byte_size(v_fst_5747_);
v___x_5751_ = lean_nat_dec_eq(v_snd_5748_, v___x_5750_);
if (v___x_5751_ == 0)
{
if (v___x_5749_ == 0)
{
v___y_5737_ = v___y_5743_;
v___y_5738_ = v_pos_5746_;
v_snd_5739_ = v_snd_5748_;
goto v___jp_5736_;
}
else
{
uint32_t v___x_5752_; uint32_t v_c_5753_; uint8_t v___x_5754_; 
v___x_5752_ = 113;
v_c_5753_ = lean_string_utf8_get_fast(v_fst_5747_, v_snd_5748_);
v___x_5754_ = lean_uint32_dec_eq(v_c_5753_, v___x_5752_);
if (v___x_5754_ == 0)
{
lean_object* v___x_5755_; 
v___x_5755_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3);
v___y_5731_ = v___y_5743_;
v_snd_5732_ = v_snd_5748_;
v_pos_5733_ = v_pos_5746_;
v_err_5734_ = v___x_5755_;
goto v___jp_5730_;
}
else
{
lean_object* v___x_5757_; uint8_t v_isShared_5758_; uint8_t v_isSharedCheck_5771_; 
lean_inc(v_fst_5747_);
v_isSharedCheck_5771_ = !lean_is_exclusive(v_pos_5746_);
if (v_isSharedCheck_5771_ == 0)
{
lean_object* v_unused_5772_; lean_object* v_unused_5773_; 
v_unused_5772_ = lean_ctor_get(v_pos_5746_, 1);
lean_dec(v_unused_5772_);
v_unused_5773_ = lean_ctor_get(v_pos_5746_, 0);
lean_dec(v_unused_5773_);
v___x_5757_ = v_pos_5746_;
v_isShared_5758_ = v_isSharedCheck_5771_;
goto v_resetjp_5756_;
}
else
{
lean_dec(v_pos_5746_);
v___x_5757_ = lean_box(0);
v_isShared_5758_ = v_isSharedCheck_5771_;
goto v_resetjp_5756_;
}
v_resetjp_5756_:
{
lean_object* v___x_5759_; lean_object* v_it_x27_5761_; 
v___x_5759_ = lean_string_utf8_next_fast(v_fst_5747_, v_snd_5748_);
if (v_isShared_5758_ == 0)
{
lean_ctor_set(v___x_5757_, 1, v___x_5759_);
v_it_x27_5761_ = v___x_5757_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v_fst_5747_);
lean_ctor_set(v_reuseFailAlloc_5770_, 1, v___x_5759_);
v_it_x27_5761_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
lean_object* v___x_5762_; lean_object* v___x_5763_; 
v___x_5762_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0);
v___x_5763_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(v___x_5762_, v_it_x27_5761_);
if (lean_obj_tag(v___x_5763_) == 0)
{
lean_object* v_pos_5764_; lean_object* v_res_5765_; lean_object* v___x_5766_; 
v_pos_5764_ = lean_ctor_get(v___x_5763_, 0);
lean_inc(v_pos_5764_);
v_res_5765_ = lean_ctor_get(v___x_5763_, 1);
lean_inc(v_res_5765_);
lean_dec_ref_known(v___x_5763_, 2);
v___x_5766_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5741_, v_res_5765_, v_pos_5764_);
if (lean_obj_tag(v___x_5766_) == 0)
{
lean_dec(v_snd_5748_);
lean_dec_ref(v___y_5743_);
return v___x_5766_;
}
else
{
lean_object* v_pos_5767_; 
v_pos_5767_ = lean_ctor_get(v___x_5766_, 0);
lean_inc(v_pos_5767_);
v___y_5699_ = v___y_5743_;
v_snd_5700_ = v_snd_5748_;
v___y_5701_ = v___x_5766_;
v_pos_5702_ = v_pos_5767_;
goto v___jp_5698_;
}
}
else
{
lean_object* v_pos_5768_; lean_object* v_err_5769_; 
v_pos_5768_ = lean_ctor_get(v___x_5763_, 0);
lean_inc(v_pos_5768_);
v_err_5769_ = lean_ctor_get(v___x_5763_, 1);
lean_inc(v_err_5769_);
lean_dec_ref_known(v___x_5763_, 2);
v___y_5731_ = v___y_5743_;
v_snd_5732_ = v_snd_5748_;
v_pos_5733_ = v_pos_5768_;
v_err_5734_ = v_err_5769_;
goto v___jp_5730_;
}
}
}
}
}
}
else
{
v___y_5737_ = v___y_5743_;
v___y_5738_ = v_pos_5746_;
v_snd_5739_ = v_snd_5748_;
goto v___jp_5736_;
}
}
}
v___jp_5774_:
{
lean_object* v___x_5779_; 
lean_inc_ref(v_pos_5777_);
v___x_5779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5779_, 0, v_pos_5777_);
lean_ctor_set(v___x_5779_, 1, v_err_5778_);
v___y_5743_ = v___y_5775_;
v_snd_5744_ = v_snd_5776_;
v___y_5745_ = v___x_5779_;
v_pos_5746_ = v_pos_5777_;
goto v___jp_5742_;
}
v___jp_5780_:
{
lean_object* v___x_5784_; 
v___x_5784_ = lean_box(0);
v___y_5775_ = v___y_5781_;
v_snd_5776_ = v_snd_5783_;
v_pos_5777_ = v___y_5782_;
v_err_5778_ = v___x_5784_;
goto v___jp_5774_;
}
v___jp_5786_:
{
lean_object* v_fst_5791_; lean_object* v_snd_5792_; uint8_t v___x_5793_; 
v_fst_5791_ = lean_ctor_get(v_pos_5790_, 0);
v_snd_5792_ = lean_ctor_get(v_pos_5790_, 1);
lean_inc(v_snd_5792_);
v___x_5793_ = lean_nat_dec_eq(v___y_5788_, v_snd_5792_);
lean_dec(v___y_5788_);
if (v___x_5793_ == 0)
{
lean_dec(v_snd_5792_);
lean_dec_ref(v_pos_5790_);
lean_dec_ref(v___y_5787_);
return v___y_5789_;
}
else
{
lean_object* v___x_5794_; uint8_t v___x_5795_; 
lean_dec_ref(v___y_5789_);
v___x_5794_ = lean_string_utf8_byte_size(v_fst_5791_);
v___x_5795_ = lean_nat_dec_eq(v_snd_5792_, v___x_5794_);
if (v___x_5795_ == 0)
{
if (v___x_5793_ == 0)
{
v___y_5781_ = v___y_5787_;
v___y_5782_ = v_pos_5790_;
v_snd_5783_ = v_snd_5792_;
goto v___jp_5780_;
}
else
{
uint32_t v___x_5796_; uint32_t v_c_5797_; uint8_t v___x_5798_; 
v___x_5796_ = 81;
v_c_5797_ = lean_string_utf8_get_fast(v_fst_5791_, v_snd_5792_);
v___x_5798_ = lean_uint32_dec_eq(v_c_5797_, v___x_5796_);
if (v___x_5798_ == 0)
{
lean_object* v___x_5799_; 
v___x_5799_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3);
v___y_5775_ = v___y_5787_;
v_snd_5776_ = v_snd_5792_;
v_pos_5777_ = v_pos_5790_;
v_err_5778_ = v___x_5799_;
goto v___jp_5774_;
}
else
{
lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5815_; 
lean_inc(v_fst_5791_);
v_isSharedCheck_5815_ = !lean_is_exclusive(v_pos_5790_);
if (v_isSharedCheck_5815_ == 0)
{
lean_object* v_unused_5816_; lean_object* v_unused_5817_; 
v_unused_5816_ = lean_ctor_get(v_pos_5790_, 1);
lean_dec(v_unused_5816_);
v_unused_5817_ = lean_ctor_get(v_pos_5790_, 0);
lean_dec(v_unused_5817_);
v___x_5801_ = v_pos_5790_;
v_isShared_5802_ = v_isSharedCheck_5815_;
goto v_resetjp_5800_;
}
else
{
lean_dec(v_pos_5790_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5815_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v___x_5803_; lean_object* v_it_x27_5805_; 
v___x_5803_ = lean_string_utf8_next_fast(v_fst_5791_, v_snd_5792_);
if (v_isShared_5802_ == 0)
{
lean_ctor_set(v___x_5801_, 1, v___x_5803_);
v_it_x27_5805_ = v___x_5801_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5814_; 
v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5814_, 0, v_fst_5791_);
lean_ctor_set(v_reuseFailAlloc_5814_, 1, v___x_5803_);
v_it_x27_5805_ = v_reuseFailAlloc_5814_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
lean_object* v___x_5806_; lean_object* v___x_5807_; 
v___x_5806_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0);
v___x_5807_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(v___x_5806_, v_it_x27_5805_);
if (lean_obj_tag(v___x_5807_) == 0)
{
lean_object* v_pos_5808_; lean_object* v_res_5809_; lean_object* v___x_5810_; 
v_pos_5808_ = lean_ctor_get(v___x_5807_, 0);
lean_inc(v_pos_5808_);
v_res_5809_ = lean_ctor_get(v___x_5807_, 1);
lean_inc(v_res_5809_);
lean_dec_ref_known(v___x_5807_, 2);
v___x_5810_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5785_, v_res_5809_, v_pos_5808_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_dec(v_snd_5792_);
lean_dec_ref(v___y_5787_);
return v___x_5810_;
}
else
{
lean_object* v_pos_5811_; 
v_pos_5811_ = lean_ctor_get(v___x_5810_, 0);
lean_inc(v_pos_5811_);
v___y_5743_ = v___y_5787_;
v_snd_5744_ = v_snd_5792_;
v___y_5745_ = v___x_5810_;
v_pos_5746_ = v_pos_5811_;
goto v___jp_5742_;
}
}
else
{
lean_object* v_pos_5812_; lean_object* v_err_5813_; 
v_pos_5812_ = lean_ctor_get(v___x_5807_, 0);
lean_inc(v_pos_5812_);
v_err_5813_ = lean_ctor_get(v___x_5807_, 1);
lean_inc(v_err_5813_);
lean_dec_ref_known(v___x_5807_, 2);
v___y_5775_ = v___y_5787_;
v_snd_5776_ = v_snd_5792_;
v_pos_5777_ = v_pos_5812_;
v_err_5778_ = v_err_5813_;
goto v___jp_5774_;
}
}
}
}
}
}
else
{
v___y_5781_ = v___y_5787_;
v___y_5782_ = v_pos_5790_;
v_snd_5783_ = v_snd_5792_;
goto v___jp_5780_;
}
}
}
v___jp_5818_:
{
lean_object* v___x_5823_; 
lean_inc_ref(v_pos_5821_);
v___x_5823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5823_, 0, v_pos_5821_);
lean_ctor_set(v___x_5823_, 1, v_err_5822_);
v___y_5787_ = v___y_5819_;
v___y_5788_ = v___y_5820_;
v___y_5789_ = v___x_5823_;
v_pos_5790_ = v_pos_5821_;
goto v___jp_5786_;
}
v___jp_5824_:
{
lean_object* v___x_5828_; 
v___x_5828_ = lean_box(0);
v___y_5819_ = v___y_5826_;
v___y_5820_ = v___y_5827_;
v_pos_5821_ = v___y_5825_;
v_err_5822_ = v___x_5828_;
goto v___jp_5818_;
}
v___jp_5830_:
{
lean_object* v_fst_5834_; lean_object* v_snd_5835_; uint8_t v___x_5836_; 
v_fst_5834_ = lean_ctor_get(v_pos_5833_, 0);
v_snd_5835_ = lean_ctor_get(v_pos_5833_, 1);
lean_inc(v_snd_5835_);
v___x_5836_ = lean_nat_dec_eq(v_snd_5831_, v_snd_5835_);
lean_dec(v_snd_5831_);
if (v___x_5836_ == 0)
{
lean_dec(v_snd_5835_);
lean_dec_ref(v_pos_5833_);
return v___y_5832_;
}
else
{
lean_object* v___x_5837_; lean_object* v___x_5838_; uint8_t v___x_5839_; 
lean_dec_ref(v___y_5832_);
v___x_5837_ = ((lean_object*)(l_Std_Time_parseModifier___closed__26));
v___x_5838_ = lean_string_utf8_byte_size(v_fst_5834_);
v___x_5839_ = lean_nat_dec_eq(v_snd_5835_, v___x_5838_);
if (v___x_5839_ == 0)
{
if (v___x_5836_ == 0)
{
v___y_5825_ = v_pos_5833_;
v___y_5826_ = v___x_5837_;
v___y_5827_ = v_snd_5835_;
goto v___jp_5824_;
}
else
{
uint32_t v___x_5840_; uint32_t v_c_5841_; uint8_t v___x_5842_; 
v___x_5840_ = 100;
v_c_5841_ = lean_string_utf8_get_fast(v_fst_5834_, v_snd_5835_);
v___x_5842_ = lean_uint32_dec_eq(v_c_5841_, v___x_5840_);
if (v___x_5842_ == 0)
{
lean_object* v___x_5843_; 
v___x_5843_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3);
v___y_5819_ = v___x_5837_;
v___y_5820_ = v_snd_5835_;
v_pos_5821_ = v_pos_5833_;
v_err_5822_ = v___x_5843_;
goto v___jp_5818_;
}
else
{
lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5859_; 
lean_inc(v_fst_5834_);
v_isSharedCheck_5859_ = !lean_is_exclusive(v_pos_5833_);
if (v_isSharedCheck_5859_ == 0)
{
lean_object* v_unused_5860_; lean_object* v_unused_5861_; 
v_unused_5860_ = lean_ctor_get(v_pos_5833_, 1);
lean_dec(v_unused_5860_);
v_unused_5861_ = lean_ctor_get(v_pos_5833_, 0);
lean_dec(v_unused_5861_);
v___x_5845_ = v_pos_5833_;
v_isShared_5846_ = v_isSharedCheck_5859_;
goto v_resetjp_5844_;
}
else
{
lean_dec(v_pos_5833_);
v___x_5845_ = lean_box(0);
v_isShared_5846_ = v_isSharedCheck_5859_;
goto v_resetjp_5844_;
}
v_resetjp_5844_:
{
lean_object* v___x_5847_; lean_object* v_it_x27_5849_; 
v___x_5847_ = lean_string_utf8_next_fast(v_fst_5834_, v_snd_5835_);
if (v_isShared_5846_ == 0)
{
lean_ctor_set(v___x_5845_, 1, v___x_5847_);
v_it_x27_5849_ = v___x_5845_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_fst_5834_);
lean_ctor_set(v_reuseFailAlloc_5858_, 1, v___x_5847_);
v_it_x27_5849_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___x_5850_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0);
v___x_5851_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(v___x_5850_, v_it_x27_5849_);
if (lean_obj_tag(v___x_5851_) == 0)
{
lean_object* v_pos_5852_; lean_object* v_res_5853_; lean_object* v___x_5854_; 
v_pos_5852_ = lean_ctor_get(v___x_5851_, 0);
lean_inc(v_pos_5852_);
v_res_5853_ = lean_ctor_get(v___x_5851_, 1);
lean_inc(v_res_5853_);
lean_dec_ref_known(v___x_5851_, 2);
v___x_5854_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5829_, v___x_5837_, v_res_5853_, v_pos_5852_);
if (lean_obj_tag(v___x_5854_) == 0)
{
lean_dec(v_snd_5835_);
return v___x_5854_;
}
else
{
lean_object* v_pos_5855_; 
v_pos_5855_ = lean_ctor_get(v___x_5854_, 0);
lean_inc(v_pos_5855_);
v___y_5787_ = v___x_5837_;
v___y_5788_ = v_snd_5835_;
v___y_5789_ = v___x_5854_;
v_pos_5790_ = v_pos_5855_;
goto v___jp_5786_;
}
}
else
{
lean_object* v_pos_5856_; lean_object* v_err_5857_; 
v_pos_5856_ = lean_ctor_get(v___x_5851_, 0);
lean_inc(v_pos_5856_);
v_err_5857_ = lean_ctor_get(v___x_5851_, 1);
lean_inc(v_err_5857_);
lean_dec_ref_known(v___x_5851_, 2);
v___y_5819_ = v___x_5837_;
v___y_5820_ = v_snd_5835_;
v_pos_5821_ = v_pos_5856_;
v_err_5822_ = v_err_5857_;
goto v___jp_5818_;
}
}
}
}
}
}
else
{
v___y_5825_ = v_pos_5833_;
v___y_5826_ = v___x_5837_;
v___y_5827_ = v_snd_5835_;
goto v___jp_5824_;
}
}
}
v___jp_5862_:
{
lean_object* v___x_5866_; 
lean_inc_ref(v_pos_5864_);
v___x_5866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5866_, 0, v_pos_5864_);
lean_ctor_set(v___x_5866_, 1, v_err_5865_);
v_snd_5831_ = v_snd_5863_;
v___y_5832_ = v___x_5866_;
v_pos_5833_ = v_pos_5864_;
goto v___jp_5830_;
}
v___jp_5867_:
{
lean_object* v___x_5870_; 
v___x_5870_ = lean_box(0);
v_snd_5863_ = v_snd_5869_;
v_pos_5864_ = v___y_5868_;
v_err_5865_ = v___x_5870_;
goto v___jp_5862_;
}
v___jp_5872_:
{
lean_object* v_fst_5876_; lean_object* v_snd_5877_; uint8_t v___x_5878_; 
v_fst_5876_ = lean_ctor_get(v_pos_5875_, 0);
v_snd_5877_ = lean_ctor_get(v_pos_5875_, 1);
lean_inc(v_snd_5877_);
v___x_5878_ = lean_nat_dec_eq(v_snd_5873_, v_snd_5877_);
lean_dec(v_snd_5873_);
if (v___x_5878_ == 0)
{
lean_dec(v_snd_5877_);
lean_dec_ref(v_pos_5875_);
return v___y_5874_;
}
else
{
lean_object* v___x_5879_; uint8_t v___x_5880_; 
lean_dec_ref(v___y_5874_);
v___x_5879_ = lean_string_utf8_byte_size(v_fst_5876_);
v___x_5880_ = lean_nat_dec_eq(v_snd_5877_, v___x_5879_);
if (v___x_5880_ == 0)
{
if (v___x_5878_ == 0)
{
v___y_5868_ = v_pos_5875_;
v_snd_5869_ = v_snd_5877_;
goto v___jp_5867_;
}
else
{
uint32_t v___x_5881_; uint32_t v_c_5882_; uint8_t v___x_5883_; 
v___x_5881_ = 76;
v_c_5882_ = lean_string_utf8_get_fast(v_fst_5876_, v_snd_5877_);
v___x_5883_ = lean_uint32_dec_eq(v_c_5882_, v___x_5881_);
if (v___x_5883_ == 0)
{
lean_object* v___x_5884_; 
v___x_5884_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3);
v_snd_5863_ = v_snd_5877_;
v_pos_5864_ = v_pos_5875_;
v_err_5865_ = v___x_5884_;
goto v___jp_5862_;
}
else
{
lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5900_; 
lean_inc(v_fst_5876_);
v_isSharedCheck_5900_ = !lean_is_exclusive(v_pos_5875_);
if (v_isSharedCheck_5900_ == 0)
{
lean_object* v_unused_5901_; lean_object* v_unused_5902_; 
v_unused_5901_ = lean_ctor_get(v_pos_5875_, 1);
lean_dec(v_unused_5901_);
v_unused_5902_ = lean_ctor_get(v_pos_5875_, 0);
lean_dec(v_unused_5902_);
v___x_5886_ = v_pos_5875_;
v_isShared_5887_ = v_isSharedCheck_5900_;
goto v_resetjp_5885_;
}
else
{
lean_dec(v_pos_5875_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5900_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___x_5888_; lean_object* v_it_x27_5890_; 
v___x_5888_ = lean_string_utf8_next_fast(v_fst_5876_, v_snd_5877_);
if (v_isShared_5887_ == 0)
{
lean_ctor_set(v___x_5886_, 1, v___x_5888_);
v_it_x27_5890_ = v___x_5886_;
goto v_reusejp_5889_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v_fst_5876_);
lean_ctor_set(v_reuseFailAlloc_5899_, 1, v___x_5888_);
v_it_x27_5890_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5889_;
}
v_reusejp_5889_:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; 
v___x_5891_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0);
v___x_5892_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(v___x_5891_, v_it_x27_5890_);
if (lean_obj_tag(v___x_5892_) == 0)
{
lean_object* v_pos_5893_; lean_object* v_res_5894_; lean_object* v___x_5895_; 
v_pos_5893_ = lean_ctor_get(v___x_5892_, 0);
lean_inc(v_pos_5893_);
v_res_5894_ = lean_ctor_get(v___x_5892_, 1);
lean_inc(v_res_5894_);
lean_dec_ref_known(v___x_5892_, 2);
v___x_5895_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5871_, v_res_5894_, v_pos_5893_);
if (lean_obj_tag(v___x_5895_) == 0)
{
lean_dec(v_snd_5877_);
return v___x_5895_;
}
else
{
lean_object* v_pos_5896_; 
v_pos_5896_ = lean_ctor_get(v___x_5895_, 0);
lean_inc(v_pos_5896_);
v_snd_5831_ = v_snd_5877_;
v___y_5832_ = v___x_5895_;
v_pos_5833_ = v_pos_5896_;
goto v___jp_5830_;
}
}
else
{
lean_object* v_pos_5897_; lean_object* v_err_5898_; 
v_pos_5897_ = lean_ctor_get(v___x_5892_, 0);
lean_inc(v_pos_5897_);
v_err_5898_ = lean_ctor_get(v___x_5892_, 1);
lean_inc(v_err_5898_);
lean_dec_ref_known(v___x_5892_, 2);
v_snd_5863_ = v_snd_5877_;
v_pos_5864_ = v_pos_5897_;
v_err_5865_ = v_err_5898_;
goto v___jp_5862_;
}
}
}
}
}
}
else
{
v___y_5868_ = v_pos_5875_;
v_snd_5869_ = v_snd_5877_;
goto v___jp_5867_;
}
}
}
v___jp_5903_:
{
lean_object* v___x_5907_; 
lean_inc_ref(v_pos_5905_);
v___x_5907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5907_, 0, v_pos_5905_);
lean_ctor_set(v___x_5907_, 1, v_err_5906_);
v_snd_5873_ = v_snd_5904_;
v___y_5874_ = v___x_5907_;
v_pos_5875_ = v_pos_5905_;
goto v___jp_5872_;
}
v___jp_5908_:
{
lean_object* v___x_5911_; 
v___x_5911_ = lean_box(0);
v_snd_5904_ = v_snd_5910_;
v_pos_5905_ = v___y_5909_;
v_err_5906_ = v___x_5911_;
goto v___jp_5903_;
}
v___jp_5913_:
{
lean_object* v_fst_5917_; lean_object* v_snd_5918_; uint8_t v___x_5919_; 
v_fst_5917_ = lean_ctor_get(v_pos_5916_, 0);
v_snd_5918_ = lean_ctor_get(v_pos_5916_, 1);
lean_inc(v_snd_5918_);
v___x_5919_ = lean_nat_dec_eq(v_snd_5914_, v_snd_5918_);
lean_dec(v_snd_5914_);
if (v___x_5919_ == 0)
{
lean_dec(v_snd_5918_);
lean_dec_ref(v_pos_5916_);
return v___y_5915_;
}
else
{
lean_object* v___x_5920_; uint8_t v___x_5921_; 
lean_dec_ref(v___y_5915_);
v___x_5920_ = lean_string_utf8_byte_size(v_fst_5917_);
v___x_5921_ = lean_nat_dec_eq(v_snd_5918_, v___x_5920_);
if (v___x_5921_ == 0)
{
if (v___x_5919_ == 0)
{
v___y_5909_ = v_pos_5916_;
v_snd_5910_ = v_snd_5918_;
goto v___jp_5908_;
}
else
{
uint32_t v___x_5922_; uint32_t v_c_5923_; uint8_t v___x_5924_; 
v___x_5922_ = 77;
v_c_5923_ = lean_string_utf8_get_fast(v_fst_5917_, v_snd_5918_);
v___x_5924_ = lean_uint32_dec_eq(v_c_5923_, v___x_5922_);
if (v___x_5924_ == 0)
{
lean_object* v___x_5925_; 
v___x_5925_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3);
v_snd_5904_ = v_snd_5918_;
v_pos_5905_ = v_pos_5916_;
v_err_5906_ = v___x_5925_;
goto v___jp_5903_;
}
else
{
lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_5941_; 
lean_inc(v_fst_5917_);
v_isSharedCheck_5941_ = !lean_is_exclusive(v_pos_5916_);
if (v_isSharedCheck_5941_ == 0)
{
lean_object* v_unused_5942_; lean_object* v_unused_5943_; 
v_unused_5942_ = lean_ctor_get(v_pos_5916_, 1);
lean_dec(v_unused_5942_);
v_unused_5943_ = lean_ctor_get(v_pos_5916_, 0);
lean_dec(v_unused_5943_);
v___x_5927_ = v_pos_5916_;
v_isShared_5928_ = v_isSharedCheck_5941_;
goto v_resetjp_5926_;
}
else
{
lean_dec(v_pos_5916_);
v___x_5927_ = lean_box(0);
v_isShared_5928_ = v_isSharedCheck_5941_;
goto v_resetjp_5926_;
}
v_resetjp_5926_:
{
lean_object* v___x_5929_; lean_object* v_it_x27_5931_; 
v___x_5929_ = lean_string_utf8_next_fast(v_fst_5917_, v_snd_5918_);
if (v_isShared_5928_ == 0)
{
lean_ctor_set(v___x_5927_, 1, v___x_5929_);
v_it_x27_5931_ = v___x_5927_;
goto v_reusejp_5930_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_fst_5917_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v___x_5929_);
v_it_x27_5931_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5930_;
}
v_reusejp_5930_:
{
lean_object* v___x_5932_; lean_object* v___x_5933_; 
v___x_5932_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0);
v___x_5933_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(v___x_5932_, v_it_x27_5931_);
if (lean_obj_tag(v___x_5933_) == 0)
{
lean_object* v_pos_5934_; lean_object* v_res_5935_; lean_object* v___x_5936_; 
v_pos_5934_ = lean_ctor_get(v___x_5933_, 0);
lean_inc(v_pos_5934_);
v_res_5935_ = lean_ctor_get(v___x_5933_, 1);
lean_inc(v_res_5935_);
lean_dec_ref_known(v___x_5933_, 2);
v___x_5936_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5912_, v_res_5935_, v_pos_5934_);
if (lean_obj_tag(v___x_5936_) == 0)
{
lean_dec(v_snd_5918_);
return v___x_5936_;
}
else
{
lean_object* v_pos_5937_; 
v_pos_5937_ = lean_ctor_get(v___x_5936_, 0);
lean_inc(v_pos_5937_);
v_snd_5873_ = v_snd_5918_;
v___y_5874_ = v___x_5936_;
v_pos_5875_ = v_pos_5937_;
goto v___jp_5872_;
}
}
else
{
lean_object* v_pos_5938_; lean_object* v_err_5939_; 
v_pos_5938_ = lean_ctor_get(v___x_5933_, 0);
lean_inc(v_pos_5938_);
v_err_5939_ = lean_ctor_get(v___x_5933_, 1);
lean_inc(v_err_5939_);
lean_dec_ref_known(v___x_5933_, 2);
v_snd_5904_ = v_snd_5918_;
v_pos_5905_ = v_pos_5938_;
v_err_5906_ = v_err_5939_;
goto v___jp_5903_;
}
}
}
}
}
}
else
{
v___y_5909_ = v_pos_5916_;
v_snd_5910_ = v_snd_5918_;
goto v___jp_5908_;
}
}
}
v___jp_5944_:
{
lean_object* v___x_5948_; 
lean_inc_ref(v_pos_5946_);
v___x_5948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5948_, 0, v_pos_5946_);
lean_ctor_set(v___x_5948_, 1, v_err_5947_);
v_snd_5914_ = v_snd_5945_;
v___y_5915_ = v___x_5948_;
v_pos_5916_ = v_pos_5946_;
goto v___jp_5913_;
}
v___jp_5949_:
{
lean_object* v___x_5952_; 
v___x_5952_ = lean_box(0);
v_snd_5945_ = v_snd_5951_;
v_pos_5946_ = v___y_5950_;
v_err_5947_ = v___x_5952_;
goto v___jp_5944_;
}
v___jp_5954_:
{
lean_object* v_fst_5958_; lean_object* v_snd_5959_; uint8_t v___x_5960_; 
v_fst_5958_ = lean_ctor_get(v_pos_5957_, 0);
v_snd_5959_ = lean_ctor_get(v_pos_5957_, 1);
lean_inc(v_snd_5959_);
v___x_5960_ = lean_nat_dec_eq(v_snd_5955_, v_snd_5959_);
lean_dec(v_snd_5955_);
if (v___x_5960_ == 0)
{
lean_dec(v_snd_5959_);
lean_dec_ref(v_pos_5957_);
return v___y_5956_;
}
else
{
lean_object* v___x_5961_; uint8_t v___x_5962_; 
lean_dec_ref(v___y_5956_);
v___x_5961_ = lean_string_utf8_byte_size(v_fst_5958_);
v___x_5962_ = lean_nat_dec_eq(v_snd_5959_, v___x_5961_);
if (v___x_5962_ == 0)
{
if (v___x_5960_ == 0)
{
v___y_5950_ = v_pos_5957_;
v_snd_5951_ = v_snd_5959_;
goto v___jp_5949_;
}
else
{
uint32_t v___x_5963_; uint32_t v_c_5964_; uint8_t v___x_5965_; 
v___x_5963_ = 68;
v_c_5964_ = lean_string_utf8_get_fast(v_fst_5958_, v_snd_5959_);
v___x_5965_ = lean_uint32_dec_eq(v_c_5964_, v___x_5963_);
if (v___x_5965_ == 0)
{
lean_object* v___x_5966_; 
v___x_5966_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3);
v_snd_5945_ = v_snd_5959_;
v_pos_5946_ = v_pos_5957_;
v_err_5947_ = v___x_5966_;
goto v___jp_5944_;
}
else
{
lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5983_; 
lean_inc(v_fst_5958_);
v_isSharedCheck_5983_ = !lean_is_exclusive(v_pos_5957_);
if (v_isSharedCheck_5983_ == 0)
{
lean_object* v_unused_5984_; lean_object* v_unused_5985_; 
v_unused_5984_ = lean_ctor_get(v_pos_5957_, 1);
lean_dec(v_unused_5984_);
v_unused_5985_ = lean_ctor_get(v_pos_5957_, 0);
lean_dec(v_unused_5985_);
v___x_5968_ = v_pos_5957_;
v_isShared_5969_ = v_isSharedCheck_5983_;
goto v_resetjp_5967_;
}
else
{
lean_dec(v_pos_5957_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5983_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v___x_5970_; lean_object* v_it_x27_5972_; 
v___x_5970_ = lean_string_utf8_next_fast(v_fst_5958_, v_snd_5959_);
if (v_isShared_5969_ == 0)
{
lean_ctor_set(v___x_5968_, 1, v___x_5970_);
v_it_x27_5972_ = v___x_5968_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_fst_5958_);
lean_ctor_set(v_reuseFailAlloc_5982_, 1, v___x_5970_);
v_it_x27_5972_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
lean_object* v___x_5973_; lean_object* v___x_5974_; 
v___x_5973_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0);
v___x_5974_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(v___x_5973_, v_it_x27_5972_);
if (lean_obj_tag(v___x_5974_) == 0)
{
lean_object* v_pos_5975_; lean_object* v_res_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
v_pos_5975_ = lean_ctor_get(v___x_5974_, 0);
lean_inc(v_pos_5975_);
v_res_5976_ = lean_ctor_get(v___x_5974_, 1);
lean_inc(v_res_5976_);
lean_dec_ref_known(v___x_5974_, 2);
v___x_5977_ = ((lean_object*)(l_Std_Time_parseModifier___closed__30));
v___x_5978_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5953_, v___x_5977_, v_res_5976_, v_pos_5975_);
if (lean_obj_tag(v___x_5978_) == 0)
{
lean_dec(v_snd_5959_);
return v___x_5978_;
}
else
{
lean_object* v_pos_5979_; 
v_pos_5979_ = lean_ctor_get(v___x_5978_, 0);
lean_inc(v_pos_5979_);
v_snd_5914_ = v_snd_5959_;
v___y_5915_ = v___x_5978_;
v_pos_5916_ = v_pos_5979_;
goto v___jp_5913_;
}
}
else
{
lean_object* v_pos_5980_; lean_object* v_err_5981_; 
v_pos_5980_ = lean_ctor_get(v___x_5974_, 0);
lean_inc(v_pos_5980_);
v_err_5981_ = lean_ctor_get(v___x_5974_, 1);
lean_inc(v_err_5981_);
lean_dec_ref_known(v___x_5974_, 2);
v_snd_5945_ = v_snd_5959_;
v_pos_5946_ = v_pos_5980_;
v_err_5947_ = v_err_5981_;
goto v___jp_5944_;
}
}
}
}
}
}
else
{
v___y_5950_ = v_pos_5957_;
v_snd_5951_ = v_snd_5959_;
goto v___jp_5949_;
}
}
}
v___jp_5986_:
{
lean_object* v___x_5990_; 
lean_inc_ref(v_pos_5988_);
v___x_5990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5990_, 0, v_pos_5988_);
lean_ctor_set(v___x_5990_, 1, v_err_5989_);
v_snd_5955_ = v_snd_5987_;
v___y_5956_ = v___x_5990_;
v_pos_5957_ = v_pos_5988_;
goto v___jp_5954_;
}
v___jp_5991_:
{
lean_object* v___x_5994_; 
v___x_5994_ = lean_box(0);
v_snd_5987_ = v_snd_5993_;
v_pos_5988_ = v___y_5992_;
v_err_5989_ = v___x_5994_;
goto v___jp_5986_;
}
v___jp_5996_:
{
lean_object* v_fst_6000_; lean_object* v_snd_6001_; uint8_t v___x_6002_; 
v_fst_6000_ = lean_ctor_get(v_pos_5999_, 0);
v_snd_6001_ = lean_ctor_get(v_pos_5999_, 1);
lean_inc(v_snd_6001_);
v___x_6002_ = lean_nat_dec_eq(v_snd_5997_, v_snd_6001_);
lean_dec(v_snd_5997_);
if (v___x_6002_ == 0)
{
lean_dec(v_snd_6001_);
lean_dec_ref(v_pos_5999_);
return v___y_5998_;
}
else
{
lean_object* v___x_6003_; uint8_t v___x_6004_; 
lean_dec_ref(v___y_5998_);
v___x_6003_ = lean_string_utf8_byte_size(v_fst_6000_);
v___x_6004_ = lean_nat_dec_eq(v_snd_6001_, v___x_6003_);
if (v___x_6004_ == 0)
{
if (v___x_6002_ == 0)
{
v___y_5992_ = v_pos_5999_;
v_snd_5993_ = v_snd_6001_;
goto v___jp_5991_;
}
else
{
uint32_t v___x_6005_; uint32_t v_c_6006_; uint8_t v___x_6007_; 
v___x_6005_ = 117;
v_c_6006_ = lean_string_utf8_get_fast(v_fst_6000_, v_snd_6001_);
v___x_6007_ = lean_uint32_dec_eq(v_c_6006_, v___x_6005_);
if (v___x_6007_ == 0)
{
lean_object* v___x_6008_; 
v___x_6008_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3);
v_snd_5987_ = v_snd_6001_;
v_pos_5988_ = v_pos_5999_;
v_err_5989_ = v___x_6008_;
goto v___jp_5986_;
}
else
{
lean_object* v___x_6010_; uint8_t v_isShared_6011_; uint8_t v_isSharedCheck_6024_; 
lean_inc(v_fst_6000_);
v_isSharedCheck_6024_ = !lean_is_exclusive(v_pos_5999_);
if (v_isSharedCheck_6024_ == 0)
{
lean_object* v_unused_6025_; lean_object* v_unused_6026_; 
v_unused_6025_ = lean_ctor_get(v_pos_5999_, 1);
lean_dec(v_unused_6025_);
v_unused_6026_ = lean_ctor_get(v_pos_5999_, 0);
lean_dec(v_unused_6026_);
v___x_6010_ = v_pos_5999_;
v_isShared_6011_ = v_isSharedCheck_6024_;
goto v_resetjp_6009_;
}
else
{
lean_dec(v_pos_5999_);
v___x_6010_ = lean_box(0);
v_isShared_6011_ = v_isSharedCheck_6024_;
goto v_resetjp_6009_;
}
v_resetjp_6009_:
{
lean_object* v___x_6012_; lean_object* v_it_x27_6014_; 
v___x_6012_ = lean_string_utf8_next_fast(v_fst_6000_, v_snd_6001_);
if (v_isShared_6011_ == 0)
{
lean_ctor_set(v___x_6010_, 1, v___x_6012_);
v_it_x27_6014_ = v___x_6010_;
goto v_reusejp_6013_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_fst_6000_);
lean_ctor_set(v_reuseFailAlloc_6023_, 1, v___x_6012_);
v_it_x27_6014_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6013_;
}
v_reusejp_6013_:
{
lean_object* v___x_6015_; lean_object* v___x_6016_; 
v___x_6015_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0);
v___x_6016_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(v___x_6015_, v_it_x27_6014_);
if (lean_obj_tag(v___x_6016_) == 0)
{
lean_object* v_pos_6017_; lean_object* v_res_6018_; lean_object* v___x_6019_; 
v_pos_6017_ = lean_ctor_get(v___x_6016_, 0);
lean_inc(v_pos_6017_);
v_res_6018_ = lean_ctor_get(v___x_6016_, 1);
lean_inc(v_res_6018_);
lean_dec_ref_known(v___x_6016_, 2);
v___x_6019_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5995_, v_res_6018_, v_pos_6017_);
if (lean_obj_tag(v___x_6019_) == 0)
{
lean_dec(v_snd_6001_);
return v___x_6019_;
}
else
{
lean_object* v_pos_6020_; 
v_pos_6020_ = lean_ctor_get(v___x_6019_, 0);
lean_inc(v_pos_6020_);
v_snd_5955_ = v_snd_6001_;
v___y_5956_ = v___x_6019_;
v_pos_5957_ = v_pos_6020_;
goto v___jp_5954_;
}
}
else
{
lean_object* v_pos_6021_; lean_object* v_err_6022_; 
v_pos_6021_ = lean_ctor_get(v___x_6016_, 0);
lean_inc(v_pos_6021_);
v_err_6022_ = lean_ctor_get(v___x_6016_, 1);
lean_inc(v_err_6022_);
lean_dec_ref_known(v___x_6016_, 2);
v_snd_5987_ = v_snd_6001_;
v_pos_5988_ = v_pos_6021_;
v_err_5989_ = v_err_6022_;
goto v___jp_5986_;
}
}
}
}
}
}
else
{
v___y_5992_ = v_pos_5999_;
v_snd_5993_ = v_snd_6001_;
goto v___jp_5991_;
}
}
}
v___jp_6027_:
{
lean_object* v___x_6031_; 
lean_inc_ref(v_pos_6029_);
v___x_6031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6031_, 0, v_pos_6029_);
lean_ctor_set(v___x_6031_, 1, v_err_6030_);
v_snd_5997_ = v_snd_6028_;
v___y_5998_ = v___x_6031_;
v_pos_5999_ = v_pos_6029_;
goto v___jp_5996_;
}
v___jp_6032_:
{
lean_object* v___x_6035_; 
v___x_6035_ = lean_box(0);
v_snd_6028_ = v_snd_6034_;
v_pos_6029_ = v___y_6033_;
v_err_6030_ = v___x_6035_;
goto v___jp_6027_;
}
v___jp_6037_:
{
lean_object* v_fst_6041_; lean_object* v_snd_6042_; uint8_t v___x_6043_; 
v_fst_6041_ = lean_ctor_get(v_pos_6040_, 0);
v_snd_6042_ = lean_ctor_get(v_pos_6040_, 1);
lean_inc(v_snd_6042_);
v___x_6043_ = lean_nat_dec_eq(v_snd_6038_, v_snd_6042_);
lean_dec(v_snd_6038_);
if (v___x_6043_ == 0)
{
lean_dec(v_snd_6042_);
lean_dec_ref(v_pos_6040_);
return v___y_6039_;
}
else
{
lean_object* v___x_6044_; uint8_t v___x_6045_; 
lean_dec_ref(v___y_6039_);
v___x_6044_ = lean_string_utf8_byte_size(v_fst_6041_);
v___x_6045_ = lean_nat_dec_eq(v_snd_6042_, v___x_6044_);
if (v___x_6045_ == 0)
{
if (v___x_6043_ == 0)
{
v___y_6033_ = v_pos_6040_;
v_snd_6034_ = v_snd_6042_;
goto v___jp_6032_;
}
else
{
uint32_t v___x_6046_; uint32_t v_c_6047_; uint8_t v___x_6048_; 
v___x_6046_ = 89;
v_c_6047_ = lean_string_utf8_get_fast(v_fst_6041_, v_snd_6042_);
v___x_6048_ = lean_uint32_dec_eq(v_c_6047_, v___x_6046_);
if (v___x_6048_ == 0)
{
lean_object* v___x_6049_; 
v___x_6049_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3);
v_snd_6028_ = v_snd_6042_;
v_pos_6029_ = v_pos_6040_;
v_err_6030_ = v___x_6049_;
goto v___jp_6027_;
}
else
{
lean_object* v___x_6051_; uint8_t v_isShared_6052_; uint8_t v_isSharedCheck_6065_; 
lean_inc(v_fst_6041_);
v_isSharedCheck_6065_ = !lean_is_exclusive(v_pos_6040_);
if (v_isSharedCheck_6065_ == 0)
{
lean_object* v_unused_6066_; lean_object* v_unused_6067_; 
v_unused_6066_ = lean_ctor_get(v_pos_6040_, 1);
lean_dec(v_unused_6066_);
v_unused_6067_ = lean_ctor_get(v_pos_6040_, 0);
lean_dec(v_unused_6067_);
v___x_6051_ = v_pos_6040_;
v_isShared_6052_ = v_isSharedCheck_6065_;
goto v_resetjp_6050_;
}
else
{
lean_dec(v_pos_6040_);
v___x_6051_ = lean_box(0);
v_isShared_6052_ = v_isSharedCheck_6065_;
goto v_resetjp_6050_;
}
v_resetjp_6050_:
{
lean_object* v___x_6053_; lean_object* v_it_x27_6055_; 
v___x_6053_ = lean_string_utf8_next_fast(v_fst_6041_, v_snd_6042_);
if (v_isShared_6052_ == 0)
{
lean_ctor_set(v___x_6051_, 1, v___x_6053_);
v_it_x27_6055_ = v___x_6051_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6064_; 
v_reuseFailAlloc_6064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_fst_6041_);
lean_ctor_set(v_reuseFailAlloc_6064_, 1, v___x_6053_);
v_it_x27_6055_ = v_reuseFailAlloc_6064_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
lean_object* v___x_6056_; lean_object* v___x_6057_; 
v___x_6056_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0);
v___x_6057_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(v___x_6056_, v_it_x27_6055_);
if (lean_obj_tag(v___x_6057_) == 0)
{
lean_object* v_pos_6058_; lean_object* v_res_6059_; lean_object* v___x_6060_; 
v_pos_6058_ = lean_ctor_get(v___x_6057_, 0);
lean_inc(v_pos_6058_);
v_res_6059_ = lean_ctor_get(v___x_6057_, 1);
lean_inc(v_res_6059_);
lean_dec_ref_known(v___x_6057_, 2);
v___x_6060_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_6036_, v_res_6059_, v_pos_6058_);
if (lean_obj_tag(v___x_6060_) == 0)
{
lean_dec(v_snd_6042_);
return v___x_6060_;
}
else
{
lean_object* v_pos_6061_; 
v_pos_6061_ = lean_ctor_get(v___x_6060_, 0);
lean_inc(v_pos_6061_);
v_snd_5997_ = v_snd_6042_;
v___y_5998_ = v___x_6060_;
v_pos_5999_ = v_pos_6061_;
goto v___jp_5996_;
}
}
else
{
lean_object* v_pos_6062_; lean_object* v_err_6063_; 
v_pos_6062_ = lean_ctor_get(v___x_6057_, 0);
lean_inc(v_pos_6062_);
v_err_6063_ = lean_ctor_get(v___x_6057_, 1);
lean_inc(v_err_6063_);
lean_dec_ref_known(v___x_6057_, 2);
v_snd_6028_ = v_snd_6042_;
v_pos_6029_ = v_pos_6062_;
v_err_6030_ = v_err_6063_;
goto v___jp_6027_;
}
}
}
}
}
}
else
{
v___y_6033_ = v_pos_6040_;
v_snd_6034_ = v_snd_6042_;
goto v___jp_6032_;
}
}
}
v___jp_6068_:
{
lean_object* v___x_6072_; 
lean_inc_ref(v_pos_6070_);
v___x_6072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6072_, 0, v_pos_6070_);
lean_ctor_set(v___x_6072_, 1, v_err_6071_);
v_snd_6038_ = v_snd_6069_;
v___y_6039_ = v___x_6072_;
v_pos_6040_ = v_pos_6070_;
goto v___jp_6037_;
}
v___jp_6073_:
{
lean_object* v___x_6076_; 
v___x_6076_ = lean_box(0);
v_snd_6069_ = v_snd_6075_;
v_pos_6070_ = v___y_6074_;
v_err_6071_ = v___x_6076_;
goto v___jp_6068_;
}
v___jp_6078_:
{
lean_object* v_fst_6081_; lean_object* v_snd_6082_; uint8_t v___x_6083_; 
v_fst_6081_ = lean_ctor_get(v_pos_6080_, 0);
v_snd_6082_ = lean_ctor_get(v_pos_6080_, 1);
lean_inc(v_snd_6082_);
v___x_6083_ = lean_nat_dec_eq(v_snd_4616_, v_snd_6082_);
lean_dec(v_snd_4616_);
if (v___x_6083_ == 0)
{
lean_dec(v_snd_6082_);
lean_dec_ref(v_pos_6080_);
return v___y_6079_;
}
else
{
lean_object* v___x_6084_; uint8_t v___x_6085_; 
lean_dec_ref(v___y_6079_);
v___x_6084_ = lean_string_utf8_byte_size(v_fst_6081_);
v___x_6085_ = lean_nat_dec_eq(v_snd_6082_, v___x_6084_);
if (v___x_6085_ == 0)
{
if (v___x_6083_ == 0)
{
v___y_6074_ = v_pos_6080_;
v_snd_6075_ = v_snd_6082_;
goto v___jp_6073_;
}
else
{
uint32_t v___x_6086_; uint32_t v_c_6087_; uint8_t v___x_6088_; 
v___x_6086_ = 121;
v_c_6087_ = lean_string_utf8_get_fast(v_fst_6081_, v_snd_6082_);
v___x_6088_ = lean_uint32_dec_eq(v_c_6087_, v___x_6086_);
if (v___x_6088_ == 0)
{
lean_object* v___x_6089_; 
v___x_6089_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3);
v_snd_6069_ = v_snd_6082_;
v_pos_6070_ = v_pos_6080_;
v_err_6071_ = v___x_6089_;
goto v___jp_6068_;
}
else
{
lean_object* v___x_6091_; uint8_t v_isShared_6092_; uint8_t v_isSharedCheck_6105_; 
lean_inc(v_fst_6081_);
v_isSharedCheck_6105_ = !lean_is_exclusive(v_pos_6080_);
if (v_isSharedCheck_6105_ == 0)
{
lean_object* v_unused_6106_; lean_object* v_unused_6107_; 
v_unused_6106_ = lean_ctor_get(v_pos_6080_, 1);
lean_dec(v_unused_6106_);
v_unused_6107_ = lean_ctor_get(v_pos_6080_, 0);
lean_dec(v_unused_6107_);
v___x_6091_ = v_pos_6080_;
v_isShared_6092_ = v_isSharedCheck_6105_;
goto v_resetjp_6090_;
}
else
{
lean_dec(v_pos_6080_);
v___x_6091_ = lean_box(0);
v_isShared_6092_ = v_isSharedCheck_6105_;
goto v_resetjp_6090_;
}
v_resetjp_6090_:
{
lean_object* v___x_6093_; lean_object* v_it_x27_6095_; 
v___x_6093_ = lean_string_utf8_next_fast(v_fst_6081_, v_snd_6082_);
if (v_isShared_6092_ == 0)
{
lean_ctor_set(v___x_6091_, 1, v___x_6093_);
v_it_x27_6095_ = v___x_6091_;
goto v_reusejp_6094_;
}
else
{
lean_object* v_reuseFailAlloc_6104_; 
v_reuseFailAlloc_6104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6104_, 0, v_fst_6081_);
lean_ctor_set(v_reuseFailAlloc_6104_, 1, v___x_6093_);
v_it_x27_6095_ = v_reuseFailAlloc_6104_;
goto v_reusejp_6094_;
}
v_reusejp_6094_:
{
lean_object* v___x_6096_; lean_object* v___x_6097_; 
v___x_6096_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0);
v___x_6097_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(v___x_6096_, v_it_x27_6095_);
if (lean_obj_tag(v___x_6097_) == 0)
{
lean_object* v_pos_6098_; lean_object* v_res_6099_; lean_object* v___x_6100_; 
v_pos_6098_ = lean_ctor_get(v___x_6097_, 0);
lean_inc(v_pos_6098_);
v_res_6099_ = lean_ctor_get(v___x_6097_, 1);
lean_inc(v_res_6099_);
lean_dec_ref_known(v___x_6097_, 2);
v___x_6100_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_6077_, v_res_6099_, v_pos_6098_);
if (lean_obj_tag(v___x_6100_) == 0)
{
lean_dec(v_snd_6082_);
return v___x_6100_;
}
else
{
lean_object* v_pos_6101_; 
v_pos_6101_ = lean_ctor_get(v___x_6100_, 0);
lean_inc(v_pos_6101_);
v_snd_6038_ = v_snd_6082_;
v___y_6039_ = v___x_6100_;
v_pos_6040_ = v_pos_6101_;
goto v___jp_6037_;
}
}
else
{
lean_object* v_pos_6102_; lean_object* v_err_6103_; 
v_pos_6102_ = lean_ctor_get(v___x_6097_, 0);
lean_inc(v_pos_6102_);
v_err_6103_ = lean_ctor_get(v___x_6097_, 1);
lean_inc(v_err_6103_);
lean_dec_ref_known(v___x_6097_, 2);
v_snd_6069_ = v_snd_6082_;
v_pos_6070_ = v_pos_6102_;
v_err_6071_ = v_err_6103_;
goto v___jp_6068_;
}
}
}
}
}
}
else
{
v___y_6074_ = v_pos_6080_;
v_snd_6075_ = v_snd_6082_;
goto v___jp_6073_;
}
}
}
v___jp_6108_:
{
lean_object* v___x_6111_; 
lean_inc_ref(v_pos_6109_);
v___x_6111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6111_, 0, v_pos_6109_);
lean_ctor_set(v___x_6111_, 1, v_err_6110_);
v___y_6079_ = v___x_6111_;
v_pos_6080_ = v_pos_6109_;
goto v___jp_6078_;
}
}
}
lean_object* runtime_initialize_Std_Time_Zoned(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Format_Modifier(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedText_default = _init_l_Std_Time_instInhabitedText_default();
l_Std_Time_instInhabitedText = _init_l_Std_Time_instInhabitedText();
l_Std_Time_instInhabitedNumber_default = _init_l_Std_Time_instInhabitedNumber_default();
lean_mark_persistent(l_Std_Time_instInhabitedNumber_default);
l_Std_Time_instInhabitedNumber = _init_l_Std_Time_instInhabitedNumber();
lean_mark_persistent(l_Std_Time_instInhabitedNumber);
l_Std_Time_instInhabitedFraction_default = _init_l_Std_Time_instInhabitedFraction_default();
lean_mark_persistent(l_Std_Time_instInhabitedFraction_default);
l_Std_Time_instInhabitedFraction = _init_l_Std_Time_instInhabitedFraction();
lean_mark_persistent(l_Std_Time_instInhabitedFraction);
l_Std_Time_instInhabitedYear_default = _init_l_Std_Time_instInhabitedYear_default();
lean_mark_persistent(l_Std_Time_instInhabitedYear_default);
l_Std_Time_instInhabitedYear = _init_l_Std_Time_instInhabitedYear();
lean_mark_persistent(l_Std_Time_instInhabitedYear);
l_Std_Time_instInhabitedZoneId_default = _init_l_Std_Time_instInhabitedZoneId_default();
l_Std_Time_instInhabitedZoneId = _init_l_Std_Time_instInhabitedZoneId();
l_Std_Time_instInhabitedZoneName_default = _init_l_Std_Time_instInhabitedZoneName_default();
l_Std_Time_instInhabitedZoneName = _init_l_Std_Time_instInhabitedZoneName();
l_Std_Time_instInhabitedOffsetX_default = _init_l_Std_Time_instInhabitedOffsetX_default();
l_Std_Time_instInhabitedOffsetX = _init_l_Std_Time_instInhabitedOffsetX();
l_Std_Time_instInhabitedOffsetO_default = _init_l_Std_Time_instInhabitedOffsetO_default();
l_Std_Time_instInhabitedOffsetO = _init_l_Std_Time_instInhabitedOffsetO();
l_Std_Time_instInhabitedOffsetZ_default = _init_l_Std_Time_instInhabitedOffsetZ_default();
l_Std_Time_instInhabitedOffsetZ = _init_l_Std_Time_instInhabitedOffsetZ();
l_Std_Time_instInhabitedDayPeriod_default = _init_l_Std_Time_instInhabitedDayPeriod_default();
l_Std_Time_instInhabitedDayPeriod = _init_l_Std_Time_instInhabitedDayPeriod();
l_Std_Time_instInhabitedExtendedDayPeriod_default = _init_l_Std_Time_instInhabitedExtendedDayPeriod_default();
l_Std_Time_instInhabitedExtendedDayPeriod = _init_l_Std_Time_instInhabitedExtendedDayPeriod();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Format_Modifier(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Format_Modifier(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Format_Modifier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Format_Modifier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Format_Modifier(builtin);
}
#ifdef __cplusplus
}
#endif
