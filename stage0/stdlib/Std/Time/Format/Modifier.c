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
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___redArg(lean_object* v_k_9_){
_start:
{
lean_inc(v_k_9_);
return v_k_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___redArg___boxed(lean_object* v_k_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Std_Time_Text_ctorElim___redArg(v_k_10_);
lean_dec(v_k_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, uint8_t v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Time_Text_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___redArg(lean_object* v_short_24_){
_start:
{
lean_inc(v_short_24_);
return v_short_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___redArg___boxed(lean_object* v_short_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_Text_short_elim___redArg(v_short_25_);
lean_dec(v_short_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_short_30_){
_start:
{
lean_inc(v_short_30_);
return v_short_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___boxed(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_short_34_){
_start:
{
uint8_t v_t_boxed_35_; lean_object* v_res_36_; 
v_t_boxed_35_ = lean_unbox(v_t_32_);
v_res_36_ = l_Std_Time_Text_short_elim(v_motive_31_, v_t_boxed_35_, v_h_33_, v_short_34_);
lean_dec(v_short_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___redArg(lean_object* v_full_37_){
_start:
{
lean_inc(v_full_37_);
return v_full_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___redArg___boxed(lean_object* v_full_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_Time_Text_full_elim___redArg(v_full_38_);
lean_dec(v_full_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim(lean_object* v_motive_40_, uint8_t v_t_41_, lean_object* v_h_42_, lean_object* v_full_43_){
_start:
{
lean_inc(v_full_43_);
return v_full_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___boxed(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_full_47_){
_start:
{
uint8_t v_t_boxed_48_; lean_object* v_res_49_; 
v_t_boxed_48_ = lean_unbox(v_t_45_);
v_res_49_ = l_Std_Time_Text_full_elim(v_motive_44_, v_t_boxed_48_, v_h_46_, v_full_47_);
lean_dec(v_full_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___redArg(lean_object* v_narrow_50_){
_start:
{
lean_inc(v_narrow_50_);
return v_narrow_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___redArg___boxed(lean_object* v_narrow_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Time_Text_narrow_elim___redArg(v_narrow_51_);
lean_dec(v_narrow_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim(lean_object* v_motive_53_, uint8_t v_t_54_, lean_object* v_h_55_, lean_object* v_narrow_56_){
_start:
{
lean_inc(v_narrow_56_);
return v_narrow_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___boxed(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_narrow_60_){
_start:
{
uint8_t v_t_boxed_61_; lean_object* v_res_62_; 
v_t_boxed_61_ = lean_unbox(v_t_58_);
v_res_62_ = l_Std_Time_Text_narrow_elim(v_motive_57_, v_t_boxed_61_, v_h_59_, v_narrow_60_);
lean_dec(v_narrow_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___redArg(lean_object* v_twoLetterShort_63_){
_start:
{
lean_inc(v_twoLetterShort_63_);
return v_twoLetterShort_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___redArg___boxed(lean_object* v_twoLetterShort_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_Time_Text_twoLetterShort_elim___redArg(v_twoLetterShort_64_);
lean_dec(v_twoLetterShort_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim(lean_object* v_motive_66_, uint8_t v_t_67_, lean_object* v_h_68_, lean_object* v_twoLetterShort_69_){
_start:
{
lean_inc(v_twoLetterShort_69_);
return v_twoLetterShort_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___boxed(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_twoLetterShort_73_){
_start:
{
uint8_t v_t_boxed_74_; lean_object* v_res_75_; 
v_t_boxed_74_ = lean_unbox(v_t_71_);
v_res_75_ = l_Std_Time_Text_twoLetterShort_elim(v_motive_70_, v_t_boxed_74_, v_h_72_, v_twoLetterShort_73_);
lean_dec(v_twoLetterShort_73_);
return v_res_75_;
}
}
static lean_object* _init_l_Std_Time_instReprText_repr___closed__8(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(2u);
v___x_89_ = lean_nat_to_int(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Std_Time_instReprText_repr___closed__9(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_to_int(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprText_repr(uint8_t v_x_92_, lean_object* v_prec_93_){
_start:
{
lean_object* v___y_95_; lean_object* v___y_102_; lean_object* v___y_109_; lean_object* v___y_116_; 
switch(v_x_92_)
{
case 0:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(1024u);
v___x_123_ = lean_nat_dec_le(v___x_122_, v_prec_93_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_95_ = v___x_124_;
goto v___jp_94_;
}
else
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_95_ = v___x_125_;
goto v___jp_94_;
}
}
case 1:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1024u);
v___x_127_ = lean_nat_dec_le(v___x_126_, v_prec_93_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_102_ = v___x_128_;
goto v___jp_101_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_102_ = v___x_129_;
goto v___jp_101_;
}
}
case 2:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1024u);
v___x_131_ = lean_nat_dec_le(v___x_130_, v_prec_93_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_109_ = v___x_132_;
goto v___jp_108_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_109_ = v___x_133_;
goto v___jp_108_;
}
}
default: 
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(1024u);
v___x_135_ = lean_nat_dec_le(v___x_134_, v_prec_93_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_116_ = v___x_136_;
goto v___jp_115_;
}
else
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_116_ = v___x_137_;
goto v___jp_115_;
}
}
}
v___jp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_96_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__1));
lean_inc(v___y_95_);
v___x_97_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_97_, 0, v___y_95_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = 0;
v___x_99_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set_uint8(v___x_99_, sizeof(void*)*1, v___x_98_);
v___x_100_ = l_Repr_addAppParen(v___x_99_, v_prec_93_);
return v___x_100_;
}
v___jp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_103_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__3));
lean_inc(v___y_102_);
v___x_104_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_104_, 0, v___y_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = 0;
v___x_106_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*1, v___x_105_);
v___x_107_ = l_Repr_addAppParen(v___x_106_, v_prec_93_);
return v___x_107_;
}
v___jp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_110_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__5));
lean_inc(v___y_109_);
v___x_111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_111_, 0, v___y_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = 0;
v___x_113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
v___x_114_ = l_Repr_addAppParen(v___x_113_, v_prec_93_);
return v___x_114_;
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_117_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__7));
lean_inc(v___y_116_);
v___x_118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_118_, 0, v___y_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = 0;
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_119_);
v___x_121_ = l_Repr_addAppParen(v___x_120_, v_prec_93_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprText_repr___boxed(lean_object* v_x_138_, lean_object* v_prec_139_){
_start:
{
uint8_t v_x_225__boxed_140_; lean_object* v_res_141_; 
v_x_225__boxed_140_ = lean_unbox(v_x_138_);
v_res_141_ = l_Std_Time_instReprText_repr(v_x_225__boxed_140_, v_prec_139_);
lean_dec(v_prec_139_);
return v_res_141_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedText_default(void){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedText(void){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_classify(lean_object* v_num_155_){
_start:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = lean_nat_dec_lt(v_num_155_, v___x_156_);
if (v___x_157_ == 0)
{
uint8_t v___x_158_; 
v___x_158_ = lean_nat_dec_eq(v_num_155_, v___x_156_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(5u);
v___x_160_ = lean_nat_dec_eq(v_num_155_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(0);
return v___x_161_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Std_Time_Text_classify___closed__0));
return v___x_162_;
}
}
else
{
lean_object* v___x_163_; 
v___x_163_ = ((lean_object*)(l_Std_Time_Text_classify___closed__1));
return v___x_163_;
}
}
else
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l_Std_Time_Text_classify___closed__2));
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_classify___boxed(lean_object* v_num_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Time_Text_classify(v_num_165_);
lean_dec(v_num_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprNumber_repr_spec__0(lean_object* v_a_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_nat_to_int(v_a_167_);
return v___x_168_;
}
}
static lean_object* _init_l_Std_Time_instReprNumber_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(11u);
v___x_183_ = lean_nat_to_int(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Std_Time_instReprNumber_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__0));
v___x_186_ = lean_string_length(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Std_Time_instReprNumber_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_obj_once(&l_Std_Time_instReprNumber_repr___redArg___closed__9, &l_Std_Time_instReprNumber_repr___redArg___closed__9_once, _init_l_Std_Time_instReprNumber_repr___redArg___closed__9);
v___x_188_ = lean_nat_to_int(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr___redArg(lean_object* v_x_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_194_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__6));
v___x_195_ = lean_obj_once(&l_Std_Time_instReprNumber_repr___redArg___closed__7, &l_Std_Time_instReprNumber_repr___redArg___closed__7_once, _init_l_Std_Time_instReprNumber_repr___redArg___closed__7);
v___x_196_ = l_Nat_reprFast(v_x_193_);
v___x_197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
v___x_198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_195_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = 0;
v___x_200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*1, v___x_199_);
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_194_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_obj_once(&l_Std_Time_instReprNumber_repr___redArg___closed__10, &l_Std_Time_instReprNumber_repr___redArg___closed__10_once, _init_l_Std_Time_instReprNumber_repr___redArg___closed__10);
v___x_203_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__11));
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_201_);
v___x_205_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__12));
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_202_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set_uint8(v___x_208_, sizeof(void*)*1, v___x_199_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr(lean_object* v_x_209_, lean_object* v_prec_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Std_Time_instReprNumber_repr___redArg(v_x_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr___boxed(lean_object* v_x_212_, lean_object* v_prec_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Time_instReprNumber_repr(v_x_212_, v_prec_213_);
lean_dec(v_prec_213_);
return v_res_214_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedNumber_default(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_unsigned_to_nat(0u);
return v___x_217_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedNumber(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_unsigned_to_nat(0u);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyNumberText(lean_object* v_x_219_){
_start:
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = lean_unsigned_to_nat(3u);
v___x_221_ = lean_nat_dec_lt(v_x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
v___x_222_ = l_Std_Time_Text_classify(v_x_219_);
lean_dec(v_x_219_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(0);
return v___x_223_;
}
else
{
lean_object* v_val_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_val_224_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_232_ == 0)
{
v___x_226_ = v___x_222_;
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_val_224_);
lean_dec(v___x_222_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v_val_224_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_x_219_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx(lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(0u);
return v___x_236_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(1u);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx___boxed(lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Time_Fraction_ctorIdx(v_x_238_);
lean_dec(v_x_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim___redArg(lean_object* v_t_240_, lean_object* v_k_241_){
_start:
{
if (lean_obj_tag(v_t_240_) == 0)
{
return v_k_241_;
}
else
{
lean_object* v_digits_242_; lean_object* v___x_243_; 
v_digits_242_ = lean_ctor_get(v_t_240_, 0);
lean_inc(v_digits_242_);
lean_dec_ref_known(v_t_240_, 1);
v___x_243_ = lean_apply_1(v_k_241_, v_digits_242_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim(lean_object* v_motive_244_, lean_object* v_ctorIdx_245_, lean_object* v_t_246_, lean_object* v_h_247_, lean_object* v_k_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_246_, v_k_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim___boxed(lean_object* v_motive_250_, lean_object* v_ctorIdx_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_k_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_Time_Fraction_ctorElim(v_motive_250_, v_ctorIdx_251_, v_t_252_, v_h_253_, v_k_254_);
lean_dec(v_ctorIdx_251_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_nano_elim___redArg(lean_object* v_t_256_, lean_object* v_nano_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_256_, v_nano_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_nano_elim(lean_object* v_motive_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_nano_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_260_, v_nano_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_truncated_elim___redArg(lean_object* v_t_264_, lean_object* v_truncated_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_264_, v_truncated_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_truncated_elim(lean_object* v_motive_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_truncated_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_268_, v_truncated_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFraction_repr(lean_object* v_x_281_, lean_object* v_prec_282_){
_start:
{
lean_object* v___y_284_; 
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(1024u);
v___x_291_ = lean_nat_dec_le(v___x_290_, v_prec_282_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
v___x_292_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_284_ = v___x_292_;
goto v___jp_283_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_284_ = v___x_293_;
goto v___jp_283_;
}
}
else
{
lean_object* v_digits_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_314_; 
v_digits_294_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_314_ == 0)
{
v___x_296_ = v_x_281_;
v_isShared_297_ = v_isSharedCheck_314_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_digits_294_);
lean_dec(v_x_281_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_314_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___y_299_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(1024u);
v___x_311_ = lean_nat_dec_le(v___x_310_, v_prec_282_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_299_ = v___x_312_;
goto v___jp_298_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_299_ = v___x_313_;
goto v___jp_298_;
}
v___jp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_300_ = ((lean_object*)(l_Std_Time_instReprFraction_repr___closed__4));
v___x_301_ = l_Nat_reprFast(v_digits_294_);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 3);
lean_ctor_set(v___x_296_, 0, v___x_301_);
v___x_303_ = v___x_296_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_309_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_300_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
lean_inc(v___y_299_);
v___x_305_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_305_, 0, v___y_299_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = 0;
v___x_307_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set_uint8(v___x_307_, sizeof(void*)*1, v___x_306_);
v___x_308_ = l_Repr_addAppParen(v___x_307_, v_prec_282_);
return v___x_308_;
}
}
}
}
v___jp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_285_ = ((lean_object*)(l_Std_Time_instReprFraction_repr___closed__1));
lean_inc(v___y_284_);
v___x_286_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_286_, 0, v___y_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = 0;
v___x_288_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*1, v___x_287_);
v___x_289_ = l_Repr_addAppParen(v___x_288_, v_prec_282_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFraction_repr___boxed(lean_object* v_x_315_, lean_object* v_prec_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_Time_instReprFraction_repr(v_x_315_, v_prec_316_);
lean_dec(v_prec_316_);
return v_res_317_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFraction_default(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_box(0);
return v___x_320_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFraction(void){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_box(0);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_classify(lean_object* v_nat_324_){
_start:
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(9u);
v___x_326_ = lean_nat_dec_lt(v_nat_324_, v___x_325_);
if (v___x_326_ == 0)
{
uint8_t v___x_327_; 
v___x_327_ = lean_nat_dec_eq(v_nat_324_, v___x_325_);
lean_dec(v_nat_324_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
v___x_328_ = lean_box(0);
return v___x_328_;
}
else
{
lean_object* v___x_329_; 
v___x_329_ = ((lean_object*)(l_Std_Time_Fraction_classify___closed__0));
return v___x_329_;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v_nat_324_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx(lean_object* v_x_332_){
_start:
{
switch(lean_obj_tag(v_x_332_))
{
case 0:
{
lean_object* v___x_333_; 
v___x_333_ = lean_unsigned_to_nat(0u);
return v___x_333_;
}
case 1:
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(1u);
return v___x_334_;
}
case 2:
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(2u);
return v___x_335_;
}
default: 
{
lean_object* v___x_336_; 
v___x_336_ = lean_unsigned_to_nat(3u);
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx___boxed(lean_object* v_x_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_Time_Year_ctorIdx(v_x_337_);
lean_dec(v_x_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim___redArg(lean_object* v_t_339_, lean_object* v_k_340_){
_start:
{
if (lean_obj_tag(v_t_339_) == 3)
{
lean_object* v_num_341_; lean_object* v___x_342_; 
v_num_341_ = lean_ctor_get(v_t_339_, 0);
lean_inc(v_num_341_);
lean_dec_ref_known(v_t_339_, 1);
v___x_342_ = lean_apply_1(v_k_340_, v_num_341_);
return v___x_342_;
}
else
{
lean_dec(v_t_339_);
return v_k_340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim(lean_object* v_motive_343_, lean_object* v_ctorIdx_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_k_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Std_Time_Year_ctorElim___redArg(v_t_345_, v_k_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim___boxed(lean_object* v_motive_349_, lean_object* v_ctorIdx_350_, lean_object* v_t_351_, lean_object* v_h_352_, lean_object* v_k_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_Time_Year_ctorElim(v_motive_349_, v_ctorIdx_350_, v_t_351_, v_h_352_, v_k_353_);
lean_dec(v_ctorIdx_350_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_any_elim___redArg(lean_object* v_t_355_, lean_object* v_any_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_Time_Year_ctorElim___redArg(v_t_355_, v_any_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_any_elim(lean_object* v_motive_358_, lean_object* v_t_359_, lean_object* v_h_360_, lean_object* v_any_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_Time_Year_ctorElim___redArg(v_t_359_, v_any_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_twoDigit_elim___redArg(lean_object* v_t_363_, lean_object* v_twoDigit_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_Time_Year_ctorElim___redArg(v_t_363_, v_twoDigit_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_twoDigit_elim(lean_object* v_motive_366_, lean_object* v_t_367_, lean_object* v_h_368_, lean_object* v_twoDigit_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_Time_Year_ctorElim___redArg(v_t_367_, v_twoDigit_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_fourDigit_elim___redArg(lean_object* v_t_371_, lean_object* v_fourDigit_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Std_Time_Year_ctorElim___redArg(v_t_371_, v_fourDigit_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_fourDigit_elim(lean_object* v_motive_374_, lean_object* v_t_375_, lean_object* v_h_376_, lean_object* v_fourDigit_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_Time_Year_ctorElim___redArg(v_t_375_, v_fourDigit_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_extended_elim___redArg(lean_object* v_t_379_, lean_object* v_extended_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_Time_Year_ctorElim___redArg(v_t_379_, v_extended_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_extended_elim(lean_object* v_motive_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_extended_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_Time_Year_ctorElim___redArg(v_t_383_, v_extended_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprYear_repr(lean_object* v_x_402_, lean_object* v_prec_403_){
_start:
{
lean_object* v___y_405_; lean_object* v___y_412_; lean_object* v___y_419_; 
switch(lean_obj_tag(v_x_402_))
{
case 0:
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_unsigned_to_nat(1024u);
v___x_426_ = lean_nat_dec_le(v___x_425_, v_prec_403_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
v___x_427_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_419_ = v___x_427_;
goto v___jp_418_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_419_ = v___x_428_;
goto v___jp_418_;
}
}
case 1:
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(1024u);
v___x_430_ = lean_nat_dec_le(v___x_429_, v_prec_403_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_412_ = v___x_431_;
goto v___jp_411_;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_412_ = v___x_432_;
goto v___jp_411_;
}
}
case 2:
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(1024u);
v___x_434_ = lean_nat_dec_le(v___x_433_, v_prec_403_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_405_ = v___x_435_;
goto v___jp_404_;
}
else
{
lean_object* v___x_436_; 
v___x_436_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_405_ = v___x_436_;
goto v___jp_404_;
}
}
default: 
{
lean_object* v_num_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_457_; 
v_num_437_ = lean_ctor_get(v_x_402_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_402_);
if (v_isSharedCheck_457_ == 0)
{
v___x_439_ = v_x_402_;
v_isShared_440_ = v_isSharedCheck_457_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_num_437_);
lean_dec(v_x_402_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_457_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___y_442_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(1024u);
v___x_454_ = lean_nat_dec_le(v___x_453_, v_prec_403_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_442_ = v___x_455_;
goto v___jp_441_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_442_ = v___x_456_;
goto v___jp_441_;
}
v___jp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_443_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__8));
v___x_444_ = l_Nat_reprFast(v_num_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_444_);
v___x_446_ = v___x_439_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_452_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_443_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
lean_inc(v___y_442_);
v___x_448_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_448_, 0, v___y_442_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = 0;
v___x_450_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*1, v___x_449_);
v___x_451_ = l_Repr_addAppParen(v___x_450_, v_prec_403_);
return v___x_451_;
}
}
}
}
}
v___jp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_406_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__1));
lean_inc(v___y_405_);
v___x_407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_407_, 0, v___y_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = 0;
v___x_409_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*1, v___x_408_);
v___x_410_ = l_Repr_addAppParen(v___x_409_, v_prec_403_);
return v___x_410_;
}
v___jp_411_:
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_413_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__3));
lean_inc(v___y_412_);
v___x_414_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_414_, 0, v___y_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = 0;
v___x_416_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*1, v___x_415_);
v___x_417_ = l_Repr_addAppParen(v___x_416_, v_prec_403_);
return v___x_417_;
}
v___jp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__5));
lean_inc(v___y_419_);
v___x_421_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_421_, 0, v___y_419_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = 0;
v___x_423_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*1, v___x_422_);
v___x_424_ = l_Repr_addAppParen(v___x_423_, v_prec_403_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprYear_repr___boxed(lean_object* v_x_458_, lean_object* v_prec_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_Time_instReprYear_repr(v_x_458_, v_prec_459_);
lean_dec(v_prec_459_);
return v_res_460_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedYear_default(void){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_box(0);
return v___x_463_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedYear(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_box(0);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_classify(lean_object* v_num_471_){
_start:
{
uint8_t v___y_473_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_nat_dec_eq(v_num_471_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = lean_nat_dec_eq(v_num_471_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(4u);
v___x_482_ = lean_nat_dec_eq(v_num_471_, v___x_481_);
if (v___x_482_ == 0)
{
uint8_t v___x_483_; 
v___x_483_ = lean_nat_dec_lt(v___x_481_, v_num_471_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(3u);
v___x_485_ = lean_nat_dec_eq(v_num_471_, v___x_484_);
v___y_473_ = v___x_485_;
goto v___jp_472_;
}
else
{
v___y_473_ = v___x_483_;
goto v___jp_472_;
}
}
else
{
lean_object* v___x_486_; 
lean_dec(v_num_471_);
v___x_486_ = ((lean_object*)(l_Std_Time_Year_classify___closed__0));
return v___x_486_;
}
}
else
{
lean_object* v___x_487_; 
lean_dec(v_num_471_);
v___x_487_ = ((lean_object*)(l_Std_Time_Year_classify___closed__1));
return v___x_487_;
}
}
else
{
lean_object* v___x_488_; 
lean_dec(v_num_471_);
v___x_488_ = ((lean_object*)(l_Std_Time_Year_classify___closed__2));
return v___x_488_;
}
v___jp_472_:
{
if (v___y_473_ == 0)
{
lean_object* v___x_474_; 
lean_dec(v_num_471_);
v___x_474_ = lean_box(0);
return v___x_474_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_475_, 0, v_num_471_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx(uint8_t v_x_489_){
_start:
{
switch(v_x_489_)
{
case 0:
{
lean_object* v___x_490_; 
v___x_490_ = lean_unsigned_to_nat(0u);
return v___x_490_;
}
case 1:
{
lean_object* v___x_491_; 
v___x_491_ = lean_unsigned_to_nat(1u);
return v___x_491_;
}
default: 
{
lean_object* v___x_492_; 
v___x_492_ = lean_unsigned_to_nat(2u);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx___boxed(lean_object* v_x_493_){
_start:
{
uint8_t v_x_boxed_494_; lean_object* v_res_495_; 
v_x_boxed_494_ = lean_unbox(v_x_493_);
v_res_495_ = l_Std_Time_ZoneId_ctorIdx(v_x_boxed_494_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___redArg(lean_object* v_k_496_){
_start:
{
lean_inc(v_k_496_);
return v_k_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___redArg___boxed(lean_object* v_k_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_Time_ZoneId_ctorElim___redArg(v_k_497_);
lean_dec(v_k_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim(lean_object* v_motive_499_, lean_object* v_ctorIdx_500_, uint8_t v_t_501_, lean_object* v_h_502_, lean_object* v_k_503_){
_start:
{
lean_inc(v_k_503_);
return v_k_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___boxed(lean_object* v_motive_504_, lean_object* v_ctorIdx_505_, lean_object* v_t_506_, lean_object* v_h_507_, lean_object* v_k_508_){
_start:
{
uint8_t v_t_boxed_509_; lean_object* v_res_510_; 
v_t_boxed_509_ = lean_unbox(v_t_506_);
v_res_510_ = l_Std_Time_ZoneId_ctorElim(v_motive_504_, v_ctorIdx_505_, v_t_boxed_509_, v_h_507_, v_k_508_);
lean_dec(v_k_508_);
lean_dec(v_ctorIdx_505_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg(lean_object* v_unknown_511_){
_start:
{
lean_inc(v_unknown_511_);
return v_unknown_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg___boxed(lean_object* v_unknown_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_Time_ZoneId_unknown_elim___redArg(v_unknown_512_);
lean_dec(v_unknown_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim(lean_object* v_motive_514_, uint8_t v_t_515_, lean_object* v_h_516_, lean_object* v_unknown_517_){
_start:
{
lean_inc(v_unknown_517_);
return v_unknown_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___boxed(lean_object* v_motive_518_, lean_object* v_t_519_, lean_object* v_h_520_, lean_object* v_unknown_521_){
_start:
{
uint8_t v_t_boxed_522_; lean_object* v_res_523_; 
v_t_boxed_522_ = lean_unbox(v_t_519_);
v_res_523_ = l_Std_Time_ZoneId_unknown_elim(v_motive_518_, v_t_boxed_522_, v_h_520_, v_unknown_521_);
lean_dec(v_unknown_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg(lean_object* v_short_524_){
_start:
{
lean_inc(v_short_524_);
return v_short_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg___boxed(lean_object* v_short_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_Time_ZoneId_short_elim___redArg(v_short_525_);
lean_dec(v_short_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim(lean_object* v_motive_527_, uint8_t v_t_528_, lean_object* v_h_529_, lean_object* v_short_530_){
_start:
{
lean_inc(v_short_530_);
return v_short_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___boxed(lean_object* v_motive_531_, lean_object* v_t_532_, lean_object* v_h_533_, lean_object* v_short_534_){
_start:
{
uint8_t v_t_boxed_535_; lean_object* v_res_536_; 
v_t_boxed_535_ = lean_unbox(v_t_532_);
v_res_536_ = l_Std_Time_ZoneId_short_elim(v_motive_531_, v_t_boxed_535_, v_h_533_, v_short_534_);
lean_dec(v_short_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg(lean_object* v_full_537_){
_start:
{
lean_inc(v_full_537_);
return v_full_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg___boxed(lean_object* v_full_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Std_Time_ZoneId_full_elim___redArg(v_full_538_);
lean_dec(v_full_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim(lean_object* v_motive_540_, uint8_t v_t_541_, lean_object* v_h_542_, lean_object* v_full_543_){
_start:
{
lean_inc(v_full_543_);
return v_full_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___boxed(lean_object* v_motive_544_, lean_object* v_t_545_, lean_object* v_h_546_, lean_object* v_full_547_){
_start:
{
uint8_t v_t_boxed_548_; lean_object* v_res_549_; 
v_t_boxed_548_ = lean_unbox(v_t_545_);
v_res_549_ = l_Std_Time_ZoneId_full_elim(v_motive_544_, v_t_boxed_548_, v_h_546_, v_full_547_);
lean_dec(v_full_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr(uint8_t v_x_559_, lean_object* v_prec_560_){
_start:
{
lean_object* v___y_562_; lean_object* v___y_569_; lean_object* v___y_576_; 
switch(v_x_559_)
{
case 0:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1024u);
v___x_583_ = lean_nat_dec_le(v___x_582_, v_prec_560_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_562_ = v___x_584_;
goto v___jp_561_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_562_ = v___x_585_;
goto v___jp_561_;
}
}
case 1:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1024u);
v___x_587_ = lean_nat_dec_le(v___x_586_, v_prec_560_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_569_ = v___x_588_;
goto v___jp_568_;
}
else
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_569_ = v___x_589_;
goto v___jp_568_;
}
}
default: 
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(1024u);
v___x_591_ = lean_nat_dec_le(v___x_590_, v_prec_560_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_576_ = v___x_592_;
goto v___jp_575_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_576_ = v___x_593_;
goto v___jp_575_;
}
}
}
v___jp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_563_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__1));
lean_inc(v___y_562_);
v___x_564_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_564_, 0, v___y_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = 0;
v___x_566_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_565_);
v___x_567_ = l_Repr_addAppParen(v___x_566_, v_prec_560_);
return v___x_567_;
}
v___jp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_570_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__3));
lean_inc(v___y_569_);
v___x_571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_571_, 0, v___y_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = 0;
v___x_573_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*1, v___x_572_);
v___x_574_ = l_Repr_addAppParen(v___x_573_, v_prec_560_);
return v___x_574_;
}
v___jp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_577_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__5));
lean_inc(v___y_576_);
v___x_578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_578_, 0, v___y_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = 0;
v___x_580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*1, v___x_579_);
v___x_581_ = l_Repr_addAppParen(v___x_580_, v_prec_560_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr___boxed(lean_object* v_x_594_, lean_object* v_prec_595_){
_start:
{
uint8_t v_x_167__boxed_596_; lean_object* v_res_597_; 
v_x_167__boxed_596_ = lean_unbox(v_x_594_);
v_res_597_ = l_Std_Time_instReprZoneId_repr(v_x_167__boxed_596_, v_prec_595_);
lean_dec(v_prec_595_);
return v_res_597_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneId_default(void){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = 0;
return v___x_600_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneId(void){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = 0;
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify(lean_object* v_num_611_){
_start:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_dec_eq(v_num_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(2u);
v___x_615_ = lean_nat_dec_eq(v_num_611_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(4u);
v___x_617_ = lean_nat_dec_eq(v_num_611_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_box(0);
return v___x_618_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__0));
return v___x_619_;
}
}
else
{
lean_object* v___x_620_; 
v___x_620_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__1));
return v___x_620_;
}
}
else
{
lean_object* v___x_621_; 
v___x_621_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__2));
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify___boxed(lean_object* v_num_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_Time_ZoneId_classify(v_num_622_);
lean_dec(v_num_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx(uint8_t v_x_624_){
_start:
{
if (v_x_624_ == 0)
{
lean_object* v___x_625_; 
v___x_625_ = lean_unsigned_to_nat(0u);
return v___x_625_;
}
else
{
lean_object* v___x_626_; 
v___x_626_ = lean_unsigned_to_nat(1u);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx___boxed(lean_object* v_x_627_){
_start:
{
uint8_t v_x_boxed_628_; lean_object* v_res_629_; 
v_x_boxed_628_ = lean_unbox(v_x_627_);
v_res_629_ = l_Std_Time_ZoneName_ctorIdx(v_x_boxed_628_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg(lean_object* v_k_630_){
_start:
{
lean_inc(v_k_630_);
return v_k_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg___boxed(lean_object* v_k_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_Time_ZoneName_ctorElim___redArg(v_k_631_);
lean_dec(v_k_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim(lean_object* v_motive_633_, lean_object* v_ctorIdx_634_, uint8_t v_t_635_, lean_object* v_h_636_, lean_object* v_k_637_){
_start:
{
lean_inc(v_k_637_);
return v_k_637_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___boxed(lean_object* v_motive_638_, lean_object* v_ctorIdx_639_, lean_object* v_t_640_, lean_object* v_h_641_, lean_object* v_k_642_){
_start:
{
uint8_t v_t_boxed_643_; lean_object* v_res_644_; 
v_t_boxed_643_ = lean_unbox(v_t_640_);
v_res_644_ = l_Std_Time_ZoneName_ctorElim(v_motive_638_, v_ctorIdx_639_, v_t_boxed_643_, v_h_641_, v_k_642_);
lean_dec(v_k_642_);
lean_dec(v_ctorIdx_639_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg(lean_object* v_short_645_){
_start:
{
lean_inc(v_short_645_);
return v_short_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg___boxed(lean_object* v_short_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_Time_ZoneName_short_elim___redArg(v_short_646_);
lean_dec(v_short_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim(lean_object* v_motive_648_, uint8_t v_t_649_, lean_object* v_h_650_, lean_object* v_short_651_){
_start:
{
lean_inc(v_short_651_);
return v_short_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___boxed(lean_object* v_motive_652_, lean_object* v_t_653_, lean_object* v_h_654_, lean_object* v_short_655_){
_start:
{
uint8_t v_t_boxed_656_; lean_object* v_res_657_; 
v_t_boxed_656_ = lean_unbox(v_t_653_);
v_res_657_ = l_Std_Time_ZoneName_short_elim(v_motive_652_, v_t_boxed_656_, v_h_654_, v_short_655_);
lean_dec(v_short_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg(lean_object* v_full_658_){
_start:
{
lean_inc(v_full_658_);
return v_full_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg___boxed(lean_object* v_full_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_Time_ZoneName_full_elim___redArg(v_full_659_);
lean_dec(v_full_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim(lean_object* v_motive_661_, uint8_t v_t_662_, lean_object* v_h_663_, lean_object* v_full_664_){
_start:
{
lean_inc(v_full_664_);
return v_full_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___boxed(lean_object* v_motive_665_, lean_object* v_t_666_, lean_object* v_h_667_, lean_object* v_full_668_){
_start:
{
uint8_t v_t_boxed_669_; lean_object* v_res_670_; 
v_t_boxed_669_ = lean_unbox(v_t_666_);
v_res_670_ = l_Std_Time_ZoneName_full_elim(v_motive_665_, v_t_boxed_669_, v_h_667_, v_full_668_);
lean_dec(v_full_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr(uint8_t v_x_677_, lean_object* v_prec_678_){
_start:
{
lean_object* v___y_680_; lean_object* v___y_687_; 
if (v_x_677_ == 0)
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(1024u);
v___x_694_ = lean_nat_dec_le(v___x_693_, v_prec_678_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_680_ = v___x_695_;
goto v___jp_679_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_680_ = v___x_696_;
goto v___jp_679_;
}
}
else
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = lean_unsigned_to_nat(1024u);
v___x_698_ = lean_nat_dec_le(v___x_697_, v_prec_678_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
v___x_699_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_687_ = v___x_699_;
goto v___jp_686_;
}
else
{
lean_object* v___x_700_; 
v___x_700_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_687_ = v___x_700_;
goto v___jp_686_;
}
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_681_ = ((lean_object*)(l_Std_Time_instReprZoneName_repr___closed__1));
lean_inc(v___y_680_);
v___x_682_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = 0;
v___x_684_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*1, v___x_683_);
v___x_685_ = l_Repr_addAppParen(v___x_684_, v_prec_678_);
return v___x_685_;
}
v___jp_686_:
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_688_ = ((lean_object*)(l_Std_Time_instReprZoneName_repr___closed__3));
lean_inc(v___y_687_);
v___x_689_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_689_, 0, v___y_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = 0;
v___x_691_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*1, v___x_690_);
v___x_692_ = l_Repr_addAppParen(v___x_691_, v_prec_678_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr___boxed(lean_object* v_x_701_, lean_object* v_prec_702_){
_start:
{
uint8_t v_x_113__boxed_703_; lean_object* v_res_704_; 
v_x_113__boxed_703_ = lean_unbox(v_x_701_);
v_res_704_ = l_Std_Time_instReprZoneName_repr(v_x_113__boxed_703_, v_prec_702_);
lean_dec(v_prec_702_);
return v_res_704_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneName_default(void){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = 0;
return v___x_707_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneName(void){
_start:
{
uint8_t v___x_708_; 
v___x_708_ = 0;
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify(uint32_t v_letter_715_, lean_object* v_num_716_){
_start:
{
uint32_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 122;
v___x_718_ = lean_uint32_dec_eq(v_letter_715_, v___x_717_);
if (v___x_718_ == 0)
{
uint32_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 118;
v___x_720_ = lean_uint32_dec_eq(v_letter_715_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
v___x_721_ = lean_box(0);
return v___x_721_;
}
else
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_unsigned_to_nat(1u);
v___x_723_ = lean_nat_dec_eq(v_num_716_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(4u);
v___x_725_ = lean_nat_dec_eq(v_num_716_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
v___x_726_ = lean_box(0);
return v___x_726_;
}
else
{
lean_object* v___x_727_; 
v___x_727_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__0));
return v___x_727_;
}
}
else
{
lean_object* v___x_728_; 
v___x_728_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__1));
return v___x_728_;
}
}
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(4u);
v___x_730_ = lean_nat_dec_lt(v_num_716_, v___x_729_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
v___x_731_ = lean_nat_dec_eq(v_num_716_, v___x_729_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
return v___x_732_;
}
else
{
lean_object* v___x_733_; 
v___x_733_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__0));
return v___x_733_;
}
}
else
{
lean_object* v___x_734_; 
v___x_734_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__1));
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify___boxed(lean_object* v_letter_735_, lean_object* v_num_736_){
_start:
{
uint32_t v_letter_boxed_737_; lean_object* v_res_738_; 
v_letter_boxed_737_ = lean_unbox_uint32(v_letter_735_);
lean_dec(v_letter_735_);
v_res_738_ = l_Std_Time_ZoneName_classify(v_letter_boxed_737_, v_num_736_);
lean_dec(v_num_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx(uint8_t v_x_739_){
_start:
{
switch(v_x_739_)
{
case 0:
{
lean_object* v___x_740_; 
v___x_740_ = lean_unsigned_to_nat(0u);
return v___x_740_;
}
case 1:
{
lean_object* v___x_741_; 
v___x_741_ = lean_unsigned_to_nat(1u);
return v___x_741_;
}
case 2:
{
lean_object* v___x_742_; 
v___x_742_ = lean_unsigned_to_nat(2u);
return v___x_742_;
}
case 3:
{
lean_object* v___x_743_; 
v___x_743_ = lean_unsigned_to_nat(3u);
return v___x_743_;
}
default: 
{
lean_object* v___x_744_; 
v___x_744_ = lean_unsigned_to_nat(4u);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx___boxed(lean_object* v_x_745_){
_start:
{
uint8_t v_x_boxed_746_; lean_object* v_res_747_; 
v_x_boxed_746_ = lean_unbox(v_x_745_);
v_res_747_ = l_Std_Time_OffsetX_ctorIdx(v_x_boxed_746_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg(lean_object* v_k_748_){
_start:
{
lean_inc(v_k_748_);
return v_k_748_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg___boxed(lean_object* v_k_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_Time_OffsetX_ctorElim___redArg(v_k_749_);
lean_dec(v_k_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim(lean_object* v_motive_751_, lean_object* v_ctorIdx_752_, uint8_t v_t_753_, lean_object* v_h_754_, lean_object* v_k_755_){
_start:
{
lean_inc(v_k_755_);
return v_k_755_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___boxed(lean_object* v_motive_756_, lean_object* v_ctorIdx_757_, lean_object* v_t_758_, lean_object* v_h_759_, lean_object* v_k_760_){
_start:
{
uint8_t v_t_boxed_761_; lean_object* v_res_762_; 
v_t_boxed_761_ = lean_unbox(v_t_758_);
v_res_762_ = l_Std_Time_OffsetX_ctorElim(v_motive_756_, v_ctorIdx_757_, v_t_boxed_761_, v_h_759_, v_k_760_);
lean_dec(v_k_760_);
lean_dec(v_ctorIdx_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg(lean_object* v_hour_763_){
_start:
{
lean_inc(v_hour_763_);
return v_hour_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg___boxed(lean_object* v_hour_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_Time_OffsetX_hour_elim___redArg(v_hour_764_);
lean_dec(v_hour_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim(lean_object* v_motive_766_, uint8_t v_t_767_, lean_object* v_h_768_, lean_object* v_hour_769_){
_start:
{
lean_inc(v_hour_769_);
return v_hour_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___boxed(lean_object* v_motive_770_, lean_object* v_t_771_, lean_object* v_h_772_, lean_object* v_hour_773_){
_start:
{
uint8_t v_t_boxed_774_; lean_object* v_res_775_; 
v_t_boxed_774_ = lean_unbox(v_t_771_);
v_res_775_ = l_Std_Time_OffsetX_hour_elim(v_motive_770_, v_t_boxed_774_, v_h_772_, v_hour_773_);
lean_dec(v_hour_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg(lean_object* v_hourMinute_776_){
_start:
{
lean_inc(v_hourMinute_776_);
return v_hourMinute_776_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg___boxed(lean_object* v_hourMinute_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_Time_OffsetX_hourMinute_elim___redArg(v_hourMinute_777_);
lean_dec(v_hourMinute_777_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim(lean_object* v_motive_779_, uint8_t v_t_780_, lean_object* v_h_781_, lean_object* v_hourMinute_782_){
_start:
{
lean_inc(v_hourMinute_782_);
return v_hourMinute_782_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___boxed(lean_object* v_motive_783_, lean_object* v_t_784_, lean_object* v_h_785_, lean_object* v_hourMinute_786_){
_start:
{
uint8_t v_t_boxed_787_; lean_object* v_res_788_; 
v_t_boxed_787_ = lean_unbox(v_t_784_);
v_res_788_ = l_Std_Time_OffsetX_hourMinute_elim(v_motive_783_, v_t_boxed_787_, v_h_785_, v_hourMinute_786_);
lean_dec(v_hourMinute_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(lean_object* v_hourMinuteColon_789_){
_start:
{
lean_inc(v_hourMinuteColon_789_);
return v_hourMinuteColon_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg___boxed(lean_object* v_hourMinuteColon_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(v_hourMinuteColon_790_);
lean_dec(v_hourMinuteColon_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim(lean_object* v_motive_792_, uint8_t v_t_793_, lean_object* v_h_794_, lean_object* v_hourMinuteColon_795_){
_start:
{
lean_inc(v_hourMinuteColon_795_);
return v_hourMinuteColon_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___boxed(lean_object* v_motive_796_, lean_object* v_t_797_, lean_object* v_h_798_, lean_object* v_hourMinuteColon_799_){
_start:
{
uint8_t v_t_boxed_800_; lean_object* v_res_801_; 
v_t_boxed_800_ = lean_unbox(v_t_797_);
v_res_801_ = l_Std_Time_OffsetX_hourMinuteColon_elim(v_motive_796_, v_t_boxed_800_, v_h_798_, v_hourMinuteColon_799_);
lean_dec(v_hourMinuteColon_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(lean_object* v_hourMinuteSecond_802_){
_start:
{
lean_inc(v_hourMinuteSecond_802_);
return v_hourMinuteSecond_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg___boxed(lean_object* v_hourMinuteSecond_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(v_hourMinuteSecond_803_);
lean_dec(v_hourMinuteSecond_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim(lean_object* v_motive_805_, uint8_t v_t_806_, lean_object* v_h_807_, lean_object* v_hourMinuteSecond_808_){
_start:
{
lean_inc(v_hourMinuteSecond_808_);
return v_hourMinuteSecond_808_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___boxed(lean_object* v_motive_809_, lean_object* v_t_810_, lean_object* v_h_811_, lean_object* v_hourMinuteSecond_812_){
_start:
{
uint8_t v_t_boxed_813_; lean_object* v_res_814_; 
v_t_boxed_813_ = lean_unbox(v_t_810_);
v_res_814_ = l_Std_Time_OffsetX_hourMinuteSecond_elim(v_motive_809_, v_t_boxed_813_, v_h_811_, v_hourMinuteSecond_812_);
lean_dec(v_hourMinuteSecond_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(lean_object* v_hourMinuteSecondColon_815_){
_start:
{
lean_inc(v_hourMinuteSecondColon_815_);
return v_hourMinuteSecondColon_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg___boxed(lean_object* v_hourMinuteSecondColon_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(v_hourMinuteSecondColon_816_);
lean_dec(v_hourMinuteSecondColon_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim(lean_object* v_motive_818_, uint8_t v_t_819_, lean_object* v_h_820_, lean_object* v_hourMinuteSecondColon_821_){
_start:
{
lean_inc(v_hourMinuteSecondColon_821_);
return v_hourMinuteSecondColon_821_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___boxed(lean_object* v_motive_822_, lean_object* v_t_823_, lean_object* v_h_824_, lean_object* v_hourMinuteSecondColon_825_){
_start:
{
uint8_t v_t_boxed_826_; lean_object* v_res_827_; 
v_t_boxed_826_ = lean_unbox(v_t_823_);
v_res_827_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim(v_motive_822_, v_t_boxed_826_, v_h_824_, v_hourMinuteSecondColon_825_);
lean_dec(v_hourMinuteSecondColon_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr(uint8_t v_x_843_, lean_object* v_prec_844_){
_start:
{
lean_object* v___y_846_; lean_object* v___y_853_; lean_object* v___y_860_; lean_object* v___y_867_; lean_object* v___y_874_; 
switch(v_x_843_)
{
case 0:
{
lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(1024u);
v___x_881_ = lean_nat_dec_le(v___x_880_, v_prec_844_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_846_ = v___x_882_;
goto v___jp_845_;
}
else
{
lean_object* v___x_883_; 
v___x_883_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_846_ = v___x_883_;
goto v___jp_845_;
}
}
case 1:
{
lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(1024u);
v___x_885_ = lean_nat_dec_le(v___x_884_, v_prec_844_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
v___x_886_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_853_ = v___x_886_;
goto v___jp_852_;
}
else
{
lean_object* v___x_887_; 
v___x_887_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_853_ = v___x_887_;
goto v___jp_852_;
}
}
case 2:
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_unsigned_to_nat(1024u);
v___x_889_ = lean_nat_dec_le(v___x_888_, v_prec_844_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
v___x_890_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_860_ = v___x_890_;
goto v___jp_859_;
}
else
{
lean_object* v___x_891_; 
v___x_891_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_860_ = v___x_891_;
goto v___jp_859_;
}
}
case 3:
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_unsigned_to_nat(1024u);
v___x_893_ = lean_nat_dec_le(v___x_892_, v_prec_844_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
v___x_894_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_867_ = v___x_894_;
goto v___jp_866_;
}
else
{
lean_object* v___x_895_; 
v___x_895_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_867_ = v___x_895_;
goto v___jp_866_;
}
}
default: 
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = lean_unsigned_to_nat(1024u);
v___x_897_ = lean_nat_dec_le(v___x_896_, v_prec_844_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
v___x_898_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_874_ = v___x_898_;
goto v___jp_873_;
}
else
{
lean_object* v___x_899_; 
v___x_899_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_874_ = v___x_899_;
goto v___jp_873_;
}
}
}
v___jp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_847_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__1));
lean_inc(v___y_846_);
v___x_848_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_848_, 0, v___y_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = 0;
v___x_850_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*1, v___x_849_);
v___x_851_ = l_Repr_addAppParen(v___x_850_, v_prec_844_);
return v___x_851_;
}
v___jp_852_:
{
lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_854_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__3));
lean_inc(v___y_853_);
v___x_855_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_855_, 0, v___y_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = 0;
v___x_857_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*1, v___x_856_);
v___x_858_ = l_Repr_addAppParen(v___x_857_, v_prec_844_);
return v___x_858_;
}
v___jp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_861_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__5));
lean_inc(v___y_860_);
v___x_862_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_862_, 0, v___y_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = 0;
v___x_864_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set_uint8(v___x_864_, sizeof(void*)*1, v___x_863_);
v___x_865_ = l_Repr_addAppParen(v___x_864_, v_prec_844_);
return v___x_865_;
}
v___jp_866_:
{
lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_868_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__7));
lean_inc(v___y_867_);
v___x_869_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_869_, 0, v___y_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = 0;
v___x_871_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*1, v___x_870_);
v___x_872_ = l_Repr_addAppParen(v___x_871_, v_prec_844_);
return v___x_872_;
}
v___jp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_875_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__9));
lean_inc(v___y_874_);
v___x_876_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_876_, 0, v___y_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = 0;
v___x_878_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set_uint8(v___x_878_, sizeof(void*)*1, v___x_877_);
v___x_879_ = l_Repr_addAppParen(v___x_878_, v_prec_844_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr___boxed(lean_object* v_x_900_, lean_object* v_prec_901_){
_start:
{
uint8_t v_x_275__boxed_902_; lean_object* v_res_903_; 
v_x_275__boxed_902_ = lean_unbox(v_x_900_);
v_res_903_ = l_Std_Time_instReprOffsetX_repr(v_x_275__boxed_902_, v_prec_901_);
lean_dec(v_prec_901_);
return v_res_903_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetX_default(void){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = 0;
return v___x_906_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetX(void){
_start:
{
uint8_t v___x_907_; 
v___x_907_ = 0;
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify(lean_object* v_num_923_){
_start:
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_dec_eq(v_num_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = lean_unsigned_to_nat(2u);
v___x_927_ = lean_nat_dec_eq(v_num_923_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(3u);
v___x_929_ = lean_nat_dec_eq(v_num_923_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = lean_unsigned_to_nat(4u);
v___x_931_ = lean_nat_dec_eq(v_num_923_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = lean_unsigned_to_nat(5u);
v___x_933_ = lean_nat_dec_eq(v_num_923_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; 
v___x_934_ = lean_box(0);
return v___x_934_;
}
else
{
lean_object* v___x_935_; 
v___x_935_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__0));
return v___x_935_;
}
}
else
{
lean_object* v___x_936_; 
v___x_936_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__1));
return v___x_936_;
}
}
else
{
lean_object* v___x_937_; 
v___x_937_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__2));
return v___x_937_;
}
}
else
{
lean_object* v___x_938_; 
v___x_938_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__3));
return v___x_938_;
}
}
else
{
lean_object* v___x_939_; 
v___x_939_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__4));
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify___boxed(lean_object* v_num_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_Time_OffsetX_classify(v_num_940_);
lean_dec(v_num_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx(uint8_t v_x_942_){
_start:
{
if (v_x_942_ == 0)
{
lean_object* v___x_943_; 
v___x_943_ = lean_unsigned_to_nat(0u);
return v___x_943_;
}
else
{
lean_object* v___x_944_; 
v___x_944_ = lean_unsigned_to_nat(1u);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx___boxed(lean_object* v_x_945_){
_start:
{
uint8_t v_x_boxed_946_; lean_object* v_res_947_; 
v_x_boxed_946_ = lean_unbox(v_x_945_);
v_res_947_ = l_Std_Time_OffsetO_ctorIdx(v_x_boxed_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg(lean_object* v_k_948_){
_start:
{
lean_inc(v_k_948_);
return v_k_948_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg___boxed(lean_object* v_k_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Std_Time_OffsetO_ctorElim___redArg(v_k_949_);
lean_dec(v_k_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim(lean_object* v_motive_951_, lean_object* v_ctorIdx_952_, uint8_t v_t_953_, lean_object* v_h_954_, lean_object* v_k_955_){
_start:
{
lean_inc(v_k_955_);
return v_k_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___boxed(lean_object* v_motive_956_, lean_object* v_ctorIdx_957_, lean_object* v_t_958_, lean_object* v_h_959_, lean_object* v_k_960_){
_start:
{
uint8_t v_t_boxed_961_; lean_object* v_res_962_; 
v_t_boxed_961_ = lean_unbox(v_t_958_);
v_res_962_ = l_Std_Time_OffsetO_ctorElim(v_motive_956_, v_ctorIdx_957_, v_t_boxed_961_, v_h_959_, v_k_960_);
lean_dec(v_k_960_);
lean_dec(v_ctorIdx_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg(lean_object* v_short_963_){
_start:
{
lean_inc(v_short_963_);
return v_short_963_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg___boxed(lean_object* v_short_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_Time_OffsetO_short_elim___redArg(v_short_964_);
lean_dec(v_short_964_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim(lean_object* v_motive_966_, uint8_t v_t_967_, lean_object* v_h_968_, lean_object* v_short_969_){
_start:
{
lean_inc(v_short_969_);
return v_short_969_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___boxed(lean_object* v_motive_970_, lean_object* v_t_971_, lean_object* v_h_972_, lean_object* v_short_973_){
_start:
{
uint8_t v_t_boxed_974_; lean_object* v_res_975_; 
v_t_boxed_974_ = lean_unbox(v_t_971_);
v_res_975_ = l_Std_Time_OffsetO_short_elim(v_motive_970_, v_t_boxed_974_, v_h_972_, v_short_973_);
lean_dec(v_short_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg(lean_object* v_full_976_){
_start:
{
lean_inc(v_full_976_);
return v_full_976_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg___boxed(lean_object* v_full_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_Time_OffsetO_full_elim___redArg(v_full_977_);
lean_dec(v_full_977_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim(lean_object* v_motive_979_, uint8_t v_t_980_, lean_object* v_h_981_, lean_object* v_full_982_){
_start:
{
lean_inc(v_full_982_);
return v_full_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___boxed(lean_object* v_motive_983_, lean_object* v_t_984_, lean_object* v_h_985_, lean_object* v_full_986_){
_start:
{
uint8_t v_t_boxed_987_; lean_object* v_res_988_; 
v_t_boxed_987_ = lean_unbox(v_t_984_);
v_res_988_ = l_Std_Time_OffsetO_full_elim(v_motive_983_, v_t_boxed_987_, v_h_985_, v_full_986_);
lean_dec(v_full_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr(uint8_t v_x_995_, lean_object* v_prec_996_){
_start:
{
lean_object* v___y_998_; lean_object* v___y_1005_; 
if (v_x_995_ == 0)
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = lean_unsigned_to_nat(1024u);
v___x_1012_ = lean_nat_dec_le(v___x_1011_, v_prec_996_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_998_ = v___x_1013_;
goto v___jp_997_;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_998_ = v___x_1014_;
goto v___jp_997_;
}
}
else
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(1024u);
v___x_1016_ = lean_nat_dec_le(v___x_1015_, v_prec_996_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1005_ = v___x_1017_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1005_ = v___x_1018_;
goto v___jp_1004_;
}
}
v___jp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_999_ = ((lean_object*)(l_Std_Time_instReprOffsetO_repr___closed__1));
lean_inc(v___y_998_);
v___x_1000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___y_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = 0;
v___x_1002_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*1, v___x_1001_);
v___x_1003_ = l_Repr_addAppParen(v___x_1002_, v_prec_996_);
return v___x_1003_;
}
v___jp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1006_ = ((lean_object*)(l_Std_Time_instReprOffsetO_repr___closed__3));
lean_inc(v___y_1005_);
v___x_1007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___y_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = 0;
v___x_1009_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*1, v___x_1008_);
v___x_1010_ = l_Repr_addAppParen(v___x_1009_, v_prec_996_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr___boxed(lean_object* v_x_1019_, lean_object* v_prec_1020_){
_start:
{
uint8_t v_x_113__boxed_1021_; lean_object* v_res_1022_; 
v_x_113__boxed_1021_ = lean_unbox(v_x_1019_);
v_res_1022_ = l_Std_Time_instReprOffsetO_repr(v_x_113__boxed_1021_, v_prec_1020_);
lean_dec(v_prec_1020_);
return v_res_1022_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetO_default(void){
_start:
{
uint8_t v___x_1025_; 
v___x_1025_ = 0;
return v___x_1025_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetO(void){
_start:
{
uint8_t v___x_1026_; 
v___x_1026_ = 0;
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify(lean_object* v_num_1033_){
_start:
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_unsigned_to_nat(1u);
v___x_1035_ = lean_nat_dec_eq(v_num_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = lean_unsigned_to_nat(4u);
v___x_1037_ = lean_nat_dec_eq(v_num_1033_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_box(0);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Std_Time_OffsetO_classify___closed__0));
return v___x_1039_;
}
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l_Std_Time_OffsetO_classify___closed__1));
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify___boxed(lean_object* v_num_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Std_Time_OffsetO_classify(v_num_1041_);
lean_dec(v_num_1041_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx(uint8_t v_x_1043_){
_start:
{
switch(v_x_1043_)
{
case 0:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_unsigned_to_nat(0u);
return v___x_1044_;
}
case 1:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_unsigned_to_nat(1u);
return v___x_1045_;
}
default: 
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_unsigned_to_nat(2u);
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx___boxed(lean_object* v_x_1047_){
_start:
{
uint8_t v_x_boxed_1048_; lean_object* v_res_1049_; 
v_x_boxed_1048_ = lean_unbox(v_x_1047_);
v_res_1049_ = l_Std_Time_OffsetZ_ctorIdx(v_x_boxed_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg(lean_object* v_k_1050_){
_start:
{
lean_inc(v_k_1050_);
return v_k_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg___boxed(lean_object* v_k_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Std_Time_OffsetZ_ctorElim___redArg(v_k_1051_);
lean_dec(v_k_1051_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim(lean_object* v_motive_1053_, lean_object* v_ctorIdx_1054_, uint8_t v_t_1055_, lean_object* v_h_1056_, lean_object* v_k_1057_){
_start:
{
lean_inc(v_k_1057_);
return v_k_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___boxed(lean_object* v_motive_1058_, lean_object* v_ctorIdx_1059_, lean_object* v_t_1060_, lean_object* v_h_1061_, lean_object* v_k_1062_){
_start:
{
uint8_t v_t_boxed_1063_; lean_object* v_res_1064_; 
v_t_boxed_1063_ = lean_unbox(v_t_1060_);
v_res_1064_ = l_Std_Time_OffsetZ_ctorElim(v_motive_1058_, v_ctorIdx_1059_, v_t_boxed_1063_, v_h_1061_, v_k_1062_);
lean_dec(v_k_1062_);
lean_dec(v_ctorIdx_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg(lean_object* v_hourMinute_1065_){
_start:
{
lean_inc(v_hourMinute_1065_);
return v_hourMinute_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg___boxed(lean_object* v_hourMinute_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_Time_OffsetZ_hourMinute_elim___redArg(v_hourMinute_1066_);
lean_dec(v_hourMinute_1066_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim(lean_object* v_motive_1068_, uint8_t v_t_1069_, lean_object* v_h_1070_, lean_object* v_hourMinute_1071_){
_start:
{
lean_inc(v_hourMinute_1071_);
return v_hourMinute_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___boxed(lean_object* v_motive_1072_, lean_object* v_t_1073_, lean_object* v_h_1074_, lean_object* v_hourMinute_1075_){
_start:
{
uint8_t v_t_boxed_1076_; lean_object* v_res_1077_; 
v_t_boxed_1076_ = lean_unbox(v_t_1073_);
v_res_1077_ = l_Std_Time_OffsetZ_hourMinute_elim(v_motive_1072_, v_t_boxed_1076_, v_h_1074_, v_hourMinute_1075_);
lean_dec(v_hourMinute_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg(lean_object* v_full_1078_){
_start:
{
lean_inc(v_full_1078_);
return v_full_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg___boxed(lean_object* v_full_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Std_Time_OffsetZ_full_elim___redArg(v_full_1079_);
lean_dec(v_full_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim(lean_object* v_motive_1081_, uint8_t v_t_1082_, lean_object* v_h_1083_, lean_object* v_full_1084_){
_start:
{
lean_inc(v_full_1084_);
return v_full_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___boxed(lean_object* v_motive_1085_, lean_object* v_t_1086_, lean_object* v_h_1087_, lean_object* v_full_1088_){
_start:
{
uint8_t v_t_boxed_1089_; lean_object* v_res_1090_; 
v_t_boxed_1089_ = lean_unbox(v_t_1086_);
v_res_1090_ = l_Std_Time_OffsetZ_full_elim(v_motive_1085_, v_t_boxed_1089_, v_h_1087_, v_full_1088_);
lean_dec(v_full_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(lean_object* v_hourMinuteSecondColon_1091_){
_start:
{
lean_inc(v_hourMinuteSecondColon_1091_);
return v_hourMinuteSecondColon_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg___boxed(lean_object* v_hourMinuteSecondColon_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(v_hourMinuteSecondColon_1092_);
lean_dec(v_hourMinuteSecondColon_1092_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(lean_object* v_motive_1094_, uint8_t v_t_1095_, lean_object* v_h_1096_, lean_object* v_hourMinuteSecondColon_1097_){
_start:
{
lean_inc(v_hourMinuteSecondColon_1097_);
return v_hourMinuteSecondColon_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___boxed(lean_object* v_motive_1098_, lean_object* v_t_1099_, lean_object* v_h_1100_, lean_object* v_hourMinuteSecondColon_1101_){
_start:
{
uint8_t v_t_boxed_1102_; lean_object* v_res_1103_; 
v_t_boxed_1102_ = lean_unbox(v_t_1099_);
v_res_1103_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(v_motive_1098_, v_t_boxed_1102_, v_h_1100_, v_hourMinuteSecondColon_1101_);
lean_dec(v_hourMinuteSecondColon_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr(uint8_t v_x_1113_, lean_object* v_prec_1114_){
_start:
{
lean_object* v___y_1116_; lean_object* v___y_1123_; lean_object* v___y_1130_; 
switch(v_x_1113_)
{
case 0:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(1024u);
v___x_1137_ = lean_nat_dec_le(v___x_1136_, v_prec_1114_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1116_ = v___x_1138_;
goto v___jp_1115_;
}
else
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1116_ = v___x_1139_;
goto v___jp_1115_;
}
}
case 1:
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_unsigned_to_nat(1024u);
v___x_1141_ = lean_nat_dec_le(v___x_1140_, v_prec_1114_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1123_ = v___x_1142_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1123_ = v___x_1143_;
goto v___jp_1122_;
}
}
default: 
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = lean_unsigned_to_nat(1024u);
v___x_1145_ = lean_nat_dec_le(v___x_1144_, v_prec_1114_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1130_ = v___x_1146_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1130_ = v___x_1147_;
goto v___jp_1129_;
}
}
}
v___jp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1117_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__1));
lean_inc(v___y_1116_);
v___x_1118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___y_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = 0;
v___x_1120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*1, v___x_1119_);
v___x_1121_ = l_Repr_addAppParen(v___x_1120_, v_prec_1114_);
return v___x_1121_;
}
v___jp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1124_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__3));
lean_inc(v___y_1123_);
v___x_1125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___y_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = 0;
v___x_1127_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*1, v___x_1126_);
v___x_1128_ = l_Repr_addAppParen(v___x_1127_, v_prec_1114_);
return v___x_1128_;
}
v___jp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1131_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__5));
lean_inc(v___y_1130_);
v___x_1132_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___y_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = 0;
v___x_1134_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*1, v___x_1133_);
v___x_1135_ = l_Repr_addAppParen(v___x_1134_, v_prec_1114_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr___boxed(lean_object* v_x_1148_, lean_object* v_prec_1149_){
_start:
{
uint8_t v_x_167__boxed_1150_; lean_object* v_res_1151_; 
v_x_167__boxed_1150_ = lean_unbox(v_x_1148_);
v_res_1151_ = l_Std_Time_instReprOffsetZ_repr(v_x_167__boxed_1150_, v_prec_1149_);
lean_dec(v_prec_1149_);
return v_res_1151_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetZ_default(void){
_start:
{
uint8_t v___x_1154_; 
v___x_1154_ = 0;
return v___x_1154_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetZ(void){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = 0;
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify(lean_object* v_num_1165_){
_start:
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = lean_nat_dec_eq(v_num_1165_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_unsigned_to_nat(2u);
v___x_1171_ = lean_nat_dec_eq(v_num_1165_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = lean_unsigned_to_nat(3u);
v___x_1173_ = lean_nat_dec_eq(v_num_1165_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_unsigned_to_nat(4u);
v___x_1175_ = lean_nat_dec_eq(v_num_1165_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_unsigned_to_nat(5u);
v___x_1177_ = lean_nat_dec_eq(v_num_1165_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_box(0);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; 
v___x_1179_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__1));
return v___x_1179_;
}
}
else
{
lean_object* v___x_1180_; 
v___x_1180_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__2));
return v___x_1180_;
}
}
else
{
goto v___jp_1166_;
}
}
else
{
goto v___jp_1166_;
}
}
else
{
goto v___jp_1166_;
}
v___jp_1166_:
{
lean_object* v___x_1167_; 
v___x_1167_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__0));
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify___boxed(lean_object* v_num_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Std_Time_OffsetZ_classify(v_num_1181_);
lean_dec(v_num_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx(uint8_t v_x_1183_){
_start:
{
switch(v_x_1183_)
{
case 0:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_unsigned_to_nat(0u);
return v___x_1184_;
}
case 1:
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_unsigned_to_nat(1u);
return v___x_1185_;
}
case 2:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_unsigned_to_nat(2u);
return v___x_1186_;
}
default: 
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_unsigned_to_nat(3u);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx___boxed(lean_object* v_x_1188_){
_start:
{
uint8_t v_x_boxed_1189_; lean_object* v_res_1190_; 
v_x_boxed_1189_ = lean_unbox(v_x_1188_);
v_res_1190_ = l_Std_Time_DayPeriod_ctorIdx(v_x_boxed_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg(lean_object* v_k_1191_){
_start:
{
lean_inc(v_k_1191_);
return v_k_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg___boxed(lean_object* v_k_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_Time_DayPeriod_ctorElim___redArg(v_k_1192_);
lean_dec(v_k_1192_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim(lean_object* v_motive_1194_, lean_object* v_ctorIdx_1195_, uint8_t v_t_1196_, lean_object* v_h_1197_, lean_object* v_k_1198_){
_start:
{
lean_inc(v_k_1198_);
return v_k_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___boxed(lean_object* v_motive_1199_, lean_object* v_ctorIdx_1200_, lean_object* v_t_1201_, lean_object* v_h_1202_, lean_object* v_k_1203_){
_start:
{
uint8_t v_t_boxed_1204_; lean_object* v_res_1205_; 
v_t_boxed_1204_ = lean_unbox(v_t_1201_);
v_res_1205_ = l_Std_Time_DayPeriod_ctorElim(v_motive_1199_, v_ctorIdx_1200_, v_t_boxed_1204_, v_h_1202_, v_k_1203_);
lean_dec(v_k_1203_);
lean_dec(v_ctorIdx_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg(lean_object* v_am_1206_){
_start:
{
lean_inc(v_am_1206_);
return v_am_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg___boxed(lean_object* v_am_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Std_Time_DayPeriod_am_elim___redArg(v_am_1207_);
lean_dec(v_am_1207_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim(lean_object* v_motive_1209_, uint8_t v_t_1210_, lean_object* v_h_1211_, lean_object* v_am_1212_){
_start:
{
lean_inc(v_am_1212_);
return v_am_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___boxed(lean_object* v_motive_1213_, lean_object* v_t_1214_, lean_object* v_h_1215_, lean_object* v_am_1216_){
_start:
{
uint8_t v_t_boxed_1217_; lean_object* v_res_1218_; 
v_t_boxed_1217_ = lean_unbox(v_t_1214_);
v_res_1218_ = l_Std_Time_DayPeriod_am_elim(v_motive_1213_, v_t_boxed_1217_, v_h_1215_, v_am_1216_);
lean_dec(v_am_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg(lean_object* v_pm_1219_){
_start:
{
lean_inc(v_pm_1219_);
return v_pm_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg___boxed(lean_object* v_pm_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Std_Time_DayPeriod_pm_elim___redArg(v_pm_1220_);
lean_dec(v_pm_1220_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim(lean_object* v_motive_1222_, uint8_t v_t_1223_, lean_object* v_h_1224_, lean_object* v_pm_1225_){
_start:
{
lean_inc(v_pm_1225_);
return v_pm_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___boxed(lean_object* v_motive_1226_, lean_object* v_t_1227_, lean_object* v_h_1228_, lean_object* v_pm_1229_){
_start:
{
uint8_t v_t_boxed_1230_; lean_object* v_res_1231_; 
v_t_boxed_1230_ = lean_unbox(v_t_1227_);
v_res_1231_ = l_Std_Time_DayPeriod_pm_elim(v_motive_1226_, v_t_boxed_1230_, v_h_1228_, v_pm_1229_);
lean_dec(v_pm_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg(lean_object* v_noon_1232_){
_start:
{
lean_inc(v_noon_1232_);
return v_noon_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg___boxed(lean_object* v_noon_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_Time_DayPeriod_noon_elim___redArg(v_noon_1233_);
lean_dec(v_noon_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim(lean_object* v_motive_1235_, uint8_t v_t_1236_, lean_object* v_h_1237_, lean_object* v_noon_1238_){
_start:
{
lean_inc(v_noon_1238_);
return v_noon_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___boxed(lean_object* v_motive_1239_, lean_object* v_t_1240_, lean_object* v_h_1241_, lean_object* v_noon_1242_){
_start:
{
uint8_t v_t_boxed_1243_; lean_object* v_res_1244_; 
v_t_boxed_1243_ = lean_unbox(v_t_1240_);
v_res_1244_ = l_Std_Time_DayPeriod_noon_elim(v_motive_1239_, v_t_boxed_1243_, v_h_1241_, v_noon_1242_);
lean_dec(v_noon_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg(lean_object* v_midnight_1245_){
_start:
{
lean_inc(v_midnight_1245_);
return v_midnight_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg___boxed(lean_object* v_midnight_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_Time_DayPeriod_midnight_elim___redArg(v_midnight_1246_);
lean_dec(v_midnight_1246_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim(lean_object* v_motive_1248_, uint8_t v_t_1249_, lean_object* v_h_1250_, lean_object* v_midnight_1251_){
_start:
{
lean_inc(v_midnight_1251_);
return v_midnight_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___boxed(lean_object* v_motive_1252_, lean_object* v_t_1253_, lean_object* v_h_1254_, lean_object* v_midnight_1255_){
_start:
{
uint8_t v_t_boxed_1256_; lean_object* v_res_1257_; 
v_t_boxed_1256_ = lean_unbox(v_t_1253_);
v_res_1257_ = l_Std_Time_DayPeriod_midnight_elim(v_motive_1252_, v_t_boxed_1256_, v_h_1254_, v_midnight_1255_);
lean_dec(v_midnight_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr(uint8_t v_x_1270_, lean_object* v_prec_1271_){
_start:
{
lean_object* v___y_1273_; lean_object* v___y_1280_; lean_object* v___y_1287_; lean_object* v___y_1294_; 
switch(v_x_1270_)
{
case 0:
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = lean_unsigned_to_nat(1024u);
v___x_1301_ = lean_nat_dec_le(v___x_1300_, v_prec_1271_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1273_ = v___x_1302_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1273_ = v___x_1303_;
goto v___jp_1272_;
}
}
case 1:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = lean_unsigned_to_nat(1024u);
v___x_1305_ = lean_nat_dec_le(v___x_1304_, v_prec_1271_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1280_ = v___x_1306_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1280_ = v___x_1307_;
goto v___jp_1279_;
}
}
case 2:
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = lean_unsigned_to_nat(1024u);
v___x_1309_ = lean_nat_dec_le(v___x_1308_, v_prec_1271_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1287_ = v___x_1310_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1287_ = v___x_1311_;
goto v___jp_1286_;
}
}
default: 
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = lean_unsigned_to_nat(1024u);
v___x_1313_ = lean_nat_dec_le(v___x_1312_, v_prec_1271_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1294_ = v___x_1314_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1294_ = v___x_1315_;
goto v___jp_1293_;
}
}
}
v___jp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1274_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__1));
lean_inc(v___y_1273_);
v___x_1275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___y_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = 0;
v___x_1277_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*1, v___x_1276_);
v___x_1278_ = l_Repr_addAppParen(v___x_1277_, v_prec_1271_);
return v___x_1278_;
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1281_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__3));
lean_inc(v___y_1280_);
v___x_1282_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___y_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = 0;
v___x_1284_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*1, v___x_1283_);
v___x_1285_ = l_Repr_addAppParen(v___x_1284_, v_prec_1271_);
return v___x_1285_;
}
v___jp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1288_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__5));
lean_inc(v___y_1287_);
v___x_1289_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___y_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = 0;
v___x_1291_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1291_, 0, v___x_1289_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*1, v___x_1290_);
v___x_1292_ = l_Repr_addAppParen(v___x_1291_, v_prec_1271_);
return v___x_1292_;
}
v___jp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1295_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__7));
lean_inc(v___y_1294_);
v___x_1296_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___y_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = 0;
v___x_1298_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set_uint8(v___x_1298_, sizeof(void*)*1, v___x_1297_);
v___x_1299_ = l_Repr_addAppParen(v___x_1298_, v_prec_1271_);
return v___x_1299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr___boxed(lean_object* v_x_1316_, lean_object* v_prec_1317_){
_start:
{
uint8_t v_x_221__boxed_1318_; lean_object* v_res_1319_; 
v_x_221__boxed_1318_ = lean_unbox(v_x_1316_);
v_res_1319_ = l_Std_Time_instReprDayPeriod_repr(v_x_221__boxed_1318_, v_prec_1317_);
lean_dec(v_prec_1317_);
return v_res_1319_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedDayPeriod_default(void){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = 0;
return v___x_1322_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedDayPeriod(void){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = 0;
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx(uint8_t v_x_1324_){
_start:
{
switch(v_x_1324_)
{
case 0:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_unsigned_to_nat(0u);
return v___x_1325_;
}
case 1:
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_unsigned_to_nat(1u);
return v___x_1326_;
}
case 2:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_unsigned_to_nat(2u);
return v___x_1327_;
}
case 3:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_unsigned_to_nat(3u);
return v___x_1328_;
}
case 4:
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_unsigned_to_nat(4u);
return v___x_1329_;
}
default: 
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_unsigned_to_nat(5u);
return v___x_1330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx___boxed(lean_object* v_x_1331_){
_start:
{
uint8_t v_x_boxed_1332_; lean_object* v_res_1333_; 
v_x_boxed_1332_ = lean_unbox(v_x_1331_);
v_res_1333_ = l_Std_Time_ExtendedDayPeriod_ctorIdx(v_x_boxed_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(lean_object* v_k_1334_){
_start:
{
lean_inc(v_k_1334_);
return v_k_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg___boxed(lean_object* v_k_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(v_k_1335_);
lean_dec(v_k_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim(lean_object* v_motive_1337_, lean_object* v_ctorIdx_1338_, uint8_t v_t_1339_, lean_object* v_h_1340_, lean_object* v_k_1341_){
_start:
{
lean_inc(v_k_1341_);
return v_k_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___boxed(lean_object* v_motive_1342_, lean_object* v_ctorIdx_1343_, lean_object* v_t_1344_, lean_object* v_h_1345_, lean_object* v_k_1346_){
_start:
{
uint8_t v_t_boxed_1347_; lean_object* v_res_1348_; 
v_t_boxed_1347_ = lean_unbox(v_t_1344_);
v_res_1348_ = l_Std_Time_ExtendedDayPeriod_ctorElim(v_motive_1342_, v_ctorIdx_1343_, v_t_boxed_1347_, v_h_1345_, v_k_1346_);
lean_dec(v_k_1346_);
lean_dec(v_ctorIdx_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(lean_object* v_midnight_1349_){
_start:
{
lean_inc(v_midnight_1349_);
return v_midnight_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg___boxed(lean_object* v_midnight_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(v_midnight_1350_);
lean_dec(v_midnight_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim(lean_object* v_motive_1352_, uint8_t v_t_1353_, lean_object* v_h_1354_, lean_object* v_midnight_1355_){
_start:
{
lean_inc(v_midnight_1355_);
return v_midnight_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___boxed(lean_object* v_motive_1356_, lean_object* v_t_1357_, lean_object* v_h_1358_, lean_object* v_midnight_1359_){
_start:
{
uint8_t v_t_boxed_1360_; lean_object* v_res_1361_; 
v_t_boxed_1360_ = lean_unbox(v_t_1357_);
v_res_1361_ = l_Std_Time_ExtendedDayPeriod_midnight_elim(v_motive_1356_, v_t_boxed_1360_, v_h_1358_, v_midnight_1359_);
lean_dec(v_midnight_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg(lean_object* v_night_1362_){
_start:
{
lean_inc(v_night_1362_);
return v_night_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg___boxed(lean_object* v_night_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_Time_ExtendedDayPeriod_night_elim___redArg(v_night_1363_);
lean_dec(v_night_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim(lean_object* v_motive_1365_, uint8_t v_t_1366_, lean_object* v_h_1367_, lean_object* v_night_1368_){
_start:
{
lean_inc(v_night_1368_);
return v_night_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___boxed(lean_object* v_motive_1369_, lean_object* v_t_1370_, lean_object* v_h_1371_, lean_object* v_night_1372_){
_start:
{
uint8_t v_t_boxed_1373_; lean_object* v_res_1374_; 
v_t_boxed_1373_ = lean_unbox(v_t_1370_);
v_res_1374_ = l_Std_Time_ExtendedDayPeriod_night_elim(v_motive_1369_, v_t_boxed_1373_, v_h_1371_, v_night_1372_);
lean_dec(v_night_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(lean_object* v_morning_1375_){
_start:
{
lean_inc(v_morning_1375_);
return v_morning_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg___boxed(lean_object* v_morning_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(v_morning_1376_);
lean_dec(v_morning_1376_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim(lean_object* v_motive_1378_, uint8_t v_t_1379_, lean_object* v_h_1380_, lean_object* v_morning_1381_){
_start:
{
lean_inc(v_morning_1381_);
return v_morning_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___boxed(lean_object* v_motive_1382_, lean_object* v_t_1383_, lean_object* v_h_1384_, lean_object* v_morning_1385_){
_start:
{
uint8_t v_t_boxed_1386_; lean_object* v_res_1387_; 
v_t_boxed_1386_ = lean_unbox(v_t_1383_);
v_res_1387_ = l_Std_Time_ExtendedDayPeriod_morning_elim(v_motive_1382_, v_t_boxed_1386_, v_h_1384_, v_morning_1385_);
lean_dec(v_morning_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(lean_object* v_noon_1388_){
_start:
{
lean_inc(v_noon_1388_);
return v_noon_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg___boxed(lean_object* v_noon_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(v_noon_1389_);
lean_dec(v_noon_1389_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim(lean_object* v_motive_1391_, uint8_t v_t_1392_, lean_object* v_h_1393_, lean_object* v_noon_1394_){
_start:
{
lean_inc(v_noon_1394_);
return v_noon_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___boxed(lean_object* v_motive_1395_, lean_object* v_t_1396_, lean_object* v_h_1397_, lean_object* v_noon_1398_){
_start:
{
uint8_t v_t_boxed_1399_; lean_object* v_res_1400_; 
v_t_boxed_1399_ = lean_unbox(v_t_1396_);
v_res_1400_ = l_Std_Time_ExtendedDayPeriod_noon_elim(v_motive_1395_, v_t_boxed_1399_, v_h_1397_, v_noon_1398_);
lean_dec(v_noon_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(lean_object* v_afternoon_1401_){
_start:
{
lean_inc(v_afternoon_1401_);
return v_afternoon_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg___boxed(lean_object* v_afternoon_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(v_afternoon_1402_);
lean_dec(v_afternoon_1402_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim(lean_object* v_motive_1404_, uint8_t v_t_1405_, lean_object* v_h_1406_, lean_object* v_afternoon_1407_){
_start:
{
lean_inc(v_afternoon_1407_);
return v_afternoon_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___boxed(lean_object* v_motive_1408_, lean_object* v_t_1409_, lean_object* v_h_1410_, lean_object* v_afternoon_1411_){
_start:
{
uint8_t v_t_boxed_1412_; lean_object* v_res_1413_; 
v_t_boxed_1412_ = lean_unbox(v_t_1409_);
v_res_1413_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim(v_motive_1408_, v_t_boxed_1412_, v_h_1410_, v_afternoon_1411_);
lean_dec(v_afternoon_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(lean_object* v_evening_1414_){
_start:
{
lean_inc(v_evening_1414_);
return v_evening_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg___boxed(lean_object* v_evening_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(v_evening_1415_);
lean_dec(v_evening_1415_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim(lean_object* v_motive_1417_, uint8_t v_t_1418_, lean_object* v_h_1419_, lean_object* v_evening_1420_){
_start:
{
lean_inc(v_evening_1420_);
return v_evening_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___boxed(lean_object* v_motive_1421_, lean_object* v_t_1422_, lean_object* v_h_1423_, lean_object* v_evening_1424_){
_start:
{
uint8_t v_t_boxed_1425_; lean_object* v_res_1426_; 
v_t_boxed_1425_ = lean_unbox(v_t_1422_);
v_res_1426_ = l_Std_Time_ExtendedDayPeriod_evening_elim(v_motive_1421_, v_t_boxed_1425_, v_h_1423_, v_evening_1424_);
lean_dec(v_evening_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr(uint8_t v_x_1445_, lean_object* v_prec_1446_){
_start:
{
lean_object* v___y_1448_; lean_object* v___y_1455_; lean_object* v___y_1462_; lean_object* v___y_1469_; lean_object* v___y_1476_; lean_object* v___y_1483_; 
switch(v_x_1445_)
{
case 0:
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = lean_unsigned_to_nat(1024u);
v___x_1490_ = lean_nat_dec_le(v___x_1489_, v_prec_1446_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1448_ = v___x_1491_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1448_ = v___x_1492_;
goto v___jp_1447_;
}
}
case 1:
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_unsigned_to_nat(1024u);
v___x_1494_ = lean_nat_dec_le(v___x_1493_, v_prec_1446_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1455_ = v___x_1495_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1455_ = v___x_1496_;
goto v___jp_1454_;
}
}
case 2:
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = lean_unsigned_to_nat(1024u);
v___x_1498_ = lean_nat_dec_le(v___x_1497_, v_prec_1446_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1462_ = v___x_1499_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1462_ = v___x_1500_;
goto v___jp_1461_;
}
}
case 3:
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = lean_unsigned_to_nat(1024u);
v___x_1502_ = lean_nat_dec_le(v___x_1501_, v_prec_1446_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1469_ = v___x_1503_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1469_ = v___x_1504_;
goto v___jp_1468_;
}
}
case 4:
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = lean_unsigned_to_nat(1024u);
v___x_1506_ = lean_nat_dec_le(v___x_1505_, v_prec_1446_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1476_ = v___x_1507_;
goto v___jp_1475_;
}
else
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1476_ = v___x_1508_;
goto v___jp_1475_;
}
}
default: 
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = lean_unsigned_to_nat(1024u);
v___x_1510_ = lean_nat_dec_le(v___x_1509_, v_prec_1446_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1483_ = v___x_1511_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1483_ = v___x_1512_;
goto v___jp_1482_;
}
}
}
v___jp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1449_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__1));
lean_inc(v___y_1448_);
v___x_1450_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___y_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = 0;
v___x_1452_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*1, v___x_1451_);
v___x_1453_ = l_Repr_addAppParen(v___x_1452_, v_prec_1446_);
return v___x_1453_;
}
v___jp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1456_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__3));
lean_inc(v___y_1455_);
v___x_1457_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___y_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = 0;
v___x_1459_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*1, v___x_1458_);
v___x_1460_ = l_Repr_addAppParen(v___x_1459_, v_prec_1446_);
return v___x_1460_;
}
v___jp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1463_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__5));
lean_inc(v___y_1462_);
v___x_1464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___y_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = 0;
v___x_1466_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set_uint8(v___x_1466_, sizeof(void*)*1, v___x_1465_);
v___x_1467_ = l_Repr_addAppParen(v___x_1466_, v_prec_1446_);
return v___x_1467_;
}
v___jp_1468_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1470_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__7));
lean_inc(v___y_1469_);
v___x_1471_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = 0;
v___x_1473_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set_uint8(v___x_1473_, sizeof(void*)*1, v___x_1472_);
v___x_1474_ = l_Repr_addAppParen(v___x_1473_, v_prec_1446_);
return v___x_1474_;
}
v___jp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1477_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__9));
lean_inc(v___y_1476_);
v___x_1478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___y_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = 0;
v___x_1480_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set_uint8(v___x_1480_, sizeof(void*)*1, v___x_1479_);
v___x_1481_ = l_Repr_addAppParen(v___x_1480_, v_prec_1446_);
return v___x_1481_;
}
v___jp_1482_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1484_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__11));
lean_inc(v___y_1483_);
v___x_1485_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___y_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = 0;
v___x_1487_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*1, v___x_1486_);
v___x_1488_ = l_Repr_addAppParen(v___x_1487_, v_prec_1446_);
return v___x_1488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___boxed(lean_object* v_x_1513_, lean_object* v_prec_1514_){
_start:
{
uint8_t v_x_329__boxed_1515_; lean_object* v_res_1516_; 
v_x_329__boxed_1515_ = lean_unbox(v_x_1513_);
v_res_1516_ = l_Std_Time_instReprExtendedDayPeriod_repr(v_x_329__boxed_1515_, v_prec_1514_);
lean_dec(v_prec_1514_);
return v_res_1516_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedExtendedDayPeriod_default(void){
_start:
{
uint8_t v___x_1519_; 
v___x_1519_ = 0;
return v___x_1519_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedExtendedDayPeriod(void){
_start:
{
uint8_t v___x_1520_; 
v___x_1520_ = 0;
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx(lean_object* v_x_1521_){
_start:
{
switch(lean_obj_tag(v_x_1521_))
{
case 0:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_unsigned_to_nat(0u);
return v___x_1522_;
}
case 1:
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_unsigned_to_nat(1u);
return v___x_1523_;
}
case 2:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_unsigned_to_nat(2u);
return v___x_1524_;
}
case 3:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_unsigned_to_nat(3u);
return v___x_1525_;
}
case 4:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_unsigned_to_nat(4u);
return v___x_1526_;
}
case 5:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_unsigned_to_nat(5u);
return v___x_1527_;
}
case 6:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_unsigned_to_nat(6u);
return v___x_1528_;
}
case 7:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_unsigned_to_nat(7u);
return v___x_1529_;
}
case 8:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_unsigned_to_nat(8u);
return v___x_1530_;
}
case 9:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_unsigned_to_nat(9u);
return v___x_1531_;
}
case 10:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_unsigned_to_nat(10u);
return v___x_1532_;
}
case 11:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_unsigned_to_nat(11u);
return v___x_1533_;
}
case 12:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_unsigned_to_nat(12u);
return v___x_1534_;
}
case 13:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_unsigned_to_nat(13u);
return v___x_1535_;
}
case 14:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_unsigned_to_nat(14u);
return v___x_1536_;
}
case 15:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_unsigned_to_nat(15u);
return v___x_1537_;
}
case 16:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_unsigned_to_nat(16u);
return v___x_1538_;
}
case 17:
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_unsigned_to_nat(17u);
return v___x_1539_;
}
case 18:
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_unsigned_to_nat(18u);
return v___x_1540_;
}
case 19:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_unsigned_to_nat(19u);
return v___x_1541_;
}
case 20:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_unsigned_to_nat(20u);
return v___x_1542_;
}
case 21:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_unsigned_to_nat(21u);
return v___x_1543_;
}
case 22:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_unsigned_to_nat(22u);
return v___x_1544_;
}
case 23:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_unsigned_to_nat(23u);
return v___x_1545_;
}
case 24:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_unsigned_to_nat(24u);
return v___x_1546_;
}
case 25:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_unsigned_to_nat(25u);
return v___x_1547_;
}
case 26:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_unsigned_to_nat(26u);
return v___x_1548_;
}
case 27:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_unsigned_to_nat(27u);
return v___x_1549_;
}
case 28:
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_unsigned_to_nat(28u);
return v___x_1550_;
}
case 29:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_unsigned_to_nat(29u);
return v___x_1551_;
}
case 30:
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_unsigned_to_nat(30u);
return v___x_1552_;
}
case 31:
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_unsigned_to_nat(31u);
return v___x_1553_;
}
case 32:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_unsigned_to_nat(32u);
return v___x_1554_;
}
case 33:
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_unsigned_to_nat(33u);
return v___x_1555_;
}
case 34:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_unsigned_to_nat(34u);
return v___x_1556_;
}
default: 
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_unsigned_to_nat(35u);
return v___x_1557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx___boxed(lean_object* v_x_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Std_Time_Modifier_ctorIdx(v_x_1558_);
lean_dec_ref(v_x_1558_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___redArg(lean_object* v_t_1560_, lean_object* v_k_1561_){
_start:
{
switch(lean_obj_tag(v_t_1560_))
{
case 0:
{
uint8_t v_presentation_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_presentation_1562_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1563_ = lean_box(v_presentation_1562_);
v___x_1564_ = lean_apply_1(v_k_1561_, v___x_1563_);
return v___x_1564_;
}
case 4:
{
lean_object* v_presentation_1565_; lean_object* v___x_1566_; 
v_presentation_1565_ = lean_ctor_get(v_t_1560_, 0);
lean_inc_ref(v_presentation_1565_);
lean_dec_ref_known(v_t_1560_, 1);
v___x_1566_ = lean_apply_1(v_k_1561_, v_presentation_1565_);
return v___x_1566_;
}
case 5:
{
lean_object* v_presentation_1567_; lean_object* v___x_1568_; 
v_presentation_1567_ = lean_ctor_get(v_t_1560_, 0);
lean_inc_ref(v_presentation_1567_);
lean_dec_ref_known(v_t_1560_, 1);
v___x_1568_ = lean_apply_1(v_k_1561_, v_presentation_1567_);
return v___x_1568_;
}
case 7:
{
lean_object* v_presentation_1569_; lean_object* v___x_1570_; 
v_presentation_1569_ = lean_ctor_get(v_t_1560_, 0);
lean_inc_ref(v_presentation_1569_);
lean_dec_ref_known(v_t_1560_, 1);
v___x_1570_ = lean_apply_1(v_k_1561_, v_presentation_1569_);
return v___x_1570_;
}
case 8:
{
lean_object* v_presentation_1571_; lean_object* v___x_1572_; 
v_presentation_1571_ = lean_ctor_get(v_t_1560_, 0);
lean_inc_ref(v_presentation_1571_);
lean_dec_ref_known(v_t_1560_, 1);
v___x_1572_ = lean_apply_1(v_k_1561_, v_presentation_1571_);
return v___x_1572_;
}
case 12:
{
uint8_t v_presentation_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_presentation_1573_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1574_ = lean_box(v_presentation_1573_);
v___x_1575_ = lean_apply_1(v_k_1561_, v___x_1574_);
return v___x_1575_;
}
case 13:
{
lean_object* v_presentation_1576_; lean_object* v___x_1577_; 
v_presentation_1576_ = lean_ctor_get(v_t_1560_, 0);
lean_inc_ref(v_presentation_1576_);
lean_dec_ref_known(v_t_1560_, 1);
v___x_1577_ = lean_apply_1(v_k_1561_, v_presentation_1576_);
return v___x_1577_;
}
case 14:
{
lean_object* v_presentation_1578_; lean_object* v___x_1579_; 
v_presentation_1578_ = lean_ctor_get(v_t_1560_, 0);
lean_inc_ref(v_presentation_1578_);
lean_dec_ref_known(v_t_1560_, 1);
v___x_1579_ = lean_apply_1(v_k_1561_, v_presentation_1578_);
return v___x_1579_;
}
case 16:
{
uint8_t v_presentation_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_presentation_1580_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1581_ = lean_box(v_presentation_1580_);
v___x_1582_ = lean_apply_1(v_k_1561_, v___x_1581_);
return v___x_1582_;
}
case 17:
{
uint8_t v_presentation_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_presentation_1583_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1584_ = lean_box(v_presentation_1583_);
v___x_1585_ = lean_apply_1(v_k_1561_, v___x_1584_);
return v___x_1585_;
}
case 18:
{
uint8_t v_presentation_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_presentation_1586_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1587_ = lean_box(v_presentation_1586_);
v___x_1588_ = lean_apply_1(v_k_1561_, v___x_1587_);
return v___x_1588_;
}
case 29:
{
uint8_t v_presentation_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_presentation_1589_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1590_ = lean_box(v_presentation_1589_);
v___x_1591_ = lean_apply_1(v_k_1561_, v___x_1590_);
return v___x_1591_;
}
case 30:
{
uint8_t v_presentation_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_presentation_1592_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1593_ = lean_box(v_presentation_1592_);
v___x_1594_ = lean_apply_1(v_k_1561_, v___x_1593_);
return v___x_1594_;
}
case 31:
{
uint8_t v_presentation_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_presentation_1595_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1596_ = lean_box(v_presentation_1595_);
v___x_1597_ = lean_apply_1(v_k_1561_, v___x_1596_);
return v___x_1597_;
}
case 32:
{
uint8_t v_presentation_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_presentation_1598_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1599_ = lean_box(v_presentation_1598_);
v___x_1600_ = lean_apply_1(v_k_1561_, v___x_1599_);
return v___x_1600_;
}
case 33:
{
uint8_t v_presentation_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_presentation_1601_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1602_ = lean_box(v_presentation_1601_);
v___x_1603_ = lean_apply_1(v_k_1561_, v___x_1602_);
return v___x_1603_;
}
case 34:
{
uint8_t v_presentation_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_presentation_1604_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1605_ = lean_box(v_presentation_1604_);
v___x_1606_ = lean_apply_1(v_k_1561_, v___x_1605_);
return v___x_1606_;
}
case 35:
{
uint8_t v_presentation_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_presentation_1607_ = lean_ctor_get_uint8(v_t_1560_, 0);
lean_dec_ref_known(v_t_1560_, 0);
v___x_1608_ = lean_box(v_presentation_1607_);
v___x_1609_ = lean_apply_1(v_k_1561_, v___x_1608_);
return v___x_1609_;
}
default: 
{
lean_object* v_presentation_1610_; lean_object* v___x_1611_; 
v_presentation_1610_ = lean_ctor_get(v_t_1560_, 0);
lean_inc(v_presentation_1610_);
lean_dec_ref(v_t_1560_);
v___x_1611_ = lean_apply_1(v_k_1561_, v_presentation_1610_);
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim(lean_object* v_motive_1612_, lean_object* v_ctorIdx_1613_, lean_object* v_t_1614_, lean_object* v_h_1615_, lean_object* v_k_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1614_, v_k_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___boxed(lean_object* v_motive_1618_, lean_object* v_ctorIdx_1619_, lean_object* v_t_1620_, lean_object* v_h_1621_, lean_object* v_k_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Std_Time_Modifier_ctorElim(v_motive_1618_, v_ctorIdx_1619_, v_t_1620_, v_h_1621_, v_k_1622_);
lean_dec(v_ctorIdx_1619_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim___redArg(lean_object* v_t_1624_, lean_object* v_G_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1624_, v_G_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim(lean_object* v_motive_1627_, lean_object* v_t_1628_, lean_object* v_h_1629_, lean_object* v_G_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1628_, v_G_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim___redArg(lean_object* v_t_1632_, lean_object* v_u_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1632_, v_u_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim(lean_object* v_motive_1635_, lean_object* v_t_1636_, lean_object* v_h_1637_, lean_object* v_u_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1636_, v_u_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim___redArg(lean_object* v_t_1640_, lean_object* v_y_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1640_, v_y_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim(lean_object* v_motive_1643_, lean_object* v_t_1644_, lean_object* v_h_1645_, lean_object* v_y_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1644_, v_y_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim___redArg(lean_object* v_t_1648_, lean_object* v_D_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1648_, v_D_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim(lean_object* v_motive_1651_, lean_object* v_t_1652_, lean_object* v_h_1653_, lean_object* v_D_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1652_, v_D_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim___redArg(lean_object* v_t_1656_, lean_object* v_M_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1656_, v_M_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim(lean_object* v_motive_1659_, lean_object* v_t_1660_, lean_object* v_h_1661_, lean_object* v_M_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1660_, v_M_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim___redArg(lean_object* v_t_1664_, lean_object* v_L_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1664_, v_L_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim(lean_object* v_motive_1667_, lean_object* v_t_1668_, lean_object* v_h_1669_, lean_object* v_L_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1668_, v_L_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim___redArg(lean_object* v_t_1672_, lean_object* v_d_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1672_, v_d_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim(lean_object* v_motive_1675_, lean_object* v_t_1676_, lean_object* v_h_1677_, lean_object* v_d_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1676_, v_d_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim___redArg(lean_object* v_t_1680_, lean_object* v_Q_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1680_, v_Q_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim(lean_object* v_motive_1683_, lean_object* v_t_1684_, lean_object* v_h_1685_, lean_object* v_Q_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1684_, v_Q_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim___redArg(lean_object* v_t_1688_, lean_object* v_q_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1688_, v_q_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim(lean_object* v_motive_1691_, lean_object* v_t_1692_, lean_object* v_h_1693_, lean_object* v_q_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1692_, v_q_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim___redArg(lean_object* v_t_1696_, lean_object* v_Y_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1696_, v_Y_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim(lean_object* v_motive_1699_, lean_object* v_t_1700_, lean_object* v_h_1701_, lean_object* v_Y_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1700_, v_Y_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim___redArg(lean_object* v_t_1704_, lean_object* v_w_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1704_, v_w_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim(lean_object* v_motive_1707_, lean_object* v_t_1708_, lean_object* v_h_1709_, lean_object* v_w_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1708_, v_w_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim___redArg(lean_object* v_t_1712_, lean_object* v_W_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1712_, v_W_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim(lean_object* v_motive_1715_, lean_object* v_t_1716_, lean_object* v_h_1717_, lean_object* v_W_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1716_, v_W_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim___redArg(lean_object* v_t_1720_, lean_object* v_E_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1720_, v_E_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim(lean_object* v_motive_1723_, lean_object* v_t_1724_, lean_object* v_h_1725_, lean_object* v_E_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1724_, v_E_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim___redArg(lean_object* v_t_1728_, lean_object* v_e_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1728_, v_e_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim(lean_object* v_motive_1731_, lean_object* v_t_1732_, lean_object* v_h_1733_, lean_object* v_e_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1732_, v_e_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim___redArg(lean_object* v_t_1736_, lean_object* v_c_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1736_, v_c_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim(lean_object* v_motive_1739_, lean_object* v_t_1740_, lean_object* v_h_1741_, lean_object* v_c_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1740_, v_c_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim___redArg(lean_object* v_t_1744_, lean_object* v_F_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1744_, v_F_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim(lean_object* v_motive_1747_, lean_object* v_t_1748_, lean_object* v_h_1749_, lean_object* v_F_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1748_, v_F_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim___redArg(lean_object* v_t_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1752_, v_a_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim(lean_object* v_motive_1755_, lean_object* v_t_1756_, lean_object* v_h_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1756_, v_a_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim___redArg(lean_object* v_t_1760_, lean_object* v_b_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1760_, v_b_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim(lean_object* v_motive_1763_, lean_object* v_t_1764_, lean_object* v_h_1765_, lean_object* v_b_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1764_, v_b_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim___redArg(lean_object* v_t_1768_, lean_object* v_B_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1768_, v_B_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim(lean_object* v_motive_1771_, lean_object* v_t_1772_, lean_object* v_h_1773_, lean_object* v_B_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1772_, v_B_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim___redArg(lean_object* v_t_1776_, lean_object* v_h_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1776_, v_h_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim(lean_object* v_motive_1779_, lean_object* v_t_1780_, lean_object* v_h_1781_, lean_object* v_h_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1780_, v_h_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim___redArg(lean_object* v_t_1784_, lean_object* v_K_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1784_, v_K_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim(lean_object* v_motive_1787_, lean_object* v_t_1788_, lean_object* v_h_1789_, lean_object* v_K_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1788_, v_K_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim___redArg(lean_object* v_t_1792_, lean_object* v_k_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1792_, v_k_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim(lean_object* v_motive_1795_, lean_object* v_t_1796_, lean_object* v_h_1797_, lean_object* v_k_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1796_, v_k_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim___redArg(lean_object* v_t_1800_, lean_object* v_H_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1800_, v_H_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim(lean_object* v_motive_1803_, lean_object* v_t_1804_, lean_object* v_h_1805_, lean_object* v_H_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1804_, v_H_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim___redArg(lean_object* v_t_1808_, lean_object* v_m_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1808_, v_m_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim(lean_object* v_motive_1811_, lean_object* v_t_1812_, lean_object* v_h_1813_, lean_object* v_m_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1812_, v_m_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim___redArg(lean_object* v_t_1816_, lean_object* v_s_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1816_, v_s_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim(lean_object* v_motive_1819_, lean_object* v_t_1820_, lean_object* v_h_1821_, lean_object* v_s_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1820_, v_s_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim___redArg(lean_object* v_t_1824_, lean_object* v_S_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1824_, v_S_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim(lean_object* v_motive_1827_, lean_object* v_t_1828_, lean_object* v_h_1829_, lean_object* v_S_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1828_, v_S_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim___redArg(lean_object* v_t_1832_, lean_object* v_A_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1832_, v_A_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim(lean_object* v_motive_1835_, lean_object* v_t_1836_, lean_object* v_h_1837_, lean_object* v_A_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1836_, v_A_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim___redArg(lean_object* v_t_1840_, lean_object* v_n_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1840_, v_n_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim(lean_object* v_motive_1843_, lean_object* v_t_1844_, lean_object* v_h_1845_, lean_object* v_n_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1844_, v_n_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim___redArg(lean_object* v_t_1848_, lean_object* v_N_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1848_, v_N_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim(lean_object* v_motive_1851_, lean_object* v_t_1852_, lean_object* v_h_1853_, lean_object* v_N_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1852_, v_N_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim___redArg(lean_object* v_t_1856_, lean_object* v_V_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1856_, v_V_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim(lean_object* v_motive_1859_, lean_object* v_t_1860_, lean_object* v_h_1861_, lean_object* v_V_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1860_, v_V_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim___redArg(lean_object* v_t_1864_, lean_object* v_z_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1864_, v_z_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim(lean_object* v_motive_1867_, lean_object* v_t_1868_, lean_object* v_h_1869_, lean_object* v_z_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1868_, v_z_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim___redArg(lean_object* v_t_1872_, lean_object* v_v_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1872_, v_v_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim(lean_object* v_motive_1875_, lean_object* v_t_1876_, lean_object* v_h_1877_, lean_object* v_v_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1876_, v_v_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim___redArg(lean_object* v_t_1880_, lean_object* v_O_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1880_, v_O_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim(lean_object* v_motive_1883_, lean_object* v_t_1884_, lean_object* v_h_1885_, lean_object* v_O_1886_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1884_, v_O_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim___redArg(lean_object* v_t_1888_, lean_object* v_X_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1888_, v_X_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim(lean_object* v_motive_1891_, lean_object* v_t_1892_, lean_object* v_h_1893_, lean_object* v_X_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1892_, v_X_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim___redArg(lean_object* v_t_1896_, lean_object* v_x_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1896_, v_x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim(lean_object* v_motive_1899_, lean_object* v_t_1900_, lean_object* v_h_1901_, lean_object* v_x_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1900_, v_x_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim___redArg(lean_object* v_t_1904_, lean_object* v_Z_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1904_, v_Z_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim(lean_object* v_motive_1907_, lean_object* v_t_1908_, lean_object* v_h_1909_, lean_object* v_Z_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1908_, v_Z_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
if (lean_obj_tag(v_x_1918_) == 0)
{
lean_object* v_val_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_val_1920_ = lean_ctor_get(v_x_1918_, 0);
lean_inc(v_val_1920_);
lean_dec_ref_known(v_x_1918_, 1);
v___x_1921_ = ((lean_object*)(l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__1));
v___x_1922_ = l_Std_Time_instReprNumber_repr___redArg(v_val_1920_);
v___x_1923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_Repr_addAppParen(v___x_1923_, v_x_1919_);
return v___x_1924_;
}
else
{
lean_object* v_val_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_val_1925_ = lean_ctor_get(v_x_1918_, 0);
lean_inc(v_val_1925_);
lean_dec_ref_known(v_x_1918_, 1);
v___x_1926_ = ((lean_object*)(l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__3));
v___x_1927_ = lean_unsigned_to_nat(1024u);
v___x_1928_ = lean_unbox(v_val_1925_);
lean_dec(v_val_1925_);
v___x_1929_ = l_Std_Time_instReprText_repr(v___x_1928_, v___x_1927_);
v___x_1930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1926_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = l_Repr_addAppParen(v___x_1930_, v_x_1919_);
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___boxed(lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_x_1932_, v_x_1933_);
lean_dec(v_x_1933_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr(lean_object* v_x_2151_, lean_object* v_prec_2152_){
_start:
{
switch(lean_obj_tag(v_x_2151_))
{
case 0:
{
uint8_t v_presentation_2153_; lean_object* v___y_2155_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v_presentation_2153_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2164_ = lean_unsigned_to_nat(1024u);
v___x_2165_ = lean_nat_dec_le(v___x_2164_, v_prec_2152_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; 
v___x_2166_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2155_ = v___x_2166_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2155_ = v___x_2167_;
goto v___jp_2154_;
}
v___jp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2156_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__2));
v___x_2157_ = lean_unsigned_to_nat(1024u);
v___x_2158_ = l_Std_Time_instReprText_repr(v_presentation_2153_, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2156_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
lean_inc(v___y_2155_);
v___x_2160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___y_2155_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = 0;
v___x_2162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*1, v___x_2161_);
v___x_2163_ = l_Repr_addAppParen(v___x_2162_, v_prec_2152_);
return v___x_2163_;
}
}
case 1:
{
lean_object* v_presentation_2168_; lean_object* v___y_2170_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v_presentation_2168_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2168_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2179_ = lean_unsigned_to_nat(1024u);
v___x_2180_ = lean_nat_dec_le(v___x_2179_, v_prec_2152_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2170_ = v___x_2181_;
goto v___jp_2169_;
}
else
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2170_ = v___x_2182_;
goto v___jp_2169_;
}
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2171_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__5));
v___x_2172_ = lean_unsigned_to_nat(1024u);
v___x_2173_ = l_Std_Time_instReprYear_repr(v_presentation_2168_, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2171_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
lean_inc(v___y_2170_);
v___x_2175_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___y_2170_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = 0;
v___x_2177_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set_uint8(v___x_2177_, sizeof(void*)*1, v___x_2176_);
v___x_2178_ = l_Repr_addAppParen(v___x_2177_, v_prec_2152_);
return v___x_2178_;
}
}
case 2:
{
lean_object* v_presentation_2183_; lean_object* v___y_2185_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v_presentation_2183_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2183_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2194_ = lean_unsigned_to_nat(1024u);
v___x_2195_ = lean_nat_dec_le(v___x_2194_, v_prec_2152_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2185_ = v___x_2196_;
goto v___jp_2184_;
}
else
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2185_ = v___x_2197_;
goto v___jp_2184_;
}
v___jp_2184_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2186_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__8));
v___x_2187_ = lean_unsigned_to_nat(1024u);
v___x_2188_ = l_Std_Time_instReprYear_repr(v_presentation_2183_, v___x_2187_);
v___x_2189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2186_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
lean_inc(v___y_2185_);
v___x_2190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___y_2185_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = 0;
v___x_2192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*1, v___x_2191_);
v___x_2193_ = l_Repr_addAppParen(v___x_2192_, v_prec_2152_);
return v___x_2193_;
}
}
case 3:
{
lean_object* v_presentation_2198_; lean_object* v___y_2200_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v_presentation_2198_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2198_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2208_ = lean_unsigned_to_nat(1024u);
v___x_2209_ = lean_nat_dec_le(v___x_2208_, v_prec_2152_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; 
v___x_2210_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2200_ = v___x_2210_;
goto v___jp_2199_;
}
else
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2200_ = v___x_2211_;
goto v___jp_2199_;
}
v___jp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2201_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__11));
v___x_2202_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2198_);
v___x_2203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2201_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
lean_inc(v___y_2200_);
v___x_2204_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___y_2200_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = 0;
v___x_2206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*1, v___x_2205_);
v___x_2207_ = l_Repr_addAppParen(v___x_2206_, v_prec_2152_);
return v___x_2207_;
}
}
case 4:
{
lean_object* v_presentation_2212_; lean_object* v___y_2214_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_presentation_2212_ = lean_ctor_get(v_x_2151_, 0);
lean_inc_ref(v_presentation_2212_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2223_ = lean_unsigned_to_nat(1024u);
v___x_2224_ = lean_nat_dec_le(v___x_2223_, v_prec_2152_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2214_ = v___x_2225_;
goto v___jp_2213_;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2214_ = v___x_2226_;
goto v___jp_2213_;
}
v___jp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2215_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__14));
v___x_2216_ = lean_unsigned_to_nat(1024u);
v___x_2217_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2212_, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2215_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
lean_inc(v___y_2214_);
v___x_2219_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___y_2214_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = 0;
v___x_2221_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*1, v___x_2220_);
v___x_2222_ = l_Repr_addAppParen(v___x_2221_, v_prec_2152_);
return v___x_2222_;
}
}
case 5:
{
lean_object* v_presentation_2227_; lean_object* v___y_2229_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v_presentation_2227_ = lean_ctor_get(v_x_2151_, 0);
lean_inc_ref(v_presentation_2227_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2238_ = lean_unsigned_to_nat(1024u);
v___x_2239_ = lean_nat_dec_le(v___x_2238_, v_prec_2152_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2229_ = v___x_2240_;
goto v___jp_2228_;
}
else
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2229_ = v___x_2241_;
goto v___jp_2228_;
}
v___jp_2228_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2230_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__17));
v___x_2231_ = lean_unsigned_to_nat(1024u);
v___x_2232_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2227_, v___x_2231_);
v___x_2233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2230_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
lean_inc(v___y_2229_);
v___x_2234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___y_2229_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = 0;
v___x_2236_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2236_, 0, v___x_2234_);
lean_ctor_set_uint8(v___x_2236_, sizeof(void*)*1, v___x_2235_);
v___x_2237_ = l_Repr_addAppParen(v___x_2236_, v_prec_2152_);
return v___x_2237_;
}
}
case 6:
{
lean_object* v_presentation_2242_; lean_object* v___y_2244_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v_presentation_2242_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2242_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2252_ = lean_unsigned_to_nat(1024u);
v___x_2253_ = lean_nat_dec_le(v___x_2252_, v_prec_2152_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2244_ = v___x_2254_;
goto v___jp_2243_;
}
else
{
lean_object* v___x_2255_; 
v___x_2255_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2244_ = v___x_2255_;
goto v___jp_2243_;
}
v___jp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2245_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__20));
v___x_2246_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2242_);
v___x_2247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2245_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
lean_inc(v___y_2244_);
v___x_2248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___y_2244_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = 0;
v___x_2250_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set_uint8(v___x_2250_, sizeof(void*)*1, v___x_2249_);
v___x_2251_ = l_Repr_addAppParen(v___x_2250_, v_prec_2152_);
return v___x_2251_;
}
}
case 7:
{
lean_object* v_presentation_2256_; lean_object* v___y_2258_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_presentation_2256_ = lean_ctor_get(v_x_2151_, 0);
lean_inc_ref(v_presentation_2256_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2267_ = lean_unsigned_to_nat(1024u);
v___x_2268_ = lean_nat_dec_le(v___x_2267_, v_prec_2152_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2258_ = v___x_2269_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2270_; 
v___x_2270_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2258_ = v___x_2270_;
goto v___jp_2257_;
}
v___jp_2257_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2259_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__23));
v___x_2260_ = lean_unsigned_to_nat(1024u);
v___x_2261_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2256_, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2259_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
lean_inc(v___y_2258_);
v___x_2263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___y_2258_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = 0;
v___x_2265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*1, v___x_2264_);
v___x_2266_ = l_Repr_addAppParen(v___x_2265_, v_prec_2152_);
return v___x_2266_;
}
}
case 8:
{
lean_object* v_presentation_2271_; lean_object* v___y_2273_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_presentation_2271_ = lean_ctor_get(v_x_2151_, 0);
lean_inc_ref(v_presentation_2271_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2282_ = lean_unsigned_to_nat(1024u);
v___x_2283_ = lean_nat_dec_le(v___x_2282_, v_prec_2152_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2273_ = v___x_2284_;
goto v___jp_2272_;
}
else
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2273_ = v___x_2285_;
goto v___jp_2272_;
}
v___jp_2272_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2274_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__26));
v___x_2275_ = lean_unsigned_to_nat(1024u);
v___x_2276_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2271_, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2274_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
lean_inc(v___y_2273_);
v___x_2278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___y_2273_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = 0;
v___x_2280_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set_uint8(v___x_2280_, sizeof(void*)*1, v___x_2279_);
v___x_2281_ = l_Repr_addAppParen(v___x_2280_, v_prec_2152_);
return v___x_2281_;
}
}
case 9:
{
lean_object* v_presentation_2286_; lean_object* v___y_2288_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
v_presentation_2286_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2286_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2297_ = lean_unsigned_to_nat(1024u);
v___x_2298_ = lean_nat_dec_le(v___x_2297_, v_prec_2152_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2288_ = v___x_2299_;
goto v___jp_2287_;
}
else
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2288_ = v___x_2300_;
goto v___jp_2287_;
}
v___jp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2289_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__29));
v___x_2290_ = lean_unsigned_to_nat(1024u);
v___x_2291_ = l_Std_Time_instReprYear_repr(v_presentation_2286_, v___x_2290_);
v___x_2292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2289_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
lean_inc(v___y_2288_);
v___x_2293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___y_2288_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = 0;
v___x_2295_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1, v___x_2294_);
v___x_2296_ = l_Repr_addAppParen(v___x_2295_, v_prec_2152_);
return v___x_2296_;
}
}
case 10:
{
lean_object* v_presentation_2301_; lean_object* v___y_2303_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v_presentation_2301_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2301_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2311_ = lean_unsigned_to_nat(1024u);
v___x_2312_ = lean_nat_dec_le(v___x_2311_, v_prec_2152_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2303_ = v___x_2313_;
goto v___jp_2302_;
}
else
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2303_ = v___x_2314_;
goto v___jp_2302_;
}
v___jp_2302_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2304_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__32));
v___x_2305_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2301_);
v___x_2306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
lean_inc(v___y_2303_);
v___x_2307_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___y_2303_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = 0;
v___x_2309_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*1, v___x_2308_);
v___x_2310_ = l_Repr_addAppParen(v___x_2309_, v_prec_2152_);
return v___x_2310_;
}
}
case 11:
{
lean_object* v_presentation_2315_; lean_object* v___y_2317_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_presentation_2315_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2315_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2325_ = lean_unsigned_to_nat(1024u);
v___x_2326_ = lean_nat_dec_le(v___x_2325_, v_prec_2152_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2317_ = v___x_2327_;
goto v___jp_2316_;
}
else
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2317_ = v___x_2328_;
goto v___jp_2316_;
}
v___jp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2318_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__35));
v___x_2319_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2315_);
v___x_2320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
lean_inc(v___y_2317_);
v___x_2321_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___y_2317_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = 0;
v___x_2323_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*1, v___x_2322_);
v___x_2324_ = l_Repr_addAppParen(v___x_2323_, v_prec_2152_);
return v___x_2324_;
}
}
case 12:
{
uint8_t v_presentation_2329_; lean_object* v___y_2331_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v_presentation_2329_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2340_ = lean_unsigned_to_nat(1024u);
v___x_2341_ = lean_nat_dec_le(v___x_2340_, v_prec_2152_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2331_ = v___x_2342_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2331_ = v___x_2343_;
goto v___jp_2330_;
}
v___jp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2332_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__38));
v___x_2333_ = lean_unsigned_to_nat(1024u);
v___x_2334_ = l_Std_Time_instReprText_repr(v_presentation_2329_, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2332_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
lean_inc(v___y_2331_);
v___x_2336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___y_2331_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = 0;
v___x_2338_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2338_, 0, v___x_2336_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*1, v___x_2337_);
v___x_2339_ = l_Repr_addAppParen(v___x_2338_, v_prec_2152_);
return v___x_2339_;
}
}
case 13:
{
lean_object* v_presentation_2344_; lean_object* v___y_2346_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v_presentation_2344_ = lean_ctor_get(v_x_2151_, 0);
lean_inc_ref(v_presentation_2344_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2355_ = lean_unsigned_to_nat(1024u);
v___x_2356_ = lean_nat_dec_le(v___x_2355_, v_prec_2152_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2346_ = v___x_2357_;
goto v___jp_2345_;
}
else
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2346_ = v___x_2358_;
goto v___jp_2345_;
}
v___jp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2347_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__41));
v___x_2348_ = lean_unsigned_to_nat(1024u);
v___x_2349_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2344_, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2347_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
lean_inc(v___y_2346_);
v___x_2351_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___y_2346_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___x_2352_ = 0;
v___x_2353_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*1, v___x_2352_);
v___x_2354_ = l_Repr_addAppParen(v___x_2353_, v_prec_2152_);
return v___x_2354_;
}
}
case 14:
{
lean_object* v_presentation_2359_; lean_object* v___y_2361_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v_presentation_2359_ = lean_ctor_get(v_x_2151_, 0);
lean_inc_ref(v_presentation_2359_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2370_ = lean_unsigned_to_nat(1024u);
v___x_2371_ = lean_nat_dec_le(v___x_2370_, v_prec_2152_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2361_ = v___x_2372_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2361_ = v___x_2373_;
goto v___jp_2360_;
}
v___jp_2360_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2362_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__44));
v___x_2363_ = lean_unsigned_to_nat(1024u);
v___x_2364_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2359_, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2362_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
lean_inc(v___y_2361_);
v___x_2366_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___y_2361_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = 0;
v___x_2368_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*1, v___x_2367_);
v___x_2369_ = l_Repr_addAppParen(v___x_2368_, v_prec_2152_);
return v___x_2369_;
}
}
case 15:
{
lean_object* v_presentation_2374_; lean_object* v___y_2376_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v_presentation_2374_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2374_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2384_ = lean_unsigned_to_nat(1024u);
v___x_2385_ = lean_nat_dec_le(v___x_2384_, v_prec_2152_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2376_ = v___x_2386_;
goto v___jp_2375_;
}
else
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2376_ = v___x_2387_;
goto v___jp_2375_;
}
v___jp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2377_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__47));
v___x_2378_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2374_);
v___x_2379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
lean_inc(v___y_2376_);
v___x_2380_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___y_2376_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = 0;
v___x_2382_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set_uint8(v___x_2382_, sizeof(void*)*1, v___x_2381_);
v___x_2383_ = l_Repr_addAppParen(v___x_2382_, v_prec_2152_);
return v___x_2383_;
}
}
case 16:
{
uint8_t v_presentation_2388_; lean_object* v___y_2390_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v_presentation_2388_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2399_ = lean_unsigned_to_nat(1024u);
v___x_2400_ = lean_nat_dec_le(v___x_2399_, v_prec_2152_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2390_ = v___x_2401_;
goto v___jp_2389_;
}
else
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2390_ = v___x_2402_;
goto v___jp_2389_;
}
v___jp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2391_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__50));
v___x_2392_ = lean_unsigned_to_nat(1024u);
v___x_2393_ = l_Std_Time_instReprText_repr(v_presentation_2388_, v___x_2392_);
v___x_2394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2391_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
lean_inc(v___y_2390_);
v___x_2395_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___y_2390_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = 0;
v___x_2397_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1, v___x_2396_);
v___x_2398_ = l_Repr_addAppParen(v___x_2397_, v_prec_2152_);
return v___x_2398_;
}
}
case 17:
{
uint8_t v_presentation_2403_; lean_object* v___y_2405_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v_presentation_2403_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2414_ = lean_unsigned_to_nat(1024u);
v___x_2415_ = lean_nat_dec_le(v___x_2414_, v_prec_2152_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2405_ = v___x_2416_;
goto v___jp_2404_;
}
else
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2405_ = v___x_2417_;
goto v___jp_2404_;
}
v___jp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2406_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__53));
v___x_2407_ = lean_unsigned_to_nat(1024u);
v___x_2408_ = l_Std_Time_instReprText_repr(v_presentation_2403_, v___x_2407_);
v___x_2409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2406_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
lean_inc(v___y_2405_);
v___x_2410_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___y_2405_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = 0;
v___x_2412_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*1, v___x_2411_);
v___x_2413_ = l_Repr_addAppParen(v___x_2412_, v_prec_2152_);
return v___x_2413_;
}
}
case 18:
{
uint8_t v_presentation_2418_; lean_object* v___y_2420_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
v_presentation_2418_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2429_ = lean_unsigned_to_nat(1024u);
v___x_2430_ = lean_nat_dec_le(v___x_2429_, v_prec_2152_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2420_ = v___x_2431_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2432_; 
v___x_2432_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2420_ = v___x_2432_;
goto v___jp_2419_;
}
v___jp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2421_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__56));
v___x_2422_ = lean_unsigned_to_nat(1024u);
v___x_2423_ = l_Std_Time_instReprText_repr(v_presentation_2418_, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2421_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
lean_inc(v___y_2420_);
v___x_2425_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___y_2420_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = 0;
v___x_2427_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*1, v___x_2426_);
v___x_2428_ = l_Repr_addAppParen(v___x_2427_, v_prec_2152_);
return v___x_2428_;
}
}
case 19:
{
lean_object* v_presentation_2433_; lean_object* v___y_2435_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v_presentation_2433_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2433_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2443_ = lean_unsigned_to_nat(1024u);
v___x_2444_ = lean_nat_dec_le(v___x_2443_, v_prec_2152_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2435_ = v___x_2445_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2435_ = v___x_2446_;
goto v___jp_2434_;
}
v___jp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2436_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__59));
v___x_2437_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2433_);
v___x_2438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
lean_inc(v___y_2435_);
v___x_2439_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___y_2435_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = 0;
v___x_2441_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*1, v___x_2440_);
v___x_2442_ = l_Repr_addAppParen(v___x_2441_, v_prec_2152_);
return v___x_2442_;
}
}
case 20:
{
lean_object* v_presentation_2447_; lean_object* v___y_2449_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v_presentation_2447_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2447_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2457_ = lean_unsigned_to_nat(1024u);
v___x_2458_ = lean_nat_dec_le(v___x_2457_, v_prec_2152_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2449_ = v___x_2459_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2449_ = v___x_2460_;
goto v___jp_2448_;
}
v___jp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2450_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__62));
v___x_2451_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2447_);
v___x_2452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
lean_inc(v___y_2449_);
v___x_2453_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___y_2449_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = 0;
v___x_2455_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2455_, 0, v___x_2453_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*1, v___x_2454_);
v___x_2456_ = l_Repr_addAppParen(v___x_2455_, v_prec_2152_);
return v___x_2456_;
}
}
case 21:
{
lean_object* v_presentation_2461_; lean_object* v___y_2463_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v_presentation_2461_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2461_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2471_ = lean_unsigned_to_nat(1024u);
v___x_2472_ = lean_nat_dec_le(v___x_2471_, v_prec_2152_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2463_ = v___x_2473_;
goto v___jp_2462_;
}
else
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2463_ = v___x_2474_;
goto v___jp_2462_;
}
v___jp_2462_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2464_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__65));
v___x_2465_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2461_);
v___x_2466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
lean_inc(v___y_2463_);
v___x_2467_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___y_2463_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = 0;
v___x_2469_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*1, v___x_2468_);
v___x_2470_ = l_Repr_addAppParen(v___x_2469_, v_prec_2152_);
return v___x_2470_;
}
}
case 22:
{
lean_object* v_presentation_2475_; lean_object* v___y_2477_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_presentation_2475_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2475_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2485_ = lean_unsigned_to_nat(1024u);
v___x_2486_ = lean_nat_dec_le(v___x_2485_, v_prec_2152_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2477_ = v___x_2487_;
goto v___jp_2476_;
}
else
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2477_ = v___x_2488_;
goto v___jp_2476_;
}
v___jp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2478_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__68));
v___x_2479_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2475_);
v___x_2480_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
lean_inc(v___y_2477_);
v___x_2481_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___y_2477_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = 0;
v___x_2483_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*1, v___x_2482_);
v___x_2484_ = l_Repr_addAppParen(v___x_2483_, v_prec_2152_);
return v___x_2484_;
}
}
case 23:
{
lean_object* v_presentation_2489_; lean_object* v___y_2491_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v_presentation_2489_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2489_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2499_ = lean_unsigned_to_nat(1024u);
v___x_2500_ = lean_nat_dec_le(v___x_2499_, v_prec_2152_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2491_ = v___x_2501_;
goto v___jp_2490_;
}
else
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2491_ = v___x_2502_;
goto v___jp_2490_;
}
v___jp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2492_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__71));
v___x_2493_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2489_);
v___x_2494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
lean_inc(v___y_2491_);
v___x_2495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___y_2491_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = 0;
v___x_2497_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2497_, 0, v___x_2495_);
lean_ctor_set_uint8(v___x_2497_, sizeof(void*)*1, v___x_2496_);
v___x_2498_ = l_Repr_addAppParen(v___x_2497_, v_prec_2152_);
return v___x_2498_;
}
}
case 24:
{
lean_object* v_presentation_2503_; lean_object* v___y_2505_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v_presentation_2503_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2503_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2513_ = lean_unsigned_to_nat(1024u);
v___x_2514_ = lean_nat_dec_le(v___x_2513_, v_prec_2152_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2505_ = v___x_2515_;
goto v___jp_2504_;
}
else
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2505_ = v___x_2516_;
goto v___jp_2504_;
}
v___jp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2506_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__74));
v___x_2507_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2503_);
v___x_2508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
lean_inc(v___y_2505_);
v___x_2509_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___y_2505_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = 0;
v___x_2511_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*1, v___x_2510_);
v___x_2512_ = l_Repr_addAppParen(v___x_2511_, v_prec_2152_);
return v___x_2512_;
}
}
case 25:
{
lean_object* v_presentation_2517_; lean_object* v___y_2519_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v_presentation_2517_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2517_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2528_ = lean_unsigned_to_nat(1024u);
v___x_2529_ = lean_nat_dec_le(v___x_2528_, v_prec_2152_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2519_ = v___x_2530_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2519_ = v___x_2531_;
goto v___jp_2518_;
}
v___jp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2520_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__77));
v___x_2521_ = lean_unsigned_to_nat(1024u);
v___x_2522_ = l_Std_Time_instReprFraction_repr(v_presentation_2517_, v___x_2521_);
v___x_2523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2520_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
lean_inc(v___y_2519_);
v___x_2524_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___y_2519_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = 0;
v___x_2526_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*1, v___x_2525_);
v___x_2527_ = l_Repr_addAppParen(v___x_2526_, v_prec_2152_);
return v___x_2527_;
}
}
case 26:
{
lean_object* v_presentation_2532_; lean_object* v___y_2534_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v_presentation_2532_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2532_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2542_ = lean_unsigned_to_nat(1024u);
v___x_2543_ = lean_nat_dec_le(v___x_2542_, v_prec_2152_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2534_ = v___x_2544_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2534_ = v___x_2545_;
goto v___jp_2533_;
}
v___jp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2535_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__80));
v___x_2536_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2532_);
v___x_2537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
lean_inc(v___y_2534_);
v___x_2538_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___y_2534_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = 0;
v___x_2540_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*1, v___x_2539_);
v___x_2541_ = l_Repr_addAppParen(v___x_2540_, v_prec_2152_);
return v___x_2541_;
}
}
case 27:
{
lean_object* v_presentation_2546_; lean_object* v___y_2548_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v_presentation_2546_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2546_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2556_ = lean_unsigned_to_nat(1024u);
v___x_2557_ = lean_nat_dec_le(v___x_2556_, v_prec_2152_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2548_ = v___x_2558_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2548_ = v___x_2559_;
goto v___jp_2547_;
}
v___jp_2547_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2549_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__83));
v___x_2550_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2546_);
v___x_2551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
lean_inc(v___y_2548_);
v___x_2552_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___y_2548_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = 0;
v___x_2554_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set_uint8(v___x_2554_, sizeof(void*)*1, v___x_2553_);
v___x_2555_ = l_Repr_addAppParen(v___x_2554_, v_prec_2152_);
return v___x_2555_;
}
}
case 28:
{
lean_object* v_presentation_2560_; lean_object* v___y_2562_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_presentation_2560_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_presentation_2560_);
lean_dec_ref_known(v_x_2151_, 1);
v___x_2570_ = lean_unsigned_to_nat(1024u);
v___x_2571_ = lean_nat_dec_le(v___x_2570_, v_prec_2152_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2562_ = v___x_2572_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2562_ = v___x_2573_;
goto v___jp_2561_;
}
v___jp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2563_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__86));
v___x_2564_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2560_);
v___x_2565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2563_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
lean_inc(v___y_2562_);
v___x_2566_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___y_2562_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = 0;
v___x_2568_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2568_, 0, v___x_2566_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*1, v___x_2567_);
v___x_2569_ = l_Repr_addAppParen(v___x_2568_, v_prec_2152_);
return v___x_2569_;
}
}
case 29:
{
uint8_t v_presentation_2574_; lean_object* v___y_2576_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v_presentation_2574_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2585_ = lean_unsigned_to_nat(1024u);
v___x_2586_ = lean_nat_dec_le(v___x_2585_, v_prec_2152_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2576_ = v___x_2587_;
goto v___jp_2575_;
}
else
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2576_ = v___x_2588_;
goto v___jp_2575_;
}
v___jp_2575_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2577_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__89));
v___x_2578_ = lean_unsigned_to_nat(1024u);
v___x_2579_ = l_Std_Time_instReprZoneId_repr(v_presentation_2574_, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2577_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
lean_inc(v___y_2576_);
v___x_2581_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___y_2576_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = 0;
v___x_2583_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set_uint8(v___x_2583_, sizeof(void*)*1, v___x_2582_);
v___x_2584_ = l_Repr_addAppParen(v___x_2583_, v_prec_2152_);
return v___x_2584_;
}
}
case 30:
{
uint8_t v_presentation_2589_; lean_object* v___y_2591_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_presentation_2589_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2600_ = lean_unsigned_to_nat(1024u);
v___x_2601_ = lean_nat_dec_le(v___x_2600_, v_prec_2152_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2591_ = v___x_2602_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2591_ = v___x_2603_;
goto v___jp_2590_;
}
v___jp_2590_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2592_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__92));
v___x_2593_ = lean_unsigned_to_nat(1024u);
v___x_2594_ = l_Std_Time_instReprZoneName_repr(v_presentation_2589_, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2592_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
lean_inc(v___y_2591_);
v___x_2596_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___y_2591_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = 0;
v___x_2598_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*1, v___x_2597_);
v___x_2599_ = l_Repr_addAppParen(v___x_2598_, v_prec_2152_);
return v___x_2599_;
}
}
case 31:
{
uint8_t v_presentation_2604_; lean_object* v___y_2606_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v_presentation_2604_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2615_ = lean_unsigned_to_nat(1024u);
v___x_2616_ = lean_nat_dec_le(v___x_2615_, v_prec_2152_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
v___x_2617_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2606_ = v___x_2617_;
goto v___jp_2605_;
}
else
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2606_ = v___x_2618_;
goto v___jp_2605_;
}
v___jp_2605_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2607_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__95));
v___x_2608_ = lean_unsigned_to_nat(1024u);
v___x_2609_ = l_Std_Time_instReprZoneName_repr(v_presentation_2604_, v___x_2608_);
v___x_2610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2607_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
lean_inc(v___y_2606_);
v___x_2611_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___y_2606_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = 0;
v___x_2613_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set_uint8(v___x_2613_, sizeof(void*)*1, v___x_2612_);
v___x_2614_ = l_Repr_addAppParen(v___x_2613_, v_prec_2152_);
return v___x_2614_;
}
}
case 32:
{
uint8_t v_presentation_2619_; lean_object* v___y_2621_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v_presentation_2619_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2630_ = lean_unsigned_to_nat(1024u);
v___x_2631_ = lean_nat_dec_le(v___x_2630_, v_prec_2152_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2621_ = v___x_2632_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2621_ = v___x_2633_;
goto v___jp_2620_;
}
v___jp_2620_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2622_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__98));
v___x_2623_ = lean_unsigned_to_nat(1024u);
v___x_2624_ = l_Std_Time_instReprOffsetO_repr(v_presentation_2619_, v___x_2623_);
v___x_2625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2622_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
lean_inc(v___y_2621_);
v___x_2626_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___y_2621_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = 0;
v___x_2628_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2628_, 0, v___x_2626_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*1, v___x_2627_);
v___x_2629_ = l_Repr_addAppParen(v___x_2628_, v_prec_2152_);
return v___x_2629_;
}
}
case 33:
{
uint8_t v_presentation_2634_; lean_object* v___y_2636_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v_presentation_2634_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2645_ = lean_unsigned_to_nat(1024u);
v___x_2646_ = lean_nat_dec_le(v___x_2645_, v_prec_2152_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; 
v___x_2647_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2636_ = v___x_2647_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2636_ = v___x_2648_;
goto v___jp_2635_;
}
v___jp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2637_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__101));
v___x_2638_ = lean_unsigned_to_nat(1024u);
v___x_2639_ = l_Std_Time_instReprOffsetX_repr(v_presentation_2634_, v___x_2638_);
v___x_2640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2637_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
lean_inc(v___y_2636_);
v___x_2641_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___y_2636_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = 0;
v___x_2643_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2643_, 0, v___x_2641_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*1, v___x_2642_);
v___x_2644_ = l_Repr_addAppParen(v___x_2643_, v_prec_2152_);
return v___x_2644_;
}
}
case 34:
{
uint8_t v_presentation_2649_; lean_object* v___y_2651_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
v_presentation_2649_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2660_ = lean_unsigned_to_nat(1024u);
v___x_2661_ = lean_nat_dec_le(v___x_2660_, v_prec_2152_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2651_ = v___x_2662_;
goto v___jp_2650_;
}
else
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2651_ = v___x_2663_;
goto v___jp_2650_;
}
v___jp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2652_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__104));
v___x_2653_ = lean_unsigned_to_nat(1024u);
v___x_2654_ = l_Std_Time_instReprOffsetX_repr(v_presentation_2649_, v___x_2653_);
v___x_2655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2652_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
lean_inc(v___y_2651_);
v___x_2656_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___y_2651_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = 0;
v___x_2658_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*1, v___x_2657_);
v___x_2659_ = l_Repr_addAppParen(v___x_2658_, v_prec_2152_);
return v___x_2659_;
}
}
default: 
{
uint8_t v_presentation_2664_; lean_object* v___y_2666_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v_presentation_2664_ = lean_ctor_get_uint8(v_x_2151_, 0);
lean_dec_ref_known(v_x_2151_, 0);
v___x_2675_ = lean_unsigned_to_nat(1024u);
v___x_2676_ = lean_nat_dec_le(v___x_2675_, v_prec_2152_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2666_ = v___x_2677_;
goto v___jp_2665_;
}
else
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2666_ = v___x_2678_;
goto v___jp_2665_;
}
v___jp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2667_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__107));
v___x_2668_ = lean_unsigned_to_nat(1024u);
v___x_2669_ = l_Std_Time_instReprOffsetZ_repr(v_presentation_2664_, v___x_2668_);
v___x_2670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2667_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
lean_inc(v___y_2666_);
v___x_2671_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___y_2666_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = 0;
v___x_2673_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*1, v___x_2672_);
v___x_2674_ = l_Repr_addAppParen(v___x_2673_, v_prec_2152_);
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr___boxed(lean_object* v_x_2679_, lean_object* v_prec_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Std_Time_instReprModifier_repr(v_x_2679_, v_prec_2680_);
lean_dec(v_prec_2680_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(lean_object* v_constructor_2691_, lean_object* v_classify_2692_, lean_object* v_p_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_len_2695_; lean_object* v___x_2696_; 
v_len_2695_ = lean_string_length(v_p_2693_);
v___x_2696_ = lean_apply_1(v_classify_2692_, v_len_2695_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v___x_2697_; uint32_t v___y_2699_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec_ref(v_constructor_2691_);
v___x_2697_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_string_utf8_byte_size(v_p_2693_);
v___x_2709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2709_, 0, v_p_2693_);
lean_ctor_set(v___x_2709_, 1, v___x_2707_);
lean_ctor_set(v___x_2709_, 2, v___x_2708_);
v___x_2710_ = l_String_Slice_Pos_get_x3f(v___x_2709_, v___x_2707_);
lean_dec_ref_known(v___x_2709_, 3);
if (lean_obj_tag(v___x_2710_) == 0)
{
uint32_t v___x_2711_; 
v___x_2711_ = 65;
v___y_2699_ = v___x_2711_;
goto v___jp_2698_;
}
else
{
lean_object* v_val_2712_; uint32_t v___x_2713_; 
v_val_2712_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_val_2712_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2713_ = lean_unbox_uint32(v_val_2712_);
lean_dec(v_val_2712_);
v___y_2699_ = v___x_2713_;
goto v___jp_2698_;
}
v___jp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2700_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2701_ = lean_string_push(v___x_2700_, v___y_2699_);
v___x_2702_ = lean_string_append(v___x_2697_, v___x_2701_);
lean_dec_ref(v___x_2701_);
v___x_2703_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_2704_ = lean_string_append(v___x_2702_, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_a_2694_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
return v___x_2706_;
}
}
else
{
lean_object* v_val_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_dec_ref(v_p_2693_);
v_val_2714_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_val_2714_);
lean_dec_ref_known(v___x_2696_, 1);
v___x_2715_ = lean_apply_1(v_constructor_2691_, v_val_2714_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_a_2694_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
return v___x_2716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod(lean_object* v_00_u03b1_2717_, lean_object* v_constructor_2718_, lean_object* v_classify_2719_, lean_object* v_p_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2718_, v_classify_2719_, v_p_2720_, v_a_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(lean_object* v_constructor_2724_, lean_object* v_p_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseText___closed__0));
v___x_2728_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2724_, v___x_2727_, v_p_2725_, v_a_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(lean_object* v_max_2729_, lean_object* v_x_2730_){
_start:
{
uint8_t v___x_2731_; 
v___x_2731_ = lean_nat_dec_le(v_x_2730_, v_max_2729_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; 
lean_dec(v_x_2730_);
v___x_2732_ = lean_box(0);
return v___x_2732_;
}
else
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2733_, 0, v_x_2730_);
return v___x_2733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax___boxed(lean_object* v_max_2734_, lean_object* v_x_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(v_max_2734_, v_x_2735_);
lean_dec(v_max_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(lean_object* v_x_2739_){
_start:
{
lean_object* v___x_2740_; uint8_t v___x_2741_; 
v___x_2740_ = lean_unsigned_to_nat(1u);
v___x_2741_ = lean_nat_dec_eq(v_x_2739_, v___x_2740_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; 
v___x_2742_ = lean_box(0);
return v___x_2742_;
}
else
{
lean_object* v___x_2743_; 
v___x_2743_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___closed__0));
return v___x_2743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___boxed(lean_object* v_x_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(v_x_2744_);
lean_dec(v_x_2744_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(lean_object* v_x_2749_){
_start:
{
lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = lean_unsigned_to_nat(6u);
v___x_2751_ = lean_nat_dec_eq(v_x_2749_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Std_Time_Text_classify(v_x_2749_);
return v___x_2752_;
}
else
{
lean_object* v___x_2753_; 
v___x_2753_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___closed__0));
return v___x_2753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___boxed(lean_object* v_x_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(v_x_2754_);
lean_dec(v_x_2754_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(lean_object* v_constructor_2757_, lean_object* v_p_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText___closed__0));
v___x_2761_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2757_, v___x_2760_, v_p_2758_, v_a_2759_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(lean_object* v_constructor_2763_, lean_object* v_p_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction___closed__0));
v___x_2767_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2763_, v___x_2766_, v_p_2764_, v_a_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(lean_object* v_constructor_2768_, lean_object* v_p_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = lean_string_length(v_p_2769_);
v___x_2772_ = lean_apply_1(v_constructor_2768_, v___x_2771_);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v_a_2770_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber___boxed(lean_object* v_constructor_2774_, lean_object* v_p_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v_constructor_2774_, v_p_2775_, v_a_2776_);
lean_dec_ref(v_p_2775_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(lean_object* v_constructor_2779_, lean_object* v_p_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear___closed__0));
v___x_2783_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2779_, v___x_2782_, v_p_2780_, v_a_2781_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(lean_object* v_constructor_2785_, lean_object* v_p_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX___closed__0));
v___x_2789_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2785_, v___x_2788_, v_p_2786_, v_a_2787_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(lean_object* v_constructor_2791_, lean_object* v_p_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ___closed__0));
v___x_2795_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2791_, v___x_2794_, v_p_2792_, v_a_2793_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(lean_object* v_constructor_2797_, lean_object* v_p_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO___closed__0));
v___x_2801_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2797_, v___x_2800_, v_p_2798_, v_a_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(lean_object* v_p_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v___x_2809_ = lean_string_length(v_p_2807_);
v___x_2810_ = lean_unsigned_to_nat(1u);
v___x_2811_ = lean_nat_dec_eq(v___x_2809_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = lean_unsigned_to_nat(2u);
v___x_2813_ = lean_nat_dec_eq(v___x_2809_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; uint32_t v___y_2816_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2814_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = lean_string_utf8_byte_size(v_p_2807_);
v___x_2826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2826_, 0, v_p_2807_);
lean_ctor_set(v___x_2826_, 1, v___x_2824_);
lean_ctor_set(v___x_2826_, 2, v___x_2825_);
v___x_2827_ = l_String_Slice_Pos_get_x3f(v___x_2826_, v___x_2824_);
lean_dec_ref_known(v___x_2826_, 3);
if (lean_obj_tag(v___x_2827_) == 0)
{
uint32_t v___x_2828_; 
v___x_2828_ = 65;
v___y_2816_ = v___x_2828_;
goto v___jp_2815_;
}
else
{
lean_object* v_val_2829_; uint32_t v___x_2830_; 
v_val_2829_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_val_2829_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2830_ = lean_unbox_uint32(v_val_2829_);
lean_dec(v_val_2829_);
v___y_2816_ = v___x_2830_;
goto v___jp_2815_;
}
v___jp_2815_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2817_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2818_ = lean_string_push(v___x_2817_, v___y_2816_);
v___x_2819_ = lean_string_append(v___x_2814_, v___x_2818_);
lean_dec_ref(v___x_2818_);
v___x_2820_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__0));
v___x_2821_ = lean_string_append(v___x_2819_, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
v___x_2823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2823_, 0, v_a_2808_);
lean_ctor_set(v___x_2823_, 1, v___x_2822_);
return v___x_2823_;
}
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_dec_ref(v_p_2807_);
v___x_2831_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__1));
v___x_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2832_, 0, v_a_2808_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
return v___x_2832_;
}
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref(v_p_2807_);
v___x_2833_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__2));
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v_a_2808_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(lean_object* v_constructor_2836_, lean_object* v_p_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText___closed__0));
v___x_2840_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2836_, v___x_2839_, v_p_2837_, v_a_2838_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText(lean_object* v_x_2846_){
_start:
{
lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = lean_unsigned_to_nat(3u);
v___x_2848_ = lean_nat_dec_lt(v_x_2846_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = lean_unsigned_to_nat(6u);
v___x_2850_ = lean_nat_dec_eq(v_x_2846_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Std_Time_Text_classify(v_x_2846_);
lean_dec(v_x_2846_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2852_; 
v___x_2852_ = lean_box(0);
return v___x_2852_;
}
else
{
lean_object* v_val_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2861_; 
v_val_2853_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2855_ = v___x_2851_;
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_val_2853_);
lean_dec(v___x_2851_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_val_2853_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2857_);
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_object* v___x_2862_; 
lean_dec(v_x_2846_);
v___x_2862_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1));
return v___x_2862_;
}
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2863_, 0, v_x_2846_);
v___x_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(lean_object* v_constructor_2866_, lean_object* v_p_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText___closed__0));
v___x_2870_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2866_, v___x_2869_, v_p_2867_, v_a_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(lean_object* v_x_2875_){
_start:
{
lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2876_ = lean_unsigned_to_nat(1u);
v___x_2877_ = lean_nat_dec_eq(v_x_2875_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2878_ = lean_unsigned_to_nat(6u);
v___x_2879_ = lean_nat_dec_eq(v_x_2875_, v___x_2878_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2880_ = lean_unsigned_to_nat(3u);
v___x_2881_ = lean_nat_dec_le(v___x_2880_, v_x_2875_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; 
v___x_2882_ = lean_box(0);
return v___x_2882_;
}
else
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Std_Time_Text_classify(v_x_2875_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2884_; 
v___x_2884_ = lean_box(0);
return v___x_2884_;
}
else
{
lean_object* v_val_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2893_; 
v_val_2885_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2887_ = v___x_2883_;
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_val_2885_);
lean_dec(v___x_2883_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_val_2885_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2889_);
v___x_2891_ = v___x_2887_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
else
{
lean_object* v___x_2894_; 
v___x_2894_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1));
return v___x_2894_;
}
}
else
{
lean_object* v___x_2895_; 
v___x_2895_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__1));
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___boxed(lean_object* v_x_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(v_x_2896_);
lean_dec(v_x_2896_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(lean_object* v_constructor_2899_, lean_object* v_p_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText___closed__0));
v___x_2903_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2899_, v___x_2902_, v_p_2900_, v_a_2901_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(uint8_t v_presentation_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = lean_alloc_ctor(16, 0, 1);
lean_ctor_set_uint8(v___x_2905_, 0, v_presentation_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0___boxed(lean_object* v_presentation_2906_){
_start:
{
uint8_t v_presentation_boxed_2907_; lean_object* v_res_2908_; 
v_presentation_boxed_2907_ = lean_unbox(v_presentation_2906_);
v_res_2908_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(v_presentation_boxed_2907_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(lean_object* v_p_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v___f_2912_; lean_object* v___x_2913_; 
v___f_2912_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___closed__0));
v___x_2913_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2912_, v_p_2910_, v_a_2911_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(uint8_t v_presentation_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_alloc_ctor(17, 0, 1);
lean_ctor_set_uint8(v___x_2915_, 0, v_presentation_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0___boxed(lean_object* v_presentation_2916_){
_start:
{
uint8_t v_presentation_boxed_2917_; lean_object* v_res_2918_; 
v_presentation_boxed_2917_ = lean_unbox(v_presentation_2916_);
v_res_2918_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(v_presentation_boxed_2917_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(lean_object* v_p_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___f_2922_; lean_object* v___x_2923_; 
v___f_2922_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___closed__0));
v___x_2923_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2922_, v_p_2920_, v_a_2921_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(uint8_t v_presentation_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_alloc_ctor(18, 0, 1);
lean_ctor_set_uint8(v___x_2925_, 0, v_presentation_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0___boxed(lean_object* v_presentation_2926_){
_start:
{
uint8_t v_presentation_boxed_2927_; lean_object* v_res_2928_; 
v_presentation_boxed_2927_ = lean_unbox(v_presentation_2926_);
v_res_2928_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(v_presentation_boxed_2927_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(lean_object* v_p_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___f_2932_; lean_object* v___x_2933_; 
v___f_2932_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___closed__0));
v___x_2933_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2932_, v_p_2930_, v_a_2931_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(lean_object* v_constructor_2934_, lean_object* v_p_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v___y_2938_; uint32_t v___y_2939_; lean_object* v_len_2947_; uint32_t v___y_2949_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_len_2947_ = lean_string_length(v_p_2935_);
v___x_2962_ = lean_unsigned_to_nat(0u);
v___x_2963_ = lean_string_utf8_byte_size(v_p_2935_);
lean_inc_ref(v_p_2935_);
v___x_2964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2964_, 0, v_p_2935_);
lean_ctor_set(v___x_2964_, 1, v___x_2962_);
lean_ctor_set(v___x_2964_, 2, v___x_2963_);
v___x_2965_ = l_String_Slice_Pos_get_x3f(v___x_2964_, v___x_2962_);
lean_dec_ref_known(v___x_2964_, 3);
if (lean_obj_tag(v___x_2965_) == 0)
{
uint32_t v___x_2966_; 
v___x_2966_ = 65;
v___y_2949_ = v___x_2966_;
goto v___jp_2948_;
}
else
{
lean_object* v_val_2967_; uint32_t v___x_2968_; 
v_val_2967_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_val_2967_);
lean_dec_ref_known(v___x_2965_, 1);
v___x_2968_ = lean_unbox_uint32(v_val_2967_);
lean_dec(v_val_2967_);
v___y_2949_ = v___x_2968_;
goto v___jp_2948_;
}
v___jp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2940_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2941_ = lean_string_push(v___x_2940_, v___y_2939_);
lean_inc_ref(v___y_2938_);
v___x_2942_ = lean_string_append(v___y_2938_, v___x_2941_);
lean_dec_ref(v___x_2941_);
v___x_2943_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_2944_ = lean_string_append(v___x_2942_, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
v___x_2946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2946_, 0, v_a_2936_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
return v___x_2946_;
}
v___jp_2948_:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Std_Time_ZoneName_classify(v___y_2949_, v_len_2947_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_dec_ref(v_constructor_2934_);
v___x_2951_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2952_ = lean_unsigned_to_nat(0u);
v___x_2953_ = lean_string_utf8_byte_size(v_p_2935_);
v___x_2954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2954_, 0, v_p_2935_);
lean_ctor_set(v___x_2954_, 1, v___x_2952_);
lean_ctor_set(v___x_2954_, 2, v___x_2953_);
v___x_2955_ = l_String_Slice_Pos_get_x3f(v___x_2954_, v___x_2952_);
lean_dec_ref_known(v___x_2954_, 3);
if (lean_obj_tag(v___x_2955_) == 0)
{
uint32_t v___x_2956_; 
v___x_2956_ = 65;
v___y_2938_ = v___x_2951_;
v___y_2939_ = v___x_2956_;
goto v___jp_2937_;
}
else
{
lean_object* v_val_2957_; uint32_t v___x_2958_; 
v_val_2957_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_val_2957_);
lean_dec_ref_known(v___x_2955_, 1);
v___x_2958_ = lean_unbox_uint32(v_val_2957_);
lean_dec(v_val_2957_);
v___y_2938_ = v___x_2951_;
v___y_2939_ = v___x_2958_;
goto v___jp_2937_;
}
}
else
{
lean_object* v_val_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
lean_dec_ref(v_p_2935_);
v_val_2959_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_val_2959_);
lean_dec_ref_known(v___x_2950_, 1);
v___x_2960_ = lean_apply_1(v_constructor_2934_, v_val_2959_);
v___x_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2961_, 0, v_a_2936_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
return v___x_2961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0(uint8_t v_presentation_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = lean_alloc_ctor(35, 0, 1);
lean_ctor_set_uint8(v___x_2970_, 0, v_presentation_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0___boxed(lean_object* v_presentation_2971_){
_start:
{
uint8_t v_presentation_boxed_2972_; lean_object* v_res_2973_; 
v_presentation_boxed_2972_ = lean_unbox(v_presentation_2971_);
v_res_2973_ = l_Std_Time_parseModifier___lam__0(v_presentation_boxed_2972_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1(uint8_t v_presentation_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_alloc_ctor(34, 0, 1);
lean_ctor_set_uint8(v___x_2975_, 0, v_presentation_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1___boxed(lean_object* v_presentation_2976_){
_start:
{
uint8_t v_presentation_boxed_2977_; lean_object* v_res_2978_; 
v_presentation_boxed_2977_ = lean_unbox(v_presentation_2976_);
v_res_2978_ = l_Std_Time_parseModifier___lam__1(v_presentation_boxed_2977_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2(uint8_t v_presentation_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_alloc_ctor(33, 0, 1);
lean_ctor_set_uint8(v___x_2980_, 0, v_presentation_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2___boxed(lean_object* v_presentation_2981_){
_start:
{
uint8_t v_presentation_boxed_2982_; lean_object* v_res_2983_; 
v_presentation_boxed_2982_ = lean_unbox(v_presentation_2981_);
v_res_2983_ = l_Std_Time_parseModifier___lam__2(v_presentation_boxed_2982_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3(uint8_t v_presentation_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_alloc_ctor(32, 0, 1);
lean_ctor_set_uint8(v___x_2985_, 0, v_presentation_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3___boxed(lean_object* v_presentation_2986_){
_start:
{
uint8_t v_presentation_boxed_2987_; lean_object* v_res_2988_; 
v_presentation_boxed_2987_ = lean_unbox(v_presentation_2986_);
v_res_2988_ = l_Std_Time_parseModifier___lam__3(v_presentation_boxed_2987_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4(uint8_t v_presentation_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_alloc_ctor(31, 0, 1);
lean_ctor_set_uint8(v___x_2990_, 0, v_presentation_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4___boxed(lean_object* v_presentation_2991_){
_start:
{
uint8_t v_presentation_boxed_2992_; lean_object* v_res_2993_; 
v_presentation_boxed_2992_ = lean_unbox(v_presentation_2991_);
v_res_2993_ = l_Std_Time_parseModifier___lam__4(v_presentation_boxed_2992_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5(uint8_t v_presentation_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_alloc_ctor(30, 0, 1);
lean_ctor_set_uint8(v___x_2995_, 0, v_presentation_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5___boxed(lean_object* v_presentation_2996_){
_start:
{
uint8_t v_presentation_boxed_2997_; lean_object* v_res_2998_; 
v_presentation_boxed_2997_ = lean_unbox(v_presentation_2996_);
v_res_2998_ = l_Std_Time_parseModifier___lam__5(v_presentation_boxed_2997_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__6(lean_object* v_presentation_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_alloc_ctor(28, 1, 0);
lean_ctor_set(v___x_3000_, 0, v_presentation_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__7(lean_object* v_presentation_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_alloc_ctor(27, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_presentation_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__8(lean_object* v_presentation_3003_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_alloc_ctor(26, 1, 0);
lean_ctor_set(v___x_3004_, 0, v_presentation_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__9(lean_object* v_presentation_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_alloc_ctor(25, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_presentation_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__10(lean_object* v_presentation_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_alloc_ctor(24, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_presentation_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__11(lean_object* v_presentation_3009_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_alloc_ctor(23, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_presentation_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__12(lean_object* v_presentation_3011_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_presentation_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__13(lean_object* v_presentation_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_presentation_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__14(lean_object* v_presentation_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(v___x_3016_, 0, v_presentation_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__15(lean_object* v_presentation_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_alloc_ctor(19, 1, 0);
lean_ctor_set(v___x_3018_, 0, v_presentation_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__16(lean_object* v_presentation_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_3020_, 0, v_presentation_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__17(lean_object* v_presentation_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_3022_, 0, v_presentation_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__18(lean_object* v_presentation_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_3024_, 0, v_presentation_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19(uint8_t v_presentation_3025_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_alloc_ctor(12, 0, 1);
lean_ctor_set_uint8(v___x_3026_, 0, v_presentation_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19___boxed(lean_object* v_presentation_3027_){
_start:
{
uint8_t v_presentation_boxed_3028_; lean_object* v_res_3029_; 
v_presentation_boxed_3028_ = lean_unbox(v_presentation_3027_);
v_res_3029_ = l_Std_Time_parseModifier___lam__19(v_presentation_boxed_3028_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__20(lean_object* v_presentation_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_3031_, 0, v_presentation_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__21(lean_object* v_presentation_3032_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_presentation_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__22(lean_object* v_presentation_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_presentation_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__23(lean_object* v_presentation_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3037_, 0, v_presentation_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__24(lean_object* v_presentation_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_presentation_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__25(lean_object* v_presentation_3040_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3041_, 0, v_presentation_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__26(lean_object* v_presentation_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3043_, 0, v_presentation_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__27(lean_object* v_presentation_3044_){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3045_, 0, v_presentation_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__28(lean_object* v_presentation_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_presentation_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__29(lean_object* v_presentation_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_presentation_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__30(lean_object* v_presentation_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3051_, 0, v_presentation_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31(uint8_t v_presentation_3052_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3053_, 0, v_presentation_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31___boxed(lean_object* v_presentation_3054_){
_start:
{
uint8_t v_presentation_boxed_3055_; lean_object* v_res_3056_; 
v_presentation_boxed_3055_ = lean_unbox(v_presentation_3054_);
v_res_3056_ = l_Std_Time_parseModifier___lam__31(v_presentation_boxed_3055_);
return v_res_3056_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1(void){
_start:
{
uint32_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = 120;
v___x_3059_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3060_ = lean_string_push(v___x_3059_, v___x_3058_);
return v___x_3060_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1);
v___x_3062_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3063_ = lean_string_append(v___x_3062_, v___x_3061_);
return v___x_3063_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3065_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2);
v___x_3066_ = lean_string_append(v___x_3065_, v___x_3064_);
return v___x_3066_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3);
v___x_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(lean_object* v_acc_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v_fst_3071_; lean_object* v_snd_3072_; lean_object* v_pos_3074_; lean_object* v_snd_3075_; lean_object* v_err_3076_; lean_object* v___x_3080_; uint8_t v_decide_3081_; 
v_fst_3071_ = lean_ctor_get(v_a_3070_, 0);
v_snd_3072_ = lean_ctor_get(v_a_3070_, 1);
lean_inc(v_snd_3072_);
v___x_3080_ = lean_string_utf8_byte_size(v_fst_3071_);
v_decide_3081_ = lean_nat_dec_eq(v_snd_3072_, v___x_3080_);
if (v_decide_3081_ == 0)
{
uint32_t v___x_3082_; uint32_t v_c_3083_; uint8_t v___x_3084_; 
v___x_3082_ = 120;
v_c_3083_ = lean_string_utf8_get_fast(v_fst_3071_, v_snd_3072_);
v___x_3084_ = lean_uint32_dec_eq(v_c_3083_, v___x_3082_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4);
lean_inc(v_snd_3072_);
v_pos_3074_ = v_a_3070_;
v_snd_3075_ = v_snd_3072_;
v_err_3076_ = v___x_3085_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3095_; 
lean_inc(v_fst_3071_);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_a_3070_);
if (v_isSharedCheck_3095_ == 0)
{
lean_object* v_unused_3096_; lean_object* v_unused_3097_; 
v_unused_3096_ = lean_ctor_get(v_a_3070_, 1);
lean_dec(v_unused_3096_);
v_unused_3097_ = lean_ctor_get(v_a_3070_, 0);
lean_dec(v_unused_3097_);
v___x_3087_ = v_a_3070_;
v_isShared_3088_ = v_isSharedCheck_3095_;
goto v_resetjp_3086_;
}
else
{
lean_dec(v_a_3070_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3095_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v_it_x27_3091_; 
v___x_3089_ = lean_string_utf8_next_fast(v_fst_3071_, v_snd_3072_);
lean_dec(v_snd_3072_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 1, v___x_3089_);
v_it_x27_3091_ = v___x_3087_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_fst_3071_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3089_);
v_it_x27_3091_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3092_; 
v___x_3092_ = lean_string_push(v_acc_3069_, v___x_3082_);
v_acc_3069_ = v___x_3092_;
v_a_3070_ = v_it_x27_3091_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3098_; 
v___x_3098_ = lean_box(0);
lean_inc(v_snd_3072_);
v_pos_3074_ = v_a_3070_;
v_snd_3075_ = v_snd_3072_;
v_err_3076_ = v___x_3098_;
goto v___jp_3073_;
}
v___jp_3073_:
{
uint8_t v_decide_3077_; 
v_decide_3077_ = lean_nat_dec_eq(v_snd_3072_, v_snd_3075_);
lean_dec(v_snd_3075_);
lean_dec(v_snd_3072_);
if (v_decide_3077_ == 0)
{
lean_object* v___x_3078_; 
lean_dec_ref(v_acc_3069_);
lean_inc(v_err_3076_);
v___x_3078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3078_, 0, v_pos_3074_);
lean_ctor_set(v___x_3078_, 1, v_err_3076_);
return v___x_3078_;
}
else
{
lean_object* v___x_3079_; 
v___x_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3079_, 0, v_pos_3074_);
lean_ctor_set(v___x_3079_, 1, v_acc_3069_);
return v___x_3079_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0(void){
_start:
{
uint32_t v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = 89;
v___x_3100_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3101_ = lean_string_push(v___x_3100_, v___x_3099_);
return v___x_3101_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0);
v___x_3103_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3104_ = lean_string_append(v___x_3103_, v___x_3102_);
return v___x_3104_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2(void){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3106_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1);
v___x_3107_ = lean_string_append(v___x_3106_, v___x_3105_);
return v___x_3107_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3(void){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2);
v___x_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(lean_object* v_acc_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v_fst_3112_; lean_object* v_snd_3113_; lean_object* v_pos_3115_; lean_object* v_snd_3116_; lean_object* v_err_3117_; lean_object* v___x_3121_; uint8_t v_decide_3122_; 
v_fst_3112_ = lean_ctor_get(v_a_3111_, 0);
v_snd_3113_ = lean_ctor_get(v_a_3111_, 1);
lean_inc(v_snd_3113_);
v___x_3121_ = lean_string_utf8_byte_size(v_fst_3112_);
v_decide_3122_ = lean_nat_dec_eq(v_snd_3113_, v___x_3121_);
if (v_decide_3122_ == 0)
{
uint32_t v___x_3123_; uint32_t v_c_3124_; uint8_t v___x_3125_; 
v___x_3123_ = 89;
v_c_3124_ = lean_string_utf8_get_fast(v_fst_3112_, v_snd_3113_);
v___x_3125_ = lean_uint32_dec_eq(v_c_3124_, v___x_3123_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3126_; 
v___x_3126_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3);
lean_inc(v_snd_3113_);
v_pos_3115_ = v_a_3111_;
v_snd_3116_ = v_snd_3113_;
v_err_3117_ = v___x_3126_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3136_; 
lean_inc(v_fst_3112_);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_a_3111_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; lean_object* v_unused_3138_; 
v_unused_3137_ = lean_ctor_get(v_a_3111_, 1);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v_a_3111_, 0);
lean_dec(v_unused_3138_);
v___x_3128_ = v_a_3111_;
v_isShared_3129_ = v_isSharedCheck_3136_;
goto v_resetjp_3127_;
}
else
{
lean_dec(v_a_3111_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3136_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v_it_x27_3132_; 
v___x_3130_ = lean_string_utf8_next_fast(v_fst_3112_, v_snd_3113_);
lean_dec(v_snd_3113_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 1, v___x_3130_);
v_it_x27_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_fst_3112_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_3130_);
v_it_x27_3132_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_string_push(v_acc_3110_, v___x_3123_);
v_acc_3110_ = v___x_3133_;
v_a_3111_ = v_it_x27_3132_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3139_; 
v___x_3139_ = lean_box(0);
lean_inc(v_snd_3113_);
v_pos_3115_ = v_a_3111_;
v_snd_3116_ = v_snd_3113_;
v_err_3117_ = v___x_3139_;
goto v___jp_3114_;
}
v___jp_3114_:
{
uint8_t v_decide_3118_; 
v_decide_3118_ = lean_nat_dec_eq(v_snd_3113_, v_snd_3116_);
lean_dec(v_snd_3116_);
lean_dec(v_snd_3113_);
if (v_decide_3118_ == 0)
{
lean_object* v___x_3119_; 
lean_dec_ref(v_acc_3110_);
lean_inc(v_err_3117_);
v___x_3119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_pos_3115_);
lean_ctor_set(v___x_3119_, 1, v_err_3117_);
return v___x_3119_;
}
else
{
lean_object* v___x_3120_; 
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v_pos_3115_);
lean_ctor_set(v___x_3120_, 1, v_acc_3110_);
return v___x_3120_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0(void){
_start:
{
uint32_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = 110;
v___x_3141_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3142_ = lean_string_push(v___x_3141_, v___x_3140_);
return v___x_3142_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0);
v___x_3144_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3145_ = lean_string_append(v___x_3144_, v___x_3143_);
return v___x_3145_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3147_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1);
v___x_3148_ = lean_string_append(v___x_3147_, v___x_3146_);
return v___x_3148_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2);
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(lean_object* v_acc_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v_fst_3153_; lean_object* v_snd_3154_; lean_object* v_pos_3156_; lean_object* v_snd_3157_; lean_object* v_err_3158_; lean_object* v___x_3162_; uint8_t v_decide_3163_; 
v_fst_3153_ = lean_ctor_get(v_a_3152_, 0);
v_snd_3154_ = lean_ctor_get(v_a_3152_, 1);
lean_inc(v_snd_3154_);
v___x_3162_ = lean_string_utf8_byte_size(v_fst_3153_);
v_decide_3163_ = lean_nat_dec_eq(v_snd_3154_, v___x_3162_);
if (v_decide_3163_ == 0)
{
uint32_t v___x_3164_; uint32_t v_c_3165_; uint8_t v___x_3166_; 
v___x_3164_ = 110;
v_c_3165_ = lean_string_utf8_get_fast(v_fst_3153_, v_snd_3154_);
v___x_3166_ = lean_uint32_dec_eq(v_c_3165_, v___x_3164_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; 
v___x_3167_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3);
lean_inc(v_snd_3154_);
v_pos_3156_ = v_a_3152_;
v_snd_3157_ = v_snd_3154_;
v_err_3158_ = v___x_3167_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3177_; 
lean_inc(v_fst_3153_);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_a_3152_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; lean_object* v_unused_3179_; 
v_unused_3178_ = lean_ctor_get(v_a_3152_, 1);
lean_dec(v_unused_3178_);
v_unused_3179_ = lean_ctor_get(v_a_3152_, 0);
lean_dec(v_unused_3179_);
v___x_3169_ = v_a_3152_;
v_isShared_3170_ = v_isSharedCheck_3177_;
goto v_resetjp_3168_;
}
else
{
lean_dec(v_a_3152_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3177_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v_it_x27_3173_; 
v___x_3171_ = lean_string_utf8_next_fast(v_fst_3153_, v_snd_3154_);
lean_dec(v_snd_3154_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 1, v___x_3171_);
v_it_x27_3173_ = v___x_3169_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_fst_3153_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v___x_3171_);
v_it_x27_3173_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_string_push(v_acc_3151_, v___x_3164_);
v_acc_3151_ = v___x_3174_;
v_a_3152_ = v_it_x27_3173_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_box(0);
lean_inc(v_snd_3154_);
v_pos_3156_ = v_a_3152_;
v_snd_3157_ = v_snd_3154_;
v_err_3158_ = v___x_3180_;
goto v___jp_3155_;
}
v___jp_3155_:
{
uint8_t v_decide_3159_; 
v_decide_3159_ = lean_nat_dec_eq(v_snd_3154_, v_snd_3157_);
lean_dec(v_snd_3157_);
lean_dec(v_snd_3154_);
if (v_decide_3159_ == 0)
{
lean_object* v___x_3160_; 
lean_dec_ref(v_acc_3151_);
lean_inc(v_err_3158_);
v___x_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3160_, 0, v_pos_3156_);
lean_ctor_set(v___x_3160_, 1, v_err_3158_);
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v_pos_3156_);
lean_ctor_set(v___x_3161_, 1, v_acc_3151_);
return v___x_3161_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0(void){
_start:
{
uint32_t v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = 71;
v___x_3182_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3183_ = lean_string_push(v___x_3182_, v___x_3181_);
return v___x_3183_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3184_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0);
v___x_3185_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3186_ = lean_string_append(v___x_3185_, v___x_3184_);
return v___x_3186_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3188_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1);
v___x_3189_ = lean_string_append(v___x_3188_, v___x_3187_);
return v___x_3189_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2);
v___x_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(lean_object* v_acc_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_fst_3194_; lean_object* v_snd_3195_; lean_object* v_pos_3197_; lean_object* v_snd_3198_; lean_object* v_err_3199_; lean_object* v___x_3203_; uint8_t v_decide_3204_; 
v_fst_3194_ = lean_ctor_get(v_a_3193_, 0);
v_snd_3195_ = lean_ctor_get(v_a_3193_, 1);
lean_inc(v_snd_3195_);
v___x_3203_ = lean_string_utf8_byte_size(v_fst_3194_);
v_decide_3204_ = lean_nat_dec_eq(v_snd_3195_, v___x_3203_);
if (v_decide_3204_ == 0)
{
uint32_t v___x_3205_; uint32_t v_c_3206_; uint8_t v___x_3207_; 
v___x_3205_ = 71;
v_c_3206_ = lean_string_utf8_get_fast(v_fst_3194_, v_snd_3195_);
v___x_3207_ = lean_uint32_dec_eq(v_c_3206_, v___x_3205_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; 
v___x_3208_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3);
lean_inc(v_snd_3195_);
v_pos_3197_ = v_a_3193_;
v_snd_3198_ = v_snd_3195_;
v_err_3199_ = v___x_3208_;
goto v___jp_3196_;
}
else
{
lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3218_; 
lean_inc(v_fst_3194_);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_a_3193_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; lean_object* v_unused_3220_; 
v_unused_3219_ = lean_ctor_get(v_a_3193_, 1);
lean_dec(v_unused_3219_);
v_unused_3220_ = lean_ctor_get(v_a_3193_, 0);
lean_dec(v_unused_3220_);
v___x_3210_ = v_a_3193_;
v_isShared_3211_ = v_isSharedCheck_3218_;
goto v_resetjp_3209_;
}
else
{
lean_dec(v_a_3193_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3218_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v_it_x27_3214_; 
v___x_3212_ = lean_string_utf8_next_fast(v_fst_3194_, v_snd_3195_);
lean_dec(v_snd_3195_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 1, v___x_3212_);
v_it_x27_3214_ = v___x_3210_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_fst_3194_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v___x_3212_);
v_it_x27_3214_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_string_push(v_acc_3192_, v___x_3205_);
v_acc_3192_ = v___x_3215_;
v_a_3193_ = v_it_x27_3214_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_box(0);
lean_inc(v_snd_3195_);
v_pos_3197_ = v_a_3193_;
v_snd_3198_ = v_snd_3195_;
v_err_3199_ = v___x_3221_;
goto v___jp_3196_;
}
v___jp_3196_:
{
uint8_t v_decide_3200_; 
v_decide_3200_ = lean_nat_dec_eq(v_snd_3195_, v_snd_3198_);
lean_dec(v_snd_3198_);
lean_dec(v_snd_3195_);
if (v_decide_3200_ == 0)
{
lean_object* v___x_3201_; 
lean_dec_ref(v_acc_3192_);
lean_inc(v_err_3199_);
v___x_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_pos_3197_);
lean_ctor_set(v___x_3201_, 1, v_err_3199_);
return v___x_3201_;
}
else
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_pos_3197_);
lean_ctor_set(v___x_3202_, 1, v_acc_3192_);
return v___x_3202_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0(void){
_start:
{
uint32_t v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3222_ = 86;
v___x_3223_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3224_ = lean_string_push(v___x_3223_, v___x_3222_);
return v___x_3224_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3225_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0);
v___x_3226_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3227_ = lean_string_append(v___x_3226_, v___x_3225_);
return v___x_3227_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3229_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1);
v___x_3230_ = lean_string_append(v___x_3229_, v___x_3228_);
return v___x_3230_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2);
v___x_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(lean_object* v_acc_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v_fst_3235_; lean_object* v_snd_3236_; lean_object* v_pos_3238_; lean_object* v_snd_3239_; lean_object* v_err_3240_; lean_object* v___x_3244_; uint8_t v_decide_3245_; 
v_fst_3235_ = lean_ctor_get(v_a_3234_, 0);
v_snd_3236_ = lean_ctor_get(v_a_3234_, 1);
lean_inc(v_snd_3236_);
v___x_3244_ = lean_string_utf8_byte_size(v_fst_3235_);
v_decide_3245_ = lean_nat_dec_eq(v_snd_3236_, v___x_3244_);
if (v_decide_3245_ == 0)
{
uint32_t v___x_3246_; uint32_t v_c_3247_; uint8_t v___x_3248_; 
v___x_3246_ = 86;
v_c_3247_ = lean_string_utf8_get_fast(v_fst_3235_, v_snd_3236_);
v___x_3248_ = lean_uint32_dec_eq(v_c_3247_, v___x_3246_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3);
lean_inc(v_snd_3236_);
v_pos_3238_ = v_a_3234_;
v_snd_3239_ = v_snd_3236_;
v_err_3240_ = v___x_3249_;
goto v___jp_3237_;
}
else
{
lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3259_; 
lean_inc(v_fst_3235_);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_a_3234_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; lean_object* v_unused_3261_; 
v_unused_3260_ = lean_ctor_get(v_a_3234_, 1);
lean_dec(v_unused_3260_);
v_unused_3261_ = lean_ctor_get(v_a_3234_, 0);
lean_dec(v_unused_3261_);
v___x_3251_ = v_a_3234_;
v_isShared_3252_ = v_isSharedCheck_3259_;
goto v_resetjp_3250_;
}
else
{
lean_dec(v_a_3234_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3259_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v_it_x27_3255_; 
v___x_3253_ = lean_string_utf8_next_fast(v_fst_3235_, v_snd_3236_);
lean_dec(v_snd_3236_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 1, v___x_3253_);
v_it_x27_3255_ = v___x_3251_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_fst_3235_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v___x_3253_);
v_it_x27_3255_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_string_push(v_acc_3233_, v___x_3246_);
v_acc_3233_ = v___x_3256_;
v_a_3234_ = v_it_x27_3255_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_box(0);
lean_inc(v_snd_3236_);
v_pos_3238_ = v_a_3234_;
v_snd_3239_ = v_snd_3236_;
v_err_3240_ = v___x_3262_;
goto v___jp_3237_;
}
v___jp_3237_:
{
uint8_t v_decide_3241_; 
v_decide_3241_ = lean_nat_dec_eq(v_snd_3236_, v_snd_3239_);
lean_dec(v_snd_3239_);
lean_dec(v_snd_3236_);
if (v_decide_3241_ == 0)
{
lean_object* v___x_3242_; 
lean_dec_ref(v_acc_3233_);
lean_inc(v_err_3240_);
v___x_3242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3242_, 0, v_pos_3238_);
lean_ctor_set(v___x_3242_, 1, v_err_3240_);
return v___x_3242_;
}
else
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_pos_3238_);
lean_ctor_set(v___x_3243_, 1, v_acc_3233_);
return v___x_3243_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0(void){
_start:
{
uint32_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = 83;
v___x_3264_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3265_ = lean_string_push(v___x_3264_, v___x_3263_);
return v___x_3265_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3266_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0);
v___x_3267_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3268_ = lean_string_append(v___x_3267_, v___x_3266_);
return v___x_3268_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3269_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3270_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1);
v___x_3271_ = lean_string_append(v___x_3270_, v___x_3269_);
return v___x_3271_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2);
v___x_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(lean_object* v_acc_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v_fst_3276_; lean_object* v_snd_3277_; lean_object* v_pos_3279_; lean_object* v_snd_3280_; lean_object* v_err_3281_; lean_object* v___x_3285_; uint8_t v_decide_3286_; 
v_fst_3276_ = lean_ctor_get(v_a_3275_, 0);
v_snd_3277_ = lean_ctor_get(v_a_3275_, 1);
lean_inc(v_snd_3277_);
v___x_3285_ = lean_string_utf8_byte_size(v_fst_3276_);
v_decide_3286_ = lean_nat_dec_eq(v_snd_3277_, v___x_3285_);
if (v_decide_3286_ == 0)
{
uint32_t v___x_3287_; uint32_t v_c_3288_; uint8_t v___x_3289_; 
v___x_3287_ = 83;
v_c_3288_ = lean_string_utf8_get_fast(v_fst_3276_, v_snd_3277_);
v___x_3289_ = lean_uint32_dec_eq(v_c_3288_, v___x_3287_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; 
v___x_3290_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3);
lean_inc(v_snd_3277_);
v_pos_3279_ = v_a_3275_;
v_snd_3280_ = v_snd_3277_;
v_err_3281_ = v___x_3290_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3300_; 
lean_inc(v_fst_3276_);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_a_3275_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; lean_object* v_unused_3302_; 
v_unused_3301_ = lean_ctor_get(v_a_3275_, 1);
lean_dec(v_unused_3301_);
v_unused_3302_ = lean_ctor_get(v_a_3275_, 0);
lean_dec(v_unused_3302_);
v___x_3292_ = v_a_3275_;
v_isShared_3293_ = v_isSharedCheck_3300_;
goto v_resetjp_3291_;
}
else
{
lean_dec(v_a_3275_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3300_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; lean_object* v_it_x27_3296_; 
v___x_3294_ = lean_string_utf8_next_fast(v_fst_3276_, v_snd_3277_);
lean_dec(v_snd_3277_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 1, v___x_3294_);
v_it_x27_3296_ = v___x_3292_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_fst_3276_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v___x_3294_);
v_it_x27_3296_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_string_push(v_acc_3274_, v___x_3287_);
v_acc_3274_ = v___x_3297_;
v_a_3275_ = v_it_x27_3296_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3303_; 
v___x_3303_ = lean_box(0);
lean_inc(v_snd_3277_);
v_pos_3279_ = v_a_3275_;
v_snd_3280_ = v_snd_3277_;
v_err_3281_ = v___x_3303_;
goto v___jp_3278_;
}
v___jp_3278_:
{
uint8_t v_decide_3282_; 
v_decide_3282_ = lean_nat_dec_eq(v_snd_3277_, v_snd_3280_);
lean_dec(v_snd_3280_);
lean_dec(v_snd_3277_);
if (v_decide_3282_ == 0)
{
lean_object* v___x_3283_; 
lean_dec_ref(v_acc_3274_);
lean_inc(v_err_3281_);
v___x_3283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3283_, 0, v_pos_3279_);
lean_ctor_set(v___x_3283_, 1, v_err_3281_);
return v___x_3283_;
}
else
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v_pos_3279_);
lean_ctor_set(v___x_3284_, 1, v_acc_3274_);
return v___x_3284_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0(void){
_start:
{
uint32_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = 104;
v___x_3305_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3306_ = lean_string_push(v___x_3305_, v___x_3304_);
return v___x_3306_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0);
v___x_3308_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3309_ = lean_string_append(v___x_3308_, v___x_3307_);
return v___x_3309_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3311_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1);
v___x_3312_ = lean_string_append(v___x_3311_, v___x_3310_);
return v___x_3312_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2);
v___x_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(lean_object* v_acc_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v_fst_3317_; lean_object* v_snd_3318_; lean_object* v_pos_3320_; lean_object* v_snd_3321_; lean_object* v_err_3322_; lean_object* v___x_3326_; uint8_t v_decide_3327_; 
v_fst_3317_ = lean_ctor_get(v_a_3316_, 0);
v_snd_3318_ = lean_ctor_get(v_a_3316_, 1);
lean_inc(v_snd_3318_);
v___x_3326_ = lean_string_utf8_byte_size(v_fst_3317_);
v_decide_3327_ = lean_nat_dec_eq(v_snd_3318_, v___x_3326_);
if (v_decide_3327_ == 0)
{
uint32_t v___x_3328_; uint32_t v_c_3329_; uint8_t v___x_3330_; 
v___x_3328_ = 104;
v_c_3329_ = lean_string_utf8_get_fast(v_fst_3317_, v_snd_3318_);
v___x_3330_ = lean_uint32_dec_eq(v_c_3329_, v___x_3328_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3);
lean_inc(v_snd_3318_);
v_pos_3320_ = v_a_3316_;
v_snd_3321_ = v_snd_3318_;
v_err_3322_ = v___x_3331_;
goto v___jp_3319_;
}
else
{
lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3341_; 
lean_inc(v_fst_3317_);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_a_3316_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; lean_object* v_unused_3343_; 
v_unused_3342_ = lean_ctor_get(v_a_3316_, 1);
lean_dec(v_unused_3342_);
v_unused_3343_ = lean_ctor_get(v_a_3316_, 0);
lean_dec(v_unused_3343_);
v___x_3333_ = v_a_3316_;
v_isShared_3334_ = v_isSharedCheck_3341_;
goto v_resetjp_3332_;
}
else
{
lean_dec(v_a_3316_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3341_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; lean_object* v_it_x27_3337_; 
v___x_3335_ = lean_string_utf8_next_fast(v_fst_3317_, v_snd_3318_);
lean_dec(v_snd_3318_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 1, v___x_3335_);
v_it_x27_3337_ = v___x_3333_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_fst_3317_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___x_3335_);
v_it_x27_3337_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3338_; 
v___x_3338_ = lean_string_push(v_acc_3315_, v___x_3328_);
v_acc_3315_ = v___x_3338_;
v_a_3316_ = v_it_x27_3337_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_box(0);
lean_inc(v_snd_3318_);
v_pos_3320_ = v_a_3316_;
v_snd_3321_ = v_snd_3318_;
v_err_3322_ = v___x_3344_;
goto v___jp_3319_;
}
v___jp_3319_:
{
uint8_t v_decide_3323_; 
v_decide_3323_ = lean_nat_dec_eq(v_snd_3318_, v_snd_3321_);
lean_dec(v_snd_3321_);
lean_dec(v_snd_3318_);
if (v_decide_3323_ == 0)
{
lean_object* v___x_3324_; 
lean_dec_ref(v_acc_3315_);
lean_inc(v_err_3322_);
v___x_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3324_, 0, v_pos_3320_);
lean_ctor_set(v___x_3324_, 1, v_err_3322_);
return v___x_3324_;
}
else
{
lean_object* v___x_3325_; 
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v_pos_3320_);
lean_ctor_set(v___x_3325_, 1, v_acc_3315_);
return v___x_3325_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0(void){
_start:
{
uint32_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = 81;
v___x_3346_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3347_ = lean_string_push(v___x_3346_, v___x_3345_);
return v___x_3347_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0);
v___x_3349_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3350_ = lean_string_append(v___x_3349_, v___x_3348_);
return v___x_3350_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3351_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3352_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1);
v___x_3353_ = lean_string_append(v___x_3352_, v___x_3351_);
return v___x_3353_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3(void){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2);
v___x_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(lean_object* v_acc_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v_fst_3358_; lean_object* v_snd_3359_; lean_object* v_pos_3361_; lean_object* v_snd_3362_; lean_object* v_err_3363_; lean_object* v___x_3367_; uint8_t v_decide_3368_; 
v_fst_3358_ = lean_ctor_get(v_a_3357_, 0);
v_snd_3359_ = lean_ctor_get(v_a_3357_, 1);
lean_inc(v_snd_3359_);
v___x_3367_ = lean_string_utf8_byte_size(v_fst_3358_);
v_decide_3368_ = lean_nat_dec_eq(v_snd_3359_, v___x_3367_);
if (v_decide_3368_ == 0)
{
uint32_t v___x_3369_; uint32_t v_c_3370_; uint8_t v___x_3371_; 
v___x_3369_ = 81;
v_c_3370_ = lean_string_utf8_get_fast(v_fst_3358_, v_snd_3359_);
v___x_3371_ = lean_uint32_dec_eq(v_c_3370_, v___x_3369_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; 
v___x_3372_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3);
lean_inc(v_snd_3359_);
v_pos_3361_ = v_a_3357_;
v_snd_3362_ = v_snd_3359_;
v_err_3363_ = v___x_3372_;
goto v___jp_3360_;
}
else
{
lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3382_; 
lean_inc(v_fst_3358_);
v_isSharedCheck_3382_ = !lean_is_exclusive(v_a_3357_);
if (v_isSharedCheck_3382_ == 0)
{
lean_object* v_unused_3383_; lean_object* v_unused_3384_; 
v_unused_3383_ = lean_ctor_get(v_a_3357_, 1);
lean_dec(v_unused_3383_);
v_unused_3384_ = lean_ctor_get(v_a_3357_, 0);
lean_dec(v_unused_3384_);
v___x_3374_ = v_a_3357_;
v_isShared_3375_ = v_isSharedCheck_3382_;
goto v_resetjp_3373_;
}
else
{
lean_dec(v_a_3357_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3382_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v_it_x27_3378_; 
v___x_3376_ = lean_string_utf8_next_fast(v_fst_3358_, v_snd_3359_);
lean_dec(v_snd_3359_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 1, v___x_3376_);
v_it_x27_3378_ = v___x_3374_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_fst_3358_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v___x_3376_);
v_it_x27_3378_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_string_push(v_acc_3356_, v___x_3369_);
v_acc_3356_ = v___x_3379_;
v_a_3357_ = v_it_x27_3378_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3385_; 
v___x_3385_ = lean_box(0);
lean_inc(v_snd_3359_);
v_pos_3361_ = v_a_3357_;
v_snd_3362_ = v_snd_3359_;
v_err_3363_ = v___x_3385_;
goto v___jp_3360_;
}
v___jp_3360_:
{
uint8_t v_decide_3364_; 
v_decide_3364_ = lean_nat_dec_eq(v_snd_3359_, v_snd_3362_);
lean_dec(v_snd_3362_);
lean_dec(v_snd_3359_);
if (v_decide_3364_ == 0)
{
lean_object* v___x_3365_; 
lean_dec_ref(v_acc_3356_);
lean_inc(v_err_3363_);
v___x_3365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3365_, 0, v_pos_3361_);
lean_ctor_set(v___x_3365_, 1, v_err_3363_);
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_pos_3361_);
lean_ctor_set(v___x_3366_, 1, v_acc_3356_);
return v___x_3366_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0(void){
_start:
{
uint32_t v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = 68;
v___x_3387_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3388_ = lean_string_push(v___x_3387_, v___x_3386_);
return v___x_3388_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0);
v___x_3390_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3391_ = lean_string_append(v___x_3390_, v___x_3389_);
return v___x_3391_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3392_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3393_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1);
v___x_3394_ = lean_string_append(v___x_3393_, v___x_3392_);
return v___x_3394_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2);
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(lean_object* v_acc_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v_fst_3399_; lean_object* v_snd_3400_; lean_object* v_pos_3402_; lean_object* v_snd_3403_; lean_object* v_err_3404_; lean_object* v___x_3408_; uint8_t v_decide_3409_; 
v_fst_3399_ = lean_ctor_get(v_a_3398_, 0);
v_snd_3400_ = lean_ctor_get(v_a_3398_, 1);
lean_inc(v_snd_3400_);
v___x_3408_ = lean_string_utf8_byte_size(v_fst_3399_);
v_decide_3409_ = lean_nat_dec_eq(v_snd_3400_, v___x_3408_);
if (v_decide_3409_ == 0)
{
uint32_t v___x_3410_; uint32_t v_c_3411_; uint8_t v___x_3412_; 
v___x_3410_ = 68;
v_c_3411_ = lean_string_utf8_get_fast(v_fst_3399_, v_snd_3400_);
v___x_3412_ = lean_uint32_dec_eq(v_c_3411_, v___x_3410_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3);
lean_inc(v_snd_3400_);
v_pos_3402_ = v_a_3398_;
v_snd_3403_ = v_snd_3400_;
v_err_3404_ = v___x_3413_;
goto v___jp_3401_;
}
else
{
lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3423_; 
lean_inc(v_fst_3399_);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_a_3398_);
if (v_isSharedCheck_3423_ == 0)
{
lean_object* v_unused_3424_; lean_object* v_unused_3425_; 
v_unused_3424_ = lean_ctor_get(v_a_3398_, 1);
lean_dec(v_unused_3424_);
v_unused_3425_ = lean_ctor_get(v_a_3398_, 0);
lean_dec(v_unused_3425_);
v___x_3415_ = v_a_3398_;
v_isShared_3416_ = v_isSharedCheck_3423_;
goto v_resetjp_3414_;
}
else
{
lean_dec(v_a_3398_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3423_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; lean_object* v_it_x27_3419_; 
v___x_3417_ = lean_string_utf8_next_fast(v_fst_3399_, v_snd_3400_);
lean_dec(v_snd_3400_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v___x_3417_);
v_it_x27_3419_ = v___x_3415_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_fst_3399_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v___x_3417_);
v_it_x27_3419_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_string_push(v_acc_3397_, v___x_3410_);
v_acc_3397_ = v___x_3420_;
v_a_3398_ = v_it_x27_3419_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_box(0);
lean_inc(v_snd_3400_);
v_pos_3402_ = v_a_3398_;
v_snd_3403_ = v_snd_3400_;
v_err_3404_ = v___x_3426_;
goto v___jp_3401_;
}
v___jp_3401_:
{
uint8_t v_decide_3405_; 
v_decide_3405_ = lean_nat_dec_eq(v_snd_3400_, v_snd_3403_);
lean_dec(v_snd_3403_);
lean_dec(v_snd_3400_);
if (v_decide_3405_ == 0)
{
lean_object* v___x_3406_; 
lean_dec_ref(v_acc_3397_);
lean_inc(v_err_3404_);
v___x_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3406_, 0, v_pos_3402_);
lean_ctor_set(v___x_3406_, 1, v_err_3404_);
return v___x_3406_;
}
else
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3407_, 0, v_pos_3402_);
lean_ctor_set(v___x_3407_, 1, v_acc_3397_);
return v___x_3407_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0(void){
_start:
{
uint32_t v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = 88;
v___x_3428_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3429_ = lean_string_push(v___x_3428_, v___x_3427_);
return v___x_3429_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3430_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0);
v___x_3431_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3432_ = lean_string_append(v___x_3431_, v___x_3430_);
return v___x_3432_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3434_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1);
v___x_3435_ = lean_string_append(v___x_3434_, v___x_3433_);
return v___x_3435_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2);
v___x_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(lean_object* v_acc_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v_fst_3440_; lean_object* v_snd_3441_; lean_object* v_pos_3443_; lean_object* v_snd_3444_; lean_object* v_err_3445_; lean_object* v___x_3449_; uint8_t v_decide_3450_; 
v_fst_3440_ = lean_ctor_get(v_a_3439_, 0);
v_snd_3441_ = lean_ctor_get(v_a_3439_, 1);
lean_inc(v_snd_3441_);
v___x_3449_ = lean_string_utf8_byte_size(v_fst_3440_);
v_decide_3450_ = lean_nat_dec_eq(v_snd_3441_, v___x_3449_);
if (v_decide_3450_ == 0)
{
uint32_t v___x_3451_; uint32_t v_c_3452_; uint8_t v___x_3453_; 
v___x_3451_ = 88;
v_c_3452_ = lean_string_utf8_get_fast(v_fst_3440_, v_snd_3441_);
v___x_3453_ = lean_uint32_dec_eq(v_c_3452_, v___x_3451_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3);
lean_inc(v_snd_3441_);
v_pos_3443_ = v_a_3439_;
v_snd_3444_ = v_snd_3441_;
v_err_3445_ = v___x_3454_;
goto v___jp_3442_;
}
else
{
lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3464_; 
lean_inc(v_fst_3440_);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_a_3439_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; lean_object* v_unused_3466_; 
v_unused_3465_ = lean_ctor_get(v_a_3439_, 1);
lean_dec(v_unused_3465_);
v_unused_3466_ = lean_ctor_get(v_a_3439_, 0);
lean_dec(v_unused_3466_);
v___x_3456_ = v_a_3439_;
v_isShared_3457_ = v_isSharedCheck_3464_;
goto v_resetjp_3455_;
}
else
{
lean_dec(v_a_3439_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3464_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v_it_x27_3460_; 
v___x_3458_ = lean_string_utf8_next_fast(v_fst_3440_, v_snd_3441_);
lean_dec(v_snd_3441_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 1, v___x_3458_);
v_it_x27_3460_ = v___x_3456_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_fst_3440_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v___x_3458_);
v_it_x27_3460_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3461_; 
v___x_3461_ = lean_string_push(v_acc_3438_, v___x_3451_);
v_acc_3438_ = v___x_3461_;
v_a_3439_ = v_it_x27_3460_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_box(0);
lean_inc(v_snd_3441_);
v_pos_3443_ = v_a_3439_;
v_snd_3444_ = v_snd_3441_;
v_err_3445_ = v___x_3467_;
goto v___jp_3442_;
}
v___jp_3442_:
{
uint8_t v_decide_3446_; 
v_decide_3446_ = lean_nat_dec_eq(v_snd_3441_, v_snd_3444_);
lean_dec(v_snd_3444_);
lean_dec(v_snd_3441_);
if (v_decide_3446_ == 0)
{
lean_object* v___x_3447_; 
lean_dec_ref(v_acc_3438_);
lean_inc(v_err_3445_);
v___x_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3447_, 0, v_pos_3443_);
lean_ctor_set(v___x_3447_, 1, v_err_3445_);
return v___x_3447_;
}
else
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3448_, 0, v_pos_3443_);
lean_ctor_set(v___x_3448_, 1, v_acc_3438_);
return v___x_3448_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0(void){
_start:
{
uint32_t v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = 122;
v___x_3469_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3470_ = lean_string_push(v___x_3469_, v___x_3468_);
return v___x_3470_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0);
v___x_3472_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3473_ = lean_string_append(v___x_3472_, v___x_3471_);
return v___x_3473_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3474_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3475_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1);
v___x_3476_ = lean_string_append(v___x_3475_, v___x_3474_);
return v___x_3476_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2);
v___x_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(lean_object* v_acc_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v_fst_3481_; lean_object* v_snd_3482_; lean_object* v_pos_3484_; lean_object* v_snd_3485_; lean_object* v_err_3486_; lean_object* v___x_3490_; uint8_t v_decide_3491_; 
v_fst_3481_ = lean_ctor_get(v_a_3480_, 0);
v_snd_3482_ = lean_ctor_get(v_a_3480_, 1);
lean_inc(v_snd_3482_);
v___x_3490_ = lean_string_utf8_byte_size(v_fst_3481_);
v_decide_3491_ = lean_nat_dec_eq(v_snd_3482_, v___x_3490_);
if (v_decide_3491_ == 0)
{
uint32_t v___x_3492_; uint32_t v_c_3493_; uint8_t v___x_3494_; 
v___x_3492_ = 122;
v_c_3493_ = lean_string_utf8_get_fast(v_fst_3481_, v_snd_3482_);
v___x_3494_ = lean_uint32_dec_eq(v_c_3493_, v___x_3492_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3);
lean_inc(v_snd_3482_);
v_pos_3484_ = v_a_3480_;
v_snd_3485_ = v_snd_3482_;
v_err_3486_ = v___x_3495_;
goto v___jp_3483_;
}
else
{
lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3505_; 
lean_inc(v_fst_3481_);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_a_3480_);
if (v_isSharedCheck_3505_ == 0)
{
lean_object* v_unused_3506_; lean_object* v_unused_3507_; 
v_unused_3506_ = lean_ctor_get(v_a_3480_, 1);
lean_dec(v_unused_3506_);
v_unused_3507_ = lean_ctor_get(v_a_3480_, 0);
lean_dec(v_unused_3507_);
v___x_3497_ = v_a_3480_;
v_isShared_3498_ = v_isSharedCheck_3505_;
goto v_resetjp_3496_;
}
else
{
lean_dec(v_a_3480_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3505_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3499_; lean_object* v_it_x27_3501_; 
v___x_3499_ = lean_string_utf8_next_fast(v_fst_3481_, v_snd_3482_);
lean_dec(v_snd_3482_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 1, v___x_3499_);
v_it_x27_3501_ = v___x_3497_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_fst_3481_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3499_);
v_it_x27_3501_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3502_; 
v___x_3502_ = lean_string_push(v_acc_3479_, v___x_3492_);
v_acc_3479_ = v___x_3502_;
v_a_3480_ = v_it_x27_3501_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_box(0);
lean_inc(v_snd_3482_);
v_pos_3484_ = v_a_3480_;
v_snd_3485_ = v_snd_3482_;
v_err_3486_ = v___x_3508_;
goto v___jp_3483_;
}
v___jp_3483_:
{
uint8_t v_decide_3487_; 
v_decide_3487_ = lean_nat_dec_eq(v_snd_3482_, v_snd_3485_);
lean_dec(v_snd_3485_);
lean_dec(v_snd_3482_);
if (v_decide_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_dec_ref(v_acc_3479_);
lean_inc(v_err_3486_);
v___x_3488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3488_, 0, v_pos_3484_);
lean_ctor_set(v___x_3488_, 1, v_err_3486_);
return v___x_3488_;
}
else
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3489_, 0, v_pos_3484_);
lean_ctor_set(v___x_3489_, 1, v_acc_3479_);
return v___x_3489_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0(void){
_start:
{
uint32_t v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = 115;
v___x_3510_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3511_ = lean_string_push(v___x_3510_, v___x_3509_);
return v___x_3511_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0);
v___x_3513_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3514_ = lean_string_append(v___x_3513_, v___x_3512_);
return v___x_3514_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3516_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1);
v___x_3517_ = lean_string_append(v___x_3516_, v___x_3515_);
return v___x_3517_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2);
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(lean_object* v_acc_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_fst_3522_; lean_object* v_snd_3523_; lean_object* v_pos_3525_; lean_object* v_snd_3526_; lean_object* v_err_3527_; lean_object* v___x_3531_; uint8_t v_decide_3532_; 
v_fst_3522_ = lean_ctor_get(v_a_3521_, 0);
v_snd_3523_ = lean_ctor_get(v_a_3521_, 1);
lean_inc(v_snd_3523_);
v___x_3531_ = lean_string_utf8_byte_size(v_fst_3522_);
v_decide_3532_ = lean_nat_dec_eq(v_snd_3523_, v___x_3531_);
if (v_decide_3532_ == 0)
{
uint32_t v___x_3533_; uint32_t v_c_3534_; uint8_t v___x_3535_; 
v___x_3533_ = 115;
v_c_3534_ = lean_string_utf8_get_fast(v_fst_3522_, v_snd_3523_);
v___x_3535_ = lean_uint32_dec_eq(v_c_3534_, v___x_3533_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; 
v___x_3536_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3);
lean_inc(v_snd_3523_);
v_pos_3525_ = v_a_3521_;
v_snd_3526_ = v_snd_3523_;
v_err_3527_ = v___x_3536_;
goto v___jp_3524_;
}
else
{
lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3546_; 
lean_inc(v_fst_3522_);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_a_3521_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; lean_object* v_unused_3548_; 
v_unused_3547_ = lean_ctor_get(v_a_3521_, 1);
lean_dec(v_unused_3547_);
v_unused_3548_ = lean_ctor_get(v_a_3521_, 0);
lean_dec(v_unused_3548_);
v___x_3538_ = v_a_3521_;
v_isShared_3539_ = v_isSharedCheck_3546_;
goto v_resetjp_3537_;
}
else
{
lean_dec(v_a_3521_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3546_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v_it_x27_3542_; 
v___x_3540_ = lean_string_utf8_next_fast(v_fst_3522_, v_snd_3523_);
lean_dec(v_snd_3523_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 1, v___x_3540_);
v_it_x27_3542_ = v___x_3538_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_fst_3522_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v___x_3540_);
v_it_x27_3542_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3543_; 
v___x_3543_ = lean_string_push(v_acc_3520_, v___x_3533_);
v_acc_3520_ = v___x_3543_;
v_a_3521_ = v_it_x27_3542_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3549_; 
v___x_3549_ = lean_box(0);
lean_inc(v_snd_3523_);
v_pos_3525_ = v_a_3521_;
v_snd_3526_ = v_snd_3523_;
v_err_3527_ = v___x_3549_;
goto v___jp_3524_;
}
v___jp_3524_:
{
uint8_t v_decide_3528_; 
v_decide_3528_ = lean_nat_dec_eq(v_snd_3523_, v_snd_3526_);
lean_dec(v_snd_3526_);
lean_dec(v_snd_3523_);
if (v_decide_3528_ == 0)
{
lean_object* v___x_3529_; 
lean_dec_ref(v_acc_3520_);
lean_inc(v_err_3527_);
v___x_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_pos_3525_);
lean_ctor_set(v___x_3529_, 1, v_err_3527_);
return v___x_3529_;
}
else
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v_pos_3525_);
lean_ctor_set(v___x_3530_, 1, v_acc_3520_);
return v___x_3530_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0(void){
_start:
{
uint32_t v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = 75;
v___x_3551_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3552_ = lean_string_push(v___x_3551_, v___x_3550_);
return v___x_3552_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0);
v___x_3554_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3555_ = lean_string_append(v___x_3554_, v___x_3553_);
return v___x_3555_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3557_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1);
v___x_3558_ = lean_string_append(v___x_3557_, v___x_3556_);
return v___x_3558_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2);
v___x_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(lean_object* v_acc_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_fst_3563_; lean_object* v_snd_3564_; lean_object* v_pos_3566_; lean_object* v_snd_3567_; lean_object* v_err_3568_; lean_object* v___x_3572_; uint8_t v_decide_3573_; 
v_fst_3563_ = lean_ctor_get(v_a_3562_, 0);
v_snd_3564_ = lean_ctor_get(v_a_3562_, 1);
lean_inc(v_snd_3564_);
v___x_3572_ = lean_string_utf8_byte_size(v_fst_3563_);
v_decide_3573_ = lean_nat_dec_eq(v_snd_3564_, v___x_3572_);
if (v_decide_3573_ == 0)
{
uint32_t v___x_3574_; uint32_t v_c_3575_; uint8_t v___x_3576_; 
v___x_3574_ = 75;
v_c_3575_ = lean_string_utf8_get_fast(v_fst_3563_, v_snd_3564_);
v___x_3576_ = lean_uint32_dec_eq(v_c_3575_, v___x_3574_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; 
v___x_3577_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3);
lean_inc(v_snd_3564_);
v_pos_3566_ = v_a_3562_;
v_snd_3567_ = v_snd_3564_;
v_err_3568_ = v___x_3577_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3587_; 
lean_inc(v_fst_3563_);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_a_3562_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; lean_object* v_unused_3589_; 
v_unused_3588_ = lean_ctor_get(v_a_3562_, 1);
lean_dec(v_unused_3588_);
v_unused_3589_ = lean_ctor_get(v_a_3562_, 0);
lean_dec(v_unused_3589_);
v___x_3579_ = v_a_3562_;
v_isShared_3580_ = v_isSharedCheck_3587_;
goto v_resetjp_3578_;
}
else
{
lean_dec(v_a_3562_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3587_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; lean_object* v_it_x27_3583_; 
v___x_3581_ = lean_string_utf8_next_fast(v_fst_3563_, v_snd_3564_);
lean_dec(v_snd_3564_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 1, v___x_3581_);
v_it_x27_3583_ = v___x_3579_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_fst_3563_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v___x_3581_);
v_it_x27_3583_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3584_; 
v___x_3584_ = lean_string_push(v_acc_3561_, v___x_3574_);
v_acc_3561_ = v___x_3584_;
v_a_3562_ = v_it_x27_3583_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_box(0);
lean_inc(v_snd_3564_);
v_pos_3566_ = v_a_3562_;
v_snd_3567_ = v_snd_3564_;
v_err_3568_ = v___x_3590_;
goto v___jp_3565_;
}
v___jp_3565_:
{
uint8_t v_decide_3569_; 
v_decide_3569_ = lean_nat_dec_eq(v_snd_3564_, v_snd_3567_);
lean_dec(v_snd_3567_);
lean_dec(v_snd_3564_);
if (v_decide_3569_ == 0)
{
lean_object* v___x_3570_; 
lean_dec_ref(v_acc_3561_);
lean_inc(v_err_3568_);
v___x_3570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_pos_3566_);
lean_ctor_set(v___x_3570_, 1, v_err_3568_);
return v___x_3570_;
}
else
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v_pos_3566_);
lean_ctor_set(v___x_3571_, 1, v_acc_3561_);
return v___x_3571_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0(void){
_start:
{
uint32_t v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = 101;
v___x_3592_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3593_ = lean_string_push(v___x_3592_, v___x_3591_);
return v___x_3593_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0);
v___x_3595_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3596_ = lean_string_append(v___x_3595_, v___x_3594_);
return v___x_3596_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2(void){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3598_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1);
v___x_3599_ = lean_string_append(v___x_3598_, v___x_3597_);
return v___x_3599_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3(void){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2);
v___x_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(lean_object* v_acc_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_fst_3604_; lean_object* v_snd_3605_; lean_object* v_pos_3607_; lean_object* v_snd_3608_; lean_object* v_err_3609_; lean_object* v___x_3613_; uint8_t v_decide_3614_; 
v_fst_3604_ = lean_ctor_get(v_a_3603_, 0);
v_snd_3605_ = lean_ctor_get(v_a_3603_, 1);
lean_inc(v_snd_3605_);
v___x_3613_ = lean_string_utf8_byte_size(v_fst_3604_);
v_decide_3614_ = lean_nat_dec_eq(v_snd_3605_, v___x_3613_);
if (v_decide_3614_ == 0)
{
uint32_t v___x_3615_; uint32_t v_c_3616_; uint8_t v___x_3617_; 
v___x_3615_ = 101;
v_c_3616_ = lean_string_utf8_get_fast(v_fst_3604_, v_snd_3605_);
v___x_3617_ = lean_uint32_dec_eq(v_c_3616_, v___x_3615_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; 
v___x_3618_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3);
lean_inc(v_snd_3605_);
v_pos_3607_ = v_a_3603_;
v_snd_3608_ = v_snd_3605_;
v_err_3609_ = v___x_3618_;
goto v___jp_3606_;
}
else
{
lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3628_; 
lean_inc(v_fst_3604_);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_a_3603_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; lean_object* v_unused_3630_; 
v_unused_3629_ = lean_ctor_get(v_a_3603_, 1);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_a_3603_, 0);
lean_dec(v_unused_3630_);
v___x_3620_ = v_a_3603_;
v_isShared_3621_ = v_isSharedCheck_3628_;
goto v_resetjp_3619_;
}
else
{
lean_dec(v_a_3603_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3628_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; lean_object* v_it_x27_3624_; 
v___x_3622_ = lean_string_utf8_next_fast(v_fst_3604_, v_snd_3605_);
lean_dec(v_snd_3605_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 1, v___x_3622_);
v_it_x27_3624_ = v___x_3620_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_fst_3604_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v___x_3622_);
v_it_x27_3624_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3625_; 
v___x_3625_ = lean_string_push(v_acc_3602_, v___x_3615_);
v_acc_3602_ = v___x_3625_;
v_a_3603_ = v_it_x27_3624_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3631_; 
v___x_3631_ = lean_box(0);
lean_inc(v_snd_3605_);
v_pos_3607_ = v_a_3603_;
v_snd_3608_ = v_snd_3605_;
v_err_3609_ = v___x_3631_;
goto v___jp_3606_;
}
v___jp_3606_:
{
uint8_t v_decide_3610_; 
v_decide_3610_ = lean_nat_dec_eq(v_snd_3605_, v_snd_3608_);
lean_dec(v_snd_3608_);
lean_dec(v_snd_3605_);
if (v_decide_3610_ == 0)
{
lean_object* v___x_3611_; 
lean_dec_ref(v_acc_3602_);
lean_inc(v_err_3609_);
v___x_3611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3611_, 0, v_pos_3607_);
lean_ctor_set(v___x_3611_, 1, v_err_3609_);
return v___x_3611_;
}
else
{
lean_object* v___x_3612_; 
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v_pos_3607_);
lean_ctor_set(v___x_3612_, 1, v_acc_3602_);
return v___x_3612_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0(void){
_start:
{
uint32_t v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3632_ = 77;
v___x_3633_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3634_ = lean_string_push(v___x_3633_, v___x_3632_);
return v___x_3634_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3635_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0);
v___x_3636_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3637_ = lean_string_append(v___x_3636_, v___x_3635_);
return v___x_3637_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3638_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3639_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1);
v___x_3640_ = lean_string_append(v___x_3639_, v___x_3638_);
return v___x_3640_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2);
v___x_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(lean_object* v_acc_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v_fst_3645_; lean_object* v_snd_3646_; lean_object* v_pos_3648_; lean_object* v_snd_3649_; lean_object* v_err_3650_; lean_object* v___x_3654_; uint8_t v_decide_3655_; 
v_fst_3645_ = lean_ctor_get(v_a_3644_, 0);
v_snd_3646_ = lean_ctor_get(v_a_3644_, 1);
lean_inc(v_snd_3646_);
v___x_3654_ = lean_string_utf8_byte_size(v_fst_3645_);
v_decide_3655_ = lean_nat_dec_eq(v_snd_3646_, v___x_3654_);
if (v_decide_3655_ == 0)
{
uint32_t v___x_3656_; uint32_t v_c_3657_; uint8_t v___x_3658_; 
v___x_3656_ = 77;
v_c_3657_ = lean_string_utf8_get_fast(v_fst_3645_, v_snd_3646_);
v___x_3658_ = lean_uint32_dec_eq(v_c_3657_, v___x_3656_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3);
lean_inc(v_snd_3646_);
v_pos_3648_ = v_a_3644_;
v_snd_3649_ = v_snd_3646_;
v_err_3650_ = v___x_3659_;
goto v___jp_3647_;
}
else
{
lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3669_; 
lean_inc(v_fst_3645_);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_a_3644_);
if (v_isSharedCheck_3669_ == 0)
{
lean_object* v_unused_3670_; lean_object* v_unused_3671_; 
v_unused_3670_ = lean_ctor_get(v_a_3644_, 1);
lean_dec(v_unused_3670_);
v_unused_3671_ = lean_ctor_get(v_a_3644_, 0);
lean_dec(v_unused_3671_);
v___x_3661_ = v_a_3644_;
v_isShared_3662_ = v_isSharedCheck_3669_;
goto v_resetjp_3660_;
}
else
{
lean_dec(v_a_3644_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3669_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; lean_object* v_it_x27_3665_; 
v___x_3663_ = lean_string_utf8_next_fast(v_fst_3645_, v_snd_3646_);
lean_dec(v_snd_3646_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 1, v___x_3663_);
v_it_x27_3665_ = v___x_3661_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_fst_3645_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v___x_3663_);
v_it_x27_3665_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; 
v___x_3666_ = lean_string_push(v_acc_3643_, v___x_3656_);
v_acc_3643_ = v___x_3666_;
v_a_3644_ = v_it_x27_3665_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3672_; 
v___x_3672_ = lean_box(0);
lean_inc(v_snd_3646_);
v_pos_3648_ = v_a_3644_;
v_snd_3649_ = v_snd_3646_;
v_err_3650_ = v___x_3672_;
goto v___jp_3647_;
}
v___jp_3647_:
{
uint8_t v_decide_3651_; 
v_decide_3651_ = lean_nat_dec_eq(v_snd_3646_, v_snd_3649_);
lean_dec(v_snd_3649_);
lean_dec(v_snd_3646_);
if (v_decide_3651_ == 0)
{
lean_object* v___x_3652_; 
lean_dec_ref(v_acc_3643_);
lean_inc(v_err_3650_);
v___x_3652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3652_, 0, v_pos_3648_);
lean_ctor_set(v___x_3652_, 1, v_err_3650_);
return v___x_3652_;
}
else
{
lean_object* v___x_3653_; 
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v_pos_3648_);
lean_ctor_set(v___x_3653_, 1, v_acc_3643_);
return v___x_3653_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0(void){
_start:
{
uint32_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3673_ = 119;
v___x_3674_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3675_ = lean_string_push(v___x_3674_, v___x_3673_);
return v___x_3675_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3676_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0);
v___x_3677_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3678_ = lean_string_append(v___x_3677_, v___x_3676_);
return v___x_3678_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2(void){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3679_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3680_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1);
v___x_3681_ = lean_string_append(v___x_3680_, v___x_3679_);
return v___x_3681_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2);
v___x_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(lean_object* v_acc_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_fst_3686_; lean_object* v_snd_3687_; lean_object* v_pos_3689_; lean_object* v_snd_3690_; lean_object* v_err_3691_; lean_object* v___x_3695_; uint8_t v_decide_3696_; 
v_fst_3686_ = lean_ctor_get(v_a_3685_, 0);
v_snd_3687_ = lean_ctor_get(v_a_3685_, 1);
lean_inc(v_snd_3687_);
v___x_3695_ = lean_string_utf8_byte_size(v_fst_3686_);
v_decide_3696_ = lean_nat_dec_eq(v_snd_3687_, v___x_3695_);
if (v_decide_3696_ == 0)
{
uint32_t v___x_3697_; uint32_t v_c_3698_; uint8_t v___x_3699_; 
v___x_3697_ = 119;
v_c_3698_ = lean_string_utf8_get_fast(v_fst_3686_, v_snd_3687_);
v___x_3699_ = lean_uint32_dec_eq(v_c_3698_, v___x_3697_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3);
lean_inc(v_snd_3687_);
v_pos_3689_ = v_a_3685_;
v_snd_3690_ = v_snd_3687_;
v_err_3691_ = v___x_3700_;
goto v___jp_3688_;
}
else
{
lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3710_; 
lean_inc(v_fst_3686_);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_a_3685_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; lean_object* v_unused_3712_; 
v_unused_3711_ = lean_ctor_get(v_a_3685_, 1);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_a_3685_, 0);
lean_dec(v_unused_3712_);
v___x_3702_ = v_a_3685_;
v_isShared_3703_ = v_isSharedCheck_3710_;
goto v_resetjp_3701_;
}
else
{
lean_dec(v_a_3685_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3710_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3704_; lean_object* v_it_x27_3706_; 
v___x_3704_ = lean_string_utf8_next_fast(v_fst_3686_, v_snd_3687_);
lean_dec(v_snd_3687_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 1, v___x_3704_);
v_it_x27_3706_ = v___x_3702_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_fst_3686_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v___x_3704_);
v_it_x27_3706_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; 
v___x_3707_ = lean_string_push(v_acc_3684_, v___x_3697_);
v_acc_3684_ = v___x_3707_;
v_a_3685_ = v_it_x27_3706_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_box(0);
lean_inc(v_snd_3687_);
v_pos_3689_ = v_a_3685_;
v_snd_3690_ = v_snd_3687_;
v_err_3691_ = v___x_3713_;
goto v___jp_3688_;
}
v___jp_3688_:
{
uint8_t v_decide_3692_; 
v_decide_3692_ = lean_nat_dec_eq(v_snd_3687_, v_snd_3690_);
lean_dec(v_snd_3690_);
lean_dec(v_snd_3687_);
if (v_decide_3692_ == 0)
{
lean_object* v___x_3693_; 
lean_dec_ref(v_acc_3684_);
lean_inc(v_err_3691_);
v___x_3693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3693_, 0, v_pos_3689_);
lean_ctor_set(v___x_3693_, 1, v_err_3691_);
return v___x_3693_;
}
else
{
lean_object* v___x_3694_; 
v___x_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3694_, 0, v_pos_3689_);
lean_ctor_set(v___x_3694_, 1, v_acc_3684_);
return v___x_3694_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0(void){
_start:
{
uint32_t v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3714_ = 100;
v___x_3715_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3716_ = lean_string_push(v___x_3715_, v___x_3714_);
return v___x_3716_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0);
v___x_3718_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3719_ = lean_string_append(v___x_3718_, v___x_3717_);
return v___x_3719_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3720_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3721_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1);
v___x_3722_ = lean_string_append(v___x_3721_, v___x_3720_);
return v___x_3722_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3(void){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2);
v___x_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(lean_object* v_acc_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v_fst_3727_; lean_object* v_snd_3728_; lean_object* v_pos_3730_; lean_object* v_snd_3731_; lean_object* v_err_3732_; lean_object* v___x_3736_; uint8_t v_decide_3737_; 
v_fst_3727_ = lean_ctor_get(v_a_3726_, 0);
v_snd_3728_ = lean_ctor_get(v_a_3726_, 1);
lean_inc(v_snd_3728_);
v___x_3736_ = lean_string_utf8_byte_size(v_fst_3727_);
v_decide_3737_ = lean_nat_dec_eq(v_snd_3728_, v___x_3736_);
if (v_decide_3737_ == 0)
{
uint32_t v___x_3738_; uint32_t v_c_3739_; uint8_t v___x_3740_; 
v___x_3738_ = 100;
v_c_3739_ = lean_string_utf8_get_fast(v_fst_3727_, v_snd_3728_);
v___x_3740_ = lean_uint32_dec_eq(v_c_3739_, v___x_3738_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3);
lean_inc(v_snd_3728_);
v_pos_3730_ = v_a_3726_;
v_snd_3731_ = v_snd_3728_;
v_err_3732_ = v___x_3741_;
goto v___jp_3729_;
}
else
{
lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3751_; 
lean_inc(v_fst_3727_);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_a_3726_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; lean_object* v_unused_3753_; 
v_unused_3752_ = lean_ctor_get(v_a_3726_, 1);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_a_3726_, 0);
lean_dec(v_unused_3753_);
v___x_3743_ = v_a_3726_;
v_isShared_3744_ = v_isSharedCheck_3751_;
goto v_resetjp_3742_;
}
else
{
lean_dec(v_a_3726_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3751_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3745_; lean_object* v_it_x27_3747_; 
v___x_3745_ = lean_string_utf8_next_fast(v_fst_3727_, v_snd_3728_);
lean_dec(v_snd_3728_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 1, v___x_3745_);
v_it_x27_3747_ = v___x_3743_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_fst_3727_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v___x_3745_);
v_it_x27_3747_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3748_; 
v___x_3748_ = lean_string_push(v_acc_3725_, v___x_3738_);
v_acc_3725_ = v___x_3748_;
v_a_3726_ = v_it_x27_3747_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3754_; 
v___x_3754_ = lean_box(0);
lean_inc(v_snd_3728_);
v_pos_3730_ = v_a_3726_;
v_snd_3731_ = v_snd_3728_;
v_err_3732_ = v___x_3754_;
goto v___jp_3729_;
}
v___jp_3729_:
{
uint8_t v_decide_3733_; 
v_decide_3733_ = lean_nat_dec_eq(v_snd_3728_, v_snd_3731_);
lean_dec(v_snd_3731_);
lean_dec(v_snd_3728_);
if (v_decide_3733_ == 0)
{
lean_object* v___x_3734_; 
lean_dec_ref(v_acc_3725_);
lean_inc(v_err_3732_);
v___x_3734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3734_, 0, v_pos_3730_);
lean_ctor_set(v___x_3734_, 1, v_err_3732_);
return v___x_3734_;
}
else
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3735_, 0, v_pos_3730_);
lean_ctor_set(v___x_3735_, 1, v_acc_3725_);
return v___x_3735_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0(void){
_start:
{
uint32_t v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3755_ = 99;
v___x_3756_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3757_ = lean_string_push(v___x_3756_, v___x_3755_);
return v___x_3757_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1(void){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3758_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0);
v___x_3759_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3760_ = lean_string_append(v___x_3759_, v___x_3758_);
return v___x_3760_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2(void){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3761_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3762_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1);
v___x_3763_ = lean_string_append(v___x_3762_, v___x_3761_);
return v___x_3763_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3(void){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2);
v___x_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(lean_object* v_acc_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v_fst_3768_; lean_object* v_snd_3769_; lean_object* v_pos_3771_; lean_object* v_snd_3772_; lean_object* v_err_3773_; lean_object* v___x_3777_; uint8_t v_decide_3778_; 
v_fst_3768_ = lean_ctor_get(v_a_3767_, 0);
v_snd_3769_ = lean_ctor_get(v_a_3767_, 1);
lean_inc(v_snd_3769_);
v___x_3777_ = lean_string_utf8_byte_size(v_fst_3768_);
v_decide_3778_ = lean_nat_dec_eq(v_snd_3769_, v___x_3777_);
if (v_decide_3778_ == 0)
{
uint32_t v___x_3779_; uint32_t v_c_3780_; uint8_t v___x_3781_; 
v___x_3779_ = 99;
v_c_3780_ = lean_string_utf8_get_fast(v_fst_3768_, v_snd_3769_);
v___x_3781_ = lean_uint32_dec_eq(v_c_3780_, v___x_3779_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; 
v___x_3782_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3);
lean_inc(v_snd_3769_);
v_pos_3771_ = v_a_3767_;
v_snd_3772_ = v_snd_3769_;
v_err_3773_ = v___x_3782_;
goto v___jp_3770_;
}
else
{
lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3792_; 
lean_inc(v_fst_3768_);
v_isSharedCheck_3792_ = !lean_is_exclusive(v_a_3767_);
if (v_isSharedCheck_3792_ == 0)
{
lean_object* v_unused_3793_; lean_object* v_unused_3794_; 
v_unused_3793_ = lean_ctor_get(v_a_3767_, 1);
lean_dec(v_unused_3793_);
v_unused_3794_ = lean_ctor_get(v_a_3767_, 0);
lean_dec(v_unused_3794_);
v___x_3784_ = v_a_3767_;
v_isShared_3785_ = v_isSharedCheck_3792_;
goto v_resetjp_3783_;
}
else
{
lean_dec(v_a_3767_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3792_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3786_; lean_object* v_it_x27_3788_; 
v___x_3786_ = lean_string_utf8_next_fast(v_fst_3768_, v_snd_3769_);
lean_dec(v_snd_3769_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 1, v___x_3786_);
v_it_x27_3788_ = v___x_3784_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_fst_3768_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v___x_3786_);
v_it_x27_3788_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3789_; 
v___x_3789_ = lean_string_push(v_acc_3766_, v___x_3779_);
v_acc_3766_ = v___x_3789_;
v_a_3767_ = v_it_x27_3788_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3795_; 
v___x_3795_ = lean_box(0);
lean_inc(v_snd_3769_);
v_pos_3771_ = v_a_3767_;
v_snd_3772_ = v_snd_3769_;
v_err_3773_ = v___x_3795_;
goto v___jp_3770_;
}
v___jp_3770_:
{
uint8_t v_decide_3774_; 
v_decide_3774_ = lean_nat_dec_eq(v_snd_3769_, v_snd_3772_);
lean_dec(v_snd_3772_);
lean_dec(v_snd_3769_);
if (v_decide_3774_ == 0)
{
lean_object* v___x_3775_; 
lean_dec_ref(v_acc_3766_);
lean_inc(v_err_3773_);
v___x_3775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3775_, 0, v_pos_3771_);
lean_ctor_set(v___x_3775_, 1, v_err_3773_);
return v___x_3775_;
}
else
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3776_, 0, v_pos_3771_);
lean_ctor_set(v___x_3776_, 1, v_acc_3766_);
return v___x_3776_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0(void){
_start:
{
uint32_t v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = 69;
v___x_3797_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3798_ = lean_string_push(v___x_3797_, v___x_3796_);
return v___x_3798_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3799_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0);
v___x_3800_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3801_ = lean_string_append(v___x_3800_, v___x_3799_);
return v___x_3801_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2(void){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3802_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3803_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1);
v___x_3804_ = lean_string_append(v___x_3803_, v___x_3802_);
return v___x_3804_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3(void){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2);
v___x_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(lean_object* v_acc_3807_, lean_object* v_a_3808_){
_start:
{
lean_object* v_fst_3809_; lean_object* v_snd_3810_; lean_object* v_pos_3812_; lean_object* v_snd_3813_; lean_object* v_err_3814_; lean_object* v___x_3818_; uint8_t v_decide_3819_; 
v_fst_3809_ = lean_ctor_get(v_a_3808_, 0);
v_snd_3810_ = lean_ctor_get(v_a_3808_, 1);
lean_inc(v_snd_3810_);
v___x_3818_ = lean_string_utf8_byte_size(v_fst_3809_);
v_decide_3819_ = lean_nat_dec_eq(v_snd_3810_, v___x_3818_);
if (v_decide_3819_ == 0)
{
uint32_t v___x_3820_; uint32_t v_c_3821_; uint8_t v___x_3822_; 
v___x_3820_ = 69;
v_c_3821_ = lean_string_utf8_get_fast(v_fst_3809_, v_snd_3810_);
v___x_3822_ = lean_uint32_dec_eq(v_c_3821_, v___x_3820_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; 
v___x_3823_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3);
lean_inc(v_snd_3810_);
v_pos_3812_ = v_a_3808_;
v_snd_3813_ = v_snd_3810_;
v_err_3814_ = v___x_3823_;
goto v___jp_3811_;
}
else
{
lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3833_; 
lean_inc(v_fst_3809_);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_a_3808_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; lean_object* v_unused_3835_; 
v_unused_3834_ = lean_ctor_get(v_a_3808_, 1);
lean_dec(v_unused_3834_);
v_unused_3835_ = lean_ctor_get(v_a_3808_, 0);
lean_dec(v_unused_3835_);
v___x_3825_ = v_a_3808_;
v_isShared_3826_ = v_isSharedCheck_3833_;
goto v_resetjp_3824_;
}
else
{
lean_dec(v_a_3808_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3833_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3827_; lean_object* v_it_x27_3829_; 
v___x_3827_ = lean_string_utf8_next_fast(v_fst_3809_, v_snd_3810_);
lean_dec(v_snd_3810_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 1, v___x_3827_);
v_it_x27_3829_ = v___x_3825_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_fst_3809_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v___x_3827_);
v_it_x27_3829_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; 
v___x_3830_ = lean_string_push(v_acc_3807_, v___x_3820_);
v_acc_3807_ = v___x_3830_;
v_a_3808_ = v_it_x27_3829_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3836_; 
v___x_3836_ = lean_box(0);
lean_inc(v_snd_3810_);
v_pos_3812_ = v_a_3808_;
v_snd_3813_ = v_snd_3810_;
v_err_3814_ = v___x_3836_;
goto v___jp_3811_;
}
v___jp_3811_:
{
uint8_t v_decide_3815_; 
v_decide_3815_ = lean_nat_dec_eq(v_snd_3810_, v_snd_3813_);
lean_dec(v_snd_3813_);
lean_dec(v_snd_3810_);
if (v_decide_3815_ == 0)
{
lean_object* v___x_3816_; 
lean_dec_ref(v_acc_3807_);
lean_inc(v_err_3814_);
v___x_3816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3816_, 0, v_pos_3812_);
lean_ctor_set(v___x_3816_, 1, v_err_3814_);
return v___x_3816_;
}
else
{
lean_object* v___x_3817_; 
v___x_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3817_, 0, v_pos_3812_);
lean_ctor_set(v___x_3817_, 1, v_acc_3807_);
return v___x_3817_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0(void){
_start:
{
uint32_t v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = 97;
v___x_3838_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3839_ = lean_string_push(v___x_3838_, v___x_3837_);
return v___x_3839_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3840_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0);
v___x_3841_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3842_ = lean_string_append(v___x_3841_, v___x_3840_);
return v___x_3842_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2(void){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3843_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3844_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1);
v___x_3845_ = lean_string_append(v___x_3844_, v___x_3843_);
return v___x_3845_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2);
v___x_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(lean_object* v_acc_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v_fst_3850_; lean_object* v_snd_3851_; lean_object* v_pos_3853_; lean_object* v_snd_3854_; lean_object* v_err_3855_; lean_object* v___x_3859_; uint8_t v_decide_3860_; 
v_fst_3850_ = lean_ctor_get(v_a_3849_, 0);
v_snd_3851_ = lean_ctor_get(v_a_3849_, 1);
lean_inc(v_snd_3851_);
v___x_3859_ = lean_string_utf8_byte_size(v_fst_3850_);
v_decide_3860_ = lean_nat_dec_eq(v_snd_3851_, v___x_3859_);
if (v_decide_3860_ == 0)
{
uint32_t v___x_3861_; uint32_t v_c_3862_; uint8_t v___x_3863_; 
v___x_3861_ = 97;
v_c_3862_ = lean_string_utf8_get_fast(v_fst_3850_, v_snd_3851_);
v___x_3863_ = lean_uint32_dec_eq(v_c_3862_, v___x_3861_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3);
lean_inc(v_snd_3851_);
v_pos_3853_ = v_a_3849_;
v_snd_3854_ = v_snd_3851_;
v_err_3855_ = v___x_3864_;
goto v___jp_3852_;
}
else
{
lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3874_; 
lean_inc(v_fst_3850_);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_a_3849_);
if (v_isSharedCheck_3874_ == 0)
{
lean_object* v_unused_3875_; lean_object* v_unused_3876_; 
v_unused_3875_ = lean_ctor_get(v_a_3849_, 1);
lean_dec(v_unused_3875_);
v_unused_3876_ = lean_ctor_get(v_a_3849_, 0);
lean_dec(v_unused_3876_);
v___x_3866_ = v_a_3849_;
v_isShared_3867_ = v_isSharedCheck_3874_;
goto v_resetjp_3865_;
}
else
{
lean_dec(v_a_3849_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3874_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; lean_object* v_it_x27_3870_; 
v___x_3868_ = lean_string_utf8_next_fast(v_fst_3850_, v_snd_3851_);
lean_dec(v_snd_3851_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 1, v___x_3868_);
v_it_x27_3870_ = v___x_3866_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_fst_3850_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v___x_3868_);
v_it_x27_3870_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_string_push(v_acc_3848_, v___x_3861_);
v_acc_3848_ = v___x_3871_;
v_a_3849_ = v_it_x27_3870_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3877_; 
v___x_3877_ = lean_box(0);
lean_inc(v_snd_3851_);
v_pos_3853_ = v_a_3849_;
v_snd_3854_ = v_snd_3851_;
v_err_3855_ = v___x_3877_;
goto v___jp_3852_;
}
v___jp_3852_:
{
uint8_t v_decide_3856_; 
v_decide_3856_ = lean_nat_dec_eq(v_snd_3851_, v_snd_3854_);
lean_dec(v_snd_3854_);
lean_dec(v_snd_3851_);
if (v_decide_3856_ == 0)
{
lean_object* v___x_3857_; 
lean_dec_ref(v_acc_3848_);
lean_inc(v_err_3855_);
v___x_3857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3857_, 0, v_pos_3853_);
lean_ctor_set(v___x_3857_, 1, v_err_3855_);
return v___x_3857_;
}
else
{
lean_object* v___x_3858_; 
v___x_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3858_, 0, v_pos_3853_);
lean_ctor_set(v___x_3858_, 1, v_acc_3848_);
return v___x_3858_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0(void){
_start:
{
uint32_t v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = 79;
v___x_3879_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3880_ = lean_string_push(v___x_3879_, v___x_3878_);
return v___x_3880_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3881_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0);
v___x_3882_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3883_ = lean_string_append(v___x_3882_, v___x_3881_);
return v___x_3883_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3885_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1);
v___x_3886_ = lean_string_append(v___x_3885_, v___x_3884_);
return v___x_3886_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2);
v___x_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(lean_object* v_acc_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v_fst_3891_; lean_object* v_snd_3892_; lean_object* v_pos_3894_; lean_object* v_snd_3895_; lean_object* v_err_3896_; lean_object* v___x_3900_; uint8_t v_decide_3901_; 
v_fst_3891_ = lean_ctor_get(v_a_3890_, 0);
v_snd_3892_ = lean_ctor_get(v_a_3890_, 1);
lean_inc(v_snd_3892_);
v___x_3900_ = lean_string_utf8_byte_size(v_fst_3891_);
v_decide_3901_ = lean_nat_dec_eq(v_snd_3892_, v___x_3900_);
if (v_decide_3901_ == 0)
{
uint32_t v___x_3902_; uint32_t v_c_3903_; uint8_t v___x_3904_; 
v___x_3902_ = 79;
v_c_3903_ = lean_string_utf8_get_fast(v_fst_3891_, v_snd_3892_);
v___x_3904_ = lean_uint32_dec_eq(v_c_3903_, v___x_3902_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; 
v___x_3905_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3);
lean_inc(v_snd_3892_);
v_pos_3894_ = v_a_3890_;
v_snd_3895_ = v_snd_3892_;
v_err_3896_ = v___x_3905_;
goto v___jp_3893_;
}
else
{
lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3915_; 
lean_inc(v_fst_3891_);
v_isSharedCheck_3915_ = !lean_is_exclusive(v_a_3890_);
if (v_isSharedCheck_3915_ == 0)
{
lean_object* v_unused_3916_; lean_object* v_unused_3917_; 
v_unused_3916_ = lean_ctor_get(v_a_3890_, 1);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_a_3890_, 0);
lean_dec(v_unused_3917_);
v___x_3907_ = v_a_3890_;
v_isShared_3908_ = v_isSharedCheck_3915_;
goto v_resetjp_3906_;
}
else
{
lean_dec(v_a_3890_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3915_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v_it_x27_3911_; 
v___x_3909_ = lean_string_utf8_next_fast(v_fst_3891_, v_snd_3892_);
lean_dec(v_snd_3892_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 1, v___x_3909_);
v_it_x27_3911_ = v___x_3907_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_fst_3891_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3909_);
v_it_x27_3911_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3912_; 
v___x_3912_ = lean_string_push(v_acc_3889_, v___x_3902_);
v_acc_3889_ = v___x_3912_;
v_a_3890_ = v_it_x27_3911_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3918_; 
v___x_3918_ = lean_box(0);
lean_inc(v_snd_3892_);
v_pos_3894_ = v_a_3890_;
v_snd_3895_ = v_snd_3892_;
v_err_3896_ = v___x_3918_;
goto v___jp_3893_;
}
v___jp_3893_:
{
uint8_t v_decide_3897_; 
v_decide_3897_ = lean_nat_dec_eq(v_snd_3892_, v_snd_3895_);
lean_dec(v_snd_3895_);
lean_dec(v_snd_3892_);
if (v_decide_3897_ == 0)
{
lean_object* v___x_3898_; 
lean_dec_ref(v_acc_3889_);
lean_inc(v_err_3896_);
v___x_3898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3898_, 0, v_pos_3894_);
lean_ctor_set(v___x_3898_, 1, v_err_3896_);
return v___x_3898_;
}
else
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3899_, 0, v_pos_3894_);
lean_ctor_set(v___x_3899_, 1, v_acc_3889_);
return v___x_3899_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0(void){
_start:
{
uint32_t v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3919_ = 65;
v___x_3920_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3921_ = lean_string_push(v___x_3920_, v___x_3919_);
return v___x_3921_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3922_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0);
v___x_3923_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3924_ = lean_string_append(v___x_3923_, v___x_3922_);
return v___x_3924_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2(void){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3925_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3926_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1);
v___x_3927_ = lean_string_append(v___x_3926_, v___x_3925_);
return v___x_3927_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3(void){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2);
v___x_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(lean_object* v_acc_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v_fst_3932_; lean_object* v_snd_3933_; lean_object* v_pos_3935_; lean_object* v_snd_3936_; lean_object* v_err_3937_; lean_object* v___x_3941_; uint8_t v_decide_3942_; 
v_fst_3932_ = lean_ctor_get(v_a_3931_, 0);
v_snd_3933_ = lean_ctor_get(v_a_3931_, 1);
lean_inc(v_snd_3933_);
v___x_3941_ = lean_string_utf8_byte_size(v_fst_3932_);
v_decide_3942_ = lean_nat_dec_eq(v_snd_3933_, v___x_3941_);
if (v_decide_3942_ == 0)
{
uint32_t v___x_3943_; uint32_t v_c_3944_; uint8_t v___x_3945_; 
v___x_3943_ = 65;
v_c_3944_ = lean_string_utf8_get_fast(v_fst_3932_, v_snd_3933_);
v___x_3945_ = lean_uint32_dec_eq(v_c_3944_, v___x_3943_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3946_; 
v___x_3946_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3);
lean_inc(v_snd_3933_);
v_pos_3935_ = v_a_3931_;
v_snd_3936_ = v_snd_3933_;
v_err_3937_ = v___x_3946_;
goto v___jp_3934_;
}
else
{
lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3956_; 
lean_inc(v_fst_3932_);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_a_3931_);
if (v_isSharedCheck_3956_ == 0)
{
lean_object* v_unused_3957_; lean_object* v_unused_3958_; 
v_unused_3957_ = lean_ctor_get(v_a_3931_, 1);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v_a_3931_, 0);
lean_dec(v_unused_3958_);
v___x_3948_ = v_a_3931_;
v_isShared_3949_ = v_isSharedCheck_3956_;
goto v_resetjp_3947_;
}
else
{
lean_dec(v_a_3931_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3956_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; lean_object* v_it_x27_3952_; 
v___x_3950_ = lean_string_utf8_next_fast(v_fst_3932_, v_snd_3933_);
lean_dec(v_snd_3933_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v___x_3950_);
v_it_x27_3952_ = v___x_3948_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_fst_3932_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v___x_3950_);
v_it_x27_3952_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3953_; 
v___x_3953_ = lean_string_push(v_acc_3930_, v___x_3943_);
v_acc_3930_ = v___x_3953_;
v_a_3931_ = v_it_x27_3952_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3959_; 
v___x_3959_ = lean_box(0);
lean_inc(v_snd_3933_);
v_pos_3935_ = v_a_3931_;
v_snd_3936_ = v_snd_3933_;
v_err_3937_ = v___x_3959_;
goto v___jp_3934_;
}
v___jp_3934_:
{
uint8_t v_decide_3938_; 
v_decide_3938_ = lean_nat_dec_eq(v_snd_3933_, v_snd_3936_);
lean_dec(v_snd_3936_);
lean_dec(v_snd_3933_);
if (v_decide_3938_ == 0)
{
lean_object* v___x_3939_; 
lean_dec_ref(v_acc_3930_);
lean_inc(v_err_3937_);
v___x_3939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3939_, 0, v_pos_3935_);
lean_ctor_set(v___x_3939_, 1, v_err_3937_);
return v___x_3939_;
}
else
{
lean_object* v___x_3940_; 
v___x_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3940_, 0, v_pos_3935_);
lean_ctor_set(v___x_3940_, 1, v_acc_3930_);
return v___x_3940_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0(void){
_start:
{
uint32_t v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = 76;
v___x_3961_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3962_ = lean_string_push(v___x_3961_, v___x_3960_);
return v___x_3962_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0);
v___x_3964_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3965_ = lean_string_append(v___x_3964_, v___x_3963_);
return v___x_3965_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3966_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3967_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1);
v___x_3968_ = lean_string_append(v___x_3967_, v___x_3966_);
return v___x_3968_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2);
v___x_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(lean_object* v_acc_3971_, lean_object* v_a_3972_){
_start:
{
lean_object* v_fst_3973_; lean_object* v_snd_3974_; lean_object* v_pos_3976_; lean_object* v_snd_3977_; lean_object* v_err_3978_; lean_object* v___x_3982_; uint8_t v_decide_3983_; 
v_fst_3973_ = lean_ctor_get(v_a_3972_, 0);
v_snd_3974_ = lean_ctor_get(v_a_3972_, 1);
lean_inc(v_snd_3974_);
v___x_3982_ = lean_string_utf8_byte_size(v_fst_3973_);
v_decide_3983_ = lean_nat_dec_eq(v_snd_3974_, v___x_3982_);
if (v_decide_3983_ == 0)
{
uint32_t v___x_3984_; uint32_t v_c_3985_; uint8_t v___x_3986_; 
v___x_3984_ = 76;
v_c_3985_ = lean_string_utf8_get_fast(v_fst_3973_, v_snd_3974_);
v___x_3986_ = lean_uint32_dec_eq(v_c_3985_, v___x_3984_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; 
v___x_3987_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3);
lean_inc(v_snd_3974_);
v_pos_3976_ = v_a_3972_;
v_snd_3977_ = v_snd_3974_;
v_err_3978_ = v___x_3987_;
goto v___jp_3975_;
}
else
{
lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3997_; 
lean_inc(v_fst_3973_);
v_isSharedCheck_3997_ = !lean_is_exclusive(v_a_3972_);
if (v_isSharedCheck_3997_ == 0)
{
lean_object* v_unused_3998_; lean_object* v_unused_3999_; 
v_unused_3998_ = lean_ctor_get(v_a_3972_, 1);
lean_dec(v_unused_3998_);
v_unused_3999_ = lean_ctor_get(v_a_3972_, 0);
lean_dec(v_unused_3999_);
v___x_3989_ = v_a_3972_;
v_isShared_3990_ = v_isSharedCheck_3997_;
goto v_resetjp_3988_;
}
else
{
lean_dec(v_a_3972_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3997_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3991_; lean_object* v_it_x27_3993_; 
v___x_3991_ = lean_string_utf8_next_fast(v_fst_3973_, v_snd_3974_);
lean_dec(v_snd_3974_);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 1, v___x_3991_);
v_it_x27_3993_ = v___x_3989_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_fst_3973_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v___x_3991_);
v_it_x27_3993_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_string_push(v_acc_3971_, v___x_3984_);
v_acc_3971_ = v___x_3994_;
v_a_3972_ = v_it_x27_3993_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_box(0);
lean_inc(v_snd_3974_);
v_pos_3976_ = v_a_3972_;
v_snd_3977_ = v_snd_3974_;
v_err_3978_ = v___x_4000_;
goto v___jp_3975_;
}
v___jp_3975_:
{
uint8_t v_decide_3979_; 
v_decide_3979_ = lean_nat_dec_eq(v_snd_3974_, v_snd_3977_);
lean_dec(v_snd_3977_);
lean_dec(v_snd_3974_);
if (v_decide_3979_ == 0)
{
lean_object* v___x_3980_; 
lean_dec_ref(v_acc_3971_);
lean_inc(v_err_3978_);
v___x_3980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3980_, 0, v_pos_3976_);
lean_ctor_set(v___x_3980_, 1, v_err_3978_);
return v___x_3980_;
}
else
{
lean_object* v___x_3981_; 
v___x_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3981_, 0, v_pos_3976_);
lean_ctor_set(v___x_3981_, 1, v_acc_3971_);
return v___x_3981_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0(void){
_start:
{
uint32_t v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = 113;
v___x_4002_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4003_ = lean_string_push(v___x_4002_, v___x_4001_);
return v___x_4003_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1(void){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0);
v___x_4005_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4006_ = lean_string_append(v___x_4005_, v___x_4004_);
return v___x_4006_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2(void){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4007_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4008_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1);
v___x_4009_ = lean_string_append(v___x_4008_, v___x_4007_);
return v___x_4009_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3(void){
_start:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2);
v___x_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(lean_object* v_acc_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_fst_4014_; lean_object* v_snd_4015_; lean_object* v_pos_4017_; lean_object* v_snd_4018_; lean_object* v_err_4019_; lean_object* v___x_4023_; uint8_t v_decide_4024_; 
v_fst_4014_ = lean_ctor_get(v_a_4013_, 0);
v_snd_4015_ = lean_ctor_get(v_a_4013_, 1);
lean_inc(v_snd_4015_);
v___x_4023_ = lean_string_utf8_byte_size(v_fst_4014_);
v_decide_4024_ = lean_nat_dec_eq(v_snd_4015_, v___x_4023_);
if (v_decide_4024_ == 0)
{
uint32_t v___x_4025_; uint32_t v_c_4026_; uint8_t v___x_4027_; 
v___x_4025_ = 113;
v_c_4026_ = lean_string_utf8_get_fast(v_fst_4014_, v_snd_4015_);
v___x_4027_ = lean_uint32_dec_eq(v_c_4026_, v___x_4025_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; 
v___x_4028_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3);
lean_inc(v_snd_4015_);
v_pos_4017_ = v_a_4013_;
v_snd_4018_ = v_snd_4015_;
v_err_4019_ = v___x_4028_;
goto v___jp_4016_;
}
else
{
lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4038_; 
lean_inc(v_fst_4014_);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_a_4013_);
if (v_isSharedCheck_4038_ == 0)
{
lean_object* v_unused_4039_; lean_object* v_unused_4040_; 
v_unused_4039_ = lean_ctor_get(v_a_4013_, 1);
lean_dec(v_unused_4039_);
v_unused_4040_ = lean_ctor_get(v_a_4013_, 0);
lean_dec(v_unused_4040_);
v___x_4030_ = v_a_4013_;
v_isShared_4031_ = v_isSharedCheck_4038_;
goto v_resetjp_4029_;
}
else
{
lean_dec(v_a_4013_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4038_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4032_; lean_object* v_it_x27_4034_; 
v___x_4032_ = lean_string_utf8_next_fast(v_fst_4014_, v_snd_4015_);
lean_dec(v_snd_4015_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4032_);
v_it_x27_4034_ = v___x_4030_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_fst_4014_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v___x_4032_);
v_it_x27_4034_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4035_; 
v___x_4035_ = lean_string_push(v_acc_4012_, v___x_4025_);
v_acc_4012_ = v___x_4035_;
v_a_4013_ = v_it_x27_4034_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_box(0);
lean_inc(v_snd_4015_);
v_pos_4017_ = v_a_4013_;
v_snd_4018_ = v_snd_4015_;
v_err_4019_ = v___x_4041_;
goto v___jp_4016_;
}
v___jp_4016_:
{
uint8_t v_decide_4020_; 
v_decide_4020_ = lean_nat_dec_eq(v_snd_4015_, v_snd_4018_);
lean_dec(v_snd_4018_);
lean_dec(v_snd_4015_);
if (v_decide_4020_ == 0)
{
lean_object* v___x_4021_; 
lean_dec_ref(v_acc_4012_);
lean_inc(v_err_4019_);
v___x_4021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4021_, 0, v_pos_4017_);
lean_ctor_set(v___x_4021_, 1, v_err_4019_);
return v___x_4021_;
}
else
{
lean_object* v___x_4022_; 
v___x_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4022_, 0, v_pos_4017_);
lean_ctor_set(v___x_4022_, 1, v_acc_4012_);
return v___x_4022_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0(void){
_start:
{
uint32_t v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = 72;
v___x_4043_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4044_ = lean_string_push(v___x_4043_, v___x_4042_);
return v___x_4044_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1(void){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4045_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0);
v___x_4046_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4047_ = lean_string_append(v___x_4046_, v___x_4045_);
return v___x_4047_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4048_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4049_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1);
v___x_4050_ = lean_string_append(v___x_4049_, v___x_4048_);
return v___x_4050_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4051_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2);
v___x_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(lean_object* v_acc_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v_fst_4055_; lean_object* v_snd_4056_; lean_object* v_pos_4058_; lean_object* v_snd_4059_; lean_object* v_err_4060_; lean_object* v___x_4064_; uint8_t v_decide_4065_; 
v_fst_4055_ = lean_ctor_get(v_a_4054_, 0);
v_snd_4056_ = lean_ctor_get(v_a_4054_, 1);
lean_inc(v_snd_4056_);
v___x_4064_ = lean_string_utf8_byte_size(v_fst_4055_);
v_decide_4065_ = lean_nat_dec_eq(v_snd_4056_, v___x_4064_);
if (v_decide_4065_ == 0)
{
uint32_t v___x_4066_; uint32_t v_c_4067_; uint8_t v___x_4068_; 
v___x_4066_ = 72;
v_c_4067_ = lean_string_utf8_get_fast(v_fst_4055_, v_snd_4056_);
v___x_4068_ = lean_uint32_dec_eq(v_c_4067_, v___x_4066_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; 
v___x_4069_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3);
lean_inc(v_snd_4056_);
v_pos_4058_ = v_a_4054_;
v_snd_4059_ = v_snd_4056_;
v_err_4060_ = v___x_4069_;
goto v___jp_4057_;
}
else
{
lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4079_; 
lean_inc(v_fst_4055_);
v_isSharedCheck_4079_ = !lean_is_exclusive(v_a_4054_);
if (v_isSharedCheck_4079_ == 0)
{
lean_object* v_unused_4080_; lean_object* v_unused_4081_; 
v_unused_4080_ = lean_ctor_get(v_a_4054_, 1);
lean_dec(v_unused_4080_);
v_unused_4081_ = lean_ctor_get(v_a_4054_, 0);
lean_dec(v_unused_4081_);
v___x_4071_ = v_a_4054_;
v_isShared_4072_ = v_isSharedCheck_4079_;
goto v_resetjp_4070_;
}
else
{
lean_dec(v_a_4054_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4079_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v_it_x27_4075_; 
v___x_4073_ = lean_string_utf8_next_fast(v_fst_4055_, v_snd_4056_);
lean_dec(v_snd_4056_);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 1, v___x_4073_);
v_it_x27_4075_ = v___x_4071_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_fst_4055_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v___x_4073_);
v_it_x27_4075_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4076_; 
v___x_4076_ = lean_string_push(v_acc_4053_, v___x_4066_);
v_acc_4053_ = v___x_4076_;
v_a_4054_ = v_it_x27_4075_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4082_; 
v___x_4082_ = lean_box(0);
lean_inc(v_snd_4056_);
v_pos_4058_ = v_a_4054_;
v_snd_4059_ = v_snd_4056_;
v_err_4060_ = v___x_4082_;
goto v___jp_4057_;
}
v___jp_4057_:
{
uint8_t v_decide_4061_; 
v_decide_4061_ = lean_nat_dec_eq(v_snd_4056_, v_snd_4059_);
lean_dec(v_snd_4059_);
lean_dec(v_snd_4056_);
if (v_decide_4061_ == 0)
{
lean_object* v___x_4062_; 
lean_dec_ref(v_acc_4053_);
lean_inc(v_err_4060_);
v___x_4062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4062_, 0, v_pos_4058_);
lean_ctor_set(v___x_4062_, 1, v_err_4060_);
return v___x_4062_;
}
else
{
lean_object* v___x_4063_; 
v___x_4063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4063_, 0, v_pos_4058_);
lean_ctor_set(v___x_4063_, 1, v_acc_4053_);
return v___x_4063_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0(void){
_start:
{
uint32_t v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4083_ = 118;
v___x_4084_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4085_ = lean_string_push(v___x_4084_, v___x_4083_);
return v___x_4085_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1(void){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0);
v___x_4087_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4088_ = lean_string_append(v___x_4087_, v___x_4086_);
return v___x_4088_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2(void){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4090_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1);
v___x_4091_ = lean_string_append(v___x_4090_, v___x_4089_);
return v___x_4091_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3(void){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4092_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2);
v___x_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(lean_object* v_acc_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_fst_4096_; lean_object* v_snd_4097_; lean_object* v_pos_4099_; lean_object* v_snd_4100_; lean_object* v_err_4101_; lean_object* v___x_4105_; uint8_t v_decide_4106_; 
v_fst_4096_ = lean_ctor_get(v_a_4095_, 0);
v_snd_4097_ = lean_ctor_get(v_a_4095_, 1);
lean_inc(v_snd_4097_);
v___x_4105_ = lean_string_utf8_byte_size(v_fst_4096_);
v_decide_4106_ = lean_nat_dec_eq(v_snd_4097_, v___x_4105_);
if (v_decide_4106_ == 0)
{
uint32_t v___x_4107_; uint32_t v_c_4108_; uint8_t v___x_4109_; 
v___x_4107_ = 118;
v_c_4108_ = lean_string_utf8_get_fast(v_fst_4096_, v_snd_4097_);
v___x_4109_ = lean_uint32_dec_eq(v_c_4108_, v___x_4107_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; 
v___x_4110_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3);
lean_inc(v_snd_4097_);
v_pos_4099_ = v_a_4095_;
v_snd_4100_ = v_snd_4097_;
v_err_4101_ = v___x_4110_;
goto v___jp_4098_;
}
else
{
lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4120_; 
lean_inc(v_fst_4096_);
v_isSharedCheck_4120_ = !lean_is_exclusive(v_a_4095_);
if (v_isSharedCheck_4120_ == 0)
{
lean_object* v_unused_4121_; lean_object* v_unused_4122_; 
v_unused_4121_ = lean_ctor_get(v_a_4095_, 1);
lean_dec(v_unused_4121_);
v_unused_4122_ = lean_ctor_get(v_a_4095_, 0);
lean_dec(v_unused_4122_);
v___x_4112_ = v_a_4095_;
v_isShared_4113_ = v_isSharedCheck_4120_;
goto v_resetjp_4111_;
}
else
{
lean_dec(v_a_4095_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4120_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4114_; lean_object* v_it_x27_4116_; 
v___x_4114_ = lean_string_utf8_next_fast(v_fst_4096_, v_snd_4097_);
lean_dec(v_snd_4097_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 1, v___x_4114_);
v_it_x27_4116_ = v___x_4112_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_fst_4096_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v___x_4114_);
v_it_x27_4116_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
lean_object* v___x_4117_; 
v___x_4117_ = lean_string_push(v_acc_4094_, v___x_4107_);
v_acc_4094_ = v___x_4117_;
v_a_4095_ = v_it_x27_4116_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4123_; 
v___x_4123_ = lean_box(0);
lean_inc(v_snd_4097_);
v_pos_4099_ = v_a_4095_;
v_snd_4100_ = v_snd_4097_;
v_err_4101_ = v___x_4123_;
goto v___jp_4098_;
}
v___jp_4098_:
{
uint8_t v_decide_4102_; 
v_decide_4102_ = lean_nat_dec_eq(v_snd_4097_, v_snd_4100_);
lean_dec(v_snd_4100_);
lean_dec(v_snd_4097_);
if (v_decide_4102_ == 0)
{
lean_object* v___x_4103_; 
lean_dec_ref(v_acc_4094_);
lean_inc(v_err_4101_);
v___x_4103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4103_, 0, v_pos_4099_);
lean_ctor_set(v___x_4103_, 1, v_err_4101_);
return v___x_4103_;
}
else
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4104_, 0, v_pos_4099_);
lean_ctor_set(v___x_4104_, 1, v_acc_4094_);
return v___x_4104_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0(void){
_start:
{
uint32_t v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4124_ = 87;
v___x_4125_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4126_ = lean_string_push(v___x_4125_, v___x_4124_);
return v___x_4126_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1(void){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4127_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0);
v___x_4128_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4129_ = lean_string_append(v___x_4128_, v___x_4127_);
return v___x_4129_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4130_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4131_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1);
v___x_4132_ = lean_string_append(v___x_4131_, v___x_4130_);
return v___x_4132_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4133_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2);
v___x_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(lean_object* v_acc_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v_fst_4137_; lean_object* v_snd_4138_; lean_object* v_pos_4140_; lean_object* v_snd_4141_; lean_object* v_err_4142_; lean_object* v___x_4146_; uint8_t v_decide_4147_; 
v_fst_4137_ = lean_ctor_get(v_a_4136_, 0);
v_snd_4138_ = lean_ctor_get(v_a_4136_, 1);
lean_inc(v_snd_4138_);
v___x_4146_ = lean_string_utf8_byte_size(v_fst_4137_);
v_decide_4147_ = lean_nat_dec_eq(v_snd_4138_, v___x_4146_);
if (v_decide_4147_ == 0)
{
uint32_t v___x_4148_; uint32_t v_c_4149_; uint8_t v___x_4150_; 
v___x_4148_ = 87;
v_c_4149_ = lean_string_utf8_get_fast(v_fst_4137_, v_snd_4138_);
v___x_4150_ = lean_uint32_dec_eq(v_c_4149_, v___x_4148_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; 
v___x_4151_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3);
lean_inc(v_snd_4138_);
v_pos_4140_ = v_a_4136_;
v_snd_4141_ = v_snd_4138_;
v_err_4142_ = v___x_4151_;
goto v___jp_4139_;
}
else
{
lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4161_; 
lean_inc(v_fst_4137_);
v_isSharedCheck_4161_ = !lean_is_exclusive(v_a_4136_);
if (v_isSharedCheck_4161_ == 0)
{
lean_object* v_unused_4162_; lean_object* v_unused_4163_; 
v_unused_4162_ = lean_ctor_get(v_a_4136_, 1);
lean_dec(v_unused_4162_);
v_unused_4163_ = lean_ctor_get(v_a_4136_, 0);
lean_dec(v_unused_4163_);
v___x_4153_ = v_a_4136_;
v_isShared_4154_ = v_isSharedCheck_4161_;
goto v_resetjp_4152_;
}
else
{
lean_dec(v_a_4136_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4161_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4155_; lean_object* v_it_x27_4157_; 
v___x_4155_ = lean_string_utf8_next_fast(v_fst_4137_, v_snd_4138_);
lean_dec(v_snd_4138_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 1, v___x_4155_);
v_it_x27_4157_ = v___x_4153_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_fst_4137_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v___x_4155_);
v_it_x27_4157_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4158_; 
v___x_4158_ = lean_string_push(v_acc_4135_, v___x_4148_);
v_acc_4135_ = v___x_4158_;
v_a_4136_ = v_it_x27_4157_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4164_; 
v___x_4164_ = lean_box(0);
lean_inc(v_snd_4138_);
v_pos_4140_ = v_a_4136_;
v_snd_4141_ = v_snd_4138_;
v_err_4142_ = v___x_4164_;
goto v___jp_4139_;
}
v___jp_4139_:
{
uint8_t v_decide_4143_; 
v_decide_4143_ = lean_nat_dec_eq(v_snd_4138_, v_snd_4141_);
lean_dec(v_snd_4141_);
lean_dec(v_snd_4138_);
if (v_decide_4143_ == 0)
{
lean_object* v___x_4144_; 
lean_dec_ref(v_acc_4135_);
lean_inc(v_err_4142_);
v___x_4144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4144_, 0, v_pos_4140_);
lean_ctor_set(v___x_4144_, 1, v_err_4142_);
return v___x_4144_;
}
else
{
lean_object* v___x_4145_; 
v___x_4145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4145_, 0, v_pos_4140_);
lean_ctor_set(v___x_4145_, 1, v_acc_4135_);
return v___x_4145_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0(void){
_start:
{
uint32_t v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4165_ = 107;
v___x_4166_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4167_ = lean_string_push(v___x_4166_, v___x_4165_);
return v___x_4167_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1(void){
_start:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4168_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0);
v___x_4169_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4170_ = lean_string_append(v___x_4169_, v___x_4168_);
return v___x_4170_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2(void){
_start:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4171_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4172_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1);
v___x_4173_ = lean_string_append(v___x_4172_, v___x_4171_);
return v___x_4173_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3(void){
_start:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2);
v___x_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(lean_object* v_acc_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v_fst_4178_; lean_object* v_snd_4179_; lean_object* v_pos_4181_; lean_object* v_snd_4182_; lean_object* v_err_4183_; lean_object* v___x_4187_; uint8_t v_decide_4188_; 
v_fst_4178_ = lean_ctor_get(v_a_4177_, 0);
v_snd_4179_ = lean_ctor_get(v_a_4177_, 1);
lean_inc(v_snd_4179_);
v___x_4187_ = lean_string_utf8_byte_size(v_fst_4178_);
v_decide_4188_ = lean_nat_dec_eq(v_snd_4179_, v___x_4187_);
if (v_decide_4188_ == 0)
{
uint32_t v___x_4189_; uint32_t v_c_4190_; uint8_t v___x_4191_; 
v___x_4189_ = 107;
v_c_4190_ = lean_string_utf8_get_fast(v_fst_4178_, v_snd_4179_);
v___x_4191_ = lean_uint32_dec_eq(v_c_4190_, v___x_4189_);
if (v___x_4191_ == 0)
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3);
lean_inc(v_snd_4179_);
v_pos_4181_ = v_a_4177_;
v_snd_4182_ = v_snd_4179_;
v_err_4183_ = v___x_4192_;
goto v___jp_4180_;
}
else
{
lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4202_; 
lean_inc(v_fst_4178_);
v_isSharedCheck_4202_ = !lean_is_exclusive(v_a_4177_);
if (v_isSharedCheck_4202_ == 0)
{
lean_object* v_unused_4203_; lean_object* v_unused_4204_; 
v_unused_4203_ = lean_ctor_get(v_a_4177_, 1);
lean_dec(v_unused_4203_);
v_unused_4204_ = lean_ctor_get(v_a_4177_, 0);
lean_dec(v_unused_4204_);
v___x_4194_ = v_a_4177_;
v_isShared_4195_ = v_isSharedCheck_4202_;
goto v_resetjp_4193_;
}
else
{
lean_dec(v_a_4177_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4202_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4196_; lean_object* v_it_x27_4198_; 
v___x_4196_ = lean_string_utf8_next_fast(v_fst_4178_, v_snd_4179_);
lean_dec(v_snd_4179_);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 1, v___x_4196_);
v_it_x27_4198_ = v___x_4194_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_fst_4178_);
lean_ctor_set(v_reuseFailAlloc_4201_, 1, v___x_4196_);
v_it_x27_4198_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4199_; 
v___x_4199_ = lean_string_push(v_acc_4176_, v___x_4189_);
v_acc_4176_ = v___x_4199_;
v_a_4177_ = v_it_x27_4198_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4205_; 
v___x_4205_ = lean_box(0);
lean_inc(v_snd_4179_);
v_pos_4181_ = v_a_4177_;
v_snd_4182_ = v_snd_4179_;
v_err_4183_ = v___x_4205_;
goto v___jp_4180_;
}
v___jp_4180_:
{
uint8_t v_decide_4184_; 
v_decide_4184_ = lean_nat_dec_eq(v_snd_4179_, v_snd_4182_);
lean_dec(v_snd_4182_);
lean_dec(v_snd_4179_);
if (v_decide_4184_ == 0)
{
lean_object* v___x_4185_; 
lean_dec_ref(v_acc_4176_);
lean_inc(v_err_4183_);
v___x_4185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4185_, 0, v_pos_4181_);
lean_ctor_set(v___x_4185_, 1, v_err_4183_);
return v___x_4185_;
}
else
{
lean_object* v___x_4186_; 
v___x_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4186_, 0, v_pos_4181_);
lean_ctor_set(v___x_4186_, 1, v_acc_4176_);
return v___x_4186_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0(void){
_start:
{
uint32_t v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4206_ = 121;
v___x_4207_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4208_ = lean_string_push(v___x_4207_, v___x_4206_);
return v___x_4208_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1(void){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0);
v___x_4210_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4211_ = lean_string_append(v___x_4210_, v___x_4209_);
return v___x_4211_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2(void){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4213_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1);
v___x_4214_ = lean_string_append(v___x_4213_, v___x_4212_);
return v___x_4214_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2);
v___x_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(lean_object* v_acc_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_fst_4219_; lean_object* v_snd_4220_; lean_object* v_pos_4222_; lean_object* v_snd_4223_; lean_object* v_err_4224_; lean_object* v___x_4228_; uint8_t v_decide_4229_; 
v_fst_4219_ = lean_ctor_get(v_a_4218_, 0);
v_snd_4220_ = lean_ctor_get(v_a_4218_, 1);
lean_inc(v_snd_4220_);
v___x_4228_ = lean_string_utf8_byte_size(v_fst_4219_);
v_decide_4229_ = lean_nat_dec_eq(v_snd_4220_, v___x_4228_);
if (v_decide_4229_ == 0)
{
uint32_t v___x_4230_; uint32_t v_c_4231_; uint8_t v___x_4232_; 
v___x_4230_ = 121;
v_c_4231_ = lean_string_utf8_get_fast(v_fst_4219_, v_snd_4220_);
v___x_4232_ = lean_uint32_dec_eq(v_c_4231_, v___x_4230_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4233_; 
v___x_4233_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3);
lean_inc(v_snd_4220_);
v_pos_4222_ = v_a_4218_;
v_snd_4223_ = v_snd_4220_;
v_err_4224_ = v___x_4233_;
goto v___jp_4221_;
}
else
{
lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4243_; 
lean_inc(v_fst_4219_);
v_isSharedCheck_4243_ = !lean_is_exclusive(v_a_4218_);
if (v_isSharedCheck_4243_ == 0)
{
lean_object* v_unused_4244_; lean_object* v_unused_4245_; 
v_unused_4244_ = lean_ctor_get(v_a_4218_, 1);
lean_dec(v_unused_4244_);
v_unused_4245_ = lean_ctor_get(v_a_4218_, 0);
lean_dec(v_unused_4245_);
v___x_4235_ = v_a_4218_;
v_isShared_4236_ = v_isSharedCheck_4243_;
goto v_resetjp_4234_;
}
else
{
lean_dec(v_a_4218_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4243_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; lean_object* v_it_x27_4239_; 
v___x_4237_ = lean_string_utf8_next_fast(v_fst_4219_, v_snd_4220_);
lean_dec(v_snd_4220_);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 1, v___x_4237_);
v_it_x27_4239_ = v___x_4235_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_fst_4219_);
lean_ctor_set(v_reuseFailAlloc_4242_, 1, v___x_4237_);
v_it_x27_4239_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_string_push(v_acc_4217_, v___x_4230_);
v_acc_4217_ = v___x_4240_;
v_a_4218_ = v_it_x27_4239_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4246_; 
v___x_4246_ = lean_box(0);
lean_inc(v_snd_4220_);
v_pos_4222_ = v_a_4218_;
v_snd_4223_ = v_snd_4220_;
v_err_4224_ = v___x_4246_;
goto v___jp_4221_;
}
v___jp_4221_:
{
uint8_t v_decide_4225_; 
v_decide_4225_ = lean_nat_dec_eq(v_snd_4220_, v_snd_4223_);
lean_dec(v_snd_4223_);
lean_dec(v_snd_4220_);
if (v_decide_4225_ == 0)
{
lean_object* v___x_4226_; 
lean_dec_ref(v_acc_4217_);
lean_inc(v_err_4224_);
v___x_4226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4226_, 0, v_pos_4222_);
lean_ctor_set(v___x_4226_, 1, v_err_4224_);
return v___x_4226_;
}
else
{
lean_object* v___x_4227_; 
v___x_4227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4227_, 0, v_pos_4222_);
lean_ctor_set(v___x_4227_, 1, v_acc_4217_);
return v___x_4227_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0(void){
_start:
{
uint32_t v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4247_ = 98;
v___x_4248_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4249_ = lean_string_push(v___x_4248_, v___x_4247_);
return v___x_4249_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1(void){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4250_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0);
v___x_4251_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4252_ = lean_string_append(v___x_4251_, v___x_4250_);
return v___x_4252_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2(void){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4253_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4254_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1);
v___x_4255_ = lean_string_append(v___x_4254_, v___x_4253_);
return v___x_4255_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3(void){
_start:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4256_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2);
v___x_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(lean_object* v_acc_4258_, lean_object* v_a_4259_){
_start:
{
lean_object* v_fst_4260_; lean_object* v_snd_4261_; lean_object* v_pos_4263_; lean_object* v_snd_4264_; lean_object* v_err_4265_; lean_object* v___x_4269_; uint8_t v_decide_4270_; 
v_fst_4260_ = lean_ctor_get(v_a_4259_, 0);
v_snd_4261_ = lean_ctor_get(v_a_4259_, 1);
lean_inc(v_snd_4261_);
v___x_4269_ = lean_string_utf8_byte_size(v_fst_4260_);
v_decide_4270_ = lean_nat_dec_eq(v_snd_4261_, v___x_4269_);
if (v_decide_4270_ == 0)
{
uint32_t v___x_4271_; uint32_t v_c_4272_; uint8_t v___x_4273_; 
v___x_4271_ = 98;
v_c_4272_ = lean_string_utf8_get_fast(v_fst_4260_, v_snd_4261_);
v___x_4273_ = lean_uint32_dec_eq(v_c_4272_, v___x_4271_);
if (v___x_4273_ == 0)
{
lean_object* v___x_4274_; 
v___x_4274_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3);
lean_inc(v_snd_4261_);
v_pos_4263_ = v_a_4259_;
v_snd_4264_ = v_snd_4261_;
v_err_4265_ = v___x_4274_;
goto v___jp_4262_;
}
else
{
lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4284_; 
lean_inc(v_fst_4260_);
v_isSharedCheck_4284_ = !lean_is_exclusive(v_a_4259_);
if (v_isSharedCheck_4284_ == 0)
{
lean_object* v_unused_4285_; lean_object* v_unused_4286_; 
v_unused_4285_ = lean_ctor_get(v_a_4259_, 1);
lean_dec(v_unused_4285_);
v_unused_4286_ = lean_ctor_get(v_a_4259_, 0);
lean_dec(v_unused_4286_);
v___x_4276_ = v_a_4259_;
v_isShared_4277_ = v_isSharedCheck_4284_;
goto v_resetjp_4275_;
}
else
{
lean_dec(v_a_4259_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4284_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4278_; lean_object* v_it_x27_4280_; 
v___x_4278_ = lean_string_utf8_next_fast(v_fst_4260_, v_snd_4261_);
lean_dec(v_snd_4261_);
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 1, v___x_4278_);
v_it_x27_4280_ = v___x_4276_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_fst_4260_);
lean_ctor_set(v_reuseFailAlloc_4283_, 1, v___x_4278_);
v_it_x27_4280_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
lean_object* v___x_4281_; 
v___x_4281_ = lean_string_push(v_acc_4258_, v___x_4271_);
v_acc_4258_ = v___x_4281_;
v_a_4259_ = v_it_x27_4280_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4287_; 
v___x_4287_ = lean_box(0);
lean_inc(v_snd_4261_);
v_pos_4263_ = v_a_4259_;
v_snd_4264_ = v_snd_4261_;
v_err_4265_ = v___x_4287_;
goto v___jp_4262_;
}
v___jp_4262_:
{
uint8_t v_decide_4266_; 
v_decide_4266_ = lean_nat_dec_eq(v_snd_4261_, v_snd_4264_);
lean_dec(v_snd_4264_);
lean_dec(v_snd_4261_);
if (v_decide_4266_ == 0)
{
lean_object* v___x_4267_; 
lean_dec_ref(v_acc_4258_);
lean_inc(v_err_4265_);
v___x_4267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4267_, 0, v_pos_4263_);
lean_ctor_set(v___x_4267_, 1, v_err_4265_);
return v___x_4267_;
}
else
{
lean_object* v___x_4268_; 
v___x_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4268_, 0, v_pos_4263_);
lean_ctor_set(v___x_4268_, 1, v_acc_4258_);
return v___x_4268_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0(void){
_start:
{
uint32_t v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4288_ = 109;
v___x_4289_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4290_ = lean_string_push(v___x_4289_, v___x_4288_);
return v___x_4290_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1(void){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4291_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0);
v___x_4292_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4293_ = lean_string_append(v___x_4292_, v___x_4291_);
return v___x_4293_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4295_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1);
v___x_4296_ = lean_string_append(v___x_4295_, v___x_4294_);
return v___x_4296_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3(void){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4297_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2);
v___x_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(lean_object* v_acc_4299_, lean_object* v_a_4300_){
_start:
{
lean_object* v_fst_4301_; lean_object* v_snd_4302_; lean_object* v_pos_4304_; lean_object* v_snd_4305_; lean_object* v_err_4306_; lean_object* v___x_4310_; uint8_t v_decide_4311_; 
v_fst_4301_ = lean_ctor_get(v_a_4300_, 0);
v_snd_4302_ = lean_ctor_get(v_a_4300_, 1);
lean_inc(v_snd_4302_);
v___x_4310_ = lean_string_utf8_byte_size(v_fst_4301_);
v_decide_4311_ = lean_nat_dec_eq(v_snd_4302_, v___x_4310_);
if (v_decide_4311_ == 0)
{
uint32_t v___x_4312_; uint32_t v_c_4313_; uint8_t v___x_4314_; 
v___x_4312_ = 109;
v_c_4313_ = lean_string_utf8_get_fast(v_fst_4301_, v_snd_4302_);
v___x_4314_ = lean_uint32_dec_eq(v_c_4313_, v___x_4312_);
if (v___x_4314_ == 0)
{
lean_object* v___x_4315_; 
v___x_4315_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3);
lean_inc(v_snd_4302_);
v_pos_4304_ = v_a_4300_;
v_snd_4305_ = v_snd_4302_;
v_err_4306_ = v___x_4315_;
goto v___jp_4303_;
}
else
{
lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4325_; 
lean_inc(v_fst_4301_);
v_isSharedCheck_4325_ = !lean_is_exclusive(v_a_4300_);
if (v_isSharedCheck_4325_ == 0)
{
lean_object* v_unused_4326_; lean_object* v_unused_4327_; 
v_unused_4326_ = lean_ctor_get(v_a_4300_, 1);
lean_dec(v_unused_4326_);
v_unused_4327_ = lean_ctor_get(v_a_4300_, 0);
lean_dec(v_unused_4327_);
v___x_4317_ = v_a_4300_;
v_isShared_4318_ = v_isSharedCheck_4325_;
goto v_resetjp_4316_;
}
else
{
lean_dec(v_a_4300_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4325_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4319_; lean_object* v_it_x27_4321_; 
v___x_4319_ = lean_string_utf8_next_fast(v_fst_4301_, v_snd_4302_);
lean_dec(v_snd_4302_);
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 1, v___x_4319_);
v_it_x27_4321_ = v___x_4317_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_fst_4301_);
lean_ctor_set(v_reuseFailAlloc_4324_, 1, v___x_4319_);
v_it_x27_4321_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
lean_object* v___x_4322_; 
v___x_4322_ = lean_string_push(v_acc_4299_, v___x_4312_);
v_acc_4299_ = v___x_4322_;
v_a_4300_ = v_it_x27_4321_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4328_; 
v___x_4328_ = lean_box(0);
lean_inc(v_snd_4302_);
v_pos_4304_ = v_a_4300_;
v_snd_4305_ = v_snd_4302_;
v_err_4306_ = v___x_4328_;
goto v___jp_4303_;
}
v___jp_4303_:
{
uint8_t v_decide_4307_; 
v_decide_4307_ = lean_nat_dec_eq(v_snd_4302_, v_snd_4305_);
lean_dec(v_snd_4305_);
lean_dec(v_snd_4302_);
if (v_decide_4307_ == 0)
{
lean_object* v___x_4308_; 
lean_dec_ref(v_acc_4299_);
lean_inc(v_err_4306_);
v___x_4308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4308_, 0, v_pos_4304_);
lean_ctor_set(v___x_4308_, 1, v_err_4306_);
return v___x_4308_;
}
else
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4309_, 0, v_pos_4304_);
lean_ctor_set(v___x_4309_, 1, v_acc_4299_);
return v___x_4309_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0(void){
_start:
{
uint32_t v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4329_ = 117;
v___x_4330_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4331_ = lean_string_push(v___x_4330_, v___x_4329_);
return v___x_4331_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0);
v___x_4333_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4334_ = lean_string_append(v___x_4333_, v___x_4332_);
return v___x_4334_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4335_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4336_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1);
v___x_4337_ = lean_string_append(v___x_4336_, v___x_4335_);
return v___x_4337_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3(void){
_start:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4338_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2);
v___x_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(lean_object* v_acc_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v_fst_4342_; lean_object* v_snd_4343_; lean_object* v_pos_4345_; lean_object* v_snd_4346_; lean_object* v_err_4347_; lean_object* v___x_4351_; uint8_t v_decide_4352_; 
v_fst_4342_ = lean_ctor_get(v_a_4341_, 0);
v_snd_4343_ = lean_ctor_get(v_a_4341_, 1);
lean_inc(v_snd_4343_);
v___x_4351_ = lean_string_utf8_byte_size(v_fst_4342_);
v_decide_4352_ = lean_nat_dec_eq(v_snd_4343_, v___x_4351_);
if (v_decide_4352_ == 0)
{
uint32_t v___x_4353_; uint32_t v_c_4354_; uint8_t v___x_4355_; 
v___x_4353_ = 117;
v_c_4354_ = lean_string_utf8_get_fast(v_fst_4342_, v_snd_4343_);
v___x_4355_ = lean_uint32_dec_eq(v_c_4354_, v___x_4353_);
if (v___x_4355_ == 0)
{
lean_object* v___x_4356_; 
v___x_4356_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3);
lean_inc(v_snd_4343_);
v_pos_4345_ = v_a_4341_;
v_snd_4346_ = v_snd_4343_;
v_err_4347_ = v___x_4356_;
goto v___jp_4344_;
}
else
{
lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4366_; 
lean_inc(v_fst_4342_);
v_isSharedCheck_4366_ = !lean_is_exclusive(v_a_4341_);
if (v_isSharedCheck_4366_ == 0)
{
lean_object* v_unused_4367_; lean_object* v_unused_4368_; 
v_unused_4367_ = lean_ctor_get(v_a_4341_, 1);
lean_dec(v_unused_4367_);
v_unused_4368_ = lean_ctor_get(v_a_4341_, 0);
lean_dec(v_unused_4368_);
v___x_4358_ = v_a_4341_;
v_isShared_4359_ = v_isSharedCheck_4366_;
goto v_resetjp_4357_;
}
else
{
lean_dec(v_a_4341_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4366_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4360_; lean_object* v_it_x27_4362_; 
v___x_4360_ = lean_string_utf8_next_fast(v_fst_4342_, v_snd_4343_);
lean_dec(v_snd_4343_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 1, v___x_4360_);
v_it_x27_4362_ = v___x_4358_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_fst_4342_);
lean_ctor_set(v_reuseFailAlloc_4365_, 1, v___x_4360_);
v_it_x27_4362_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
lean_object* v___x_4363_; 
v___x_4363_ = lean_string_push(v_acc_4340_, v___x_4353_);
v_acc_4340_ = v___x_4363_;
v_a_4341_ = v_it_x27_4362_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4369_; 
v___x_4369_ = lean_box(0);
lean_inc(v_snd_4343_);
v_pos_4345_ = v_a_4341_;
v_snd_4346_ = v_snd_4343_;
v_err_4347_ = v___x_4369_;
goto v___jp_4344_;
}
v___jp_4344_:
{
uint8_t v_decide_4348_; 
v_decide_4348_ = lean_nat_dec_eq(v_snd_4343_, v_snd_4346_);
lean_dec(v_snd_4346_);
lean_dec(v_snd_4343_);
if (v_decide_4348_ == 0)
{
lean_object* v___x_4349_; 
lean_dec_ref(v_acc_4340_);
lean_inc(v_err_4347_);
v___x_4349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4349_, 0, v_pos_4345_);
lean_ctor_set(v___x_4349_, 1, v_err_4347_);
return v___x_4349_;
}
else
{
lean_object* v___x_4350_; 
v___x_4350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4350_, 0, v_pos_4345_);
lean_ctor_set(v___x_4350_, 1, v_acc_4340_);
return v___x_4350_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0(void){
_start:
{
uint32_t v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4370_ = 90;
v___x_4371_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4372_ = lean_string_push(v___x_4371_, v___x_4370_);
return v___x_4372_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4373_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0);
v___x_4374_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4375_ = lean_string_append(v___x_4374_, v___x_4373_);
return v___x_4375_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4376_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4377_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1);
v___x_4378_ = lean_string_append(v___x_4377_, v___x_4376_);
return v___x_4378_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2);
v___x_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(lean_object* v_acc_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v_fst_4383_; lean_object* v_snd_4384_; lean_object* v_pos_4386_; lean_object* v_snd_4387_; lean_object* v_err_4388_; lean_object* v___x_4392_; uint8_t v_decide_4393_; 
v_fst_4383_ = lean_ctor_get(v_a_4382_, 0);
v_snd_4384_ = lean_ctor_get(v_a_4382_, 1);
lean_inc(v_snd_4384_);
v___x_4392_ = lean_string_utf8_byte_size(v_fst_4383_);
v_decide_4393_ = lean_nat_dec_eq(v_snd_4384_, v___x_4392_);
if (v_decide_4393_ == 0)
{
uint32_t v___x_4394_; uint32_t v_c_4395_; uint8_t v___x_4396_; 
v___x_4394_ = 90;
v_c_4395_ = lean_string_utf8_get_fast(v_fst_4383_, v_snd_4384_);
v___x_4396_ = lean_uint32_dec_eq(v_c_4395_, v___x_4394_);
if (v___x_4396_ == 0)
{
lean_object* v___x_4397_; 
v___x_4397_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3);
lean_inc(v_snd_4384_);
v_pos_4386_ = v_a_4382_;
v_snd_4387_ = v_snd_4384_;
v_err_4388_ = v___x_4397_;
goto v___jp_4385_;
}
else
{
lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4407_; 
lean_inc(v_fst_4383_);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_a_4382_);
if (v_isSharedCheck_4407_ == 0)
{
lean_object* v_unused_4408_; lean_object* v_unused_4409_; 
v_unused_4408_ = lean_ctor_get(v_a_4382_, 1);
lean_dec(v_unused_4408_);
v_unused_4409_ = lean_ctor_get(v_a_4382_, 0);
lean_dec(v_unused_4409_);
v___x_4399_ = v_a_4382_;
v_isShared_4400_ = v_isSharedCheck_4407_;
goto v_resetjp_4398_;
}
else
{
lean_dec(v_a_4382_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4407_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4401_; lean_object* v_it_x27_4403_; 
v___x_4401_ = lean_string_utf8_next_fast(v_fst_4383_, v_snd_4384_);
lean_dec(v_snd_4384_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 1, v___x_4401_);
v_it_x27_4403_ = v___x_4399_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_fst_4383_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v___x_4401_);
v_it_x27_4403_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4404_; 
v___x_4404_ = lean_string_push(v_acc_4381_, v___x_4394_);
v_acc_4381_ = v___x_4404_;
v_a_4382_ = v_it_x27_4403_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4410_; 
v___x_4410_ = lean_box(0);
lean_inc(v_snd_4384_);
v_pos_4386_ = v_a_4382_;
v_snd_4387_ = v_snd_4384_;
v_err_4388_ = v___x_4410_;
goto v___jp_4385_;
}
v___jp_4385_:
{
uint8_t v_decide_4389_; 
v_decide_4389_ = lean_nat_dec_eq(v_snd_4384_, v_snd_4387_);
lean_dec(v_snd_4387_);
lean_dec(v_snd_4384_);
if (v_decide_4389_ == 0)
{
lean_object* v___x_4390_; 
lean_dec_ref(v_acc_4381_);
lean_inc(v_err_4388_);
v___x_4390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4390_, 0, v_pos_4386_);
lean_ctor_set(v___x_4390_, 1, v_err_4388_);
return v___x_4390_;
}
else
{
lean_object* v___x_4391_; 
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v_pos_4386_);
lean_ctor_set(v___x_4391_, 1, v_acc_4381_);
return v___x_4391_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0(void){
_start:
{
uint32_t v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4411_ = 78;
v___x_4412_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4413_ = lean_string_push(v___x_4412_, v___x_4411_);
return v___x_4413_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1(void){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0);
v___x_4415_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4416_ = lean_string_append(v___x_4415_, v___x_4414_);
return v___x_4416_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4417_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4418_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1);
v___x_4419_ = lean_string_append(v___x_4418_, v___x_4417_);
return v___x_4419_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3(void){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4420_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2);
v___x_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(lean_object* v_acc_4422_, lean_object* v_a_4423_){
_start:
{
lean_object* v_fst_4424_; lean_object* v_snd_4425_; lean_object* v_pos_4427_; lean_object* v_snd_4428_; lean_object* v_err_4429_; lean_object* v___x_4433_; uint8_t v_decide_4434_; 
v_fst_4424_ = lean_ctor_get(v_a_4423_, 0);
v_snd_4425_ = lean_ctor_get(v_a_4423_, 1);
lean_inc(v_snd_4425_);
v___x_4433_ = lean_string_utf8_byte_size(v_fst_4424_);
v_decide_4434_ = lean_nat_dec_eq(v_snd_4425_, v___x_4433_);
if (v_decide_4434_ == 0)
{
uint32_t v___x_4435_; uint32_t v_c_4436_; uint8_t v___x_4437_; 
v___x_4435_ = 78;
v_c_4436_ = lean_string_utf8_get_fast(v_fst_4424_, v_snd_4425_);
v___x_4437_ = lean_uint32_dec_eq(v_c_4436_, v___x_4435_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4438_; 
v___x_4438_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3);
lean_inc(v_snd_4425_);
v_pos_4427_ = v_a_4423_;
v_snd_4428_ = v_snd_4425_;
v_err_4429_ = v___x_4438_;
goto v___jp_4426_;
}
else
{
lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4448_; 
lean_inc(v_fst_4424_);
v_isSharedCheck_4448_ = !lean_is_exclusive(v_a_4423_);
if (v_isSharedCheck_4448_ == 0)
{
lean_object* v_unused_4449_; lean_object* v_unused_4450_; 
v_unused_4449_ = lean_ctor_get(v_a_4423_, 1);
lean_dec(v_unused_4449_);
v_unused_4450_ = lean_ctor_get(v_a_4423_, 0);
lean_dec(v_unused_4450_);
v___x_4440_ = v_a_4423_;
v_isShared_4441_ = v_isSharedCheck_4448_;
goto v_resetjp_4439_;
}
else
{
lean_dec(v_a_4423_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4448_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4442_; lean_object* v_it_x27_4444_; 
v___x_4442_ = lean_string_utf8_next_fast(v_fst_4424_, v_snd_4425_);
lean_dec(v_snd_4425_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 1, v___x_4442_);
v_it_x27_4444_ = v___x_4440_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_fst_4424_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v___x_4442_);
v_it_x27_4444_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
lean_object* v___x_4445_; 
v___x_4445_ = lean_string_push(v_acc_4422_, v___x_4435_);
v_acc_4422_ = v___x_4445_;
v_a_4423_ = v_it_x27_4444_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4451_; 
v___x_4451_ = lean_box(0);
lean_inc(v_snd_4425_);
v_pos_4427_ = v_a_4423_;
v_snd_4428_ = v_snd_4425_;
v_err_4429_ = v___x_4451_;
goto v___jp_4426_;
}
v___jp_4426_:
{
uint8_t v_decide_4430_; 
v_decide_4430_ = lean_nat_dec_eq(v_snd_4425_, v_snd_4428_);
lean_dec(v_snd_4428_);
lean_dec(v_snd_4425_);
if (v_decide_4430_ == 0)
{
lean_object* v___x_4431_; 
lean_dec_ref(v_acc_4422_);
lean_inc(v_err_4429_);
v___x_4431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4431_, 0, v_pos_4427_);
lean_ctor_set(v___x_4431_, 1, v_err_4429_);
return v___x_4431_;
}
else
{
lean_object* v___x_4432_; 
v___x_4432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4432_, 0, v_pos_4427_);
lean_ctor_set(v___x_4432_, 1, v_acc_4422_);
return v___x_4432_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0(void){
_start:
{
uint32_t v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = 70;
v___x_4453_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4454_ = lean_string_push(v___x_4453_, v___x_4452_);
return v___x_4454_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1(void){
_start:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0);
v___x_4456_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4457_ = lean_string_append(v___x_4456_, v___x_4455_);
return v___x_4457_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2(void){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4458_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4459_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1);
v___x_4460_ = lean_string_append(v___x_4459_, v___x_4458_);
return v___x_4460_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3(void){
_start:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4461_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2);
v___x_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(lean_object* v_acc_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v_fst_4465_; lean_object* v_snd_4466_; lean_object* v_pos_4468_; lean_object* v_snd_4469_; lean_object* v_err_4470_; lean_object* v___x_4474_; uint8_t v_decide_4475_; 
v_fst_4465_ = lean_ctor_get(v_a_4464_, 0);
v_snd_4466_ = lean_ctor_get(v_a_4464_, 1);
lean_inc(v_snd_4466_);
v___x_4474_ = lean_string_utf8_byte_size(v_fst_4465_);
v_decide_4475_ = lean_nat_dec_eq(v_snd_4466_, v___x_4474_);
if (v_decide_4475_ == 0)
{
uint32_t v___x_4476_; uint32_t v_c_4477_; uint8_t v___x_4478_; 
v___x_4476_ = 70;
v_c_4477_ = lean_string_utf8_get_fast(v_fst_4465_, v_snd_4466_);
v___x_4478_ = lean_uint32_dec_eq(v_c_4477_, v___x_4476_);
if (v___x_4478_ == 0)
{
lean_object* v___x_4479_; 
v___x_4479_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3);
lean_inc(v_snd_4466_);
v_pos_4468_ = v_a_4464_;
v_snd_4469_ = v_snd_4466_;
v_err_4470_ = v___x_4479_;
goto v___jp_4467_;
}
else
{
lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4489_; 
lean_inc(v_fst_4465_);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_a_4464_);
if (v_isSharedCheck_4489_ == 0)
{
lean_object* v_unused_4490_; lean_object* v_unused_4491_; 
v_unused_4490_ = lean_ctor_get(v_a_4464_, 1);
lean_dec(v_unused_4490_);
v_unused_4491_ = lean_ctor_get(v_a_4464_, 0);
lean_dec(v_unused_4491_);
v___x_4481_ = v_a_4464_;
v_isShared_4482_ = v_isSharedCheck_4489_;
goto v_resetjp_4480_;
}
else
{
lean_dec(v_a_4464_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4489_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4483_; lean_object* v_it_x27_4485_; 
v___x_4483_ = lean_string_utf8_next_fast(v_fst_4465_, v_snd_4466_);
lean_dec(v_snd_4466_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 1, v___x_4483_);
v_it_x27_4485_ = v___x_4481_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_fst_4465_);
lean_ctor_set(v_reuseFailAlloc_4488_, 1, v___x_4483_);
v_it_x27_4485_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
lean_object* v___x_4486_; 
v___x_4486_ = lean_string_push(v_acc_4463_, v___x_4476_);
v_acc_4463_ = v___x_4486_;
v_a_4464_ = v_it_x27_4485_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4492_; 
v___x_4492_ = lean_box(0);
lean_inc(v_snd_4466_);
v_pos_4468_ = v_a_4464_;
v_snd_4469_ = v_snd_4466_;
v_err_4470_ = v___x_4492_;
goto v___jp_4467_;
}
v___jp_4467_:
{
uint8_t v_decide_4471_; 
v_decide_4471_ = lean_nat_dec_eq(v_snd_4466_, v_snd_4469_);
lean_dec(v_snd_4469_);
lean_dec(v_snd_4466_);
if (v_decide_4471_ == 0)
{
lean_object* v___x_4472_; 
lean_dec_ref(v_acc_4463_);
lean_inc(v_err_4470_);
v___x_4472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4472_, 0, v_pos_4468_);
lean_ctor_set(v___x_4472_, 1, v_err_4470_);
return v___x_4472_;
}
else
{
lean_object* v___x_4473_; 
v___x_4473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4473_, 0, v_pos_4468_);
lean_ctor_set(v___x_4473_, 1, v_acc_4463_);
return v___x_4473_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0(void){
_start:
{
uint32_t v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4493_ = 66;
v___x_4494_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4495_ = lean_string_push(v___x_4494_, v___x_4493_);
return v___x_4495_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1(void){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4496_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0);
v___x_4497_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4498_ = lean_string_append(v___x_4497_, v___x_4496_);
return v___x_4498_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2(void){
_start:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4499_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4500_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1);
v___x_4501_ = lean_string_append(v___x_4500_, v___x_4499_);
return v___x_4501_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3(void){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2);
v___x_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(lean_object* v_acc_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v_fst_4506_; lean_object* v_snd_4507_; lean_object* v_pos_4509_; lean_object* v_snd_4510_; lean_object* v_err_4511_; lean_object* v___x_4515_; uint8_t v_decide_4516_; 
v_fst_4506_ = lean_ctor_get(v_a_4505_, 0);
v_snd_4507_ = lean_ctor_get(v_a_4505_, 1);
lean_inc(v_snd_4507_);
v___x_4515_ = lean_string_utf8_byte_size(v_fst_4506_);
v_decide_4516_ = lean_nat_dec_eq(v_snd_4507_, v___x_4515_);
if (v_decide_4516_ == 0)
{
uint32_t v___x_4517_; uint32_t v_c_4518_; uint8_t v___x_4519_; 
v___x_4517_ = 66;
v_c_4518_ = lean_string_utf8_get_fast(v_fst_4506_, v_snd_4507_);
v___x_4519_ = lean_uint32_dec_eq(v_c_4518_, v___x_4517_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; 
v___x_4520_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3);
lean_inc(v_snd_4507_);
v_pos_4509_ = v_a_4505_;
v_snd_4510_ = v_snd_4507_;
v_err_4511_ = v___x_4520_;
goto v___jp_4508_;
}
else
{
lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4530_; 
lean_inc(v_fst_4506_);
v_isSharedCheck_4530_ = !lean_is_exclusive(v_a_4505_);
if (v_isSharedCheck_4530_ == 0)
{
lean_object* v_unused_4531_; lean_object* v_unused_4532_; 
v_unused_4531_ = lean_ctor_get(v_a_4505_, 1);
lean_dec(v_unused_4531_);
v_unused_4532_ = lean_ctor_get(v_a_4505_, 0);
lean_dec(v_unused_4532_);
v___x_4522_ = v_a_4505_;
v_isShared_4523_ = v_isSharedCheck_4530_;
goto v_resetjp_4521_;
}
else
{
lean_dec(v_a_4505_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4530_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4524_; lean_object* v_it_x27_4526_; 
v___x_4524_ = lean_string_utf8_next_fast(v_fst_4506_, v_snd_4507_);
lean_dec(v_snd_4507_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 1, v___x_4524_);
v_it_x27_4526_ = v___x_4522_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_fst_4506_);
lean_ctor_set(v_reuseFailAlloc_4529_, 1, v___x_4524_);
v_it_x27_4526_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
lean_object* v___x_4527_; 
v___x_4527_ = lean_string_push(v_acc_4504_, v___x_4517_);
v_acc_4504_ = v___x_4527_;
v_a_4505_ = v_it_x27_4526_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4533_; 
v___x_4533_ = lean_box(0);
lean_inc(v_snd_4507_);
v_pos_4509_ = v_a_4505_;
v_snd_4510_ = v_snd_4507_;
v_err_4511_ = v___x_4533_;
goto v___jp_4508_;
}
v___jp_4508_:
{
uint8_t v_decide_4512_; 
v_decide_4512_ = lean_nat_dec_eq(v_snd_4507_, v_snd_4510_);
lean_dec(v_snd_4510_);
lean_dec(v_snd_4507_);
if (v_decide_4512_ == 0)
{
lean_object* v___x_4513_; 
lean_dec_ref(v_acc_4504_);
lean_inc(v_err_4511_);
v___x_4513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4513_, 0, v_pos_4509_);
lean_ctor_set(v___x_4513_, 1, v_err_4511_);
return v___x_4513_;
}
else
{
lean_object* v___x_4514_; 
v___x_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4514_, 0, v_pos_4509_);
lean_ctor_set(v___x_4514_, 1, v_acc_4504_);
return v___x_4514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier(lean_object* v_a_4571_){
_start:
{
lean_object* v___y_4573_; lean_object* v_fst_4576_; lean_object* v_snd_4577_; lean_object* v___f_4578_; lean_object* v_snd_4580_; lean_object* v___y_4581_; lean_object* v_pos_4582_; lean_object* v_snd_4618_; lean_object* v_pos_4619_; lean_object* v_err_4620_; lean_object* v___y_4623_; lean_object* v_snd_4624_; lean_object* v___f_4626_; lean_object* v_snd_4628_; lean_object* v___y_4629_; lean_object* v_pos_4630_; lean_object* v_snd_4659_; lean_object* v_pos_4660_; lean_object* v_err_4661_; lean_object* v___y_4664_; lean_object* v_snd_4665_; lean_object* v___f_4667_; lean_object* v_snd_4669_; lean_object* v___y_4670_; lean_object* v_pos_4671_; lean_object* v_snd_4700_; lean_object* v_pos_4701_; lean_object* v_err_4702_; lean_object* v___y_4705_; lean_object* v_snd_4706_; lean_object* v___f_4708_; lean_object* v_snd_4710_; lean_object* v___y_4711_; lean_object* v_pos_4712_; lean_object* v_snd_4741_; lean_object* v_pos_4742_; lean_object* v_err_4743_; lean_object* v___y_4746_; lean_object* v_snd_4747_; lean_object* v___f_4749_; lean_object* v_snd_4751_; lean_object* v___y_4752_; lean_object* v_pos_4753_; lean_object* v_snd_4782_; lean_object* v_pos_4783_; lean_object* v_err_4784_; lean_object* v___y_4787_; lean_object* v_snd_4788_; lean_object* v___f_4790_; lean_object* v_snd_4792_; lean_object* v___y_4793_; lean_object* v_pos_4794_; lean_object* v_snd_4823_; lean_object* v_pos_4824_; lean_object* v_err_4825_; lean_object* v___y_4828_; lean_object* v_snd_4829_; lean_object* v_snd_4832_; lean_object* v___y_4833_; lean_object* v_pos_4834_; lean_object* v_snd_4863_; lean_object* v_pos_4864_; lean_object* v_err_4865_; lean_object* v___y_4868_; lean_object* v_snd_4869_; lean_object* v___f_4871_; lean_object* v_snd_4873_; lean_object* v___y_4874_; lean_object* v_pos_4875_; lean_object* v_snd_4903_; lean_object* v_pos_4904_; lean_object* v_err_4905_; lean_object* v___y_4908_; lean_object* v_snd_4909_; lean_object* v___f_4911_; lean_object* v_snd_4913_; lean_object* v___y_4914_; lean_object* v_pos_4915_; lean_object* v_snd_4943_; lean_object* v_pos_4944_; lean_object* v_err_4945_; lean_object* v___y_4948_; lean_object* v_snd_4949_; lean_object* v___f_4951_; lean_object* v_snd_4953_; lean_object* v___y_4954_; lean_object* v_pos_4955_; lean_object* v_snd_4983_; lean_object* v_pos_4984_; lean_object* v_err_4985_; lean_object* v___y_4988_; lean_object* v_snd_4989_; lean_object* v___f_4991_; lean_object* v_snd_4993_; lean_object* v___y_4994_; lean_object* v_pos_4995_; lean_object* v_snd_5024_; lean_object* v_pos_5025_; lean_object* v_err_5026_; lean_object* v___y_5029_; lean_object* v_snd_5030_; lean_object* v___f_5032_; lean_object* v_snd_5034_; lean_object* v___y_5035_; lean_object* v___y_5036_; lean_object* v_pos_5037_; lean_object* v_snd_5066_; lean_object* v___y_5067_; lean_object* v_pos_5068_; lean_object* v_err_5069_; lean_object* v___y_5072_; lean_object* v_snd_5073_; lean_object* v___y_5074_; lean_object* v___f_5076_; lean_object* v_snd_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v_pos_5081_; lean_object* v_snd_5110_; lean_object* v___y_5111_; lean_object* v_pos_5112_; lean_object* v_err_5113_; lean_object* v___y_5116_; lean_object* v_snd_5117_; lean_object* v___y_5118_; lean_object* v___f_5120_; lean_object* v___y_5122_; lean_object* v_snd_5123_; lean_object* v___y_5124_; lean_object* v_pos_5125_; lean_object* v___y_5154_; lean_object* v_snd_5155_; lean_object* v_pos_5156_; lean_object* v_err_5157_; lean_object* v___y_5160_; lean_object* v___y_5161_; lean_object* v_snd_5162_; lean_object* v___f_5164_; lean_object* v_snd_5166_; lean_object* v___y_5167_; lean_object* v___y_5168_; lean_object* v_pos_5169_; lean_object* v_snd_5198_; lean_object* v___y_5199_; lean_object* v_pos_5200_; lean_object* v_err_5201_; lean_object* v___y_5204_; lean_object* v_snd_5205_; lean_object* v___y_5206_; lean_object* v___f_5208_; lean_object* v_snd_5210_; lean_object* v___y_5211_; lean_object* v___y_5212_; lean_object* v_pos_5213_; lean_object* v_snd_5242_; lean_object* v___y_5243_; lean_object* v_pos_5244_; lean_object* v_err_5245_; lean_object* v___y_5248_; lean_object* v_snd_5249_; lean_object* v___y_5250_; lean_object* v___f_5252_; lean_object* v_snd_5254_; lean_object* v___y_5255_; lean_object* v___y_5256_; lean_object* v_pos_5257_; lean_object* v_snd_5286_; lean_object* v___y_5287_; lean_object* v_pos_5288_; lean_object* v_err_5289_; lean_object* v___y_5292_; lean_object* v_snd_5293_; lean_object* v___y_5294_; lean_object* v_snd_5297_; lean_object* v___y_5298_; lean_object* v___y_5299_; lean_object* v_pos_5300_; lean_object* v_snd_5329_; lean_object* v___y_5330_; lean_object* v_pos_5331_; lean_object* v_err_5332_; lean_object* v___y_5335_; lean_object* v_snd_5336_; lean_object* v___y_5337_; lean_object* v_snd_5340_; lean_object* v___y_5341_; lean_object* v___y_5342_; lean_object* v_pos_5343_; lean_object* v_snd_5372_; lean_object* v___y_5373_; lean_object* v_pos_5374_; lean_object* v_err_5375_; lean_object* v___y_5378_; lean_object* v_snd_5379_; lean_object* v___y_5380_; lean_object* v___y_5383_; lean_object* v_snd_5384_; lean_object* v___y_5385_; lean_object* v_pos_5386_; lean_object* v___y_5415_; lean_object* v_snd_5416_; lean_object* v_pos_5417_; lean_object* v_err_5418_; lean_object* v___y_5421_; lean_object* v___y_5422_; lean_object* v_snd_5423_; lean_object* v___f_5425_; lean_object* v___y_5427_; lean_object* v_snd_5428_; lean_object* v___y_5429_; lean_object* v___y_5430_; lean_object* v_pos_5431_; lean_object* v___y_5460_; lean_object* v_snd_5461_; lean_object* v___y_5462_; lean_object* v_pos_5463_; lean_object* v_err_5464_; lean_object* v___y_5467_; lean_object* v___y_5468_; lean_object* v_snd_5469_; lean_object* v___y_5470_; lean_object* v___f_5472_; lean_object* v___y_5474_; lean_object* v_snd_5475_; lean_object* v___y_5476_; lean_object* v___y_5477_; lean_object* v_pos_5478_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v_snd_5509_; lean_object* v_pos_5510_; lean_object* v_err_5511_; lean_object* v___y_5514_; lean_object* v___y_5515_; lean_object* v___y_5516_; lean_object* v_snd_5517_; lean_object* v___f_5519_; lean_object* v___y_5521_; lean_object* v_snd_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v_pos_5525_; lean_object* v___y_5554_; lean_object* v_snd_5555_; lean_object* v___y_5556_; lean_object* v_pos_5557_; lean_object* v_err_5558_; lean_object* v___y_5561_; lean_object* v___y_5562_; lean_object* v_snd_5563_; lean_object* v___y_5564_; lean_object* v___f_5566_; lean_object* v___y_5568_; lean_object* v___y_5569_; lean_object* v___y_5570_; lean_object* v___y_5571_; lean_object* v_pos_5572_; lean_object* v___y_5601_; lean_object* v___y_5602_; lean_object* v___y_5603_; lean_object* v_pos_5604_; lean_object* v_err_5605_; lean_object* v___y_5608_; lean_object* v___y_5609_; lean_object* v___y_5610_; lean_object* v___y_5611_; lean_object* v___f_5613_; lean_object* v___y_5615_; lean_object* v_snd_5616_; lean_object* v___y_5617_; lean_object* v_pos_5618_; lean_object* v___y_5648_; lean_object* v_snd_5649_; lean_object* v_pos_5650_; lean_object* v_err_5651_; lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v_snd_5656_; lean_object* v___f_5658_; lean_object* v___y_5660_; lean_object* v_snd_5661_; lean_object* v___y_5662_; lean_object* v_pos_5663_; lean_object* v___y_5692_; lean_object* v_snd_5693_; lean_object* v_pos_5694_; lean_object* v_err_5695_; lean_object* v___y_5698_; lean_object* v___y_5699_; lean_object* v_snd_5700_; lean_object* v___f_5702_; lean_object* v_snd_5704_; lean_object* v___y_5705_; lean_object* v___y_5706_; lean_object* v_pos_5707_; lean_object* v_snd_5736_; lean_object* v___y_5737_; lean_object* v_pos_5738_; lean_object* v_err_5739_; lean_object* v___y_5742_; lean_object* v_snd_5743_; lean_object* v___y_5744_; lean_object* v___f_5746_; lean_object* v___y_5748_; lean_object* v___y_5749_; lean_object* v___y_5750_; lean_object* v_pos_5751_; lean_object* v___y_5780_; lean_object* v___y_5781_; lean_object* v_pos_5782_; lean_object* v_err_5783_; lean_object* v___y_5786_; lean_object* v___y_5787_; lean_object* v___y_5788_; lean_object* v___f_5790_; lean_object* v_snd_5792_; lean_object* v___y_5793_; lean_object* v_pos_5794_; lean_object* v_snd_5824_; lean_object* v_pos_5825_; lean_object* v_err_5826_; lean_object* v___y_5829_; lean_object* v_snd_5830_; lean_object* v___f_5832_; lean_object* v_snd_5834_; lean_object* v___y_5835_; lean_object* v_pos_5836_; lean_object* v_snd_5865_; lean_object* v_pos_5866_; lean_object* v_err_5867_; lean_object* v___y_5870_; lean_object* v_snd_5871_; lean_object* v___f_5873_; lean_object* v_snd_5875_; lean_object* v___y_5876_; lean_object* v_pos_5877_; lean_object* v_snd_5906_; lean_object* v_pos_5907_; lean_object* v_err_5908_; lean_object* v___y_5911_; lean_object* v_snd_5912_; lean_object* v___f_5914_; lean_object* v_snd_5916_; lean_object* v___y_5917_; lean_object* v_pos_5918_; lean_object* v_snd_5948_; lean_object* v_pos_5949_; lean_object* v_err_5950_; lean_object* v___y_5953_; lean_object* v_snd_5954_; lean_object* v___f_5956_; lean_object* v_snd_5958_; lean_object* v___y_5959_; lean_object* v_pos_5960_; lean_object* v_snd_5989_; lean_object* v_pos_5990_; lean_object* v_err_5991_; lean_object* v___y_5994_; lean_object* v_snd_5995_; lean_object* v___f_5997_; lean_object* v_snd_5999_; lean_object* v___y_6000_; lean_object* v_pos_6001_; lean_object* v_snd_6030_; lean_object* v_pos_6031_; lean_object* v_err_6032_; lean_object* v___y_6035_; lean_object* v_snd_6036_; lean_object* v___f_6038_; lean_object* v___y_6040_; lean_object* v_pos_6041_; lean_object* v_pos_6070_; lean_object* v_err_6071_; lean_object* v___x_6073_; uint8_t v_decide_6074_; 
v_fst_4576_ = lean_ctor_get(v_a_4571_, 0);
v_snd_4577_ = lean_ctor_get(v_a_4571_, 1);
lean_inc(v_snd_4577_);
v___f_4578_ = ((lean_object*)(l_Std_Time_parseModifier___closed__0));
v___f_4626_ = ((lean_object*)(l_Std_Time_parseModifier___closed__1));
v___f_4667_ = ((lean_object*)(l_Std_Time_parseModifier___closed__2));
v___f_4708_ = ((lean_object*)(l_Std_Time_parseModifier___closed__3));
v___f_4749_ = ((lean_object*)(l_Std_Time_parseModifier___closed__4));
v___f_4790_ = ((lean_object*)(l_Std_Time_parseModifier___closed__5));
v___f_4871_ = ((lean_object*)(l_Std_Time_parseModifier___closed__6));
v___f_4911_ = ((lean_object*)(l_Std_Time_parseModifier___closed__7));
v___f_4951_ = ((lean_object*)(l_Std_Time_parseModifier___closed__8));
v___f_4991_ = ((lean_object*)(l_Std_Time_parseModifier___closed__9));
v___f_5032_ = ((lean_object*)(l_Std_Time_parseModifier___closed__10));
v___f_5076_ = ((lean_object*)(l_Std_Time_parseModifier___closed__11));
v___f_5120_ = ((lean_object*)(l_Std_Time_parseModifier___closed__12));
v___f_5164_ = ((lean_object*)(l_Std_Time_parseModifier___closed__13));
v___f_5208_ = ((lean_object*)(l_Std_Time_parseModifier___closed__14));
v___f_5252_ = ((lean_object*)(l_Std_Time_parseModifier___closed__15));
v___f_5425_ = ((lean_object*)(l_Std_Time_parseModifier___closed__16));
v___f_5472_ = ((lean_object*)(l_Std_Time_parseModifier___closed__17));
v___f_5519_ = ((lean_object*)(l_Std_Time_parseModifier___closed__18));
v___f_5566_ = ((lean_object*)(l_Std_Time_parseModifier___closed__19));
v___f_5613_ = ((lean_object*)(l_Std_Time_parseModifier___closed__20));
v___f_5658_ = ((lean_object*)(l_Std_Time_parseModifier___closed__22));
v___f_5702_ = ((lean_object*)(l_Std_Time_parseModifier___closed__23));
v___f_5746_ = ((lean_object*)(l_Std_Time_parseModifier___closed__24));
v___f_5790_ = ((lean_object*)(l_Std_Time_parseModifier___closed__25));
v___f_5832_ = ((lean_object*)(l_Std_Time_parseModifier___closed__27));
v___f_5873_ = ((lean_object*)(l_Std_Time_parseModifier___closed__28));
v___f_5914_ = ((lean_object*)(l_Std_Time_parseModifier___closed__29));
v___f_5956_ = ((lean_object*)(l_Std_Time_parseModifier___closed__31));
v___f_5997_ = ((lean_object*)(l_Std_Time_parseModifier___closed__32));
v___f_6038_ = ((lean_object*)(l_Std_Time_parseModifier___closed__33));
v___x_6073_ = lean_string_utf8_byte_size(v_fst_4576_);
v_decide_6074_ = lean_nat_dec_eq(v_snd_4577_, v___x_6073_);
if (v_decide_6074_ == 0)
{
uint32_t v___x_6075_; uint32_t v_c_6076_; uint8_t v___x_6077_; 
v___x_6075_ = 71;
v_c_6076_ = lean_string_utf8_get_fast(v_fst_4576_, v_snd_4577_);
v___x_6077_ = lean_uint32_dec_eq(v_c_6076_, v___x_6075_);
if (v___x_6077_ == 0)
{
lean_object* v___x_6078_; 
v___x_6078_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3);
v_pos_6070_ = v_a_4571_;
v_err_6071_ = v___x_6078_;
goto v___jp_6069_;
}
else
{
lean_object* v___x_6080_; uint8_t v_isShared_6081_; uint8_t v_isSharedCheck_6095_; 
lean_inc(v_fst_4576_);
v_isSharedCheck_6095_ = !lean_is_exclusive(v_a_4571_);
if (v_isSharedCheck_6095_ == 0)
{
lean_object* v_unused_6096_; lean_object* v_unused_6097_; 
v_unused_6096_ = lean_ctor_get(v_a_4571_, 1);
lean_dec(v_unused_6096_);
v_unused_6097_ = lean_ctor_get(v_a_4571_, 0);
lean_dec(v_unused_6097_);
v___x_6080_ = v_a_4571_;
v_isShared_6081_ = v_isSharedCheck_6095_;
goto v_resetjp_6079_;
}
else
{
lean_dec(v_a_4571_);
v___x_6080_ = lean_box(0);
v_isShared_6081_ = v_isSharedCheck_6095_;
goto v_resetjp_6079_;
}
v_resetjp_6079_:
{
lean_object* v___x_6082_; lean_object* v_it_x27_6084_; 
v___x_6082_ = lean_string_utf8_next_fast(v_fst_4576_, v_snd_4577_);
if (v_isShared_6081_ == 0)
{
lean_ctor_set(v___x_6080_, 1, v___x_6082_);
v_it_x27_6084_ = v___x_6080_;
goto v_reusejp_6083_;
}
else
{
lean_object* v_reuseFailAlloc_6094_; 
v_reuseFailAlloc_6094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6094_, 0, v_fst_4576_);
lean_ctor_set(v_reuseFailAlloc_6094_, 1, v___x_6082_);
v_it_x27_6084_ = v_reuseFailAlloc_6094_;
goto v_reusejp_6083_;
}
v_reusejp_6083_:
{
lean_object* v___x_6085_; lean_object* v___x_6086_; 
v___x_6085_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0);
v___x_6086_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(v___x_6085_, v_it_x27_6084_);
if (lean_obj_tag(v___x_6086_) == 0)
{
lean_object* v_pos_6087_; lean_object* v_res_6088_; lean_object* v___f_6089_; lean_object* v___x_6090_; 
v_pos_6087_ = lean_ctor_get(v___x_6086_, 0);
lean_inc(v_pos_6087_);
v_res_6088_ = lean_ctor_get(v___x_6086_, 1);
lean_inc(v_res_6088_);
lean_dec_ref_known(v___x_6086_, 2);
v___f_6089_ = ((lean_object*)(l_Std_Time_parseModifier___closed__34));
v___x_6090_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_6089_, v_res_6088_, v_pos_6087_);
if (lean_obj_tag(v___x_6090_) == 0)
{
lean_dec(v_snd_4577_);
return v___x_6090_;
}
else
{
lean_object* v_pos_6091_; 
v_pos_6091_ = lean_ctor_get(v___x_6090_, 0);
lean_inc(v_pos_6091_);
v___y_6040_ = v___x_6090_;
v_pos_6041_ = v_pos_6091_;
goto v___jp_6039_;
}
}
else
{
lean_object* v_pos_6092_; lean_object* v_err_6093_; 
v_pos_6092_ = lean_ctor_get(v___x_6086_, 0);
lean_inc(v_pos_6092_);
v_err_6093_ = lean_ctor_get(v___x_6086_, 1);
lean_inc(v_err_6093_);
lean_dec_ref_known(v___x_6086_, 2);
v_pos_6070_ = v_pos_6092_;
v_err_6071_ = v_err_6093_;
goto v___jp_6069_;
}
}
}
}
}
else
{
lean_object* v___x_6098_; 
v___x_6098_ = lean_box(0);
v_pos_6070_ = v_a_4571_;
v_err_6071_ = v___x_6098_;
goto v___jp_6069_;
}
v___jp_4572_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4574_ = lean_box(0);
v___x_4575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___y_4573_);
lean_ctor_set(v___x_4575_, 1, v___x_4574_);
return v___x_4575_;
}
v___jp_4579_:
{
lean_object* v_fst_4583_; lean_object* v_snd_4584_; uint8_t v_decide_4585_; 
v_fst_4583_ = lean_ctor_get(v_pos_4582_, 0);
v_snd_4584_ = lean_ctor_get(v_pos_4582_, 1);
v_decide_4585_ = lean_nat_dec_eq(v_snd_4580_, v_snd_4584_);
lean_dec(v_snd_4580_);
if (v_decide_4585_ == 0)
{
lean_dec_ref(v_pos_4582_);
return v___y_4581_;
}
else
{
lean_object* v___x_4586_; uint8_t v_decide_4587_; 
lean_dec_ref(v___y_4581_);
v___x_4586_ = lean_string_utf8_byte_size(v_fst_4583_);
v_decide_4587_ = lean_nat_dec_eq(v_snd_4584_, v___x_4586_);
if (v_decide_4587_ == 0)
{
if (v_decide_4585_ == 0)
{
v___y_4573_ = v_pos_4582_;
goto v___jp_4572_;
}
else
{
uint32_t v___x_4588_; uint32_t v_c_4589_; uint8_t v___x_4590_; 
v___x_4588_ = 90;
v_c_4589_ = lean_string_utf8_get_fast(v_fst_4583_, v_snd_4584_);
v___x_4590_ = lean_uint32_dec_eq(v_c_4589_, v___x_4588_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4591_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3);
v___x_4592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4592_, 0, v_pos_4582_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
return v___x_4592_;
}
else
{
lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4614_; 
lean_inc(v_snd_4584_);
lean_inc(v_fst_4583_);
v_isSharedCheck_4614_ = !lean_is_exclusive(v_pos_4582_);
if (v_isSharedCheck_4614_ == 0)
{
lean_object* v_unused_4615_; lean_object* v_unused_4616_; 
v_unused_4615_ = lean_ctor_get(v_pos_4582_, 1);
lean_dec(v_unused_4615_);
v_unused_4616_ = lean_ctor_get(v_pos_4582_, 0);
lean_dec(v_unused_4616_);
v___x_4594_ = v_pos_4582_;
v_isShared_4595_ = v_isSharedCheck_4614_;
goto v_resetjp_4593_;
}
else
{
lean_dec(v_pos_4582_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4614_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4596_; lean_object* v_it_x27_4598_; 
v___x_4596_ = lean_string_utf8_next_fast(v_fst_4583_, v_snd_4584_);
lean_dec(v_snd_4584_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 1, v___x_4596_);
v_it_x27_4598_ = v___x_4594_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_fst_4583_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v___x_4596_);
v_it_x27_4598_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0);
v___x_4600_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(v___x_4599_, v_it_x27_4598_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_object* v_pos_4601_; lean_object* v_res_4602_; lean_object* v___x_4603_; 
v_pos_4601_ = lean_ctor_get(v___x_4600_, 0);
lean_inc(v_pos_4601_);
v_res_4602_ = lean_ctor_get(v___x_4600_, 1);
lean_inc(v_res_4602_);
lean_dec_ref_known(v___x_4600_, 2);
v___x_4603_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(v___f_4578_, v_res_4602_, v_pos_4601_);
return v___x_4603_;
}
else
{
lean_object* v_pos_4604_; lean_object* v_err_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
v_pos_4604_ = lean_ctor_get(v___x_4600_, 0);
v_err_4605_ = lean_ctor_get(v___x_4600_, 1);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4600_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4600_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_err_4605_);
lean_inc(v_pos_4604_);
lean_dec(v___x_4600_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_pos_4604_);
lean_ctor_set(v_reuseFailAlloc_4611_, 1, v_err_4605_);
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
}
}
}
else
{
v___y_4573_ = v_pos_4582_;
goto v___jp_4572_;
}
}
}
v___jp_4617_:
{
lean_object* v___x_4621_; 
lean_inc_ref(v_pos_4619_);
v___x_4621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4621_, 0, v_pos_4619_);
lean_ctor_set(v___x_4621_, 1, v_err_4620_);
v_snd_4580_ = v_snd_4618_;
v___y_4581_ = v___x_4621_;
v_pos_4582_ = v_pos_4619_;
goto v___jp_4579_;
}
v___jp_4622_:
{
lean_object* v___x_4625_; 
v___x_4625_ = lean_box(0);
v_snd_4618_ = v_snd_4624_;
v_pos_4619_ = v___y_4623_;
v_err_4620_ = v___x_4625_;
goto v___jp_4617_;
}
v___jp_4627_:
{
lean_object* v_fst_4631_; lean_object* v_snd_4632_; uint8_t v_decide_4633_; 
v_fst_4631_ = lean_ctor_get(v_pos_4630_, 0);
v_snd_4632_ = lean_ctor_get(v_pos_4630_, 1);
lean_inc(v_snd_4632_);
v_decide_4633_ = lean_nat_dec_eq(v_snd_4628_, v_snd_4632_);
lean_dec(v_snd_4628_);
if (v_decide_4633_ == 0)
{
lean_dec(v_snd_4632_);
lean_dec_ref(v_pos_4630_);
return v___y_4629_;
}
else
{
lean_object* v___x_4634_; uint8_t v_decide_4635_; 
lean_dec_ref(v___y_4629_);
v___x_4634_ = lean_string_utf8_byte_size(v_fst_4631_);
v_decide_4635_ = lean_nat_dec_eq(v_snd_4632_, v___x_4634_);
if (v_decide_4635_ == 0)
{
if (v_decide_4633_ == 0)
{
v___y_4623_ = v_pos_4630_;
v_snd_4624_ = v_snd_4632_;
goto v___jp_4622_;
}
else
{
uint32_t v___x_4636_; uint32_t v_c_4637_; uint8_t v___x_4638_; 
v___x_4636_ = 120;
v_c_4637_ = lean_string_utf8_get_fast(v_fst_4631_, v_snd_4632_);
v___x_4638_ = lean_uint32_dec_eq(v_c_4637_, v___x_4636_);
if (v___x_4638_ == 0)
{
lean_object* v___x_4639_; 
v___x_4639_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4);
v_snd_4618_ = v_snd_4632_;
v_pos_4619_ = v_pos_4630_;
v_err_4620_ = v___x_4639_;
goto v___jp_4617_;
}
else
{
lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4655_; 
lean_inc(v_fst_4631_);
v_isSharedCheck_4655_ = !lean_is_exclusive(v_pos_4630_);
if (v_isSharedCheck_4655_ == 0)
{
lean_object* v_unused_4656_; lean_object* v_unused_4657_; 
v_unused_4656_ = lean_ctor_get(v_pos_4630_, 1);
lean_dec(v_unused_4656_);
v_unused_4657_ = lean_ctor_get(v_pos_4630_, 0);
lean_dec(v_unused_4657_);
v___x_4641_ = v_pos_4630_;
v_isShared_4642_ = v_isSharedCheck_4655_;
goto v_resetjp_4640_;
}
else
{
lean_dec(v_pos_4630_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4655_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4643_; lean_object* v_it_x27_4645_; 
v___x_4643_ = lean_string_utf8_next_fast(v_fst_4631_, v_snd_4632_);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 1, v___x_4643_);
v_it_x27_4645_ = v___x_4641_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_fst_4631_);
lean_ctor_set(v_reuseFailAlloc_4654_, 1, v___x_4643_);
v_it_x27_4645_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1);
v___x_4647_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(v___x_4646_, v_it_x27_4645_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_pos_4648_; lean_object* v_res_4649_; lean_object* v___x_4650_; 
v_pos_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_pos_4648_);
v_res_4649_ = lean_ctor_get(v___x_4647_, 1);
lean_inc(v_res_4649_);
lean_dec_ref_known(v___x_4647_, 2);
v___x_4650_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4626_, v_res_4649_, v_pos_4648_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_dec(v_snd_4632_);
return v___x_4650_;
}
else
{
lean_object* v_pos_4651_; 
v_pos_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_pos_4651_);
v_snd_4580_ = v_snd_4632_;
v___y_4581_ = v___x_4650_;
v_pos_4582_ = v_pos_4651_;
goto v___jp_4579_;
}
}
else
{
lean_object* v_pos_4652_; lean_object* v_err_4653_; 
v_pos_4652_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_pos_4652_);
v_err_4653_ = lean_ctor_get(v___x_4647_, 1);
lean_inc(v_err_4653_);
lean_dec_ref_known(v___x_4647_, 2);
v_snd_4618_ = v_snd_4632_;
v_pos_4619_ = v_pos_4652_;
v_err_4620_ = v_err_4653_;
goto v___jp_4617_;
}
}
}
}
}
}
else
{
v___y_4623_ = v_pos_4630_;
v_snd_4624_ = v_snd_4632_;
goto v___jp_4622_;
}
}
}
v___jp_4658_:
{
lean_object* v___x_4662_; 
lean_inc_ref(v_pos_4660_);
v___x_4662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4662_, 0, v_pos_4660_);
lean_ctor_set(v___x_4662_, 1, v_err_4661_);
v_snd_4628_ = v_snd_4659_;
v___y_4629_ = v___x_4662_;
v_pos_4630_ = v_pos_4660_;
goto v___jp_4627_;
}
v___jp_4663_:
{
lean_object* v___x_4666_; 
v___x_4666_ = lean_box(0);
v_snd_4659_ = v_snd_4665_;
v_pos_4660_ = v___y_4664_;
v_err_4661_ = v___x_4666_;
goto v___jp_4658_;
}
v___jp_4668_:
{
lean_object* v_fst_4672_; lean_object* v_snd_4673_; uint8_t v_decide_4674_; 
v_fst_4672_ = lean_ctor_get(v_pos_4671_, 0);
v_snd_4673_ = lean_ctor_get(v_pos_4671_, 1);
lean_inc(v_snd_4673_);
v_decide_4674_ = lean_nat_dec_eq(v_snd_4669_, v_snd_4673_);
lean_dec(v_snd_4669_);
if (v_decide_4674_ == 0)
{
lean_dec(v_snd_4673_);
lean_dec_ref(v_pos_4671_);
return v___y_4670_;
}
else
{
lean_object* v___x_4675_; uint8_t v_decide_4676_; 
lean_dec_ref(v___y_4670_);
v___x_4675_ = lean_string_utf8_byte_size(v_fst_4672_);
v_decide_4676_ = lean_nat_dec_eq(v_snd_4673_, v___x_4675_);
if (v_decide_4676_ == 0)
{
if (v_decide_4674_ == 0)
{
v___y_4664_ = v_pos_4671_;
v_snd_4665_ = v_snd_4673_;
goto v___jp_4663_;
}
else
{
uint32_t v___x_4677_; uint32_t v_c_4678_; uint8_t v___x_4679_; 
v___x_4677_ = 88;
v_c_4678_ = lean_string_utf8_get_fast(v_fst_4672_, v_snd_4673_);
v___x_4679_ = lean_uint32_dec_eq(v_c_4678_, v___x_4677_);
if (v___x_4679_ == 0)
{
lean_object* v___x_4680_; 
v___x_4680_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3);
v_snd_4659_ = v_snd_4673_;
v_pos_4660_ = v_pos_4671_;
v_err_4661_ = v___x_4680_;
goto v___jp_4658_;
}
else
{
lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4696_; 
lean_inc(v_fst_4672_);
v_isSharedCheck_4696_ = !lean_is_exclusive(v_pos_4671_);
if (v_isSharedCheck_4696_ == 0)
{
lean_object* v_unused_4697_; lean_object* v_unused_4698_; 
v_unused_4697_ = lean_ctor_get(v_pos_4671_, 1);
lean_dec(v_unused_4697_);
v_unused_4698_ = lean_ctor_get(v_pos_4671_, 0);
lean_dec(v_unused_4698_);
v___x_4682_ = v_pos_4671_;
v_isShared_4683_ = v_isSharedCheck_4696_;
goto v_resetjp_4681_;
}
else
{
lean_dec(v_pos_4671_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4696_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4684_; lean_object* v_it_x27_4686_; 
v___x_4684_ = lean_string_utf8_next_fast(v_fst_4672_, v_snd_4673_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 1, v___x_4684_);
v_it_x27_4686_ = v___x_4682_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_fst_4672_);
lean_ctor_set(v_reuseFailAlloc_4695_, 1, v___x_4684_);
v_it_x27_4686_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4687_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0);
v___x_4688_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(v___x_4687_, v_it_x27_4686_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_pos_4689_; lean_object* v_res_4690_; lean_object* v___x_4691_; 
v_pos_4689_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_pos_4689_);
v_res_4690_ = lean_ctor_get(v___x_4688_, 1);
lean_inc(v_res_4690_);
lean_dec_ref_known(v___x_4688_, 2);
v___x_4691_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4667_, v_res_4690_, v_pos_4689_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_dec(v_snd_4673_);
return v___x_4691_;
}
else
{
lean_object* v_pos_4692_; 
v_pos_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_pos_4692_);
v_snd_4628_ = v_snd_4673_;
v___y_4629_ = v___x_4691_;
v_pos_4630_ = v_pos_4692_;
goto v___jp_4627_;
}
}
else
{
lean_object* v_pos_4693_; lean_object* v_err_4694_; 
v_pos_4693_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_pos_4693_);
v_err_4694_ = lean_ctor_get(v___x_4688_, 1);
lean_inc(v_err_4694_);
lean_dec_ref_known(v___x_4688_, 2);
v_snd_4659_ = v_snd_4673_;
v_pos_4660_ = v_pos_4693_;
v_err_4661_ = v_err_4694_;
goto v___jp_4658_;
}
}
}
}
}
}
else
{
v___y_4664_ = v_pos_4671_;
v_snd_4665_ = v_snd_4673_;
goto v___jp_4663_;
}
}
}
v___jp_4699_:
{
lean_object* v___x_4703_; 
lean_inc_ref(v_pos_4701_);
v___x_4703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4703_, 0, v_pos_4701_);
lean_ctor_set(v___x_4703_, 1, v_err_4702_);
v_snd_4669_ = v_snd_4700_;
v___y_4670_ = v___x_4703_;
v_pos_4671_ = v_pos_4701_;
goto v___jp_4668_;
}
v___jp_4704_:
{
lean_object* v___x_4707_; 
v___x_4707_ = lean_box(0);
v_snd_4700_ = v_snd_4706_;
v_pos_4701_ = v___y_4705_;
v_err_4702_ = v___x_4707_;
goto v___jp_4699_;
}
v___jp_4709_:
{
lean_object* v_fst_4713_; lean_object* v_snd_4714_; uint8_t v_decide_4715_; 
v_fst_4713_ = lean_ctor_get(v_pos_4712_, 0);
v_snd_4714_ = lean_ctor_get(v_pos_4712_, 1);
lean_inc(v_snd_4714_);
v_decide_4715_ = lean_nat_dec_eq(v_snd_4710_, v_snd_4714_);
lean_dec(v_snd_4710_);
if (v_decide_4715_ == 0)
{
lean_dec(v_snd_4714_);
lean_dec_ref(v_pos_4712_);
return v___y_4711_;
}
else
{
lean_object* v___x_4716_; uint8_t v_decide_4717_; 
lean_dec_ref(v___y_4711_);
v___x_4716_ = lean_string_utf8_byte_size(v_fst_4713_);
v_decide_4717_ = lean_nat_dec_eq(v_snd_4714_, v___x_4716_);
if (v_decide_4717_ == 0)
{
if (v_decide_4715_ == 0)
{
v___y_4705_ = v_pos_4712_;
v_snd_4706_ = v_snd_4714_;
goto v___jp_4704_;
}
else
{
uint32_t v___x_4718_; uint32_t v_c_4719_; uint8_t v___x_4720_; 
v___x_4718_ = 79;
v_c_4719_ = lean_string_utf8_get_fast(v_fst_4713_, v_snd_4714_);
v___x_4720_ = lean_uint32_dec_eq(v_c_4719_, v___x_4718_);
if (v___x_4720_ == 0)
{
lean_object* v___x_4721_; 
v___x_4721_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3);
v_snd_4700_ = v_snd_4714_;
v_pos_4701_ = v_pos_4712_;
v_err_4702_ = v___x_4721_;
goto v___jp_4699_;
}
else
{
lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4737_; 
lean_inc(v_fst_4713_);
v_isSharedCheck_4737_ = !lean_is_exclusive(v_pos_4712_);
if (v_isSharedCheck_4737_ == 0)
{
lean_object* v_unused_4738_; lean_object* v_unused_4739_; 
v_unused_4738_ = lean_ctor_get(v_pos_4712_, 1);
lean_dec(v_unused_4738_);
v_unused_4739_ = lean_ctor_get(v_pos_4712_, 0);
lean_dec(v_unused_4739_);
v___x_4723_ = v_pos_4712_;
v_isShared_4724_ = v_isSharedCheck_4737_;
goto v_resetjp_4722_;
}
else
{
lean_dec(v_pos_4712_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4737_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4725_; lean_object* v_it_x27_4727_; 
v___x_4725_ = lean_string_utf8_next_fast(v_fst_4713_, v_snd_4714_);
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 1, v___x_4725_);
v_it_x27_4727_ = v___x_4723_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_fst_4713_);
lean_ctor_set(v_reuseFailAlloc_4736_, 1, v___x_4725_);
v_it_x27_4727_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0);
v___x_4729_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(v___x_4728_, v_it_x27_4727_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_pos_4730_; lean_object* v_res_4731_; lean_object* v___x_4732_; 
v_pos_4730_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_pos_4730_);
v_res_4731_ = lean_ctor_get(v___x_4729_, 1);
lean_inc(v_res_4731_);
lean_dec_ref_known(v___x_4729_, 2);
v___x_4732_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(v___f_4708_, v_res_4731_, v_pos_4730_);
if (lean_obj_tag(v___x_4732_) == 0)
{
lean_dec(v_snd_4714_);
return v___x_4732_;
}
else
{
lean_object* v_pos_4733_; 
v_pos_4733_ = lean_ctor_get(v___x_4732_, 0);
lean_inc(v_pos_4733_);
v_snd_4669_ = v_snd_4714_;
v___y_4670_ = v___x_4732_;
v_pos_4671_ = v_pos_4733_;
goto v___jp_4668_;
}
}
else
{
lean_object* v_pos_4734_; lean_object* v_err_4735_; 
v_pos_4734_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_pos_4734_);
v_err_4735_ = lean_ctor_get(v___x_4729_, 1);
lean_inc(v_err_4735_);
lean_dec_ref_known(v___x_4729_, 2);
v_snd_4700_ = v_snd_4714_;
v_pos_4701_ = v_pos_4734_;
v_err_4702_ = v_err_4735_;
goto v___jp_4699_;
}
}
}
}
}
}
else
{
v___y_4705_ = v_pos_4712_;
v_snd_4706_ = v_snd_4714_;
goto v___jp_4704_;
}
}
}
v___jp_4740_:
{
lean_object* v___x_4744_; 
lean_inc_ref(v_pos_4742_);
v___x_4744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4744_, 0, v_pos_4742_);
lean_ctor_set(v___x_4744_, 1, v_err_4743_);
v_snd_4710_ = v_snd_4741_;
v___y_4711_ = v___x_4744_;
v_pos_4712_ = v_pos_4742_;
goto v___jp_4709_;
}
v___jp_4745_:
{
lean_object* v___x_4748_; 
v___x_4748_ = lean_box(0);
v_snd_4741_ = v_snd_4747_;
v_pos_4742_ = v___y_4746_;
v_err_4743_ = v___x_4748_;
goto v___jp_4740_;
}
v___jp_4750_:
{
lean_object* v_fst_4754_; lean_object* v_snd_4755_; uint8_t v_decide_4756_; 
v_fst_4754_ = lean_ctor_get(v_pos_4753_, 0);
v_snd_4755_ = lean_ctor_get(v_pos_4753_, 1);
lean_inc(v_snd_4755_);
v_decide_4756_ = lean_nat_dec_eq(v_snd_4751_, v_snd_4755_);
lean_dec(v_snd_4751_);
if (v_decide_4756_ == 0)
{
lean_dec(v_snd_4755_);
lean_dec_ref(v_pos_4753_);
return v___y_4752_;
}
else
{
lean_object* v___x_4757_; uint8_t v_decide_4758_; 
lean_dec_ref(v___y_4752_);
v___x_4757_ = lean_string_utf8_byte_size(v_fst_4754_);
v_decide_4758_ = lean_nat_dec_eq(v_snd_4755_, v___x_4757_);
if (v_decide_4758_ == 0)
{
if (v_decide_4756_ == 0)
{
v___y_4746_ = v_pos_4753_;
v_snd_4747_ = v_snd_4755_;
goto v___jp_4745_;
}
else
{
uint32_t v___x_4759_; uint32_t v_c_4760_; uint8_t v___x_4761_; 
v___x_4759_ = 118;
v_c_4760_ = lean_string_utf8_get_fast(v_fst_4754_, v_snd_4755_);
v___x_4761_ = lean_uint32_dec_eq(v_c_4760_, v___x_4759_);
if (v___x_4761_ == 0)
{
lean_object* v___x_4762_; 
v___x_4762_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3);
v_snd_4741_ = v_snd_4755_;
v_pos_4742_ = v_pos_4753_;
v_err_4743_ = v___x_4762_;
goto v___jp_4740_;
}
else
{
lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4778_; 
lean_inc(v_fst_4754_);
v_isSharedCheck_4778_ = !lean_is_exclusive(v_pos_4753_);
if (v_isSharedCheck_4778_ == 0)
{
lean_object* v_unused_4779_; lean_object* v_unused_4780_; 
v_unused_4779_ = lean_ctor_get(v_pos_4753_, 1);
lean_dec(v_unused_4779_);
v_unused_4780_ = lean_ctor_get(v_pos_4753_, 0);
lean_dec(v_unused_4780_);
v___x_4764_ = v_pos_4753_;
v_isShared_4765_ = v_isSharedCheck_4778_;
goto v_resetjp_4763_;
}
else
{
lean_dec(v_pos_4753_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4778_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4766_; lean_object* v_it_x27_4768_; 
v___x_4766_ = lean_string_utf8_next_fast(v_fst_4754_, v_snd_4755_);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 1, v___x_4766_);
v_it_x27_4768_ = v___x_4764_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_fst_4754_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v___x_4766_);
v_it_x27_4768_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4769_; lean_object* v___x_4770_; 
v___x_4769_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0);
v___x_4770_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(v___x_4769_, v_it_x27_4768_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_pos_4771_; lean_object* v_res_4772_; lean_object* v___x_4773_; 
v_pos_4771_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_pos_4771_);
v_res_4772_ = lean_ctor_get(v___x_4770_, 1);
lean_inc(v_res_4772_);
lean_dec_ref_known(v___x_4770_, 2);
v___x_4773_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4749_, v_res_4772_, v_pos_4771_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_dec(v_snd_4755_);
return v___x_4773_;
}
else
{
lean_object* v_pos_4774_; 
v_pos_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_pos_4774_);
v_snd_4710_ = v_snd_4755_;
v___y_4711_ = v___x_4773_;
v_pos_4712_ = v_pos_4774_;
goto v___jp_4709_;
}
}
else
{
lean_object* v_pos_4775_; lean_object* v_err_4776_; 
v_pos_4775_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_pos_4775_);
v_err_4776_ = lean_ctor_get(v___x_4770_, 1);
lean_inc(v_err_4776_);
lean_dec_ref_known(v___x_4770_, 2);
v_snd_4741_ = v_snd_4755_;
v_pos_4742_ = v_pos_4775_;
v_err_4743_ = v_err_4776_;
goto v___jp_4740_;
}
}
}
}
}
}
else
{
v___y_4746_ = v_pos_4753_;
v_snd_4747_ = v_snd_4755_;
goto v___jp_4745_;
}
}
}
v___jp_4781_:
{
lean_object* v___x_4785_; 
lean_inc_ref(v_pos_4783_);
v___x_4785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4785_, 0, v_pos_4783_);
lean_ctor_set(v___x_4785_, 1, v_err_4784_);
v_snd_4751_ = v_snd_4782_;
v___y_4752_ = v___x_4785_;
v_pos_4753_ = v_pos_4783_;
goto v___jp_4750_;
}
v___jp_4786_:
{
lean_object* v___x_4789_; 
v___x_4789_ = lean_box(0);
v_snd_4782_ = v_snd_4788_;
v_pos_4783_ = v___y_4787_;
v_err_4784_ = v___x_4789_;
goto v___jp_4781_;
}
v___jp_4791_:
{
lean_object* v_fst_4795_; lean_object* v_snd_4796_; uint8_t v_decide_4797_; 
v_fst_4795_ = lean_ctor_get(v_pos_4794_, 0);
v_snd_4796_ = lean_ctor_get(v_pos_4794_, 1);
lean_inc(v_snd_4796_);
v_decide_4797_ = lean_nat_dec_eq(v_snd_4792_, v_snd_4796_);
lean_dec(v_snd_4792_);
if (v_decide_4797_ == 0)
{
lean_dec(v_snd_4796_);
lean_dec_ref(v_pos_4794_);
return v___y_4793_;
}
else
{
lean_object* v___x_4798_; uint8_t v_decide_4799_; 
lean_dec_ref(v___y_4793_);
v___x_4798_ = lean_string_utf8_byte_size(v_fst_4795_);
v_decide_4799_ = lean_nat_dec_eq(v_snd_4796_, v___x_4798_);
if (v_decide_4799_ == 0)
{
if (v_decide_4797_ == 0)
{
v___y_4787_ = v_pos_4794_;
v_snd_4788_ = v_snd_4796_;
goto v___jp_4786_;
}
else
{
uint32_t v___x_4800_; uint32_t v_c_4801_; uint8_t v___x_4802_; 
v___x_4800_ = 122;
v_c_4801_ = lean_string_utf8_get_fast(v_fst_4795_, v_snd_4796_);
v___x_4802_ = lean_uint32_dec_eq(v_c_4801_, v___x_4800_);
if (v___x_4802_ == 0)
{
lean_object* v___x_4803_; 
v___x_4803_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3);
v_snd_4782_ = v_snd_4796_;
v_pos_4783_ = v_pos_4794_;
v_err_4784_ = v___x_4803_;
goto v___jp_4781_;
}
else
{
lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4819_; 
lean_inc(v_fst_4795_);
v_isSharedCheck_4819_ = !lean_is_exclusive(v_pos_4794_);
if (v_isSharedCheck_4819_ == 0)
{
lean_object* v_unused_4820_; lean_object* v_unused_4821_; 
v_unused_4820_ = lean_ctor_get(v_pos_4794_, 1);
lean_dec(v_unused_4820_);
v_unused_4821_ = lean_ctor_get(v_pos_4794_, 0);
lean_dec(v_unused_4821_);
v___x_4805_ = v_pos_4794_;
v_isShared_4806_ = v_isSharedCheck_4819_;
goto v_resetjp_4804_;
}
else
{
lean_dec(v_pos_4794_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4819_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4807_; lean_object* v_it_x27_4809_; 
v___x_4807_ = lean_string_utf8_next_fast(v_fst_4795_, v_snd_4796_);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 1, v___x_4807_);
v_it_x27_4809_ = v___x_4805_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_fst_4795_);
lean_ctor_set(v_reuseFailAlloc_4818_, 1, v___x_4807_);
v_it_x27_4809_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4810_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0);
v___x_4811_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(v___x_4810_, v_it_x27_4809_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_object* v_pos_4812_; lean_object* v_res_4813_; lean_object* v___x_4814_; 
v_pos_4812_ = lean_ctor_get(v___x_4811_, 0);
lean_inc(v_pos_4812_);
v_res_4813_ = lean_ctor_get(v___x_4811_, 1);
lean_inc(v_res_4813_);
lean_dec_ref_known(v___x_4811_, 2);
v___x_4814_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4790_, v_res_4813_, v_pos_4812_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_dec(v_snd_4796_);
return v___x_4814_;
}
else
{
lean_object* v_pos_4815_; 
v_pos_4815_ = lean_ctor_get(v___x_4814_, 0);
lean_inc(v_pos_4815_);
v_snd_4751_ = v_snd_4796_;
v___y_4752_ = v___x_4814_;
v_pos_4753_ = v_pos_4815_;
goto v___jp_4750_;
}
}
else
{
lean_object* v_pos_4816_; lean_object* v_err_4817_; 
v_pos_4816_ = lean_ctor_get(v___x_4811_, 0);
lean_inc(v_pos_4816_);
v_err_4817_ = lean_ctor_get(v___x_4811_, 1);
lean_inc(v_err_4817_);
lean_dec_ref_known(v___x_4811_, 2);
v_snd_4782_ = v_snd_4796_;
v_pos_4783_ = v_pos_4816_;
v_err_4784_ = v_err_4817_;
goto v___jp_4781_;
}
}
}
}
}
}
else
{
v___y_4787_ = v_pos_4794_;
v_snd_4788_ = v_snd_4796_;
goto v___jp_4786_;
}
}
}
v___jp_4822_:
{
lean_object* v___x_4826_; 
lean_inc_ref(v_pos_4824_);
v___x_4826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4826_, 0, v_pos_4824_);
lean_ctor_set(v___x_4826_, 1, v_err_4825_);
v_snd_4792_ = v_snd_4823_;
v___y_4793_ = v___x_4826_;
v_pos_4794_ = v_pos_4824_;
goto v___jp_4791_;
}
v___jp_4827_:
{
lean_object* v___x_4830_; 
v___x_4830_ = lean_box(0);
v_snd_4823_ = v_snd_4829_;
v_pos_4824_ = v___y_4828_;
v_err_4825_ = v___x_4830_;
goto v___jp_4822_;
}
v___jp_4831_:
{
lean_object* v_fst_4835_; lean_object* v_snd_4836_; uint8_t v_decide_4837_; 
v_fst_4835_ = lean_ctor_get(v_pos_4834_, 0);
v_snd_4836_ = lean_ctor_get(v_pos_4834_, 1);
lean_inc(v_snd_4836_);
v_decide_4837_ = lean_nat_dec_eq(v_snd_4832_, v_snd_4836_);
lean_dec(v_snd_4832_);
if (v_decide_4837_ == 0)
{
lean_dec(v_snd_4836_);
lean_dec_ref(v_pos_4834_);
return v___y_4833_;
}
else
{
lean_object* v___x_4838_; uint8_t v_decide_4839_; 
lean_dec_ref(v___y_4833_);
v___x_4838_ = lean_string_utf8_byte_size(v_fst_4835_);
v_decide_4839_ = lean_nat_dec_eq(v_snd_4836_, v___x_4838_);
if (v_decide_4839_ == 0)
{
if (v_decide_4837_ == 0)
{
v___y_4828_ = v_pos_4834_;
v_snd_4829_ = v_snd_4836_;
goto v___jp_4827_;
}
else
{
uint32_t v___x_4840_; uint32_t v_c_4841_; uint8_t v___x_4842_; 
v___x_4840_ = 86;
v_c_4841_ = lean_string_utf8_get_fast(v_fst_4835_, v_snd_4836_);
v___x_4842_ = lean_uint32_dec_eq(v_c_4841_, v___x_4840_);
if (v___x_4842_ == 0)
{
lean_object* v___x_4843_; 
v___x_4843_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3);
v_snd_4823_ = v_snd_4836_;
v_pos_4824_ = v_pos_4834_;
v_err_4825_ = v___x_4843_;
goto v___jp_4822_;
}
else
{
lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4859_; 
lean_inc(v_fst_4835_);
v_isSharedCheck_4859_ = !lean_is_exclusive(v_pos_4834_);
if (v_isSharedCheck_4859_ == 0)
{
lean_object* v_unused_4860_; lean_object* v_unused_4861_; 
v_unused_4860_ = lean_ctor_get(v_pos_4834_, 1);
lean_dec(v_unused_4860_);
v_unused_4861_ = lean_ctor_get(v_pos_4834_, 0);
lean_dec(v_unused_4861_);
v___x_4845_ = v_pos_4834_;
v_isShared_4846_ = v_isSharedCheck_4859_;
goto v_resetjp_4844_;
}
else
{
lean_dec(v_pos_4834_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4859_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4847_; lean_object* v_it_x27_4849_; 
v___x_4847_ = lean_string_utf8_next_fast(v_fst_4835_, v_snd_4836_);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 1, v___x_4847_);
v_it_x27_4849_ = v___x_4845_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_fst_4835_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v___x_4847_);
v_it_x27_4849_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; 
v___x_4850_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0);
v___x_4851_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(v___x_4850_, v_it_x27_4849_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_pos_4852_; lean_object* v_res_4853_; lean_object* v___x_4854_; 
v_pos_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_pos_4852_);
v_res_4853_ = lean_ctor_get(v___x_4851_, 1);
lean_inc(v_res_4853_);
lean_dec_ref_known(v___x_4851_, 2);
v___x_4854_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(v_res_4853_, v_pos_4852_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_dec(v_snd_4836_);
return v___x_4854_;
}
else
{
lean_object* v_pos_4855_; 
v_pos_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_pos_4855_);
v_snd_4792_ = v_snd_4836_;
v___y_4793_ = v___x_4854_;
v_pos_4794_ = v_pos_4855_;
goto v___jp_4791_;
}
}
else
{
lean_object* v_pos_4856_; lean_object* v_err_4857_; 
v_pos_4856_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_pos_4856_);
v_err_4857_ = lean_ctor_get(v___x_4851_, 1);
lean_inc(v_err_4857_);
lean_dec_ref_known(v___x_4851_, 2);
v_snd_4823_ = v_snd_4836_;
v_pos_4824_ = v_pos_4856_;
v_err_4825_ = v_err_4857_;
goto v___jp_4822_;
}
}
}
}
}
}
else
{
v___y_4828_ = v_pos_4834_;
v_snd_4829_ = v_snd_4836_;
goto v___jp_4827_;
}
}
}
v___jp_4862_:
{
lean_object* v___x_4866_; 
lean_inc_ref(v_pos_4864_);
v___x_4866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4866_, 0, v_pos_4864_);
lean_ctor_set(v___x_4866_, 1, v_err_4865_);
v_snd_4832_ = v_snd_4863_;
v___y_4833_ = v___x_4866_;
v_pos_4834_ = v_pos_4864_;
goto v___jp_4831_;
}
v___jp_4867_:
{
lean_object* v___x_4870_; 
v___x_4870_ = lean_box(0);
v_snd_4863_ = v_snd_4869_;
v_pos_4864_ = v___y_4868_;
v_err_4865_ = v___x_4870_;
goto v___jp_4862_;
}
v___jp_4872_:
{
lean_object* v_fst_4876_; lean_object* v_snd_4877_; uint8_t v_decide_4878_; 
v_fst_4876_ = lean_ctor_get(v_pos_4875_, 0);
v_snd_4877_ = lean_ctor_get(v_pos_4875_, 1);
lean_inc(v_snd_4877_);
v_decide_4878_ = lean_nat_dec_eq(v_snd_4873_, v_snd_4877_);
lean_dec(v_snd_4873_);
if (v_decide_4878_ == 0)
{
lean_dec(v_snd_4877_);
lean_dec_ref(v_pos_4875_);
return v___y_4874_;
}
else
{
lean_object* v___x_4879_; uint8_t v_decide_4880_; 
lean_dec_ref(v___y_4874_);
v___x_4879_ = lean_string_utf8_byte_size(v_fst_4876_);
v_decide_4880_ = lean_nat_dec_eq(v_snd_4877_, v___x_4879_);
if (v_decide_4880_ == 0)
{
if (v_decide_4878_ == 0)
{
v___y_4868_ = v_pos_4875_;
v_snd_4869_ = v_snd_4877_;
goto v___jp_4867_;
}
else
{
uint32_t v___x_4881_; uint32_t v_c_4882_; uint8_t v___x_4883_; 
v___x_4881_ = 78;
v_c_4882_ = lean_string_utf8_get_fast(v_fst_4876_, v_snd_4877_);
v___x_4883_ = lean_uint32_dec_eq(v_c_4882_, v___x_4881_);
if (v___x_4883_ == 0)
{
lean_object* v___x_4884_; 
v___x_4884_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3);
v_snd_4863_ = v_snd_4877_;
v_pos_4864_ = v_pos_4875_;
v_err_4865_ = v___x_4884_;
goto v___jp_4862_;
}
else
{
lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4899_; 
lean_inc(v_fst_4876_);
v_isSharedCheck_4899_ = !lean_is_exclusive(v_pos_4875_);
if (v_isSharedCheck_4899_ == 0)
{
lean_object* v_unused_4900_; lean_object* v_unused_4901_; 
v_unused_4900_ = lean_ctor_get(v_pos_4875_, 1);
lean_dec(v_unused_4900_);
v_unused_4901_ = lean_ctor_get(v_pos_4875_, 0);
lean_dec(v_unused_4901_);
v___x_4886_ = v_pos_4875_;
v_isShared_4887_ = v_isSharedCheck_4899_;
goto v_resetjp_4885_;
}
else
{
lean_dec(v_pos_4875_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4899_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4888_; lean_object* v_it_x27_4890_; 
v___x_4888_ = lean_string_utf8_next_fast(v_fst_4876_, v_snd_4877_);
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 1, v___x_4888_);
v_it_x27_4890_ = v___x_4886_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_fst_4876_);
lean_ctor_set(v_reuseFailAlloc_4898_, 1, v___x_4888_);
v_it_x27_4890_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4891_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0);
v___x_4892_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(v___x_4891_, v_it_x27_4890_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_pos_4893_; lean_object* v_res_4894_; lean_object* v___x_4895_; 
lean_dec(v_snd_4877_);
v_pos_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_pos_4893_);
v_res_4894_ = lean_ctor_get(v___x_4892_, 1);
lean_inc(v_res_4894_);
lean_dec_ref_known(v___x_4892_, 2);
v___x_4895_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4871_, v_res_4894_, v_pos_4893_);
lean_dec(v_res_4894_);
return v___x_4895_;
}
else
{
lean_object* v_pos_4896_; lean_object* v_err_4897_; 
v_pos_4896_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_pos_4896_);
v_err_4897_ = lean_ctor_get(v___x_4892_, 1);
lean_inc(v_err_4897_);
lean_dec_ref_known(v___x_4892_, 2);
v_snd_4863_ = v_snd_4877_;
v_pos_4864_ = v_pos_4896_;
v_err_4865_ = v_err_4897_;
goto v___jp_4862_;
}
}
}
}
}
}
else
{
v___y_4868_ = v_pos_4875_;
v_snd_4869_ = v_snd_4877_;
goto v___jp_4867_;
}
}
}
v___jp_4902_:
{
lean_object* v___x_4906_; 
lean_inc_ref(v_pos_4904_);
v___x_4906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4906_, 0, v_pos_4904_);
lean_ctor_set(v___x_4906_, 1, v_err_4905_);
v_snd_4873_ = v_snd_4903_;
v___y_4874_ = v___x_4906_;
v_pos_4875_ = v_pos_4904_;
goto v___jp_4872_;
}
v___jp_4907_:
{
lean_object* v___x_4910_; 
v___x_4910_ = lean_box(0);
v_snd_4903_ = v_snd_4909_;
v_pos_4904_ = v___y_4908_;
v_err_4905_ = v___x_4910_;
goto v___jp_4902_;
}
v___jp_4912_:
{
lean_object* v_fst_4916_; lean_object* v_snd_4917_; uint8_t v_decide_4918_; 
v_fst_4916_ = lean_ctor_get(v_pos_4915_, 0);
v_snd_4917_ = lean_ctor_get(v_pos_4915_, 1);
lean_inc(v_snd_4917_);
v_decide_4918_ = lean_nat_dec_eq(v_snd_4913_, v_snd_4917_);
lean_dec(v_snd_4913_);
if (v_decide_4918_ == 0)
{
lean_dec(v_snd_4917_);
lean_dec_ref(v_pos_4915_);
return v___y_4914_;
}
else
{
lean_object* v___x_4919_; uint8_t v_decide_4920_; 
lean_dec_ref(v___y_4914_);
v___x_4919_ = lean_string_utf8_byte_size(v_fst_4916_);
v_decide_4920_ = lean_nat_dec_eq(v_snd_4917_, v___x_4919_);
if (v_decide_4920_ == 0)
{
if (v_decide_4918_ == 0)
{
v___y_4908_ = v_pos_4915_;
v_snd_4909_ = v_snd_4917_;
goto v___jp_4907_;
}
else
{
uint32_t v___x_4921_; uint32_t v_c_4922_; uint8_t v___x_4923_; 
v___x_4921_ = 110;
v_c_4922_ = lean_string_utf8_get_fast(v_fst_4916_, v_snd_4917_);
v___x_4923_ = lean_uint32_dec_eq(v_c_4922_, v___x_4921_);
if (v___x_4923_ == 0)
{
lean_object* v___x_4924_; 
v___x_4924_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3);
v_snd_4903_ = v_snd_4917_;
v_pos_4904_ = v_pos_4915_;
v_err_4905_ = v___x_4924_;
goto v___jp_4902_;
}
else
{
lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4939_; 
lean_inc(v_fst_4916_);
v_isSharedCheck_4939_ = !lean_is_exclusive(v_pos_4915_);
if (v_isSharedCheck_4939_ == 0)
{
lean_object* v_unused_4940_; lean_object* v_unused_4941_; 
v_unused_4940_ = lean_ctor_get(v_pos_4915_, 1);
lean_dec(v_unused_4940_);
v_unused_4941_ = lean_ctor_get(v_pos_4915_, 0);
lean_dec(v_unused_4941_);
v___x_4926_ = v_pos_4915_;
v_isShared_4927_ = v_isSharedCheck_4939_;
goto v_resetjp_4925_;
}
else
{
lean_dec(v_pos_4915_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4939_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v_it_x27_4930_; 
v___x_4928_ = lean_string_utf8_next_fast(v_fst_4916_, v_snd_4917_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 1, v___x_4928_);
v_it_x27_4930_ = v___x_4926_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_fst_4916_);
lean_ctor_set(v_reuseFailAlloc_4938_, 1, v___x_4928_);
v_it_x27_4930_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4931_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0);
v___x_4932_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(v___x_4931_, v_it_x27_4930_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_pos_4933_; lean_object* v_res_4934_; lean_object* v___x_4935_; 
lean_dec(v_snd_4917_);
v_pos_4933_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_pos_4933_);
v_res_4934_ = lean_ctor_get(v___x_4932_, 1);
lean_inc(v_res_4934_);
lean_dec_ref_known(v___x_4932_, 2);
v___x_4935_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4911_, v_res_4934_, v_pos_4933_);
lean_dec(v_res_4934_);
return v___x_4935_;
}
else
{
lean_object* v_pos_4936_; lean_object* v_err_4937_; 
v_pos_4936_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_pos_4936_);
v_err_4937_ = lean_ctor_get(v___x_4932_, 1);
lean_inc(v_err_4937_);
lean_dec_ref_known(v___x_4932_, 2);
v_snd_4903_ = v_snd_4917_;
v_pos_4904_ = v_pos_4936_;
v_err_4905_ = v_err_4937_;
goto v___jp_4902_;
}
}
}
}
}
}
else
{
v___y_4908_ = v_pos_4915_;
v_snd_4909_ = v_snd_4917_;
goto v___jp_4907_;
}
}
}
v___jp_4942_:
{
lean_object* v___x_4946_; 
lean_inc_ref(v_pos_4944_);
v___x_4946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4946_, 0, v_pos_4944_);
lean_ctor_set(v___x_4946_, 1, v_err_4945_);
v_snd_4913_ = v_snd_4943_;
v___y_4914_ = v___x_4946_;
v_pos_4915_ = v_pos_4944_;
goto v___jp_4912_;
}
v___jp_4947_:
{
lean_object* v___x_4950_; 
v___x_4950_ = lean_box(0);
v_snd_4943_ = v_snd_4949_;
v_pos_4944_ = v___y_4948_;
v_err_4945_ = v___x_4950_;
goto v___jp_4942_;
}
v___jp_4952_:
{
lean_object* v_fst_4956_; lean_object* v_snd_4957_; uint8_t v_decide_4958_; 
v_fst_4956_ = lean_ctor_get(v_pos_4955_, 0);
v_snd_4957_ = lean_ctor_get(v_pos_4955_, 1);
lean_inc(v_snd_4957_);
v_decide_4958_ = lean_nat_dec_eq(v_snd_4953_, v_snd_4957_);
lean_dec(v_snd_4953_);
if (v_decide_4958_ == 0)
{
lean_dec(v_snd_4957_);
lean_dec_ref(v_pos_4955_);
return v___y_4954_;
}
else
{
lean_object* v___x_4959_; uint8_t v_decide_4960_; 
lean_dec_ref(v___y_4954_);
v___x_4959_ = lean_string_utf8_byte_size(v_fst_4956_);
v_decide_4960_ = lean_nat_dec_eq(v_snd_4957_, v___x_4959_);
if (v_decide_4960_ == 0)
{
if (v_decide_4958_ == 0)
{
v___y_4948_ = v_pos_4955_;
v_snd_4949_ = v_snd_4957_;
goto v___jp_4947_;
}
else
{
uint32_t v___x_4961_; uint32_t v_c_4962_; uint8_t v___x_4963_; 
v___x_4961_ = 65;
v_c_4962_ = lean_string_utf8_get_fast(v_fst_4956_, v_snd_4957_);
v___x_4963_ = lean_uint32_dec_eq(v_c_4962_, v___x_4961_);
if (v___x_4963_ == 0)
{
lean_object* v___x_4964_; 
v___x_4964_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3);
v_snd_4943_ = v_snd_4957_;
v_pos_4944_ = v_pos_4955_;
v_err_4945_ = v___x_4964_;
goto v___jp_4942_;
}
else
{
lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4979_; 
lean_inc(v_fst_4956_);
v_isSharedCheck_4979_ = !lean_is_exclusive(v_pos_4955_);
if (v_isSharedCheck_4979_ == 0)
{
lean_object* v_unused_4980_; lean_object* v_unused_4981_; 
v_unused_4980_ = lean_ctor_get(v_pos_4955_, 1);
lean_dec(v_unused_4980_);
v_unused_4981_ = lean_ctor_get(v_pos_4955_, 0);
lean_dec(v_unused_4981_);
v___x_4966_ = v_pos_4955_;
v_isShared_4967_ = v_isSharedCheck_4979_;
goto v_resetjp_4965_;
}
else
{
lean_dec(v_pos_4955_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4979_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4968_; lean_object* v_it_x27_4970_; 
v___x_4968_ = lean_string_utf8_next_fast(v_fst_4956_, v_snd_4957_);
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 1, v___x_4968_);
v_it_x27_4970_ = v___x_4966_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_fst_4956_);
lean_ctor_set(v_reuseFailAlloc_4978_, 1, v___x_4968_);
v_it_x27_4970_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4971_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0);
v___x_4972_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(v___x_4971_, v_it_x27_4970_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v_pos_4973_; lean_object* v_res_4974_; lean_object* v___x_4975_; 
lean_dec(v_snd_4957_);
v_pos_4973_ = lean_ctor_get(v___x_4972_, 0);
lean_inc(v_pos_4973_);
v_res_4974_ = lean_ctor_get(v___x_4972_, 1);
lean_inc(v_res_4974_);
lean_dec_ref_known(v___x_4972_, 2);
v___x_4975_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4951_, v_res_4974_, v_pos_4973_);
lean_dec(v_res_4974_);
return v___x_4975_;
}
else
{
lean_object* v_pos_4976_; lean_object* v_err_4977_; 
v_pos_4976_ = lean_ctor_get(v___x_4972_, 0);
lean_inc(v_pos_4976_);
v_err_4977_ = lean_ctor_get(v___x_4972_, 1);
lean_inc(v_err_4977_);
lean_dec_ref_known(v___x_4972_, 2);
v_snd_4943_ = v_snd_4957_;
v_pos_4944_ = v_pos_4976_;
v_err_4945_ = v_err_4977_;
goto v___jp_4942_;
}
}
}
}
}
}
else
{
v___y_4948_ = v_pos_4955_;
v_snd_4949_ = v_snd_4957_;
goto v___jp_4947_;
}
}
}
v___jp_4982_:
{
lean_object* v___x_4986_; 
lean_inc_ref(v_pos_4984_);
v___x_4986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4986_, 0, v_pos_4984_);
lean_ctor_set(v___x_4986_, 1, v_err_4985_);
v_snd_4953_ = v_snd_4983_;
v___y_4954_ = v___x_4986_;
v_pos_4955_ = v_pos_4984_;
goto v___jp_4952_;
}
v___jp_4987_:
{
lean_object* v___x_4990_; 
v___x_4990_ = lean_box(0);
v_snd_4983_ = v_snd_4989_;
v_pos_4984_ = v___y_4988_;
v_err_4985_ = v___x_4990_;
goto v___jp_4982_;
}
v___jp_4992_:
{
lean_object* v_fst_4996_; lean_object* v_snd_4997_; uint8_t v_decide_4998_; 
v_fst_4996_ = lean_ctor_get(v_pos_4995_, 0);
v_snd_4997_ = lean_ctor_get(v_pos_4995_, 1);
lean_inc(v_snd_4997_);
v_decide_4998_ = lean_nat_dec_eq(v_snd_4993_, v_snd_4997_);
lean_dec(v_snd_4993_);
if (v_decide_4998_ == 0)
{
lean_dec(v_snd_4997_);
lean_dec_ref(v_pos_4995_);
return v___y_4994_;
}
else
{
lean_object* v___x_4999_; uint8_t v_decide_5000_; 
lean_dec_ref(v___y_4994_);
v___x_4999_ = lean_string_utf8_byte_size(v_fst_4996_);
v_decide_5000_ = lean_nat_dec_eq(v_snd_4997_, v___x_4999_);
if (v_decide_5000_ == 0)
{
if (v_decide_4998_ == 0)
{
v___y_4988_ = v_pos_4995_;
v_snd_4989_ = v_snd_4997_;
goto v___jp_4987_;
}
else
{
uint32_t v___x_5001_; uint32_t v_c_5002_; uint8_t v___x_5003_; 
v___x_5001_ = 83;
v_c_5002_ = lean_string_utf8_get_fast(v_fst_4996_, v_snd_4997_);
v___x_5003_ = lean_uint32_dec_eq(v_c_5002_, v___x_5001_);
if (v___x_5003_ == 0)
{
lean_object* v___x_5004_; 
v___x_5004_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3);
v_snd_4983_ = v_snd_4997_;
v_pos_4984_ = v_pos_4995_;
v_err_4985_ = v___x_5004_;
goto v___jp_4982_;
}
else
{
lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5020_; 
lean_inc(v_fst_4996_);
v_isSharedCheck_5020_ = !lean_is_exclusive(v_pos_4995_);
if (v_isSharedCheck_5020_ == 0)
{
lean_object* v_unused_5021_; lean_object* v_unused_5022_; 
v_unused_5021_ = lean_ctor_get(v_pos_4995_, 1);
lean_dec(v_unused_5021_);
v_unused_5022_ = lean_ctor_get(v_pos_4995_, 0);
lean_dec(v_unused_5022_);
v___x_5006_ = v_pos_4995_;
v_isShared_5007_ = v_isSharedCheck_5020_;
goto v_resetjp_5005_;
}
else
{
lean_dec(v_pos_4995_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5020_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5008_; lean_object* v_it_x27_5010_; 
v___x_5008_ = lean_string_utf8_next_fast(v_fst_4996_, v_snd_4997_);
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 1, v___x_5008_);
v_it_x27_5010_ = v___x_5006_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_fst_4996_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v___x_5008_);
v_it_x27_5010_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5011_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0);
v___x_5012_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(v___x_5011_, v_it_x27_5010_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_pos_5013_; lean_object* v_res_5014_; lean_object* v___x_5015_; 
v_pos_5013_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_pos_5013_);
v_res_5014_ = lean_ctor_get(v___x_5012_, 1);
lean_inc(v_res_5014_);
lean_dec_ref_known(v___x_5012_, 2);
v___x_5015_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(v___f_4991_, v_res_5014_, v_pos_5013_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_dec(v_snd_4997_);
return v___x_5015_;
}
else
{
lean_object* v_pos_5016_; 
v_pos_5016_ = lean_ctor_get(v___x_5015_, 0);
lean_inc(v_pos_5016_);
v_snd_4953_ = v_snd_4997_;
v___y_4954_ = v___x_5015_;
v_pos_4955_ = v_pos_5016_;
goto v___jp_4952_;
}
}
else
{
lean_object* v_pos_5017_; lean_object* v_err_5018_; 
v_pos_5017_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_pos_5017_);
v_err_5018_ = lean_ctor_get(v___x_5012_, 1);
lean_inc(v_err_5018_);
lean_dec_ref_known(v___x_5012_, 2);
v_snd_4983_ = v_snd_4997_;
v_pos_4984_ = v_pos_5017_;
v_err_4985_ = v_err_5018_;
goto v___jp_4982_;
}
}
}
}
}
}
else
{
v___y_4988_ = v_pos_4995_;
v_snd_4989_ = v_snd_4997_;
goto v___jp_4987_;
}
}
}
v___jp_5023_:
{
lean_object* v___x_5027_; 
lean_inc_ref(v_pos_5025_);
v___x_5027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5027_, 0, v_pos_5025_);
lean_ctor_set(v___x_5027_, 1, v_err_5026_);
v_snd_4993_ = v_snd_5024_;
v___y_4994_ = v___x_5027_;
v_pos_4995_ = v_pos_5025_;
goto v___jp_4992_;
}
v___jp_5028_:
{
lean_object* v___x_5031_; 
v___x_5031_ = lean_box(0);
v_snd_5024_ = v_snd_5030_;
v_pos_5025_ = v___y_5029_;
v_err_5026_ = v___x_5031_;
goto v___jp_5023_;
}
v___jp_5033_:
{
lean_object* v_fst_5038_; lean_object* v_snd_5039_; uint8_t v_decide_5040_; 
v_fst_5038_ = lean_ctor_get(v_pos_5037_, 0);
v_snd_5039_ = lean_ctor_get(v_pos_5037_, 1);
lean_inc(v_snd_5039_);
v_decide_5040_ = lean_nat_dec_eq(v_snd_5034_, v_snd_5039_);
lean_dec(v_snd_5034_);
if (v_decide_5040_ == 0)
{
lean_dec(v_snd_5039_);
lean_dec_ref(v_pos_5037_);
lean_dec_ref(v___y_5035_);
return v___y_5036_;
}
else
{
lean_object* v___x_5041_; uint8_t v_decide_5042_; 
lean_dec_ref(v___y_5036_);
v___x_5041_ = lean_string_utf8_byte_size(v_fst_5038_);
v_decide_5042_ = lean_nat_dec_eq(v_snd_5039_, v___x_5041_);
if (v_decide_5042_ == 0)
{
if (v_decide_5040_ == 0)
{
lean_dec_ref(v___y_5035_);
v___y_5029_ = v_pos_5037_;
v_snd_5030_ = v_snd_5039_;
goto v___jp_5028_;
}
else
{
uint32_t v___x_5043_; uint32_t v_c_5044_; uint8_t v___x_5045_; 
v___x_5043_ = 115;
v_c_5044_ = lean_string_utf8_get_fast(v_fst_5038_, v_snd_5039_);
v___x_5045_ = lean_uint32_dec_eq(v_c_5044_, v___x_5043_);
if (v___x_5045_ == 0)
{
lean_object* v___x_5046_; 
lean_dec_ref(v___y_5035_);
v___x_5046_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3);
v_snd_5024_ = v_snd_5039_;
v_pos_5025_ = v_pos_5037_;
v_err_5026_ = v___x_5046_;
goto v___jp_5023_;
}
else
{
lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5062_; 
lean_inc(v_fst_5038_);
v_isSharedCheck_5062_ = !lean_is_exclusive(v_pos_5037_);
if (v_isSharedCheck_5062_ == 0)
{
lean_object* v_unused_5063_; lean_object* v_unused_5064_; 
v_unused_5063_ = lean_ctor_get(v_pos_5037_, 1);
lean_dec(v_unused_5063_);
v_unused_5064_ = lean_ctor_get(v_pos_5037_, 0);
lean_dec(v_unused_5064_);
v___x_5048_ = v_pos_5037_;
v_isShared_5049_ = v_isSharedCheck_5062_;
goto v_resetjp_5047_;
}
else
{
lean_dec(v_pos_5037_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5062_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5050_; lean_object* v_it_x27_5052_; 
v___x_5050_ = lean_string_utf8_next_fast(v_fst_5038_, v_snd_5039_);
if (v_isShared_5049_ == 0)
{
lean_ctor_set(v___x_5048_, 1, v___x_5050_);
v_it_x27_5052_ = v___x_5048_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_fst_5038_);
lean_ctor_set(v_reuseFailAlloc_5061_, 1, v___x_5050_);
v_it_x27_5052_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0);
v___x_5054_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(v___x_5053_, v_it_x27_5052_);
if (lean_obj_tag(v___x_5054_) == 0)
{
lean_object* v_pos_5055_; lean_object* v_res_5056_; lean_object* v___x_5057_; 
v_pos_5055_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_pos_5055_);
v_res_5056_ = lean_ctor_get(v___x_5054_, 1);
lean_inc(v_res_5056_);
lean_dec_ref_known(v___x_5054_, 2);
v___x_5057_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5032_, v___y_5035_, v_res_5056_, v_pos_5055_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_dec(v_snd_5039_);
return v___x_5057_;
}
else
{
lean_object* v_pos_5058_; 
v_pos_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_pos_5058_);
v_snd_4993_ = v_snd_5039_;
v___y_4994_ = v___x_5057_;
v_pos_4995_ = v_pos_5058_;
goto v___jp_4992_;
}
}
else
{
lean_object* v_pos_5059_; lean_object* v_err_5060_; 
lean_dec_ref(v___y_5035_);
v_pos_5059_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_pos_5059_);
v_err_5060_ = lean_ctor_get(v___x_5054_, 1);
lean_inc(v_err_5060_);
lean_dec_ref_known(v___x_5054_, 2);
v_snd_5024_ = v_snd_5039_;
v_pos_5025_ = v_pos_5059_;
v_err_5026_ = v_err_5060_;
goto v___jp_5023_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_5035_);
v___y_5029_ = v_pos_5037_;
v_snd_5030_ = v_snd_5039_;
goto v___jp_5028_;
}
}
}
v___jp_5065_:
{
lean_object* v___x_5070_; 
lean_inc_ref(v_pos_5068_);
v___x_5070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5070_, 0, v_pos_5068_);
lean_ctor_set(v___x_5070_, 1, v_err_5069_);
v_snd_5034_ = v_snd_5066_;
v___y_5035_ = v___y_5067_;
v___y_5036_ = v___x_5070_;
v_pos_5037_ = v_pos_5068_;
goto v___jp_5033_;
}
v___jp_5071_:
{
lean_object* v___x_5075_; 
v___x_5075_ = lean_box(0);
v_snd_5066_ = v_snd_5073_;
v___y_5067_ = v___y_5074_;
v_pos_5068_ = v___y_5072_;
v_err_5069_ = v___x_5075_;
goto v___jp_5065_;
}
v___jp_5077_:
{
lean_object* v_fst_5082_; lean_object* v_snd_5083_; uint8_t v_decide_5084_; 
v_fst_5082_ = lean_ctor_get(v_pos_5081_, 0);
v_snd_5083_ = lean_ctor_get(v_pos_5081_, 1);
lean_inc(v_snd_5083_);
v_decide_5084_ = lean_nat_dec_eq(v_snd_5078_, v_snd_5083_);
lean_dec(v_snd_5078_);
if (v_decide_5084_ == 0)
{
lean_dec(v_snd_5083_);
lean_dec_ref(v_pos_5081_);
lean_dec_ref(v___y_5079_);
return v___y_5080_;
}
else
{
lean_object* v___x_5085_; uint8_t v_decide_5086_; 
lean_dec_ref(v___y_5080_);
v___x_5085_ = lean_string_utf8_byte_size(v_fst_5082_);
v_decide_5086_ = lean_nat_dec_eq(v_snd_5083_, v___x_5085_);
if (v_decide_5086_ == 0)
{
if (v_decide_5084_ == 0)
{
v___y_5072_ = v_pos_5081_;
v_snd_5073_ = v_snd_5083_;
v___y_5074_ = v___y_5079_;
goto v___jp_5071_;
}
else
{
uint32_t v___x_5087_; uint32_t v_c_5088_; uint8_t v___x_5089_; 
v___x_5087_ = 109;
v_c_5088_ = lean_string_utf8_get_fast(v_fst_5082_, v_snd_5083_);
v___x_5089_ = lean_uint32_dec_eq(v_c_5088_, v___x_5087_);
if (v___x_5089_ == 0)
{
lean_object* v___x_5090_; 
v___x_5090_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3);
v_snd_5066_ = v_snd_5083_;
v___y_5067_ = v___y_5079_;
v_pos_5068_ = v_pos_5081_;
v_err_5069_ = v___x_5090_;
goto v___jp_5065_;
}
else
{
lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5106_; 
lean_inc(v_fst_5082_);
v_isSharedCheck_5106_ = !lean_is_exclusive(v_pos_5081_);
if (v_isSharedCheck_5106_ == 0)
{
lean_object* v_unused_5107_; lean_object* v_unused_5108_; 
v_unused_5107_ = lean_ctor_get(v_pos_5081_, 1);
lean_dec(v_unused_5107_);
v_unused_5108_ = lean_ctor_get(v_pos_5081_, 0);
lean_dec(v_unused_5108_);
v___x_5092_ = v_pos_5081_;
v_isShared_5093_ = v_isSharedCheck_5106_;
goto v_resetjp_5091_;
}
else
{
lean_dec(v_pos_5081_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5106_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5094_; lean_object* v_it_x27_5096_; 
v___x_5094_ = lean_string_utf8_next_fast(v_fst_5082_, v_snd_5083_);
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 1, v___x_5094_);
v_it_x27_5096_ = v___x_5092_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_fst_5082_);
lean_ctor_set(v_reuseFailAlloc_5105_, 1, v___x_5094_);
v_it_x27_5096_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5097_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0);
v___x_5098_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(v___x_5097_, v_it_x27_5096_);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_object* v_pos_5099_; lean_object* v_res_5100_; lean_object* v___x_5101_; 
v_pos_5099_ = lean_ctor_get(v___x_5098_, 0);
lean_inc(v_pos_5099_);
v_res_5100_ = lean_ctor_get(v___x_5098_, 1);
lean_inc(v_res_5100_);
lean_dec_ref_known(v___x_5098_, 2);
lean_inc_ref(v___y_5079_);
v___x_5101_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5076_, v___y_5079_, v_res_5100_, v_pos_5099_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_dec(v_snd_5083_);
lean_dec_ref(v___y_5079_);
return v___x_5101_;
}
else
{
lean_object* v_pos_5102_; 
v_pos_5102_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_pos_5102_);
v_snd_5034_ = v_snd_5083_;
v___y_5035_ = v___y_5079_;
v___y_5036_ = v___x_5101_;
v_pos_5037_ = v_pos_5102_;
goto v___jp_5033_;
}
}
else
{
lean_object* v_pos_5103_; lean_object* v_err_5104_; 
v_pos_5103_ = lean_ctor_get(v___x_5098_, 0);
lean_inc(v_pos_5103_);
v_err_5104_ = lean_ctor_get(v___x_5098_, 1);
lean_inc(v_err_5104_);
lean_dec_ref_known(v___x_5098_, 2);
v_snd_5066_ = v_snd_5083_;
v___y_5067_ = v___y_5079_;
v_pos_5068_ = v_pos_5103_;
v_err_5069_ = v_err_5104_;
goto v___jp_5065_;
}
}
}
}
}
}
else
{
v___y_5072_ = v_pos_5081_;
v_snd_5073_ = v_snd_5083_;
v___y_5074_ = v___y_5079_;
goto v___jp_5071_;
}
}
}
v___jp_5109_:
{
lean_object* v___x_5114_; 
lean_inc_ref(v_pos_5112_);
v___x_5114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5114_, 0, v_pos_5112_);
lean_ctor_set(v___x_5114_, 1, v_err_5113_);
v_snd_5078_ = v_snd_5110_;
v___y_5079_ = v___y_5111_;
v___y_5080_ = v___x_5114_;
v_pos_5081_ = v_pos_5112_;
goto v___jp_5077_;
}
v___jp_5115_:
{
lean_object* v___x_5119_; 
v___x_5119_ = lean_box(0);
v_snd_5110_ = v_snd_5117_;
v___y_5111_ = v___y_5118_;
v_pos_5112_ = v___y_5116_;
v_err_5113_ = v___x_5119_;
goto v___jp_5109_;
}
v___jp_5121_:
{
lean_object* v_fst_5126_; lean_object* v_snd_5127_; uint8_t v_decide_5128_; 
v_fst_5126_ = lean_ctor_get(v_pos_5125_, 0);
v_snd_5127_ = lean_ctor_get(v_pos_5125_, 1);
lean_inc(v_snd_5127_);
v_decide_5128_ = lean_nat_dec_eq(v_snd_5123_, v_snd_5127_);
lean_dec(v_snd_5123_);
if (v_decide_5128_ == 0)
{
lean_dec(v_snd_5127_);
lean_dec_ref(v_pos_5125_);
lean_dec_ref(v___y_5122_);
return v___y_5124_;
}
else
{
lean_object* v___x_5129_; uint8_t v_decide_5130_; 
lean_dec_ref(v___y_5124_);
v___x_5129_ = lean_string_utf8_byte_size(v_fst_5126_);
v_decide_5130_ = lean_nat_dec_eq(v_snd_5127_, v___x_5129_);
if (v_decide_5130_ == 0)
{
if (v_decide_5128_ == 0)
{
v___y_5116_ = v_pos_5125_;
v_snd_5117_ = v_snd_5127_;
v___y_5118_ = v___y_5122_;
goto v___jp_5115_;
}
else
{
uint32_t v___x_5131_; uint32_t v_c_5132_; uint8_t v___x_5133_; 
v___x_5131_ = 72;
v_c_5132_ = lean_string_utf8_get_fast(v_fst_5126_, v_snd_5127_);
v___x_5133_ = lean_uint32_dec_eq(v_c_5132_, v___x_5131_);
if (v___x_5133_ == 0)
{
lean_object* v___x_5134_; 
v___x_5134_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3);
v_snd_5110_ = v_snd_5127_;
v___y_5111_ = v___y_5122_;
v_pos_5112_ = v_pos_5125_;
v_err_5113_ = v___x_5134_;
goto v___jp_5109_;
}
else
{
lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5150_; 
lean_inc(v_fst_5126_);
v_isSharedCheck_5150_ = !lean_is_exclusive(v_pos_5125_);
if (v_isSharedCheck_5150_ == 0)
{
lean_object* v_unused_5151_; lean_object* v_unused_5152_; 
v_unused_5151_ = lean_ctor_get(v_pos_5125_, 1);
lean_dec(v_unused_5151_);
v_unused_5152_ = lean_ctor_get(v_pos_5125_, 0);
lean_dec(v_unused_5152_);
v___x_5136_ = v_pos_5125_;
v_isShared_5137_ = v_isSharedCheck_5150_;
goto v_resetjp_5135_;
}
else
{
lean_dec(v_pos_5125_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5150_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5138_; lean_object* v_it_x27_5140_; 
v___x_5138_ = lean_string_utf8_next_fast(v_fst_5126_, v_snd_5127_);
if (v_isShared_5137_ == 0)
{
lean_ctor_set(v___x_5136_, 1, v___x_5138_);
v_it_x27_5140_ = v___x_5136_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_fst_5126_);
lean_ctor_set(v_reuseFailAlloc_5149_, 1, v___x_5138_);
v_it_x27_5140_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
lean_object* v___x_5141_; lean_object* v___x_5142_; 
v___x_5141_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0);
v___x_5142_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(v___x_5141_, v_it_x27_5140_);
if (lean_obj_tag(v___x_5142_) == 0)
{
lean_object* v_pos_5143_; lean_object* v_res_5144_; lean_object* v___x_5145_; 
v_pos_5143_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_pos_5143_);
v_res_5144_ = lean_ctor_get(v___x_5142_, 1);
lean_inc(v_res_5144_);
lean_dec_ref_known(v___x_5142_, 2);
lean_inc_ref(v___y_5122_);
v___x_5145_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5120_, v___y_5122_, v_res_5144_, v_pos_5143_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_dec(v_snd_5127_);
lean_dec_ref(v___y_5122_);
return v___x_5145_;
}
else
{
lean_object* v_pos_5146_; 
v_pos_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_pos_5146_);
v_snd_5078_ = v_snd_5127_;
v___y_5079_ = v___y_5122_;
v___y_5080_ = v___x_5145_;
v_pos_5081_ = v_pos_5146_;
goto v___jp_5077_;
}
}
else
{
lean_object* v_pos_5147_; lean_object* v_err_5148_; 
v_pos_5147_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_pos_5147_);
v_err_5148_ = lean_ctor_get(v___x_5142_, 1);
lean_inc(v_err_5148_);
lean_dec_ref_known(v___x_5142_, 2);
v_snd_5110_ = v_snd_5127_;
v___y_5111_ = v___y_5122_;
v_pos_5112_ = v_pos_5147_;
v_err_5113_ = v_err_5148_;
goto v___jp_5109_;
}
}
}
}
}
}
else
{
v___y_5116_ = v_pos_5125_;
v_snd_5117_ = v_snd_5127_;
v___y_5118_ = v___y_5122_;
goto v___jp_5115_;
}
}
}
v___jp_5153_:
{
lean_object* v___x_5158_; 
lean_inc_ref(v_pos_5156_);
v___x_5158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5158_, 0, v_pos_5156_);
lean_ctor_set(v___x_5158_, 1, v_err_5157_);
v___y_5122_ = v___y_5154_;
v_snd_5123_ = v_snd_5155_;
v___y_5124_ = v___x_5158_;
v_pos_5125_ = v_pos_5156_;
goto v___jp_5121_;
}
v___jp_5159_:
{
lean_object* v___x_5163_; 
v___x_5163_ = lean_box(0);
v___y_5154_ = v___y_5160_;
v_snd_5155_ = v_snd_5162_;
v_pos_5156_ = v___y_5161_;
v_err_5157_ = v___x_5163_;
goto v___jp_5153_;
}
v___jp_5165_:
{
lean_object* v_fst_5170_; lean_object* v_snd_5171_; uint8_t v_decide_5172_; 
v_fst_5170_ = lean_ctor_get(v_pos_5169_, 0);
v_snd_5171_ = lean_ctor_get(v_pos_5169_, 1);
lean_inc(v_snd_5171_);
v_decide_5172_ = lean_nat_dec_eq(v_snd_5166_, v_snd_5171_);
lean_dec(v_snd_5166_);
if (v_decide_5172_ == 0)
{
lean_dec(v_snd_5171_);
lean_dec_ref(v_pos_5169_);
lean_dec_ref(v___y_5167_);
return v___y_5168_;
}
else
{
lean_object* v___x_5173_; uint8_t v_decide_5174_; 
lean_dec_ref(v___y_5168_);
v___x_5173_ = lean_string_utf8_byte_size(v_fst_5170_);
v_decide_5174_ = lean_nat_dec_eq(v_snd_5171_, v___x_5173_);
if (v_decide_5174_ == 0)
{
if (v_decide_5172_ == 0)
{
v___y_5160_ = v___y_5167_;
v___y_5161_ = v_pos_5169_;
v_snd_5162_ = v_snd_5171_;
goto v___jp_5159_;
}
else
{
uint32_t v___x_5175_; uint32_t v_c_5176_; uint8_t v___x_5177_; 
v___x_5175_ = 107;
v_c_5176_ = lean_string_utf8_get_fast(v_fst_5170_, v_snd_5171_);
v___x_5177_ = lean_uint32_dec_eq(v_c_5176_, v___x_5175_);
if (v___x_5177_ == 0)
{
lean_object* v___x_5178_; 
v___x_5178_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3);
v___y_5154_ = v___y_5167_;
v_snd_5155_ = v_snd_5171_;
v_pos_5156_ = v_pos_5169_;
v_err_5157_ = v___x_5178_;
goto v___jp_5153_;
}
else
{
lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5194_; 
lean_inc(v_fst_5170_);
v_isSharedCheck_5194_ = !lean_is_exclusive(v_pos_5169_);
if (v_isSharedCheck_5194_ == 0)
{
lean_object* v_unused_5195_; lean_object* v_unused_5196_; 
v_unused_5195_ = lean_ctor_get(v_pos_5169_, 1);
lean_dec(v_unused_5195_);
v_unused_5196_ = lean_ctor_get(v_pos_5169_, 0);
lean_dec(v_unused_5196_);
v___x_5180_ = v_pos_5169_;
v_isShared_5181_ = v_isSharedCheck_5194_;
goto v_resetjp_5179_;
}
else
{
lean_dec(v_pos_5169_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5194_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5182_; lean_object* v_it_x27_5184_; 
v___x_5182_ = lean_string_utf8_next_fast(v_fst_5170_, v_snd_5171_);
if (v_isShared_5181_ == 0)
{
lean_ctor_set(v___x_5180_, 1, v___x_5182_);
v_it_x27_5184_ = v___x_5180_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_fst_5170_);
lean_ctor_set(v_reuseFailAlloc_5193_, 1, v___x_5182_);
v_it_x27_5184_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
lean_object* v___x_5185_; lean_object* v___x_5186_; 
v___x_5185_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0);
v___x_5186_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(v___x_5185_, v_it_x27_5184_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_pos_5187_; lean_object* v_res_5188_; lean_object* v___x_5189_; 
v_pos_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_pos_5187_);
v_res_5188_ = lean_ctor_get(v___x_5186_, 1);
lean_inc(v_res_5188_);
lean_dec_ref_known(v___x_5186_, 2);
lean_inc_ref(v___y_5167_);
v___x_5189_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5164_, v___y_5167_, v_res_5188_, v_pos_5187_);
if (lean_obj_tag(v___x_5189_) == 0)
{
lean_dec(v_snd_5171_);
lean_dec_ref(v___y_5167_);
return v___x_5189_;
}
else
{
lean_object* v_pos_5190_; 
v_pos_5190_ = lean_ctor_get(v___x_5189_, 0);
lean_inc(v_pos_5190_);
v___y_5122_ = v___y_5167_;
v_snd_5123_ = v_snd_5171_;
v___y_5124_ = v___x_5189_;
v_pos_5125_ = v_pos_5190_;
goto v___jp_5121_;
}
}
else
{
lean_object* v_pos_5191_; lean_object* v_err_5192_; 
v_pos_5191_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_pos_5191_);
v_err_5192_ = lean_ctor_get(v___x_5186_, 1);
lean_inc(v_err_5192_);
lean_dec_ref_known(v___x_5186_, 2);
v___y_5154_ = v___y_5167_;
v_snd_5155_ = v_snd_5171_;
v_pos_5156_ = v_pos_5191_;
v_err_5157_ = v_err_5192_;
goto v___jp_5153_;
}
}
}
}
}
}
else
{
v___y_5160_ = v___y_5167_;
v___y_5161_ = v_pos_5169_;
v_snd_5162_ = v_snd_5171_;
goto v___jp_5159_;
}
}
}
v___jp_5197_:
{
lean_object* v___x_5202_; 
lean_inc_ref(v_pos_5200_);
v___x_5202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5202_, 0, v_pos_5200_);
lean_ctor_set(v___x_5202_, 1, v_err_5201_);
v_snd_5166_ = v_snd_5198_;
v___y_5167_ = v___y_5199_;
v___y_5168_ = v___x_5202_;
v_pos_5169_ = v_pos_5200_;
goto v___jp_5165_;
}
v___jp_5203_:
{
lean_object* v___x_5207_; 
v___x_5207_ = lean_box(0);
v_snd_5198_ = v_snd_5205_;
v___y_5199_ = v___y_5206_;
v_pos_5200_ = v___y_5204_;
v_err_5201_ = v___x_5207_;
goto v___jp_5197_;
}
v___jp_5209_:
{
lean_object* v_fst_5214_; lean_object* v_snd_5215_; uint8_t v_decide_5216_; 
v_fst_5214_ = lean_ctor_get(v_pos_5213_, 0);
v_snd_5215_ = lean_ctor_get(v_pos_5213_, 1);
lean_inc(v_snd_5215_);
v_decide_5216_ = lean_nat_dec_eq(v_snd_5210_, v_snd_5215_);
lean_dec(v_snd_5210_);
if (v_decide_5216_ == 0)
{
lean_dec(v_snd_5215_);
lean_dec_ref(v_pos_5213_);
lean_dec_ref(v___y_5211_);
return v___y_5212_;
}
else
{
lean_object* v___x_5217_; uint8_t v_decide_5218_; 
lean_dec_ref(v___y_5212_);
v___x_5217_ = lean_string_utf8_byte_size(v_fst_5214_);
v_decide_5218_ = lean_nat_dec_eq(v_snd_5215_, v___x_5217_);
if (v_decide_5218_ == 0)
{
if (v_decide_5216_ == 0)
{
v___y_5204_ = v_pos_5213_;
v_snd_5205_ = v_snd_5215_;
v___y_5206_ = v___y_5211_;
goto v___jp_5203_;
}
else
{
uint32_t v___x_5219_; uint32_t v_c_5220_; uint8_t v___x_5221_; 
v___x_5219_ = 75;
v_c_5220_ = lean_string_utf8_get_fast(v_fst_5214_, v_snd_5215_);
v___x_5221_ = lean_uint32_dec_eq(v_c_5220_, v___x_5219_);
if (v___x_5221_ == 0)
{
lean_object* v___x_5222_; 
v___x_5222_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3);
v_snd_5198_ = v_snd_5215_;
v___y_5199_ = v___y_5211_;
v_pos_5200_ = v_pos_5213_;
v_err_5201_ = v___x_5222_;
goto v___jp_5197_;
}
else
{
lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5238_; 
lean_inc(v_fst_5214_);
v_isSharedCheck_5238_ = !lean_is_exclusive(v_pos_5213_);
if (v_isSharedCheck_5238_ == 0)
{
lean_object* v_unused_5239_; lean_object* v_unused_5240_; 
v_unused_5239_ = lean_ctor_get(v_pos_5213_, 1);
lean_dec(v_unused_5239_);
v_unused_5240_ = lean_ctor_get(v_pos_5213_, 0);
lean_dec(v_unused_5240_);
v___x_5224_ = v_pos_5213_;
v_isShared_5225_ = v_isSharedCheck_5238_;
goto v_resetjp_5223_;
}
else
{
lean_dec(v_pos_5213_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5238_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5226_; lean_object* v_it_x27_5228_; 
v___x_5226_ = lean_string_utf8_next_fast(v_fst_5214_, v_snd_5215_);
if (v_isShared_5225_ == 0)
{
lean_ctor_set(v___x_5224_, 1, v___x_5226_);
v_it_x27_5228_ = v___x_5224_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_fst_5214_);
lean_ctor_set(v_reuseFailAlloc_5237_, 1, v___x_5226_);
v_it_x27_5228_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
lean_object* v___x_5229_; lean_object* v___x_5230_; 
v___x_5229_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0);
v___x_5230_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(v___x_5229_, v_it_x27_5228_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_pos_5231_; lean_object* v_res_5232_; lean_object* v___x_5233_; 
v_pos_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_pos_5231_);
v_res_5232_ = lean_ctor_get(v___x_5230_, 1);
lean_inc(v_res_5232_);
lean_dec_ref_known(v___x_5230_, 2);
lean_inc_ref(v___y_5211_);
v___x_5233_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5208_, v___y_5211_, v_res_5232_, v_pos_5231_);
if (lean_obj_tag(v___x_5233_) == 0)
{
lean_dec(v_snd_5215_);
lean_dec_ref(v___y_5211_);
return v___x_5233_;
}
else
{
lean_object* v_pos_5234_; 
v_pos_5234_ = lean_ctor_get(v___x_5233_, 0);
lean_inc(v_pos_5234_);
v_snd_5166_ = v_snd_5215_;
v___y_5167_ = v___y_5211_;
v___y_5168_ = v___x_5233_;
v_pos_5169_ = v_pos_5234_;
goto v___jp_5165_;
}
}
else
{
lean_object* v_pos_5235_; lean_object* v_err_5236_; 
v_pos_5235_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_pos_5235_);
v_err_5236_ = lean_ctor_get(v___x_5230_, 1);
lean_inc(v_err_5236_);
lean_dec_ref_known(v___x_5230_, 2);
v_snd_5198_ = v_snd_5215_;
v___y_5199_ = v___y_5211_;
v_pos_5200_ = v_pos_5235_;
v_err_5201_ = v_err_5236_;
goto v___jp_5197_;
}
}
}
}
}
}
else
{
v___y_5204_ = v_pos_5213_;
v_snd_5205_ = v_snd_5215_;
v___y_5206_ = v___y_5211_;
goto v___jp_5203_;
}
}
}
v___jp_5241_:
{
lean_object* v___x_5246_; 
lean_inc_ref(v_pos_5244_);
v___x_5246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5246_, 0, v_pos_5244_);
lean_ctor_set(v___x_5246_, 1, v_err_5245_);
v_snd_5210_ = v_snd_5242_;
v___y_5211_ = v___y_5243_;
v___y_5212_ = v___x_5246_;
v_pos_5213_ = v_pos_5244_;
goto v___jp_5209_;
}
v___jp_5247_:
{
lean_object* v___x_5251_; 
v___x_5251_ = lean_box(0);
v_snd_5242_ = v_snd_5249_;
v___y_5243_ = v___y_5250_;
v_pos_5244_ = v___y_5248_;
v_err_5245_ = v___x_5251_;
goto v___jp_5241_;
}
v___jp_5253_:
{
lean_object* v_fst_5258_; lean_object* v_snd_5259_; uint8_t v_decide_5260_; 
v_fst_5258_ = lean_ctor_get(v_pos_5257_, 0);
v_snd_5259_ = lean_ctor_get(v_pos_5257_, 1);
lean_inc(v_snd_5259_);
v_decide_5260_ = lean_nat_dec_eq(v_snd_5254_, v_snd_5259_);
lean_dec(v_snd_5254_);
if (v_decide_5260_ == 0)
{
lean_dec(v_snd_5259_);
lean_dec_ref(v_pos_5257_);
lean_dec_ref(v___y_5255_);
return v___y_5256_;
}
else
{
lean_object* v___x_5261_; uint8_t v_decide_5262_; 
lean_dec_ref(v___y_5256_);
v___x_5261_ = lean_string_utf8_byte_size(v_fst_5258_);
v_decide_5262_ = lean_nat_dec_eq(v_snd_5259_, v___x_5261_);
if (v_decide_5262_ == 0)
{
if (v_decide_5260_ == 0)
{
v___y_5248_ = v_pos_5257_;
v_snd_5249_ = v_snd_5259_;
v___y_5250_ = v___y_5255_;
goto v___jp_5247_;
}
else
{
uint32_t v___x_5263_; uint32_t v_c_5264_; uint8_t v___x_5265_; 
v___x_5263_ = 104;
v_c_5264_ = lean_string_utf8_get_fast(v_fst_5258_, v_snd_5259_);
v___x_5265_ = lean_uint32_dec_eq(v_c_5264_, v___x_5263_);
if (v___x_5265_ == 0)
{
lean_object* v___x_5266_; 
v___x_5266_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3);
v_snd_5242_ = v_snd_5259_;
v___y_5243_ = v___y_5255_;
v_pos_5244_ = v_pos_5257_;
v_err_5245_ = v___x_5266_;
goto v___jp_5241_;
}
else
{
lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5282_; 
lean_inc(v_fst_5258_);
v_isSharedCheck_5282_ = !lean_is_exclusive(v_pos_5257_);
if (v_isSharedCheck_5282_ == 0)
{
lean_object* v_unused_5283_; lean_object* v_unused_5284_; 
v_unused_5283_ = lean_ctor_get(v_pos_5257_, 1);
lean_dec(v_unused_5283_);
v_unused_5284_ = lean_ctor_get(v_pos_5257_, 0);
lean_dec(v_unused_5284_);
v___x_5268_ = v_pos_5257_;
v_isShared_5269_ = v_isSharedCheck_5282_;
goto v_resetjp_5267_;
}
else
{
lean_dec(v_pos_5257_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5282_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v___x_5270_; lean_object* v_it_x27_5272_; 
v___x_5270_ = lean_string_utf8_next_fast(v_fst_5258_, v_snd_5259_);
if (v_isShared_5269_ == 0)
{
lean_ctor_set(v___x_5268_, 1, v___x_5270_);
v_it_x27_5272_ = v___x_5268_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_fst_5258_);
lean_ctor_set(v_reuseFailAlloc_5281_, 1, v___x_5270_);
v_it_x27_5272_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
lean_object* v___x_5273_; lean_object* v___x_5274_; 
v___x_5273_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0);
v___x_5274_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(v___x_5273_, v_it_x27_5272_);
if (lean_obj_tag(v___x_5274_) == 0)
{
lean_object* v_pos_5275_; lean_object* v_res_5276_; lean_object* v___x_5277_; 
v_pos_5275_ = lean_ctor_get(v___x_5274_, 0);
lean_inc(v_pos_5275_);
v_res_5276_ = lean_ctor_get(v___x_5274_, 1);
lean_inc(v_res_5276_);
lean_dec_ref_known(v___x_5274_, 2);
lean_inc_ref(v___y_5255_);
v___x_5277_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5252_, v___y_5255_, v_res_5276_, v_pos_5275_);
if (lean_obj_tag(v___x_5277_) == 0)
{
lean_dec(v_snd_5259_);
lean_dec_ref(v___y_5255_);
return v___x_5277_;
}
else
{
lean_object* v_pos_5278_; 
v_pos_5278_ = lean_ctor_get(v___x_5277_, 0);
lean_inc(v_pos_5278_);
v_snd_5210_ = v_snd_5259_;
v___y_5211_ = v___y_5255_;
v___y_5212_ = v___x_5277_;
v_pos_5213_ = v_pos_5278_;
goto v___jp_5209_;
}
}
else
{
lean_object* v_pos_5279_; lean_object* v_err_5280_; 
v_pos_5279_ = lean_ctor_get(v___x_5274_, 0);
lean_inc(v_pos_5279_);
v_err_5280_ = lean_ctor_get(v___x_5274_, 1);
lean_inc(v_err_5280_);
lean_dec_ref_known(v___x_5274_, 2);
v_snd_5242_ = v_snd_5259_;
v___y_5243_ = v___y_5255_;
v_pos_5244_ = v_pos_5279_;
v_err_5245_ = v_err_5280_;
goto v___jp_5241_;
}
}
}
}
}
}
else
{
v___y_5248_ = v_pos_5257_;
v_snd_5249_ = v_snd_5259_;
v___y_5250_ = v___y_5255_;
goto v___jp_5247_;
}
}
}
v___jp_5285_:
{
lean_object* v___x_5290_; 
lean_inc_ref(v_pos_5288_);
v___x_5290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5290_, 0, v_pos_5288_);
lean_ctor_set(v___x_5290_, 1, v_err_5289_);
v_snd_5254_ = v_snd_5286_;
v___y_5255_ = v___y_5287_;
v___y_5256_ = v___x_5290_;
v_pos_5257_ = v_pos_5288_;
goto v___jp_5253_;
}
v___jp_5291_:
{
lean_object* v___x_5295_; 
v___x_5295_ = lean_box(0);
v_snd_5286_ = v_snd_5293_;
v___y_5287_ = v___y_5294_;
v_pos_5288_ = v___y_5292_;
v_err_5289_ = v___x_5295_;
goto v___jp_5285_;
}
v___jp_5296_:
{
lean_object* v_fst_5301_; lean_object* v_snd_5302_; uint8_t v_decide_5303_; 
v_fst_5301_ = lean_ctor_get(v_pos_5300_, 0);
v_snd_5302_ = lean_ctor_get(v_pos_5300_, 1);
lean_inc(v_snd_5302_);
v_decide_5303_ = lean_nat_dec_eq(v_snd_5297_, v_snd_5302_);
lean_dec(v_snd_5297_);
if (v_decide_5303_ == 0)
{
lean_dec(v_snd_5302_);
lean_dec_ref(v_pos_5300_);
lean_dec_ref(v___y_5298_);
return v___y_5299_;
}
else
{
lean_object* v___x_5304_; uint8_t v_decide_5305_; 
lean_dec_ref(v___y_5299_);
v___x_5304_ = lean_string_utf8_byte_size(v_fst_5301_);
v_decide_5305_ = lean_nat_dec_eq(v_snd_5302_, v___x_5304_);
if (v_decide_5305_ == 0)
{
if (v_decide_5303_ == 0)
{
v___y_5292_ = v_pos_5300_;
v_snd_5293_ = v_snd_5302_;
v___y_5294_ = v___y_5298_;
goto v___jp_5291_;
}
else
{
uint32_t v___x_5306_; uint32_t v_c_5307_; uint8_t v___x_5308_; 
v___x_5306_ = 66;
v_c_5307_ = lean_string_utf8_get_fast(v_fst_5301_, v_snd_5302_);
v___x_5308_ = lean_uint32_dec_eq(v_c_5307_, v___x_5306_);
if (v___x_5308_ == 0)
{
lean_object* v___x_5309_; 
v___x_5309_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3);
v_snd_5286_ = v_snd_5302_;
v___y_5287_ = v___y_5298_;
v_pos_5288_ = v_pos_5300_;
v_err_5289_ = v___x_5309_;
goto v___jp_5285_;
}
else
{
lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5325_; 
lean_inc(v_fst_5301_);
v_isSharedCheck_5325_ = !lean_is_exclusive(v_pos_5300_);
if (v_isSharedCheck_5325_ == 0)
{
lean_object* v_unused_5326_; lean_object* v_unused_5327_; 
v_unused_5326_ = lean_ctor_get(v_pos_5300_, 1);
lean_dec(v_unused_5326_);
v_unused_5327_ = lean_ctor_get(v_pos_5300_, 0);
lean_dec(v_unused_5327_);
v___x_5311_ = v_pos_5300_;
v_isShared_5312_ = v_isSharedCheck_5325_;
goto v_resetjp_5310_;
}
else
{
lean_dec(v_pos_5300_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5325_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
lean_object* v___x_5313_; lean_object* v_it_x27_5315_; 
v___x_5313_ = lean_string_utf8_next_fast(v_fst_5301_, v_snd_5302_);
if (v_isShared_5312_ == 0)
{
lean_ctor_set(v___x_5311_, 1, v___x_5313_);
v_it_x27_5315_ = v___x_5311_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_fst_5301_);
lean_ctor_set(v_reuseFailAlloc_5324_, 1, v___x_5313_);
v_it_x27_5315_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; 
v___x_5316_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0);
v___x_5317_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(v___x_5316_, v_it_x27_5315_);
if (lean_obj_tag(v___x_5317_) == 0)
{
lean_object* v_pos_5318_; lean_object* v_res_5319_; lean_object* v___x_5320_; 
v_pos_5318_ = lean_ctor_get(v___x_5317_, 0);
lean_inc(v_pos_5318_);
v_res_5319_ = lean_ctor_get(v___x_5317_, 1);
lean_inc(v_res_5319_);
lean_dec_ref_known(v___x_5317_, 2);
v___x_5320_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(v_res_5319_, v_pos_5318_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_dec(v_snd_5302_);
lean_dec_ref(v___y_5298_);
return v___x_5320_;
}
else
{
lean_object* v_pos_5321_; 
v_pos_5321_ = lean_ctor_get(v___x_5320_, 0);
lean_inc(v_pos_5321_);
v_snd_5254_ = v_snd_5302_;
v___y_5255_ = v___y_5298_;
v___y_5256_ = v___x_5320_;
v_pos_5257_ = v_pos_5321_;
goto v___jp_5253_;
}
}
else
{
lean_object* v_pos_5322_; lean_object* v_err_5323_; 
v_pos_5322_ = lean_ctor_get(v___x_5317_, 0);
lean_inc(v_pos_5322_);
v_err_5323_ = lean_ctor_get(v___x_5317_, 1);
lean_inc(v_err_5323_);
lean_dec_ref_known(v___x_5317_, 2);
v_snd_5286_ = v_snd_5302_;
v___y_5287_ = v___y_5298_;
v_pos_5288_ = v_pos_5322_;
v_err_5289_ = v_err_5323_;
goto v___jp_5285_;
}
}
}
}
}
}
else
{
v___y_5292_ = v_pos_5300_;
v_snd_5293_ = v_snd_5302_;
v___y_5294_ = v___y_5298_;
goto v___jp_5291_;
}
}
}
v___jp_5328_:
{
lean_object* v___x_5333_; 
lean_inc_ref(v_pos_5331_);
v___x_5333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5333_, 0, v_pos_5331_);
lean_ctor_set(v___x_5333_, 1, v_err_5332_);
v_snd_5297_ = v_snd_5329_;
v___y_5298_ = v___y_5330_;
v___y_5299_ = v___x_5333_;
v_pos_5300_ = v_pos_5331_;
goto v___jp_5296_;
}
v___jp_5334_:
{
lean_object* v___x_5338_; 
v___x_5338_ = lean_box(0);
v_snd_5329_ = v_snd_5336_;
v___y_5330_ = v___y_5337_;
v_pos_5331_ = v___y_5335_;
v_err_5332_ = v___x_5338_;
goto v___jp_5328_;
}
v___jp_5339_:
{
lean_object* v_fst_5344_; lean_object* v_snd_5345_; uint8_t v_decide_5346_; 
v_fst_5344_ = lean_ctor_get(v_pos_5343_, 0);
v_snd_5345_ = lean_ctor_get(v_pos_5343_, 1);
lean_inc(v_snd_5345_);
v_decide_5346_ = lean_nat_dec_eq(v_snd_5340_, v_snd_5345_);
lean_dec(v_snd_5340_);
if (v_decide_5346_ == 0)
{
lean_dec(v_snd_5345_);
lean_dec_ref(v_pos_5343_);
lean_dec_ref(v___y_5341_);
return v___y_5342_;
}
else
{
lean_object* v___x_5347_; uint8_t v_decide_5348_; 
lean_dec_ref(v___y_5342_);
v___x_5347_ = lean_string_utf8_byte_size(v_fst_5344_);
v_decide_5348_ = lean_nat_dec_eq(v_snd_5345_, v___x_5347_);
if (v_decide_5348_ == 0)
{
if (v_decide_5346_ == 0)
{
v___y_5335_ = v_pos_5343_;
v_snd_5336_ = v_snd_5345_;
v___y_5337_ = v___y_5341_;
goto v___jp_5334_;
}
else
{
uint32_t v___x_5349_; uint32_t v_c_5350_; uint8_t v___x_5351_; 
v___x_5349_ = 98;
v_c_5350_ = lean_string_utf8_get_fast(v_fst_5344_, v_snd_5345_);
v___x_5351_ = lean_uint32_dec_eq(v_c_5350_, v___x_5349_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5352_; 
v___x_5352_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3);
v_snd_5329_ = v_snd_5345_;
v___y_5330_ = v___y_5341_;
v_pos_5331_ = v_pos_5343_;
v_err_5332_ = v___x_5352_;
goto v___jp_5328_;
}
else
{
lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5368_; 
lean_inc(v_fst_5344_);
v_isSharedCheck_5368_ = !lean_is_exclusive(v_pos_5343_);
if (v_isSharedCheck_5368_ == 0)
{
lean_object* v_unused_5369_; lean_object* v_unused_5370_; 
v_unused_5369_ = lean_ctor_get(v_pos_5343_, 1);
lean_dec(v_unused_5369_);
v_unused_5370_ = lean_ctor_get(v_pos_5343_, 0);
lean_dec(v_unused_5370_);
v___x_5354_ = v_pos_5343_;
v_isShared_5355_ = v_isSharedCheck_5368_;
goto v_resetjp_5353_;
}
else
{
lean_dec(v_pos_5343_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5368_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5356_; lean_object* v_it_x27_5358_; 
v___x_5356_ = lean_string_utf8_next_fast(v_fst_5344_, v_snd_5345_);
if (v_isShared_5355_ == 0)
{
lean_ctor_set(v___x_5354_, 1, v___x_5356_);
v_it_x27_5358_ = v___x_5354_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_fst_5344_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v___x_5356_);
v_it_x27_5358_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
lean_object* v___x_5359_; lean_object* v___x_5360_; 
v___x_5359_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0);
v___x_5360_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(v___x_5359_, v_it_x27_5358_);
if (lean_obj_tag(v___x_5360_) == 0)
{
lean_object* v_pos_5361_; lean_object* v_res_5362_; lean_object* v___x_5363_; 
v_pos_5361_ = lean_ctor_get(v___x_5360_, 0);
lean_inc(v_pos_5361_);
v_res_5362_ = lean_ctor_get(v___x_5360_, 1);
lean_inc(v_res_5362_);
lean_dec_ref_known(v___x_5360_, 2);
v___x_5363_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(v_res_5362_, v_pos_5361_);
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_dec(v_snd_5345_);
lean_dec_ref(v___y_5341_);
return v___x_5363_;
}
else
{
lean_object* v_pos_5364_; 
v_pos_5364_ = lean_ctor_get(v___x_5363_, 0);
lean_inc(v_pos_5364_);
v_snd_5297_ = v_snd_5345_;
v___y_5298_ = v___y_5341_;
v___y_5299_ = v___x_5363_;
v_pos_5300_ = v_pos_5364_;
goto v___jp_5296_;
}
}
else
{
lean_object* v_pos_5365_; lean_object* v_err_5366_; 
v_pos_5365_ = lean_ctor_get(v___x_5360_, 0);
lean_inc(v_pos_5365_);
v_err_5366_ = lean_ctor_get(v___x_5360_, 1);
lean_inc(v_err_5366_);
lean_dec_ref_known(v___x_5360_, 2);
v_snd_5329_ = v_snd_5345_;
v___y_5330_ = v___y_5341_;
v_pos_5331_ = v_pos_5365_;
v_err_5332_ = v_err_5366_;
goto v___jp_5328_;
}
}
}
}
}
}
else
{
v___y_5335_ = v_pos_5343_;
v_snd_5336_ = v_snd_5345_;
v___y_5337_ = v___y_5341_;
goto v___jp_5334_;
}
}
}
v___jp_5371_:
{
lean_object* v___x_5376_; 
lean_inc_ref(v_pos_5374_);
v___x_5376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5376_, 0, v_pos_5374_);
lean_ctor_set(v___x_5376_, 1, v_err_5375_);
v_snd_5340_ = v_snd_5372_;
v___y_5341_ = v___y_5373_;
v___y_5342_ = v___x_5376_;
v_pos_5343_ = v_pos_5374_;
goto v___jp_5339_;
}
v___jp_5377_:
{
lean_object* v___x_5381_; 
v___x_5381_ = lean_box(0);
v_snd_5372_ = v_snd_5379_;
v___y_5373_ = v___y_5380_;
v_pos_5374_ = v___y_5378_;
v_err_5375_ = v___x_5381_;
goto v___jp_5371_;
}
v___jp_5382_:
{
lean_object* v_fst_5387_; lean_object* v_snd_5388_; uint8_t v_decide_5389_; 
v_fst_5387_ = lean_ctor_get(v_pos_5386_, 0);
v_snd_5388_ = lean_ctor_get(v_pos_5386_, 1);
lean_inc(v_snd_5388_);
v_decide_5389_ = lean_nat_dec_eq(v_snd_5384_, v_snd_5388_);
lean_dec(v_snd_5384_);
if (v_decide_5389_ == 0)
{
lean_dec(v_snd_5388_);
lean_dec_ref(v_pos_5386_);
lean_dec_ref(v___y_5383_);
return v___y_5385_;
}
else
{
lean_object* v___x_5390_; uint8_t v_decide_5391_; 
lean_dec_ref(v___y_5385_);
v___x_5390_ = lean_string_utf8_byte_size(v_fst_5387_);
v_decide_5391_ = lean_nat_dec_eq(v_snd_5388_, v___x_5390_);
if (v_decide_5391_ == 0)
{
if (v_decide_5389_ == 0)
{
v___y_5378_ = v_pos_5386_;
v_snd_5379_ = v_snd_5388_;
v___y_5380_ = v___y_5383_;
goto v___jp_5377_;
}
else
{
uint32_t v___x_5392_; uint32_t v_c_5393_; uint8_t v___x_5394_; 
v___x_5392_ = 97;
v_c_5393_ = lean_string_utf8_get_fast(v_fst_5387_, v_snd_5388_);
v___x_5394_ = lean_uint32_dec_eq(v_c_5393_, v___x_5392_);
if (v___x_5394_ == 0)
{
lean_object* v___x_5395_; 
v___x_5395_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3);
v_snd_5372_ = v_snd_5388_;
v___y_5373_ = v___y_5383_;
v_pos_5374_ = v_pos_5386_;
v_err_5375_ = v___x_5395_;
goto v___jp_5371_;
}
else
{
lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5411_; 
lean_inc(v_fst_5387_);
v_isSharedCheck_5411_ = !lean_is_exclusive(v_pos_5386_);
if (v_isSharedCheck_5411_ == 0)
{
lean_object* v_unused_5412_; lean_object* v_unused_5413_; 
v_unused_5412_ = lean_ctor_get(v_pos_5386_, 1);
lean_dec(v_unused_5412_);
v_unused_5413_ = lean_ctor_get(v_pos_5386_, 0);
lean_dec(v_unused_5413_);
v___x_5397_ = v_pos_5386_;
v_isShared_5398_ = v_isSharedCheck_5411_;
goto v_resetjp_5396_;
}
else
{
lean_dec(v_pos_5386_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5411_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5399_; lean_object* v_it_x27_5401_; 
v___x_5399_ = lean_string_utf8_next_fast(v_fst_5387_, v_snd_5388_);
if (v_isShared_5398_ == 0)
{
lean_ctor_set(v___x_5397_, 1, v___x_5399_);
v_it_x27_5401_ = v___x_5397_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_fst_5387_);
lean_ctor_set(v_reuseFailAlloc_5410_, 1, v___x_5399_);
v_it_x27_5401_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5402_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0);
v___x_5403_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(v___x_5402_, v_it_x27_5401_);
if (lean_obj_tag(v___x_5403_) == 0)
{
lean_object* v_pos_5404_; lean_object* v_res_5405_; lean_object* v___x_5406_; 
v_pos_5404_ = lean_ctor_get(v___x_5403_, 0);
lean_inc(v_pos_5404_);
v_res_5405_ = lean_ctor_get(v___x_5403_, 1);
lean_inc(v_res_5405_);
lean_dec_ref_known(v___x_5403_, 2);
v___x_5406_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(v_res_5405_, v_pos_5404_);
if (lean_obj_tag(v___x_5406_) == 0)
{
lean_dec(v_snd_5388_);
lean_dec_ref(v___y_5383_);
return v___x_5406_;
}
else
{
lean_object* v_pos_5407_; 
v_pos_5407_ = lean_ctor_get(v___x_5406_, 0);
lean_inc(v_pos_5407_);
v_snd_5340_ = v_snd_5388_;
v___y_5341_ = v___y_5383_;
v___y_5342_ = v___x_5406_;
v_pos_5343_ = v_pos_5407_;
goto v___jp_5339_;
}
}
else
{
lean_object* v_pos_5408_; lean_object* v_err_5409_; 
v_pos_5408_ = lean_ctor_get(v___x_5403_, 0);
lean_inc(v_pos_5408_);
v_err_5409_ = lean_ctor_get(v___x_5403_, 1);
lean_inc(v_err_5409_);
lean_dec_ref_known(v___x_5403_, 2);
v_snd_5372_ = v_snd_5388_;
v___y_5373_ = v___y_5383_;
v_pos_5374_ = v_pos_5408_;
v_err_5375_ = v_err_5409_;
goto v___jp_5371_;
}
}
}
}
}
}
else
{
v___y_5378_ = v_pos_5386_;
v_snd_5379_ = v_snd_5388_;
v___y_5380_ = v___y_5383_;
goto v___jp_5377_;
}
}
}
v___jp_5414_:
{
lean_object* v___x_5419_; 
lean_inc_ref(v_pos_5417_);
v___x_5419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5419_, 0, v_pos_5417_);
lean_ctor_set(v___x_5419_, 1, v_err_5418_);
v___y_5383_ = v___y_5415_;
v_snd_5384_ = v_snd_5416_;
v___y_5385_ = v___x_5419_;
v_pos_5386_ = v_pos_5417_;
goto v___jp_5382_;
}
v___jp_5420_:
{
lean_object* v___x_5424_; 
v___x_5424_ = lean_box(0);
v___y_5415_ = v___y_5421_;
v_snd_5416_ = v_snd_5423_;
v_pos_5417_ = v___y_5422_;
v_err_5418_ = v___x_5424_;
goto v___jp_5414_;
}
v___jp_5426_:
{
lean_object* v_fst_5432_; lean_object* v_snd_5433_; uint8_t v_decide_5434_; 
v_fst_5432_ = lean_ctor_get(v_pos_5431_, 0);
v_snd_5433_ = lean_ctor_get(v_pos_5431_, 1);
lean_inc(v_snd_5433_);
v_decide_5434_ = lean_nat_dec_eq(v_snd_5428_, v_snd_5433_);
lean_dec(v_snd_5428_);
if (v_decide_5434_ == 0)
{
lean_dec(v_snd_5433_);
lean_dec_ref(v_pos_5431_);
lean_dec_ref(v___y_5429_);
lean_dec_ref(v___y_5427_);
return v___y_5430_;
}
else
{
lean_object* v___x_5435_; uint8_t v_decide_5436_; 
lean_dec_ref(v___y_5430_);
v___x_5435_ = lean_string_utf8_byte_size(v_fst_5432_);
v_decide_5436_ = lean_nat_dec_eq(v_snd_5433_, v___x_5435_);
if (v_decide_5436_ == 0)
{
if (v_decide_5434_ == 0)
{
lean_dec_ref(v___y_5427_);
v___y_5421_ = v___y_5429_;
v___y_5422_ = v_pos_5431_;
v_snd_5423_ = v_snd_5433_;
goto v___jp_5420_;
}
else
{
uint32_t v___x_5437_; uint32_t v_c_5438_; uint8_t v___x_5439_; 
v___x_5437_ = 70;
v_c_5438_ = lean_string_utf8_get_fast(v_fst_5432_, v_snd_5433_);
v___x_5439_ = lean_uint32_dec_eq(v_c_5438_, v___x_5437_);
if (v___x_5439_ == 0)
{
lean_object* v___x_5440_; 
lean_dec_ref(v___y_5427_);
v___x_5440_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3);
v___y_5415_ = v___y_5429_;
v_snd_5416_ = v_snd_5433_;
v_pos_5417_ = v_pos_5431_;
v_err_5418_ = v___x_5440_;
goto v___jp_5414_;
}
else
{
lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5456_; 
lean_inc(v_fst_5432_);
v_isSharedCheck_5456_ = !lean_is_exclusive(v_pos_5431_);
if (v_isSharedCheck_5456_ == 0)
{
lean_object* v_unused_5457_; lean_object* v_unused_5458_; 
v_unused_5457_ = lean_ctor_get(v_pos_5431_, 1);
lean_dec(v_unused_5457_);
v_unused_5458_ = lean_ctor_get(v_pos_5431_, 0);
lean_dec(v_unused_5458_);
v___x_5442_ = v_pos_5431_;
v_isShared_5443_ = v_isSharedCheck_5456_;
goto v_resetjp_5441_;
}
else
{
lean_dec(v_pos_5431_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5456_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
lean_object* v___x_5444_; lean_object* v_it_x27_5446_; 
v___x_5444_ = lean_string_utf8_next_fast(v_fst_5432_, v_snd_5433_);
if (v_isShared_5443_ == 0)
{
lean_ctor_set(v___x_5442_, 1, v___x_5444_);
v_it_x27_5446_ = v___x_5442_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5455_; 
v_reuseFailAlloc_5455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_fst_5432_);
lean_ctor_set(v_reuseFailAlloc_5455_, 1, v___x_5444_);
v_it_x27_5446_ = v_reuseFailAlloc_5455_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5447_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0);
v___x_5448_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(v___x_5447_, v_it_x27_5446_);
if (lean_obj_tag(v___x_5448_) == 0)
{
lean_object* v_pos_5449_; lean_object* v_res_5450_; lean_object* v___x_5451_; 
v_pos_5449_ = lean_ctor_get(v___x_5448_, 0);
lean_inc(v_pos_5449_);
v_res_5450_ = lean_ctor_get(v___x_5448_, 1);
lean_inc(v_res_5450_);
lean_dec_ref_known(v___x_5448_, 2);
v___x_5451_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5425_, v___y_5427_, v_res_5450_, v_pos_5449_);
if (lean_obj_tag(v___x_5451_) == 0)
{
lean_dec(v_snd_5433_);
lean_dec_ref(v___y_5429_);
return v___x_5451_;
}
else
{
lean_object* v_pos_5452_; 
v_pos_5452_ = lean_ctor_get(v___x_5451_, 0);
lean_inc(v_pos_5452_);
v___y_5383_ = v___y_5429_;
v_snd_5384_ = v_snd_5433_;
v___y_5385_ = v___x_5451_;
v_pos_5386_ = v_pos_5452_;
goto v___jp_5382_;
}
}
else
{
lean_object* v_pos_5453_; lean_object* v_err_5454_; 
lean_dec_ref(v___y_5427_);
v_pos_5453_ = lean_ctor_get(v___x_5448_, 0);
lean_inc(v_pos_5453_);
v_err_5454_ = lean_ctor_get(v___x_5448_, 1);
lean_inc(v_err_5454_);
lean_dec_ref_known(v___x_5448_, 2);
v___y_5415_ = v___y_5429_;
v_snd_5416_ = v_snd_5433_;
v_pos_5417_ = v_pos_5453_;
v_err_5418_ = v_err_5454_;
goto v___jp_5414_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_5427_);
v___y_5421_ = v___y_5429_;
v___y_5422_ = v_pos_5431_;
v_snd_5423_ = v_snd_5433_;
goto v___jp_5420_;
}
}
}
v___jp_5459_:
{
lean_object* v___x_5465_; 
lean_inc_ref(v_pos_5463_);
v___x_5465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5465_, 0, v_pos_5463_);
lean_ctor_set(v___x_5465_, 1, v_err_5464_);
v___y_5427_ = v___y_5460_;
v_snd_5428_ = v_snd_5461_;
v___y_5429_ = v___y_5462_;
v___y_5430_ = v___x_5465_;
v_pos_5431_ = v_pos_5463_;
goto v___jp_5426_;
}
v___jp_5466_:
{
lean_object* v___x_5471_; 
v___x_5471_ = lean_box(0);
v___y_5460_ = v___y_5467_;
v_snd_5461_ = v_snd_5469_;
v___y_5462_ = v___y_5470_;
v_pos_5463_ = v___y_5468_;
v_err_5464_ = v___x_5471_;
goto v___jp_5459_;
}
v___jp_5473_:
{
lean_object* v_fst_5479_; lean_object* v_snd_5480_; uint8_t v_decide_5481_; 
v_fst_5479_ = lean_ctor_get(v_pos_5478_, 0);
v_snd_5480_ = lean_ctor_get(v_pos_5478_, 1);
lean_inc(v_snd_5480_);
v_decide_5481_ = lean_nat_dec_eq(v_snd_5475_, v_snd_5480_);
lean_dec(v_snd_5475_);
if (v_decide_5481_ == 0)
{
lean_dec(v_snd_5480_);
lean_dec_ref(v_pos_5478_);
lean_dec_ref(v___y_5476_);
lean_dec_ref(v___y_5474_);
return v___y_5477_;
}
else
{
lean_object* v___x_5482_; uint8_t v_decide_5483_; 
lean_dec_ref(v___y_5477_);
v___x_5482_ = lean_string_utf8_byte_size(v_fst_5479_);
v_decide_5483_ = lean_nat_dec_eq(v_snd_5480_, v___x_5482_);
if (v_decide_5483_ == 0)
{
if (v_decide_5481_ == 0)
{
v___y_5467_ = v___y_5474_;
v___y_5468_ = v_pos_5478_;
v_snd_5469_ = v_snd_5480_;
v___y_5470_ = v___y_5476_;
goto v___jp_5466_;
}
else
{
uint32_t v___x_5484_; uint32_t v_c_5485_; uint8_t v___x_5486_; 
v___x_5484_ = 99;
v_c_5485_ = lean_string_utf8_get_fast(v_fst_5479_, v_snd_5480_);
v___x_5486_ = lean_uint32_dec_eq(v_c_5485_, v___x_5484_);
if (v___x_5486_ == 0)
{
lean_object* v___x_5487_; 
v___x_5487_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3);
v___y_5460_ = v___y_5474_;
v_snd_5461_ = v_snd_5480_;
v___y_5462_ = v___y_5476_;
v_pos_5463_ = v_pos_5478_;
v_err_5464_ = v___x_5487_;
goto v___jp_5459_;
}
else
{
lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5503_; 
lean_inc(v_fst_5479_);
v_isSharedCheck_5503_ = !lean_is_exclusive(v_pos_5478_);
if (v_isSharedCheck_5503_ == 0)
{
lean_object* v_unused_5504_; lean_object* v_unused_5505_; 
v_unused_5504_ = lean_ctor_get(v_pos_5478_, 1);
lean_dec(v_unused_5504_);
v_unused_5505_ = lean_ctor_get(v_pos_5478_, 0);
lean_dec(v_unused_5505_);
v___x_5489_ = v_pos_5478_;
v_isShared_5490_ = v_isSharedCheck_5503_;
goto v_resetjp_5488_;
}
else
{
lean_dec(v_pos_5478_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5503_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5491_; lean_object* v_it_x27_5493_; 
v___x_5491_ = lean_string_utf8_next_fast(v_fst_5479_, v_snd_5480_);
if (v_isShared_5490_ == 0)
{
lean_ctor_set(v___x_5489_, 1, v___x_5491_);
v_it_x27_5493_ = v___x_5489_;
goto v_reusejp_5492_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v_fst_5479_);
lean_ctor_set(v_reuseFailAlloc_5502_, 1, v___x_5491_);
v_it_x27_5493_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5492_;
}
v_reusejp_5492_:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5494_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0);
v___x_5495_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(v___x_5494_, v_it_x27_5493_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_pos_5496_; lean_object* v_res_5497_; lean_object* v___x_5498_; 
v_pos_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_pos_5496_);
v_res_5497_ = lean_ctor_get(v___x_5495_, 1);
lean_inc(v_res_5497_);
lean_dec_ref_known(v___x_5495_, 2);
v___x_5498_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(v___f_5472_, v_res_5497_, v_pos_5496_);
if (lean_obj_tag(v___x_5498_) == 0)
{
lean_dec(v_snd_5480_);
lean_dec_ref(v___y_5476_);
lean_dec_ref(v___y_5474_);
return v___x_5498_;
}
else
{
lean_object* v_pos_5499_; 
v_pos_5499_ = lean_ctor_get(v___x_5498_, 0);
lean_inc(v_pos_5499_);
v___y_5427_ = v___y_5474_;
v_snd_5428_ = v_snd_5480_;
v___y_5429_ = v___y_5476_;
v___y_5430_ = v___x_5498_;
v_pos_5431_ = v_pos_5499_;
goto v___jp_5426_;
}
}
else
{
lean_object* v_pos_5500_; lean_object* v_err_5501_; 
v_pos_5500_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_pos_5500_);
v_err_5501_ = lean_ctor_get(v___x_5495_, 1);
lean_inc(v_err_5501_);
lean_dec_ref_known(v___x_5495_, 2);
v___y_5460_ = v___y_5474_;
v_snd_5461_ = v_snd_5480_;
v___y_5462_ = v___y_5476_;
v_pos_5463_ = v_pos_5500_;
v_err_5464_ = v_err_5501_;
goto v___jp_5459_;
}
}
}
}
}
}
else
{
v___y_5467_ = v___y_5474_;
v___y_5468_ = v_pos_5478_;
v_snd_5469_ = v_snd_5480_;
v___y_5470_ = v___y_5476_;
goto v___jp_5466_;
}
}
}
v___jp_5506_:
{
lean_object* v___x_5512_; 
lean_inc_ref(v_pos_5510_);
v___x_5512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5512_, 0, v_pos_5510_);
lean_ctor_set(v___x_5512_, 1, v_err_5511_);
v___y_5474_ = v___y_5507_;
v_snd_5475_ = v_snd_5509_;
v___y_5476_ = v___y_5508_;
v___y_5477_ = v___x_5512_;
v_pos_5478_ = v_pos_5510_;
goto v___jp_5473_;
}
v___jp_5513_:
{
lean_object* v___x_5518_; 
v___x_5518_ = lean_box(0);
v___y_5507_ = v___y_5514_;
v___y_5508_ = v___y_5515_;
v_snd_5509_ = v_snd_5517_;
v_pos_5510_ = v___y_5516_;
v_err_5511_ = v___x_5518_;
goto v___jp_5506_;
}
v___jp_5520_:
{
lean_object* v_fst_5526_; lean_object* v_snd_5527_; uint8_t v_decide_5528_; 
v_fst_5526_ = lean_ctor_get(v_pos_5525_, 0);
v_snd_5527_ = lean_ctor_get(v_pos_5525_, 1);
lean_inc(v_snd_5527_);
v_decide_5528_ = lean_nat_dec_eq(v_snd_5522_, v_snd_5527_);
lean_dec(v_snd_5522_);
if (v_decide_5528_ == 0)
{
lean_dec(v_snd_5527_);
lean_dec_ref(v_pos_5525_);
lean_dec_ref(v___y_5523_);
lean_dec_ref(v___y_5521_);
return v___y_5524_;
}
else
{
lean_object* v___x_5529_; uint8_t v_decide_5530_; 
lean_dec_ref(v___y_5524_);
v___x_5529_ = lean_string_utf8_byte_size(v_fst_5526_);
v_decide_5530_ = lean_nat_dec_eq(v_snd_5527_, v___x_5529_);
if (v_decide_5530_ == 0)
{
if (v_decide_5528_ == 0)
{
v___y_5514_ = v___y_5521_;
v___y_5515_ = v___y_5523_;
v___y_5516_ = v_pos_5525_;
v_snd_5517_ = v_snd_5527_;
goto v___jp_5513_;
}
else
{
uint32_t v___x_5531_; uint32_t v_c_5532_; uint8_t v___x_5533_; 
v___x_5531_ = 101;
v_c_5532_ = lean_string_utf8_get_fast(v_fst_5526_, v_snd_5527_);
v___x_5533_ = lean_uint32_dec_eq(v_c_5532_, v___x_5531_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; 
v___x_5534_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3);
v___y_5507_ = v___y_5521_;
v___y_5508_ = v___y_5523_;
v_snd_5509_ = v_snd_5527_;
v_pos_5510_ = v_pos_5525_;
v_err_5511_ = v___x_5534_;
goto v___jp_5506_;
}
else
{
lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5550_; 
lean_inc(v_fst_5526_);
v_isSharedCheck_5550_ = !lean_is_exclusive(v_pos_5525_);
if (v_isSharedCheck_5550_ == 0)
{
lean_object* v_unused_5551_; lean_object* v_unused_5552_; 
v_unused_5551_ = lean_ctor_get(v_pos_5525_, 1);
lean_dec(v_unused_5551_);
v_unused_5552_ = lean_ctor_get(v_pos_5525_, 0);
lean_dec(v_unused_5552_);
v___x_5536_ = v_pos_5525_;
v_isShared_5537_ = v_isSharedCheck_5550_;
goto v_resetjp_5535_;
}
else
{
lean_dec(v_pos_5525_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5550_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v___x_5538_; lean_object* v_it_x27_5540_; 
v___x_5538_ = lean_string_utf8_next_fast(v_fst_5526_, v_snd_5527_);
if (v_isShared_5537_ == 0)
{
lean_ctor_set(v___x_5536_, 1, v___x_5538_);
v_it_x27_5540_ = v___x_5536_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_fst_5526_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v___x_5538_);
v_it_x27_5540_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
lean_object* v___x_5541_; lean_object* v___x_5542_; 
v___x_5541_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0);
v___x_5542_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(v___x_5541_, v_it_x27_5540_);
if (lean_obj_tag(v___x_5542_) == 0)
{
lean_object* v_pos_5543_; lean_object* v_res_5544_; lean_object* v___x_5545_; 
v_pos_5543_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_pos_5543_);
v_res_5544_ = lean_ctor_get(v___x_5542_, 1);
lean_inc(v_res_5544_);
lean_dec_ref_known(v___x_5542_, 2);
v___x_5545_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(v___f_5519_, v_res_5544_, v_pos_5543_);
if (lean_obj_tag(v___x_5545_) == 0)
{
lean_dec(v_snd_5527_);
lean_dec_ref(v___y_5523_);
lean_dec_ref(v___y_5521_);
return v___x_5545_;
}
else
{
lean_object* v_pos_5546_; 
v_pos_5546_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_pos_5546_);
v___y_5474_ = v___y_5521_;
v_snd_5475_ = v_snd_5527_;
v___y_5476_ = v___y_5523_;
v___y_5477_ = v___x_5545_;
v_pos_5478_ = v_pos_5546_;
goto v___jp_5473_;
}
}
else
{
lean_object* v_pos_5547_; lean_object* v_err_5548_; 
v_pos_5547_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_pos_5547_);
v_err_5548_ = lean_ctor_get(v___x_5542_, 1);
lean_inc(v_err_5548_);
lean_dec_ref_known(v___x_5542_, 2);
v___y_5507_ = v___y_5521_;
v___y_5508_ = v___y_5523_;
v_snd_5509_ = v_snd_5527_;
v_pos_5510_ = v_pos_5547_;
v_err_5511_ = v_err_5548_;
goto v___jp_5506_;
}
}
}
}
}
}
else
{
v___y_5514_ = v___y_5521_;
v___y_5515_ = v___y_5523_;
v___y_5516_ = v_pos_5525_;
v_snd_5517_ = v_snd_5527_;
goto v___jp_5513_;
}
}
}
v___jp_5553_:
{
lean_object* v___x_5559_; 
lean_inc_ref(v_pos_5557_);
v___x_5559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5559_, 0, v_pos_5557_);
lean_ctor_set(v___x_5559_, 1, v_err_5558_);
v___y_5521_ = v___y_5554_;
v_snd_5522_ = v_snd_5555_;
v___y_5523_ = v___y_5556_;
v___y_5524_ = v___x_5559_;
v_pos_5525_ = v_pos_5557_;
goto v___jp_5520_;
}
v___jp_5560_:
{
lean_object* v___x_5565_; 
v___x_5565_ = lean_box(0);
v___y_5554_ = v___y_5561_;
v_snd_5555_ = v_snd_5563_;
v___y_5556_ = v___y_5564_;
v_pos_5557_ = v___y_5562_;
v_err_5558_ = v___x_5565_;
goto v___jp_5553_;
}
v___jp_5567_:
{
lean_object* v_fst_5573_; lean_object* v_snd_5574_; uint8_t v_decide_5575_; 
v_fst_5573_ = lean_ctor_get(v_pos_5572_, 0);
v_snd_5574_ = lean_ctor_get(v_pos_5572_, 1);
lean_inc(v_snd_5574_);
v_decide_5575_ = lean_nat_dec_eq(v___y_5569_, v_snd_5574_);
lean_dec(v___y_5569_);
if (v_decide_5575_ == 0)
{
lean_dec(v_snd_5574_);
lean_dec_ref(v_pos_5572_);
lean_dec_ref(v___y_5570_);
lean_dec_ref(v___y_5568_);
return v___y_5571_;
}
else
{
lean_object* v___x_5576_; uint8_t v_decide_5577_; 
lean_dec_ref(v___y_5571_);
v___x_5576_ = lean_string_utf8_byte_size(v_fst_5573_);
v_decide_5577_ = lean_nat_dec_eq(v_snd_5574_, v___x_5576_);
if (v_decide_5577_ == 0)
{
if (v_decide_5575_ == 0)
{
v___y_5561_ = v___y_5568_;
v___y_5562_ = v_pos_5572_;
v_snd_5563_ = v_snd_5574_;
v___y_5564_ = v___y_5570_;
goto v___jp_5560_;
}
else
{
uint32_t v___x_5578_; uint32_t v_c_5579_; uint8_t v___x_5580_; 
v___x_5578_ = 69;
v_c_5579_ = lean_string_utf8_get_fast(v_fst_5573_, v_snd_5574_);
v___x_5580_ = lean_uint32_dec_eq(v_c_5579_, v___x_5578_);
if (v___x_5580_ == 0)
{
lean_object* v___x_5581_; 
v___x_5581_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3);
v___y_5554_ = v___y_5568_;
v_snd_5555_ = v_snd_5574_;
v___y_5556_ = v___y_5570_;
v_pos_5557_ = v_pos_5572_;
v_err_5558_ = v___x_5581_;
goto v___jp_5553_;
}
else
{
lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5597_; 
lean_inc(v_fst_5573_);
v_isSharedCheck_5597_ = !lean_is_exclusive(v_pos_5572_);
if (v_isSharedCheck_5597_ == 0)
{
lean_object* v_unused_5598_; lean_object* v_unused_5599_; 
v_unused_5598_ = lean_ctor_get(v_pos_5572_, 1);
lean_dec(v_unused_5598_);
v_unused_5599_ = lean_ctor_get(v_pos_5572_, 0);
lean_dec(v_unused_5599_);
v___x_5583_ = v_pos_5572_;
v_isShared_5584_ = v_isSharedCheck_5597_;
goto v_resetjp_5582_;
}
else
{
lean_dec(v_pos_5572_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5597_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5585_; lean_object* v_it_x27_5587_; 
v___x_5585_ = lean_string_utf8_next_fast(v_fst_5573_, v_snd_5574_);
if (v_isShared_5584_ == 0)
{
lean_ctor_set(v___x_5583_, 1, v___x_5585_);
v_it_x27_5587_ = v___x_5583_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_fst_5573_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v___x_5585_);
v_it_x27_5587_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_5588_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0);
v___x_5589_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(v___x_5588_, v_it_x27_5587_);
if (lean_obj_tag(v___x_5589_) == 0)
{
lean_object* v_pos_5590_; lean_object* v_res_5591_; lean_object* v___x_5592_; 
v_pos_5590_ = lean_ctor_get(v___x_5589_, 0);
lean_inc(v_pos_5590_);
v_res_5591_ = lean_ctor_get(v___x_5589_, 1);
lean_inc(v_res_5591_);
lean_dec_ref_known(v___x_5589_, 2);
v___x_5592_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(v___f_5566_, v_res_5591_, v_pos_5590_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_dec(v_snd_5574_);
lean_dec_ref(v___y_5570_);
lean_dec_ref(v___y_5568_);
return v___x_5592_;
}
else
{
lean_object* v_pos_5593_; 
v_pos_5593_ = lean_ctor_get(v___x_5592_, 0);
lean_inc(v_pos_5593_);
v___y_5521_ = v___y_5568_;
v_snd_5522_ = v_snd_5574_;
v___y_5523_ = v___y_5570_;
v___y_5524_ = v___x_5592_;
v_pos_5525_ = v_pos_5593_;
goto v___jp_5520_;
}
}
else
{
lean_object* v_pos_5594_; lean_object* v_err_5595_; 
v_pos_5594_ = lean_ctor_get(v___x_5589_, 0);
lean_inc(v_pos_5594_);
v_err_5595_ = lean_ctor_get(v___x_5589_, 1);
lean_inc(v_err_5595_);
lean_dec_ref_known(v___x_5589_, 2);
v___y_5554_ = v___y_5568_;
v_snd_5555_ = v_snd_5574_;
v___y_5556_ = v___y_5570_;
v_pos_5557_ = v_pos_5594_;
v_err_5558_ = v_err_5595_;
goto v___jp_5553_;
}
}
}
}
}
}
else
{
v___y_5561_ = v___y_5568_;
v___y_5562_ = v_pos_5572_;
v_snd_5563_ = v_snd_5574_;
v___y_5564_ = v___y_5570_;
goto v___jp_5560_;
}
}
}
v___jp_5600_:
{
lean_object* v___x_5606_; 
lean_inc_ref(v_pos_5604_);
v___x_5606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5606_, 0, v_pos_5604_);
lean_ctor_set(v___x_5606_, 1, v_err_5605_);
v___y_5568_ = v___y_5601_;
v___y_5569_ = v___y_5602_;
v___y_5570_ = v___y_5603_;
v___y_5571_ = v___x_5606_;
v_pos_5572_ = v_pos_5604_;
goto v___jp_5567_;
}
v___jp_5607_:
{
lean_object* v___x_5612_; 
v___x_5612_ = lean_box(0);
v___y_5601_ = v___y_5608_;
v___y_5602_ = v___y_5610_;
v___y_5603_ = v___y_5611_;
v_pos_5604_ = v___y_5609_;
v_err_5605_ = v___x_5612_;
goto v___jp_5600_;
}
v___jp_5614_:
{
lean_object* v_fst_5619_; lean_object* v_snd_5620_; uint8_t v_decide_5621_; 
v_fst_5619_ = lean_ctor_get(v_pos_5618_, 0);
v_snd_5620_ = lean_ctor_get(v_pos_5618_, 1);
lean_inc(v_snd_5620_);
v_decide_5621_ = lean_nat_dec_eq(v_snd_5616_, v_snd_5620_);
lean_dec(v_snd_5616_);
if (v_decide_5621_ == 0)
{
lean_dec(v_snd_5620_);
lean_dec_ref(v_pos_5618_);
lean_dec_ref(v___y_5615_);
return v___y_5617_;
}
else
{
lean_object* v___x_5622_; lean_object* v___x_5623_; uint8_t v_decide_5624_; 
lean_dec_ref(v___y_5617_);
v___x_5622_ = ((lean_object*)(l_Std_Time_parseModifier___closed__21));
v___x_5623_ = lean_string_utf8_byte_size(v_fst_5619_);
v_decide_5624_ = lean_nat_dec_eq(v_snd_5620_, v___x_5623_);
if (v_decide_5624_ == 0)
{
if (v_decide_5621_ == 0)
{
v___y_5608_ = v___x_5622_;
v___y_5609_ = v_pos_5618_;
v___y_5610_ = v_snd_5620_;
v___y_5611_ = v___y_5615_;
goto v___jp_5607_;
}
else
{
uint32_t v___x_5625_; uint32_t v_c_5626_; uint8_t v___x_5627_; 
v___x_5625_ = 87;
v_c_5626_ = lean_string_utf8_get_fast(v_fst_5619_, v_snd_5620_);
v___x_5627_ = lean_uint32_dec_eq(v_c_5626_, v___x_5625_);
if (v___x_5627_ == 0)
{
lean_object* v___x_5628_; 
v___x_5628_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3);
v___y_5601_ = v___x_5622_;
v___y_5602_ = v_snd_5620_;
v___y_5603_ = v___y_5615_;
v_pos_5604_ = v_pos_5618_;
v_err_5605_ = v___x_5628_;
goto v___jp_5600_;
}
else
{
lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5644_; 
lean_inc(v_fst_5619_);
v_isSharedCheck_5644_ = !lean_is_exclusive(v_pos_5618_);
if (v_isSharedCheck_5644_ == 0)
{
lean_object* v_unused_5645_; lean_object* v_unused_5646_; 
v_unused_5645_ = lean_ctor_get(v_pos_5618_, 1);
lean_dec(v_unused_5645_);
v_unused_5646_ = lean_ctor_get(v_pos_5618_, 0);
lean_dec(v_unused_5646_);
v___x_5630_ = v_pos_5618_;
v_isShared_5631_ = v_isSharedCheck_5644_;
goto v_resetjp_5629_;
}
else
{
lean_dec(v_pos_5618_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5644_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v___x_5632_; lean_object* v_it_x27_5634_; 
v___x_5632_ = lean_string_utf8_next_fast(v_fst_5619_, v_snd_5620_);
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 1, v___x_5632_);
v_it_x27_5634_ = v___x_5630_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_fst_5619_);
lean_ctor_set(v_reuseFailAlloc_5643_, 1, v___x_5632_);
v_it_x27_5634_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
lean_object* v___x_5635_; lean_object* v___x_5636_; 
v___x_5635_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0);
v___x_5636_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(v___x_5635_, v_it_x27_5634_);
if (lean_obj_tag(v___x_5636_) == 0)
{
lean_object* v_pos_5637_; lean_object* v_res_5638_; lean_object* v___x_5639_; 
v_pos_5637_ = lean_ctor_get(v___x_5636_, 0);
lean_inc(v_pos_5637_);
v_res_5638_ = lean_ctor_get(v___x_5636_, 1);
lean_inc(v_res_5638_);
lean_dec_ref_known(v___x_5636_, 2);
v___x_5639_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5613_, v___x_5622_, v_res_5638_, v_pos_5637_);
if (lean_obj_tag(v___x_5639_) == 0)
{
lean_dec(v_snd_5620_);
lean_dec_ref(v___y_5615_);
return v___x_5639_;
}
else
{
lean_object* v_pos_5640_; 
v_pos_5640_ = lean_ctor_get(v___x_5639_, 0);
lean_inc(v_pos_5640_);
v___y_5568_ = v___x_5622_;
v___y_5569_ = v_snd_5620_;
v___y_5570_ = v___y_5615_;
v___y_5571_ = v___x_5639_;
v_pos_5572_ = v_pos_5640_;
goto v___jp_5567_;
}
}
else
{
lean_object* v_pos_5641_; lean_object* v_err_5642_; 
v_pos_5641_ = lean_ctor_get(v___x_5636_, 0);
lean_inc(v_pos_5641_);
v_err_5642_ = lean_ctor_get(v___x_5636_, 1);
lean_inc(v_err_5642_);
lean_dec_ref_known(v___x_5636_, 2);
v___y_5601_ = v___x_5622_;
v___y_5602_ = v_snd_5620_;
v___y_5603_ = v___y_5615_;
v_pos_5604_ = v_pos_5641_;
v_err_5605_ = v_err_5642_;
goto v___jp_5600_;
}
}
}
}
}
}
else
{
v___y_5608_ = v___x_5622_;
v___y_5609_ = v_pos_5618_;
v___y_5610_ = v_snd_5620_;
v___y_5611_ = v___y_5615_;
goto v___jp_5607_;
}
}
}
v___jp_5647_:
{
lean_object* v___x_5652_; 
lean_inc_ref(v_pos_5650_);
v___x_5652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5652_, 0, v_pos_5650_);
lean_ctor_set(v___x_5652_, 1, v_err_5651_);
v___y_5615_ = v___y_5648_;
v_snd_5616_ = v_snd_5649_;
v___y_5617_ = v___x_5652_;
v_pos_5618_ = v_pos_5650_;
goto v___jp_5614_;
}
v___jp_5653_:
{
lean_object* v___x_5657_; 
v___x_5657_ = lean_box(0);
v___y_5648_ = v___y_5654_;
v_snd_5649_ = v_snd_5656_;
v_pos_5650_ = v___y_5655_;
v_err_5651_ = v___x_5657_;
goto v___jp_5647_;
}
v___jp_5659_:
{
lean_object* v_fst_5664_; lean_object* v_snd_5665_; uint8_t v_decide_5666_; 
v_fst_5664_ = lean_ctor_get(v_pos_5663_, 0);
v_snd_5665_ = lean_ctor_get(v_pos_5663_, 1);
lean_inc(v_snd_5665_);
v_decide_5666_ = lean_nat_dec_eq(v_snd_5661_, v_snd_5665_);
lean_dec(v_snd_5661_);
if (v_decide_5666_ == 0)
{
lean_dec(v_snd_5665_);
lean_dec_ref(v_pos_5663_);
lean_dec_ref(v___y_5660_);
return v___y_5662_;
}
else
{
lean_object* v___x_5667_; uint8_t v_decide_5668_; 
lean_dec_ref(v___y_5662_);
v___x_5667_ = lean_string_utf8_byte_size(v_fst_5664_);
v_decide_5668_ = lean_nat_dec_eq(v_snd_5665_, v___x_5667_);
if (v_decide_5668_ == 0)
{
if (v_decide_5666_ == 0)
{
v___y_5654_ = v___y_5660_;
v___y_5655_ = v_pos_5663_;
v_snd_5656_ = v_snd_5665_;
goto v___jp_5653_;
}
else
{
uint32_t v___x_5669_; uint32_t v_c_5670_; uint8_t v___x_5671_; 
v___x_5669_ = 119;
v_c_5670_ = lean_string_utf8_get_fast(v_fst_5664_, v_snd_5665_);
v___x_5671_ = lean_uint32_dec_eq(v_c_5670_, v___x_5669_);
if (v___x_5671_ == 0)
{
lean_object* v___x_5672_; 
v___x_5672_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3);
v___y_5648_ = v___y_5660_;
v_snd_5649_ = v_snd_5665_;
v_pos_5650_ = v_pos_5663_;
v_err_5651_ = v___x_5672_;
goto v___jp_5647_;
}
else
{
lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5688_; 
lean_inc(v_fst_5664_);
v_isSharedCheck_5688_ = !lean_is_exclusive(v_pos_5663_);
if (v_isSharedCheck_5688_ == 0)
{
lean_object* v_unused_5689_; lean_object* v_unused_5690_; 
v_unused_5689_ = lean_ctor_get(v_pos_5663_, 1);
lean_dec(v_unused_5689_);
v_unused_5690_ = lean_ctor_get(v_pos_5663_, 0);
lean_dec(v_unused_5690_);
v___x_5674_ = v_pos_5663_;
v_isShared_5675_ = v_isSharedCheck_5688_;
goto v_resetjp_5673_;
}
else
{
lean_dec(v_pos_5663_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5688_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v___x_5676_; lean_object* v_it_x27_5678_; 
v___x_5676_ = lean_string_utf8_next_fast(v_fst_5664_, v_snd_5665_);
if (v_isShared_5675_ == 0)
{
lean_ctor_set(v___x_5674_, 1, v___x_5676_);
v_it_x27_5678_ = v___x_5674_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_fst_5664_);
lean_ctor_set(v_reuseFailAlloc_5687_, 1, v___x_5676_);
v_it_x27_5678_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
lean_object* v___x_5679_; lean_object* v___x_5680_; 
v___x_5679_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0);
v___x_5680_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(v___x_5679_, v_it_x27_5678_);
if (lean_obj_tag(v___x_5680_) == 0)
{
lean_object* v_pos_5681_; lean_object* v_res_5682_; lean_object* v___x_5683_; 
v_pos_5681_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_pos_5681_);
v_res_5682_ = lean_ctor_get(v___x_5680_, 1);
lean_inc(v_res_5682_);
lean_dec_ref_known(v___x_5680_, 2);
lean_inc_ref(v___y_5660_);
v___x_5683_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5658_, v___y_5660_, v_res_5682_, v_pos_5681_);
if (lean_obj_tag(v___x_5683_) == 0)
{
lean_dec(v_snd_5665_);
lean_dec_ref(v___y_5660_);
return v___x_5683_;
}
else
{
lean_object* v_pos_5684_; 
v_pos_5684_ = lean_ctor_get(v___x_5683_, 0);
lean_inc(v_pos_5684_);
v___y_5615_ = v___y_5660_;
v_snd_5616_ = v_snd_5665_;
v___y_5617_ = v___x_5683_;
v_pos_5618_ = v_pos_5684_;
goto v___jp_5614_;
}
}
else
{
lean_object* v_pos_5685_; lean_object* v_err_5686_; 
v_pos_5685_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_pos_5685_);
v_err_5686_ = lean_ctor_get(v___x_5680_, 1);
lean_inc(v_err_5686_);
lean_dec_ref_known(v___x_5680_, 2);
v___y_5648_ = v___y_5660_;
v_snd_5649_ = v_snd_5665_;
v_pos_5650_ = v_pos_5685_;
v_err_5651_ = v_err_5686_;
goto v___jp_5647_;
}
}
}
}
}
}
else
{
v___y_5654_ = v___y_5660_;
v___y_5655_ = v_pos_5663_;
v_snd_5656_ = v_snd_5665_;
goto v___jp_5653_;
}
}
}
v___jp_5691_:
{
lean_object* v___x_5696_; 
lean_inc_ref(v_pos_5694_);
v___x_5696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5696_, 0, v_pos_5694_);
lean_ctor_set(v___x_5696_, 1, v_err_5695_);
v___y_5660_ = v___y_5692_;
v_snd_5661_ = v_snd_5693_;
v___y_5662_ = v___x_5696_;
v_pos_5663_ = v_pos_5694_;
goto v___jp_5659_;
}
v___jp_5697_:
{
lean_object* v___x_5701_; 
v___x_5701_ = lean_box(0);
v___y_5692_ = v___y_5698_;
v_snd_5693_ = v_snd_5700_;
v_pos_5694_ = v___y_5699_;
v_err_5695_ = v___x_5701_;
goto v___jp_5691_;
}
v___jp_5703_:
{
lean_object* v_fst_5708_; lean_object* v_snd_5709_; uint8_t v_decide_5710_; 
v_fst_5708_ = lean_ctor_get(v_pos_5707_, 0);
v_snd_5709_ = lean_ctor_get(v_pos_5707_, 1);
lean_inc(v_snd_5709_);
v_decide_5710_ = lean_nat_dec_eq(v_snd_5704_, v_snd_5709_);
lean_dec(v_snd_5704_);
if (v_decide_5710_ == 0)
{
lean_dec(v_snd_5709_);
lean_dec_ref(v_pos_5707_);
lean_dec_ref(v___y_5705_);
return v___y_5706_;
}
else
{
lean_object* v___x_5711_; uint8_t v_decide_5712_; 
lean_dec_ref(v___y_5706_);
v___x_5711_ = lean_string_utf8_byte_size(v_fst_5708_);
v_decide_5712_ = lean_nat_dec_eq(v_snd_5709_, v___x_5711_);
if (v_decide_5712_ == 0)
{
if (v_decide_5710_ == 0)
{
v___y_5698_ = v___y_5705_;
v___y_5699_ = v_pos_5707_;
v_snd_5700_ = v_snd_5709_;
goto v___jp_5697_;
}
else
{
uint32_t v___x_5713_; uint32_t v_c_5714_; uint8_t v___x_5715_; 
v___x_5713_ = 113;
v_c_5714_ = lean_string_utf8_get_fast(v_fst_5708_, v_snd_5709_);
v___x_5715_ = lean_uint32_dec_eq(v_c_5714_, v___x_5713_);
if (v___x_5715_ == 0)
{
lean_object* v___x_5716_; 
v___x_5716_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3);
v___y_5692_ = v___y_5705_;
v_snd_5693_ = v_snd_5709_;
v_pos_5694_ = v_pos_5707_;
v_err_5695_ = v___x_5716_;
goto v___jp_5691_;
}
else
{
lean_object* v___x_5718_; uint8_t v_isShared_5719_; uint8_t v_isSharedCheck_5732_; 
lean_inc(v_fst_5708_);
v_isSharedCheck_5732_ = !lean_is_exclusive(v_pos_5707_);
if (v_isSharedCheck_5732_ == 0)
{
lean_object* v_unused_5733_; lean_object* v_unused_5734_; 
v_unused_5733_ = lean_ctor_get(v_pos_5707_, 1);
lean_dec(v_unused_5733_);
v_unused_5734_ = lean_ctor_get(v_pos_5707_, 0);
lean_dec(v_unused_5734_);
v___x_5718_ = v_pos_5707_;
v_isShared_5719_ = v_isSharedCheck_5732_;
goto v_resetjp_5717_;
}
else
{
lean_dec(v_pos_5707_);
v___x_5718_ = lean_box(0);
v_isShared_5719_ = v_isSharedCheck_5732_;
goto v_resetjp_5717_;
}
v_resetjp_5717_:
{
lean_object* v___x_5720_; lean_object* v_it_x27_5722_; 
v___x_5720_ = lean_string_utf8_next_fast(v_fst_5708_, v_snd_5709_);
if (v_isShared_5719_ == 0)
{
lean_ctor_set(v___x_5718_, 1, v___x_5720_);
v_it_x27_5722_ = v___x_5718_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5731_; 
v_reuseFailAlloc_5731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5731_, 0, v_fst_5708_);
lean_ctor_set(v_reuseFailAlloc_5731_, 1, v___x_5720_);
v_it_x27_5722_ = v_reuseFailAlloc_5731_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
lean_object* v___x_5723_; lean_object* v___x_5724_; 
v___x_5723_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0);
v___x_5724_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(v___x_5723_, v_it_x27_5722_);
if (lean_obj_tag(v___x_5724_) == 0)
{
lean_object* v_pos_5725_; lean_object* v_res_5726_; lean_object* v___x_5727_; 
v_pos_5725_ = lean_ctor_get(v___x_5724_, 0);
lean_inc(v_pos_5725_);
v_res_5726_ = lean_ctor_get(v___x_5724_, 1);
lean_inc(v_res_5726_);
lean_dec_ref_known(v___x_5724_, 2);
v___x_5727_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5702_, v_res_5726_, v_pos_5725_);
if (lean_obj_tag(v___x_5727_) == 0)
{
lean_dec(v_snd_5709_);
lean_dec_ref(v___y_5705_);
return v___x_5727_;
}
else
{
lean_object* v_pos_5728_; 
v_pos_5728_ = lean_ctor_get(v___x_5727_, 0);
lean_inc(v_pos_5728_);
v___y_5660_ = v___y_5705_;
v_snd_5661_ = v_snd_5709_;
v___y_5662_ = v___x_5727_;
v_pos_5663_ = v_pos_5728_;
goto v___jp_5659_;
}
}
else
{
lean_object* v_pos_5729_; lean_object* v_err_5730_; 
v_pos_5729_ = lean_ctor_get(v___x_5724_, 0);
lean_inc(v_pos_5729_);
v_err_5730_ = lean_ctor_get(v___x_5724_, 1);
lean_inc(v_err_5730_);
lean_dec_ref_known(v___x_5724_, 2);
v___y_5692_ = v___y_5705_;
v_snd_5693_ = v_snd_5709_;
v_pos_5694_ = v_pos_5729_;
v_err_5695_ = v_err_5730_;
goto v___jp_5691_;
}
}
}
}
}
}
else
{
v___y_5698_ = v___y_5705_;
v___y_5699_ = v_pos_5707_;
v_snd_5700_ = v_snd_5709_;
goto v___jp_5697_;
}
}
}
v___jp_5735_:
{
lean_object* v___x_5740_; 
lean_inc_ref(v_pos_5738_);
v___x_5740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5740_, 0, v_pos_5738_);
lean_ctor_set(v___x_5740_, 1, v_err_5739_);
v_snd_5704_ = v_snd_5736_;
v___y_5705_ = v___y_5737_;
v___y_5706_ = v___x_5740_;
v_pos_5707_ = v_pos_5738_;
goto v___jp_5703_;
}
v___jp_5741_:
{
lean_object* v___x_5745_; 
v___x_5745_ = lean_box(0);
v_snd_5736_ = v_snd_5743_;
v___y_5737_ = v___y_5744_;
v_pos_5738_ = v___y_5742_;
v_err_5739_ = v___x_5745_;
goto v___jp_5735_;
}
v___jp_5747_:
{
lean_object* v_fst_5752_; lean_object* v_snd_5753_; uint8_t v_decide_5754_; 
v_fst_5752_ = lean_ctor_get(v_pos_5751_, 0);
v_snd_5753_ = lean_ctor_get(v_pos_5751_, 1);
lean_inc(v_snd_5753_);
v_decide_5754_ = lean_nat_dec_eq(v___y_5749_, v_snd_5753_);
lean_dec(v___y_5749_);
if (v_decide_5754_ == 0)
{
lean_dec(v_snd_5753_);
lean_dec_ref(v_pos_5751_);
lean_dec_ref(v___y_5748_);
return v___y_5750_;
}
else
{
lean_object* v___x_5755_; uint8_t v_decide_5756_; 
lean_dec_ref(v___y_5750_);
v___x_5755_ = lean_string_utf8_byte_size(v_fst_5752_);
v_decide_5756_ = lean_nat_dec_eq(v_snd_5753_, v___x_5755_);
if (v_decide_5756_ == 0)
{
if (v_decide_5754_ == 0)
{
v___y_5742_ = v_pos_5751_;
v_snd_5743_ = v_snd_5753_;
v___y_5744_ = v___y_5748_;
goto v___jp_5741_;
}
else
{
uint32_t v___x_5757_; uint32_t v_c_5758_; uint8_t v___x_5759_; 
v___x_5757_ = 81;
v_c_5758_ = lean_string_utf8_get_fast(v_fst_5752_, v_snd_5753_);
v___x_5759_ = lean_uint32_dec_eq(v_c_5758_, v___x_5757_);
if (v___x_5759_ == 0)
{
lean_object* v___x_5760_; 
v___x_5760_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3);
v_snd_5736_ = v_snd_5753_;
v___y_5737_ = v___y_5748_;
v_pos_5738_ = v_pos_5751_;
v_err_5739_ = v___x_5760_;
goto v___jp_5735_;
}
else
{
lean_object* v___x_5762_; uint8_t v_isShared_5763_; uint8_t v_isSharedCheck_5776_; 
lean_inc(v_fst_5752_);
v_isSharedCheck_5776_ = !lean_is_exclusive(v_pos_5751_);
if (v_isSharedCheck_5776_ == 0)
{
lean_object* v_unused_5777_; lean_object* v_unused_5778_; 
v_unused_5777_ = lean_ctor_get(v_pos_5751_, 1);
lean_dec(v_unused_5777_);
v_unused_5778_ = lean_ctor_get(v_pos_5751_, 0);
lean_dec(v_unused_5778_);
v___x_5762_ = v_pos_5751_;
v_isShared_5763_ = v_isSharedCheck_5776_;
goto v_resetjp_5761_;
}
else
{
lean_dec(v_pos_5751_);
v___x_5762_ = lean_box(0);
v_isShared_5763_ = v_isSharedCheck_5776_;
goto v_resetjp_5761_;
}
v_resetjp_5761_:
{
lean_object* v___x_5764_; lean_object* v_it_x27_5766_; 
v___x_5764_ = lean_string_utf8_next_fast(v_fst_5752_, v_snd_5753_);
if (v_isShared_5763_ == 0)
{
lean_ctor_set(v___x_5762_, 1, v___x_5764_);
v_it_x27_5766_ = v___x_5762_;
goto v_reusejp_5765_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_fst_5752_);
lean_ctor_set(v_reuseFailAlloc_5775_, 1, v___x_5764_);
v_it_x27_5766_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5765_;
}
v_reusejp_5765_:
{
lean_object* v___x_5767_; lean_object* v___x_5768_; 
v___x_5767_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0);
v___x_5768_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(v___x_5767_, v_it_x27_5766_);
if (lean_obj_tag(v___x_5768_) == 0)
{
lean_object* v_pos_5769_; lean_object* v_res_5770_; lean_object* v___x_5771_; 
v_pos_5769_ = lean_ctor_get(v___x_5768_, 0);
lean_inc(v_pos_5769_);
v_res_5770_ = lean_ctor_get(v___x_5768_, 1);
lean_inc(v_res_5770_);
lean_dec_ref_known(v___x_5768_, 2);
v___x_5771_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5746_, v_res_5770_, v_pos_5769_);
if (lean_obj_tag(v___x_5771_) == 0)
{
lean_dec(v_snd_5753_);
lean_dec_ref(v___y_5748_);
return v___x_5771_;
}
else
{
lean_object* v_pos_5772_; 
v_pos_5772_ = lean_ctor_get(v___x_5771_, 0);
lean_inc(v_pos_5772_);
v_snd_5704_ = v_snd_5753_;
v___y_5705_ = v___y_5748_;
v___y_5706_ = v___x_5771_;
v_pos_5707_ = v_pos_5772_;
goto v___jp_5703_;
}
}
else
{
lean_object* v_pos_5773_; lean_object* v_err_5774_; 
v_pos_5773_ = lean_ctor_get(v___x_5768_, 0);
lean_inc(v_pos_5773_);
v_err_5774_ = lean_ctor_get(v___x_5768_, 1);
lean_inc(v_err_5774_);
lean_dec_ref_known(v___x_5768_, 2);
v_snd_5736_ = v_snd_5753_;
v___y_5737_ = v___y_5748_;
v_pos_5738_ = v_pos_5773_;
v_err_5739_ = v_err_5774_;
goto v___jp_5735_;
}
}
}
}
}
}
else
{
v___y_5742_ = v_pos_5751_;
v_snd_5743_ = v_snd_5753_;
v___y_5744_ = v___y_5748_;
goto v___jp_5741_;
}
}
}
v___jp_5779_:
{
lean_object* v___x_5784_; 
lean_inc_ref(v_pos_5782_);
v___x_5784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5784_, 0, v_pos_5782_);
lean_ctor_set(v___x_5784_, 1, v_err_5783_);
v___y_5748_ = v___y_5780_;
v___y_5749_ = v___y_5781_;
v___y_5750_ = v___x_5784_;
v_pos_5751_ = v_pos_5782_;
goto v___jp_5747_;
}
v___jp_5785_:
{
lean_object* v___x_5789_; 
v___x_5789_ = lean_box(0);
v___y_5780_ = v___y_5787_;
v___y_5781_ = v___y_5788_;
v_pos_5782_ = v___y_5786_;
v_err_5783_ = v___x_5789_;
goto v___jp_5779_;
}
v___jp_5791_:
{
lean_object* v_fst_5795_; lean_object* v_snd_5796_; uint8_t v_decide_5797_; 
v_fst_5795_ = lean_ctor_get(v_pos_5794_, 0);
v_snd_5796_ = lean_ctor_get(v_pos_5794_, 1);
lean_inc(v_snd_5796_);
v_decide_5797_ = lean_nat_dec_eq(v_snd_5792_, v_snd_5796_);
lean_dec(v_snd_5792_);
if (v_decide_5797_ == 0)
{
lean_dec(v_snd_5796_);
lean_dec_ref(v_pos_5794_);
return v___y_5793_;
}
else
{
lean_object* v___x_5798_; lean_object* v___x_5799_; uint8_t v_decide_5800_; 
lean_dec_ref(v___y_5793_);
v___x_5798_ = ((lean_object*)(l_Std_Time_parseModifier___closed__26));
v___x_5799_ = lean_string_utf8_byte_size(v_fst_5795_);
v_decide_5800_ = lean_nat_dec_eq(v_snd_5796_, v___x_5799_);
if (v_decide_5800_ == 0)
{
if (v_decide_5797_ == 0)
{
v___y_5786_ = v_pos_5794_;
v___y_5787_ = v___x_5798_;
v___y_5788_ = v_snd_5796_;
goto v___jp_5785_;
}
else
{
uint32_t v___x_5801_; uint32_t v_c_5802_; uint8_t v___x_5803_; 
v___x_5801_ = 100;
v_c_5802_ = lean_string_utf8_get_fast(v_fst_5795_, v_snd_5796_);
v___x_5803_ = lean_uint32_dec_eq(v_c_5802_, v___x_5801_);
if (v___x_5803_ == 0)
{
lean_object* v___x_5804_; 
v___x_5804_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3);
v___y_5780_ = v___x_5798_;
v___y_5781_ = v_snd_5796_;
v_pos_5782_ = v_pos_5794_;
v_err_5783_ = v___x_5804_;
goto v___jp_5779_;
}
else
{
lean_object* v___x_5806_; uint8_t v_isShared_5807_; uint8_t v_isSharedCheck_5820_; 
lean_inc(v_fst_5795_);
v_isSharedCheck_5820_ = !lean_is_exclusive(v_pos_5794_);
if (v_isSharedCheck_5820_ == 0)
{
lean_object* v_unused_5821_; lean_object* v_unused_5822_; 
v_unused_5821_ = lean_ctor_get(v_pos_5794_, 1);
lean_dec(v_unused_5821_);
v_unused_5822_ = lean_ctor_get(v_pos_5794_, 0);
lean_dec(v_unused_5822_);
v___x_5806_ = v_pos_5794_;
v_isShared_5807_ = v_isSharedCheck_5820_;
goto v_resetjp_5805_;
}
else
{
lean_dec(v_pos_5794_);
v___x_5806_ = lean_box(0);
v_isShared_5807_ = v_isSharedCheck_5820_;
goto v_resetjp_5805_;
}
v_resetjp_5805_:
{
lean_object* v___x_5808_; lean_object* v_it_x27_5810_; 
v___x_5808_ = lean_string_utf8_next_fast(v_fst_5795_, v_snd_5796_);
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 1, v___x_5808_);
v_it_x27_5810_ = v___x_5806_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_fst_5795_);
lean_ctor_set(v_reuseFailAlloc_5819_, 1, v___x_5808_);
v_it_x27_5810_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
lean_object* v___x_5811_; lean_object* v___x_5812_; 
v___x_5811_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0);
v___x_5812_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(v___x_5811_, v_it_x27_5810_);
if (lean_obj_tag(v___x_5812_) == 0)
{
lean_object* v_pos_5813_; lean_object* v_res_5814_; lean_object* v___x_5815_; 
v_pos_5813_ = lean_ctor_get(v___x_5812_, 0);
lean_inc(v_pos_5813_);
v_res_5814_ = lean_ctor_get(v___x_5812_, 1);
lean_inc(v_res_5814_);
lean_dec_ref_known(v___x_5812_, 2);
v___x_5815_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5790_, v___x_5798_, v_res_5814_, v_pos_5813_);
if (lean_obj_tag(v___x_5815_) == 0)
{
lean_dec(v_snd_5796_);
return v___x_5815_;
}
else
{
lean_object* v_pos_5816_; 
v_pos_5816_ = lean_ctor_get(v___x_5815_, 0);
lean_inc(v_pos_5816_);
v___y_5748_ = v___x_5798_;
v___y_5749_ = v_snd_5796_;
v___y_5750_ = v___x_5815_;
v_pos_5751_ = v_pos_5816_;
goto v___jp_5747_;
}
}
else
{
lean_object* v_pos_5817_; lean_object* v_err_5818_; 
v_pos_5817_ = lean_ctor_get(v___x_5812_, 0);
lean_inc(v_pos_5817_);
v_err_5818_ = lean_ctor_get(v___x_5812_, 1);
lean_inc(v_err_5818_);
lean_dec_ref_known(v___x_5812_, 2);
v___y_5780_ = v___x_5798_;
v___y_5781_ = v_snd_5796_;
v_pos_5782_ = v_pos_5817_;
v_err_5783_ = v_err_5818_;
goto v___jp_5779_;
}
}
}
}
}
}
else
{
v___y_5786_ = v_pos_5794_;
v___y_5787_ = v___x_5798_;
v___y_5788_ = v_snd_5796_;
goto v___jp_5785_;
}
}
}
v___jp_5823_:
{
lean_object* v___x_5827_; 
lean_inc_ref(v_pos_5825_);
v___x_5827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5827_, 0, v_pos_5825_);
lean_ctor_set(v___x_5827_, 1, v_err_5826_);
v_snd_5792_ = v_snd_5824_;
v___y_5793_ = v___x_5827_;
v_pos_5794_ = v_pos_5825_;
goto v___jp_5791_;
}
v___jp_5828_:
{
lean_object* v___x_5831_; 
v___x_5831_ = lean_box(0);
v_snd_5824_ = v_snd_5830_;
v_pos_5825_ = v___y_5829_;
v_err_5826_ = v___x_5831_;
goto v___jp_5823_;
}
v___jp_5833_:
{
lean_object* v_fst_5837_; lean_object* v_snd_5838_; uint8_t v_decide_5839_; 
v_fst_5837_ = lean_ctor_get(v_pos_5836_, 0);
v_snd_5838_ = lean_ctor_get(v_pos_5836_, 1);
lean_inc(v_snd_5838_);
v_decide_5839_ = lean_nat_dec_eq(v_snd_5834_, v_snd_5838_);
lean_dec(v_snd_5834_);
if (v_decide_5839_ == 0)
{
lean_dec(v_snd_5838_);
lean_dec_ref(v_pos_5836_);
return v___y_5835_;
}
else
{
lean_object* v___x_5840_; uint8_t v_decide_5841_; 
lean_dec_ref(v___y_5835_);
v___x_5840_ = lean_string_utf8_byte_size(v_fst_5837_);
v_decide_5841_ = lean_nat_dec_eq(v_snd_5838_, v___x_5840_);
if (v_decide_5841_ == 0)
{
if (v_decide_5839_ == 0)
{
v___y_5829_ = v_pos_5836_;
v_snd_5830_ = v_snd_5838_;
goto v___jp_5828_;
}
else
{
uint32_t v___x_5842_; uint32_t v_c_5843_; uint8_t v___x_5844_; 
v___x_5842_ = 76;
v_c_5843_ = lean_string_utf8_get_fast(v_fst_5837_, v_snd_5838_);
v___x_5844_ = lean_uint32_dec_eq(v_c_5843_, v___x_5842_);
if (v___x_5844_ == 0)
{
lean_object* v___x_5845_; 
v___x_5845_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3);
v_snd_5824_ = v_snd_5838_;
v_pos_5825_ = v_pos_5836_;
v_err_5826_ = v___x_5845_;
goto v___jp_5823_;
}
else
{
lean_object* v___x_5847_; uint8_t v_isShared_5848_; uint8_t v_isSharedCheck_5861_; 
lean_inc(v_fst_5837_);
v_isSharedCheck_5861_ = !lean_is_exclusive(v_pos_5836_);
if (v_isSharedCheck_5861_ == 0)
{
lean_object* v_unused_5862_; lean_object* v_unused_5863_; 
v_unused_5862_ = lean_ctor_get(v_pos_5836_, 1);
lean_dec(v_unused_5862_);
v_unused_5863_ = lean_ctor_get(v_pos_5836_, 0);
lean_dec(v_unused_5863_);
v___x_5847_ = v_pos_5836_;
v_isShared_5848_ = v_isSharedCheck_5861_;
goto v_resetjp_5846_;
}
else
{
lean_dec(v_pos_5836_);
v___x_5847_ = lean_box(0);
v_isShared_5848_ = v_isSharedCheck_5861_;
goto v_resetjp_5846_;
}
v_resetjp_5846_:
{
lean_object* v___x_5849_; lean_object* v_it_x27_5851_; 
v___x_5849_ = lean_string_utf8_next_fast(v_fst_5837_, v_snd_5838_);
if (v_isShared_5848_ == 0)
{
lean_ctor_set(v___x_5847_, 1, v___x_5849_);
v_it_x27_5851_ = v___x_5847_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_fst_5837_);
lean_ctor_set(v_reuseFailAlloc_5860_, 1, v___x_5849_);
v_it_x27_5851_ = v_reuseFailAlloc_5860_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___x_5852_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0);
v___x_5853_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(v___x_5852_, v_it_x27_5851_);
if (lean_obj_tag(v___x_5853_) == 0)
{
lean_object* v_pos_5854_; lean_object* v_res_5855_; lean_object* v___x_5856_; 
v_pos_5854_ = lean_ctor_get(v___x_5853_, 0);
lean_inc(v_pos_5854_);
v_res_5855_ = lean_ctor_get(v___x_5853_, 1);
lean_inc(v_res_5855_);
lean_dec_ref_known(v___x_5853_, 2);
v___x_5856_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5832_, v_res_5855_, v_pos_5854_);
if (lean_obj_tag(v___x_5856_) == 0)
{
lean_dec(v_snd_5838_);
return v___x_5856_;
}
else
{
lean_object* v_pos_5857_; 
v_pos_5857_ = lean_ctor_get(v___x_5856_, 0);
lean_inc(v_pos_5857_);
v_snd_5792_ = v_snd_5838_;
v___y_5793_ = v___x_5856_;
v_pos_5794_ = v_pos_5857_;
goto v___jp_5791_;
}
}
else
{
lean_object* v_pos_5858_; lean_object* v_err_5859_; 
v_pos_5858_ = lean_ctor_get(v___x_5853_, 0);
lean_inc(v_pos_5858_);
v_err_5859_ = lean_ctor_get(v___x_5853_, 1);
lean_inc(v_err_5859_);
lean_dec_ref_known(v___x_5853_, 2);
v_snd_5824_ = v_snd_5838_;
v_pos_5825_ = v_pos_5858_;
v_err_5826_ = v_err_5859_;
goto v___jp_5823_;
}
}
}
}
}
}
else
{
v___y_5829_ = v_pos_5836_;
v_snd_5830_ = v_snd_5838_;
goto v___jp_5828_;
}
}
}
v___jp_5864_:
{
lean_object* v___x_5868_; 
lean_inc_ref(v_pos_5866_);
v___x_5868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5868_, 0, v_pos_5866_);
lean_ctor_set(v___x_5868_, 1, v_err_5867_);
v_snd_5834_ = v_snd_5865_;
v___y_5835_ = v___x_5868_;
v_pos_5836_ = v_pos_5866_;
goto v___jp_5833_;
}
v___jp_5869_:
{
lean_object* v___x_5872_; 
v___x_5872_ = lean_box(0);
v_snd_5865_ = v_snd_5871_;
v_pos_5866_ = v___y_5870_;
v_err_5867_ = v___x_5872_;
goto v___jp_5864_;
}
v___jp_5874_:
{
lean_object* v_fst_5878_; lean_object* v_snd_5879_; uint8_t v_decide_5880_; 
v_fst_5878_ = lean_ctor_get(v_pos_5877_, 0);
v_snd_5879_ = lean_ctor_get(v_pos_5877_, 1);
lean_inc(v_snd_5879_);
v_decide_5880_ = lean_nat_dec_eq(v_snd_5875_, v_snd_5879_);
lean_dec(v_snd_5875_);
if (v_decide_5880_ == 0)
{
lean_dec(v_snd_5879_);
lean_dec_ref(v_pos_5877_);
return v___y_5876_;
}
else
{
lean_object* v___x_5881_; uint8_t v_decide_5882_; 
lean_dec_ref(v___y_5876_);
v___x_5881_ = lean_string_utf8_byte_size(v_fst_5878_);
v_decide_5882_ = lean_nat_dec_eq(v_snd_5879_, v___x_5881_);
if (v_decide_5882_ == 0)
{
if (v_decide_5880_ == 0)
{
v___y_5870_ = v_pos_5877_;
v_snd_5871_ = v_snd_5879_;
goto v___jp_5869_;
}
else
{
uint32_t v___x_5883_; uint32_t v_c_5884_; uint8_t v___x_5885_; 
v___x_5883_ = 77;
v_c_5884_ = lean_string_utf8_get_fast(v_fst_5878_, v_snd_5879_);
v___x_5885_ = lean_uint32_dec_eq(v_c_5884_, v___x_5883_);
if (v___x_5885_ == 0)
{
lean_object* v___x_5886_; 
v___x_5886_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3);
v_snd_5865_ = v_snd_5879_;
v_pos_5866_ = v_pos_5877_;
v_err_5867_ = v___x_5886_;
goto v___jp_5864_;
}
else
{
lean_object* v___x_5888_; uint8_t v_isShared_5889_; uint8_t v_isSharedCheck_5902_; 
lean_inc(v_fst_5878_);
v_isSharedCheck_5902_ = !lean_is_exclusive(v_pos_5877_);
if (v_isSharedCheck_5902_ == 0)
{
lean_object* v_unused_5903_; lean_object* v_unused_5904_; 
v_unused_5903_ = lean_ctor_get(v_pos_5877_, 1);
lean_dec(v_unused_5903_);
v_unused_5904_ = lean_ctor_get(v_pos_5877_, 0);
lean_dec(v_unused_5904_);
v___x_5888_ = v_pos_5877_;
v_isShared_5889_ = v_isSharedCheck_5902_;
goto v_resetjp_5887_;
}
else
{
lean_dec(v_pos_5877_);
v___x_5888_ = lean_box(0);
v_isShared_5889_ = v_isSharedCheck_5902_;
goto v_resetjp_5887_;
}
v_resetjp_5887_:
{
lean_object* v___x_5890_; lean_object* v_it_x27_5892_; 
v___x_5890_ = lean_string_utf8_next_fast(v_fst_5878_, v_snd_5879_);
if (v_isShared_5889_ == 0)
{
lean_ctor_set(v___x_5888_, 1, v___x_5890_);
v_it_x27_5892_ = v___x_5888_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_fst_5878_);
lean_ctor_set(v_reuseFailAlloc_5901_, 1, v___x_5890_);
v_it_x27_5892_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
lean_object* v___x_5893_; lean_object* v___x_5894_; 
v___x_5893_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0);
v___x_5894_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(v___x_5893_, v_it_x27_5892_);
if (lean_obj_tag(v___x_5894_) == 0)
{
lean_object* v_pos_5895_; lean_object* v_res_5896_; lean_object* v___x_5897_; 
v_pos_5895_ = lean_ctor_get(v___x_5894_, 0);
lean_inc(v_pos_5895_);
v_res_5896_ = lean_ctor_get(v___x_5894_, 1);
lean_inc(v_res_5896_);
lean_dec_ref_known(v___x_5894_, 2);
v___x_5897_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5873_, v_res_5896_, v_pos_5895_);
if (lean_obj_tag(v___x_5897_) == 0)
{
lean_dec(v_snd_5879_);
return v___x_5897_;
}
else
{
lean_object* v_pos_5898_; 
v_pos_5898_ = lean_ctor_get(v___x_5897_, 0);
lean_inc(v_pos_5898_);
v_snd_5834_ = v_snd_5879_;
v___y_5835_ = v___x_5897_;
v_pos_5836_ = v_pos_5898_;
goto v___jp_5833_;
}
}
else
{
lean_object* v_pos_5899_; lean_object* v_err_5900_; 
v_pos_5899_ = lean_ctor_get(v___x_5894_, 0);
lean_inc(v_pos_5899_);
v_err_5900_ = lean_ctor_get(v___x_5894_, 1);
lean_inc(v_err_5900_);
lean_dec_ref_known(v___x_5894_, 2);
v_snd_5865_ = v_snd_5879_;
v_pos_5866_ = v_pos_5899_;
v_err_5867_ = v_err_5900_;
goto v___jp_5864_;
}
}
}
}
}
}
else
{
v___y_5870_ = v_pos_5877_;
v_snd_5871_ = v_snd_5879_;
goto v___jp_5869_;
}
}
}
v___jp_5905_:
{
lean_object* v___x_5909_; 
lean_inc_ref(v_pos_5907_);
v___x_5909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5909_, 0, v_pos_5907_);
lean_ctor_set(v___x_5909_, 1, v_err_5908_);
v_snd_5875_ = v_snd_5906_;
v___y_5876_ = v___x_5909_;
v_pos_5877_ = v_pos_5907_;
goto v___jp_5874_;
}
v___jp_5910_:
{
lean_object* v___x_5913_; 
v___x_5913_ = lean_box(0);
v_snd_5906_ = v_snd_5912_;
v_pos_5907_ = v___y_5911_;
v_err_5908_ = v___x_5913_;
goto v___jp_5905_;
}
v___jp_5915_:
{
lean_object* v_fst_5919_; lean_object* v_snd_5920_; uint8_t v_decide_5921_; 
v_fst_5919_ = lean_ctor_get(v_pos_5918_, 0);
v_snd_5920_ = lean_ctor_get(v_pos_5918_, 1);
lean_inc(v_snd_5920_);
v_decide_5921_ = lean_nat_dec_eq(v_snd_5916_, v_snd_5920_);
lean_dec(v_snd_5916_);
if (v_decide_5921_ == 0)
{
lean_dec(v_snd_5920_);
lean_dec_ref(v_pos_5918_);
return v___y_5917_;
}
else
{
lean_object* v___x_5922_; uint8_t v_decide_5923_; 
lean_dec_ref(v___y_5917_);
v___x_5922_ = lean_string_utf8_byte_size(v_fst_5919_);
v_decide_5923_ = lean_nat_dec_eq(v_snd_5920_, v___x_5922_);
if (v_decide_5923_ == 0)
{
if (v_decide_5921_ == 0)
{
v___y_5911_ = v_pos_5918_;
v_snd_5912_ = v_snd_5920_;
goto v___jp_5910_;
}
else
{
uint32_t v___x_5924_; uint32_t v_c_5925_; uint8_t v___x_5926_; 
v___x_5924_ = 68;
v_c_5925_ = lean_string_utf8_get_fast(v_fst_5919_, v_snd_5920_);
v___x_5926_ = lean_uint32_dec_eq(v_c_5925_, v___x_5924_);
if (v___x_5926_ == 0)
{
lean_object* v___x_5927_; 
v___x_5927_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3);
v_snd_5906_ = v_snd_5920_;
v_pos_5907_ = v_pos_5918_;
v_err_5908_ = v___x_5927_;
goto v___jp_5905_;
}
else
{
lean_object* v___x_5929_; uint8_t v_isShared_5930_; uint8_t v_isSharedCheck_5944_; 
lean_inc(v_fst_5919_);
v_isSharedCheck_5944_ = !lean_is_exclusive(v_pos_5918_);
if (v_isSharedCheck_5944_ == 0)
{
lean_object* v_unused_5945_; lean_object* v_unused_5946_; 
v_unused_5945_ = lean_ctor_get(v_pos_5918_, 1);
lean_dec(v_unused_5945_);
v_unused_5946_ = lean_ctor_get(v_pos_5918_, 0);
lean_dec(v_unused_5946_);
v___x_5929_ = v_pos_5918_;
v_isShared_5930_ = v_isSharedCheck_5944_;
goto v_resetjp_5928_;
}
else
{
lean_dec(v_pos_5918_);
v___x_5929_ = lean_box(0);
v_isShared_5930_ = v_isSharedCheck_5944_;
goto v_resetjp_5928_;
}
v_resetjp_5928_:
{
lean_object* v___x_5931_; lean_object* v_it_x27_5933_; 
v___x_5931_ = lean_string_utf8_next_fast(v_fst_5919_, v_snd_5920_);
if (v_isShared_5930_ == 0)
{
lean_ctor_set(v___x_5929_, 1, v___x_5931_);
v_it_x27_5933_ = v___x_5929_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5943_; 
v_reuseFailAlloc_5943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5943_, 0, v_fst_5919_);
lean_ctor_set(v_reuseFailAlloc_5943_, 1, v___x_5931_);
v_it_x27_5933_ = v_reuseFailAlloc_5943_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
lean_object* v___x_5934_; lean_object* v___x_5935_; 
v___x_5934_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0);
v___x_5935_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(v___x_5934_, v_it_x27_5933_);
if (lean_obj_tag(v___x_5935_) == 0)
{
lean_object* v_pos_5936_; lean_object* v_res_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; 
v_pos_5936_ = lean_ctor_get(v___x_5935_, 0);
lean_inc(v_pos_5936_);
v_res_5937_ = lean_ctor_get(v___x_5935_, 1);
lean_inc(v_res_5937_);
lean_dec_ref_known(v___x_5935_, 2);
v___x_5938_ = ((lean_object*)(l_Std_Time_parseModifier___closed__30));
v___x_5939_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5914_, v___x_5938_, v_res_5937_, v_pos_5936_);
if (lean_obj_tag(v___x_5939_) == 0)
{
lean_dec(v_snd_5920_);
return v___x_5939_;
}
else
{
lean_object* v_pos_5940_; 
v_pos_5940_ = lean_ctor_get(v___x_5939_, 0);
lean_inc(v_pos_5940_);
v_snd_5875_ = v_snd_5920_;
v___y_5876_ = v___x_5939_;
v_pos_5877_ = v_pos_5940_;
goto v___jp_5874_;
}
}
else
{
lean_object* v_pos_5941_; lean_object* v_err_5942_; 
v_pos_5941_ = lean_ctor_get(v___x_5935_, 0);
lean_inc(v_pos_5941_);
v_err_5942_ = lean_ctor_get(v___x_5935_, 1);
lean_inc(v_err_5942_);
lean_dec_ref_known(v___x_5935_, 2);
v_snd_5906_ = v_snd_5920_;
v_pos_5907_ = v_pos_5941_;
v_err_5908_ = v_err_5942_;
goto v___jp_5905_;
}
}
}
}
}
}
else
{
v___y_5911_ = v_pos_5918_;
v_snd_5912_ = v_snd_5920_;
goto v___jp_5910_;
}
}
}
v___jp_5947_:
{
lean_object* v___x_5951_; 
lean_inc_ref(v_pos_5949_);
v___x_5951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5951_, 0, v_pos_5949_);
lean_ctor_set(v___x_5951_, 1, v_err_5950_);
v_snd_5916_ = v_snd_5948_;
v___y_5917_ = v___x_5951_;
v_pos_5918_ = v_pos_5949_;
goto v___jp_5915_;
}
v___jp_5952_:
{
lean_object* v___x_5955_; 
v___x_5955_ = lean_box(0);
v_snd_5948_ = v_snd_5954_;
v_pos_5949_ = v___y_5953_;
v_err_5950_ = v___x_5955_;
goto v___jp_5947_;
}
v___jp_5957_:
{
lean_object* v_fst_5961_; lean_object* v_snd_5962_; uint8_t v_decide_5963_; 
v_fst_5961_ = lean_ctor_get(v_pos_5960_, 0);
v_snd_5962_ = lean_ctor_get(v_pos_5960_, 1);
lean_inc(v_snd_5962_);
v_decide_5963_ = lean_nat_dec_eq(v_snd_5958_, v_snd_5962_);
lean_dec(v_snd_5958_);
if (v_decide_5963_ == 0)
{
lean_dec(v_snd_5962_);
lean_dec_ref(v_pos_5960_);
return v___y_5959_;
}
else
{
lean_object* v___x_5964_; uint8_t v_decide_5965_; 
lean_dec_ref(v___y_5959_);
v___x_5964_ = lean_string_utf8_byte_size(v_fst_5961_);
v_decide_5965_ = lean_nat_dec_eq(v_snd_5962_, v___x_5964_);
if (v_decide_5965_ == 0)
{
if (v_decide_5963_ == 0)
{
v___y_5953_ = v_pos_5960_;
v_snd_5954_ = v_snd_5962_;
goto v___jp_5952_;
}
else
{
uint32_t v___x_5966_; uint32_t v_c_5967_; uint8_t v___x_5968_; 
v___x_5966_ = 117;
v_c_5967_ = lean_string_utf8_get_fast(v_fst_5961_, v_snd_5962_);
v___x_5968_ = lean_uint32_dec_eq(v_c_5967_, v___x_5966_);
if (v___x_5968_ == 0)
{
lean_object* v___x_5969_; 
v___x_5969_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3);
v_snd_5948_ = v_snd_5962_;
v_pos_5949_ = v_pos_5960_;
v_err_5950_ = v___x_5969_;
goto v___jp_5947_;
}
else
{
lean_object* v___x_5971_; uint8_t v_isShared_5972_; uint8_t v_isSharedCheck_5985_; 
lean_inc(v_fst_5961_);
v_isSharedCheck_5985_ = !lean_is_exclusive(v_pos_5960_);
if (v_isSharedCheck_5985_ == 0)
{
lean_object* v_unused_5986_; lean_object* v_unused_5987_; 
v_unused_5986_ = lean_ctor_get(v_pos_5960_, 1);
lean_dec(v_unused_5986_);
v_unused_5987_ = lean_ctor_get(v_pos_5960_, 0);
lean_dec(v_unused_5987_);
v___x_5971_ = v_pos_5960_;
v_isShared_5972_ = v_isSharedCheck_5985_;
goto v_resetjp_5970_;
}
else
{
lean_dec(v_pos_5960_);
v___x_5971_ = lean_box(0);
v_isShared_5972_ = v_isSharedCheck_5985_;
goto v_resetjp_5970_;
}
v_resetjp_5970_:
{
lean_object* v___x_5973_; lean_object* v_it_x27_5975_; 
v___x_5973_ = lean_string_utf8_next_fast(v_fst_5961_, v_snd_5962_);
if (v_isShared_5972_ == 0)
{
lean_ctor_set(v___x_5971_, 1, v___x_5973_);
v_it_x27_5975_ = v___x_5971_;
goto v_reusejp_5974_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v_fst_5961_);
lean_ctor_set(v_reuseFailAlloc_5984_, 1, v___x_5973_);
v_it_x27_5975_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5974_;
}
v_reusejp_5974_:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; 
v___x_5976_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0);
v___x_5977_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(v___x_5976_, v_it_x27_5975_);
if (lean_obj_tag(v___x_5977_) == 0)
{
lean_object* v_pos_5978_; lean_object* v_res_5979_; lean_object* v___x_5980_; 
v_pos_5978_ = lean_ctor_get(v___x_5977_, 0);
lean_inc(v_pos_5978_);
v_res_5979_ = lean_ctor_get(v___x_5977_, 1);
lean_inc(v_res_5979_);
lean_dec_ref_known(v___x_5977_, 2);
v___x_5980_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5956_, v_res_5979_, v_pos_5978_);
if (lean_obj_tag(v___x_5980_) == 0)
{
lean_dec(v_snd_5962_);
return v___x_5980_;
}
else
{
lean_object* v_pos_5981_; 
v_pos_5981_ = lean_ctor_get(v___x_5980_, 0);
lean_inc(v_pos_5981_);
v_snd_5916_ = v_snd_5962_;
v___y_5917_ = v___x_5980_;
v_pos_5918_ = v_pos_5981_;
goto v___jp_5915_;
}
}
else
{
lean_object* v_pos_5982_; lean_object* v_err_5983_; 
v_pos_5982_ = lean_ctor_get(v___x_5977_, 0);
lean_inc(v_pos_5982_);
v_err_5983_ = lean_ctor_get(v___x_5977_, 1);
lean_inc(v_err_5983_);
lean_dec_ref_known(v___x_5977_, 2);
v_snd_5948_ = v_snd_5962_;
v_pos_5949_ = v_pos_5982_;
v_err_5950_ = v_err_5983_;
goto v___jp_5947_;
}
}
}
}
}
}
else
{
v___y_5953_ = v_pos_5960_;
v_snd_5954_ = v_snd_5962_;
goto v___jp_5952_;
}
}
}
v___jp_5988_:
{
lean_object* v___x_5992_; 
lean_inc_ref(v_pos_5990_);
v___x_5992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5992_, 0, v_pos_5990_);
lean_ctor_set(v___x_5992_, 1, v_err_5991_);
v_snd_5958_ = v_snd_5989_;
v___y_5959_ = v___x_5992_;
v_pos_5960_ = v_pos_5990_;
goto v___jp_5957_;
}
v___jp_5993_:
{
lean_object* v___x_5996_; 
v___x_5996_ = lean_box(0);
v_snd_5989_ = v_snd_5995_;
v_pos_5990_ = v___y_5994_;
v_err_5991_ = v___x_5996_;
goto v___jp_5988_;
}
v___jp_5998_:
{
lean_object* v_fst_6002_; lean_object* v_snd_6003_; uint8_t v_decide_6004_; 
v_fst_6002_ = lean_ctor_get(v_pos_6001_, 0);
v_snd_6003_ = lean_ctor_get(v_pos_6001_, 1);
lean_inc(v_snd_6003_);
v_decide_6004_ = lean_nat_dec_eq(v_snd_5999_, v_snd_6003_);
lean_dec(v_snd_5999_);
if (v_decide_6004_ == 0)
{
lean_dec(v_snd_6003_);
lean_dec_ref(v_pos_6001_);
return v___y_6000_;
}
else
{
lean_object* v___x_6005_; uint8_t v_decide_6006_; 
lean_dec_ref(v___y_6000_);
v___x_6005_ = lean_string_utf8_byte_size(v_fst_6002_);
v_decide_6006_ = lean_nat_dec_eq(v_snd_6003_, v___x_6005_);
if (v_decide_6006_ == 0)
{
if (v_decide_6004_ == 0)
{
v___y_5994_ = v_pos_6001_;
v_snd_5995_ = v_snd_6003_;
goto v___jp_5993_;
}
else
{
uint32_t v___x_6007_; uint32_t v_c_6008_; uint8_t v___x_6009_; 
v___x_6007_ = 89;
v_c_6008_ = lean_string_utf8_get_fast(v_fst_6002_, v_snd_6003_);
v___x_6009_ = lean_uint32_dec_eq(v_c_6008_, v___x_6007_);
if (v___x_6009_ == 0)
{
lean_object* v___x_6010_; 
v___x_6010_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3);
v_snd_5989_ = v_snd_6003_;
v_pos_5990_ = v_pos_6001_;
v_err_5991_ = v___x_6010_;
goto v___jp_5988_;
}
else
{
lean_object* v___x_6012_; uint8_t v_isShared_6013_; uint8_t v_isSharedCheck_6026_; 
lean_inc(v_fst_6002_);
v_isSharedCheck_6026_ = !lean_is_exclusive(v_pos_6001_);
if (v_isSharedCheck_6026_ == 0)
{
lean_object* v_unused_6027_; lean_object* v_unused_6028_; 
v_unused_6027_ = lean_ctor_get(v_pos_6001_, 1);
lean_dec(v_unused_6027_);
v_unused_6028_ = lean_ctor_get(v_pos_6001_, 0);
lean_dec(v_unused_6028_);
v___x_6012_ = v_pos_6001_;
v_isShared_6013_ = v_isSharedCheck_6026_;
goto v_resetjp_6011_;
}
else
{
lean_dec(v_pos_6001_);
v___x_6012_ = lean_box(0);
v_isShared_6013_ = v_isSharedCheck_6026_;
goto v_resetjp_6011_;
}
v_resetjp_6011_:
{
lean_object* v___x_6014_; lean_object* v_it_x27_6016_; 
v___x_6014_ = lean_string_utf8_next_fast(v_fst_6002_, v_snd_6003_);
if (v_isShared_6013_ == 0)
{
lean_ctor_set(v___x_6012_, 1, v___x_6014_);
v_it_x27_6016_ = v___x_6012_;
goto v_reusejp_6015_;
}
else
{
lean_object* v_reuseFailAlloc_6025_; 
v_reuseFailAlloc_6025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6025_, 0, v_fst_6002_);
lean_ctor_set(v_reuseFailAlloc_6025_, 1, v___x_6014_);
v_it_x27_6016_ = v_reuseFailAlloc_6025_;
goto v_reusejp_6015_;
}
v_reusejp_6015_:
{
lean_object* v___x_6017_; lean_object* v___x_6018_; 
v___x_6017_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0);
v___x_6018_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(v___x_6017_, v_it_x27_6016_);
if (lean_obj_tag(v___x_6018_) == 0)
{
lean_object* v_pos_6019_; lean_object* v_res_6020_; lean_object* v___x_6021_; 
v_pos_6019_ = lean_ctor_get(v___x_6018_, 0);
lean_inc(v_pos_6019_);
v_res_6020_ = lean_ctor_get(v___x_6018_, 1);
lean_inc(v_res_6020_);
lean_dec_ref_known(v___x_6018_, 2);
v___x_6021_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5997_, v_res_6020_, v_pos_6019_);
if (lean_obj_tag(v___x_6021_) == 0)
{
lean_dec(v_snd_6003_);
return v___x_6021_;
}
else
{
lean_object* v_pos_6022_; 
v_pos_6022_ = lean_ctor_get(v___x_6021_, 0);
lean_inc(v_pos_6022_);
v_snd_5958_ = v_snd_6003_;
v___y_5959_ = v___x_6021_;
v_pos_5960_ = v_pos_6022_;
goto v___jp_5957_;
}
}
else
{
lean_object* v_pos_6023_; lean_object* v_err_6024_; 
v_pos_6023_ = lean_ctor_get(v___x_6018_, 0);
lean_inc(v_pos_6023_);
v_err_6024_ = lean_ctor_get(v___x_6018_, 1);
lean_inc(v_err_6024_);
lean_dec_ref_known(v___x_6018_, 2);
v_snd_5989_ = v_snd_6003_;
v_pos_5990_ = v_pos_6023_;
v_err_5991_ = v_err_6024_;
goto v___jp_5988_;
}
}
}
}
}
}
else
{
v___y_5994_ = v_pos_6001_;
v_snd_5995_ = v_snd_6003_;
goto v___jp_5993_;
}
}
}
v___jp_6029_:
{
lean_object* v___x_6033_; 
lean_inc_ref(v_pos_6031_);
v___x_6033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6033_, 0, v_pos_6031_);
lean_ctor_set(v___x_6033_, 1, v_err_6032_);
v_snd_5999_ = v_snd_6030_;
v___y_6000_ = v___x_6033_;
v_pos_6001_ = v_pos_6031_;
goto v___jp_5998_;
}
v___jp_6034_:
{
lean_object* v___x_6037_; 
v___x_6037_ = lean_box(0);
v_snd_6030_ = v_snd_6036_;
v_pos_6031_ = v___y_6035_;
v_err_6032_ = v___x_6037_;
goto v___jp_6029_;
}
v___jp_6039_:
{
lean_object* v_fst_6042_; lean_object* v_snd_6043_; uint8_t v_decide_6044_; 
v_fst_6042_ = lean_ctor_get(v_pos_6041_, 0);
v_snd_6043_ = lean_ctor_get(v_pos_6041_, 1);
lean_inc(v_snd_6043_);
v_decide_6044_ = lean_nat_dec_eq(v_snd_4577_, v_snd_6043_);
lean_dec(v_snd_4577_);
if (v_decide_6044_ == 0)
{
lean_dec(v_snd_6043_);
lean_dec_ref(v_pos_6041_);
return v___y_6040_;
}
else
{
lean_object* v___x_6045_; uint8_t v_decide_6046_; 
lean_dec_ref(v___y_6040_);
v___x_6045_ = lean_string_utf8_byte_size(v_fst_6042_);
v_decide_6046_ = lean_nat_dec_eq(v_snd_6043_, v___x_6045_);
if (v_decide_6046_ == 0)
{
if (v_decide_6044_ == 0)
{
v___y_6035_ = v_pos_6041_;
v_snd_6036_ = v_snd_6043_;
goto v___jp_6034_;
}
else
{
uint32_t v___x_6047_; uint32_t v_c_6048_; uint8_t v___x_6049_; 
v___x_6047_ = 121;
v_c_6048_ = lean_string_utf8_get_fast(v_fst_6042_, v_snd_6043_);
v___x_6049_ = lean_uint32_dec_eq(v_c_6048_, v___x_6047_);
if (v___x_6049_ == 0)
{
lean_object* v___x_6050_; 
v___x_6050_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3);
v_snd_6030_ = v_snd_6043_;
v_pos_6031_ = v_pos_6041_;
v_err_6032_ = v___x_6050_;
goto v___jp_6029_;
}
else
{
lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6066_; 
lean_inc(v_fst_6042_);
v_isSharedCheck_6066_ = !lean_is_exclusive(v_pos_6041_);
if (v_isSharedCheck_6066_ == 0)
{
lean_object* v_unused_6067_; lean_object* v_unused_6068_; 
v_unused_6067_ = lean_ctor_get(v_pos_6041_, 1);
lean_dec(v_unused_6067_);
v_unused_6068_ = lean_ctor_get(v_pos_6041_, 0);
lean_dec(v_unused_6068_);
v___x_6052_ = v_pos_6041_;
v_isShared_6053_ = v_isSharedCheck_6066_;
goto v_resetjp_6051_;
}
else
{
lean_dec(v_pos_6041_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6066_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6054_; lean_object* v_it_x27_6056_; 
v___x_6054_ = lean_string_utf8_next_fast(v_fst_6042_, v_snd_6043_);
if (v_isShared_6053_ == 0)
{
lean_ctor_set(v___x_6052_, 1, v___x_6054_);
v_it_x27_6056_ = v___x_6052_;
goto v_reusejp_6055_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_fst_6042_);
lean_ctor_set(v_reuseFailAlloc_6065_, 1, v___x_6054_);
v_it_x27_6056_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6055_;
}
v_reusejp_6055_:
{
lean_object* v___x_6057_; lean_object* v___x_6058_; 
v___x_6057_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0);
v___x_6058_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(v___x_6057_, v_it_x27_6056_);
if (lean_obj_tag(v___x_6058_) == 0)
{
lean_object* v_pos_6059_; lean_object* v_res_6060_; lean_object* v___x_6061_; 
v_pos_6059_ = lean_ctor_get(v___x_6058_, 0);
lean_inc(v_pos_6059_);
v_res_6060_ = lean_ctor_get(v___x_6058_, 1);
lean_inc(v_res_6060_);
lean_dec_ref_known(v___x_6058_, 2);
v___x_6061_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_6038_, v_res_6060_, v_pos_6059_);
if (lean_obj_tag(v___x_6061_) == 0)
{
lean_dec(v_snd_6043_);
return v___x_6061_;
}
else
{
lean_object* v_pos_6062_; 
v_pos_6062_ = lean_ctor_get(v___x_6061_, 0);
lean_inc(v_pos_6062_);
v_snd_5999_ = v_snd_6043_;
v___y_6000_ = v___x_6061_;
v_pos_6001_ = v_pos_6062_;
goto v___jp_5998_;
}
}
else
{
lean_object* v_pos_6063_; lean_object* v_err_6064_; 
v_pos_6063_ = lean_ctor_get(v___x_6058_, 0);
lean_inc(v_pos_6063_);
v_err_6064_ = lean_ctor_get(v___x_6058_, 1);
lean_inc(v_err_6064_);
lean_dec_ref_known(v___x_6058_, 2);
v_snd_6030_ = v_snd_6043_;
v_pos_6031_ = v_pos_6063_;
v_err_6032_ = v_err_6064_;
goto v___jp_6029_;
}
}
}
}
}
}
else
{
v___y_6035_ = v_pos_6041_;
v_snd_6036_ = v_snd_6043_;
goto v___jp_6034_;
}
}
}
v___jp_6069_:
{
lean_object* v___x_6072_; 
lean_inc_ref(v_pos_6070_);
v___x_6072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6072_, 0, v_pos_6070_);
lean_ctor_set(v___x_6072_, 1, v_err_6071_);
v___y_6040_ = v___x_6072_;
v_pos_6041_ = v_pos_6070_;
goto v___jp_6039_;
}
}
}
lean_object* runtime_initialize_Std_Time_Zoned(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Format_Modifier(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
