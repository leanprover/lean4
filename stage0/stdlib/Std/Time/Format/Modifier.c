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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
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
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'x'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'Y'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'n'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'G'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'V'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'S'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'h'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'Q'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'D'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'X'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'z'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 's'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'K'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'e'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'M'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'w'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'd'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'c'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'E'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'a'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'O'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'A'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'L'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'q'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'H'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'v'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'W'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'k'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'y'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'b'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'm'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'u'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'Z'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'N'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'F'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'B'"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_parseModifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__0 = (const lean_object*)&l_Std_Time_parseModifier___closed__0_value;
static const lean_string_object l_Std_Time_parseModifier___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Z"};
static const lean_object* l_Std_Time_parseModifier___closed__1 = (const lean_object*)&l_Std_Time_parseModifier___closed__1_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__2 = (const lean_object*)&l_Std_Time_parseModifier___closed__2_value;
static const lean_string_object l_Std_Time_parseModifier___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Std_Time_parseModifier___closed__3 = (const lean_object*)&l_Std_Time_parseModifier___closed__3_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__4 = (const lean_object*)&l_Std_Time_parseModifier___closed__4_value;
static const lean_string_object l_Std_Time_parseModifier___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "X"};
static const lean_object* l_Std_Time_parseModifier___closed__5 = (const lean_object*)&l_Std_Time_parseModifier___closed__5_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__6 = (const lean_object*)&l_Std_Time_parseModifier___closed__6_value;
static const lean_string_object l_Std_Time_parseModifier___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "O"};
static const lean_object* l_Std_Time_parseModifier___closed__7 = (const lean_object*)&l_Std_Time_parseModifier___closed__7_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__8 = (const lean_object*)&l_Std_Time_parseModifier___closed__8_value;
static const lean_string_object l_Std_Time_parseModifier___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l_Std_Time_parseModifier___closed__9 = (const lean_object*)&l_Std_Time_parseModifier___closed__9_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__10 = (const lean_object*)&l_Std_Time_parseModifier___closed__10_value;
static const lean_string_object l_Std_Time_parseModifier___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "z"};
static const lean_object* l_Std_Time_parseModifier___closed__11 = (const lean_object*)&l_Std_Time_parseModifier___closed__11_value;
static const lean_string_object l_Std_Time_parseModifier___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "V"};
static const lean_object* l_Std_Time_parseModifier___closed__12 = (const lean_object*)&l_Std_Time_parseModifier___closed__12_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__6, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__13 = (const lean_object*)&l_Std_Time_parseModifier___closed__13_value;
static const lean_string_object l_Std_Time_parseModifier___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "N"};
static const lean_object* l_Std_Time_parseModifier___closed__14 = (const lean_object*)&l_Std_Time_parseModifier___closed__14_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__7, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__15 = (const lean_object*)&l_Std_Time_parseModifier___closed__15_value;
static const lean_string_object l_Std_Time_parseModifier___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l_Std_Time_parseModifier___closed__16 = (const lean_object*)&l_Std_Time_parseModifier___closed__16_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__8, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__17 = (const lean_object*)&l_Std_Time_parseModifier___closed__17_value;
static const lean_string_object l_Std_Time_parseModifier___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "A"};
static const lean_object* l_Std_Time_parseModifier___closed__18 = (const lean_object*)&l_Std_Time_parseModifier___closed__18_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__9, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__19 = (const lean_object*)&l_Std_Time_parseModifier___closed__19_value;
static const lean_string_object l_Std_Time_parseModifier___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "S"};
static const lean_object* l_Std_Time_parseModifier___closed__20 = (const lean_object*)&l_Std_Time_parseModifier___closed__20_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__10, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__21 = (const lean_object*)&l_Std_Time_parseModifier___closed__21_value;
static const lean_string_object l_Std_Time_parseModifier___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Std_Time_parseModifier___closed__22 = (const lean_object*)&l_Std_Time_parseModifier___closed__22_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__11, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__23 = (const lean_object*)&l_Std_Time_parseModifier___closed__23_value;
static const lean_string_object l_Std_Time_parseModifier___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Std_Time_parseModifier___closed__24 = (const lean_object*)&l_Std_Time_parseModifier___closed__24_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__12, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__25 = (const lean_object*)&l_Std_Time_parseModifier___closed__25_value;
static const lean_string_object l_Std_Time_parseModifier___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "H"};
static const lean_object* l_Std_Time_parseModifier___closed__26 = (const lean_object*)&l_Std_Time_parseModifier___closed__26_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__13, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__27 = (const lean_object*)&l_Std_Time_parseModifier___closed__27_value;
static const lean_string_object l_Std_Time_parseModifier___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l_Std_Time_parseModifier___closed__28 = (const lean_object*)&l_Std_Time_parseModifier___closed__28_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__14, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__29 = (const lean_object*)&l_Std_Time_parseModifier___closed__29_value;
static const lean_string_object l_Std_Time_parseModifier___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "K"};
static const lean_object* l_Std_Time_parseModifier___closed__30 = (const lean_object*)&l_Std_Time_parseModifier___closed__30_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__15, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__31 = (const lean_object*)&l_Std_Time_parseModifier___closed__31_value;
static const lean_string_object l_Std_Time_parseModifier___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Std_Time_parseModifier___closed__32 = (const lean_object*)&l_Std_Time_parseModifier___closed__32_value;
static const lean_string_object l_Std_Time_parseModifier___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "B"};
static const lean_object* l_Std_Time_parseModifier___closed__33 = (const lean_object*)&l_Std_Time_parseModifier___closed__33_value;
static const lean_string_object l_Std_Time_parseModifier___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_Std_Time_parseModifier___closed__34 = (const lean_object*)&l_Std_Time_parseModifier___closed__34_value;
static const lean_string_object l_Std_Time_parseModifier___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Std_Time_parseModifier___closed__35 = (const lean_object*)&l_Std_Time_parseModifier___closed__35_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__16, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__36 = (const lean_object*)&l_Std_Time_parseModifier___closed__36_value;
static const lean_string_object l_Std_Time_parseModifier___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "F"};
static const lean_object* l_Std_Time_parseModifier___closed__37 = (const lean_object*)&l_Std_Time_parseModifier___closed__37_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__17, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__38 = (const lean_object*)&l_Std_Time_parseModifier___closed__38_value;
static const lean_string_object l_Std_Time_parseModifier___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Std_Time_parseModifier___closed__39 = (const lean_object*)&l_Std_Time_parseModifier___closed__39_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__18, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__40 = (const lean_object*)&l_Std_Time_parseModifier___closed__40_value;
static const lean_string_object l_Std_Time_parseModifier___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l_Std_Time_parseModifier___closed__41 = (const lean_object*)&l_Std_Time_parseModifier___closed__41_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__19___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__42 = (const lean_object*)&l_Std_Time_parseModifier___closed__42_value;
static const lean_string_object l_Std_Time_parseModifier___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "E"};
static const lean_object* l_Std_Time_parseModifier___closed__43 = (const lean_object*)&l_Std_Time_parseModifier___closed__43_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__20, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__44 = (const lean_object*)&l_Std_Time_parseModifier___closed__44_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__45 = (const lean_object*)&l_Std_Time_parseModifier___closed__45_value;
static const lean_string_object l_Std_Time_parseModifier___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "W"};
static const lean_object* l_Std_Time_parseModifier___closed__46 = (const lean_object*)&l_Std_Time_parseModifier___closed__46_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__21, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__47 = (const lean_object*)&l_Std_Time_parseModifier___closed__47_value;
static const lean_string_object l_Std_Time_parseModifier___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "w"};
static const lean_object* l_Std_Time_parseModifier___closed__48 = (const lean_object*)&l_Std_Time_parseModifier___closed__48_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__22, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__49 = (const lean_object*)&l_Std_Time_parseModifier___closed__49_value;
static const lean_string_object l_Std_Time_parseModifier___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "q"};
static const lean_object* l_Std_Time_parseModifier___closed__50 = (const lean_object*)&l_Std_Time_parseModifier___closed__50_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__23, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__51 = (const lean_object*)&l_Std_Time_parseModifier___closed__51_value;
static const lean_string_object l_Std_Time_parseModifier___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l_Std_Time_parseModifier___closed__52 = (const lean_object*)&l_Std_Time_parseModifier___closed__52_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__24, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__53 = (const lean_object*)&l_Std_Time_parseModifier___closed__53_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l_Std_Time_parseModifier___closed__54 = (const lean_object*)&l_Std_Time_parseModifier___closed__54_value;
static const lean_string_object l_Std_Time_parseModifier___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "d"};
static const lean_object* l_Std_Time_parseModifier___closed__55 = (const lean_object*)&l_Std_Time_parseModifier___closed__55_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__25, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__56 = (const lean_object*)&l_Std_Time_parseModifier___closed__56_value;
static const lean_string_object l_Std_Time_parseModifier___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "L"};
static const lean_object* l_Std_Time_parseModifier___closed__57 = (const lean_object*)&l_Std_Time_parseModifier___closed__57_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__26, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__58 = (const lean_object*)&l_Std_Time_parseModifier___closed__58_value;
static const lean_string_object l_Std_Time_parseModifier___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "M"};
static const lean_object* l_Std_Time_parseModifier___closed__59 = (const lean_object*)&l_Std_Time_parseModifier___closed__59_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__27, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__60 = (const lean_object*)&l_Std_Time_parseModifier___closed__60_value;
static const lean_string_object l_Std_Time_parseModifier___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "D"};
static const lean_object* l_Std_Time_parseModifier___closed__61 = (const lean_object*)&l_Std_Time_parseModifier___closed__61_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))} };
static const lean_object* l_Std_Time_parseModifier___closed__62 = (const lean_object*)&l_Std_Time_parseModifier___closed__62_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__28, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__63 = (const lean_object*)&l_Std_Time_parseModifier___closed__63_value;
static const lean_string_object l_Std_Time_parseModifier___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l_Std_Time_parseModifier___closed__64 = (const lean_object*)&l_Std_Time_parseModifier___closed__64_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__29, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__65 = (const lean_object*)&l_Std_Time_parseModifier___closed__65_value;
static const lean_string_object l_Std_Time_parseModifier___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Y"};
static const lean_object* l_Std_Time_parseModifier___closed__66 = (const lean_object*)&l_Std_Time_parseModifier___closed__66_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__30, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__67 = (const lean_object*)&l_Std_Time_parseModifier___closed__67_value;
static const lean_string_object l_Std_Time_parseModifier___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l_Std_Time_parseModifier___closed__68 = (const lean_object*)&l_Std_Time_parseModifier___closed__68_value;
static const lean_string_object l_Std_Time_parseModifier___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "G"};
static const lean_object* l_Std_Time_parseModifier___closed__69 = (const lean_object*)&l_Std_Time_parseModifier___closed__69_value;
static const lean_closure_object l_Std_Time_parseModifier___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_parseModifier___lam__31___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_parseModifier___closed__70 = (const lean_object*)&l_Std_Time_parseModifier___closed__70_value;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(lean_object* v_acc_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_fst_3062_; lean_object* v_snd_3063_; lean_object* v_pos_3065_; lean_object* v_snd_3066_; lean_object* v_err_3067_; lean_object* v___x_3071_; uint8_t v_decide_3072_; 
v_fst_3062_ = lean_ctor_get(v_a_3061_, 0);
v_snd_3063_ = lean_ctor_get(v_a_3061_, 1);
lean_inc(v_snd_3063_);
v___x_3071_ = lean_string_utf8_byte_size(v_fst_3062_);
v_decide_3072_ = lean_nat_dec_eq(v_snd_3063_, v___x_3071_);
if (v_decide_3072_ == 0)
{
uint32_t v___x_3073_; uint32_t v_c_3074_; uint8_t v___x_3075_; 
v___x_3073_ = 120;
v_c_3074_ = lean_string_utf8_get_fast(v_fst_3062_, v_snd_3063_);
v___x_3075_ = lean_uint32_dec_eq(v_c_3074_, v___x_3073_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1));
lean_inc(v_snd_3063_);
v_pos_3065_ = v_a_3061_;
v_snd_3066_ = v_snd_3063_;
v_err_3067_ = v___x_3076_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3086_; 
lean_inc(v_fst_3062_);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_a_3061_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; lean_object* v_unused_3088_; 
v_unused_3087_ = lean_ctor_get(v_a_3061_, 1);
lean_dec(v_unused_3087_);
v_unused_3088_ = lean_ctor_get(v_a_3061_, 0);
lean_dec(v_unused_3088_);
v___x_3078_ = v_a_3061_;
v_isShared_3079_ = v_isSharedCheck_3086_;
goto v_resetjp_3077_;
}
else
{
lean_dec(v_a_3061_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3086_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v_it_x27_3082_; 
v___x_3080_ = lean_string_utf8_next_fast(v_fst_3062_, v_snd_3063_);
lean_dec(v_snd_3063_);
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
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_fst_3062_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_3080_);
v_it_x27_3082_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_string_push(v_acc_3060_, v___x_3073_);
v_acc_3060_ = v___x_3083_;
v_a_3061_ = v_it_x27_3082_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_box(0);
lean_inc(v_snd_3063_);
v_pos_3065_ = v_a_3061_;
v_snd_3066_ = v_snd_3063_;
v_err_3067_ = v___x_3089_;
goto v___jp_3064_;
}
v___jp_3064_:
{
uint8_t v_decide_3068_; 
v_decide_3068_ = lean_nat_dec_eq(v_snd_3063_, v_snd_3066_);
lean_dec(v_snd_3066_);
lean_dec(v_snd_3063_);
if (v_decide_3068_ == 0)
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(lean_object* v_acc_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_fst_3095_; lean_object* v_snd_3096_; lean_object* v_pos_3098_; lean_object* v_snd_3099_; lean_object* v_err_3100_; lean_object* v___x_3104_; uint8_t v_decide_3105_; 
v_fst_3095_ = lean_ctor_get(v_a_3094_, 0);
v_snd_3096_ = lean_ctor_get(v_a_3094_, 1);
lean_inc(v_snd_3096_);
v___x_3104_ = lean_string_utf8_byte_size(v_fst_3095_);
v_decide_3105_ = lean_nat_dec_eq(v_snd_3096_, v___x_3104_);
if (v_decide_3105_ == 0)
{
uint32_t v___x_3106_; uint32_t v_c_3107_; uint8_t v___x_3108_; 
v___x_3106_ = 89;
v_c_3107_ = lean_string_utf8_get_fast(v_fst_3095_, v_snd_3096_);
v___x_3108_ = lean_uint32_dec_eq(v_c_3107_, v___x_3106_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
v___x_3109_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1));
lean_inc(v_snd_3096_);
v_pos_3098_ = v_a_3094_;
v_snd_3099_ = v_snd_3096_;
v_err_3100_ = v___x_3109_;
goto v___jp_3097_;
}
else
{
lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3119_; 
lean_inc(v_fst_3095_);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_a_3094_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; lean_object* v_unused_3121_; 
v_unused_3120_ = lean_ctor_get(v_a_3094_, 1);
lean_dec(v_unused_3120_);
v_unused_3121_ = lean_ctor_get(v_a_3094_, 0);
lean_dec(v_unused_3121_);
v___x_3111_ = v_a_3094_;
v_isShared_3112_ = v_isSharedCheck_3119_;
goto v_resetjp_3110_;
}
else
{
lean_dec(v_a_3094_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3119_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v_it_x27_3115_; 
v___x_3113_ = lean_string_utf8_next_fast(v_fst_3095_, v_snd_3096_);
lean_dec(v_snd_3096_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v___x_3113_);
v_it_x27_3115_ = v___x_3111_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_fst_3095_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3113_);
v_it_x27_3115_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_string_push(v_acc_3093_, v___x_3106_);
v_acc_3093_ = v___x_3116_;
v_a_3094_ = v_it_x27_3115_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_box(0);
lean_inc(v_snd_3096_);
v_pos_3098_ = v_a_3094_;
v_snd_3099_ = v_snd_3096_;
v_err_3100_ = v___x_3122_;
goto v___jp_3097_;
}
v___jp_3097_:
{
uint8_t v_decide_3101_; 
v_decide_3101_ = lean_nat_dec_eq(v_snd_3096_, v_snd_3099_);
lean_dec(v_snd_3099_);
lean_dec(v_snd_3096_);
if (v_decide_3101_ == 0)
{
lean_object* v___x_3102_; 
lean_dec_ref(v_acc_3093_);
lean_inc(v_err_3100_);
v___x_3102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_pos_3098_);
lean_ctor_set(v___x_3102_, 1, v_err_3100_);
return v___x_3102_;
}
else
{
lean_object* v___x_3103_; 
v___x_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3103_, 0, v_pos_3098_);
lean_ctor_set(v___x_3103_, 1, v_acc_3093_);
return v___x_3103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(lean_object* v_acc_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v_fst_3128_; lean_object* v_snd_3129_; lean_object* v_pos_3131_; lean_object* v_snd_3132_; lean_object* v_err_3133_; lean_object* v___x_3137_; uint8_t v_decide_3138_; 
v_fst_3128_ = lean_ctor_get(v_a_3127_, 0);
v_snd_3129_ = lean_ctor_get(v_a_3127_, 1);
lean_inc(v_snd_3129_);
v___x_3137_ = lean_string_utf8_byte_size(v_fst_3128_);
v_decide_3138_ = lean_nat_dec_eq(v_snd_3129_, v___x_3137_);
if (v_decide_3138_ == 0)
{
uint32_t v___x_3139_; uint32_t v_c_3140_; uint8_t v___x_3141_; 
v___x_3139_ = 110;
v_c_3140_ = lean_string_utf8_get_fast(v_fst_3128_, v_snd_3129_);
v___x_3141_ = lean_uint32_dec_eq(v_c_3140_, v___x_3139_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; 
v___x_3142_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1));
lean_inc(v_snd_3129_);
v_pos_3131_ = v_a_3127_;
v_snd_3132_ = v_snd_3129_;
v_err_3133_ = v___x_3142_;
goto v___jp_3130_;
}
else
{
lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3152_; 
lean_inc(v_fst_3128_);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_a_3127_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; lean_object* v_unused_3154_; 
v_unused_3153_ = lean_ctor_get(v_a_3127_, 1);
lean_dec(v_unused_3153_);
v_unused_3154_ = lean_ctor_get(v_a_3127_, 0);
lean_dec(v_unused_3154_);
v___x_3144_ = v_a_3127_;
v_isShared_3145_ = v_isSharedCheck_3152_;
goto v_resetjp_3143_;
}
else
{
lean_dec(v_a_3127_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3152_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v_it_x27_3148_; 
v___x_3146_ = lean_string_utf8_next_fast(v_fst_3128_, v_snd_3129_);
lean_dec(v_snd_3129_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 1, v___x_3146_);
v_it_x27_3148_ = v___x_3144_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_fst_3128_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3146_);
v_it_x27_3148_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; 
v___x_3149_ = lean_string_push(v_acc_3126_, v___x_3139_);
v_acc_3126_ = v___x_3149_;
v_a_3127_ = v_it_x27_3148_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3155_; 
v___x_3155_ = lean_box(0);
lean_inc(v_snd_3129_);
v_pos_3131_ = v_a_3127_;
v_snd_3132_ = v_snd_3129_;
v_err_3133_ = v___x_3155_;
goto v___jp_3130_;
}
v___jp_3130_:
{
uint8_t v_decide_3134_; 
v_decide_3134_ = lean_nat_dec_eq(v_snd_3129_, v_snd_3132_);
lean_dec(v_snd_3132_);
lean_dec(v_snd_3129_);
if (v_decide_3134_ == 0)
{
lean_object* v___x_3135_; 
lean_dec_ref(v_acc_3126_);
lean_inc(v_err_3133_);
v___x_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_pos_3131_);
lean_ctor_set(v___x_3135_, 1, v_err_3133_);
return v___x_3135_;
}
else
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v_pos_3131_);
lean_ctor_set(v___x_3136_, 1, v_acc_3126_);
return v___x_3136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(lean_object* v_acc_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_fst_3161_; lean_object* v_snd_3162_; lean_object* v_pos_3164_; lean_object* v_snd_3165_; lean_object* v_err_3166_; lean_object* v___x_3170_; uint8_t v_decide_3171_; 
v_fst_3161_ = lean_ctor_get(v_a_3160_, 0);
v_snd_3162_ = lean_ctor_get(v_a_3160_, 1);
lean_inc(v_snd_3162_);
v___x_3170_ = lean_string_utf8_byte_size(v_fst_3161_);
v_decide_3171_ = lean_nat_dec_eq(v_snd_3162_, v___x_3170_);
if (v_decide_3171_ == 0)
{
uint32_t v___x_3172_; uint32_t v_c_3173_; uint8_t v___x_3174_; 
v___x_3172_ = 71;
v_c_3173_ = lean_string_utf8_get_fast(v_fst_3161_, v_snd_3162_);
v___x_3174_ = lean_uint32_dec_eq(v_c_3173_, v___x_3172_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; 
v___x_3175_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1));
lean_inc(v_snd_3162_);
v_pos_3164_ = v_a_3160_;
v_snd_3165_ = v_snd_3162_;
v_err_3166_ = v___x_3175_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3185_; 
lean_inc(v_fst_3161_);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_a_3160_);
if (v_isSharedCheck_3185_ == 0)
{
lean_object* v_unused_3186_; lean_object* v_unused_3187_; 
v_unused_3186_ = lean_ctor_get(v_a_3160_, 1);
lean_dec(v_unused_3186_);
v_unused_3187_ = lean_ctor_get(v_a_3160_, 0);
lean_dec(v_unused_3187_);
v___x_3177_ = v_a_3160_;
v_isShared_3178_ = v_isSharedCheck_3185_;
goto v_resetjp_3176_;
}
else
{
lean_dec(v_a_3160_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3185_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v_it_x27_3181_; 
v___x_3179_ = lean_string_utf8_next_fast(v_fst_3161_, v_snd_3162_);
lean_dec(v_snd_3162_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 1, v___x_3179_);
v_it_x27_3181_ = v___x_3177_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_fst_3161_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_3179_);
v_it_x27_3181_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_string_push(v_acc_3159_, v___x_3172_);
v_acc_3159_ = v___x_3182_;
v_a_3160_ = v_it_x27_3181_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_box(0);
lean_inc(v_snd_3162_);
v_pos_3164_ = v_a_3160_;
v_snd_3165_ = v_snd_3162_;
v_err_3166_ = v___x_3188_;
goto v___jp_3163_;
}
v___jp_3163_:
{
uint8_t v_decide_3167_; 
v_decide_3167_ = lean_nat_dec_eq(v_snd_3162_, v_snd_3165_);
lean_dec(v_snd_3165_);
lean_dec(v_snd_3162_);
if (v_decide_3167_ == 0)
{
lean_object* v___x_3168_; 
lean_dec_ref(v_acc_3159_);
lean_inc(v_err_3166_);
v___x_3168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3168_, 0, v_pos_3164_);
lean_ctor_set(v___x_3168_, 1, v_err_3166_);
return v___x_3168_;
}
else
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v_pos_3164_);
lean_ctor_set(v___x_3169_, 1, v_acc_3159_);
return v___x_3169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(lean_object* v_acc_3192_, lean_object* v_a_3193_){
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
v___x_3205_ = 86;
v_c_3206_ = lean_string_utf8_get_fast(v_fst_3194_, v_snd_3195_);
v___x_3207_ = lean_uint32_dec_eq(v_c_3206_, v___x_3205_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; 
v___x_3208_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1));
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(lean_object* v_acc_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_fst_3227_; lean_object* v_snd_3228_; lean_object* v_pos_3230_; lean_object* v_snd_3231_; lean_object* v_err_3232_; lean_object* v___x_3236_; uint8_t v_decide_3237_; 
v_fst_3227_ = lean_ctor_get(v_a_3226_, 0);
v_snd_3228_ = lean_ctor_get(v_a_3226_, 1);
lean_inc(v_snd_3228_);
v___x_3236_ = lean_string_utf8_byte_size(v_fst_3227_);
v_decide_3237_ = lean_nat_dec_eq(v_snd_3228_, v___x_3236_);
if (v_decide_3237_ == 0)
{
uint32_t v___x_3238_; uint32_t v_c_3239_; uint8_t v___x_3240_; 
v___x_3238_ = 83;
v_c_3239_ = lean_string_utf8_get_fast(v_fst_3227_, v_snd_3228_);
v___x_3240_ = lean_uint32_dec_eq(v_c_3239_, v___x_3238_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; 
v___x_3241_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1));
lean_inc(v_snd_3228_);
v_pos_3230_ = v_a_3226_;
v_snd_3231_ = v_snd_3228_;
v_err_3232_ = v___x_3241_;
goto v___jp_3229_;
}
else
{
lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3251_; 
lean_inc(v_fst_3227_);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_a_3226_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; lean_object* v_unused_3253_; 
v_unused_3252_ = lean_ctor_get(v_a_3226_, 1);
lean_dec(v_unused_3252_);
v_unused_3253_ = lean_ctor_get(v_a_3226_, 0);
lean_dec(v_unused_3253_);
v___x_3243_ = v_a_3226_;
v_isShared_3244_ = v_isSharedCheck_3251_;
goto v_resetjp_3242_;
}
else
{
lean_dec(v_a_3226_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3251_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; lean_object* v_it_x27_3247_; 
v___x_3245_ = lean_string_utf8_next_fast(v_fst_3227_, v_snd_3228_);
lean_dec(v_snd_3228_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 1, v___x_3245_);
v_it_x27_3247_ = v___x_3243_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_fst_3227_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___x_3245_);
v_it_x27_3247_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_string_push(v_acc_3225_, v___x_3238_);
v_acc_3225_ = v___x_3248_;
v_a_3226_ = v_it_x27_3247_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_box(0);
lean_inc(v_snd_3228_);
v_pos_3230_ = v_a_3226_;
v_snd_3231_ = v_snd_3228_;
v_err_3232_ = v___x_3254_;
goto v___jp_3229_;
}
v___jp_3229_:
{
uint8_t v_decide_3233_; 
v_decide_3233_ = lean_nat_dec_eq(v_snd_3228_, v_snd_3231_);
lean_dec(v_snd_3231_);
lean_dec(v_snd_3228_);
if (v_decide_3233_ == 0)
{
lean_object* v___x_3234_; 
lean_dec_ref(v_acc_3225_);
lean_inc(v_err_3232_);
v___x_3234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3234_, 0, v_pos_3230_);
lean_ctor_set(v___x_3234_, 1, v_err_3232_);
return v___x_3234_;
}
else
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3235_, 0, v_pos_3230_);
lean_ctor_set(v___x_3235_, 1, v_acc_3225_);
return v___x_3235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(lean_object* v_acc_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v_fst_3260_; lean_object* v_snd_3261_; lean_object* v_pos_3263_; lean_object* v_snd_3264_; lean_object* v_err_3265_; lean_object* v___x_3269_; uint8_t v_decide_3270_; 
v_fst_3260_ = lean_ctor_get(v_a_3259_, 0);
v_snd_3261_ = lean_ctor_get(v_a_3259_, 1);
lean_inc(v_snd_3261_);
v___x_3269_ = lean_string_utf8_byte_size(v_fst_3260_);
v_decide_3270_ = lean_nat_dec_eq(v_snd_3261_, v___x_3269_);
if (v_decide_3270_ == 0)
{
uint32_t v___x_3271_; uint32_t v_c_3272_; uint8_t v___x_3273_; 
v___x_3271_ = 104;
v_c_3272_ = lean_string_utf8_get_fast(v_fst_3260_, v_snd_3261_);
v___x_3273_ = lean_uint32_dec_eq(v_c_3272_, v___x_3271_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1));
lean_inc(v_snd_3261_);
v_pos_3263_ = v_a_3259_;
v_snd_3264_ = v_snd_3261_;
v_err_3265_ = v___x_3274_;
goto v___jp_3262_;
}
else
{
lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3284_; 
lean_inc(v_fst_3260_);
v_isSharedCheck_3284_ = !lean_is_exclusive(v_a_3259_);
if (v_isSharedCheck_3284_ == 0)
{
lean_object* v_unused_3285_; lean_object* v_unused_3286_; 
v_unused_3285_ = lean_ctor_get(v_a_3259_, 1);
lean_dec(v_unused_3285_);
v_unused_3286_ = lean_ctor_get(v_a_3259_, 0);
lean_dec(v_unused_3286_);
v___x_3276_ = v_a_3259_;
v_isShared_3277_ = v_isSharedCheck_3284_;
goto v_resetjp_3275_;
}
else
{
lean_dec(v_a_3259_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3284_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3278_; lean_object* v_it_x27_3280_; 
v___x_3278_ = lean_string_utf8_next_fast(v_fst_3260_, v_snd_3261_);
lean_dec(v_snd_3261_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 1, v___x_3278_);
v_it_x27_3280_ = v___x_3276_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_fst_3260_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v___x_3278_);
v_it_x27_3280_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_string_push(v_acc_3258_, v___x_3271_);
v_acc_3258_ = v___x_3281_;
v_a_3259_ = v_it_x27_3280_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3287_; 
v___x_3287_ = lean_box(0);
lean_inc(v_snd_3261_);
v_pos_3263_ = v_a_3259_;
v_snd_3264_ = v_snd_3261_;
v_err_3265_ = v___x_3287_;
goto v___jp_3262_;
}
v___jp_3262_:
{
uint8_t v_decide_3266_; 
v_decide_3266_ = lean_nat_dec_eq(v_snd_3261_, v_snd_3264_);
lean_dec(v_snd_3264_);
lean_dec(v_snd_3261_);
if (v_decide_3266_ == 0)
{
lean_object* v___x_3267_; 
lean_dec_ref(v_acc_3258_);
lean_inc(v_err_3265_);
v___x_3267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3267_, 0, v_pos_3263_);
lean_ctor_set(v___x_3267_, 1, v_err_3265_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v_pos_3263_);
lean_ctor_set(v___x_3268_, 1, v_acc_3258_);
return v___x_3268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(lean_object* v_acc_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v_fst_3293_; lean_object* v_snd_3294_; lean_object* v_pos_3296_; lean_object* v_snd_3297_; lean_object* v_err_3298_; lean_object* v___x_3302_; uint8_t v_decide_3303_; 
v_fst_3293_ = lean_ctor_get(v_a_3292_, 0);
v_snd_3294_ = lean_ctor_get(v_a_3292_, 1);
lean_inc(v_snd_3294_);
v___x_3302_ = lean_string_utf8_byte_size(v_fst_3293_);
v_decide_3303_ = lean_nat_dec_eq(v_snd_3294_, v___x_3302_);
if (v_decide_3303_ == 0)
{
uint32_t v___x_3304_; uint32_t v_c_3305_; uint8_t v___x_3306_; 
v___x_3304_ = 81;
v_c_3305_ = lean_string_utf8_get_fast(v_fst_3293_, v_snd_3294_);
v___x_3306_ = lean_uint32_dec_eq(v_c_3305_, v___x_3304_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; 
v___x_3307_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1));
lean_inc(v_snd_3294_);
v_pos_3296_ = v_a_3292_;
v_snd_3297_ = v_snd_3294_;
v_err_3298_ = v___x_3307_;
goto v___jp_3295_;
}
else
{
lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3317_; 
lean_inc(v_fst_3293_);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_a_3292_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; lean_object* v_unused_3319_; 
v_unused_3318_ = lean_ctor_get(v_a_3292_, 1);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_a_3292_, 0);
lean_dec(v_unused_3319_);
v___x_3309_ = v_a_3292_;
v_isShared_3310_ = v_isSharedCheck_3317_;
goto v_resetjp_3308_;
}
else
{
lean_dec(v_a_3292_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3317_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v_it_x27_3313_; 
v___x_3311_ = lean_string_utf8_next_fast(v_fst_3293_, v_snd_3294_);
lean_dec(v_snd_3294_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 1, v___x_3311_);
v_it_x27_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_fst_3293_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3311_);
v_it_x27_3313_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3314_; 
v___x_3314_ = lean_string_push(v_acc_3291_, v___x_3304_);
v_acc_3291_ = v___x_3314_;
v_a_3292_ = v_it_x27_3313_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_box(0);
lean_inc(v_snd_3294_);
v_pos_3296_ = v_a_3292_;
v_snd_3297_ = v_snd_3294_;
v_err_3298_ = v___x_3320_;
goto v___jp_3295_;
}
v___jp_3295_:
{
uint8_t v_decide_3299_; 
v_decide_3299_ = lean_nat_dec_eq(v_snd_3294_, v_snd_3297_);
lean_dec(v_snd_3297_);
lean_dec(v_snd_3294_);
if (v_decide_3299_ == 0)
{
lean_object* v___x_3300_; 
lean_dec_ref(v_acc_3291_);
lean_inc(v_err_3298_);
v___x_3300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_pos_3296_);
lean_ctor_set(v___x_3300_, 1, v_err_3298_);
return v___x_3300_;
}
else
{
lean_object* v___x_3301_; 
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v_pos_3296_);
lean_ctor_set(v___x_3301_, 1, v_acc_3291_);
return v___x_3301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(lean_object* v_acc_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_fst_3326_; lean_object* v_snd_3327_; lean_object* v_pos_3329_; lean_object* v_snd_3330_; lean_object* v_err_3331_; lean_object* v___x_3335_; uint8_t v_decide_3336_; 
v_fst_3326_ = lean_ctor_get(v_a_3325_, 0);
v_snd_3327_ = lean_ctor_get(v_a_3325_, 1);
lean_inc(v_snd_3327_);
v___x_3335_ = lean_string_utf8_byte_size(v_fst_3326_);
v_decide_3336_ = lean_nat_dec_eq(v_snd_3327_, v___x_3335_);
if (v_decide_3336_ == 0)
{
uint32_t v___x_3337_; uint32_t v_c_3338_; uint8_t v___x_3339_; 
v___x_3337_ = 68;
v_c_3338_ = lean_string_utf8_get_fast(v_fst_3326_, v_snd_3327_);
v___x_3339_ = lean_uint32_dec_eq(v_c_3338_, v___x_3337_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; 
v___x_3340_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1));
lean_inc(v_snd_3327_);
v_pos_3329_ = v_a_3325_;
v_snd_3330_ = v_snd_3327_;
v_err_3331_ = v___x_3340_;
goto v___jp_3328_;
}
else
{
lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3350_; 
lean_inc(v_fst_3326_);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_a_3325_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; lean_object* v_unused_3352_; 
v_unused_3351_ = lean_ctor_get(v_a_3325_, 1);
lean_dec(v_unused_3351_);
v_unused_3352_ = lean_ctor_get(v_a_3325_, 0);
lean_dec(v_unused_3352_);
v___x_3342_ = v_a_3325_;
v_isShared_3343_ = v_isSharedCheck_3350_;
goto v_resetjp_3341_;
}
else
{
lean_dec(v_a_3325_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3350_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3344_; lean_object* v_it_x27_3346_; 
v___x_3344_ = lean_string_utf8_next_fast(v_fst_3326_, v_snd_3327_);
lean_dec(v_snd_3327_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 1, v___x_3344_);
v_it_x27_3346_ = v___x_3342_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_fst_3326_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v___x_3344_);
v_it_x27_3346_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3347_; 
v___x_3347_ = lean_string_push(v_acc_3324_, v___x_3337_);
v_acc_3324_ = v___x_3347_;
v_a_3325_ = v_it_x27_3346_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3353_; 
v___x_3353_ = lean_box(0);
lean_inc(v_snd_3327_);
v_pos_3329_ = v_a_3325_;
v_snd_3330_ = v_snd_3327_;
v_err_3331_ = v___x_3353_;
goto v___jp_3328_;
}
v___jp_3328_:
{
uint8_t v_decide_3332_; 
v_decide_3332_ = lean_nat_dec_eq(v_snd_3327_, v_snd_3330_);
lean_dec(v_snd_3330_);
lean_dec(v_snd_3327_);
if (v_decide_3332_ == 0)
{
lean_object* v___x_3333_; 
lean_dec_ref(v_acc_3324_);
lean_inc(v_err_3331_);
v___x_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3333_, 0, v_pos_3329_);
lean_ctor_set(v___x_3333_, 1, v_err_3331_);
return v___x_3333_;
}
else
{
lean_object* v___x_3334_; 
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v_pos_3329_);
lean_ctor_set(v___x_3334_, 1, v_acc_3324_);
return v___x_3334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(lean_object* v_acc_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v_fst_3359_; lean_object* v_snd_3360_; lean_object* v_pos_3362_; lean_object* v_snd_3363_; lean_object* v_err_3364_; lean_object* v___x_3368_; uint8_t v_decide_3369_; 
v_fst_3359_ = lean_ctor_get(v_a_3358_, 0);
v_snd_3360_ = lean_ctor_get(v_a_3358_, 1);
lean_inc(v_snd_3360_);
v___x_3368_ = lean_string_utf8_byte_size(v_fst_3359_);
v_decide_3369_ = lean_nat_dec_eq(v_snd_3360_, v___x_3368_);
if (v_decide_3369_ == 0)
{
uint32_t v___x_3370_; uint32_t v_c_3371_; uint8_t v___x_3372_; 
v___x_3370_ = 88;
v_c_3371_ = lean_string_utf8_get_fast(v_fst_3359_, v_snd_3360_);
v___x_3372_ = lean_uint32_dec_eq(v_c_3371_, v___x_3370_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; 
v___x_3373_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1));
lean_inc(v_snd_3360_);
v_pos_3362_ = v_a_3358_;
v_snd_3363_ = v_snd_3360_;
v_err_3364_ = v___x_3373_;
goto v___jp_3361_;
}
else
{
lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3383_; 
lean_inc(v_fst_3359_);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_a_3358_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; lean_object* v_unused_3385_; 
v_unused_3384_ = lean_ctor_get(v_a_3358_, 1);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_a_3358_, 0);
lean_dec(v_unused_3385_);
v___x_3375_ = v_a_3358_;
v_isShared_3376_ = v_isSharedCheck_3383_;
goto v_resetjp_3374_;
}
else
{
lean_dec(v_a_3358_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3383_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v_it_x27_3379_; 
v___x_3377_ = lean_string_utf8_next_fast(v_fst_3359_, v_snd_3360_);
lean_dec(v_snd_3360_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 1, v___x_3377_);
v_it_x27_3379_ = v___x_3375_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_fst_3359_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___x_3377_);
v_it_x27_3379_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_string_push(v_acc_3357_, v___x_3370_);
v_acc_3357_ = v___x_3380_;
v_a_3358_ = v_it_x27_3379_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_box(0);
lean_inc(v_snd_3360_);
v_pos_3362_ = v_a_3358_;
v_snd_3363_ = v_snd_3360_;
v_err_3364_ = v___x_3386_;
goto v___jp_3361_;
}
v___jp_3361_:
{
uint8_t v_decide_3365_; 
v_decide_3365_ = lean_nat_dec_eq(v_snd_3360_, v_snd_3363_);
lean_dec(v_snd_3363_);
lean_dec(v_snd_3360_);
if (v_decide_3365_ == 0)
{
lean_object* v___x_3366_; 
lean_dec_ref(v_acc_3357_);
lean_inc(v_err_3364_);
v___x_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_pos_3362_);
lean_ctor_set(v___x_3366_, 1, v_err_3364_);
return v___x_3366_;
}
else
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3367_, 0, v_pos_3362_);
lean_ctor_set(v___x_3367_, 1, v_acc_3357_);
return v___x_3367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(lean_object* v_acc_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_fst_3392_; lean_object* v_snd_3393_; lean_object* v_pos_3395_; lean_object* v_snd_3396_; lean_object* v_err_3397_; lean_object* v___x_3401_; uint8_t v_decide_3402_; 
v_fst_3392_ = lean_ctor_get(v_a_3391_, 0);
v_snd_3393_ = lean_ctor_get(v_a_3391_, 1);
lean_inc(v_snd_3393_);
v___x_3401_ = lean_string_utf8_byte_size(v_fst_3392_);
v_decide_3402_ = lean_nat_dec_eq(v_snd_3393_, v___x_3401_);
if (v_decide_3402_ == 0)
{
uint32_t v___x_3403_; uint32_t v_c_3404_; uint8_t v___x_3405_; 
v___x_3403_ = 122;
v_c_3404_ = lean_string_utf8_get_fast(v_fst_3392_, v_snd_3393_);
v___x_3405_ = lean_uint32_dec_eq(v_c_3404_, v___x_3403_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; 
v___x_3406_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1));
lean_inc(v_snd_3393_);
v_pos_3395_ = v_a_3391_;
v_snd_3396_ = v_snd_3393_;
v_err_3397_ = v___x_3406_;
goto v___jp_3394_;
}
else
{
lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3416_; 
lean_inc(v_fst_3392_);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_a_3391_);
if (v_isSharedCheck_3416_ == 0)
{
lean_object* v_unused_3417_; lean_object* v_unused_3418_; 
v_unused_3417_ = lean_ctor_get(v_a_3391_, 1);
lean_dec(v_unused_3417_);
v_unused_3418_ = lean_ctor_get(v_a_3391_, 0);
lean_dec(v_unused_3418_);
v___x_3408_ = v_a_3391_;
v_isShared_3409_ = v_isSharedCheck_3416_;
goto v_resetjp_3407_;
}
else
{
lean_dec(v_a_3391_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3416_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; lean_object* v_it_x27_3412_; 
v___x_3410_ = lean_string_utf8_next_fast(v_fst_3392_, v_snd_3393_);
lean_dec(v_snd_3393_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 1, v___x_3410_);
v_it_x27_3412_ = v___x_3408_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_fst_3392_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v___x_3410_);
v_it_x27_3412_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_string_push(v_acc_3390_, v___x_3403_);
v_acc_3390_ = v___x_3413_;
v_a_3391_ = v_it_x27_3412_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3419_; 
v___x_3419_ = lean_box(0);
lean_inc(v_snd_3393_);
v_pos_3395_ = v_a_3391_;
v_snd_3396_ = v_snd_3393_;
v_err_3397_ = v___x_3419_;
goto v___jp_3394_;
}
v___jp_3394_:
{
uint8_t v_decide_3398_; 
v_decide_3398_ = lean_nat_dec_eq(v_snd_3393_, v_snd_3396_);
lean_dec(v_snd_3396_);
lean_dec(v_snd_3393_);
if (v_decide_3398_ == 0)
{
lean_object* v___x_3399_; 
lean_dec_ref(v_acc_3390_);
lean_inc(v_err_3397_);
v___x_3399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3399_, 0, v_pos_3395_);
lean_ctor_set(v___x_3399_, 1, v_err_3397_);
return v___x_3399_;
}
else
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v_pos_3395_);
lean_ctor_set(v___x_3400_, 1, v_acc_3390_);
return v___x_3400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(lean_object* v_acc_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v_fst_3425_; lean_object* v_snd_3426_; lean_object* v_pos_3428_; lean_object* v_snd_3429_; lean_object* v_err_3430_; lean_object* v___x_3434_; uint8_t v_decide_3435_; 
v_fst_3425_ = lean_ctor_get(v_a_3424_, 0);
v_snd_3426_ = lean_ctor_get(v_a_3424_, 1);
lean_inc(v_snd_3426_);
v___x_3434_ = lean_string_utf8_byte_size(v_fst_3425_);
v_decide_3435_ = lean_nat_dec_eq(v_snd_3426_, v___x_3434_);
if (v_decide_3435_ == 0)
{
uint32_t v___x_3436_; uint32_t v_c_3437_; uint8_t v___x_3438_; 
v___x_3436_ = 115;
v_c_3437_ = lean_string_utf8_get_fast(v_fst_3425_, v_snd_3426_);
v___x_3438_ = lean_uint32_dec_eq(v_c_3437_, v___x_3436_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1));
lean_inc(v_snd_3426_);
v_pos_3428_ = v_a_3424_;
v_snd_3429_ = v_snd_3426_;
v_err_3430_ = v___x_3439_;
goto v___jp_3427_;
}
else
{
lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3449_; 
lean_inc(v_fst_3425_);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_a_3424_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; lean_object* v_unused_3451_; 
v_unused_3450_ = lean_ctor_get(v_a_3424_, 1);
lean_dec(v_unused_3450_);
v_unused_3451_ = lean_ctor_get(v_a_3424_, 0);
lean_dec(v_unused_3451_);
v___x_3441_ = v_a_3424_;
v_isShared_3442_ = v_isSharedCheck_3449_;
goto v_resetjp_3440_;
}
else
{
lean_dec(v_a_3424_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3449_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v_it_x27_3445_; 
v___x_3443_ = lean_string_utf8_next_fast(v_fst_3425_, v_snd_3426_);
lean_dec(v_snd_3426_);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 1, v___x_3443_);
v_it_x27_3445_ = v___x_3441_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_fst_3425_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v___x_3443_);
v_it_x27_3445_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_string_push(v_acc_3423_, v___x_3436_);
v_acc_3423_ = v___x_3446_;
v_a_3424_ = v_it_x27_3445_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_box(0);
lean_inc(v_snd_3426_);
v_pos_3428_ = v_a_3424_;
v_snd_3429_ = v_snd_3426_;
v_err_3430_ = v___x_3452_;
goto v___jp_3427_;
}
v___jp_3427_:
{
uint8_t v_decide_3431_; 
v_decide_3431_ = lean_nat_dec_eq(v_snd_3426_, v_snd_3429_);
lean_dec(v_snd_3429_);
lean_dec(v_snd_3426_);
if (v_decide_3431_ == 0)
{
lean_object* v___x_3432_; 
lean_dec_ref(v_acc_3423_);
lean_inc(v_err_3430_);
v___x_3432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3432_, 0, v_pos_3428_);
lean_ctor_set(v___x_3432_, 1, v_err_3430_);
return v___x_3432_;
}
else
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3433_, 0, v_pos_3428_);
lean_ctor_set(v___x_3433_, 1, v_acc_3423_);
return v___x_3433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(lean_object* v_acc_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_fst_3458_; lean_object* v_snd_3459_; lean_object* v_pos_3461_; lean_object* v_snd_3462_; lean_object* v_err_3463_; lean_object* v___x_3467_; uint8_t v_decide_3468_; 
v_fst_3458_ = lean_ctor_get(v_a_3457_, 0);
v_snd_3459_ = lean_ctor_get(v_a_3457_, 1);
lean_inc(v_snd_3459_);
v___x_3467_ = lean_string_utf8_byte_size(v_fst_3458_);
v_decide_3468_ = lean_nat_dec_eq(v_snd_3459_, v___x_3467_);
if (v_decide_3468_ == 0)
{
uint32_t v___x_3469_; uint32_t v_c_3470_; uint8_t v___x_3471_; 
v___x_3469_ = 75;
v_c_3470_ = lean_string_utf8_get_fast(v_fst_3458_, v_snd_3459_);
v___x_3471_ = lean_uint32_dec_eq(v_c_3470_, v___x_3469_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; 
v___x_3472_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1));
lean_inc(v_snd_3459_);
v_pos_3461_ = v_a_3457_;
v_snd_3462_ = v_snd_3459_;
v_err_3463_ = v___x_3472_;
goto v___jp_3460_;
}
else
{
lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3482_; 
lean_inc(v_fst_3458_);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_a_3457_);
if (v_isSharedCheck_3482_ == 0)
{
lean_object* v_unused_3483_; lean_object* v_unused_3484_; 
v_unused_3483_ = lean_ctor_get(v_a_3457_, 1);
lean_dec(v_unused_3483_);
v_unused_3484_ = lean_ctor_get(v_a_3457_, 0);
lean_dec(v_unused_3484_);
v___x_3474_ = v_a_3457_;
v_isShared_3475_ = v_isSharedCheck_3482_;
goto v_resetjp_3473_;
}
else
{
lean_dec(v_a_3457_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3482_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v_it_x27_3478_; 
v___x_3476_ = lean_string_utf8_next_fast(v_fst_3458_, v_snd_3459_);
lean_dec(v_snd_3459_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 1, v___x_3476_);
v_it_x27_3478_ = v___x_3474_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_fst_3458_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v___x_3476_);
v_it_x27_3478_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_string_push(v_acc_3456_, v___x_3469_);
v_acc_3456_ = v___x_3479_;
v_a_3457_ = v_it_x27_3478_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_box(0);
lean_inc(v_snd_3459_);
v_pos_3461_ = v_a_3457_;
v_snd_3462_ = v_snd_3459_;
v_err_3463_ = v___x_3485_;
goto v___jp_3460_;
}
v___jp_3460_:
{
uint8_t v_decide_3464_; 
v_decide_3464_ = lean_nat_dec_eq(v_snd_3459_, v_snd_3462_);
lean_dec(v_snd_3462_);
lean_dec(v_snd_3459_);
if (v_decide_3464_ == 0)
{
lean_object* v___x_3465_; 
lean_dec_ref(v_acc_3456_);
lean_inc(v_err_3463_);
v___x_3465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3465_, 0, v_pos_3461_);
lean_ctor_set(v___x_3465_, 1, v_err_3463_);
return v___x_3465_;
}
else
{
lean_object* v___x_3466_; 
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v_pos_3461_);
lean_ctor_set(v___x_3466_, 1, v_acc_3456_);
return v___x_3466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(lean_object* v_acc_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v_fst_3491_; lean_object* v_snd_3492_; lean_object* v_pos_3494_; lean_object* v_snd_3495_; lean_object* v_err_3496_; lean_object* v___x_3500_; uint8_t v_decide_3501_; 
v_fst_3491_ = lean_ctor_get(v_a_3490_, 0);
v_snd_3492_ = lean_ctor_get(v_a_3490_, 1);
lean_inc(v_snd_3492_);
v___x_3500_ = lean_string_utf8_byte_size(v_fst_3491_);
v_decide_3501_ = lean_nat_dec_eq(v_snd_3492_, v___x_3500_);
if (v_decide_3501_ == 0)
{
uint32_t v___x_3502_; uint32_t v_c_3503_; uint8_t v___x_3504_; 
v___x_3502_ = 101;
v_c_3503_ = lean_string_utf8_get_fast(v_fst_3491_, v_snd_3492_);
v___x_3504_ = lean_uint32_dec_eq(v_c_3503_, v___x_3502_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
v___x_3505_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1));
lean_inc(v_snd_3492_);
v_pos_3494_ = v_a_3490_;
v_snd_3495_ = v_snd_3492_;
v_err_3496_ = v___x_3505_;
goto v___jp_3493_;
}
else
{
lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3515_; 
lean_inc(v_fst_3491_);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_a_3490_);
if (v_isSharedCheck_3515_ == 0)
{
lean_object* v_unused_3516_; lean_object* v_unused_3517_; 
v_unused_3516_ = lean_ctor_get(v_a_3490_, 1);
lean_dec(v_unused_3516_);
v_unused_3517_ = lean_ctor_get(v_a_3490_, 0);
lean_dec(v_unused_3517_);
v___x_3507_ = v_a_3490_;
v_isShared_3508_ = v_isSharedCheck_3515_;
goto v_resetjp_3506_;
}
else
{
lean_dec(v_a_3490_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3515_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; lean_object* v_it_x27_3511_; 
v___x_3509_ = lean_string_utf8_next_fast(v_fst_3491_, v_snd_3492_);
lean_dec(v_snd_3492_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3509_);
v_it_x27_3511_ = v___x_3507_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_fst_3491_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v___x_3509_);
v_it_x27_3511_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3512_; 
v___x_3512_ = lean_string_push(v_acc_3489_, v___x_3502_);
v_acc_3489_ = v___x_3512_;
v_a_3490_ = v_it_x27_3511_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3518_; 
v___x_3518_ = lean_box(0);
lean_inc(v_snd_3492_);
v_pos_3494_ = v_a_3490_;
v_snd_3495_ = v_snd_3492_;
v_err_3496_ = v___x_3518_;
goto v___jp_3493_;
}
v___jp_3493_:
{
uint8_t v_decide_3497_; 
v_decide_3497_ = lean_nat_dec_eq(v_snd_3492_, v_snd_3495_);
lean_dec(v_snd_3495_);
lean_dec(v_snd_3492_);
if (v_decide_3497_ == 0)
{
lean_object* v___x_3498_; 
lean_dec_ref(v_acc_3489_);
lean_inc(v_err_3496_);
v___x_3498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3498_, 0, v_pos_3494_);
lean_ctor_set(v___x_3498_, 1, v_err_3496_);
return v___x_3498_;
}
else
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3499_, 0, v_pos_3494_);
lean_ctor_set(v___x_3499_, 1, v_acc_3489_);
return v___x_3499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(lean_object* v_acc_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_fst_3524_; lean_object* v_snd_3525_; lean_object* v_pos_3527_; lean_object* v_snd_3528_; lean_object* v_err_3529_; lean_object* v___x_3533_; uint8_t v_decide_3534_; 
v_fst_3524_ = lean_ctor_get(v_a_3523_, 0);
v_snd_3525_ = lean_ctor_get(v_a_3523_, 1);
lean_inc(v_snd_3525_);
v___x_3533_ = lean_string_utf8_byte_size(v_fst_3524_);
v_decide_3534_ = lean_nat_dec_eq(v_snd_3525_, v___x_3533_);
if (v_decide_3534_ == 0)
{
uint32_t v___x_3535_; uint32_t v_c_3536_; uint8_t v___x_3537_; 
v___x_3535_ = 77;
v_c_3536_ = lean_string_utf8_get_fast(v_fst_3524_, v_snd_3525_);
v___x_3537_ = lean_uint32_dec_eq(v_c_3536_, v___x_3535_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; 
v___x_3538_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1));
lean_inc(v_snd_3525_);
v_pos_3527_ = v_a_3523_;
v_snd_3528_ = v_snd_3525_;
v_err_3529_ = v___x_3538_;
goto v___jp_3526_;
}
else
{
lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3548_; 
lean_inc(v_fst_3524_);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_a_3523_);
if (v_isSharedCheck_3548_ == 0)
{
lean_object* v_unused_3549_; lean_object* v_unused_3550_; 
v_unused_3549_ = lean_ctor_get(v_a_3523_, 1);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_a_3523_, 0);
lean_dec(v_unused_3550_);
v___x_3540_ = v_a_3523_;
v_isShared_3541_ = v_isSharedCheck_3548_;
goto v_resetjp_3539_;
}
else
{
lean_dec(v_a_3523_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3548_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3542_; lean_object* v_it_x27_3544_; 
v___x_3542_ = lean_string_utf8_next_fast(v_fst_3524_, v_snd_3525_);
lean_dec(v_snd_3525_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 1, v___x_3542_);
v_it_x27_3544_ = v___x_3540_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_fst_3524_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v___x_3542_);
v_it_x27_3544_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_string_push(v_acc_3522_, v___x_3535_);
v_acc_3522_ = v___x_3545_;
v_a_3523_ = v_it_x27_3544_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_box(0);
lean_inc(v_snd_3525_);
v_pos_3527_ = v_a_3523_;
v_snd_3528_ = v_snd_3525_;
v_err_3529_ = v___x_3551_;
goto v___jp_3526_;
}
v___jp_3526_:
{
uint8_t v_decide_3530_; 
v_decide_3530_ = lean_nat_dec_eq(v_snd_3525_, v_snd_3528_);
lean_dec(v_snd_3528_);
lean_dec(v_snd_3525_);
if (v_decide_3530_ == 0)
{
lean_object* v___x_3531_; 
lean_dec_ref(v_acc_3522_);
lean_inc(v_err_3529_);
v___x_3531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3531_, 0, v_pos_3527_);
lean_ctor_set(v___x_3531_, 1, v_err_3529_);
return v___x_3531_;
}
else
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3532_, 0, v_pos_3527_);
lean_ctor_set(v___x_3532_, 1, v_acc_3522_);
return v___x_3532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(lean_object* v_acc_3555_, lean_object* v_a_3556_){
_start:
{
lean_object* v_fst_3557_; lean_object* v_snd_3558_; lean_object* v_pos_3560_; lean_object* v_snd_3561_; lean_object* v_err_3562_; lean_object* v___x_3566_; uint8_t v_decide_3567_; 
v_fst_3557_ = lean_ctor_get(v_a_3556_, 0);
v_snd_3558_ = lean_ctor_get(v_a_3556_, 1);
lean_inc(v_snd_3558_);
v___x_3566_ = lean_string_utf8_byte_size(v_fst_3557_);
v_decide_3567_ = lean_nat_dec_eq(v_snd_3558_, v___x_3566_);
if (v_decide_3567_ == 0)
{
uint32_t v___x_3568_; uint32_t v_c_3569_; uint8_t v___x_3570_; 
v___x_3568_ = 119;
v_c_3569_ = lean_string_utf8_get_fast(v_fst_3557_, v_snd_3558_);
v___x_3570_ = lean_uint32_dec_eq(v_c_3569_, v___x_3568_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
v___x_3571_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1));
lean_inc(v_snd_3558_);
v_pos_3560_ = v_a_3556_;
v_snd_3561_ = v_snd_3558_;
v_err_3562_ = v___x_3571_;
goto v___jp_3559_;
}
else
{
lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3581_; 
lean_inc(v_fst_3557_);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_a_3556_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; lean_object* v_unused_3583_; 
v_unused_3582_ = lean_ctor_get(v_a_3556_, 1);
lean_dec(v_unused_3582_);
v_unused_3583_ = lean_ctor_get(v_a_3556_, 0);
lean_dec(v_unused_3583_);
v___x_3573_ = v_a_3556_;
v_isShared_3574_ = v_isSharedCheck_3581_;
goto v_resetjp_3572_;
}
else
{
lean_dec(v_a_3556_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3581_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v_it_x27_3577_; 
v___x_3575_ = lean_string_utf8_next_fast(v_fst_3557_, v_snd_3558_);
lean_dec(v_snd_3558_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___x_3575_);
v_it_x27_3577_ = v___x_3573_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_fst_3557_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v___x_3575_);
v_it_x27_3577_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3578_; 
v___x_3578_ = lean_string_push(v_acc_3555_, v___x_3568_);
v_acc_3555_ = v___x_3578_;
v_a_3556_ = v_it_x27_3577_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3584_; 
v___x_3584_ = lean_box(0);
lean_inc(v_snd_3558_);
v_pos_3560_ = v_a_3556_;
v_snd_3561_ = v_snd_3558_;
v_err_3562_ = v___x_3584_;
goto v___jp_3559_;
}
v___jp_3559_:
{
uint8_t v_decide_3563_; 
v_decide_3563_ = lean_nat_dec_eq(v_snd_3558_, v_snd_3561_);
lean_dec(v_snd_3561_);
lean_dec(v_snd_3558_);
if (v_decide_3563_ == 0)
{
lean_object* v___x_3564_; 
lean_dec_ref(v_acc_3555_);
lean_inc(v_err_3562_);
v___x_3564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3564_, 0, v_pos_3560_);
lean_ctor_set(v___x_3564_, 1, v_err_3562_);
return v___x_3564_;
}
else
{
lean_object* v___x_3565_; 
v___x_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3565_, 0, v_pos_3560_);
lean_ctor_set(v___x_3565_, 1, v_acc_3555_);
return v___x_3565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(lean_object* v_acc_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v_fst_3590_; lean_object* v_snd_3591_; lean_object* v_pos_3593_; lean_object* v_snd_3594_; lean_object* v_err_3595_; lean_object* v___x_3599_; uint8_t v_decide_3600_; 
v_fst_3590_ = lean_ctor_get(v_a_3589_, 0);
v_snd_3591_ = lean_ctor_get(v_a_3589_, 1);
lean_inc(v_snd_3591_);
v___x_3599_ = lean_string_utf8_byte_size(v_fst_3590_);
v_decide_3600_ = lean_nat_dec_eq(v_snd_3591_, v___x_3599_);
if (v_decide_3600_ == 0)
{
uint32_t v___x_3601_; uint32_t v_c_3602_; uint8_t v___x_3603_; 
v___x_3601_ = 100;
v_c_3602_ = lean_string_utf8_get_fast(v_fst_3590_, v_snd_3591_);
v___x_3603_ = lean_uint32_dec_eq(v_c_3602_, v___x_3601_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; 
v___x_3604_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1));
lean_inc(v_snd_3591_);
v_pos_3593_ = v_a_3589_;
v_snd_3594_ = v_snd_3591_;
v_err_3595_ = v___x_3604_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3614_; 
lean_inc(v_fst_3590_);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_a_3589_);
if (v_isSharedCheck_3614_ == 0)
{
lean_object* v_unused_3615_; lean_object* v_unused_3616_; 
v_unused_3615_ = lean_ctor_get(v_a_3589_, 1);
lean_dec(v_unused_3615_);
v_unused_3616_ = lean_ctor_get(v_a_3589_, 0);
lean_dec(v_unused_3616_);
v___x_3606_ = v_a_3589_;
v_isShared_3607_ = v_isSharedCheck_3614_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v_a_3589_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3614_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v_it_x27_3610_; 
v___x_3608_ = lean_string_utf8_next_fast(v_fst_3590_, v_snd_3591_);
lean_dec(v_snd_3591_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 1, v___x_3608_);
v_it_x27_3610_ = v___x_3606_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_fst_3590_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v___x_3608_);
v_it_x27_3610_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_string_push(v_acc_3588_, v___x_3601_);
v_acc_3588_ = v___x_3611_;
v_a_3589_ = v_it_x27_3610_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3617_; 
v___x_3617_ = lean_box(0);
lean_inc(v_snd_3591_);
v_pos_3593_ = v_a_3589_;
v_snd_3594_ = v_snd_3591_;
v_err_3595_ = v___x_3617_;
goto v___jp_3592_;
}
v___jp_3592_:
{
uint8_t v_decide_3596_; 
v_decide_3596_ = lean_nat_dec_eq(v_snd_3591_, v_snd_3594_);
lean_dec(v_snd_3594_);
lean_dec(v_snd_3591_);
if (v_decide_3596_ == 0)
{
lean_object* v___x_3597_; 
lean_dec_ref(v_acc_3588_);
lean_inc(v_err_3595_);
v___x_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3597_, 0, v_pos_3593_);
lean_ctor_set(v___x_3597_, 1, v_err_3595_);
return v___x_3597_;
}
else
{
lean_object* v___x_3598_; 
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v_pos_3593_);
lean_ctor_set(v___x_3598_, 1, v_acc_3588_);
return v___x_3598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(lean_object* v_acc_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v_fst_3623_; lean_object* v_snd_3624_; lean_object* v_pos_3626_; lean_object* v_snd_3627_; lean_object* v_err_3628_; lean_object* v___x_3632_; uint8_t v_decide_3633_; 
v_fst_3623_ = lean_ctor_get(v_a_3622_, 0);
v_snd_3624_ = lean_ctor_get(v_a_3622_, 1);
lean_inc(v_snd_3624_);
v___x_3632_ = lean_string_utf8_byte_size(v_fst_3623_);
v_decide_3633_ = lean_nat_dec_eq(v_snd_3624_, v___x_3632_);
if (v_decide_3633_ == 0)
{
uint32_t v___x_3634_; uint32_t v_c_3635_; uint8_t v___x_3636_; 
v___x_3634_ = 99;
v_c_3635_ = lean_string_utf8_get_fast(v_fst_3623_, v_snd_3624_);
v___x_3636_ = lean_uint32_dec_eq(v_c_3635_, v___x_3634_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; 
v___x_3637_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1));
lean_inc(v_snd_3624_);
v_pos_3626_ = v_a_3622_;
v_snd_3627_ = v_snd_3624_;
v_err_3628_ = v___x_3637_;
goto v___jp_3625_;
}
else
{
lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3647_; 
lean_inc(v_fst_3623_);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_a_3622_);
if (v_isSharedCheck_3647_ == 0)
{
lean_object* v_unused_3648_; lean_object* v_unused_3649_; 
v_unused_3648_ = lean_ctor_get(v_a_3622_, 1);
lean_dec(v_unused_3648_);
v_unused_3649_ = lean_ctor_get(v_a_3622_, 0);
lean_dec(v_unused_3649_);
v___x_3639_ = v_a_3622_;
v_isShared_3640_ = v_isSharedCheck_3647_;
goto v_resetjp_3638_;
}
else
{
lean_dec(v_a_3622_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3647_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3641_; lean_object* v_it_x27_3643_; 
v___x_3641_ = lean_string_utf8_next_fast(v_fst_3623_, v_snd_3624_);
lean_dec(v_snd_3624_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 1, v___x_3641_);
v_it_x27_3643_ = v___x_3639_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_fst_3623_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v___x_3641_);
v_it_x27_3643_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3644_; 
v___x_3644_ = lean_string_push(v_acc_3621_, v___x_3634_);
v_acc_3621_ = v___x_3644_;
v_a_3622_ = v_it_x27_3643_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3650_; 
v___x_3650_ = lean_box(0);
lean_inc(v_snd_3624_);
v_pos_3626_ = v_a_3622_;
v_snd_3627_ = v_snd_3624_;
v_err_3628_ = v___x_3650_;
goto v___jp_3625_;
}
v___jp_3625_:
{
uint8_t v_decide_3629_; 
v_decide_3629_ = lean_nat_dec_eq(v_snd_3624_, v_snd_3627_);
lean_dec(v_snd_3627_);
lean_dec(v_snd_3624_);
if (v_decide_3629_ == 0)
{
lean_object* v___x_3630_; 
lean_dec_ref(v_acc_3621_);
lean_inc(v_err_3628_);
v___x_3630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3630_, 0, v_pos_3626_);
lean_ctor_set(v___x_3630_, 1, v_err_3628_);
return v___x_3630_;
}
else
{
lean_object* v___x_3631_; 
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v_pos_3626_);
lean_ctor_set(v___x_3631_, 1, v_acc_3621_);
return v___x_3631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(lean_object* v_acc_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v_fst_3656_; lean_object* v_snd_3657_; lean_object* v_pos_3659_; lean_object* v_snd_3660_; lean_object* v_err_3661_; lean_object* v___x_3665_; uint8_t v_decide_3666_; 
v_fst_3656_ = lean_ctor_get(v_a_3655_, 0);
v_snd_3657_ = lean_ctor_get(v_a_3655_, 1);
lean_inc(v_snd_3657_);
v___x_3665_ = lean_string_utf8_byte_size(v_fst_3656_);
v_decide_3666_ = lean_nat_dec_eq(v_snd_3657_, v___x_3665_);
if (v_decide_3666_ == 0)
{
uint32_t v___x_3667_; uint32_t v_c_3668_; uint8_t v___x_3669_; 
v___x_3667_ = 69;
v_c_3668_ = lean_string_utf8_get_fast(v_fst_3656_, v_snd_3657_);
v___x_3669_ = lean_uint32_dec_eq(v_c_3668_, v___x_3667_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; 
v___x_3670_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1));
lean_inc(v_snd_3657_);
v_pos_3659_ = v_a_3655_;
v_snd_3660_ = v_snd_3657_;
v_err_3661_ = v___x_3670_;
goto v___jp_3658_;
}
else
{
lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3680_; 
lean_inc(v_fst_3656_);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_a_3655_);
if (v_isSharedCheck_3680_ == 0)
{
lean_object* v_unused_3681_; lean_object* v_unused_3682_; 
v_unused_3681_ = lean_ctor_get(v_a_3655_, 1);
lean_dec(v_unused_3681_);
v_unused_3682_ = lean_ctor_get(v_a_3655_, 0);
lean_dec(v_unused_3682_);
v___x_3672_ = v_a_3655_;
v_isShared_3673_ = v_isSharedCheck_3680_;
goto v_resetjp_3671_;
}
else
{
lean_dec(v_a_3655_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3680_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; lean_object* v_it_x27_3676_; 
v___x_3674_ = lean_string_utf8_next_fast(v_fst_3656_, v_snd_3657_);
lean_dec(v_snd_3657_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 1, v___x_3674_);
v_it_x27_3676_ = v___x_3672_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_fst_3656_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___x_3674_);
v_it_x27_3676_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_string_push(v_acc_3654_, v___x_3667_);
v_acc_3654_ = v___x_3677_;
v_a_3655_ = v_it_x27_3676_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3683_; 
v___x_3683_ = lean_box(0);
lean_inc(v_snd_3657_);
v_pos_3659_ = v_a_3655_;
v_snd_3660_ = v_snd_3657_;
v_err_3661_ = v___x_3683_;
goto v___jp_3658_;
}
v___jp_3658_:
{
uint8_t v_decide_3662_; 
v_decide_3662_ = lean_nat_dec_eq(v_snd_3657_, v_snd_3660_);
lean_dec(v_snd_3660_);
lean_dec(v_snd_3657_);
if (v_decide_3662_ == 0)
{
lean_object* v___x_3663_; 
lean_dec_ref(v_acc_3654_);
lean_inc(v_err_3661_);
v___x_3663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3663_, 0, v_pos_3659_);
lean_ctor_set(v___x_3663_, 1, v_err_3661_);
return v___x_3663_;
}
else
{
lean_object* v___x_3664_; 
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v_pos_3659_);
lean_ctor_set(v___x_3664_, 1, v_acc_3654_);
return v___x_3664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(lean_object* v_acc_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v_fst_3689_; lean_object* v_snd_3690_; lean_object* v_pos_3692_; lean_object* v_snd_3693_; lean_object* v_err_3694_; lean_object* v___x_3698_; uint8_t v_decide_3699_; 
v_fst_3689_ = lean_ctor_get(v_a_3688_, 0);
v_snd_3690_ = lean_ctor_get(v_a_3688_, 1);
lean_inc(v_snd_3690_);
v___x_3698_ = lean_string_utf8_byte_size(v_fst_3689_);
v_decide_3699_ = lean_nat_dec_eq(v_snd_3690_, v___x_3698_);
if (v_decide_3699_ == 0)
{
uint32_t v___x_3700_; uint32_t v_c_3701_; uint8_t v___x_3702_; 
v___x_3700_ = 97;
v_c_3701_ = lean_string_utf8_get_fast(v_fst_3689_, v_snd_3690_);
v___x_3702_ = lean_uint32_dec_eq(v_c_3701_, v___x_3700_);
if (v___x_3702_ == 0)
{
lean_object* v___x_3703_; 
v___x_3703_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1));
lean_inc(v_snd_3690_);
v_pos_3692_ = v_a_3688_;
v_snd_3693_ = v_snd_3690_;
v_err_3694_ = v___x_3703_;
goto v___jp_3691_;
}
else
{
lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3713_; 
lean_inc(v_fst_3689_);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_a_3688_);
if (v_isSharedCheck_3713_ == 0)
{
lean_object* v_unused_3714_; lean_object* v_unused_3715_; 
v_unused_3714_ = lean_ctor_get(v_a_3688_, 1);
lean_dec(v_unused_3714_);
v_unused_3715_ = lean_ctor_get(v_a_3688_, 0);
lean_dec(v_unused_3715_);
v___x_3705_ = v_a_3688_;
v_isShared_3706_ = v_isSharedCheck_3713_;
goto v_resetjp_3704_;
}
else
{
lean_dec(v_a_3688_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3713_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; lean_object* v_it_x27_3709_; 
v___x_3707_ = lean_string_utf8_next_fast(v_fst_3689_, v_snd_3690_);
lean_dec(v_snd_3690_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 1, v___x_3707_);
v_it_x27_3709_ = v___x_3705_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_fst_3689_);
lean_ctor_set(v_reuseFailAlloc_3712_, 1, v___x_3707_);
v_it_x27_3709_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3710_; 
v___x_3710_ = lean_string_push(v_acc_3687_, v___x_3700_);
v_acc_3687_ = v___x_3710_;
v_a_3688_ = v_it_x27_3709_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_box(0);
lean_inc(v_snd_3690_);
v_pos_3692_ = v_a_3688_;
v_snd_3693_ = v_snd_3690_;
v_err_3694_ = v___x_3716_;
goto v___jp_3691_;
}
v___jp_3691_:
{
uint8_t v_decide_3695_; 
v_decide_3695_ = lean_nat_dec_eq(v_snd_3690_, v_snd_3693_);
lean_dec(v_snd_3693_);
lean_dec(v_snd_3690_);
if (v_decide_3695_ == 0)
{
lean_object* v___x_3696_; 
lean_dec_ref(v_acc_3687_);
lean_inc(v_err_3694_);
v___x_3696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3696_, 0, v_pos_3692_);
lean_ctor_set(v___x_3696_, 1, v_err_3694_);
return v___x_3696_;
}
else
{
lean_object* v___x_3697_; 
v___x_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3697_, 0, v_pos_3692_);
lean_ctor_set(v___x_3697_, 1, v_acc_3687_);
return v___x_3697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(lean_object* v_acc_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v_fst_3722_; lean_object* v_snd_3723_; lean_object* v_pos_3725_; lean_object* v_snd_3726_; lean_object* v_err_3727_; lean_object* v___x_3731_; uint8_t v_decide_3732_; 
v_fst_3722_ = lean_ctor_get(v_a_3721_, 0);
v_snd_3723_ = lean_ctor_get(v_a_3721_, 1);
lean_inc(v_snd_3723_);
v___x_3731_ = lean_string_utf8_byte_size(v_fst_3722_);
v_decide_3732_ = lean_nat_dec_eq(v_snd_3723_, v___x_3731_);
if (v_decide_3732_ == 0)
{
uint32_t v___x_3733_; uint32_t v_c_3734_; uint8_t v___x_3735_; 
v___x_3733_ = 79;
v_c_3734_ = lean_string_utf8_get_fast(v_fst_3722_, v_snd_3723_);
v___x_3735_ = lean_uint32_dec_eq(v_c_3734_, v___x_3733_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3736_; 
v___x_3736_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1));
lean_inc(v_snd_3723_);
v_pos_3725_ = v_a_3721_;
v_snd_3726_ = v_snd_3723_;
v_err_3727_ = v___x_3736_;
goto v___jp_3724_;
}
else
{
lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3746_; 
lean_inc(v_fst_3722_);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_a_3721_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; lean_object* v_unused_3748_; 
v_unused_3747_ = lean_ctor_get(v_a_3721_, 1);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_a_3721_, 0);
lean_dec(v_unused_3748_);
v___x_3738_ = v_a_3721_;
v_isShared_3739_ = v_isSharedCheck_3746_;
goto v_resetjp_3737_;
}
else
{
lean_dec(v_a_3721_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3746_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3740_; lean_object* v_it_x27_3742_; 
v___x_3740_ = lean_string_utf8_next_fast(v_fst_3722_, v_snd_3723_);
lean_dec(v_snd_3723_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 1, v___x_3740_);
v_it_x27_3742_ = v___x_3738_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_fst_3722_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v___x_3740_);
v_it_x27_3742_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_string_push(v_acc_3720_, v___x_3733_);
v_acc_3720_ = v___x_3743_;
v_a_3721_ = v_it_x27_3742_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3749_; 
v___x_3749_ = lean_box(0);
lean_inc(v_snd_3723_);
v_pos_3725_ = v_a_3721_;
v_snd_3726_ = v_snd_3723_;
v_err_3727_ = v___x_3749_;
goto v___jp_3724_;
}
v___jp_3724_:
{
uint8_t v_decide_3728_; 
v_decide_3728_ = lean_nat_dec_eq(v_snd_3723_, v_snd_3726_);
lean_dec(v_snd_3726_);
lean_dec(v_snd_3723_);
if (v_decide_3728_ == 0)
{
lean_object* v___x_3729_; 
lean_dec_ref(v_acc_3720_);
lean_inc(v_err_3727_);
v___x_3729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3729_, 0, v_pos_3725_);
lean_ctor_set(v___x_3729_, 1, v_err_3727_);
return v___x_3729_;
}
else
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_pos_3725_);
lean_ctor_set(v___x_3730_, 1, v_acc_3720_);
return v___x_3730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(lean_object* v_acc_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v_fst_3755_; lean_object* v_snd_3756_; lean_object* v_pos_3758_; lean_object* v_snd_3759_; lean_object* v_err_3760_; lean_object* v___x_3764_; uint8_t v_decide_3765_; 
v_fst_3755_ = lean_ctor_get(v_a_3754_, 0);
v_snd_3756_ = lean_ctor_get(v_a_3754_, 1);
lean_inc(v_snd_3756_);
v___x_3764_ = lean_string_utf8_byte_size(v_fst_3755_);
v_decide_3765_ = lean_nat_dec_eq(v_snd_3756_, v___x_3764_);
if (v_decide_3765_ == 0)
{
uint32_t v___x_3766_; uint32_t v_c_3767_; uint8_t v___x_3768_; 
v___x_3766_ = 65;
v_c_3767_ = lean_string_utf8_get_fast(v_fst_3755_, v_snd_3756_);
v___x_3768_ = lean_uint32_dec_eq(v_c_3767_, v___x_3766_);
if (v___x_3768_ == 0)
{
lean_object* v___x_3769_; 
v___x_3769_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1));
lean_inc(v_snd_3756_);
v_pos_3758_ = v_a_3754_;
v_snd_3759_ = v_snd_3756_;
v_err_3760_ = v___x_3769_;
goto v___jp_3757_;
}
else
{
lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3779_; 
lean_inc(v_fst_3755_);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_a_3754_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; lean_object* v_unused_3781_; 
v_unused_3780_ = lean_ctor_get(v_a_3754_, 1);
lean_dec(v_unused_3780_);
v_unused_3781_ = lean_ctor_get(v_a_3754_, 0);
lean_dec(v_unused_3781_);
v___x_3771_ = v_a_3754_;
v_isShared_3772_ = v_isSharedCheck_3779_;
goto v_resetjp_3770_;
}
else
{
lean_dec(v_a_3754_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3779_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3773_; lean_object* v_it_x27_3775_; 
v___x_3773_ = lean_string_utf8_next_fast(v_fst_3755_, v_snd_3756_);
lean_dec(v_snd_3756_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v___x_3773_);
v_it_x27_3775_ = v___x_3771_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_fst_3755_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v___x_3773_);
v_it_x27_3775_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_string_push(v_acc_3753_, v___x_3766_);
v_acc_3753_ = v___x_3776_;
v_a_3754_ = v_it_x27_3775_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3782_; 
v___x_3782_ = lean_box(0);
lean_inc(v_snd_3756_);
v_pos_3758_ = v_a_3754_;
v_snd_3759_ = v_snd_3756_;
v_err_3760_ = v___x_3782_;
goto v___jp_3757_;
}
v___jp_3757_:
{
uint8_t v_decide_3761_; 
v_decide_3761_ = lean_nat_dec_eq(v_snd_3756_, v_snd_3759_);
lean_dec(v_snd_3759_);
lean_dec(v_snd_3756_);
if (v_decide_3761_ == 0)
{
lean_object* v___x_3762_; 
lean_dec_ref(v_acc_3753_);
lean_inc(v_err_3760_);
v___x_3762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3762_, 0, v_pos_3758_);
lean_ctor_set(v___x_3762_, 1, v_err_3760_);
return v___x_3762_;
}
else
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3763_, 0, v_pos_3758_);
lean_ctor_set(v___x_3763_, 1, v_acc_3753_);
return v___x_3763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(lean_object* v_acc_3786_, lean_object* v_a_3787_){
_start:
{
lean_object* v_fst_3788_; lean_object* v_snd_3789_; lean_object* v_pos_3791_; lean_object* v_snd_3792_; lean_object* v_err_3793_; lean_object* v___x_3797_; uint8_t v_decide_3798_; 
v_fst_3788_ = lean_ctor_get(v_a_3787_, 0);
v_snd_3789_ = lean_ctor_get(v_a_3787_, 1);
lean_inc(v_snd_3789_);
v___x_3797_ = lean_string_utf8_byte_size(v_fst_3788_);
v_decide_3798_ = lean_nat_dec_eq(v_snd_3789_, v___x_3797_);
if (v_decide_3798_ == 0)
{
uint32_t v___x_3799_; uint32_t v_c_3800_; uint8_t v___x_3801_; 
v___x_3799_ = 76;
v_c_3800_ = lean_string_utf8_get_fast(v_fst_3788_, v_snd_3789_);
v___x_3801_ = lean_uint32_dec_eq(v_c_3800_, v___x_3799_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; 
v___x_3802_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1));
lean_inc(v_snd_3789_);
v_pos_3791_ = v_a_3787_;
v_snd_3792_ = v_snd_3789_;
v_err_3793_ = v___x_3802_;
goto v___jp_3790_;
}
else
{
lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3812_; 
lean_inc(v_fst_3788_);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_a_3787_);
if (v_isSharedCheck_3812_ == 0)
{
lean_object* v_unused_3813_; lean_object* v_unused_3814_; 
v_unused_3813_ = lean_ctor_get(v_a_3787_, 1);
lean_dec(v_unused_3813_);
v_unused_3814_ = lean_ctor_get(v_a_3787_, 0);
lean_dec(v_unused_3814_);
v___x_3804_ = v_a_3787_;
v_isShared_3805_ = v_isSharedCheck_3812_;
goto v_resetjp_3803_;
}
else
{
lean_dec(v_a_3787_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3812_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; lean_object* v_it_x27_3808_; 
v___x_3806_ = lean_string_utf8_next_fast(v_fst_3788_, v_snd_3789_);
lean_dec(v_snd_3789_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 1, v___x_3806_);
v_it_x27_3808_ = v___x_3804_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_fst_3788_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v___x_3806_);
v_it_x27_3808_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_string_push(v_acc_3786_, v___x_3799_);
v_acc_3786_ = v___x_3809_;
v_a_3787_ = v_it_x27_3808_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3815_; 
v___x_3815_ = lean_box(0);
lean_inc(v_snd_3789_);
v_pos_3791_ = v_a_3787_;
v_snd_3792_ = v_snd_3789_;
v_err_3793_ = v___x_3815_;
goto v___jp_3790_;
}
v___jp_3790_:
{
uint8_t v_decide_3794_; 
v_decide_3794_ = lean_nat_dec_eq(v_snd_3789_, v_snd_3792_);
lean_dec(v_snd_3792_);
lean_dec(v_snd_3789_);
if (v_decide_3794_ == 0)
{
lean_object* v___x_3795_; 
lean_dec_ref(v_acc_3786_);
lean_inc(v_err_3793_);
v___x_3795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3795_, 0, v_pos_3791_);
lean_ctor_set(v___x_3795_, 1, v_err_3793_);
return v___x_3795_;
}
else
{
lean_object* v___x_3796_; 
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v_pos_3791_);
lean_ctor_set(v___x_3796_, 1, v_acc_3786_);
return v___x_3796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(lean_object* v_acc_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v_fst_3821_; lean_object* v_snd_3822_; lean_object* v_pos_3824_; lean_object* v_snd_3825_; lean_object* v_err_3826_; lean_object* v___x_3830_; uint8_t v_decide_3831_; 
v_fst_3821_ = lean_ctor_get(v_a_3820_, 0);
v_snd_3822_ = lean_ctor_get(v_a_3820_, 1);
lean_inc(v_snd_3822_);
v___x_3830_ = lean_string_utf8_byte_size(v_fst_3821_);
v_decide_3831_ = lean_nat_dec_eq(v_snd_3822_, v___x_3830_);
if (v_decide_3831_ == 0)
{
uint32_t v___x_3832_; uint32_t v_c_3833_; uint8_t v___x_3834_; 
v___x_3832_ = 113;
v_c_3833_ = lean_string_utf8_get_fast(v_fst_3821_, v_snd_3822_);
v___x_3834_ = lean_uint32_dec_eq(v_c_3833_, v___x_3832_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; 
v___x_3835_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1));
lean_inc(v_snd_3822_);
v_pos_3824_ = v_a_3820_;
v_snd_3825_ = v_snd_3822_;
v_err_3826_ = v___x_3835_;
goto v___jp_3823_;
}
else
{
lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3845_; 
lean_inc(v_fst_3821_);
v_isSharedCheck_3845_ = !lean_is_exclusive(v_a_3820_);
if (v_isSharedCheck_3845_ == 0)
{
lean_object* v_unused_3846_; lean_object* v_unused_3847_; 
v_unused_3846_ = lean_ctor_get(v_a_3820_, 1);
lean_dec(v_unused_3846_);
v_unused_3847_ = lean_ctor_get(v_a_3820_, 0);
lean_dec(v_unused_3847_);
v___x_3837_ = v_a_3820_;
v_isShared_3838_ = v_isSharedCheck_3845_;
goto v_resetjp_3836_;
}
else
{
lean_dec(v_a_3820_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3845_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v_it_x27_3841_; 
v___x_3839_ = lean_string_utf8_next_fast(v_fst_3821_, v_snd_3822_);
lean_dec(v_snd_3822_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 1, v___x_3839_);
v_it_x27_3841_ = v___x_3837_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_fst_3821_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v___x_3839_);
v_it_x27_3841_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_string_push(v_acc_3819_, v___x_3832_);
v_acc_3819_ = v___x_3842_;
v_a_3820_ = v_it_x27_3841_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_box(0);
lean_inc(v_snd_3822_);
v_pos_3824_ = v_a_3820_;
v_snd_3825_ = v_snd_3822_;
v_err_3826_ = v___x_3848_;
goto v___jp_3823_;
}
v___jp_3823_:
{
uint8_t v_decide_3827_; 
v_decide_3827_ = lean_nat_dec_eq(v_snd_3822_, v_snd_3825_);
lean_dec(v_snd_3825_);
lean_dec(v_snd_3822_);
if (v_decide_3827_ == 0)
{
lean_object* v___x_3828_; 
lean_dec_ref(v_acc_3819_);
lean_inc(v_err_3826_);
v___x_3828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3828_, 0, v_pos_3824_);
lean_ctor_set(v___x_3828_, 1, v_err_3826_);
return v___x_3828_;
}
else
{
lean_object* v___x_3829_; 
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v_pos_3824_);
lean_ctor_set(v___x_3829_, 1, v_acc_3819_);
return v___x_3829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(lean_object* v_acc_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v_fst_3854_; lean_object* v_snd_3855_; lean_object* v_pos_3857_; lean_object* v_snd_3858_; lean_object* v_err_3859_; lean_object* v___x_3863_; uint8_t v_decide_3864_; 
v_fst_3854_ = lean_ctor_get(v_a_3853_, 0);
v_snd_3855_ = lean_ctor_get(v_a_3853_, 1);
lean_inc(v_snd_3855_);
v___x_3863_ = lean_string_utf8_byte_size(v_fst_3854_);
v_decide_3864_ = lean_nat_dec_eq(v_snd_3855_, v___x_3863_);
if (v_decide_3864_ == 0)
{
uint32_t v___x_3865_; uint32_t v_c_3866_; uint8_t v___x_3867_; 
v___x_3865_ = 72;
v_c_3866_ = lean_string_utf8_get_fast(v_fst_3854_, v_snd_3855_);
v___x_3867_ = lean_uint32_dec_eq(v_c_3866_, v___x_3865_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; 
v___x_3868_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1));
lean_inc(v_snd_3855_);
v_pos_3857_ = v_a_3853_;
v_snd_3858_ = v_snd_3855_;
v_err_3859_ = v___x_3868_;
goto v___jp_3856_;
}
else
{
lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3878_; 
lean_inc(v_fst_3854_);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_a_3853_);
if (v_isSharedCheck_3878_ == 0)
{
lean_object* v_unused_3879_; lean_object* v_unused_3880_; 
v_unused_3879_ = lean_ctor_get(v_a_3853_, 1);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_a_3853_, 0);
lean_dec(v_unused_3880_);
v___x_3870_ = v_a_3853_;
v_isShared_3871_ = v_isSharedCheck_3878_;
goto v_resetjp_3869_;
}
else
{
lean_dec(v_a_3853_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3878_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v_it_x27_3874_; 
v___x_3872_ = lean_string_utf8_next_fast(v_fst_3854_, v_snd_3855_);
lean_dec(v_snd_3855_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v___x_3872_);
v_it_x27_3874_ = v___x_3870_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_fst_3854_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v___x_3872_);
v_it_x27_3874_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3875_; 
v___x_3875_ = lean_string_push(v_acc_3852_, v___x_3865_);
v_acc_3852_ = v___x_3875_;
v_a_3853_ = v_it_x27_3874_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_box(0);
lean_inc(v_snd_3855_);
v_pos_3857_ = v_a_3853_;
v_snd_3858_ = v_snd_3855_;
v_err_3859_ = v___x_3881_;
goto v___jp_3856_;
}
v___jp_3856_:
{
uint8_t v_decide_3860_; 
v_decide_3860_ = lean_nat_dec_eq(v_snd_3855_, v_snd_3858_);
lean_dec(v_snd_3858_);
lean_dec(v_snd_3855_);
if (v_decide_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_dec_ref(v_acc_3852_);
lean_inc(v_err_3859_);
v___x_3861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3861_, 0, v_pos_3857_);
lean_ctor_set(v___x_3861_, 1, v_err_3859_);
return v___x_3861_;
}
else
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3862_, 0, v_pos_3857_);
lean_ctor_set(v___x_3862_, 1, v_acc_3852_);
return v___x_3862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(lean_object* v_acc_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_fst_3887_; lean_object* v_snd_3888_; lean_object* v_pos_3890_; lean_object* v_snd_3891_; lean_object* v_err_3892_; lean_object* v___x_3896_; uint8_t v_decide_3897_; 
v_fst_3887_ = lean_ctor_get(v_a_3886_, 0);
v_snd_3888_ = lean_ctor_get(v_a_3886_, 1);
lean_inc(v_snd_3888_);
v___x_3896_ = lean_string_utf8_byte_size(v_fst_3887_);
v_decide_3897_ = lean_nat_dec_eq(v_snd_3888_, v___x_3896_);
if (v_decide_3897_ == 0)
{
uint32_t v___x_3898_; uint32_t v_c_3899_; uint8_t v___x_3900_; 
v___x_3898_ = 118;
v_c_3899_ = lean_string_utf8_get_fast(v_fst_3887_, v_snd_3888_);
v___x_3900_ = lean_uint32_dec_eq(v_c_3899_, v___x_3898_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; 
v___x_3901_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1));
lean_inc(v_snd_3888_);
v_pos_3890_ = v_a_3886_;
v_snd_3891_ = v_snd_3888_;
v_err_3892_ = v___x_3901_;
goto v___jp_3889_;
}
else
{
lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3911_; 
lean_inc(v_fst_3887_);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_a_3886_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; lean_object* v_unused_3913_; 
v_unused_3912_ = lean_ctor_get(v_a_3886_, 1);
lean_dec(v_unused_3912_);
v_unused_3913_ = lean_ctor_get(v_a_3886_, 0);
lean_dec(v_unused_3913_);
v___x_3903_ = v_a_3886_;
v_isShared_3904_ = v_isSharedCheck_3911_;
goto v_resetjp_3902_;
}
else
{
lean_dec(v_a_3886_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3911_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v_it_x27_3907_; 
v___x_3905_ = lean_string_utf8_next_fast(v_fst_3887_, v_snd_3888_);
lean_dec(v_snd_3888_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 1, v___x_3905_);
v_it_x27_3907_ = v___x_3903_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_fst_3887_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v___x_3905_);
v_it_x27_3907_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3908_; 
v___x_3908_ = lean_string_push(v_acc_3885_, v___x_3898_);
v_acc_3885_ = v___x_3908_;
v_a_3886_ = v_it_x27_3907_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3914_; 
v___x_3914_ = lean_box(0);
lean_inc(v_snd_3888_);
v_pos_3890_ = v_a_3886_;
v_snd_3891_ = v_snd_3888_;
v_err_3892_ = v___x_3914_;
goto v___jp_3889_;
}
v___jp_3889_:
{
uint8_t v_decide_3893_; 
v_decide_3893_ = lean_nat_dec_eq(v_snd_3888_, v_snd_3891_);
lean_dec(v_snd_3891_);
lean_dec(v_snd_3888_);
if (v_decide_3893_ == 0)
{
lean_object* v___x_3894_; 
lean_dec_ref(v_acc_3885_);
lean_inc(v_err_3892_);
v___x_3894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3894_, 0, v_pos_3890_);
lean_ctor_set(v___x_3894_, 1, v_err_3892_);
return v___x_3894_;
}
else
{
lean_object* v___x_3895_; 
v___x_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3895_, 0, v_pos_3890_);
lean_ctor_set(v___x_3895_, 1, v_acc_3885_);
return v___x_3895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(lean_object* v_acc_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v_fst_3920_; lean_object* v_snd_3921_; lean_object* v_pos_3923_; lean_object* v_snd_3924_; lean_object* v_err_3925_; lean_object* v___x_3929_; uint8_t v_decide_3930_; 
v_fst_3920_ = lean_ctor_get(v_a_3919_, 0);
v_snd_3921_ = lean_ctor_get(v_a_3919_, 1);
lean_inc(v_snd_3921_);
v___x_3929_ = lean_string_utf8_byte_size(v_fst_3920_);
v_decide_3930_ = lean_nat_dec_eq(v_snd_3921_, v___x_3929_);
if (v_decide_3930_ == 0)
{
uint32_t v___x_3931_; uint32_t v_c_3932_; uint8_t v___x_3933_; 
v___x_3931_ = 87;
v_c_3932_ = lean_string_utf8_get_fast(v_fst_3920_, v_snd_3921_);
v___x_3933_ = lean_uint32_dec_eq(v_c_3932_, v___x_3931_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3934_; 
v___x_3934_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1));
lean_inc(v_snd_3921_);
v_pos_3923_ = v_a_3919_;
v_snd_3924_ = v_snd_3921_;
v_err_3925_ = v___x_3934_;
goto v___jp_3922_;
}
else
{
lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3944_; 
lean_inc(v_fst_3920_);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_a_3919_);
if (v_isSharedCheck_3944_ == 0)
{
lean_object* v_unused_3945_; lean_object* v_unused_3946_; 
v_unused_3945_ = lean_ctor_get(v_a_3919_, 1);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_a_3919_, 0);
lean_dec(v_unused_3946_);
v___x_3936_ = v_a_3919_;
v_isShared_3937_ = v_isSharedCheck_3944_;
goto v_resetjp_3935_;
}
else
{
lean_dec(v_a_3919_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3944_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3938_; lean_object* v_it_x27_3940_; 
v___x_3938_ = lean_string_utf8_next_fast(v_fst_3920_, v_snd_3921_);
lean_dec(v_snd_3921_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 1, v___x_3938_);
v_it_x27_3940_ = v___x_3936_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_fst_3920_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v___x_3938_);
v_it_x27_3940_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3941_; 
v___x_3941_ = lean_string_push(v_acc_3918_, v___x_3931_);
v_acc_3918_ = v___x_3941_;
v_a_3919_ = v_it_x27_3940_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3947_; 
v___x_3947_ = lean_box(0);
lean_inc(v_snd_3921_);
v_pos_3923_ = v_a_3919_;
v_snd_3924_ = v_snd_3921_;
v_err_3925_ = v___x_3947_;
goto v___jp_3922_;
}
v___jp_3922_:
{
uint8_t v_decide_3926_; 
v_decide_3926_ = lean_nat_dec_eq(v_snd_3921_, v_snd_3924_);
lean_dec(v_snd_3924_);
lean_dec(v_snd_3921_);
if (v_decide_3926_ == 0)
{
lean_object* v___x_3927_; 
lean_dec_ref(v_acc_3918_);
lean_inc(v_err_3925_);
v___x_3927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3927_, 0, v_pos_3923_);
lean_ctor_set(v___x_3927_, 1, v_err_3925_);
return v___x_3927_;
}
else
{
lean_object* v___x_3928_; 
v___x_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3928_, 0, v_pos_3923_);
lean_ctor_set(v___x_3928_, 1, v_acc_3918_);
return v___x_3928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(lean_object* v_acc_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v_fst_3953_; lean_object* v_snd_3954_; lean_object* v_pos_3956_; lean_object* v_snd_3957_; lean_object* v_err_3958_; lean_object* v___x_3962_; uint8_t v_decide_3963_; 
v_fst_3953_ = lean_ctor_get(v_a_3952_, 0);
v_snd_3954_ = lean_ctor_get(v_a_3952_, 1);
lean_inc(v_snd_3954_);
v___x_3962_ = lean_string_utf8_byte_size(v_fst_3953_);
v_decide_3963_ = lean_nat_dec_eq(v_snd_3954_, v___x_3962_);
if (v_decide_3963_ == 0)
{
uint32_t v___x_3964_; uint32_t v_c_3965_; uint8_t v___x_3966_; 
v___x_3964_ = 107;
v_c_3965_ = lean_string_utf8_get_fast(v_fst_3953_, v_snd_3954_);
v___x_3966_ = lean_uint32_dec_eq(v_c_3965_, v___x_3964_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3967_; 
v___x_3967_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1));
lean_inc(v_snd_3954_);
v_pos_3956_ = v_a_3952_;
v_snd_3957_ = v_snd_3954_;
v_err_3958_ = v___x_3967_;
goto v___jp_3955_;
}
else
{
lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3977_; 
lean_inc(v_fst_3953_);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_a_3952_);
if (v_isSharedCheck_3977_ == 0)
{
lean_object* v_unused_3978_; lean_object* v_unused_3979_; 
v_unused_3978_ = lean_ctor_get(v_a_3952_, 1);
lean_dec(v_unused_3978_);
v_unused_3979_ = lean_ctor_get(v_a_3952_, 0);
lean_dec(v_unused_3979_);
v___x_3969_ = v_a_3952_;
v_isShared_3970_ = v_isSharedCheck_3977_;
goto v_resetjp_3968_;
}
else
{
lean_dec(v_a_3952_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3977_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3971_; lean_object* v_it_x27_3973_; 
v___x_3971_ = lean_string_utf8_next_fast(v_fst_3953_, v_snd_3954_);
lean_dec(v_snd_3954_);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 1, v___x_3971_);
v_it_x27_3973_ = v___x_3969_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_fst_3953_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v___x_3971_);
v_it_x27_3973_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_string_push(v_acc_3951_, v___x_3964_);
v_acc_3951_ = v___x_3974_;
v_a_3952_ = v_it_x27_3973_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_box(0);
lean_inc(v_snd_3954_);
v_pos_3956_ = v_a_3952_;
v_snd_3957_ = v_snd_3954_;
v_err_3958_ = v___x_3980_;
goto v___jp_3955_;
}
v___jp_3955_:
{
uint8_t v_decide_3959_; 
v_decide_3959_ = lean_nat_dec_eq(v_snd_3954_, v_snd_3957_);
lean_dec(v_snd_3957_);
lean_dec(v_snd_3954_);
if (v_decide_3959_ == 0)
{
lean_object* v___x_3960_; 
lean_dec_ref(v_acc_3951_);
lean_inc(v_err_3958_);
v___x_3960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3960_, 0, v_pos_3956_);
lean_ctor_set(v___x_3960_, 1, v_err_3958_);
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3961_, 0, v_pos_3956_);
lean_ctor_set(v___x_3961_, 1, v_acc_3951_);
return v___x_3961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(lean_object* v_acc_3984_, lean_object* v_a_3985_){
_start:
{
lean_object* v_fst_3986_; lean_object* v_snd_3987_; lean_object* v_pos_3989_; lean_object* v_snd_3990_; lean_object* v_err_3991_; lean_object* v___x_3995_; uint8_t v_decide_3996_; 
v_fst_3986_ = lean_ctor_get(v_a_3985_, 0);
v_snd_3987_ = lean_ctor_get(v_a_3985_, 1);
lean_inc(v_snd_3987_);
v___x_3995_ = lean_string_utf8_byte_size(v_fst_3986_);
v_decide_3996_ = lean_nat_dec_eq(v_snd_3987_, v___x_3995_);
if (v_decide_3996_ == 0)
{
uint32_t v___x_3997_; uint32_t v_c_3998_; uint8_t v___x_3999_; 
v___x_3997_ = 121;
v_c_3998_ = lean_string_utf8_get_fast(v_fst_3986_, v_snd_3987_);
v___x_3999_ = lean_uint32_dec_eq(v_c_3998_, v___x_3997_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; 
v___x_4000_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1));
lean_inc(v_snd_3987_);
v_pos_3989_ = v_a_3985_;
v_snd_3990_ = v_snd_3987_;
v_err_3991_ = v___x_4000_;
goto v___jp_3988_;
}
else
{
lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4010_; 
lean_inc(v_fst_3986_);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_a_3985_);
if (v_isSharedCheck_4010_ == 0)
{
lean_object* v_unused_4011_; lean_object* v_unused_4012_; 
v_unused_4011_ = lean_ctor_get(v_a_3985_, 1);
lean_dec(v_unused_4011_);
v_unused_4012_ = lean_ctor_get(v_a_3985_, 0);
lean_dec(v_unused_4012_);
v___x_4002_ = v_a_3985_;
v_isShared_4003_ = v_isSharedCheck_4010_;
goto v_resetjp_4001_;
}
else
{
lean_dec(v_a_3985_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4010_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; lean_object* v_it_x27_4006_; 
v___x_4004_ = lean_string_utf8_next_fast(v_fst_3986_, v_snd_3987_);
lean_dec(v_snd_3987_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 1, v___x_4004_);
v_it_x27_4006_ = v___x_4002_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_fst_3986_);
lean_ctor_set(v_reuseFailAlloc_4009_, 1, v___x_4004_);
v_it_x27_4006_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4007_; 
v___x_4007_ = lean_string_push(v_acc_3984_, v___x_3997_);
v_acc_3984_ = v___x_4007_;
v_a_3985_ = v_it_x27_4006_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4013_; 
v___x_4013_ = lean_box(0);
lean_inc(v_snd_3987_);
v_pos_3989_ = v_a_3985_;
v_snd_3990_ = v_snd_3987_;
v_err_3991_ = v___x_4013_;
goto v___jp_3988_;
}
v___jp_3988_:
{
uint8_t v_decide_3992_; 
v_decide_3992_ = lean_nat_dec_eq(v_snd_3987_, v_snd_3990_);
lean_dec(v_snd_3990_);
lean_dec(v_snd_3987_);
if (v_decide_3992_ == 0)
{
lean_object* v___x_3993_; 
lean_dec_ref(v_acc_3984_);
lean_inc(v_err_3991_);
v___x_3993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3993_, 0, v_pos_3989_);
lean_ctor_set(v___x_3993_, 1, v_err_3991_);
return v___x_3993_;
}
else
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3994_, 0, v_pos_3989_);
lean_ctor_set(v___x_3994_, 1, v_acc_3984_);
return v___x_3994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(lean_object* v_acc_4017_, lean_object* v_a_4018_){
_start:
{
lean_object* v_fst_4019_; lean_object* v_snd_4020_; lean_object* v_pos_4022_; lean_object* v_snd_4023_; lean_object* v_err_4024_; lean_object* v___x_4028_; uint8_t v_decide_4029_; 
v_fst_4019_ = lean_ctor_get(v_a_4018_, 0);
v_snd_4020_ = lean_ctor_get(v_a_4018_, 1);
lean_inc(v_snd_4020_);
v___x_4028_ = lean_string_utf8_byte_size(v_fst_4019_);
v_decide_4029_ = lean_nat_dec_eq(v_snd_4020_, v___x_4028_);
if (v_decide_4029_ == 0)
{
uint32_t v___x_4030_; uint32_t v_c_4031_; uint8_t v___x_4032_; 
v___x_4030_ = 98;
v_c_4031_ = lean_string_utf8_get_fast(v_fst_4019_, v_snd_4020_);
v___x_4032_ = lean_uint32_dec_eq(v_c_4031_, v___x_4030_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; 
v___x_4033_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1));
lean_inc(v_snd_4020_);
v_pos_4022_ = v_a_4018_;
v_snd_4023_ = v_snd_4020_;
v_err_4024_ = v___x_4033_;
goto v___jp_4021_;
}
else
{
lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4043_; 
lean_inc(v_fst_4019_);
v_isSharedCheck_4043_ = !lean_is_exclusive(v_a_4018_);
if (v_isSharedCheck_4043_ == 0)
{
lean_object* v_unused_4044_; lean_object* v_unused_4045_; 
v_unused_4044_ = lean_ctor_get(v_a_4018_, 1);
lean_dec(v_unused_4044_);
v_unused_4045_ = lean_ctor_get(v_a_4018_, 0);
lean_dec(v_unused_4045_);
v___x_4035_ = v_a_4018_;
v_isShared_4036_ = v_isSharedCheck_4043_;
goto v_resetjp_4034_;
}
else
{
lean_dec(v_a_4018_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4043_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4037_; lean_object* v_it_x27_4039_; 
v___x_4037_ = lean_string_utf8_next_fast(v_fst_4019_, v_snd_4020_);
lean_dec(v_snd_4020_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 1, v___x_4037_);
v_it_x27_4039_ = v___x_4035_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_fst_4019_);
lean_ctor_set(v_reuseFailAlloc_4042_, 1, v___x_4037_);
v_it_x27_4039_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
lean_object* v___x_4040_; 
v___x_4040_ = lean_string_push(v_acc_4017_, v___x_4030_);
v_acc_4017_ = v___x_4040_;
v_a_4018_ = v_it_x27_4039_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4046_; 
v___x_4046_ = lean_box(0);
lean_inc(v_snd_4020_);
v_pos_4022_ = v_a_4018_;
v_snd_4023_ = v_snd_4020_;
v_err_4024_ = v___x_4046_;
goto v___jp_4021_;
}
v___jp_4021_:
{
uint8_t v_decide_4025_; 
v_decide_4025_ = lean_nat_dec_eq(v_snd_4020_, v_snd_4023_);
lean_dec(v_snd_4023_);
lean_dec(v_snd_4020_);
if (v_decide_4025_ == 0)
{
lean_object* v___x_4026_; 
lean_dec_ref(v_acc_4017_);
lean_inc(v_err_4024_);
v___x_4026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4026_, 0, v_pos_4022_);
lean_ctor_set(v___x_4026_, 1, v_err_4024_);
return v___x_4026_;
}
else
{
lean_object* v___x_4027_; 
v___x_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4027_, 0, v_pos_4022_);
lean_ctor_set(v___x_4027_, 1, v_acc_4017_);
return v___x_4027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(lean_object* v_acc_4050_, lean_object* v_a_4051_){
_start:
{
lean_object* v_fst_4052_; lean_object* v_snd_4053_; lean_object* v_pos_4055_; lean_object* v_snd_4056_; lean_object* v_err_4057_; lean_object* v___x_4061_; uint8_t v_decide_4062_; 
v_fst_4052_ = lean_ctor_get(v_a_4051_, 0);
v_snd_4053_ = lean_ctor_get(v_a_4051_, 1);
lean_inc(v_snd_4053_);
v___x_4061_ = lean_string_utf8_byte_size(v_fst_4052_);
v_decide_4062_ = lean_nat_dec_eq(v_snd_4053_, v___x_4061_);
if (v_decide_4062_ == 0)
{
uint32_t v___x_4063_; uint32_t v_c_4064_; uint8_t v___x_4065_; 
v___x_4063_ = 109;
v_c_4064_ = lean_string_utf8_get_fast(v_fst_4052_, v_snd_4053_);
v___x_4065_ = lean_uint32_dec_eq(v_c_4064_, v___x_4063_);
if (v___x_4065_ == 0)
{
lean_object* v___x_4066_; 
v___x_4066_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1));
lean_inc(v_snd_4053_);
v_pos_4055_ = v_a_4051_;
v_snd_4056_ = v_snd_4053_;
v_err_4057_ = v___x_4066_;
goto v___jp_4054_;
}
else
{
lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4076_; 
lean_inc(v_fst_4052_);
v_isSharedCheck_4076_ = !lean_is_exclusive(v_a_4051_);
if (v_isSharedCheck_4076_ == 0)
{
lean_object* v_unused_4077_; lean_object* v_unused_4078_; 
v_unused_4077_ = lean_ctor_get(v_a_4051_, 1);
lean_dec(v_unused_4077_);
v_unused_4078_ = lean_ctor_get(v_a_4051_, 0);
lean_dec(v_unused_4078_);
v___x_4068_ = v_a_4051_;
v_isShared_4069_ = v_isSharedCheck_4076_;
goto v_resetjp_4067_;
}
else
{
lean_dec(v_a_4051_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4076_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4070_; lean_object* v_it_x27_4072_; 
v___x_4070_ = lean_string_utf8_next_fast(v_fst_4052_, v_snd_4053_);
lean_dec(v_snd_4053_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 1, v___x_4070_);
v_it_x27_4072_ = v___x_4068_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_fst_4052_);
lean_ctor_set(v_reuseFailAlloc_4075_, 1, v___x_4070_);
v_it_x27_4072_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4073_; 
v___x_4073_ = lean_string_push(v_acc_4050_, v___x_4063_);
v_acc_4050_ = v___x_4073_;
v_a_4051_ = v_it_x27_4072_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_box(0);
lean_inc(v_snd_4053_);
v_pos_4055_ = v_a_4051_;
v_snd_4056_ = v_snd_4053_;
v_err_4057_ = v___x_4079_;
goto v___jp_4054_;
}
v___jp_4054_:
{
uint8_t v_decide_4058_; 
v_decide_4058_ = lean_nat_dec_eq(v_snd_4053_, v_snd_4056_);
lean_dec(v_snd_4056_);
lean_dec(v_snd_4053_);
if (v_decide_4058_ == 0)
{
lean_object* v___x_4059_; 
lean_dec_ref(v_acc_4050_);
lean_inc(v_err_4057_);
v___x_4059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4059_, 0, v_pos_4055_);
lean_ctor_set(v___x_4059_, 1, v_err_4057_);
return v___x_4059_;
}
else
{
lean_object* v___x_4060_; 
v___x_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4060_, 0, v_pos_4055_);
lean_ctor_set(v___x_4060_, 1, v_acc_4050_);
return v___x_4060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(lean_object* v_acc_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_fst_4085_; lean_object* v_snd_4086_; lean_object* v_pos_4088_; lean_object* v_snd_4089_; lean_object* v_err_4090_; lean_object* v___x_4094_; uint8_t v_decide_4095_; 
v_fst_4085_ = lean_ctor_get(v_a_4084_, 0);
v_snd_4086_ = lean_ctor_get(v_a_4084_, 1);
lean_inc(v_snd_4086_);
v___x_4094_ = lean_string_utf8_byte_size(v_fst_4085_);
v_decide_4095_ = lean_nat_dec_eq(v_snd_4086_, v___x_4094_);
if (v_decide_4095_ == 0)
{
uint32_t v___x_4096_; uint32_t v_c_4097_; uint8_t v___x_4098_; 
v___x_4096_ = 117;
v_c_4097_ = lean_string_utf8_get_fast(v_fst_4085_, v_snd_4086_);
v___x_4098_ = lean_uint32_dec_eq(v_c_4097_, v___x_4096_);
if (v___x_4098_ == 0)
{
lean_object* v___x_4099_; 
v___x_4099_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1));
lean_inc(v_snd_4086_);
v_pos_4088_ = v_a_4084_;
v_snd_4089_ = v_snd_4086_;
v_err_4090_ = v___x_4099_;
goto v___jp_4087_;
}
else
{
lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4109_; 
lean_inc(v_fst_4085_);
v_isSharedCheck_4109_ = !lean_is_exclusive(v_a_4084_);
if (v_isSharedCheck_4109_ == 0)
{
lean_object* v_unused_4110_; lean_object* v_unused_4111_; 
v_unused_4110_ = lean_ctor_get(v_a_4084_, 1);
lean_dec(v_unused_4110_);
v_unused_4111_ = lean_ctor_get(v_a_4084_, 0);
lean_dec(v_unused_4111_);
v___x_4101_ = v_a_4084_;
v_isShared_4102_ = v_isSharedCheck_4109_;
goto v_resetjp_4100_;
}
else
{
lean_dec(v_a_4084_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4109_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4103_; lean_object* v_it_x27_4105_; 
v___x_4103_ = lean_string_utf8_next_fast(v_fst_4085_, v_snd_4086_);
lean_dec(v_snd_4086_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 1, v___x_4103_);
v_it_x27_4105_ = v___x_4101_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_fst_4085_);
lean_ctor_set(v_reuseFailAlloc_4108_, 1, v___x_4103_);
v_it_x27_4105_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_string_push(v_acc_4083_, v___x_4096_);
v_acc_4083_ = v___x_4106_;
v_a_4084_ = v_it_x27_4105_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4112_; 
v___x_4112_ = lean_box(0);
lean_inc(v_snd_4086_);
v_pos_4088_ = v_a_4084_;
v_snd_4089_ = v_snd_4086_;
v_err_4090_ = v___x_4112_;
goto v___jp_4087_;
}
v___jp_4087_:
{
uint8_t v_decide_4091_; 
v_decide_4091_ = lean_nat_dec_eq(v_snd_4086_, v_snd_4089_);
lean_dec(v_snd_4089_);
lean_dec(v_snd_4086_);
if (v_decide_4091_ == 0)
{
lean_object* v___x_4092_; 
lean_dec_ref(v_acc_4083_);
lean_inc(v_err_4090_);
v___x_4092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4092_, 0, v_pos_4088_);
lean_ctor_set(v___x_4092_, 1, v_err_4090_);
return v___x_4092_;
}
else
{
lean_object* v___x_4093_; 
v___x_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4093_, 0, v_pos_4088_);
lean_ctor_set(v___x_4093_, 1, v_acc_4083_);
return v___x_4093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(lean_object* v_acc_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v_fst_4118_; lean_object* v_snd_4119_; lean_object* v_pos_4121_; lean_object* v_snd_4122_; lean_object* v_err_4123_; lean_object* v___x_4127_; uint8_t v_decide_4128_; 
v_fst_4118_ = lean_ctor_get(v_a_4117_, 0);
v_snd_4119_ = lean_ctor_get(v_a_4117_, 1);
lean_inc(v_snd_4119_);
v___x_4127_ = lean_string_utf8_byte_size(v_fst_4118_);
v_decide_4128_ = lean_nat_dec_eq(v_snd_4119_, v___x_4127_);
if (v_decide_4128_ == 0)
{
uint32_t v___x_4129_; uint32_t v_c_4130_; uint8_t v___x_4131_; 
v___x_4129_ = 90;
v_c_4130_ = lean_string_utf8_get_fast(v_fst_4118_, v_snd_4119_);
v___x_4131_ = lean_uint32_dec_eq(v_c_4130_, v___x_4129_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4132_; 
v___x_4132_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1));
lean_inc(v_snd_4119_);
v_pos_4121_ = v_a_4117_;
v_snd_4122_ = v_snd_4119_;
v_err_4123_ = v___x_4132_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4142_; 
lean_inc(v_fst_4118_);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_a_4117_);
if (v_isSharedCheck_4142_ == 0)
{
lean_object* v_unused_4143_; lean_object* v_unused_4144_; 
v_unused_4143_ = lean_ctor_get(v_a_4117_, 1);
lean_dec(v_unused_4143_);
v_unused_4144_ = lean_ctor_get(v_a_4117_, 0);
lean_dec(v_unused_4144_);
v___x_4134_ = v_a_4117_;
v_isShared_4135_ = v_isSharedCheck_4142_;
goto v_resetjp_4133_;
}
else
{
lean_dec(v_a_4117_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4142_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; lean_object* v_it_x27_4138_; 
v___x_4136_ = lean_string_utf8_next_fast(v_fst_4118_, v_snd_4119_);
lean_dec(v_snd_4119_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 1, v___x_4136_);
v_it_x27_4138_ = v___x_4134_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_fst_4118_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v___x_4136_);
v_it_x27_4138_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
lean_object* v___x_4139_; 
v___x_4139_ = lean_string_push(v_acc_4116_, v___x_4129_);
v_acc_4116_ = v___x_4139_;
v_a_4117_ = v_it_x27_4138_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4145_; 
v___x_4145_ = lean_box(0);
lean_inc(v_snd_4119_);
v_pos_4121_ = v_a_4117_;
v_snd_4122_ = v_snd_4119_;
v_err_4123_ = v___x_4145_;
goto v___jp_4120_;
}
v___jp_4120_:
{
uint8_t v_decide_4124_; 
v_decide_4124_ = lean_nat_dec_eq(v_snd_4119_, v_snd_4122_);
lean_dec(v_snd_4122_);
lean_dec(v_snd_4119_);
if (v_decide_4124_ == 0)
{
lean_object* v___x_4125_; 
lean_dec_ref(v_acc_4116_);
lean_inc(v_err_4123_);
v___x_4125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4125_, 0, v_pos_4121_);
lean_ctor_set(v___x_4125_, 1, v_err_4123_);
return v___x_4125_;
}
else
{
lean_object* v___x_4126_; 
v___x_4126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4126_, 0, v_pos_4121_);
lean_ctor_set(v___x_4126_, 1, v_acc_4116_);
return v___x_4126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(lean_object* v_acc_4149_, lean_object* v_a_4150_){
_start:
{
lean_object* v_fst_4151_; lean_object* v_snd_4152_; lean_object* v_pos_4154_; lean_object* v_snd_4155_; lean_object* v_err_4156_; lean_object* v___x_4160_; uint8_t v_decide_4161_; 
v_fst_4151_ = lean_ctor_get(v_a_4150_, 0);
v_snd_4152_ = lean_ctor_get(v_a_4150_, 1);
lean_inc(v_snd_4152_);
v___x_4160_ = lean_string_utf8_byte_size(v_fst_4151_);
v_decide_4161_ = lean_nat_dec_eq(v_snd_4152_, v___x_4160_);
if (v_decide_4161_ == 0)
{
uint32_t v___x_4162_; uint32_t v_c_4163_; uint8_t v___x_4164_; 
v___x_4162_ = 78;
v_c_4163_ = lean_string_utf8_get_fast(v_fst_4151_, v_snd_4152_);
v___x_4164_ = lean_uint32_dec_eq(v_c_4163_, v___x_4162_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; 
v___x_4165_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1));
lean_inc(v_snd_4152_);
v_pos_4154_ = v_a_4150_;
v_snd_4155_ = v_snd_4152_;
v_err_4156_ = v___x_4165_;
goto v___jp_4153_;
}
else
{
lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4175_; 
lean_inc(v_fst_4151_);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_a_4150_);
if (v_isSharedCheck_4175_ == 0)
{
lean_object* v_unused_4176_; lean_object* v_unused_4177_; 
v_unused_4176_ = lean_ctor_get(v_a_4150_, 1);
lean_dec(v_unused_4176_);
v_unused_4177_ = lean_ctor_get(v_a_4150_, 0);
lean_dec(v_unused_4177_);
v___x_4167_ = v_a_4150_;
v_isShared_4168_ = v_isSharedCheck_4175_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v_a_4150_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4175_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; lean_object* v_it_x27_4171_; 
v___x_4169_ = lean_string_utf8_next_fast(v_fst_4151_, v_snd_4152_);
lean_dec(v_snd_4152_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 1, v___x_4169_);
v_it_x27_4171_ = v___x_4167_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_fst_4151_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___x_4169_);
v_it_x27_4171_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_string_push(v_acc_4149_, v___x_4162_);
v_acc_4149_ = v___x_4172_;
v_a_4150_ = v_it_x27_4171_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4178_; 
v___x_4178_ = lean_box(0);
lean_inc(v_snd_4152_);
v_pos_4154_ = v_a_4150_;
v_snd_4155_ = v_snd_4152_;
v_err_4156_ = v___x_4178_;
goto v___jp_4153_;
}
v___jp_4153_:
{
uint8_t v_decide_4157_; 
v_decide_4157_ = lean_nat_dec_eq(v_snd_4152_, v_snd_4155_);
lean_dec(v_snd_4155_);
lean_dec(v_snd_4152_);
if (v_decide_4157_ == 0)
{
lean_object* v___x_4158_; 
lean_dec_ref(v_acc_4149_);
lean_inc(v_err_4156_);
v___x_4158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4158_, 0, v_pos_4154_);
lean_ctor_set(v___x_4158_, 1, v_err_4156_);
return v___x_4158_;
}
else
{
lean_object* v___x_4159_; 
v___x_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4159_, 0, v_pos_4154_);
lean_ctor_set(v___x_4159_, 1, v_acc_4149_);
return v___x_4159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(lean_object* v_acc_4182_, lean_object* v_a_4183_){
_start:
{
lean_object* v_fst_4184_; lean_object* v_snd_4185_; lean_object* v_pos_4187_; lean_object* v_snd_4188_; lean_object* v_err_4189_; lean_object* v___x_4193_; uint8_t v_decide_4194_; 
v_fst_4184_ = lean_ctor_get(v_a_4183_, 0);
v_snd_4185_ = lean_ctor_get(v_a_4183_, 1);
lean_inc(v_snd_4185_);
v___x_4193_ = lean_string_utf8_byte_size(v_fst_4184_);
v_decide_4194_ = lean_nat_dec_eq(v_snd_4185_, v___x_4193_);
if (v_decide_4194_ == 0)
{
uint32_t v___x_4195_; uint32_t v_c_4196_; uint8_t v___x_4197_; 
v___x_4195_ = 70;
v_c_4196_ = lean_string_utf8_get_fast(v_fst_4184_, v_snd_4185_);
v___x_4197_ = lean_uint32_dec_eq(v_c_4196_, v___x_4195_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; 
v___x_4198_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1));
lean_inc(v_snd_4185_);
v_pos_4187_ = v_a_4183_;
v_snd_4188_ = v_snd_4185_;
v_err_4189_ = v___x_4198_;
goto v___jp_4186_;
}
else
{
lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4208_; 
lean_inc(v_fst_4184_);
v_isSharedCheck_4208_ = !lean_is_exclusive(v_a_4183_);
if (v_isSharedCheck_4208_ == 0)
{
lean_object* v_unused_4209_; lean_object* v_unused_4210_; 
v_unused_4209_ = lean_ctor_get(v_a_4183_, 1);
lean_dec(v_unused_4209_);
v_unused_4210_ = lean_ctor_get(v_a_4183_, 0);
lean_dec(v_unused_4210_);
v___x_4200_ = v_a_4183_;
v_isShared_4201_ = v_isSharedCheck_4208_;
goto v_resetjp_4199_;
}
else
{
lean_dec(v_a_4183_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4208_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; lean_object* v_it_x27_4204_; 
v___x_4202_ = lean_string_utf8_next_fast(v_fst_4184_, v_snd_4185_);
lean_dec(v_snd_4185_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 1, v___x_4202_);
v_it_x27_4204_ = v___x_4200_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_fst_4184_);
lean_ctor_set(v_reuseFailAlloc_4207_, 1, v___x_4202_);
v_it_x27_4204_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
lean_object* v___x_4205_; 
v___x_4205_ = lean_string_push(v_acc_4182_, v___x_4195_);
v_acc_4182_ = v___x_4205_;
v_a_4183_ = v_it_x27_4204_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4211_; 
v___x_4211_ = lean_box(0);
lean_inc(v_snd_4185_);
v_pos_4187_ = v_a_4183_;
v_snd_4188_ = v_snd_4185_;
v_err_4189_ = v___x_4211_;
goto v___jp_4186_;
}
v___jp_4186_:
{
uint8_t v_decide_4190_; 
v_decide_4190_ = lean_nat_dec_eq(v_snd_4185_, v_snd_4188_);
lean_dec(v_snd_4188_);
lean_dec(v_snd_4185_);
if (v_decide_4190_ == 0)
{
lean_object* v___x_4191_; 
lean_dec_ref(v_acc_4182_);
lean_inc(v_err_4189_);
v___x_4191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4191_, 0, v_pos_4187_);
lean_ctor_set(v___x_4191_, 1, v_err_4189_);
return v___x_4191_;
}
else
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v_pos_4187_);
lean_ctor_set(v___x_4192_, 1, v_acc_4182_);
return v___x_4192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(lean_object* v_acc_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v_fst_4217_; lean_object* v_snd_4218_; lean_object* v_pos_4220_; lean_object* v_snd_4221_; lean_object* v_err_4222_; lean_object* v___x_4226_; uint8_t v_decide_4227_; 
v_fst_4217_ = lean_ctor_get(v_a_4216_, 0);
v_snd_4218_ = lean_ctor_get(v_a_4216_, 1);
lean_inc(v_snd_4218_);
v___x_4226_ = lean_string_utf8_byte_size(v_fst_4217_);
v_decide_4227_ = lean_nat_dec_eq(v_snd_4218_, v___x_4226_);
if (v_decide_4227_ == 0)
{
uint32_t v___x_4228_; uint32_t v_c_4229_; uint8_t v___x_4230_; 
v___x_4228_ = 66;
v_c_4229_ = lean_string_utf8_get_fast(v_fst_4217_, v_snd_4218_);
v___x_4230_ = lean_uint32_dec_eq(v_c_4229_, v___x_4228_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4231_; 
v___x_4231_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1));
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
uint8_t v_decide_4223_; 
v_decide_4223_ = lean_nat_dec_eq(v_snd_4218_, v_snd_4221_);
lean_dec(v_snd_4221_);
lean_dec(v_snd_4218_);
if (v_decide_4223_ == 0)
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
LEAN_EXPORT lean_object* l_Std_Time_parseModifier(lean_object* v_a_4318_){
_start:
{
lean_object* v___y_4320_; lean_object* v_fst_4323_; lean_object* v_snd_4324_; lean_object* v___f_4325_; lean_object* v_snd_4327_; lean_object* v___y_4328_; lean_object* v_pos_4329_; lean_object* v_snd_4365_; lean_object* v_pos_4366_; lean_object* v_err_4367_; lean_object* v___y_4370_; lean_object* v_snd_4371_; lean_object* v___f_4373_; lean_object* v_snd_4375_; lean_object* v___y_4376_; lean_object* v_pos_4377_; lean_object* v_snd_4406_; lean_object* v_pos_4407_; lean_object* v_err_4408_; lean_object* v___y_4411_; lean_object* v_snd_4412_; lean_object* v___f_4414_; lean_object* v_snd_4416_; lean_object* v___y_4417_; lean_object* v_pos_4418_; lean_object* v_snd_4447_; lean_object* v_pos_4448_; lean_object* v_err_4449_; lean_object* v___y_4452_; lean_object* v_snd_4453_; lean_object* v___f_4455_; lean_object* v_snd_4457_; lean_object* v___y_4458_; lean_object* v_pos_4459_; lean_object* v_snd_4488_; lean_object* v_pos_4489_; lean_object* v_err_4490_; lean_object* v___y_4493_; lean_object* v_snd_4494_; lean_object* v___f_4496_; lean_object* v_snd_4498_; lean_object* v___y_4499_; lean_object* v_pos_4500_; lean_object* v_snd_4529_; lean_object* v_pos_4530_; lean_object* v_err_4531_; lean_object* v___y_4534_; lean_object* v_snd_4535_; lean_object* v___f_4537_; lean_object* v_snd_4539_; lean_object* v___y_4540_; lean_object* v_pos_4541_; lean_object* v_snd_4570_; lean_object* v_pos_4571_; lean_object* v_err_4572_; lean_object* v___y_4575_; lean_object* v_snd_4576_; lean_object* v_snd_4579_; lean_object* v___y_4580_; lean_object* v_pos_4581_; lean_object* v_snd_4610_; lean_object* v_pos_4611_; lean_object* v_err_4612_; lean_object* v___y_4615_; lean_object* v_snd_4616_; lean_object* v___f_4618_; lean_object* v_snd_4620_; lean_object* v___y_4621_; lean_object* v_pos_4622_; lean_object* v_snd_4650_; lean_object* v_pos_4651_; lean_object* v_err_4652_; lean_object* v___y_4655_; lean_object* v_snd_4656_; lean_object* v___f_4658_; lean_object* v_snd_4660_; lean_object* v___y_4661_; lean_object* v_pos_4662_; lean_object* v_snd_4690_; lean_object* v_pos_4691_; lean_object* v_err_4692_; lean_object* v___y_4695_; lean_object* v_snd_4696_; lean_object* v___f_4698_; lean_object* v_snd_4700_; lean_object* v___y_4701_; lean_object* v_pos_4702_; lean_object* v_snd_4730_; lean_object* v_pos_4731_; lean_object* v_err_4732_; lean_object* v___y_4735_; lean_object* v_snd_4736_; lean_object* v___f_4738_; lean_object* v_snd_4740_; lean_object* v___y_4741_; lean_object* v_pos_4742_; lean_object* v_snd_4771_; lean_object* v_pos_4772_; lean_object* v_err_4773_; lean_object* v___y_4776_; lean_object* v_snd_4777_; lean_object* v___f_4779_; lean_object* v_snd_4781_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v_pos_4784_; lean_object* v_snd_4813_; lean_object* v___y_4814_; lean_object* v_pos_4815_; lean_object* v_err_4816_; lean_object* v___y_4819_; lean_object* v_snd_4820_; lean_object* v___y_4821_; lean_object* v___f_4823_; lean_object* v___y_4825_; lean_object* v_snd_4826_; lean_object* v___y_4827_; lean_object* v_pos_4828_; lean_object* v___y_4857_; lean_object* v_snd_4858_; lean_object* v_pos_4859_; lean_object* v_err_4860_; lean_object* v___y_4863_; lean_object* v___y_4864_; lean_object* v_snd_4865_; lean_object* v___f_4867_; lean_object* v___y_4869_; lean_object* v_snd_4870_; lean_object* v___y_4871_; lean_object* v_pos_4872_; lean_object* v___y_4901_; lean_object* v_snd_4902_; lean_object* v_pos_4903_; lean_object* v_err_4904_; lean_object* v___y_4907_; lean_object* v___y_4908_; lean_object* v_snd_4909_; lean_object* v___f_4911_; lean_object* v_snd_4913_; lean_object* v___y_4914_; lean_object* v___y_4915_; lean_object* v_pos_4916_; lean_object* v___y_4945_; lean_object* v_snd_4946_; lean_object* v_pos_4947_; lean_object* v_err_4948_; lean_object* v___y_4951_; lean_object* v___y_4952_; lean_object* v_snd_4953_; lean_object* v___f_4955_; lean_object* v___y_4957_; lean_object* v_snd_4958_; lean_object* v___y_4959_; lean_object* v_pos_4960_; lean_object* v___y_4989_; lean_object* v_snd_4990_; lean_object* v_pos_4991_; lean_object* v_err_4992_; lean_object* v___y_4995_; lean_object* v___y_4996_; lean_object* v_snd_4997_; lean_object* v___f_4999_; lean_object* v___y_5001_; lean_object* v_snd_5002_; lean_object* v___y_5003_; lean_object* v_pos_5004_; lean_object* v___y_5033_; lean_object* v_snd_5034_; lean_object* v_pos_5035_; lean_object* v_err_5036_; lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v_snd_5041_; lean_object* v___y_5044_; lean_object* v_snd_5045_; lean_object* v___y_5046_; lean_object* v_pos_5047_; lean_object* v___y_5076_; lean_object* v_snd_5077_; lean_object* v_pos_5078_; lean_object* v_err_5079_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v_snd_5084_; lean_object* v___y_5087_; lean_object* v_snd_5088_; lean_object* v___y_5089_; lean_object* v_pos_5090_; lean_object* v___y_5119_; lean_object* v_snd_5120_; lean_object* v_pos_5121_; lean_object* v_err_5122_; lean_object* v___y_5125_; lean_object* v___y_5126_; lean_object* v_snd_5127_; lean_object* v___y_5130_; lean_object* v_snd_5131_; lean_object* v___y_5132_; lean_object* v_pos_5133_; lean_object* v___y_5162_; lean_object* v_snd_5163_; lean_object* v_pos_5164_; lean_object* v_err_5165_; lean_object* v___y_5168_; lean_object* v___y_5169_; lean_object* v_snd_5170_; lean_object* v___f_5172_; lean_object* v_snd_5174_; lean_object* v___y_5175_; lean_object* v___y_5176_; lean_object* v___y_5177_; lean_object* v_pos_5178_; lean_object* v_snd_5207_; lean_object* v___y_5208_; lean_object* v___y_5209_; lean_object* v_pos_5210_; lean_object* v_err_5211_; lean_object* v___y_5214_; lean_object* v_snd_5215_; lean_object* v___y_5216_; lean_object* v___y_5217_; lean_object* v___f_5219_; lean_object* v___y_5221_; lean_object* v_snd_5222_; lean_object* v___y_5223_; lean_object* v___y_5224_; lean_object* v_pos_5225_; lean_object* v___y_5254_; lean_object* v_snd_5255_; lean_object* v___y_5256_; lean_object* v_pos_5257_; lean_object* v_err_5258_; lean_object* v___y_5261_; lean_object* v___y_5262_; lean_object* v_snd_5263_; lean_object* v___y_5264_; lean_object* v___f_5266_; lean_object* v_snd_5268_; lean_object* v___y_5269_; lean_object* v___y_5270_; lean_object* v___y_5271_; lean_object* v_pos_5272_; lean_object* v_snd_5301_; lean_object* v___y_5302_; lean_object* v___y_5303_; lean_object* v_pos_5304_; lean_object* v_err_5305_; lean_object* v___y_5308_; lean_object* v_snd_5309_; lean_object* v___y_5310_; lean_object* v___y_5311_; lean_object* v___f_5313_; lean_object* v___y_5315_; lean_object* v___y_5316_; lean_object* v___y_5317_; lean_object* v___y_5318_; lean_object* v_pos_5319_; lean_object* v___y_5348_; lean_object* v___y_5349_; lean_object* v___y_5350_; lean_object* v_pos_5351_; lean_object* v_err_5352_; lean_object* v___y_5355_; lean_object* v___y_5356_; lean_object* v___y_5357_; lean_object* v___y_5358_; lean_object* v___f_5360_; lean_object* v___y_5362_; lean_object* v_snd_5363_; lean_object* v___y_5364_; lean_object* v_pos_5365_; lean_object* v___y_5395_; lean_object* v_snd_5396_; lean_object* v_pos_5397_; lean_object* v_err_5398_; lean_object* v___y_5401_; lean_object* v___y_5402_; lean_object* v_snd_5403_; lean_object* v___f_5405_; lean_object* v___y_5407_; lean_object* v_snd_5408_; lean_object* v___y_5409_; lean_object* v_pos_5410_; lean_object* v___y_5439_; lean_object* v_snd_5440_; lean_object* v_pos_5441_; lean_object* v_err_5442_; lean_object* v___y_5445_; lean_object* v___y_5446_; lean_object* v_snd_5447_; lean_object* v___f_5449_; lean_object* v___y_5451_; lean_object* v_snd_5452_; lean_object* v___y_5453_; lean_object* v_pos_5454_; lean_object* v___y_5483_; lean_object* v_snd_5484_; lean_object* v_pos_5485_; lean_object* v_err_5486_; lean_object* v___y_5489_; lean_object* v___y_5490_; lean_object* v_snd_5491_; lean_object* v___f_5493_; lean_object* v___y_5495_; lean_object* v___y_5496_; lean_object* v___y_5497_; lean_object* v_pos_5498_; lean_object* v___y_5527_; lean_object* v___y_5528_; lean_object* v_pos_5529_; lean_object* v_err_5530_; lean_object* v___y_5533_; lean_object* v___y_5534_; lean_object* v___y_5535_; lean_object* v___f_5537_; lean_object* v_snd_5539_; lean_object* v___y_5540_; lean_object* v_pos_5541_; lean_object* v_snd_5571_; lean_object* v_pos_5572_; lean_object* v_err_5573_; lean_object* v___y_5576_; lean_object* v_snd_5577_; lean_object* v___f_5579_; lean_object* v_snd_5581_; lean_object* v___y_5582_; lean_object* v_pos_5583_; lean_object* v_snd_5612_; lean_object* v_pos_5613_; lean_object* v_err_5614_; lean_object* v___y_5617_; lean_object* v_snd_5618_; lean_object* v___f_5620_; lean_object* v_snd_5622_; lean_object* v___y_5623_; lean_object* v_pos_5624_; lean_object* v_snd_5653_; lean_object* v_pos_5654_; lean_object* v_err_5655_; lean_object* v___y_5658_; lean_object* v_snd_5659_; lean_object* v___f_5661_; lean_object* v_snd_5663_; lean_object* v___y_5664_; lean_object* v_pos_5665_; lean_object* v_snd_5695_; lean_object* v_pos_5696_; lean_object* v_err_5697_; lean_object* v___y_5700_; lean_object* v_snd_5701_; lean_object* v___f_5703_; lean_object* v_snd_5705_; lean_object* v___y_5706_; lean_object* v_pos_5707_; lean_object* v_snd_5736_; lean_object* v_pos_5737_; lean_object* v_err_5738_; lean_object* v___y_5741_; lean_object* v_snd_5742_; lean_object* v___f_5744_; lean_object* v_snd_5746_; lean_object* v___y_5747_; lean_object* v_pos_5748_; lean_object* v_snd_5777_; lean_object* v_pos_5778_; lean_object* v_err_5779_; lean_object* v___y_5782_; lean_object* v_snd_5783_; lean_object* v___f_5785_; lean_object* v___y_5787_; lean_object* v_pos_5788_; lean_object* v_pos_5817_; lean_object* v_err_5818_; lean_object* v___x_5820_; uint8_t v_decide_5821_; 
v_fst_4323_ = lean_ctor_get(v_a_4318_, 0);
v_snd_4324_ = lean_ctor_get(v_a_4318_, 1);
lean_inc(v_snd_4324_);
v___f_4325_ = ((lean_object*)(l_Std_Time_parseModifier___closed__0));
v___f_4373_ = ((lean_object*)(l_Std_Time_parseModifier___closed__2));
v___f_4414_ = ((lean_object*)(l_Std_Time_parseModifier___closed__4));
v___f_4455_ = ((lean_object*)(l_Std_Time_parseModifier___closed__6));
v___f_4496_ = ((lean_object*)(l_Std_Time_parseModifier___closed__8));
v___f_4537_ = ((lean_object*)(l_Std_Time_parseModifier___closed__10));
v___f_4618_ = ((lean_object*)(l_Std_Time_parseModifier___closed__13));
v___f_4658_ = ((lean_object*)(l_Std_Time_parseModifier___closed__15));
v___f_4698_ = ((lean_object*)(l_Std_Time_parseModifier___closed__17));
v___f_4738_ = ((lean_object*)(l_Std_Time_parseModifier___closed__19));
v___f_4779_ = ((lean_object*)(l_Std_Time_parseModifier___closed__21));
v___f_4823_ = ((lean_object*)(l_Std_Time_parseModifier___closed__23));
v___f_4867_ = ((lean_object*)(l_Std_Time_parseModifier___closed__25));
v___f_4911_ = ((lean_object*)(l_Std_Time_parseModifier___closed__27));
v___f_4955_ = ((lean_object*)(l_Std_Time_parseModifier___closed__29));
v___f_4999_ = ((lean_object*)(l_Std_Time_parseModifier___closed__31));
v___f_5172_ = ((lean_object*)(l_Std_Time_parseModifier___closed__36));
v___f_5219_ = ((lean_object*)(l_Std_Time_parseModifier___closed__38));
v___f_5266_ = ((lean_object*)(l_Std_Time_parseModifier___closed__40));
v___f_5313_ = ((lean_object*)(l_Std_Time_parseModifier___closed__42));
v___f_5360_ = ((lean_object*)(l_Std_Time_parseModifier___closed__44));
v___f_5405_ = ((lean_object*)(l_Std_Time_parseModifier___closed__47));
v___f_5449_ = ((lean_object*)(l_Std_Time_parseModifier___closed__49));
v___f_5493_ = ((lean_object*)(l_Std_Time_parseModifier___closed__51));
v___f_5537_ = ((lean_object*)(l_Std_Time_parseModifier___closed__53));
v___f_5579_ = ((lean_object*)(l_Std_Time_parseModifier___closed__56));
v___f_5620_ = ((lean_object*)(l_Std_Time_parseModifier___closed__58));
v___f_5661_ = ((lean_object*)(l_Std_Time_parseModifier___closed__60));
v___f_5703_ = ((lean_object*)(l_Std_Time_parseModifier___closed__63));
v___f_5744_ = ((lean_object*)(l_Std_Time_parseModifier___closed__65));
v___f_5785_ = ((lean_object*)(l_Std_Time_parseModifier___closed__67));
v___x_5820_ = lean_string_utf8_byte_size(v_fst_4323_);
v_decide_5821_ = lean_nat_dec_eq(v_snd_4324_, v___x_5820_);
if (v_decide_5821_ == 0)
{
uint32_t v___x_5822_; uint32_t v_c_5823_; uint8_t v___x_5824_; 
v___x_5822_ = 71;
v_c_5823_ = lean_string_utf8_get_fast(v_fst_4323_, v_snd_4324_);
v___x_5824_ = lean_uint32_dec_eq(v_c_5823_, v___x_5822_);
if (v___x_5824_ == 0)
{
lean_object* v___x_5825_; 
v___x_5825_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1));
v_pos_5817_ = v_a_4318_;
v_err_5818_ = v___x_5825_;
goto v___jp_5816_;
}
else
{
lean_object* v___x_5827_; uint8_t v_isShared_5828_; uint8_t v_isSharedCheck_5842_; 
lean_inc(v_fst_4323_);
v_isSharedCheck_5842_ = !lean_is_exclusive(v_a_4318_);
if (v_isSharedCheck_5842_ == 0)
{
lean_object* v_unused_5843_; lean_object* v_unused_5844_; 
v_unused_5843_ = lean_ctor_get(v_a_4318_, 1);
lean_dec(v_unused_5843_);
v_unused_5844_ = lean_ctor_get(v_a_4318_, 0);
lean_dec(v_unused_5844_);
v___x_5827_ = v_a_4318_;
v_isShared_5828_ = v_isSharedCheck_5842_;
goto v_resetjp_5826_;
}
else
{
lean_dec(v_a_4318_);
v___x_5827_ = lean_box(0);
v_isShared_5828_ = v_isSharedCheck_5842_;
goto v_resetjp_5826_;
}
v_resetjp_5826_:
{
lean_object* v___x_5829_; lean_object* v_it_x27_5831_; 
v___x_5829_ = lean_string_utf8_next_fast(v_fst_4323_, v_snd_4324_);
if (v_isShared_5828_ == 0)
{
lean_ctor_set(v___x_5827_, 1, v___x_5829_);
v_it_x27_5831_ = v___x_5827_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v_fst_4323_);
lean_ctor_set(v_reuseFailAlloc_5841_, 1, v___x_5829_);
v_it_x27_5831_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5830_;
}
v_reusejp_5830_:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5832_ = ((lean_object*)(l_Std_Time_parseModifier___closed__69));
v___x_5833_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(v___x_5832_, v_it_x27_5831_);
if (lean_obj_tag(v___x_5833_) == 0)
{
lean_object* v_pos_5834_; lean_object* v_res_5835_; lean_object* v___f_5836_; lean_object* v___x_5837_; 
v_pos_5834_ = lean_ctor_get(v___x_5833_, 0);
lean_inc(v_pos_5834_);
v_res_5835_ = lean_ctor_get(v___x_5833_, 1);
lean_inc(v_res_5835_);
lean_dec_ref_known(v___x_5833_, 2);
v___f_5836_ = ((lean_object*)(l_Std_Time_parseModifier___closed__70));
v___x_5837_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_5836_, v_res_5835_, v_pos_5834_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_dec(v_snd_4324_);
return v___x_5837_;
}
else
{
lean_object* v_pos_5838_; 
v_pos_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc(v_pos_5838_);
v___y_5787_ = v___x_5837_;
v_pos_5788_ = v_pos_5838_;
goto v___jp_5786_;
}
}
else
{
lean_object* v_pos_5839_; lean_object* v_err_5840_; 
v_pos_5839_ = lean_ctor_get(v___x_5833_, 0);
lean_inc(v_pos_5839_);
v_err_5840_ = lean_ctor_get(v___x_5833_, 1);
lean_inc(v_err_5840_);
lean_dec_ref_known(v___x_5833_, 2);
v_pos_5817_ = v_pos_5839_;
v_err_5818_ = v_err_5840_;
goto v___jp_5816_;
}
}
}
}
}
else
{
lean_object* v___x_5845_; 
v___x_5845_ = lean_box(0);
v_pos_5817_ = v_a_4318_;
v_err_5818_ = v___x_5845_;
goto v___jp_5816_;
}
v___jp_4319_:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = lean_box(0);
v___x_4322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___y_4320_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
return v___x_4322_;
}
v___jp_4326_:
{
lean_object* v_fst_4330_; lean_object* v_snd_4331_; uint8_t v_decide_4332_; 
v_fst_4330_ = lean_ctor_get(v_pos_4329_, 0);
v_snd_4331_ = lean_ctor_get(v_pos_4329_, 1);
v_decide_4332_ = lean_nat_dec_eq(v_snd_4327_, v_snd_4331_);
lean_dec(v_snd_4327_);
if (v_decide_4332_ == 0)
{
lean_dec_ref(v_pos_4329_);
return v___y_4328_;
}
else
{
lean_object* v___x_4333_; uint8_t v_decide_4334_; 
lean_dec_ref(v___y_4328_);
v___x_4333_ = lean_string_utf8_byte_size(v_fst_4330_);
v_decide_4334_ = lean_nat_dec_eq(v_snd_4331_, v___x_4333_);
if (v_decide_4334_ == 0)
{
if (v_decide_4332_ == 0)
{
v___y_4320_ = v_pos_4329_;
goto v___jp_4319_;
}
else
{
uint32_t v___x_4335_; uint32_t v_c_4336_; uint8_t v___x_4337_; 
v___x_4335_ = 90;
v_c_4336_ = lean_string_utf8_get_fast(v_fst_4330_, v_snd_4331_);
v___x_4337_ = lean_uint32_dec_eq(v_c_4336_, v___x_4335_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4338_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1));
v___x_4339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4339_, 0, v_pos_4329_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
return v___x_4339_;
}
else
{
lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4361_; 
lean_inc(v_snd_4331_);
lean_inc(v_fst_4330_);
v_isSharedCheck_4361_ = !lean_is_exclusive(v_pos_4329_);
if (v_isSharedCheck_4361_ == 0)
{
lean_object* v_unused_4362_; lean_object* v_unused_4363_; 
v_unused_4362_ = lean_ctor_get(v_pos_4329_, 1);
lean_dec(v_unused_4362_);
v_unused_4363_ = lean_ctor_get(v_pos_4329_, 0);
lean_dec(v_unused_4363_);
v___x_4341_ = v_pos_4329_;
v_isShared_4342_ = v_isSharedCheck_4361_;
goto v_resetjp_4340_;
}
else
{
lean_dec(v_pos_4329_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4361_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4343_; lean_object* v_it_x27_4345_; 
v___x_4343_ = lean_string_utf8_next_fast(v_fst_4330_, v_snd_4331_);
lean_dec(v_snd_4331_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 1, v___x_4343_);
v_it_x27_4345_ = v___x_4341_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_fst_4330_);
lean_ctor_set(v_reuseFailAlloc_4360_, 1, v___x_4343_);
v_it_x27_4345_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4346_ = ((lean_object*)(l_Std_Time_parseModifier___closed__1));
v___x_4347_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(v___x_4346_, v_it_x27_4345_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_pos_4348_; lean_object* v_res_4349_; lean_object* v___x_4350_; 
v_pos_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_pos_4348_);
v_res_4349_ = lean_ctor_get(v___x_4347_, 1);
lean_inc(v_res_4349_);
lean_dec_ref_known(v___x_4347_, 2);
v___x_4350_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(v___f_4325_, v_res_4349_, v_pos_4348_);
return v___x_4350_;
}
else
{
lean_object* v_pos_4351_; lean_object* v_err_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
v_pos_4351_ = lean_ctor_get(v___x_4347_, 0);
v_err_4352_ = lean_ctor_get(v___x_4347_, 1);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4347_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_err_4352_);
lean_inc(v_pos_4351_);
lean_dec(v___x_4347_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_pos_4351_);
lean_ctor_set(v_reuseFailAlloc_4358_, 1, v_err_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
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
v___y_4320_ = v_pos_4329_;
goto v___jp_4319_;
}
}
}
v___jp_4364_:
{
lean_object* v___x_4368_; 
lean_inc_ref(v_pos_4366_);
v___x_4368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4368_, 0, v_pos_4366_);
lean_ctor_set(v___x_4368_, 1, v_err_4367_);
v_snd_4327_ = v_snd_4365_;
v___y_4328_ = v___x_4368_;
v_pos_4329_ = v_pos_4366_;
goto v___jp_4326_;
}
v___jp_4369_:
{
lean_object* v___x_4372_; 
v___x_4372_ = lean_box(0);
v_snd_4365_ = v_snd_4371_;
v_pos_4366_ = v___y_4370_;
v_err_4367_ = v___x_4372_;
goto v___jp_4364_;
}
v___jp_4374_:
{
lean_object* v_fst_4378_; lean_object* v_snd_4379_; uint8_t v_decide_4380_; 
v_fst_4378_ = lean_ctor_get(v_pos_4377_, 0);
v_snd_4379_ = lean_ctor_get(v_pos_4377_, 1);
lean_inc(v_snd_4379_);
v_decide_4380_ = lean_nat_dec_eq(v_snd_4375_, v_snd_4379_);
lean_dec(v_snd_4375_);
if (v_decide_4380_ == 0)
{
lean_dec(v_snd_4379_);
lean_dec_ref(v_pos_4377_);
return v___y_4376_;
}
else
{
lean_object* v___x_4381_; uint8_t v_decide_4382_; 
lean_dec_ref(v___y_4376_);
v___x_4381_ = lean_string_utf8_byte_size(v_fst_4378_);
v_decide_4382_ = lean_nat_dec_eq(v_snd_4379_, v___x_4381_);
if (v_decide_4382_ == 0)
{
if (v_decide_4380_ == 0)
{
v___y_4370_ = v_pos_4377_;
v_snd_4371_ = v_snd_4379_;
goto v___jp_4369_;
}
else
{
uint32_t v___x_4383_; uint32_t v_c_4384_; uint8_t v___x_4385_; 
v___x_4383_ = 120;
v_c_4384_ = lean_string_utf8_get_fast(v_fst_4378_, v_snd_4379_);
v___x_4385_ = lean_uint32_dec_eq(v_c_4384_, v___x_4383_);
if (v___x_4385_ == 0)
{
lean_object* v___x_4386_; 
v___x_4386_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1));
v_snd_4365_ = v_snd_4379_;
v_pos_4366_ = v_pos_4377_;
v_err_4367_ = v___x_4386_;
goto v___jp_4364_;
}
else
{
lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4402_; 
lean_inc(v_fst_4378_);
v_isSharedCheck_4402_ = !lean_is_exclusive(v_pos_4377_);
if (v_isSharedCheck_4402_ == 0)
{
lean_object* v_unused_4403_; lean_object* v_unused_4404_; 
v_unused_4403_ = lean_ctor_get(v_pos_4377_, 1);
lean_dec(v_unused_4403_);
v_unused_4404_ = lean_ctor_get(v_pos_4377_, 0);
lean_dec(v_unused_4404_);
v___x_4388_ = v_pos_4377_;
v_isShared_4389_ = v_isSharedCheck_4402_;
goto v_resetjp_4387_;
}
else
{
lean_dec(v_pos_4377_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4402_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4390_; lean_object* v_it_x27_4392_; 
v___x_4390_ = lean_string_utf8_next_fast(v_fst_4378_, v_snd_4379_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 1, v___x_4390_);
v_it_x27_4392_ = v___x_4388_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_fst_4378_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v___x_4390_);
v_it_x27_4392_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = ((lean_object*)(l_Std_Time_parseModifier___closed__3));
v___x_4394_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(v___x_4393_, v_it_x27_4392_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_pos_4395_; lean_object* v_res_4396_; lean_object* v___x_4397_; 
v_pos_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_pos_4395_);
v_res_4396_ = lean_ctor_get(v___x_4394_, 1);
lean_inc(v_res_4396_);
lean_dec_ref_known(v___x_4394_, 2);
v___x_4397_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4373_, v_res_4396_, v_pos_4395_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_dec(v_snd_4379_);
return v___x_4397_;
}
else
{
lean_object* v_pos_4398_; 
v_pos_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_pos_4398_);
v_snd_4327_ = v_snd_4379_;
v___y_4328_ = v___x_4397_;
v_pos_4329_ = v_pos_4398_;
goto v___jp_4326_;
}
}
else
{
lean_object* v_pos_4399_; lean_object* v_err_4400_; 
v_pos_4399_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_pos_4399_);
v_err_4400_ = lean_ctor_get(v___x_4394_, 1);
lean_inc(v_err_4400_);
lean_dec_ref_known(v___x_4394_, 2);
v_snd_4365_ = v_snd_4379_;
v_pos_4366_ = v_pos_4399_;
v_err_4367_ = v_err_4400_;
goto v___jp_4364_;
}
}
}
}
}
}
else
{
v___y_4370_ = v_pos_4377_;
v_snd_4371_ = v_snd_4379_;
goto v___jp_4369_;
}
}
}
v___jp_4405_:
{
lean_object* v___x_4409_; 
lean_inc_ref(v_pos_4407_);
v___x_4409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4409_, 0, v_pos_4407_);
lean_ctor_set(v___x_4409_, 1, v_err_4408_);
v_snd_4375_ = v_snd_4406_;
v___y_4376_ = v___x_4409_;
v_pos_4377_ = v_pos_4407_;
goto v___jp_4374_;
}
v___jp_4410_:
{
lean_object* v___x_4413_; 
v___x_4413_ = lean_box(0);
v_snd_4406_ = v_snd_4412_;
v_pos_4407_ = v___y_4411_;
v_err_4408_ = v___x_4413_;
goto v___jp_4405_;
}
v___jp_4415_:
{
lean_object* v_fst_4419_; lean_object* v_snd_4420_; uint8_t v_decide_4421_; 
v_fst_4419_ = lean_ctor_get(v_pos_4418_, 0);
v_snd_4420_ = lean_ctor_get(v_pos_4418_, 1);
lean_inc(v_snd_4420_);
v_decide_4421_ = lean_nat_dec_eq(v_snd_4416_, v_snd_4420_);
lean_dec(v_snd_4416_);
if (v_decide_4421_ == 0)
{
lean_dec(v_snd_4420_);
lean_dec_ref(v_pos_4418_);
return v___y_4417_;
}
else
{
lean_object* v___x_4422_; uint8_t v_decide_4423_; 
lean_dec_ref(v___y_4417_);
v___x_4422_ = lean_string_utf8_byte_size(v_fst_4419_);
v_decide_4423_ = lean_nat_dec_eq(v_snd_4420_, v___x_4422_);
if (v_decide_4423_ == 0)
{
if (v_decide_4421_ == 0)
{
v___y_4411_ = v_pos_4418_;
v_snd_4412_ = v_snd_4420_;
goto v___jp_4410_;
}
else
{
uint32_t v___x_4424_; uint32_t v_c_4425_; uint8_t v___x_4426_; 
v___x_4424_ = 88;
v_c_4425_ = lean_string_utf8_get_fast(v_fst_4419_, v_snd_4420_);
v___x_4426_ = lean_uint32_dec_eq(v_c_4425_, v___x_4424_);
if (v___x_4426_ == 0)
{
lean_object* v___x_4427_; 
v___x_4427_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1));
v_snd_4406_ = v_snd_4420_;
v_pos_4407_ = v_pos_4418_;
v_err_4408_ = v___x_4427_;
goto v___jp_4405_;
}
else
{
lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4443_; 
lean_inc(v_fst_4419_);
v_isSharedCheck_4443_ = !lean_is_exclusive(v_pos_4418_);
if (v_isSharedCheck_4443_ == 0)
{
lean_object* v_unused_4444_; lean_object* v_unused_4445_; 
v_unused_4444_ = lean_ctor_get(v_pos_4418_, 1);
lean_dec(v_unused_4444_);
v_unused_4445_ = lean_ctor_get(v_pos_4418_, 0);
lean_dec(v_unused_4445_);
v___x_4429_ = v_pos_4418_;
v_isShared_4430_ = v_isSharedCheck_4443_;
goto v_resetjp_4428_;
}
else
{
lean_dec(v_pos_4418_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4443_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4431_; lean_object* v_it_x27_4433_; 
v___x_4431_ = lean_string_utf8_next_fast(v_fst_4419_, v_snd_4420_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 1, v___x_4431_);
v_it_x27_4433_ = v___x_4429_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_fst_4419_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v___x_4431_);
v_it_x27_4433_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4434_ = ((lean_object*)(l_Std_Time_parseModifier___closed__5));
v___x_4435_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(v___x_4434_, v_it_x27_4433_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_pos_4436_; lean_object* v_res_4437_; lean_object* v___x_4438_; 
v_pos_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_pos_4436_);
v_res_4437_ = lean_ctor_get(v___x_4435_, 1);
lean_inc(v_res_4437_);
lean_dec_ref_known(v___x_4435_, 2);
v___x_4438_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4414_, v_res_4437_, v_pos_4436_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_dec(v_snd_4420_);
return v___x_4438_;
}
else
{
lean_object* v_pos_4439_; 
v_pos_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_pos_4439_);
v_snd_4375_ = v_snd_4420_;
v___y_4376_ = v___x_4438_;
v_pos_4377_ = v_pos_4439_;
goto v___jp_4374_;
}
}
else
{
lean_object* v_pos_4440_; lean_object* v_err_4441_; 
v_pos_4440_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_pos_4440_);
v_err_4441_ = lean_ctor_get(v___x_4435_, 1);
lean_inc(v_err_4441_);
lean_dec_ref_known(v___x_4435_, 2);
v_snd_4406_ = v_snd_4420_;
v_pos_4407_ = v_pos_4440_;
v_err_4408_ = v_err_4441_;
goto v___jp_4405_;
}
}
}
}
}
}
else
{
v___y_4411_ = v_pos_4418_;
v_snd_4412_ = v_snd_4420_;
goto v___jp_4410_;
}
}
}
v___jp_4446_:
{
lean_object* v___x_4450_; 
lean_inc_ref(v_pos_4448_);
v___x_4450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4450_, 0, v_pos_4448_);
lean_ctor_set(v___x_4450_, 1, v_err_4449_);
v_snd_4416_ = v_snd_4447_;
v___y_4417_ = v___x_4450_;
v_pos_4418_ = v_pos_4448_;
goto v___jp_4415_;
}
v___jp_4451_:
{
lean_object* v___x_4454_; 
v___x_4454_ = lean_box(0);
v_snd_4447_ = v_snd_4453_;
v_pos_4448_ = v___y_4452_;
v_err_4449_ = v___x_4454_;
goto v___jp_4446_;
}
v___jp_4456_:
{
lean_object* v_fst_4460_; lean_object* v_snd_4461_; uint8_t v_decide_4462_; 
v_fst_4460_ = lean_ctor_get(v_pos_4459_, 0);
v_snd_4461_ = lean_ctor_get(v_pos_4459_, 1);
lean_inc(v_snd_4461_);
v_decide_4462_ = lean_nat_dec_eq(v_snd_4457_, v_snd_4461_);
lean_dec(v_snd_4457_);
if (v_decide_4462_ == 0)
{
lean_dec(v_snd_4461_);
lean_dec_ref(v_pos_4459_);
return v___y_4458_;
}
else
{
lean_object* v___x_4463_; uint8_t v_decide_4464_; 
lean_dec_ref(v___y_4458_);
v___x_4463_ = lean_string_utf8_byte_size(v_fst_4460_);
v_decide_4464_ = lean_nat_dec_eq(v_snd_4461_, v___x_4463_);
if (v_decide_4464_ == 0)
{
if (v_decide_4462_ == 0)
{
v___y_4452_ = v_pos_4459_;
v_snd_4453_ = v_snd_4461_;
goto v___jp_4451_;
}
else
{
uint32_t v___x_4465_; uint32_t v_c_4466_; uint8_t v___x_4467_; 
v___x_4465_ = 79;
v_c_4466_ = lean_string_utf8_get_fast(v_fst_4460_, v_snd_4461_);
v___x_4467_ = lean_uint32_dec_eq(v_c_4466_, v___x_4465_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; 
v___x_4468_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1));
v_snd_4447_ = v_snd_4461_;
v_pos_4448_ = v_pos_4459_;
v_err_4449_ = v___x_4468_;
goto v___jp_4446_;
}
else
{
lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4484_; 
lean_inc(v_fst_4460_);
v_isSharedCheck_4484_ = !lean_is_exclusive(v_pos_4459_);
if (v_isSharedCheck_4484_ == 0)
{
lean_object* v_unused_4485_; lean_object* v_unused_4486_; 
v_unused_4485_ = lean_ctor_get(v_pos_4459_, 1);
lean_dec(v_unused_4485_);
v_unused_4486_ = lean_ctor_get(v_pos_4459_, 0);
lean_dec(v_unused_4486_);
v___x_4470_ = v_pos_4459_;
v_isShared_4471_ = v_isSharedCheck_4484_;
goto v_resetjp_4469_;
}
else
{
lean_dec(v_pos_4459_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4484_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4472_; lean_object* v_it_x27_4474_; 
v___x_4472_ = lean_string_utf8_next_fast(v_fst_4460_, v_snd_4461_);
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 1, v___x_4472_);
v_it_x27_4474_ = v___x_4470_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_fst_4460_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v___x_4472_);
v_it_x27_4474_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = ((lean_object*)(l_Std_Time_parseModifier___closed__7));
v___x_4476_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(v___x_4475_, v_it_x27_4474_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_pos_4477_; lean_object* v_res_4478_; lean_object* v___x_4479_; 
v_pos_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_pos_4477_);
v_res_4478_ = lean_ctor_get(v___x_4476_, 1);
lean_inc(v_res_4478_);
lean_dec_ref_known(v___x_4476_, 2);
v___x_4479_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(v___f_4455_, v_res_4478_, v_pos_4477_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_dec(v_snd_4461_);
return v___x_4479_;
}
else
{
lean_object* v_pos_4480_; 
v_pos_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_pos_4480_);
v_snd_4416_ = v_snd_4461_;
v___y_4417_ = v___x_4479_;
v_pos_4418_ = v_pos_4480_;
goto v___jp_4415_;
}
}
else
{
lean_object* v_pos_4481_; lean_object* v_err_4482_; 
v_pos_4481_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_pos_4481_);
v_err_4482_ = lean_ctor_get(v___x_4476_, 1);
lean_inc(v_err_4482_);
lean_dec_ref_known(v___x_4476_, 2);
v_snd_4447_ = v_snd_4461_;
v_pos_4448_ = v_pos_4481_;
v_err_4449_ = v_err_4482_;
goto v___jp_4446_;
}
}
}
}
}
}
else
{
v___y_4452_ = v_pos_4459_;
v_snd_4453_ = v_snd_4461_;
goto v___jp_4451_;
}
}
}
v___jp_4487_:
{
lean_object* v___x_4491_; 
lean_inc_ref(v_pos_4489_);
v___x_4491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4491_, 0, v_pos_4489_);
lean_ctor_set(v___x_4491_, 1, v_err_4490_);
v_snd_4457_ = v_snd_4488_;
v___y_4458_ = v___x_4491_;
v_pos_4459_ = v_pos_4489_;
goto v___jp_4456_;
}
v___jp_4492_:
{
lean_object* v___x_4495_; 
v___x_4495_ = lean_box(0);
v_snd_4488_ = v_snd_4494_;
v_pos_4489_ = v___y_4493_;
v_err_4490_ = v___x_4495_;
goto v___jp_4487_;
}
v___jp_4497_:
{
lean_object* v_fst_4501_; lean_object* v_snd_4502_; uint8_t v_decide_4503_; 
v_fst_4501_ = lean_ctor_get(v_pos_4500_, 0);
v_snd_4502_ = lean_ctor_get(v_pos_4500_, 1);
lean_inc(v_snd_4502_);
v_decide_4503_ = lean_nat_dec_eq(v_snd_4498_, v_snd_4502_);
lean_dec(v_snd_4498_);
if (v_decide_4503_ == 0)
{
lean_dec(v_snd_4502_);
lean_dec_ref(v_pos_4500_);
return v___y_4499_;
}
else
{
lean_object* v___x_4504_; uint8_t v_decide_4505_; 
lean_dec_ref(v___y_4499_);
v___x_4504_ = lean_string_utf8_byte_size(v_fst_4501_);
v_decide_4505_ = lean_nat_dec_eq(v_snd_4502_, v___x_4504_);
if (v_decide_4505_ == 0)
{
if (v_decide_4503_ == 0)
{
v___y_4493_ = v_pos_4500_;
v_snd_4494_ = v_snd_4502_;
goto v___jp_4492_;
}
else
{
uint32_t v___x_4506_; uint32_t v_c_4507_; uint8_t v___x_4508_; 
v___x_4506_ = 118;
v_c_4507_ = lean_string_utf8_get_fast(v_fst_4501_, v_snd_4502_);
v___x_4508_ = lean_uint32_dec_eq(v_c_4507_, v___x_4506_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; 
v___x_4509_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1));
v_snd_4488_ = v_snd_4502_;
v_pos_4489_ = v_pos_4500_;
v_err_4490_ = v___x_4509_;
goto v___jp_4487_;
}
else
{
lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4525_; 
lean_inc(v_fst_4501_);
v_isSharedCheck_4525_ = !lean_is_exclusive(v_pos_4500_);
if (v_isSharedCheck_4525_ == 0)
{
lean_object* v_unused_4526_; lean_object* v_unused_4527_; 
v_unused_4526_ = lean_ctor_get(v_pos_4500_, 1);
lean_dec(v_unused_4526_);
v_unused_4527_ = lean_ctor_get(v_pos_4500_, 0);
lean_dec(v_unused_4527_);
v___x_4511_ = v_pos_4500_;
v_isShared_4512_ = v_isSharedCheck_4525_;
goto v_resetjp_4510_;
}
else
{
lean_dec(v_pos_4500_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4525_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4513_; lean_object* v_it_x27_4515_; 
v___x_4513_ = lean_string_utf8_next_fast(v_fst_4501_, v_snd_4502_);
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 1, v___x_4513_);
v_it_x27_4515_ = v___x_4511_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_fst_4501_);
lean_ctor_set(v_reuseFailAlloc_4524_, 1, v___x_4513_);
v_it_x27_4515_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = ((lean_object*)(l_Std_Time_parseModifier___closed__9));
v___x_4517_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(v___x_4516_, v_it_x27_4515_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_pos_4518_; lean_object* v_res_4519_; lean_object* v___x_4520_; 
v_pos_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_pos_4518_);
v_res_4519_ = lean_ctor_get(v___x_4517_, 1);
lean_inc(v_res_4519_);
lean_dec_ref_known(v___x_4517_, 2);
v___x_4520_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4496_, v_res_4519_, v_pos_4518_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_dec(v_snd_4502_);
return v___x_4520_;
}
else
{
lean_object* v_pos_4521_; 
v_pos_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_pos_4521_);
v_snd_4457_ = v_snd_4502_;
v___y_4458_ = v___x_4520_;
v_pos_4459_ = v_pos_4521_;
goto v___jp_4456_;
}
}
else
{
lean_object* v_pos_4522_; lean_object* v_err_4523_; 
v_pos_4522_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_pos_4522_);
v_err_4523_ = lean_ctor_get(v___x_4517_, 1);
lean_inc(v_err_4523_);
lean_dec_ref_known(v___x_4517_, 2);
v_snd_4488_ = v_snd_4502_;
v_pos_4489_ = v_pos_4522_;
v_err_4490_ = v_err_4523_;
goto v___jp_4487_;
}
}
}
}
}
}
else
{
v___y_4493_ = v_pos_4500_;
v_snd_4494_ = v_snd_4502_;
goto v___jp_4492_;
}
}
}
v___jp_4528_:
{
lean_object* v___x_4532_; 
lean_inc_ref(v_pos_4530_);
v___x_4532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4532_, 0, v_pos_4530_);
lean_ctor_set(v___x_4532_, 1, v_err_4531_);
v_snd_4498_ = v_snd_4529_;
v___y_4499_ = v___x_4532_;
v_pos_4500_ = v_pos_4530_;
goto v___jp_4497_;
}
v___jp_4533_:
{
lean_object* v___x_4536_; 
v___x_4536_ = lean_box(0);
v_snd_4529_ = v_snd_4535_;
v_pos_4530_ = v___y_4534_;
v_err_4531_ = v___x_4536_;
goto v___jp_4528_;
}
v___jp_4538_:
{
lean_object* v_fst_4542_; lean_object* v_snd_4543_; uint8_t v_decide_4544_; 
v_fst_4542_ = lean_ctor_get(v_pos_4541_, 0);
v_snd_4543_ = lean_ctor_get(v_pos_4541_, 1);
lean_inc(v_snd_4543_);
v_decide_4544_ = lean_nat_dec_eq(v_snd_4539_, v_snd_4543_);
lean_dec(v_snd_4539_);
if (v_decide_4544_ == 0)
{
lean_dec(v_snd_4543_);
lean_dec_ref(v_pos_4541_);
return v___y_4540_;
}
else
{
lean_object* v___x_4545_; uint8_t v_decide_4546_; 
lean_dec_ref(v___y_4540_);
v___x_4545_ = lean_string_utf8_byte_size(v_fst_4542_);
v_decide_4546_ = lean_nat_dec_eq(v_snd_4543_, v___x_4545_);
if (v_decide_4546_ == 0)
{
if (v_decide_4544_ == 0)
{
v___y_4534_ = v_pos_4541_;
v_snd_4535_ = v_snd_4543_;
goto v___jp_4533_;
}
else
{
uint32_t v___x_4547_; uint32_t v_c_4548_; uint8_t v___x_4549_; 
v___x_4547_ = 122;
v_c_4548_ = lean_string_utf8_get_fast(v_fst_4542_, v_snd_4543_);
v___x_4549_ = lean_uint32_dec_eq(v_c_4548_, v___x_4547_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4550_; 
v___x_4550_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1));
v_snd_4529_ = v_snd_4543_;
v_pos_4530_ = v_pos_4541_;
v_err_4531_ = v___x_4550_;
goto v___jp_4528_;
}
else
{
lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4566_; 
lean_inc(v_fst_4542_);
v_isSharedCheck_4566_ = !lean_is_exclusive(v_pos_4541_);
if (v_isSharedCheck_4566_ == 0)
{
lean_object* v_unused_4567_; lean_object* v_unused_4568_; 
v_unused_4567_ = lean_ctor_get(v_pos_4541_, 1);
lean_dec(v_unused_4567_);
v_unused_4568_ = lean_ctor_get(v_pos_4541_, 0);
lean_dec(v_unused_4568_);
v___x_4552_ = v_pos_4541_;
v_isShared_4553_ = v_isSharedCheck_4566_;
goto v_resetjp_4551_;
}
else
{
lean_dec(v_pos_4541_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4566_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v_it_x27_4556_; 
v___x_4554_ = lean_string_utf8_next_fast(v_fst_4542_, v_snd_4543_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 1, v___x_4554_);
v_it_x27_4556_ = v___x_4552_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_fst_4542_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v___x_4554_);
v_it_x27_4556_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4557_ = ((lean_object*)(l_Std_Time_parseModifier___closed__11));
v___x_4558_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(v___x_4557_, v_it_x27_4556_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_pos_4559_; lean_object* v_res_4560_; lean_object* v___x_4561_; 
v_pos_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_pos_4559_);
v_res_4560_ = lean_ctor_get(v___x_4558_, 1);
lean_inc(v_res_4560_);
lean_dec_ref_known(v___x_4558_, 2);
v___x_4561_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4537_, v_res_4560_, v_pos_4559_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_dec(v_snd_4543_);
return v___x_4561_;
}
else
{
lean_object* v_pos_4562_; 
v_pos_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_pos_4562_);
v_snd_4498_ = v_snd_4543_;
v___y_4499_ = v___x_4561_;
v_pos_4500_ = v_pos_4562_;
goto v___jp_4497_;
}
}
else
{
lean_object* v_pos_4563_; lean_object* v_err_4564_; 
v_pos_4563_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_pos_4563_);
v_err_4564_ = lean_ctor_get(v___x_4558_, 1);
lean_inc(v_err_4564_);
lean_dec_ref_known(v___x_4558_, 2);
v_snd_4529_ = v_snd_4543_;
v_pos_4530_ = v_pos_4563_;
v_err_4531_ = v_err_4564_;
goto v___jp_4528_;
}
}
}
}
}
}
else
{
v___y_4534_ = v_pos_4541_;
v_snd_4535_ = v_snd_4543_;
goto v___jp_4533_;
}
}
}
v___jp_4569_:
{
lean_object* v___x_4573_; 
lean_inc_ref(v_pos_4571_);
v___x_4573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4573_, 0, v_pos_4571_);
lean_ctor_set(v___x_4573_, 1, v_err_4572_);
v_snd_4539_ = v_snd_4570_;
v___y_4540_ = v___x_4573_;
v_pos_4541_ = v_pos_4571_;
goto v___jp_4538_;
}
v___jp_4574_:
{
lean_object* v___x_4577_; 
v___x_4577_ = lean_box(0);
v_snd_4570_ = v_snd_4576_;
v_pos_4571_ = v___y_4575_;
v_err_4572_ = v___x_4577_;
goto v___jp_4569_;
}
v___jp_4578_:
{
lean_object* v_fst_4582_; lean_object* v_snd_4583_; uint8_t v_decide_4584_; 
v_fst_4582_ = lean_ctor_get(v_pos_4581_, 0);
v_snd_4583_ = lean_ctor_get(v_pos_4581_, 1);
lean_inc(v_snd_4583_);
v_decide_4584_ = lean_nat_dec_eq(v_snd_4579_, v_snd_4583_);
lean_dec(v_snd_4579_);
if (v_decide_4584_ == 0)
{
lean_dec(v_snd_4583_);
lean_dec_ref(v_pos_4581_);
return v___y_4580_;
}
else
{
lean_object* v___x_4585_; uint8_t v_decide_4586_; 
lean_dec_ref(v___y_4580_);
v___x_4585_ = lean_string_utf8_byte_size(v_fst_4582_);
v_decide_4586_ = lean_nat_dec_eq(v_snd_4583_, v___x_4585_);
if (v_decide_4586_ == 0)
{
if (v_decide_4584_ == 0)
{
v___y_4575_ = v_pos_4581_;
v_snd_4576_ = v_snd_4583_;
goto v___jp_4574_;
}
else
{
uint32_t v___x_4587_; uint32_t v_c_4588_; uint8_t v___x_4589_; 
v___x_4587_ = 86;
v_c_4588_ = lean_string_utf8_get_fast(v_fst_4582_, v_snd_4583_);
v___x_4589_ = lean_uint32_dec_eq(v_c_4588_, v___x_4587_);
if (v___x_4589_ == 0)
{
lean_object* v___x_4590_; 
v___x_4590_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1));
v_snd_4570_ = v_snd_4583_;
v_pos_4571_ = v_pos_4581_;
v_err_4572_ = v___x_4590_;
goto v___jp_4569_;
}
else
{
lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4606_; 
lean_inc(v_fst_4582_);
v_isSharedCheck_4606_ = !lean_is_exclusive(v_pos_4581_);
if (v_isSharedCheck_4606_ == 0)
{
lean_object* v_unused_4607_; lean_object* v_unused_4608_; 
v_unused_4607_ = lean_ctor_get(v_pos_4581_, 1);
lean_dec(v_unused_4607_);
v_unused_4608_ = lean_ctor_get(v_pos_4581_, 0);
lean_dec(v_unused_4608_);
v___x_4592_ = v_pos_4581_;
v_isShared_4593_ = v_isSharedCheck_4606_;
goto v_resetjp_4591_;
}
else
{
lean_dec(v_pos_4581_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4606_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4594_; lean_object* v_it_x27_4596_; 
v___x_4594_ = lean_string_utf8_next_fast(v_fst_4582_, v_snd_4583_);
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 1, v___x_4594_);
v_it_x27_4596_ = v___x_4592_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_fst_4582_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v___x_4594_);
v_it_x27_4596_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4597_ = ((lean_object*)(l_Std_Time_parseModifier___closed__12));
v___x_4598_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(v___x_4597_, v_it_x27_4596_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_pos_4599_; lean_object* v_res_4600_; lean_object* v___x_4601_; 
v_pos_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_pos_4599_);
v_res_4600_ = lean_ctor_get(v___x_4598_, 1);
lean_inc(v_res_4600_);
lean_dec_ref_known(v___x_4598_, 2);
v___x_4601_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(v_res_4600_, v_pos_4599_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_dec(v_snd_4583_);
return v___x_4601_;
}
else
{
lean_object* v_pos_4602_; 
v_pos_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_pos_4602_);
v_snd_4539_ = v_snd_4583_;
v___y_4540_ = v___x_4601_;
v_pos_4541_ = v_pos_4602_;
goto v___jp_4538_;
}
}
else
{
lean_object* v_pos_4603_; lean_object* v_err_4604_; 
v_pos_4603_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_pos_4603_);
v_err_4604_ = lean_ctor_get(v___x_4598_, 1);
lean_inc(v_err_4604_);
lean_dec_ref_known(v___x_4598_, 2);
v_snd_4570_ = v_snd_4583_;
v_pos_4571_ = v_pos_4603_;
v_err_4572_ = v_err_4604_;
goto v___jp_4569_;
}
}
}
}
}
}
else
{
v___y_4575_ = v_pos_4581_;
v_snd_4576_ = v_snd_4583_;
goto v___jp_4574_;
}
}
}
v___jp_4609_:
{
lean_object* v___x_4613_; 
lean_inc_ref(v_pos_4611_);
v___x_4613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4613_, 0, v_pos_4611_);
lean_ctor_set(v___x_4613_, 1, v_err_4612_);
v_snd_4579_ = v_snd_4610_;
v___y_4580_ = v___x_4613_;
v_pos_4581_ = v_pos_4611_;
goto v___jp_4578_;
}
v___jp_4614_:
{
lean_object* v___x_4617_; 
v___x_4617_ = lean_box(0);
v_snd_4610_ = v_snd_4616_;
v_pos_4611_ = v___y_4615_;
v_err_4612_ = v___x_4617_;
goto v___jp_4609_;
}
v___jp_4619_:
{
lean_object* v_fst_4623_; lean_object* v_snd_4624_; uint8_t v_decide_4625_; 
v_fst_4623_ = lean_ctor_get(v_pos_4622_, 0);
v_snd_4624_ = lean_ctor_get(v_pos_4622_, 1);
lean_inc(v_snd_4624_);
v_decide_4625_ = lean_nat_dec_eq(v_snd_4620_, v_snd_4624_);
lean_dec(v_snd_4620_);
if (v_decide_4625_ == 0)
{
lean_dec(v_snd_4624_);
lean_dec_ref(v_pos_4622_);
return v___y_4621_;
}
else
{
lean_object* v___x_4626_; uint8_t v_decide_4627_; 
lean_dec_ref(v___y_4621_);
v___x_4626_ = lean_string_utf8_byte_size(v_fst_4623_);
v_decide_4627_ = lean_nat_dec_eq(v_snd_4624_, v___x_4626_);
if (v_decide_4627_ == 0)
{
if (v_decide_4625_ == 0)
{
v___y_4615_ = v_pos_4622_;
v_snd_4616_ = v_snd_4624_;
goto v___jp_4614_;
}
else
{
uint32_t v___x_4628_; uint32_t v_c_4629_; uint8_t v___x_4630_; 
v___x_4628_ = 78;
v_c_4629_ = lean_string_utf8_get_fast(v_fst_4623_, v_snd_4624_);
v___x_4630_ = lean_uint32_dec_eq(v_c_4629_, v___x_4628_);
if (v___x_4630_ == 0)
{
lean_object* v___x_4631_; 
v___x_4631_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1));
v_snd_4610_ = v_snd_4624_;
v_pos_4611_ = v_pos_4622_;
v_err_4612_ = v___x_4631_;
goto v___jp_4609_;
}
else
{
lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4646_; 
lean_inc(v_fst_4623_);
v_isSharedCheck_4646_ = !lean_is_exclusive(v_pos_4622_);
if (v_isSharedCheck_4646_ == 0)
{
lean_object* v_unused_4647_; lean_object* v_unused_4648_; 
v_unused_4647_ = lean_ctor_get(v_pos_4622_, 1);
lean_dec(v_unused_4647_);
v_unused_4648_ = lean_ctor_get(v_pos_4622_, 0);
lean_dec(v_unused_4648_);
v___x_4633_ = v_pos_4622_;
v_isShared_4634_ = v_isSharedCheck_4646_;
goto v_resetjp_4632_;
}
else
{
lean_dec(v_pos_4622_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4646_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4635_; lean_object* v_it_x27_4637_; 
v___x_4635_ = lean_string_utf8_next_fast(v_fst_4623_, v_snd_4624_);
if (v_isShared_4634_ == 0)
{
lean_ctor_set(v___x_4633_, 1, v___x_4635_);
v_it_x27_4637_ = v___x_4633_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_fst_4623_);
lean_ctor_set(v_reuseFailAlloc_4645_, 1, v___x_4635_);
v_it_x27_4637_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = ((lean_object*)(l_Std_Time_parseModifier___closed__14));
v___x_4639_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(v___x_4638_, v_it_x27_4637_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v_pos_4640_; lean_object* v_res_4641_; lean_object* v___x_4642_; 
lean_dec(v_snd_4624_);
v_pos_4640_ = lean_ctor_get(v___x_4639_, 0);
lean_inc(v_pos_4640_);
v_res_4641_ = lean_ctor_get(v___x_4639_, 1);
lean_inc(v_res_4641_);
lean_dec_ref_known(v___x_4639_, 2);
v___x_4642_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4618_, v_res_4641_, v_pos_4640_);
lean_dec(v_res_4641_);
return v___x_4642_;
}
else
{
lean_object* v_pos_4643_; lean_object* v_err_4644_; 
v_pos_4643_ = lean_ctor_get(v___x_4639_, 0);
lean_inc(v_pos_4643_);
v_err_4644_ = lean_ctor_get(v___x_4639_, 1);
lean_inc(v_err_4644_);
lean_dec_ref_known(v___x_4639_, 2);
v_snd_4610_ = v_snd_4624_;
v_pos_4611_ = v_pos_4643_;
v_err_4612_ = v_err_4644_;
goto v___jp_4609_;
}
}
}
}
}
}
else
{
v___y_4615_ = v_pos_4622_;
v_snd_4616_ = v_snd_4624_;
goto v___jp_4614_;
}
}
}
v___jp_4649_:
{
lean_object* v___x_4653_; 
lean_inc_ref(v_pos_4651_);
v___x_4653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4653_, 0, v_pos_4651_);
lean_ctor_set(v___x_4653_, 1, v_err_4652_);
v_snd_4620_ = v_snd_4650_;
v___y_4621_ = v___x_4653_;
v_pos_4622_ = v_pos_4651_;
goto v___jp_4619_;
}
v___jp_4654_:
{
lean_object* v___x_4657_; 
v___x_4657_ = lean_box(0);
v_snd_4650_ = v_snd_4656_;
v_pos_4651_ = v___y_4655_;
v_err_4652_ = v___x_4657_;
goto v___jp_4649_;
}
v___jp_4659_:
{
lean_object* v_fst_4663_; lean_object* v_snd_4664_; uint8_t v_decide_4665_; 
v_fst_4663_ = lean_ctor_get(v_pos_4662_, 0);
v_snd_4664_ = lean_ctor_get(v_pos_4662_, 1);
lean_inc(v_snd_4664_);
v_decide_4665_ = lean_nat_dec_eq(v_snd_4660_, v_snd_4664_);
lean_dec(v_snd_4660_);
if (v_decide_4665_ == 0)
{
lean_dec(v_snd_4664_);
lean_dec_ref(v_pos_4662_);
return v___y_4661_;
}
else
{
lean_object* v___x_4666_; uint8_t v_decide_4667_; 
lean_dec_ref(v___y_4661_);
v___x_4666_ = lean_string_utf8_byte_size(v_fst_4663_);
v_decide_4667_ = lean_nat_dec_eq(v_snd_4664_, v___x_4666_);
if (v_decide_4667_ == 0)
{
if (v_decide_4665_ == 0)
{
v___y_4655_ = v_pos_4662_;
v_snd_4656_ = v_snd_4664_;
goto v___jp_4654_;
}
else
{
uint32_t v___x_4668_; uint32_t v_c_4669_; uint8_t v___x_4670_; 
v___x_4668_ = 110;
v_c_4669_ = lean_string_utf8_get_fast(v_fst_4663_, v_snd_4664_);
v___x_4670_ = lean_uint32_dec_eq(v_c_4669_, v___x_4668_);
if (v___x_4670_ == 0)
{
lean_object* v___x_4671_; 
v___x_4671_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1));
v_snd_4650_ = v_snd_4664_;
v_pos_4651_ = v_pos_4662_;
v_err_4652_ = v___x_4671_;
goto v___jp_4649_;
}
else
{
lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4686_; 
lean_inc(v_fst_4663_);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_pos_4662_);
if (v_isSharedCheck_4686_ == 0)
{
lean_object* v_unused_4687_; lean_object* v_unused_4688_; 
v_unused_4687_ = lean_ctor_get(v_pos_4662_, 1);
lean_dec(v_unused_4687_);
v_unused_4688_ = lean_ctor_get(v_pos_4662_, 0);
lean_dec(v_unused_4688_);
v___x_4673_ = v_pos_4662_;
v_isShared_4674_ = v_isSharedCheck_4686_;
goto v_resetjp_4672_;
}
else
{
lean_dec(v_pos_4662_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4686_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v_it_x27_4677_; 
v___x_4675_ = lean_string_utf8_next_fast(v_fst_4663_, v_snd_4664_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 1, v___x_4675_);
v_it_x27_4677_ = v___x_4673_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_fst_4663_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v___x_4675_);
v_it_x27_4677_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4678_ = ((lean_object*)(l_Std_Time_parseModifier___closed__16));
v___x_4679_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(v___x_4678_, v_it_x27_4677_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_pos_4680_; lean_object* v_res_4681_; lean_object* v___x_4682_; 
lean_dec(v_snd_4664_);
v_pos_4680_ = lean_ctor_get(v___x_4679_, 0);
lean_inc(v_pos_4680_);
v_res_4681_ = lean_ctor_get(v___x_4679_, 1);
lean_inc(v_res_4681_);
lean_dec_ref_known(v___x_4679_, 2);
v___x_4682_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4658_, v_res_4681_, v_pos_4680_);
lean_dec(v_res_4681_);
return v___x_4682_;
}
else
{
lean_object* v_pos_4683_; lean_object* v_err_4684_; 
v_pos_4683_ = lean_ctor_get(v___x_4679_, 0);
lean_inc(v_pos_4683_);
v_err_4684_ = lean_ctor_get(v___x_4679_, 1);
lean_inc(v_err_4684_);
lean_dec_ref_known(v___x_4679_, 2);
v_snd_4650_ = v_snd_4664_;
v_pos_4651_ = v_pos_4683_;
v_err_4652_ = v_err_4684_;
goto v___jp_4649_;
}
}
}
}
}
}
else
{
v___y_4655_ = v_pos_4662_;
v_snd_4656_ = v_snd_4664_;
goto v___jp_4654_;
}
}
}
v___jp_4689_:
{
lean_object* v___x_4693_; 
lean_inc_ref(v_pos_4691_);
v___x_4693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4693_, 0, v_pos_4691_);
lean_ctor_set(v___x_4693_, 1, v_err_4692_);
v_snd_4660_ = v_snd_4690_;
v___y_4661_ = v___x_4693_;
v_pos_4662_ = v_pos_4691_;
goto v___jp_4659_;
}
v___jp_4694_:
{
lean_object* v___x_4697_; 
v___x_4697_ = lean_box(0);
v_snd_4690_ = v_snd_4696_;
v_pos_4691_ = v___y_4695_;
v_err_4692_ = v___x_4697_;
goto v___jp_4689_;
}
v___jp_4699_:
{
lean_object* v_fst_4703_; lean_object* v_snd_4704_; uint8_t v_decide_4705_; 
v_fst_4703_ = lean_ctor_get(v_pos_4702_, 0);
v_snd_4704_ = lean_ctor_get(v_pos_4702_, 1);
lean_inc(v_snd_4704_);
v_decide_4705_ = lean_nat_dec_eq(v_snd_4700_, v_snd_4704_);
lean_dec(v_snd_4700_);
if (v_decide_4705_ == 0)
{
lean_dec(v_snd_4704_);
lean_dec_ref(v_pos_4702_);
return v___y_4701_;
}
else
{
lean_object* v___x_4706_; uint8_t v_decide_4707_; 
lean_dec_ref(v___y_4701_);
v___x_4706_ = lean_string_utf8_byte_size(v_fst_4703_);
v_decide_4707_ = lean_nat_dec_eq(v_snd_4704_, v___x_4706_);
if (v_decide_4707_ == 0)
{
if (v_decide_4705_ == 0)
{
v___y_4695_ = v_pos_4702_;
v_snd_4696_ = v_snd_4704_;
goto v___jp_4694_;
}
else
{
uint32_t v___x_4708_; uint32_t v_c_4709_; uint8_t v___x_4710_; 
v___x_4708_ = 65;
v_c_4709_ = lean_string_utf8_get_fast(v_fst_4703_, v_snd_4704_);
v___x_4710_ = lean_uint32_dec_eq(v_c_4709_, v___x_4708_);
if (v___x_4710_ == 0)
{
lean_object* v___x_4711_; 
v___x_4711_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1));
v_snd_4690_ = v_snd_4704_;
v_pos_4691_ = v_pos_4702_;
v_err_4692_ = v___x_4711_;
goto v___jp_4689_;
}
else
{
lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4726_; 
lean_inc(v_fst_4703_);
v_isSharedCheck_4726_ = !lean_is_exclusive(v_pos_4702_);
if (v_isSharedCheck_4726_ == 0)
{
lean_object* v_unused_4727_; lean_object* v_unused_4728_; 
v_unused_4727_ = lean_ctor_get(v_pos_4702_, 1);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v_pos_4702_, 0);
lean_dec(v_unused_4728_);
v___x_4713_ = v_pos_4702_;
v_isShared_4714_ = v_isSharedCheck_4726_;
goto v_resetjp_4712_;
}
else
{
lean_dec(v_pos_4702_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4726_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4715_; lean_object* v_it_x27_4717_; 
v___x_4715_ = lean_string_utf8_next_fast(v_fst_4703_, v_snd_4704_);
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 1, v___x_4715_);
v_it_x27_4717_ = v___x_4713_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_fst_4703_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v___x_4715_);
v_it_x27_4717_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4718_ = ((lean_object*)(l_Std_Time_parseModifier___closed__18));
v___x_4719_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(v___x_4718_, v_it_x27_4717_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_pos_4720_; lean_object* v_res_4721_; lean_object* v___x_4722_; 
lean_dec(v_snd_4704_);
v_pos_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_pos_4720_);
v_res_4721_ = lean_ctor_get(v___x_4719_, 1);
lean_inc(v_res_4721_);
lean_dec_ref_known(v___x_4719_, 2);
v___x_4722_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4698_, v_res_4721_, v_pos_4720_);
lean_dec(v_res_4721_);
return v___x_4722_;
}
else
{
lean_object* v_pos_4723_; lean_object* v_err_4724_; 
v_pos_4723_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_pos_4723_);
v_err_4724_ = lean_ctor_get(v___x_4719_, 1);
lean_inc(v_err_4724_);
lean_dec_ref_known(v___x_4719_, 2);
v_snd_4690_ = v_snd_4704_;
v_pos_4691_ = v_pos_4723_;
v_err_4692_ = v_err_4724_;
goto v___jp_4689_;
}
}
}
}
}
}
else
{
v___y_4695_ = v_pos_4702_;
v_snd_4696_ = v_snd_4704_;
goto v___jp_4694_;
}
}
}
v___jp_4729_:
{
lean_object* v___x_4733_; 
lean_inc_ref(v_pos_4731_);
v___x_4733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4733_, 0, v_pos_4731_);
lean_ctor_set(v___x_4733_, 1, v_err_4732_);
v_snd_4700_ = v_snd_4730_;
v___y_4701_ = v___x_4733_;
v_pos_4702_ = v_pos_4731_;
goto v___jp_4699_;
}
v___jp_4734_:
{
lean_object* v___x_4737_; 
v___x_4737_ = lean_box(0);
v_snd_4730_ = v_snd_4736_;
v_pos_4731_ = v___y_4735_;
v_err_4732_ = v___x_4737_;
goto v___jp_4729_;
}
v___jp_4739_:
{
lean_object* v_fst_4743_; lean_object* v_snd_4744_; uint8_t v_decide_4745_; 
v_fst_4743_ = lean_ctor_get(v_pos_4742_, 0);
v_snd_4744_ = lean_ctor_get(v_pos_4742_, 1);
lean_inc(v_snd_4744_);
v_decide_4745_ = lean_nat_dec_eq(v_snd_4740_, v_snd_4744_);
lean_dec(v_snd_4740_);
if (v_decide_4745_ == 0)
{
lean_dec(v_snd_4744_);
lean_dec_ref(v_pos_4742_);
return v___y_4741_;
}
else
{
lean_object* v___x_4746_; uint8_t v_decide_4747_; 
lean_dec_ref(v___y_4741_);
v___x_4746_ = lean_string_utf8_byte_size(v_fst_4743_);
v_decide_4747_ = lean_nat_dec_eq(v_snd_4744_, v___x_4746_);
if (v_decide_4747_ == 0)
{
if (v_decide_4745_ == 0)
{
v___y_4735_ = v_pos_4742_;
v_snd_4736_ = v_snd_4744_;
goto v___jp_4734_;
}
else
{
uint32_t v___x_4748_; uint32_t v_c_4749_; uint8_t v___x_4750_; 
v___x_4748_ = 83;
v_c_4749_ = lean_string_utf8_get_fast(v_fst_4743_, v_snd_4744_);
v___x_4750_ = lean_uint32_dec_eq(v_c_4749_, v___x_4748_);
if (v___x_4750_ == 0)
{
lean_object* v___x_4751_; 
v___x_4751_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1));
v_snd_4730_ = v_snd_4744_;
v_pos_4731_ = v_pos_4742_;
v_err_4732_ = v___x_4751_;
goto v___jp_4729_;
}
else
{
lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4767_; 
lean_inc(v_fst_4743_);
v_isSharedCheck_4767_ = !lean_is_exclusive(v_pos_4742_);
if (v_isSharedCheck_4767_ == 0)
{
lean_object* v_unused_4768_; lean_object* v_unused_4769_; 
v_unused_4768_ = lean_ctor_get(v_pos_4742_, 1);
lean_dec(v_unused_4768_);
v_unused_4769_ = lean_ctor_get(v_pos_4742_, 0);
lean_dec(v_unused_4769_);
v___x_4753_ = v_pos_4742_;
v_isShared_4754_ = v_isSharedCheck_4767_;
goto v_resetjp_4752_;
}
else
{
lean_dec(v_pos_4742_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4767_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4755_; lean_object* v_it_x27_4757_; 
v___x_4755_ = lean_string_utf8_next_fast(v_fst_4743_, v_snd_4744_);
if (v_isShared_4754_ == 0)
{
lean_ctor_set(v___x_4753_, 1, v___x_4755_);
v_it_x27_4757_ = v___x_4753_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_fst_4743_);
lean_ctor_set(v_reuseFailAlloc_4766_, 1, v___x_4755_);
v_it_x27_4757_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4758_ = ((lean_object*)(l_Std_Time_parseModifier___closed__20));
v___x_4759_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(v___x_4758_, v_it_x27_4757_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_pos_4760_; lean_object* v_res_4761_; lean_object* v___x_4762_; 
v_pos_4760_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_pos_4760_);
v_res_4761_ = lean_ctor_get(v___x_4759_, 1);
lean_inc(v_res_4761_);
lean_dec_ref_known(v___x_4759_, 2);
v___x_4762_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(v___f_4738_, v_res_4761_, v_pos_4760_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_dec(v_snd_4744_);
return v___x_4762_;
}
else
{
lean_object* v_pos_4763_; 
v_pos_4763_ = lean_ctor_get(v___x_4762_, 0);
lean_inc(v_pos_4763_);
v_snd_4700_ = v_snd_4744_;
v___y_4701_ = v___x_4762_;
v_pos_4702_ = v_pos_4763_;
goto v___jp_4699_;
}
}
else
{
lean_object* v_pos_4764_; lean_object* v_err_4765_; 
v_pos_4764_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_pos_4764_);
v_err_4765_ = lean_ctor_get(v___x_4759_, 1);
lean_inc(v_err_4765_);
lean_dec_ref_known(v___x_4759_, 2);
v_snd_4730_ = v_snd_4744_;
v_pos_4731_ = v_pos_4764_;
v_err_4732_ = v_err_4765_;
goto v___jp_4729_;
}
}
}
}
}
}
else
{
v___y_4735_ = v_pos_4742_;
v_snd_4736_ = v_snd_4744_;
goto v___jp_4734_;
}
}
}
v___jp_4770_:
{
lean_object* v___x_4774_; 
lean_inc_ref(v_pos_4772_);
v___x_4774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4774_, 0, v_pos_4772_);
lean_ctor_set(v___x_4774_, 1, v_err_4773_);
v_snd_4740_ = v_snd_4771_;
v___y_4741_ = v___x_4774_;
v_pos_4742_ = v_pos_4772_;
goto v___jp_4739_;
}
v___jp_4775_:
{
lean_object* v___x_4778_; 
v___x_4778_ = lean_box(0);
v_snd_4771_ = v_snd_4777_;
v_pos_4772_ = v___y_4776_;
v_err_4773_ = v___x_4778_;
goto v___jp_4770_;
}
v___jp_4780_:
{
lean_object* v_fst_4785_; lean_object* v_snd_4786_; uint8_t v_decide_4787_; 
v_fst_4785_ = lean_ctor_get(v_pos_4784_, 0);
v_snd_4786_ = lean_ctor_get(v_pos_4784_, 1);
lean_inc(v_snd_4786_);
v_decide_4787_ = lean_nat_dec_eq(v_snd_4781_, v_snd_4786_);
lean_dec(v_snd_4781_);
if (v_decide_4787_ == 0)
{
lean_dec(v_snd_4786_);
lean_dec_ref(v_pos_4784_);
lean_dec_ref(v___y_4782_);
return v___y_4783_;
}
else
{
lean_object* v___x_4788_; uint8_t v_decide_4789_; 
lean_dec_ref(v___y_4783_);
v___x_4788_ = lean_string_utf8_byte_size(v_fst_4785_);
v_decide_4789_ = lean_nat_dec_eq(v_snd_4786_, v___x_4788_);
if (v_decide_4789_ == 0)
{
if (v_decide_4787_ == 0)
{
lean_dec_ref(v___y_4782_);
v___y_4776_ = v_pos_4784_;
v_snd_4777_ = v_snd_4786_;
goto v___jp_4775_;
}
else
{
uint32_t v___x_4790_; uint32_t v_c_4791_; uint8_t v___x_4792_; 
v___x_4790_ = 115;
v_c_4791_ = lean_string_utf8_get_fast(v_fst_4785_, v_snd_4786_);
v___x_4792_ = lean_uint32_dec_eq(v_c_4791_, v___x_4790_);
if (v___x_4792_ == 0)
{
lean_object* v___x_4793_; 
lean_dec_ref(v___y_4782_);
v___x_4793_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1));
v_snd_4771_ = v_snd_4786_;
v_pos_4772_ = v_pos_4784_;
v_err_4773_ = v___x_4793_;
goto v___jp_4770_;
}
else
{
lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4809_; 
lean_inc(v_fst_4785_);
v_isSharedCheck_4809_ = !lean_is_exclusive(v_pos_4784_);
if (v_isSharedCheck_4809_ == 0)
{
lean_object* v_unused_4810_; lean_object* v_unused_4811_; 
v_unused_4810_ = lean_ctor_get(v_pos_4784_, 1);
lean_dec(v_unused_4810_);
v_unused_4811_ = lean_ctor_get(v_pos_4784_, 0);
lean_dec(v_unused_4811_);
v___x_4795_ = v_pos_4784_;
v_isShared_4796_ = v_isSharedCheck_4809_;
goto v_resetjp_4794_;
}
else
{
lean_dec(v_pos_4784_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4809_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4797_; lean_object* v_it_x27_4799_; 
v___x_4797_ = lean_string_utf8_next_fast(v_fst_4785_, v_snd_4786_);
if (v_isShared_4796_ == 0)
{
lean_ctor_set(v___x_4795_, 1, v___x_4797_);
v_it_x27_4799_ = v___x_4795_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_fst_4785_);
lean_ctor_set(v_reuseFailAlloc_4808_, 1, v___x_4797_);
v_it_x27_4799_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4800_ = ((lean_object*)(l_Std_Time_parseModifier___closed__22));
v___x_4801_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(v___x_4800_, v_it_x27_4799_);
if (lean_obj_tag(v___x_4801_) == 0)
{
lean_object* v_pos_4802_; lean_object* v_res_4803_; lean_object* v___x_4804_; 
v_pos_4802_ = lean_ctor_get(v___x_4801_, 0);
lean_inc(v_pos_4802_);
v_res_4803_ = lean_ctor_get(v___x_4801_, 1);
lean_inc(v_res_4803_);
lean_dec_ref_known(v___x_4801_, 2);
v___x_4804_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4779_, v___y_4782_, v_res_4803_, v_pos_4802_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_dec(v_snd_4786_);
return v___x_4804_;
}
else
{
lean_object* v_pos_4805_; 
v_pos_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc(v_pos_4805_);
v_snd_4740_ = v_snd_4786_;
v___y_4741_ = v___x_4804_;
v_pos_4742_ = v_pos_4805_;
goto v___jp_4739_;
}
}
else
{
lean_object* v_pos_4806_; lean_object* v_err_4807_; 
lean_dec_ref(v___y_4782_);
v_pos_4806_ = lean_ctor_get(v___x_4801_, 0);
lean_inc(v_pos_4806_);
v_err_4807_ = lean_ctor_get(v___x_4801_, 1);
lean_inc(v_err_4807_);
lean_dec_ref_known(v___x_4801_, 2);
v_snd_4771_ = v_snd_4786_;
v_pos_4772_ = v_pos_4806_;
v_err_4773_ = v_err_4807_;
goto v___jp_4770_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_4782_);
v___y_4776_ = v_pos_4784_;
v_snd_4777_ = v_snd_4786_;
goto v___jp_4775_;
}
}
}
v___jp_4812_:
{
lean_object* v___x_4817_; 
lean_inc_ref(v_pos_4815_);
v___x_4817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4817_, 0, v_pos_4815_);
lean_ctor_set(v___x_4817_, 1, v_err_4816_);
v_snd_4781_ = v_snd_4813_;
v___y_4782_ = v___y_4814_;
v___y_4783_ = v___x_4817_;
v_pos_4784_ = v_pos_4815_;
goto v___jp_4780_;
}
v___jp_4818_:
{
lean_object* v___x_4822_; 
v___x_4822_ = lean_box(0);
v_snd_4813_ = v_snd_4820_;
v___y_4814_ = v___y_4821_;
v_pos_4815_ = v___y_4819_;
v_err_4816_ = v___x_4822_;
goto v___jp_4812_;
}
v___jp_4824_:
{
lean_object* v_fst_4829_; lean_object* v_snd_4830_; uint8_t v_decide_4831_; 
v_fst_4829_ = lean_ctor_get(v_pos_4828_, 0);
v_snd_4830_ = lean_ctor_get(v_pos_4828_, 1);
lean_inc(v_snd_4830_);
v_decide_4831_ = lean_nat_dec_eq(v_snd_4826_, v_snd_4830_);
lean_dec(v_snd_4826_);
if (v_decide_4831_ == 0)
{
lean_dec(v_snd_4830_);
lean_dec_ref(v_pos_4828_);
lean_dec_ref(v___y_4825_);
return v___y_4827_;
}
else
{
lean_object* v___x_4832_; uint8_t v_decide_4833_; 
lean_dec_ref(v___y_4827_);
v___x_4832_ = lean_string_utf8_byte_size(v_fst_4829_);
v_decide_4833_ = lean_nat_dec_eq(v_snd_4830_, v___x_4832_);
if (v_decide_4833_ == 0)
{
if (v_decide_4831_ == 0)
{
v___y_4819_ = v_pos_4828_;
v_snd_4820_ = v_snd_4830_;
v___y_4821_ = v___y_4825_;
goto v___jp_4818_;
}
else
{
uint32_t v___x_4834_; uint32_t v_c_4835_; uint8_t v___x_4836_; 
v___x_4834_ = 109;
v_c_4835_ = lean_string_utf8_get_fast(v_fst_4829_, v_snd_4830_);
v___x_4836_ = lean_uint32_dec_eq(v_c_4835_, v___x_4834_);
if (v___x_4836_ == 0)
{
lean_object* v___x_4837_; 
v___x_4837_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1));
v_snd_4813_ = v_snd_4830_;
v___y_4814_ = v___y_4825_;
v_pos_4815_ = v_pos_4828_;
v_err_4816_ = v___x_4837_;
goto v___jp_4812_;
}
else
{
lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4853_; 
lean_inc(v_fst_4829_);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_pos_4828_);
if (v_isSharedCheck_4853_ == 0)
{
lean_object* v_unused_4854_; lean_object* v_unused_4855_; 
v_unused_4854_ = lean_ctor_get(v_pos_4828_, 1);
lean_dec(v_unused_4854_);
v_unused_4855_ = lean_ctor_get(v_pos_4828_, 0);
lean_dec(v_unused_4855_);
v___x_4839_ = v_pos_4828_;
v_isShared_4840_ = v_isSharedCheck_4853_;
goto v_resetjp_4838_;
}
else
{
lean_dec(v_pos_4828_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4853_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4841_; lean_object* v_it_x27_4843_; 
v___x_4841_ = lean_string_utf8_next_fast(v_fst_4829_, v_snd_4830_);
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 1, v___x_4841_);
v_it_x27_4843_ = v___x_4839_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_fst_4829_);
lean_ctor_set(v_reuseFailAlloc_4852_, 1, v___x_4841_);
v_it_x27_4843_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = ((lean_object*)(l_Std_Time_parseModifier___closed__24));
v___x_4845_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(v___x_4844_, v_it_x27_4843_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v_pos_4846_; lean_object* v_res_4847_; lean_object* v___x_4848_; 
v_pos_4846_ = lean_ctor_get(v___x_4845_, 0);
lean_inc(v_pos_4846_);
v_res_4847_ = lean_ctor_get(v___x_4845_, 1);
lean_inc(v_res_4847_);
lean_dec_ref_known(v___x_4845_, 2);
lean_inc_ref(v___y_4825_);
v___x_4848_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4823_, v___y_4825_, v_res_4847_, v_pos_4846_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_dec(v_snd_4830_);
lean_dec_ref(v___y_4825_);
return v___x_4848_;
}
else
{
lean_object* v_pos_4849_; 
v_pos_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_pos_4849_);
v_snd_4781_ = v_snd_4830_;
v___y_4782_ = v___y_4825_;
v___y_4783_ = v___x_4848_;
v_pos_4784_ = v_pos_4849_;
goto v___jp_4780_;
}
}
else
{
lean_object* v_pos_4850_; lean_object* v_err_4851_; 
v_pos_4850_ = lean_ctor_get(v___x_4845_, 0);
lean_inc(v_pos_4850_);
v_err_4851_ = lean_ctor_get(v___x_4845_, 1);
lean_inc(v_err_4851_);
lean_dec_ref_known(v___x_4845_, 2);
v_snd_4813_ = v_snd_4830_;
v___y_4814_ = v___y_4825_;
v_pos_4815_ = v_pos_4850_;
v_err_4816_ = v_err_4851_;
goto v___jp_4812_;
}
}
}
}
}
}
else
{
v___y_4819_ = v_pos_4828_;
v_snd_4820_ = v_snd_4830_;
v___y_4821_ = v___y_4825_;
goto v___jp_4818_;
}
}
}
v___jp_4856_:
{
lean_object* v___x_4861_; 
lean_inc_ref(v_pos_4859_);
v___x_4861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4861_, 0, v_pos_4859_);
lean_ctor_set(v___x_4861_, 1, v_err_4860_);
v___y_4825_ = v___y_4857_;
v_snd_4826_ = v_snd_4858_;
v___y_4827_ = v___x_4861_;
v_pos_4828_ = v_pos_4859_;
goto v___jp_4824_;
}
v___jp_4862_:
{
lean_object* v___x_4866_; 
v___x_4866_ = lean_box(0);
v___y_4857_ = v___y_4863_;
v_snd_4858_ = v_snd_4865_;
v_pos_4859_ = v___y_4864_;
v_err_4860_ = v___x_4866_;
goto v___jp_4856_;
}
v___jp_4868_:
{
lean_object* v_fst_4873_; lean_object* v_snd_4874_; uint8_t v_decide_4875_; 
v_fst_4873_ = lean_ctor_get(v_pos_4872_, 0);
v_snd_4874_ = lean_ctor_get(v_pos_4872_, 1);
lean_inc(v_snd_4874_);
v_decide_4875_ = lean_nat_dec_eq(v_snd_4870_, v_snd_4874_);
lean_dec(v_snd_4870_);
if (v_decide_4875_ == 0)
{
lean_dec(v_snd_4874_);
lean_dec_ref(v_pos_4872_);
lean_dec_ref(v___y_4869_);
return v___y_4871_;
}
else
{
lean_object* v___x_4876_; uint8_t v_decide_4877_; 
lean_dec_ref(v___y_4871_);
v___x_4876_ = lean_string_utf8_byte_size(v_fst_4873_);
v_decide_4877_ = lean_nat_dec_eq(v_snd_4874_, v___x_4876_);
if (v_decide_4877_ == 0)
{
if (v_decide_4875_ == 0)
{
v___y_4863_ = v___y_4869_;
v___y_4864_ = v_pos_4872_;
v_snd_4865_ = v_snd_4874_;
goto v___jp_4862_;
}
else
{
uint32_t v___x_4878_; uint32_t v_c_4879_; uint8_t v___x_4880_; 
v___x_4878_ = 72;
v_c_4879_ = lean_string_utf8_get_fast(v_fst_4873_, v_snd_4874_);
v___x_4880_ = lean_uint32_dec_eq(v_c_4879_, v___x_4878_);
if (v___x_4880_ == 0)
{
lean_object* v___x_4881_; 
v___x_4881_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1));
v___y_4857_ = v___y_4869_;
v_snd_4858_ = v_snd_4874_;
v_pos_4859_ = v_pos_4872_;
v_err_4860_ = v___x_4881_;
goto v___jp_4856_;
}
else
{
lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4897_; 
lean_inc(v_fst_4873_);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_pos_4872_);
if (v_isSharedCheck_4897_ == 0)
{
lean_object* v_unused_4898_; lean_object* v_unused_4899_; 
v_unused_4898_ = lean_ctor_get(v_pos_4872_, 1);
lean_dec(v_unused_4898_);
v_unused_4899_ = lean_ctor_get(v_pos_4872_, 0);
lean_dec(v_unused_4899_);
v___x_4883_ = v_pos_4872_;
v_isShared_4884_ = v_isSharedCheck_4897_;
goto v_resetjp_4882_;
}
else
{
lean_dec(v_pos_4872_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4897_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; lean_object* v_it_x27_4887_; 
v___x_4885_ = lean_string_utf8_next_fast(v_fst_4873_, v_snd_4874_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 1, v___x_4885_);
v_it_x27_4887_ = v___x_4883_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_fst_4873_);
lean_ctor_set(v_reuseFailAlloc_4896_, 1, v___x_4885_);
v_it_x27_4887_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4888_ = ((lean_object*)(l_Std_Time_parseModifier___closed__26));
v___x_4889_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(v___x_4888_, v_it_x27_4887_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_pos_4890_; lean_object* v_res_4891_; lean_object* v___x_4892_; 
v_pos_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_pos_4890_);
v_res_4891_ = lean_ctor_get(v___x_4889_, 1);
lean_inc(v_res_4891_);
lean_dec_ref_known(v___x_4889_, 2);
lean_inc_ref(v___y_4869_);
v___x_4892_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4867_, v___y_4869_, v_res_4891_, v_pos_4890_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_dec(v_snd_4874_);
lean_dec_ref(v___y_4869_);
return v___x_4892_;
}
else
{
lean_object* v_pos_4893_; 
v_pos_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_pos_4893_);
v___y_4825_ = v___y_4869_;
v_snd_4826_ = v_snd_4874_;
v___y_4827_ = v___x_4892_;
v_pos_4828_ = v_pos_4893_;
goto v___jp_4824_;
}
}
else
{
lean_object* v_pos_4894_; lean_object* v_err_4895_; 
v_pos_4894_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_pos_4894_);
v_err_4895_ = lean_ctor_get(v___x_4889_, 1);
lean_inc(v_err_4895_);
lean_dec_ref_known(v___x_4889_, 2);
v___y_4857_ = v___y_4869_;
v_snd_4858_ = v_snd_4874_;
v_pos_4859_ = v_pos_4894_;
v_err_4860_ = v_err_4895_;
goto v___jp_4856_;
}
}
}
}
}
}
else
{
v___y_4863_ = v___y_4869_;
v___y_4864_ = v_pos_4872_;
v_snd_4865_ = v_snd_4874_;
goto v___jp_4862_;
}
}
}
v___jp_4900_:
{
lean_object* v___x_4905_; 
lean_inc_ref(v_pos_4903_);
v___x_4905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4905_, 0, v_pos_4903_);
lean_ctor_set(v___x_4905_, 1, v_err_4904_);
v___y_4869_ = v___y_4901_;
v_snd_4870_ = v_snd_4902_;
v___y_4871_ = v___x_4905_;
v_pos_4872_ = v_pos_4903_;
goto v___jp_4868_;
}
v___jp_4906_:
{
lean_object* v___x_4910_; 
v___x_4910_ = lean_box(0);
v___y_4901_ = v___y_4907_;
v_snd_4902_ = v_snd_4909_;
v_pos_4903_ = v___y_4908_;
v_err_4904_ = v___x_4910_;
goto v___jp_4900_;
}
v___jp_4912_:
{
lean_object* v_fst_4917_; lean_object* v_snd_4918_; uint8_t v_decide_4919_; 
v_fst_4917_ = lean_ctor_get(v_pos_4916_, 0);
v_snd_4918_ = lean_ctor_get(v_pos_4916_, 1);
lean_inc(v_snd_4918_);
v_decide_4919_ = lean_nat_dec_eq(v_snd_4913_, v_snd_4918_);
lean_dec(v_snd_4913_);
if (v_decide_4919_ == 0)
{
lean_dec(v_snd_4918_);
lean_dec_ref(v_pos_4916_);
lean_dec_ref(v___y_4914_);
return v___y_4915_;
}
else
{
lean_object* v___x_4920_; uint8_t v_decide_4921_; 
lean_dec_ref(v___y_4915_);
v___x_4920_ = lean_string_utf8_byte_size(v_fst_4917_);
v_decide_4921_ = lean_nat_dec_eq(v_snd_4918_, v___x_4920_);
if (v_decide_4921_ == 0)
{
if (v_decide_4919_ == 0)
{
v___y_4907_ = v___y_4914_;
v___y_4908_ = v_pos_4916_;
v_snd_4909_ = v_snd_4918_;
goto v___jp_4906_;
}
else
{
uint32_t v___x_4922_; uint32_t v_c_4923_; uint8_t v___x_4924_; 
v___x_4922_ = 107;
v_c_4923_ = lean_string_utf8_get_fast(v_fst_4917_, v_snd_4918_);
v___x_4924_ = lean_uint32_dec_eq(v_c_4923_, v___x_4922_);
if (v___x_4924_ == 0)
{
lean_object* v___x_4925_; 
v___x_4925_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1));
v___y_4901_ = v___y_4914_;
v_snd_4902_ = v_snd_4918_;
v_pos_4903_ = v_pos_4916_;
v_err_4904_ = v___x_4925_;
goto v___jp_4900_;
}
else
{
lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4941_; 
lean_inc(v_fst_4917_);
v_isSharedCheck_4941_ = !lean_is_exclusive(v_pos_4916_);
if (v_isSharedCheck_4941_ == 0)
{
lean_object* v_unused_4942_; lean_object* v_unused_4943_; 
v_unused_4942_ = lean_ctor_get(v_pos_4916_, 1);
lean_dec(v_unused_4942_);
v_unused_4943_ = lean_ctor_get(v_pos_4916_, 0);
lean_dec(v_unused_4943_);
v___x_4927_ = v_pos_4916_;
v_isShared_4928_ = v_isSharedCheck_4941_;
goto v_resetjp_4926_;
}
else
{
lean_dec(v_pos_4916_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4941_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4929_; lean_object* v_it_x27_4931_; 
v___x_4929_ = lean_string_utf8_next_fast(v_fst_4917_, v_snd_4918_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 1, v___x_4929_);
v_it_x27_4931_ = v___x_4927_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_fst_4917_);
lean_ctor_set(v_reuseFailAlloc_4940_, 1, v___x_4929_);
v_it_x27_4931_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4932_ = ((lean_object*)(l_Std_Time_parseModifier___closed__28));
v___x_4933_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(v___x_4932_, v_it_x27_4931_);
if (lean_obj_tag(v___x_4933_) == 0)
{
lean_object* v_pos_4934_; lean_object* v_res_4935_; lean_object* v___x_4936_; 
v_pos_4934_ = lean_ctor_get(v___x_4933_, 0);
lean_inc(v_pos_4934_);
v_res_4935_ = lean_ctor_get(v___x_4933_, 1);
lean_inc(v_res_4935_);
lean_dec_ref_known(v___x_4933_, 2);
lean_inc_ref(v___y_4914_);
v___x_4936_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4911_, v___y_4914_, v_res_4935_, v_pos_4934_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_dec(v_snd_4918_);
lean_dec_ref(v___y_4914_);
return v___x_4936_;
}
else
{
lean_object* v_pos_4937_; 
v_pos_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_pos_4937_);
v___y_4869_ = v___y_4914_;
v_snd_4870_ = v_snd_4918_;
v___y_4871_ = v___x_4936_;
v_pos_4872_ = v_pos_4937_;
goto v___jp_4868_;
}
}
else
{
lean_object* v_pos_4938_; lean_object* v_err_4939_; 
v_pos_4938_ = lean_ctor_get(v___x_4933_, 0);
lean_inc(v_pos_4938_);
v_err_4939_ = lean_ctor_get(v___x_4933_, 1);
lean_inc(v_err_4939_);
lean_dec_ref_known(v___x_4933_, 2);
v___y_4901_ = v___y_4914_;
v_snd_4902_ = v_snd_4918_;
v_pos_4903_ = v_pos_4938_;
v_err_4904_ = v_err_4939_;
goto v___jp_4900_;
}
}
}
}
}
}
else
{
v___y_4907_ = v___y_4914_;
v___y_4908_ = v_pos_4916_;
v_snd_4909_ = v_snd_4918_;
goto v___jp_4906_;
}
}
}
v___jp_4944_:
{
lean_object* v___x_4949_; 
lean_inc_ref(v_pos_4947_);
v___x_4949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4949_, 0, v_pos_4947_);
lean_ctor_set(v___x_4949_, 1, v_err_4948_);
v_snd_4913_ = v_snd_4946_;
v___y_4914_ = v___y_4945_;
v___y_4915_ = v___x_4949_;
v_pos_4916_ = v_pos_4947_;
goto v___jp_4912_;
}
v___jp_4950_:
{
lean_object* v___x_4954_; 
v___x_4954_ = lean_box(0);
v___y_4945_ = v___y_4951_;
v_snd_4946_ = v_snd_4953_;
v_pos_4947_ = v___y_4952_;
v_err_4948_ = v___x_4954_;
goto v___jp_4944_;
}
v___jp_4956_:
{
lean_object* v_fst_4961_; lean_object* v_snd_4962_; uint8_t v_decide_4963_; 
v_fst_4961_ = lean_ctor_get(v_pos_4960_, 0);
v_snd_4962_ = lean_ctor_get(v_pos_4960_, 1);
lean_inc(v_snd_4962_);
v_decide_4963_ = lean_nat_dec_eq(v_snd_4958_, v_snd_4962_);
lean_dec(v_snd_4958_);
if (v_decide_4963_ == 0)
{
lean_dec(v_snd_4962_);
lean_dec_ref(v_pos_4960_);
lean_dec_ref(v___y_4957_);
return v___y_4959_;
}
else
{
lean_object* v___x_4964_; uint8_t v_decide_4965_; 
lean_dec_ref(v___y_4959_);
v___x_4964_ = lean_string_utf8_byte_size(v_fst_4961_);
v_decide_4965_ = lean_nat_dec_eq(v_snd_4962_, v___x_4964_);
if (v_decide_4965_ == 0)
{
if (v_decide_4963_ == 0)
{
v___y_4951_ = v___y_4957_;
v___y_4952_ = v_pos_4960_;
v_snd_4953_ = v_snd_4962_;
goto v___jp_4950_;
}
else
{
uint32_t v___x_4966_; uint32_t v_c_4967_; uint8_t v___x_4968_; 
v___x_4966_ = 75;
v_c_4967_ = lean_string_utf8_get_fast(v_fst_4961_, v_snd_4962_);
v___x_4968_ = lean_uint32_dec_eq(v_c_4967_, v___x_4966_);
if (v___x_4968_ == 0)
{
lean_object* v___x_4969_; 
v___x_4969_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1));
v___y_4945_ = v___y_4957_;
v_snd_4946_ = v_snd_4962_;
v_pos_4947_ = v_pos_4960_;
v_err_4948_ = v___x_4969_;
goto v___jp_4944_;
}
else
{
lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4985_; 
lean_inc(v_fst_4961_);
v_isSharedCheck_4985_ = !lean_is_exclusive(v_pos_4960_);
if (v_isSharedCheck_4985_ == 0)
{
lean_object* v_unused_4986_; lean_object* v_unused_4987_; 
v_unused_4986_ = lean_ctor_get(v_pos_4960_, 1);
lean_dec(v_unused_4986_);
v_unused_4987_ = lean_ctor_get(v_pos_4960_, 0);
lean_dec(v_unused_4987_);
v___x_4971_ = v_pos_4960_;
v_isShared_4972_ = v_isSharedCheck_4985_;
goto v_resetjp_4970_;
}
else
{
lean_dec(v_pos_4960_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4985_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4973_; lean_object* v_it_x27_4975_; 
v___x_4973_ = lean_string_utf8_next_fast(v_fst_4961_, v_snd_4962_);
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_4973_);
v_it_x27_4975_ = v___x_4971_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_fst_4961_);
lean_ctor_set(v_reuseFailAlloc_4984_, 1, v___x_4973_);
v_it_x27_4975_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4976_ = ((lean_object*)(l_Std_Time_parseModifier___closed__30));
v___x_4977_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(v___x_4976_, v_it_x27_4975_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_pos_4978_; lean_object* v_res_4979_; lean_object* v___x_4980_; 
v_pos_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_pos_4978_);
v_res_4979_ = lean_ctor_get(v___x_4977_, 1);
lean_inc(v_res_4979_);
lean_dec_ref_known(v___x_4977_, 2);
lean_inc_ref(v___y_4957_);
v___x_4980_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4955_, v___y_4957_, v_res_4979_, v_pos_4978_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_dec(v_snd_4962_);
lean_dec_ref(v___y_4957_);
return v___x_4980_;
}
else
{
lean_object* v_pos_4981_; 
v_pos_4981_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_pos_4981_);
v_snd_4913_ = v_snd_4962_;
v___y_4914_ = v___y_4957_;
v___y_4915_ = v___x_4980_;
v_pos_4916_ = v_pos_4981_;
goto v___jp_4912_;
}
}
else
{
lean_object* v_pos_4982_; lean_object* v_err_4983_; 
v_pos_4982_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_pos_4982_);
v_err_4983_ = lean_ctor_get(v___x_4977_, 1);
lean_inc(v_err_4983_);
lean_dec_ref_known(v___x_4977_, 2);
v___y_4945_ = v___y_4957_;
v_snd_4946_ = v_snd_4962_;
v_pos_4947_ = v_pos_4982_;
v_err_4948_ = v_err_4983_;
goto v___jp_4944_;
}
}
}
}
}
}
else
{
v___y_4951_ = v___y_4957_;
v___y_4952_ = v_pos_4960_;
v_snd_4953_ = v_snd_4962_;
goto v___jp_4950_;
}
}
}
v___jp_4988_:
{
lean_object* v___x_4993_; 
lean_inc_ref(v_pos_4991_);
v___x_4993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4993_, 0, v_pos_4991_);
lean_ctor_set(v___x_4993_, 1, v_err_4992_);
v___y_4957_ = v___y_4989_;
v_snd_4958_ = v_snd_4990_;
v___y_4959_ = v___x_4993_;
v_pos_4960_ = v_pos_4991_;
goto v___jp_4956_;
}
v___jp_4994_:
{
lean_object* v___x_4998_; 
v___x_4998_ = lean_box(0);
v___y_4989_ = v___y_4995_;
v_snd_4990_ = v_snd_4997_;
v_pos_4991_ = v___y_4996_;
v_err_4992_ = v___x_4998_;
goto v___jp_4988_;
}
v___jp_5000_:
{
lean_object* v_fst_5005_; lean_object* v_snd_5006_; uint8_t v_decide_5007_; 
v_fst_5005_ = lean_ctor_get(v_pos_5004_, 0);
v_snd_5006_ = lean_ctor_get(v_pos_5004_, 1);
lean_inc(v_snd_5006_);
v_decide_5007_ = lean_nat_dec_eq(v_snd_5002_, v_snd_5006_);
lean_dec(v_snd_5002_);
if (v_decide_5007_ == 0)
{
lean_dec(v_snd_5006_);
lean_dec_ref(v_pos_5004_);
lean_dec_ref(v___y_5001_);
return v___y_5003_;
}
else
{
lean_object* v___x_5008_; uint8_t v_decide_5009_; 
lean_dec_ref(v___y_5003_);
v___x_5008_ = lean_string_utf8_byte_size(v_fst_5005_);
v_decide_5009_ = lean_nat_dec_eq(v_snd_5006_, v___x_5008_);
if (v_decide_5009_ == 0)
{
if (v_decide_5007_ == 0)
{
v___y_4995_ = v___y_5001_;
v___y_4996_ = v_pos_5004_;
v_snd_4997_ = v_snd_5006_;
goto v___jp_4994_;
}
else
{
uint32_t v___x_5010_; uint32_t v_c_5011_; uint8_t v___x_5012_; 
v___x_5010_ = 104;
v_c_5011_ = lean_string_utf8_get_fast(v_fst_5005_, v_snd_5006_);
v___x_5012_ = lean_uint32_dec_eq(v_c_5011_, v___x_5010_);
if (v___x_5012_ == 0)
{
lean_object* v___x_5013_; 
v___x_5013_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1));
v___y_4989_ = v___y_5001_;
v_snd_4990_ = v_snd_5006_;
v_pos_4991_ = v_pos_5004_;
v_err_4992_ = v___x_5013_;
goto v___jp_4988_;
}
else
{
lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5029_; 
lean_inc(v_fst_5005_);
v_isSharedCheck_5029_ = !lean_is_exclusive(v_pos_5004_);
if (v_isSharedCheck_5029_ == 0)
{
lean_object* v_unused_5030_; lean_object* v_unused_5031_; 
v_unused_5030_ = lean_ctor_get(v_pos_5004_, 1);
lean_dec(v_unused_5030_);
v_unused_5031_ = lean_ctor_get(v_pos_5004_, 0);
lean_dec(v_unused_5031_);
v___x_5015_ = v_pos_5004_;
v_isShared_5016_ = v_isSharedCheck_5029_;
goto v_resetjp_5014_;
}
else
{
lean_dec(v_pos_5004_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5029_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5017_; lean_object* v_it_x27_5019_; 
v___x_5017_ = lean_string_utf8_next_fast(v_fst_5005_, v_snd_5006_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 1, v___x_5017_);
v_it_x27_5019_ = v___x_5015_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_fst_5005_);
lean_ctor_set(v_reuseFailAlloc_5028_, 1, v___x_5017_);
v_it_x27_5019_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = ((lean_object*)(l_Std_Time_parseModifier___closed__32));
v___x_5021_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(v___x_5020_, v_it_x27_5019_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_pos_5022_; lean_object* v_res_5023_; lean_object* v___x_5024_; 
v_pos_5022_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_pos_5022_);
v_res_5023_ = lean_ctor_get(v___x_5021_, 1);
lean_inc(v_res_5023_);
lean_dec_ref_known(v___x_5021_, 2);
lean_inc_ref(v___y_5001_);
v___x_5024_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4999_, v___y_5001_, v_res_5023_, v_pos_5022_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_dec(v_snd_5006_);
lean_dec_ref(v___y_5001_);
return v___x_5024_;
}
else
{
lean_object* v_pos_5025_; 
v_pos_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc(v_pos_5025_);
v___y_4957_ = v___y_5001_;
v_snd_4958_ = v_snd_5006_;
v___y_4959_ = v___x_5024_;
v_pos_4960_ = v_pos_5025_;
goto v___jp_4956_;
}
}
else
{
lean_object* v_pos_5026_; lean_object* v_err_5027_; 
v_pos_5026_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_pos_5026_);
v_err_5027_ = lean_ctor_get(v___x_5021_, 1);
lean_inc(v_err_5027_);
lean_dec_ref_known(v___x_5021_, 2);
v___y_4989_ = v___y_5001_;
v_snd_4990_ = v_snd_5006_;
v_pos_4991_ = v_pos_5026_;
v_err_4992_ = v_err_5027_;
goto v___jp_4988_;
}
}
}
}
}
}
else
{
v___y_4995_ = v___y_5001_;
v___y_4996_ = v_pos_5004_;
v_snd_4997_ = v_snd_5006_;
goto v___jp_4994_;
}
}
}
v___jp_5032_:
{
lean_object* v___x_5037_; 
lean_inc_ref(v_pos_5035_);
v___x_5037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5037_, 0, v_pos_5035_);
lean_ctor_set(v___x_5037_, 1, v_err_5036_);
v___y_5001_ = v___y_5033_;
v_snd_5002_ = v_snd_5034_;
v___y_5003_ = v___x_5037_;
v_pos_5004_ = v_pos_5035_;
goto v___jp_5000_;
}
v___jp_5038_:
{
lean_object* v___x_5042_; 
v___x_5042_ = lean_box(0);
v___y_5033_ = v___y_5039_;
v_snd_5034_ = v_snd_5041_;
v_pos_5035_ = v___y_5040_;
v_err_5036_ = v___x_5042_;
goto v___jp_5032_;
}
v___jp_5043_:
{
lean_object* v_fst_5048_; lean_object* v_snd_5049_; uint8_t v_decide_5050_; 
v_fst_5048_ = lean_ctor_get(v_pos_5047_, 0);
v_snd_5049_ = lean_ctor_get(v_pos_5047_, 1);
lean_inc(v_snd_5049_);
v_decide_5050_ = lean_nat_dec_eq(v_snd_5045_, v_snd_5049_);
lean_dec(v_snd_5045_);
if (v_decide_5050_ == 0)
{
lean_dec(v_snd_5049_);
lean_dec_ref(v_pos_5047_);
lean_dec_ref(v___y_5044_);
return v___y_5046_;
}
else
{
lean_object* v___x_5051_; uint8_t v_decide_5052_; 
lean_dec_ref(v___y_5046_);
v___x_5051_ = lean_string_utf8_byte_size(v_fst_5048_);
v_decide_5052_ = lean_nat_dec_eq(v_snd_5049_, v___x_5051_);
if (v_decide_5052_ == 0)
{
if (v_decide_5050_ == 0)
{
v___y_5039_ = v___y_5044_;
v___y_5040_ = v_pos_5047_;
v_snd_5041_ = v_snd_5049_;
goto v___jp_5038_;
}
else
{
uint32_t v___x_5053_; uint32_t v_c_5054_; uint8_t v___x_5055_; 
v___x_5053_ = 66;
v_c_5054_ = lean_string_utf8_get_fast(v_fst_5048_, v_snd_5049_);
v___x_5055_ = lean_uint32_dec_eq(v_c_5054_, v___x_5053_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5056_; 
v___x_5056_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1));
v___y_5033_ = v___y_5044_;
v_snd_5034_ = v_snd_5049_;
v_pos_5035_ = v_pos_5047_;
v_err_5036_ = v___x_5056_;
goto v___jp_5032_;
}
else
{
lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5072_; 
lean_inc(v_fst_5048_);
v_isSharedCheck_5072_ = !lean_is_exclusive(v_pos_5047_);
if (v_isSharedCheck_5072_ == 0)
{
lean_object* v_unused_5073_; lean_object* v_unused_5074_; 
v_unused_5073_ = lean_ctor_get(v_pos_5047_, 1);
lean_dec(v_unused_5073_);
v_unused_5074_ = lean_ctor_get(v_pos_5047_, 0);
lean_dec(v_unused_5074_);
v___x_5058_ = v_pos_5047_;
v_isShared_5059_ = v_isSharedCheck_5072_;
goto v_resetjp_5057_;
}
else
{
lean_dec(v_pos_5047_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5072_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5060_; lean_object* v_it_x27_5062_; 
v___x_5060_ = lean_string_utf8_next_fast(v_fst_5048_, v_snd_5049_);
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 1, v___x_5060_);
v_it_x27_5062_ = v___x_5058_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_fst_5048_);
lean_ctor_set(v_reuseFailAlloc_5071_, 1, v___x_5060_);
v_it_x27_5062_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = ((lean_object*)(l_Std_Time_parseModifier___closed__33));
v___x_5064_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(v___x_5063_, v_it_x27_5062_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v_pos_5065_; lean_object* v_res_5066_; lean_object* v___x_5067_; 
v_pos_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_pos_5065_);
v_res_5066_ = lean_ctor_get(v___x_5064_, 1);
lean_inc(v_res_5066_);
lean_dec_ref_known(v___x_5064_, 2);
v___x_5067_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(v_res_5066_, v_pos_5065_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_dec(v_snd_5049_);
lean_dec_ref(v___y_5044_);
return v___x_5067_;
}
else
{
lean_object* v_pos_5068_; 
v_pos_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc(v_pos_5068_);
v___y_5001_ = v___y_5044_;
v_snd_5002_ = v_snd_5049_;
v___y_5003_ = v___x_5067_;
v_pos_5004_ = v_pos_5068_;
goto v___jp_5000_;
}
}
else
{
lean_object* v_pos_5069_; lean_object* v_err_5070_; 
v_pos_5069_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_pos_5069_);
v_err_5070_ = lean_ctor_get(v___x_5064_, 1);
lean_inc(v_err_5070_);
lean_dec_ref_known(v___x_5064_, 2);
v___y_5033_ = v___y_5044_;
v_snd_5034_ = v_snd_5049_;
v_pos_5035_ = v_pos_5069_;
v_err_5036_ = v_err_5070_;
goto v___jp_5032_;
}
}
}
}
}
}
else
{
v___y_5039_ = v___y_5044_;
v___y_5040_ = v_pos_5047_;
v_snd_5041_ = v_snd_5049_;
goto v___jp_5038_;
}
}
}
v___jp_5075_:
{
lean_object* v___x_5080_; 
lean_inc_ref(v_pos_5078_);
v___x_5080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5080_, 0, v_pos_5078_);
lean_ctor_set(v___x_5080_, 1, v_err_5079_);
v___y_5044_ = v___y_5076_;
v_snd_5045_ = v_snd_5077_;
v___y_5046_ = v___x_5080_;
v_pos_5047_ = v_pos_5078_;
goto v___jp_5043_;
}
v___jp_5081_:
{
lean_object* v___x_5085_; 
v___x_5085_ = lean_box(0);
v___y_5076_ = v___y_5082_;
v_snd_5077_ = v_snd_5084_;
v_pos_5078_ = v___y_5083_;
v_err_5079_ = v___x_5085_;
goto v___jp_5075_;
}
v___jp_5086_:
{
lean_object* v_fst_5091_; lean_object* v_snd_5092_; uint8_t v_decide_5093_; 
v_fst_5091_ = lean_ctor_get(v_pos_5090_, 0);
v_snd_5092_ = lean_ctor_get(v_pos_5090_, 1);
lean_inc(v_snd_5092_);
v_decide_5093_ = lean_nat_dec_eq(v_snd_5088_, v_snd_5092_);
lean_dec(v_snd_5088_);
if (v_decide_5093_ == 0)
{
lean_dec(v_snd_5092_);
lean_dec_ref(v_pos_5090_);
lean_dec_ref(v___y_5087_);
return v___y_5089_;
}
else
{
lean_object* v___x_5094_; uint8_t v_decide_5095_; 
lean_dec_ref(v___y_5089_);
v___x_5094_ = lean_string_utf8_byte_size(v_fst_5091_);
v_decide_5095_ = lean_nat_dec_eq(v_snd_5092_, v___x_5094_);
if (v_decide_5095_ == 0)
{
if (v_decide_5093_ == 0)
{
v___y_5082_ = v___y_5087_;
v___y_5083_ = v_pos_5090_;
v_snd_5084_ = v_snd_5092_;
goto v___jp_5081_;
}
else
{
uint32_t v___x_5096_; uint32_t v_c_5097_; uint8_t v___x_5098_; 
v___x_5096_ = 98;
v_c_5097_ = lean_string_utf8_get_fast(v_fst_5091_, v_snd_5092_);
v___x_5098_ = lean_uint32_dec_eq(v_c_5097_, v___x_5096_);
if (v___x_5098_ == 0)
{
lean_object* v___x_5099_; 
v___x_5099_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1));
v___y_5076_ = v___y_5087_;
v_snd_5077_ = v_snd_5092_;
v_pos_5078_ = v_pos_5090_;
v_err_5079_ = v___x_5099_;
goto v___jp_5075_;
}
else
{
lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5115_; 
lean_inc(v_fst_5091_);
v_isSharedCheck_5115_ = !lean_is_exclusive(v_pos_5090_);
if (v_isSharedCheck_5115_ == 0)
{
lean_object* v_unused_5116_; lean_object* v_unused_5117_; 
v_unused_5116_ = lean_ctor_get(v_pos_5090_, 1);
lean_dec(v_unused_5116_);
v_unused_5117_ = lean_ctor_get(v_pos_5090_, 0);
lean_dec(v_unused_5117_);
v___x_5101_ = v_pos_5090_;
v_isShared_5102_ = v_isSharedCheck_5115_;
goto v_resetjp_5100_;
}
else
{
lean_dec(v_pos_5090_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5115_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5103_; lean_object* v_it_x27_5105_; 
v___x_5103_ = lean_string_utf8_next_fast(v_fst_5091_, v_snd_5092_);
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 1, v___x_5103_);
v_it_x27_5105_ = v___x_5101_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_fst_5091_);
lean_ctor_set(v_reuseFailAlloc_5114_, 1, v___x_5103_);
v_it_x27_5105_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5106_ = ((lean_object*)(l_Std_Time_parseModifier___closed__34));
v___x_5107_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(v___x_5106_, v_it_x27_5105_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v_pos_5108_; lean_object* v_res_5109_; lean_object* v___x_5110_; 
v_pos_5108_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_pos_5108_);
v_res_5109_ = lean_ctor_get(v___x_5107_, 1);
lean_inc(v_res_5109_);
lean_dec_ref_known(v___x_5107_, 2);
v___x_5110_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(v_res_5109_, v_pos_5108_);
if (lean_obj_tag(v___x_5110_) == 0)
{
lean_dec(v_snd_5092_);
lean_dec_ref(v___y_5087_);
return v___x_5110_;
}
else
{
lean_object* v_pos_5111_; 
v_pos_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_pos_5111_);
v___y_5044_ = v___y_5087_;
v_snd_5045_ = v_snd_5092_;
v___y_5046_ = v___x_5110_;
v_pos_5047_ = v_pos_5111_;
goto v___jp_5043_;
}
}
else
{
lean_object* v_pos_5112_; lean_object* v_err_5113_; 
v_pos_5112_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_pos_5112_);
v_err_5113_ = lean_ctor_get(v___x_5107_, 1);
lean_inc(v_err_5113_);
lean_dec_ref_known(v___x_5107_, 2);
v___y_5076_ = v___y_5087_;
v_snd_5077_ = v_snd_5092_;
v_pos_5078_ = v_pos_5112_;
v_err_5079_ = v_err_5113_;
goto v___jp_5075_;
}
}
}
}
}
}
else
{
v___y_5082_ = v___y_5087_;
v___y_5083_ = v_pos_5090_;
v_snd_5084_ = v_snd_5092_;
goto v___jp_5081_;
}
}
}
v___jp_5118_:
{
lean_object* v___x_5123_; 
lean_inc_ref(v_pos_5121_);
v___x_5123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5123_, 0, v_pos_5121_);
lean_ctor_set(v___x_5123_, 1, v_err_5122_);
v___y_5087_ = v___y_5119_;
v_snd_5088_ = v_snd_5120_;
v___y_5089_ = v___x_5123_;
v_pos_5090_ = v_pos_5121_;
goto v___jp_5086_;
}
v___jp_5124_:
{
lean_object* v___x_5128_; 
v___x_5128_ = lean_box(0);
v___y_5119_ = v___y_5125_;
v_snd_5120_ = v_snd_5127_;
v_pos_5121_ = v___y_5126_;
v_err_5122_ = v___x_5128_;
goto v___jp_5118_;
}
v___jp_5129_:
{
lean_object* v_fst_5134_; lean_object* v_snd_5135_; uint8_t v_decide_5136_; 
v_fst_5134_ = lean_ctor_get(v_pos_5133_, 0);
v_snd_5135_ = lean_ctor_get(v_pos_5133_, 1);
lean_inc(v_snd_5135_);
v_decide_5136_ = lean_nat_dec_eq(v_snd_5131_, v_snd_5135_);
lean_dec(v_snd_5131_);
if (v_decide_5136_ == 0)
{
lean_dec(v_snd_5135_);
lean_dec_ref(v_pos_5133_);
lean_dec_ref(v___y_5130_);
return v___y_5132_;
}
else
{
lean_object* v___x_5137_; uint8_t v_decide_5138_; 
lean_dec_ref(v___y_5132_);
v___x_5137_ = lean_string_utf8_byte_size(v_fst_5134_);
v_decide_5138_ = lean_nat_dec_eq(v_snd_5135_, v___x_5137_);
if (v_decide_5138_ == 0)
{
if (v_decide_5136_ == 0)
{
v___y_5125_ = v___y_5130_;
v___y_5126_ = v_pos_5133_;
v_snd_5127_ = v_snd_5135_;
goto v___jp_5124_;
}
else
{
uint32_t v___x_5139_; uint32_t v_c_5140_; uint8_t v___x_5141_; 
v___x_5139_ = 97;
v_c_5140_ = lean_string_utf8_get_fast(v_fst_5134_, v_snd_5135_);
v___x_5141_ = lean_uint32_dec_eq(v_c_5140_, v___x_5139_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; 
v___x_5142_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1));
v___y_5119_ = v___y_5130_;
v_snd_5120_ = v_snd_5135_;
v_pos_5121_ = v_pos_5133_;
v_err_5122_ = v___x_5142_;
goto v___jp_5118_;
}
else
{
lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5158_; 
lean_inc(v_fst_5134_);
v_isSharedCheck_5158_ = !lean_is_exclusive(v_pos_5133_);
if (v_isSharedCheck_5158_ == 0)
{
lean_object* v_unused_5159_; lean_object* v_unused_5160_; 
v_unused_5159_ = lean_ctor_get(v_pos_5133_, 1);
lean_dec(v_unused_5159_);
v_unused_5160_ = lean_ctor_get(v_pos_5133_, 0);
lean_dec(v_unused_5160_);
v___x_5144_ = v_pos_5133_;
v_isShared_5145_ = v_isSharedCheck_5158_;
goto v_resetjp_5143_;
}
else
{
lean_dec(v_pos_5133_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5158_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5146_; lean_object* v_it_x27_5148_; 
v___x_5146_ = lean_string_utf8_next_fast(v_fst_5134_, v_snd_5135_);
if (v_isShared_5145_ == 0)
{
lean_ctor_set(v___x_5144_, 1, v___x_5146_);
v_it_x27_5148_ = v___x_5144_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_fst_5134_);
lean_ctor_set(v_reuseFailAlloc_5157_, 1, v___x_5146_);
v_it_x27_5148_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
lean_object* v___x_5149_; lean_object* v___x_5150_; 
v___x_5149_ = ((lean_object*)(l_Std_Time_parseModifier___closed__35));
v___x_5150_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(v___x_5149_, v_it_x27_5148_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_object* v_pos_5151_; lean_object* v_res_5152_; lean_object* v___x_5153_; 
v_pos_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_pos_5151_);
v_res_5152_ = lean_ctor_get(v___x_5150_, 1);
lean_inc(v_res_5152_);
lean_dec_ref_known(v___x_5150_, 2);
v___x_5153_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(v_res_5152_, v_pos_5151_);
if (lean_obj_tag(v___x_5153_) == 0)
{
lean_dec(v_snd_5135_);
lean_dec_ref(v___y_5130_);
return v___x_5153_;
}
else
{
lean_object* v_pos_5154_; 
v_pos_5154_ = lean_ctor_get(v___x_5153_, 0);
lean_inc(v_pos_5154_);
v___y_5087_ = v___y_5130_;
v_snd_5088_ = v_snd_5135_;
v___y_5089_ = v___x_5153_;
v_pos_5090_ = v_pos_5154_;
goto v___jp_5086_;
}
}
else
{
lean_object* v_pos_5155_; lean_object* v_err_5156_; 
v_pos_5155_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_pos_5155_);
v_err_5156_ = lean_ctor_get(v___x_5150_, 1);
lean_inc(v_err_5156_);
lean_dec_ref_known(v___x_5150_, 2);
v___y_5119_ = v___y_5130_;
v_snd_5120_ = v_snd_5135_;
v_pos_5121_ = v_pos_5155_;
v_err_5122_ = v_err_5156_;
goto v___jp_5118_;
}
}
}
}
}
}
else
{
v___y_5125_ = v___y_5130_;
v___y_5126_ = v_pos_5133_;
v_snd_5127_ = v_snd_5135_;
goto v___jp_5124_;
}
}
}
v___jp_5161_:
{
lean_object* v___x_5166_; 
lean_inc_ref(v_pos_5164_);
v___x_5166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5166_, 0, v_pos_5164_);
lean_ctor_set(v___x_5166_, 1, v_err_5165_);
v___y_5130_ = v___y_5162_;
v_snd_5131_ = v_snd_5163_;
v___y_5132_ = v___x_5166_;
v_pos_5133_ = v_pos_5164_;
goto v___jp_5129_;
}
v___jp_5167_:
{
lean_object* v___x_5171_; 
v___x_5171_ = lean_box(0);
v___y_5162_ = v___y_5168_;
v_snd_5163_ = v_snd_5170_;
v_pos_5164_ = v___y_5169_;
v_err_5165_ = v___x_5171_;
goto v___jp_5161_;
}
v___jp_5173_:
{
lean_object* v_fst_5179_; lean_object* v_snd_5180_; uint8_t v_decide_5181_; 
v_fst_5179_ = lean_ctor_get(v_pos_5178_, 0);
v_snd_5180_ = lean_ctor_get(v_pos_5178_, 1);
lean_inc(v_snd_5180_);
v_decide_5181_ = lean_nat_dec_eq(v_snd_5174_, v_snd_5180_);
lean_dec(v_snd_5174_);
if (v_decide_5181_ == 0)
{
lean_dec(v_snd_5180_);
lean_dec_ref(v_pos_5178_);
lean_dec_ref(v___y_5176_);
lean_dec_ref(v___y_5175_);
return v___y_5177_;
}
else
{
lean_object* v___x_5182_; uint8_t v_decide_5183_; 
lean_dec_ref(v___y_5177_);
v___x_5182_ = lean_string_utf8_byte_size(v_fst_5179_);
v_decide_5183_ = lean_nat_dec_eq(v_snd_5180_, v___x_5182_);
if (v_decide_5183_ == 0)
{
if (v_decide_5181_ == 0)
{
lean_dec_ref(v___y_5176_);
v___y_5168_ = v___y_5175_;
v___y_5169_ = v_pos_5178_;
v_snd_5170_ = v_snd_5180_;
goto v___jp_5167_;
}
else
{
uint32_t v___x_5184_; uint32_t v_c_5185_; uint8_t v___x_5186_; 
v___x_5184_ = 70;
v_c_5185_ = lean_string_utf8_get_fast(v_fst_5179_, v_snd_5180_);
v___x_5186_ = lean_uint32_dec_eq(v_c_5185_, v___x_5184_);
if (v___x_5186_ == 0)
{
lean_object* v___x_5187_; 
lean_dec_ref(v___y_5176_);
v___x_5187_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1));
v___y_5162_ = v___y_5175_;
v_snd_5163_ = v_snd_5180_;
v_pos_5164_ = v_pos_5178_;
v_err_5165_ = v___x_5187_;
goto v___jp_5161_;
}
else
{
lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5203_; 
lean_inc(v_fst_5179_);
v_isSharedCheck_5203_ = !lean_is_exclusive(v_pos_5178_);
if (v_isSharedCheck_5203_ == 0)
{
lean_object* v_unused_5204_; lean_object* v_unused_5205_; 
v_unused_5204_ = lean_ctor_get(v_pos_5178_, 1);
lean_dec(v_unused_5204_);
v_unused_5205_ = lean_ctor_get(v_pos_5178_, 0);
lean_dec(v_unused_5205_);
v___x_5189_ = v_pos_5178_;
v_isShared_5190_ = v_isSharedCheck_5203_;
goto v_resetjp_5188_;
}
else
{
lean_dec(v_pos_5178_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5203_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5191_; lean_object* v_it_x27_5193_; 
v___x_5191_ = lean_string_utf8_next_fast(v_fst_5179_, v_snd_5180_);
if (v_isShared_5190_ == 0)
{
lean_ctor_set(v___x_5189_, 1, v___x_5191_);
v_it_x27_5193_ = v___x_5189_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_fst_5179_);
lean_ctor_set(v_reuseFailAlloc_5202_, 1, v___x_5191_);
v_it_x27_5193_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; 
v___x_5194_ = ((lean_object*)(l_Std_Time_parseModifier___closed__37));
v___x_5195_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(v___x_5194_, v_it_x27_5193_);
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v_pos_5196_; lean_object* v_res_5197_; lean_object* v___x_5198_; 
v_pos_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc(v_pos_5196_);
v_res_5197_ = lean_ctor_get(v___x_5195_, 1);
lean_inc(v_res_5197_);
lean_dec_ref_known(v___x_5195_, 2);
v___x_5198_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5172_, v___y_5176_, v_res_5197_, v_pos_5196_);
if (lean_obj_tag(v___x_5198_) == 0)
{
lean_dec(v_snd_5180_);
lean_dec_ref(v___y_5175_);
return v___x_5198_;
}
else
{
lean_object* v_pos_5199_; 
v_pos_5199_ = lean_ctor_get(v___x_5198_, 0);
lean_inc(v_pos_5199_);
v___y_5130_ = v___y_5175_;
v_snd_5131_ = v_snd_5180_;
v___y_5132_ = v___x_5198_;
v_pos_5133_ = v_pos_5199_;
goto v___jp_5129_;
}
}
else
{
lean_object* v_pos_5200_; lean_object* v_err_5201_; 
lean_dec_ref(v___y_5176_);
v_pos_5200_ = lean_ctor_get(v___x_5195_, 0);
lean_inc(v_pos_5200_);
v_err_5201_ = lean_ctor_get(v___x_5195_, 1);
lean_inc(v_err_5201_);
lean_dec_ref_known(v___x_5195_, 2);
v___y_5162_ = v___y_5175_;
v_snd_5163_ = v_snd_5180_;
v_pos_5164_ = v_pos_5200_;
v_err_5165_ = v_err_5201_;
goto v___jp_5161_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_5176_);
v___y_5168_ = v___y_5175_;
v___y_5169_ = v_pos_5178_;
v_snd_5170_ = v_snd_5180_;
goto v___jp_5167_;
}
}
}
v___jp_5206_:
{
lean_object* v___x_5212_; 
lean_inc_ref(v_pos_5210_);
v___x_5212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5212_, 0, v_pos_5210_);
lean_ctor_set(v___x_5212_, 1, v_err_5211_);
v_snd_5174_ = v_snd_5207_;
v___y_5175_ = v___y_5208_;
v___y_5176_ = v___y_5209_;
v___y_5177_ = v___x_5212_;
v_pos_5178_ = v_pos_5210_;
goto v___jp_5173_;
}
v___jp_5213_:
{
lean_object* v___x_5218_; 
v___x_5218_ = lean_box(0);
v_snd_5207_ = v_snd_5215_;
v___y_5208_ = v___y_5216_;
v___y_5209_ = v___y_5217_;
v_pos_5210_ = v___y_5214_;
v_err_5211_ = v___x_5218_;
goto v___jp_5206_;
}
v___jp_5220_:
{
lean_object* v_fst_5226_; lean_object* v_snd_5227_; uint8_t v_decide_5228_; 
v_fst_5226_ = lean_ctor_get(v_pos_5225_, 0);
v_snd_5227_ = lean_ctor_get(v_pos_5225_, 1);
lean_inc(v_snd_5227_);
v_decide_5228_ = lean_nat_dec_eq(v_snd_5222_, v_snd_5227_);
lean_dec(v_snd_5222_);
if (v_decide_5228_ == 0)
{
lean_dec(v_snd_5227_);
lean_dec_ref(v_pos_5225_);
lean_dec_ref(v___y_5223_);
lean_dec_ref(v___y_5221_);
return v___y_5224_;
}
else
{
lean_object* v___x_5229_; uint8_t v_decide_5230_; 
lean_dec_ref(v___y_5224_);
v___x_5229_ = lean_string_utf8_byte_size(v_fst_5226_);
v_decide_5230_ = lean_nat_dec_eq(v_snd_5227_, v___x_5229_);
if (v_decide_5230_ == 0)
{
if (v_decide_5228_ == 0)
{
v___y_5214_ = v_pos_5225_;
v_snd_5215_ = v_snd_5227_;
v___y_5216_ = v___y_5221_;
v___y_5217_ = v___y_5223_;
goto v___jp_5213_;
}
else
{
uint32_t v___x_5231_; uint32_t v_c_5232_; uint8_t v___x_5233_; 
v___x_5231_ = 99;
v_c_5232_ = lean_string_utf8_get_fast(v_fst_5226_, v_snd_5227_);
v___x_5233_ = lean_uint32_dec_eq(v_c_5232_, v___x_5231_);
if (v___x_5233_ == 0)
{
lean_object* v___x_5234_; 
v___x_5234_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1));
v_snd_5207_ = v_snd_5227_;
v___y_5208_ = v___y_5221_;
v___y_5209_ = v___y_5223_;
v_pos_5210_ = v_pos_5225_;
v_err_5211_ = v___x_5234_;
goto v___jp_5206_;
}
else
{
lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5250_; 
lean_inc(v_fst_5226_);
v_isSharedCheck_5250_ = !lean_is_exclusive(v_pos_5225_);
if (v_isSharedCheck_5250_ == 0)
{
lean_object* v_unused_5251_; lean_object* v_unused_5252_; 
v_unused_5251_ = lean_ctor_get(v_pos_5225_, 1);
lean_dec(v_unused_5251_);
v_unused_5252_ = lean_ctor_get(v_pos_5225_, 0);
lean_dec(v_unused_5252_);
v___x_5236_ = v_pos_5225_;
v_isShared_5237_ = v_isSharedCheck_5250_;
goto v_resetjp_5235_;
}
else
{
lean_dec(v_pos_5225_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5250_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5238_; lean_object* v_it_x27_5240_; 
v___x_5238_ = lean_string_utf8_next_fast(v_fst_5226_, v_snd_5227_);
if (v_isShared_5237_ == 0)
{
lean_ctor_set(v___x_5236_, 1, v___x_5238_);
v_it_x27_5240_ = v___x_5236_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_fst_5226_);
lean_ctor_set(v_reuseFailAlloc_5249_, 1, v___x_5238_);
v_it_x27_5240_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
lean_object* v___x_5241_; lean_object* v___x_5242_; 
v___x_5241_ = ((lean_object*)(l_Std_Time_parseModifier___closed__39));
v___x_5242_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(v___x_5241_, v_it_x27_5240_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_pos_5243_; lean_object* v_res_5244_; lean_object* v___x_5245_; 
v_pos_5243_ = lean_ctor_get(v___x_5242_, 0);
lean_inc(v_pos_5243_);
v_res_5244_ = lean_ctor_get(v___x_5242_, 1);
lean_inc(v_res_5244_);
lean_dec_ref_known(v___x_5242_, 2);
v___x_5245_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(v___f_5219_, v_res_5244_, v_pos_5243_);
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_dec(v_snd_5227_);
lean_dec_ref(v___y_5223_);
lean_dec_ref(v___y_5221_);
return v___x_5245_;
}
else
{
lean_object* v_pos_5246_; 
v_pos_5246_ = lean_ctor_get(v___x_5245_, 0);
lean_inc(v_pos_5246_);
v_snd_5174_ = v_snd_5227_;
v___y_5175_ = v___y_5221_;
v___y_5176_ = v___y_5223_;
v___y_5177_ = v___x_5245_;
v_pos_5178_ = v_pos_5246_;
goto v___jp_5173_;
}
}
else
{
lean_object* v_pos_5247_; lean_object* v_err_5248_; 
v_pos_5247_ = lean_ctor_get(v___x_5242_, 0);
lean_inc(v_pos_5247_);
v_err_5248_ = lean_ctor_get(v___x_5242_, 1);
lean_inc(v_err_5248_);
lean_dec_ref_known(v___x_5242_, 2);
v_snd_5207_ = v_snd_5227_;
v___y_5208_ = v___y_5221_;
v___y_5209_ = v___y_5223_;
v_pos_5210_ = v_pos_5247_;
v_err_5211_ = v_err_5248_;
goto v___jp_5206_;
}
}
}
}
}
}
else
{
v___y_5214_ = v_pos_5225_;
v_snd_5215_ = v_snd_5227_;
v___y_5216_ = v___y_5221_;
v___y_5217_ = v___y_5223_;
goto v___jp_5213_;
}
}
}
v___jp_5253_:
{
lean_object* v___x_5259_; 
lean_inc_ref(v_pos_5257_);
v___x_5259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5259_, 0, v_pos_5257_);
lean_ctor_set(v___x_5259_, 1, v_err_5258_);
v___y_5221_ = v___y_5254_;
v_snd_5222_ = v_snd_5255_;
v___y_5223_ = v___y_5256_;
v___y_5224_ = v___x_5259_;
v_pos_5225_ = v_pos_5257_;
goto v___jp_5220_;
}
v___jp_5260_:
{
lean_object* v___x_5265_; 
v___x_5265_ = lean_box(0);
v___y_5254_ = v___y_5261_;
v_snd_5255_ = v_snd_5263_;
v___y_5256_ = v___y_5264_;
v_pos_5257_ = v___y_5262_;
v_err_5258_ = v___x_5265_;
goto v___jp_5253_;
}
v___jp_5267_:
{
lean_object* v_fst_5273_; lean_object* v_snd_5274_; uint8_t v_decide_5275_; 
v_fst_5273_ = lean_ctor_get(v_pos_5272_, 0);
v_snd_5274_ = lean_ctor_get(v_pos_5272_, 1);
lean_inc(v_snd_5274_);
v_decide_5275_ = lean_nat_dec_eq(v_snd_5268_, v_snd_5274_);
lean_dec(v_snd_5268_);
if (v_decide_5275_ == 0)
{
lean_dec(v_snd_5274_);
lean_dec_ref(v_pos_5272_);
lean_dec_ref(v___y_5270_);
lean_dec_ref(v___y_5269_);
return v___y_5271_;
}
else
{
lean_object* v___x_5276_; uint8_t v_decide_5277_; 
lean_dec_ref(v___y_5271_);
v___x_5276_ = lean_string_utf8_byte_size(v_fst_5273_);
v_decide_5277_ = lean_nat_dec_eq(v_snd_5274_, v___x_5276_);
if (v_decide_5277_ == 0)
{
if (v_decide_5275_ == 0)
{
v___y_5261_ = v___y_5269_;
v___y_5262_ = v_pos_5272_;
v_snd_5263_ = v_snd_5274_;
v___y_5264_ = v___y_5270_;
goto v___jp_5260_;
}
else
{
uint32_t v___x_5278_; uint32_t v_c_5279_; uint8_t v___x_5280_; 
v___x_5278_ = 101;
v_c_5279_ = lean_string_utf8_get_fast(v_fst_5273_, v_snd_5274_);
v___x_5280_ = lean_uint32_dec_eq(v_c_5279_, v___x_5278_);
if (v___x_5280_ == 0)
{
lean_object* v___x_5281_; 
v___x_5281_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1));
v___y_5254_ = v___y_5269_;
v_snd_5255_ = v_snd_5274_;
v___y_5256_ = v___y_5270_;
v_pos_5257_ = v_pos_5272_;
v_err_5258_ = v___x_5281_;
goto v___jp_5253_;
}
else
{
lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5297_; 
lean_inc(v_fst_5273_);
v_isSharedCheck_5297_ = !lean_is_exclusive(v_pos_5272_);
if (v_isSharedCheck_5297_ == 0)
{
lean_object* v_unused_5298_; lean_object* v_unused_5299_; 
v_unused_5298_ = lean_ctor_get(v_pos_5272_, 1);
lean_dec(v_unused_5298_);
v_unused_5299_ = lean_ctor_get(v_pos_5272_, 0);
lean_dec(v_unused_5299_);
v___x_5283_ = v_pos_5272_;
v_isShared_5284_ = v_isSharedCheck_5297_;
goto v_resetjp_5282_;
}
else
{
lean_dec(v_pos_5272_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5297_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5285_; lean_object* v_it_x27_5287_; 
v___x_5285_ = lean_string_utf8_next_fast(v_fst_5273_, v_snd_5274_);
if (v_isShared_5284_ == 0)
{
lean_ctor_set(v___x_5283_, 1, v___x_5285_);
v_it_x27_5287_ = v___x_5283_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_fst_5273_);
lean_ctor_set(v_reuseFailAlloc_5296_, 1, v___x_5285_);
v_it_x27_5287_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5286_;
}
v_reusejp_5286_:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; 
v___x_5288_ = ((lean_object*)(l_Std_Time_parseModifier___closed__41));
v___x_5289_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(v___x_5288_, v_it_x27_5287_);
if (lean_obj_tag(v___x_5289_) == 0)
{
lean_object* v_pos_5290_; lean_object* v_res_5291_; lean_object* v___x_5292_; 
v_pos_5290_ = lean_ctor_get(v___x_5289_, 0);
lean_inc(v_pos_5290_);
v_res_5291_ = lean_ctor_get(v___x_5289_, 1);
lean_inc(v_res_5291_);
lean_dec_ref_known(v___x_5289_, 2);
v___x_5292_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(v___f_5266_, v_res_5291_, v_pos_5290_);
if (lean_obj_tag(v___x_5292_) == 0)
{
lean_dec(v_snd_5274_);
lean_dec_ref(v___y_5270_);
lean_dec_ref(v___y_5269_);
return v___x_5292_;
}
else
{
lean_object* v_pos_5293_; 
v_pos_5293_ = lean_ctor_get(v___x_5292_, 0);
lean_inc(v_pos_5293_);
v___y_5221_ = v___y_5269_;
v_snd_5222_ = v_snd_5274_;
v___y_5223_ = v___y_5270_;
v___y_5224_ = v___x_5292_;
v_pos_5225_ = v_pos_5293_;
goto v___jp_5220_;
}
}
else
{
lean_object* v_pos_5294_; lean_object* v_err_5295_; 
v_pos_5294_ = lean_ctor_get(v___x_5289_, 0);
lean_inc(v_pos_5294_);
v_err_5295_ = lean_ctor_get(v___x_5289_, 1);
lean_inc(v_err_5295_);
lean_dec_ref_known(v___x_5289_, 2);
v___y_5254_ = v___y_5269_;
v_snd_5255_ = v_snd_5274_;
v___y_5256_ = v___y_5270_;
v_pos_5257_ = v_pos_5294_;
v_err_5258_ = v_err_5295_;
goto v___jp_5253_;
}
}
}
}
}
}
else
{
v___y_5261_ = v___y_5269_;
v___y_5262_ = v_pos_5272_;
v_snd_5263_ = v_snd_5274_;
v___y_5264_ = v___y_5270_;
goto v___jp_5260_;
}
}
}
v___jp_5300_:
{
lean_object* v___x_5306_; 
lean_inc_ref(v_pos_5304_);
v___x_5306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5306_, 0, v_pos_5304_);
lean_ctor_set(v___x_5306_, 1, v_err_5305_);
v_snd_5268_ = v_snd_5301_;
v___y_5269_ = v___y_5302_;
v___y_5270_ = v___y_5303_;
v___y_5271_ = v___x_5306_;
v_pos_5272_ = v_pos_5304_;
goto v___jp_5267_;
}
v___jp_5307_:
{
lean_object* v___x_5312_; 
v___x_5312_ = lean_box(0);
v_snd_5301_ = v_snd_5309_;
v___y_5302_ = v___y_5310_;
v___y_5303_ = v___y_5311_;
v_pos_5304_ = v___y_5308_;
v_err_5305_ = v___x_5312_;
goto v___jp_5300_;
}
v___jp_5314_:
{
lean_object* v_fst_5320_; lean_object* v_snd_5321_; uint8_t v_decide_5322_; 
v_fst_5320_ = lean_ctor_get(v_pos_5319_, 0);
v_snd_5321_ = lean_ctor_get(v_pos_5319_, 1);
lean_inc(v_snd_5321_);
v_decide_5322_ = lean_nat_dec_eq(v___y_5316_, v_snd_5321_);
lean_dec(v___y_5316_);
if (v_decide_5322_ == 0)
{
lean_dec(v_snd_5321_);
lean_dec_ref(v_pos_5319_);
lean_dec_ref(v___y_5317_);
lean_dec_ref(v___y_5315_);
return v___y_5318_;
}
else
{
lean_object* v___x_5323_; uint8_t v_decide_5324_; 
lean_dec_ref(v___y_5318_);
v___x_5323_ = lean_string_utf8_byte_size(v_fst_5320_);
v_decide_5324_ = lean_nat_dec_eq(v_snd_5321_, v___x_5323_);
if (v_decide_5324_ == 0)
{
if (v_decide_5322_ == 0)
{
v___y_5308_ = v_pos_5319_;
v_snd_5309_ = v_snd_5321_;
v___y_5310_ = v___y_5315_;
v___y_5311_ = v___y_5317_;
goto v___jp_5307_;
}
else
{
uint32_t v___x_5325_; uint32_t v_c_5326_; uint8_t v___x_5327_; 
v___x_5325_ = 69;
v_c_5326_ = lean_string_utf8_get_fast(v_fst_5320_, v_snd_5321_);
v___x_5327_ = lean_uint32_dec_eq(v_c_5326_, v___x_5325_);
if (v___x_5327_ == 0)
{
lean_object* v___x_5328_; 
v___x_5328_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1));
v_snd_5301_ = v_snd_5321_;
v___y_5302_ = v___y_5315_;
v___y_5303_ = v___y_5317_;
v_pos_5304_ = v_pos_5319_;
v_err_5305_ = v___x_5328_;
goto v___jp_5300_;
}
else
{
lean_object* v___x_5330_; uint8_t v_isShared_5331_; uint8_t v_isSharedCheck_5344_; 
lean_inc(v_fst_5320_);
v_isSharedCheck_5344_ = !lean_is_exclusive(v_pos_5319_);
if (v_isSharedCheck_5344_ == 0)
{
lean_object* v_unused_5345_; lean_object* v_unused_5346_; 
v_unused_5345_ = lean_ctor_get(v_pos_5319_, 1);
lean_dec(v_unused_5345_);
v_unused_5346_ = lean_ctor_get(v_pos_5319_, 0);
lean_dec(v_unused_5346_);
v___x_5330_ = v_pos_5319_;
v_isShared_5331_ = v_isSharedCheck_5344_;
goto v_resetjp_5329_;
}
else
{
lean_dec(v_pos_5319_);
v___x_5330_ = lean_box(0);
v_isShared_5331_ = v_isSharedCheck_5344_;
goto v_resetjp_5329_;
}
v_resetjp_5329_:
{
lean_object* v___x_5332_; lean_object* v_it_x27_5334_; 
v___x_5332_ = lean_string_utf8_next_fast(v_fst_5320_, v_snd_5321_);
if (v_isShared_5331_ == 0)
{
lean_ctor_set(v___x_5330_, 1, v___x_5332_);
v_it_x27_5334_ = v___x_5330_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v_fst_5320_);
lean_ctor_set(v_reuseFailAlloc_5343_, 1, v___x_5332_);
v_it_x27_5334_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5335_ = ((lean_object*)(l_Std_Time_parseModifier___closed__43));
v___x_5336_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(v___x_5335_, v_it_x27_5334_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_object* v_pos_5337_; lean_object* v_res_5338_; lean_object* v___x_5339_; 
v_pos_5337_ = lean_ctor_get(v___x_5336_, 0);
lean_inc(v_pos_5337_);
v_res_5338_ = lean_ctor_get(v___x_5336_, 1);
lean_inc(v_res_5338_);
lean_dec_ref_known(v___x_5336_, 2);
v___x_5339_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(v___f_5313_, v_res_5338_, v_pos_5337_);
if (lean_obj_tag(v___x_5339_) == 0)
{
lean_dec(v_snd_5321_);
lean_dec_ref(v___y_5317_);
lean_dec_ref(v___y_5315_);
return v___x_5339_;
}
else
{
lean_object* v_pos_5340_; 
v_pos_5340_ = lean_ctor_get(v___x_5339_, 0);
lean_inc(v_pos_5340_);
v_snd_5268_ = v_snd_5321_;
v___y_5269_ = v___y_5315_;
v___y_5270_ = v___y_5317_;
v___y_5271_ = v___x_5339_;
v_pos_5272_ = v_pos_5340_;
goto v___jp_5267_;
}
}
else
{
lean_object* v_pos_5341_; lean_object* v_err_5342_; 
v_pos_5341_ = lean_ctor_get(v___x_5336_, 0);
lean_inc(v_pos_5341_);
v_err_5342_ = lean_ctor_get(v___x_5336_, 1);
lean_inc(v_err_5342_);
lean_dec_ref_known(v___x_5336_, 2);
v_snd_5301_ = v_snd_5321_;
v___y_5302_ = v___y_5315_;
v___y_5303_ = v___y_5317_;
v_pos_5304_ = v_pos_5341_;
v_err_5305_ = v_err_5342_;
goto v___jp_5300_;
}
}
}
}
}
}
else
{
v___y_5308_ = v_pos_5319_;
v_snd_5309_ = v_snd_5321_;
v___y_5310_ = v___y_5315_;
v___y_5311_ = v___y_5317_;
goto v___jp_5307_;
}
}
}
v___jp_5347_:
{
lean_object* v___x_5353_; 
lean_inc_ref(v_pos_5351_);
v___x_5353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5353_, 0, v_pos_5351_);
lean_ctor_set(v___x_5353_, 1, v_err_5352_);
v___y_5315_ = v___y_5348_;
v___y_5316_ = v___y_5349_;
v___y_5317_ = v___y_5350_;
v___y_5318_ = v___x_5353_;
v_pos_5319_ = v_pos_5351_;
goto v___jp_5314_;
}
v___jp_5354_:
{
lean_object* v___x_5359_; 
v___x_5359_ = lean_box(0);
v___y_5348_ = v___y_5355_;
v___y_5349_ = v___y_5357_;
v___y_5350_ = v___y_5358_;
v_pos_5351_ = v___y_5356_;
v_err_5352_ = v___x_5359_;
goto v___jp_5347_;
}
v___jp_5361_:
{
lean_object* v_fst_5366_; lean_object* v_snd_5367_; uint8_t v_decide_5368_; 
v_fst_5366_ = lean_ctor_get(v_pos_5365_, 0);
v_snd_5367_ = lean_ctor_get(v_pos_5365_, 1);
lean_inc(v_snd_5367_);
v_decide_5368_ = lean_nat_dec_eq(v_snd_5363_, v_snd_5367_);
lean_dec(v_snd_5363_);
if (v_decide_5368_ == 0)
{
lean_dec(v_snd_5367_);
lean_dec_ref(v_pos_5365_);
lean_dec_ref(v___y_5362_);
return v___y_5364_;
}
else
{
lean_object* v___x_5369_; lean_object* v___x_5370_; uint8_t v_decide_5371_; 
lean_dec_ref(v___y_5364_);
v___x_5369_ = ((lean_object*)(l_Std_Time_parseModifier___closed__45));
v___x_5370_ = lean_string_utf8_byte_size(v_fst_5366_);
v_decide_5371_ = lean_nat_dec_eq(v_snd_5367_, v___x_5370_);
if (v_decide_5371_ == 0)
{
if (v_decide_5368_ == 0)
{
v___y_5355_ = v___y_5362_;
v___y_5356_ = v_pos_5365_;
v___y_5357_ = v_snd_5367_;
v___y_5358_ = v___x_5369_;
goto v___jp_5354_;
}
else
{
uint32_t v___x_5372_; uint32_t v_c_5373_; uint8_t v___x_5374_; 
v___x_5372_ = 87;
v_c_5373_ = lean_string_utf8_get_fast(v_fst_5366_, v_snd_5367_);
v___x_5374_ = lean_uint32_dec_eq(v_c_5373_, v___x_5372_);
if (v___x_5374_ == 0)
{
lean_object* v___x_5375_; 
v___x_5375_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1));
v___y_5348_ = v___y_5362_;
v___y_5349_ = v_snd_5367_;
v___y_5350_ = v___x_5369_;
v_pos_5351_ = v_pos_5365_;
v_err_5352_ = v___x_5375_;
goto v___jp_5347_;
}
else
{
lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5391_; 
lean_inc(v_fst_5366_);
v_isSharedCheck_5391_ = !lean_is_exclusive(v_pos_5365_);
if (v_isSharedCheck_5391_ == 0)
{
lean_object* v_unused_5392_; lean_object* v_unused_5393_; 
v_unused_5392_ = lean_ctor_get(v_pos_5365_, 1);
lean_dec(v_unused_5392_);
v_unused_5393_ = lean_ctor_get(v_pos_5365_, 0);
lean_dec(v_unused_5393_);
v___x_5377_ = v_pos_5365_;
v_isShared_5378_ = v_isSharedCheck_5391_;
goto v_resetjp_5376_;
}
else
{
lean_dec(v_pos_5365_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5391_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5379_; lean_object* v_it_x27_5381_; 
v___x_5379_ = lean_string_utf8_next_fast(v_fst_5366_, v_snd_5367_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 1, v___x_5379_);
v_it_x27_5381_ = v___x_5377_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_fst_5366_);
lean_ctor_set(v_reuseFailAlloc_5390_, 1, v___x_5379_);
v_it_x27_5381_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
lean_object* v___x_5382_; lean_object* v___x_5383_; 
v___x_5382_ = ((lean_object*)(l_Std_Time_parseModifier___closed__46));
v___x_5383_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(v___x_5382_, v_it_x27_5381_);
if (lean_obj_tag(v___x_5383_) == 0)
{
lean_object* v_pos_5384_; lean_object* v_res_5385_; lean_object* v___x_5386_; 
v_pos_5384_ = lean_ctor_get(v___x_5383_, 0);
lean_inc(v_pos_5384_);
v_res_5385_ = lean_ctor_get(v___x_5383_, 1);
lean_inc(v_res_5385_);
lean_dec_ref_known(v___x_5383_, 2);
v___x_5386_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5360_, v___x_5369_, v_res_5385_, v_pos_5384_);
if (lean_obj_tag(v___x_5386_) == 0)
{
lean_dec(v_snd_5367_);
lean_dec_ref(v___y_5362_);
return v___x_5386_;
}
else
{
lean_object* v_pos_5387_; 
v_pos_5387_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_pos_5387_);
v___y_5315_ = v___y_5362_;
v___y_5316_ = v_snd_5367_;
v___y_5317_ = v___x_5369_;
v___y_5318_ = v___x_5386_;
v_pos_5319_ = v_pos_5387_;
goto v___jp_5314_;
}
}
else
{
lean_object* v_pos_5388_; lean_object* v_err_5389_; 
v_pos_5388_ = lean_ctor_get(v___x_5383_, 0);
lean_inc(v_pos_5388_);
v_err_5389_ = lean_ctor_get(v___x_5383_, 1);
lean_inc(v_err_5389_);
lean_dec_ref_known(v___x_5383_, 2);
v___y_5348_ = v___y_5362_;
v___y_5349_ = v_snd_5367_;
v___y_5350_ = v___x_5369_;
v_pos_5351_ = v_pos_5388_;
v_err_5352_ = v_err_5389_;
goto v___jp_5347_;
}
}
}
}
}
}
else
{
v___y_5355_ = v___y_5362_;
v___y_5356_ = v_pos_5365_;
v___y_5357_ = v_snd_5367_;
v___y_5358_ = v___x_5369_;
goto v___jp_5354_;
}
}
}
v___jp_5394_:
{
lean_object* v___x_5399_; 
lean_inc_ref(v_pos_5397_);
v___x_5399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5399_, 0, v_pos_5397_);
lean_ctor_set(v___x_5399_, 1, v_err_5398_);
v___y_5362_ = v___y_5395_;
v_snd_5363_ = v_snd_5396_;
v___y_5364_ = v___x_5399_;
v_pos_5365_ = v_pos_5397_;
goto v___jp_5361_;
}
v___jp_5400_:
{
lean_object* v___x_5404_; 
v___x_5404_ = lean_box(0);
v___y_5395_ = v___y_5401_;
v_snd_5396_ = v_snd_5403_;
v_pos_5397_ = v___y_5402_;
v_err_5398_ = v___x_5404_;
goto v___jp_5394_;
}
v___jp_5406_:
{
lean_object* v_fst_5411_; lean_object* v_snd_5412_; uint8_t v_decide_5413_; 
v_fst_5411_ = lean_ctor_get(v_pos_5410_, 0);
v_snd_5412_ = lean_ctor_get(v_pos_5410_, 1);
lean_inc(v_snd_5412_);
v_decide_5413_ = lean_nat_dec_eq(v_snd_5408_, v_snd_5412_);
lean_dec(v_snd_5408_);
if (v_decide_5413_ == 0)
{
lean_dec(v_snd_5412_);
lean_dec_ref(v_pos_5410_);
lean_dec_ref(v___y_5407_);
return v___y_5409_;
}
else
{
lean_object* v___x_5414_; uint8_t v_decide_5415_; 
lean_dec_ref(v___y_5409_);
v___x_5414_ = lean_string_utf8_byte_size(v_fst_5411_);
v_decide_5415_ = lean_nat_dec_eq(v_snd_5412_, v___x_5414_);
if (v_decide_5415_ == 0)
{
if (v_decide_5413_ == 0)
{
v___y_5401_ = v___y_5407_;
v___y_5402_ = v_pos_5410_;
v_snd_5403_ = v_snd_5412_;
goto v___jp_5400_;
}
else
{
uint32_t v___x_5416_; uint32_t v_c_5417_; uint8_t v___x_5418_; 
v___x_5416_ = 119;
v_c_5417_ = lean_string_utf8_get_fast(v_fst_5411_, v_snd_5412_);
v___x_5418_ = lean_uint32_dec_eq(v_c_5417_, v___x_5416_);
if (v___x_5418_ == 0)
{
lean_object* v___x_5419_; 
v___x_5419_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1));
v___y_5395_ = v___y_5407_;
v_snd_5396_ = v_snd_5412_;
v_pos_5397_ = v_pos_5410_;
v_err_5398_ = v___x_5419_;
goto v___jp_5394_;
}
else
{
lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5435_; 
lean_inc(v_fst_5411_);
v_isSharedCheck_5435_ = !lean_is_exclusive(v_pos_5410_);
if (v_isSharedCheck_5435_ == 0)
{
lean_object* v_unused_5436_; lean_object* v_unused_5437_; 
v_unused_5436_ = lean_ctor_get(v_pos_5410_, 1);
lean_dec(v_unused_5436_);
v_unused_5437_ = lean_ctor_get(v_pos_5410_, 0);
lean_dec(v_unused_5437_);
v___x_5421_ = v_pos_5410_;
v_isShared_5422_ = v_isSharedCheck_5435_;
goto v_resetjp_5420_;
}
else
{
lean_dec(v_pos_5410_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5435_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5423_; lean_object* v_it_x27_5425_; 
v___x_5423_ = lean_string_utf8_next_fast(v_fst_5411_, v_snd_5412_);
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 1, v___x_5423_);
v_it_x27_5425_ = v___x_5421_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_fst_5411_);
lean_ctor_set(v_reuseFailAlloc_5434_, 1, v___x_5423_);
v_it_x27_5425_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
lean_object* v___x_5426_; lean_object* v___x_5427_; 
v___x_5426_ = ((lean_object*)(l_Std_Time_parseModifier___closed__48));
v___x_5427_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(v___x_5426_, v_it_x27_5425_);
if (lean_obj_tag(v___x_5427_) == 0)
{
lean_object* v_pos_5428_; lean_object* v_res_5429_; lean_object* v___x_5430_; 
v_pos_5428_ = lean_ctor_get(v___x_5427_, 0);
lean_inc(v_pos_5428_);
v_res_5429_ = lean_ctor_get(v___x_5427_, 1);
lean_inc(v_res_5429_);
lean_dec_ref_known(v___x_5427_, 2);
lean_inc_ref(v___y_5407_);
v___x_5430_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5405_, v___y_5407_, v_res_5429_, v_pos_5428_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_dec(v_snd_5412_);
lean_dec_ref(v___y_5407_);
return v___x_5430_;
}
else
{
lean_object* v_pos_5431_; 
v_pos_5431_ = lean_ctor_get(v___x_5430_, 0);
lean_inc(v_pos_5431_);
v___y_5362_ = v___y_5407_;
v_snd_5363_ = v_snd_5412_;
v___y_5364_ = v___x_5430_;
v_pos_5365_ = v_pos_5431_;
goto v___jp_5361_;
}
}
else
{
lean_object* v_pos_5432_; lean_object* v_err_5433_; 
v_pos_5432_ = lean_ctor_get(v___x_5427_, 0);
lean_inc(v_pos_5432_);
v_err_5433_ = lean_ctor_get(v___x_5427_, 1);
lean_inc(v_err_5433_);
lean_dec_ref_known(v___x_5427_, 2);
v___y_5395_ = v___y_5407_;
v_snd_5396_ = v_snd_5412_;
v_pos_5397_ = v_pos_5432_;
v_err_5398_ = v_err_5433_;
goto v___jp_5394_;
}
}
}
}
}
}
else
{
v___y_5401_ = v___y_5407_;
v___y_5402_ = v_pos_5410_;
v_snd_5403_ = v_snd_5412_;
goto v___jp_5400_;
}
}
}
v___jp_5438_:
{
lean_object* v___x_5443_; 
lean_inc_ref(v_pos_5441_);
v___x_5443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5443_, 0, v_pos_5441_);
lean_ctor_set(v___x_5443_, 1, v_err_5442_);
v___y_5407_ = v___y_5439_;
v_snd_5408_ = v_snd_5440_;
v___y_5409_ = v___x_5443_;
v_pos_5410_ = v_pos_5441_;
goto v___jp_5406_;
}
v___jp_5444_:
{
lean_object* v___x_5448_; 
v___x_5448_ = lean_box(0);
v___y_5439_ = v___y_5445_;
v_snd_5440_ = v_snd_5447_;
v_pos_5441_ = v___y_5446_;
v_err_5442_ = v___x_5448_;
goto v___jp_5438_;
}
v___jp_5450_:
{
lean_object* v_fst_5455_; lean_object* v_snd_5456_; uint8_t v_decide_5457_; 
v_fst_5455_ = lean_ctor_get(v_pos_5454_, 0);
v_snd_5456_ = lean_ctor_get(v_pos_5454_, 1);
lean_inc(v_snd_5456_);
v_decide_5457_ = lean_nat_dec_eq(v_snd_5452_, v_snd_5456_);
lean_dec(v_snd_5452_);
if (v_decide_5457_ == 0)
{
lean_dec(v_snd_5456_);
lean_dec_ref(v_pos_5454_);
lean_dec_ref(v___y_5451_);
return v___y_5453_;
}
else
{
lean_object* v___x_5458_; uint8_t v_decide_5459_; 
lean_dec_ref(v___y_5453_);
v___x_5458_ = lean_string_utf8_byte_size(v_fst_5455_);
v_decide_5459_ = lean_nat_dec_eq(v_snd_5456_, v___x_5458_);
if (v_decide_5459_ == 0)
{
if (v_decide_5457_ == 0)
{
v___y_5445_ = v___y_5451_;
v___y_5446_ = v_pos_5454_;
v_snd_5447_ = v_snd_5456_;
goto v___jp_5444_;
}
else
{
uint32_t v___x_5460_; uint32_t v_c_5461_; uint8_t v___x_5462_; 
v___x_5460_ = 113;
v_c_5461_ = lean_string_utf8_get_fast(v_fst_5455_, v_snd_5456_);
v___x_5462_ = lean_uint32_dec_eq(v_c_5461_, v___x_5460_);
if (v___x_5462_ == 0)
{
lean_object* v___x_5463_; 
v___x_5463_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1));
v___y_5439_ = v___y_5451_;
v_snd_5440_ = v_snd_5456_;
v_pos_5441_ = v_pos_5454_;
v_err_5442_ = v___x_5463_;
goto v___jp_5438_;
}
else
{
lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5479_; 
lean_inc(v_fst_5455_);
v_isSharedCheck_5479_ = !lean_is_exclusive(v_pos_5454_);
if (v_isSharedCheck_5479_ == 0)
{
lean_object* v_unused_5480_; lean_object* v_unused_5481_; 
v_unused_5480_ = lean_ctor_get(v_pos_5454_, 1);
lean_dec(v_unused_5480_);
v_unused_5481_ = lean_ctor_get(v_pos_5454_, 0);
lean_dec(v_unused_5481_);
v___x_5465_ = v_pos_5454_;
v_isShared_5466_ = v_isSharedCheck_5479_;
goto v_resetjp_5464_;
}
else
{
lean_dec(v_pos_5454_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5479_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5467_; lean_object* v_it_x27_5469_; 
v___x_5467_ = lean_string_utf8_next_fast(v_fst_5455_, v_snd_5456_);
if (v_isShared_5466_ == 0)
{
lean_ctor_set(v___x_5465_, 1, v___x_5467_);
v_it_x27_5469_ = v___x_5465_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_fst_5455_);
lean_ctor_set(v_reuseFailAlloc_5478_, 1, v___x_5467_);
v_it_x27_5469_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
lean_object* v___x_5470_; lean_object* v___x_5471_; 
v___x_5470_ = ((lean_object*)(l_Std_Time_parseModifier___closed__50));
v___x_5471_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(v___x_5470_, v_it_x27_5469_);
if (lean_obj_tag(v___x_5471_) == 0)
{
lean_object* v_pos_5472_; lean_object* v_res_5473_; lean_object* v___x_5474_; 
v_pos_5472_ = lean_ctor_get(v___x_5471_, 0);
lean_inc(v_pos_5472_);
v_res_5473_ = lean_ctor_get(v___x_5471_, 1);
lean_inc(v_res_5473_);
lean_dec_ref_known(v___x_5471_, 2);
v___x_5474_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5449_, v_res_5473_, v_pos_5472_);
if (lean_obj_tag(v___x_5474_) == 0)
{
lean_dec(v_snd_5456_);
lean_dec_ref(v___y_5451_);
return v___x_5474_;
}
else
{
lean_object* v_pos_5475_; 
v_pos_5475_ = lean_ctor_get(v___x_5474_, 0);
lean_inc(v_pos_5475_);
v___y_5407_ = v___y_5451_;
v_snd_5408_ = v_snd_5456_;
v___y_5409_ = v___x_5474_;
v_pos_5410_ = v_pos_5475_;
goto v___jp_5406_;
}
}
else
{
lean_object* v_pos_5476_; lean_object* v_err_5477_; 
v_pos_5476_ = lean_ctor_get(v___x_5471_, 0);
lean_inc(v_pos_5476_);
v_err_5477_ = lean_ctor_get(v___x_5471_, 1);
lean_inc(v_err_5477_);
lean_dec_ref_known(v___x_5471_, 2);
v___y_5439_ = v___y_5451_;
v_snd_5440_ = v_snd_5456_;
v_pos_5441_ = v_pos_5476_;
v_err_5442_ = v_err_5477_;
goto v___jp_5438_;
}
}
}
}
}
}
else
{
v___y_5445_ = v___y_5451_;
v___y_5446_ = v_pos_5454_;
v_snd_5447_ = v_snd_5456_;
goto v___jp_5444_;
}
}
}
v___jp_5482_:
{
lean_object* v___x_5487_; 
lean_inc_ref(v_pos_5485_);
v___x_5487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5487_, 0, v_pos_5485_);
lean_ctor_set(v___x_5487_, 1, v_err_5486_);
v___y_5451_ = v___y_5483_;
v_snd_5452_ = v_snd_5484_;
v___y_5453_ = v___x_5487_;
v_pos_5454_ = v_pos_5485_;
goto v___jp_5450_;
}
v___jp_5488_:
{
lean_object* v___x_5492_; 
v___x_5492_ = lean_box(0);
v___y_5483_ = v___y_5489_;
v_snd_5484_ = v_snd_5491_;
v_pos_5485_ = v___y_5490_;
v_err_5486_ = v___x_5492_;
goto v___jp_5482_;
}
v___jp_5494_:
{
lean_object* v_fst_5499_; lean_object* v_snd_5500_; uint8_t v_decide_5501_; 
v_fst_5499_ = lean_ctor_get(v_pos_5498_, 0);
v_snd_5500_ = lean_ctor_get(v_pos_5498_, 1);
lean_inc(v_snd_5500_);
v_decide_5501_ = lean_nat_dec_eq(v___y_5495_, v_snd_5500_);
lean_dec(v___y_5495_);
if (v_decide_5501_ == 0)
{
lean_dec(v_snd_5500_);
lean_dec_ref(v_pos_5498_);
lean_dec_ref(v___y_5496_);
return v___y_5497_;
}
else
{
lean_object* v___x_5502_; uint8_t v_decide_5503_; 
lean_dec_ref(v___y_5497_);
v___x_5502_ = lean_string_utf8_byte_size(v_fst_5499_);
v_decide_5503_ = lean_nat_dec_eq(v_snd_5500_, v___x_5502_);
if (v_decide_5503_ == 0)
{
if (v_decide_5501_ == 0)
{
v___y_5489_ = v___y_5496_;
v___y_5490_ = v_pos_5498_;
v_snd_5491_ = v_snd_5500_;
goto v___jp_5488_;
}
else
{
uint32_t v___x_5504_; uint32_t v_c_5505_; uint8_t v___x_5506_; 
v___x_5504_ = 81;
v_c_5505_ = lean_string_utf8_get_fast(v_fst_5499_, v_snd_5500_);
v___x_5506_ = lean_uint32_dec_eq(v_c_5505_, v___x_5504_);
if (v___x_5506_ == 0)
{
lean_object* v___x_5507_; 
v___x_5507_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1));
v___y_5483_ = v___y_5496_;
v_snd_5484_ = v_snd_5500_;
v_pos_5485_ = v_pos_5498_;
v_err_5486_ = v___x_5507_;
goto v___jp_5482_;
}
else
{
lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5523_; 
lean_inc(v_fst_5499_);
v_isSharedCheck_5523_ = !lean_is_exclusive(v_pos_5498_);
if (v_isSharedCheck_5523_ == 0)
{
lean_object* v_unused_5524_; lean_object* v_unused_5525_; 
v_unused_5524_ = lean_ctor_get(v_pos_5498_, 1);
lean_dec(v_unused_5524_);
v_unused_5525_ = lean_ctor_get(v_pos_5498_, 0);
lean_dec(v_unused_5525_);
v___x_5509_ = v_pos_5498_;
v_isShared_5510_ = v_isSharedCheck_5523_;
goto v_resetjp_5508_;
}
else
{
lean_dec(v_pos_5498_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5523_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5511_; lean_object* v_it_x27_5513_; 
v___x_5511_ = lean_string_utf8_next_fast(v_fst_5499_, v_snd_5500_);
if (v_isShared_5510_ == 0)
{
lean_ctor_set(v___x_5509_, 1, v___x_5511_);
v_it_x27_5513_ = v___x_5509_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_fst_5499_);
lean_ctor_set(v_reuseFailAlloc_5522_, 1, v___x_5511_);
v_it_x27_5513_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5514_ = ((lean_object*)(l_Std_Time_parseModifier___closed__52));
v___x_5515_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(v___x_5514_, v_it_x27_5513_);
if (lean_obj_tag(v___x_5515_) == 0)
{
lean_object* v_pos_5516_; lean_object* v_res_5517_; lean_object* v___x_5518_; 
v_pos_5516_ = lean_ctor_get(v___x_5515_, 0);
lean_inc(v_pos_5516_);
v_res_5517_ = lean_ctor_get(v___x_5515_, 1);
lean_inc(v_res_5517_);
lean_dec_ref_known(v___x_5515_, 2);
v___x_5518_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5493_, v_res_5517_, v_pos_5516_);
if (lean_obj_tag(v___x_5518_) == 0)
{
lean_dec(v_snd_5500_);
lean_dec_ref(v___y_5496_);
return v___x_5518_;
}
else
{
lean_object* v_pos_5519_; 
v_pos_5519_ = lean_ctor_get(v___x_5518_, 0);
lean_inc(v_pos_5519_);
v___y_5451_ = v___y_5496_;
v_snd_5452_ = v_snd_5500_;
v___y_5453_ = v___x_5518_;
v_pos_5454_ = v_pos_5519_;
goto v___jp_5450_;
}
}
else
{
lean_object* v_pos_5520_; lean_object* v_err_5521_; 
v_pos_5520_ = lean_ctor_get(v___x_5515_, 0);
lean_inc(v_pos_5520_);
v_err_5521_ = lean_ctor_get(v___x_5515_, 1);
lean_inc(v_err_5521_);
lean_dec_ref_known(v___x_5515_, 2);
v___y_5483_ = v___y_5496_;
v_snd_5484_ = v_snd_5500_;
v_pos_5485_ = v_pos_5520_;
v_err_5486_ = v_err_5521_;
goto v___jp_5482_;
}
}
}
}
}
}
else
{
v___y_5489_ = v___y_5496_;
v___y_5490_ = v_pos_5498_;
v_snd_5491_ = v_snd_5500_;
goto v___jp_5488_;
}
}
}
v___jp_5526_:
{
lean_object* v___x_5531_; 
lean_inc_ref(v_pos_5529_);
v___x_5531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5531_, 0, v_pos_5529_);
lean_ctor_set(v___x_5531_, 1, v_err_5530_);
v___y_5495_ = v___y_5527_;
v___y_5496_ = v___y_5528_;
v___y_5497_ = v___x_5531_;
v_pos_5498_ = v_pos_5529_;
goto v___jp_5494_;
}
v___jp_5532_:
{
lean_object* v___x_5536_; 
v___x_5536_ = lean_box(0);
v___y_5527_ = v___y_5533_;
v___y_5528_ = v___y_5534_;
v_pos_5529_ = v___y_5535_;
v_err_5530_ = v___x_5536_;
goto v___jp_5526_;
}
v___jp_5538_:
{
lean_object* v_fst_5542_; lean_object* v_snd_5543_; uint8_t v_decide_5544_; 
v_fst_5542_ = lean_ctor_get(v_pos_5541_, 0);
v_snd_5543_ = lean_ctor_get(v_pos_5541_, 1);
lean_inc(v_snd_5543_);
v_decide_5544_ = lean_nat_dec_eq(v_snd_5539_, v_snd_5543_);
lean_dec(v_snd_5539_);
if (v_decide_5544_ == 0)
{
lean_dec(v_snd_5543_);
lean_dec_ref(v_pos_5541_);
return v___y_5540_;
}
else
{
lean_object* v___x_5545_; lean_object* v___x_5546_; uint8_t v_decide_5547_; 
lean_dec_ref(v___y_5540_);
v___x_5545_ = ((lean_object*)(l_Std_Time_parseModifier___closed__54));
v___x_5546_ = lean_string_utf8_byte_size(v_fst_5542_);
v_decide_5547_ = lean_nat_dec_eq(v_snd_5543_, v___x_5546_);
if (v_decide_5547_ == 0)
{
if (v_decide_5544_ == 0)
{
v___y_5533_ = v_snd_5543_;
v___y_5534_ = v___x_5545_;
v___y_5535_ = v_pos_5541_;
goto v___jp_5532_;
}
else
{
uint32_t v___x_5548_; uint32_t v_c_5549_; uint8_t v___x_5550_; 
v___x_5548_ = 100;
v_c_5549_ = lean_string_utf8_get_fast(v_fst_5542_, v_snd_5543_);
v___x_5550_ = lean_uint32_dec_eq(v_c_5549_, v___x_5548_);
if (v___x_5550_ == 0)
{
lean_object* v___x_5551_; 
v___x_5551_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1));
v___y_5527_ = v_snd_5543_;
v___y_5528_ = v___x_5545_;
v_pos_5529_ = v_pos_5541_;
v_err_5530_ = v___x_5551_;
goto v___jp_5526_;
}
else
{
lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5567_; 
lean_inc(v_fst_5542_);
v_isSharedCheck_5567_ = !lean_is_exclusive(v_pos_5541_);
if (v_isSharedCheck_5567_ == 0)
{
lean_object* v_unused_5568_; lean_object* v_unused_5569_; 
v_unused_5568_ = lean_ctor_get(v_pos_5541_, 1);
lean_dec(v_unused_5568_);
v_unused_5569_ = lean_ctor_get(v_pos_5541_, 0);
lean_dec(v_unused_5569_);
v___x_5553_ = v_pos_5541_;
v_isShared_5554_ = v_isSharedCheck_5567_;
goto v_resetjp_5552_;
}
else
{
lean_dec(v_pos_5541_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5567_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5555_; lean_object* v_it_x27_5557_; 
v___x_5555_ = lean_string_utf8_next_fast(v_fst_5542_, v_snd_5543_);
if (v_isShared_5554_ == 0)
{
lean_ctor_set(v___x_5553_, 1, v___x_5555_);
v_it_x27_5557_ = v___x_5553_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_fst_5542_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v___x_5555_);
v_it_x27_5557_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
lean_object* v___x_5558_; lean_object* v___x_5559_; 
v___x_5558_ = ((lean_object*)(l_Std_Time_parseModifier___closed__55));
v___x_5559_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(v___x_5558_, v_it_x27_5557_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_object* v_pos_5560_; lean_object* v_res_5561_; lean_object* v___x_5562_; 
v_pos_5560_ = lean_ctor_get(v___x_5559_, 0);
lean_inc(v_pos_5560_);
v_res_5561_ = lean_ctor_get(v___x_5559_, 1);
lean_inc(v_res_5561_);
lean_dec_ref_known(v___x_5559_, 2);
v___x_5562_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5537_, v___x_5545_, v_res_5561_, v_pos_5560_);
if (lean_obj_tag(v___x_5562_) == 0)
{
lean_dec(v_snd_5543_);
return v___x_5562_;
}
else
{
lean_object* v_pos_5563_; 
v_pos_5563_ = lean_ctor_get(v___x_5562_, 0);
lean_inc(v_pos_5563_);
v___y_5495_ = v_snd_5543_;
v___y_5496_ = v___x_5545_;
v___y_5497_ = v___x_5562_;
v_pos_5498_ = v_pos_5563_;
goto v___jp_5494_;
}
}
else
{
lean_object* v_pos_5564_; lean_object* v_err_5565_; 
v_pos_5564_ = lean_ctor_get(v___x_5559_, 0);
lean_inc(v_pos_5564_);
v_err_5565_ = lean_ctor_get(v___x_5559_, 1);
lean_inc(v_err_5565_);
lean_dec_ref_known(v___x_5559_, 2);
v___y_5527_ = v_snd_5543_;
v___y_5528_ = v___x_5545_;
v_pos_5529_ = v_pos_5564_;
v_err_5530_ = v_err_5565_;
goto v___jp_5526_;
}
}
}
}
}
}
else
{
v___y_5533_ = v_snd_5543_;
v___y_5534_ = v___x_5545_;
v___y_5535_ = v_pos_5541_;
goto v___jp_5532_;
}
}
}
v___jp_5570_:
{
lean_object* v___x_5574_; 
lean_inc_ref(v_pos_5572_);
v___x_5574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5574_, 0, v_pos_5572_);
lean_ctor_set(v___x_5574_, 1, v_err_5573_);
v_snd_5539_ = v_snd_5571_;
v___y_5540_ = v___x_5574_;
v_pos_5541_ = v_pos_5572_;
goto v___jp_5538_;
}
v___jp_5575_:
{
lean_object* v___x_5578_; 
v___x_5578_ = lean_box(0);
v_snd_5571_ = v_snd_5577_;
v_pos_5572_ = v___y_5576_;
v_err_5573_ = v___x_5578_;
goto v___jp_5570_;
}
v___jp_5580_:
{
lean_object* v_fst_5584_; lean_object* v_snd_5585_; uint8_t v_decide_5586_; 
v_fst_5584_ = lean_ctor_get(v_pos_5583_, 0);
v_snd_5585_ = lean_ctor_get(v_pos_5583_, 1);
lean_inc(v_snd_5585_);
v_decide_5586_ = lean_nat_dec_eq(v_snd_5581_, v_snd_5585_);
lean_dec(v_snd_5581_);
if (v_decide_5586_ == 0)
{
lean_dec(v_snd_5585_);
lean_dec_ref(v_pos_5583_);
return v___y_5582_;
}
else
{
lean_object* v___x_5587_; uint8_t v_decide_5588_; 
lean_dec_ref(v___y_5582_);
v___x_5587_ = lean_string_utf8_byte_size(v_fst_5584_);
v_decide_5588_ = lean_nat_dec_eq(v_snd_5585_, v___x_5587_);
if (v_decide_5588_ == 0)
{
if (v_decide_5586_ == 0)
{
v___y_5576_ = v_pos_5583_;
v_snd_5577_ = v_snd_5585_;
goto v___jp_5575_;
}
else
{
uint32_t v___x_5589_; uint32_t v_c_5590_; uint8_t v___x_5591_; 
v___x_5589_ = 76;
v_c_5590_ = lean_string_utf8_get_fast(v_fst_5584_, v_snd_5585_);
v___x_5591_ = lean_uint32_dec_eq(v_c_5590_, v___x_5589_);
if (v___x_5591_ == 0)
{
lean_object* v___x_5592_; 
v___x_5592_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1));
v_snd_5571_ = v_snd_5585_;
v_pos_5572_ = v_pos_5583_;
v_err_5573_ = v___x_5592_;
goto v___jp_5570_;
}
else
{
lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5608_; 
lean_inc(v_fst_5584_);
v_isSharedCheck_5608_ = !lean_is_exclusive(v_pos_5583_);
if (v_isSharedCheck_5608_ == 0)
{
lean_object* v_unused_5609_; lean_object* v_unused_5610_; 
v_unused_5609_ = lean_ctor_get(v_pos_5583_, 1);
lean_dec(v_unused_5609_);
v_unused_5610_ = lean_ctor_get(v_pos_5583_, 0);
lean_dec(v_unused_5610_);
v___x_5594_ = v_pos_5583_;
v_isShared_5595_ = v_isSharedCheck_5608_;
goto v_resetjp_5593_;
}
else
{
lean_dec(v_pos_5583_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5608_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5596_; lean_object* v_it_x27_5598_; 
v___x_5596_ = lean_string_utf8_next_fast(v_fst_5584_, v_snd_5585_);
if (v_isShared_5595_ == 0)
{
lean_ctor_set(v___x_5594_, 1, v___x_5596_);
v_it_x27_5598_ = v___x_5594_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_fst_5584_);
lean_ctor_set(v_reuseFailAlloc_5607_, 1, v___x_5596_);
v_it_x27_5598_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
lean_object* v___x_5599_; lean_object* v___x_5600_; 
v___x_5599_ = ((lean_object*)(l_Std_Time_parseModifier___closed__57));
v___x_5600_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(v___x_5599_, v_it_x27_5598_);
if (lean_obj_tag(v___x_5600_) == 0)
{
lean_object* v_pos_5601_; lean_object* v_res_5602_; lean_object* v___x_5603_; 
v_pos_5601_ = lean_ctor_get(v___x_5600_, 0);
lean_inc(v_pos_5601_);
v_res_5602_ = lean_ctor_get(v___x_5600_, 1);
lean_inc(v_res_5602_);
lean_dec_ref_known(v___x_5600_, 2);
v___x_5603_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5579_, v_res_5602_, v_pos_5601_);
if (lean_obj_tag(v___x_5603_) == 0)
{
lean_dec(v_snd_5585_);
return v___x_5603_;
}
else
{
lean_object* v_pos_5604_; 
v_pos_5604_ = lean_ctor_get(v___x_5603_, 0);
lean_inc(v_pos_5604_);
v_snd_5539_ = v_snd_5585_;
v___y_5540_ = v___x_5603_;
v_pos_5541_ = v_pos_5604_;
goto v___jp_5538_;
}
}
else
{
lean_object* v_pos_5605_; lean_object* v_err_5606_; 
v_pos_5605_ = lean_ctor_get(v___x_5600_, 0);
lean_inc(v_pos_5605_);
v_err_5606_ = lean_ctor_get(v___x_5600_, 1);
lean_inc(v_err_5606_);
lean_dec_ref_known(v___x_5600_, 2);
v_snd_5571_ = v_snd_5585_;
v_pos_5572_ = v_pos_5605_;
v_err_5573_ = v_err_5606_;
goto v___jp_5570_;
}
}
}
}
}
}
else
{
v___y_5576_ = v_pos_5583_;
v_snd_5577_ = v_snd_5585_;
goto v___jp_5575_;
}
}
}
v___jp_5611_:
{
lean_object* v___x_5615_; 
lean_inc_ref(v_pos_5613_);
v___x_5615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5615_, 0, v_pos_5613_);
lean_ctor_set(v___x_5615_, 1, v_err_5614_);
v_snd_5581_ = v_snd_5612_;
v___y_5582_ = v___x_5615_;
v_pos_5583_ = v_pos_5613_;
goto v___jp_5580_;
}
v___jp_5616_:
{
lean_object* v___x_5619_; 
v___x_5619_ = lean_box(0);
v_snd_5612_ = v_snd_5618_;
v_pos_5613_ = v___y_5617_;
v_err_5614_ = v___x_5619_;
goto v___jp_5611_;
}
v___jp_5621_:
{
lean_object* v_fst_5625_; lean_object* v_snd_5626_; uint8_t v_decide_5627_; 
v_fst_5625_ = lean_ctor_get(v_pos_5624_, 0);
v_snd_5626_ = lean_ctor_get(v_pos_5624_, 1);
lean_inc(v_snd_5626_);
v_decide_5627_ = lean_nat_dec_eq(v_snd_5622_, v_snd_5626_);
lean_dec(v_snd_5622_);
if (v_decide_5627_ == 0)
{
lean_dec(v_snd_5626_);
lean_dec_ref(v_pos_5624_);
return v___y_5623_;
}
else
{
lean_object* v___x_5628_; uint8_t v_decide_5629_; 
lean_dec_ref(v___y_5623_);
v___x_5628_ = lean_string_utf8_byte_size(v_fst_5625_);
v_decide_5629_ = lean_nat_dec_eq(v_snd_5626_, v___x_5628_);
if (v_decide_5629_ == 0)
{
if (v_decide_5627_ == 0)
{
v___y_5617_ = v_pos_5624_;
v_snd_5618_ = v_snd_5626_;
goto v___jp_5616_;
}
else
{
uint32_t v___x_5630_; uint32_t v_c_5631_; uint8_t v___x_5632_; 
v___x_5630_ = 77;
v_c_5631_ = lean_string_utf8_get_fast(v_fst_5625_, v_snd_5626_);
v___x_5632_ = lean_uint32_dec_eq(v_c_5631_, v___x_5630_);
if (v___x_5632_ == 0)
{
lean_object* v___x_5633_; 
v___x_5633_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1));
v_snd_5612_ = v_snd_5626_;
v_pos_5613_ = v_pos_5624_;
v_err_5614_ = v___x_5633_;
goto v___jp_5611_;
}
else
{
lean_object* v___x_5635_; uint8_t v_isShared_5636_; uint8_t v_isSharedCheck_5649_; 
lean_inc(v_fst_5625_);
v_isSharedCheck_5649_ = !lean_is_exclusive(v_pos_5624_);
if (v_isSharedCheck_5649_ == 0)
{
lean_object* v_unused_5650_; lean_object* v_unused_5651_; 
v_unused_5650_ = lean_ctor_get(v_pos_5624_, 1);
lean_dec(v_unused_5650_);
v_unused_5651_ = lean_ctor_get(v_pos_5624_, 0);
lean_dec(v_unused_5651_);
v___x_5635_ = v_pos_5624_;
v_isShared_5636_ = v_isSharedCheck_5649_;
goto v_resetjp_5634_;
}
else
{
lean_dec(v_pos_5624_);
v___x_5635_ = lean_box(0);
v_isShared_5636_ = v_isSharedCheck_5649_;
goto v_resetjp_5634_;
}
v_resetjp_5634_:
{
lean_object* v___x_5637_; lean_object* v_it_x27_5639_; 
v___x_5637_ = lean_string_utf8_next_fast(v_fst_5625_, v_snd_5626_);
if (v_isShared_5636_ == 0)
{
lean_ctor_set(v___x_5635_, 1, v___x_5637_);
v_it_x27_5639_ = v___x_5635_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_fst_5625_);
lean_ctor_set(v_reuseFailAlloc_5648_, 1, v___x_5637_);
v_it_x27_5639_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
lean_object* v___x_5640_; lean_object* v___x_5641_; 
v___x_5640_ = ((lean_object*)(l_Std_Time_parseModifier___closed__59));
v___x_5641_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(v___x_5640_, v_it_x27_5639_);
if (lean_obj_tag(v___x_5641_) == 0)
{
lean_object* v_pos_5642_; lean_object* v_res_5643_; lean_object* v___x_5644_; 
v_pos_5642_ = lean_ctor_get(v___x_5641_, 0);
lean_inc(v_pos_5642_);
v_res_5643_ = lean_ctor_get(v___x_5641_, 1);
lean_inc(v_res_5643_);
lean_dec_ref_known(v___x_5641_, 2);
v___x_5644_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5620_, v_res_5643_, v_pos_5642_);
if (lean_obj_tag(v___x_5644_) == 0)
{
lean_dec(v_snd_5626_);
return v___x_5644_;
}
else
{
lean_object* v_pos_5645_; 
v_pos_5645_ = lean_ctor_get(v___x_5644_, 0);
lean_inc(v_pos_5645_);
v_snd_5581_ = v_snd_5626_;
v___y_5582_ = v___x_5644_;
v_pos_5583_ = v_pos_5645_;
goto v___jp_5580_;
}
}
else
{
lean_object* v_pos_5646_; lean_object* v_err_5647_; 
v_pos_5646_ = lean_ctor_get(v___x_5641_, 0);
lean_inc(v_pos_5646_);
v_err_5647_ = lean_ctor_get(v___x_5641_, 1);
lean_inc(v_err_5647_);
lean_dec_ref_known(v___x_5641_, 2);
v_snd_5612_ = v_snd_5626_;
v_pos_5613_ = v_pos_5646_;
v_err_5614_ = v_err_5647_;
goto v___jp_5611_;
}
}
}
}
}
}
else
{
v___y_5617_ = v_pos_5624_;
v_snd_5618_ = v_snd_5626_;
goto v___jp_5616_;
}
}
}
v___jp_5652_:
{
lean_object* v___x_5656_; 
lean_inc_ref(v_pos_5654_);
v___x_5656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5656_, 0, v_pos_5654_);
lean_ctor_set(v___x_5656_, 1, v_err_5655_);
v_snd_5622_ = v_snd_5653_;
v___y_5623_ = v___x_5656_;
v_pos_5624_ = v_pos_5654_;
goto v___jp_5621_;
}
v___jp_5657_:
{
lean_object* v___x_5660_; 
v___x_5660_ = lean_box(0);
v_snd_5653_ = v_snd_5659_;
v_pos_5654_ = v___y_5658_;
v_err_5655_ = v___x_5660_;
goto v___jp_5652_;
}
v___jp_5662_:
{
lean_object* v_fst_5666_; lean_object* v_snd_5667_; uint8_t v_decide_5668_; 
v_fst_5666_ = lean_ctor_get(v_pos_5665_, 0);
v_snd_5667_ = lean_ctor_get(v_pos_5665_, 1);
lean_inc(v_snd_5667_);
v_decide_5668_ = lean_nat_dec_eq(v_snd_5663_, v_snd_5667_);
lean_dec(v_snd_5663_);
if (v_decide_5668_ == 0)
{
lean_dec(v_snd_5667_);
lean_dec_ref(v_pos_5665_);
return v___y_5664_;
}
else
{
lean_object* v___x_5669_; uint8_t v_decide_5670_; 
lean_dec_ref(v___y_5664_);
v___x_5669_ = lean_string_utf8_byte_size(v_fst_5666_);
v_decide_5670_ = lean_nat_dec_eq(v_snd_5667_, v___x_5669_);
if (v_decide_5670_ == 0)
{
if (v_decide_5668_ == 0)
{
v___y_5658_ = v_pos_5665_;
v_snd_5659_ = v_snd_5667_;
goto v___jp_5657_;
}
else
{
uint32_t v___x_5671_; uint32_t v_c_5672_; uint8_t v___x_5673_; 
v___x_5671_ = 68;
v_c_5672_ = lean_string_utf8_get_fast(v_fst_5666_, v_snd_5667_);
v___x_5673_ = lean_uint32_dec_eq(v_c_5672_, v___x_5671_);
if (v___x_5673_ == 0)
{
lean_object* v___x_5674_; 
v___x_5674_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1));
v_snd_5653_ = v_snd_5667_;
v_pos_5654_ = v_pos_5665_;
v_err_5655_ = v___x_5674_;
goto v___jp_5652_;
}
else
{
lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5691_; 
lean_inc(v_fst_5666_);
v_isSharedCheck_5691_ = !lean_is_exclusive(v_pos_5665_);
if (v_isSharedCheck_5691_ == 0)
{
lean_object* v_unused_5692_; lean_object* v_unused_5693_; 
v_unused_5692_ = lean_ctor_get(v_pos_5665_, 1);
lean_dec(v_unused_5692_);
v_unused_5693_ = lean_ctor_get(v_pos_5665_, 0);
lean_dec(v_unused_5693_);
v___x_5676_ = v_pos_5665_;
v_isShared_5677_ = v_isSharedCheck_5691_;
goto v_resetjp_5675_;
}
else
{
lean_dec(v_pos_5665_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5691_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5678_; lean_object* v_it_x27_5680_; 
v___x_5678_ = lean_string_utf8_next_fast(v_fst_5666_, v_snd_5667_);
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 1, v___x_5678_);
v_it_x27_5680_ = v___x_5676_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v_fst_5666_);
lean_ctor_set(v_reuseFailAlloc_5690_, 1, v___x_5678_);
v_it_x27_5680_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
lean_object* v___x_5681_; lean_object* v___x_5682_; 
v___x_5681_ = ((lean_object*)(l_Std_Time_parseModifier___closed__61));
v___x_5682_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(v___x_5681_, v_it_x27_5680_);
if (lean_obj_tag(v___x_5682_) == 0)
{
lean_object* v_pos_5683_; lean_object* v_res_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; 
v_pos_5683_ = lean_ctor_get(v___x_5682_, 0);
lean_inc(v_pos_5683_);
v_res_5684_ = lean_ctor_get(v___x_5682_, 1);
lean_inc(v_res_5684_);
lean_dec_ref_known(v___x_5682_, 2);
v___x_5685_ = ((lean_object*)(l_Std_Time_parseModifier___closed__62));
v___x_5686_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5661_, v___x_5685_, v_res_5684_, v_pos_5683_);
if (lean_obj_tag(v___x_5686_) == 0)
{
lean_dec(v_snd_5667_);
return v___x_5686_;
}
else
{
lean_object* v_pos_5687_; 
v_pos_5687_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_pos_5687_);
v_snd_5622_ = v_snd_5667_;
v___y_5623_ = v___x_5686_;
v_pos_5624_ = v_pos_5687_;
goto v___jp_5621_;
}
}
else
{
lean_object* v_pos_5688_; lean_object* v_err_5689_; 
v_pos_5688_ = lean_ctor_get(v___x_5682_, 0);
lean_inc(v_pos_5688_);
v_err_5689_ = lean_ctor_get(v___x_5682_, 1);
lean_inc(v_err_5689_);
lean_dec_ref_known(v___x_5682_, 2);
v_snd_5653_ = v_snd_5667_;
v_pos_5654_ = v_pos_5688_;
v_err_5655_ = v_err_5689_;
goto v___jp_5652_;
}
}
}
}
}
}
else
{
v___y_5658_ = v_pos_5665_;
v_snd_5659_ = v_snd_5667_;
goto v___jp_5657_;
}
}
}
v___jp_5694_:
{
lean_object* v___x_5698_; 
lean_inc_ref(v_pos_5696_);
v___x_5698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5698_, 0, v_pos_5696_);
lean_ctor_set(v___x_5698_, 1, v_err_5697_);
v_snd_5663_ = v_snd_5695_;
v___y_5664_ = v___x_5698_;
v_pos_5665_ = v_pos_5696_;
goto v___jp_5662_;
}
v___jp_5699_:
{
lean_object* v___x_5702_; 
v___x_5702_ = lean_box(0);
v_snd_5695_ = v_snd_5701_;
v_pos_5696_ = v___y_5700_;
v_err_5697_ = v___x_5702_;
goto v___jp_5694_;
}
v___jp_5704_:
{
lean_object* v_fst_5708_; lean_object* v_snd_5709_; uint8_t v_decide_5710_; 
v_fst_5708_ = lean_ctor_get(v_pos_5707_, 0);
v_snd_5709_ = lean_ctor_get(v_pos_5707_, 1);
lean_inc(v_snd_5709_);
v_decide_5710_ = lean_nat_dec_eq(v_snd_5705_, v_snd_5709_);
lean_dec(v_snd_5705_);
if (v_decide_5710_ == 0)
{
lean_dec(v_snd_5709_);
lean_dec_ref(v_pos_5707_);
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
v___y_5700_ = v_pos_5707_;
v_snd_5701_ = v_snd_5709_;
goto v___jp_5699_;
}
else
{
uint32_t v___x_5713_; uint32_t v_c_5714_; uint8_t v___x_5715_; 
v___x_5713_ = 117;
v_c_5714_ = lean_string_utf8_get_fast(v_fst_5708_, v_snd_5709_);
v___x_5715_ = lean_uint32_dec_eq(v_c_5714_, v___x_5713_);
if (v___x_5715_ == 0)
{
lean_object* v___x_5716_; 
v___x_5716_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1));
v_snd_5695_ = v_snd_5709_;
v_pos_5696_ = v_pos_5707_;
v_err_5697_ = v___x_5716_;
goto v___jp_5694_;
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
v___x_5723_ = ((lean_object*)(l_Std_Time_parseModifier___closed__64));
v___x_5724_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(v___x_5723_, v_it_x27_5722_);
if (lean_obj_tag(v___x_5724_) == 0)
{
lean_object* v_pos_5725_; lean_object* v_res_5726_; lean_object* v___x_5727_; 
v_pos_5725_ = lean_ctor_get(v___x_5724_, 0);
lean_inc(v_pos_5725_);
v_res_5726_ = lean_ctor_get(v___x_5724_, 1);
lean_inc(v_res_5726_);
lean_dec_ref_known(v___x_5724_, 2);
v___x_5727_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5703_, v_res_5726_, v_pos_5725_);
if (lean_obj_tag(v___x_5727_) == 0)
{
lean_dec(v_snd_5709_);
return v___x_5727_;
}
else
{
lean_object* v_pos_5728_; 
v_pos_5728_ = lean_ctor_get(v___x_5727_, 0);
lean_inc(v_pos_5728_);
v_snd_5663_ = v_snd_5709_;
v___y_5664_ = v___x_5727_;
v_pos_5665_ = v_pos_5728_;
goto v___jp_5662_;
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
v_snd_5695_ = v_snd_5709_;
v_pos_5696_ = v_pos_5729_;
v_err_5697_ = v_err_5730_;
goto v___jp_5694_;
}
}
}
}
}
}
else
{
v___y_5700_ = v_pos_5707_;
v_snd_5701_ = v_snd_5709_;
goto v___jp_5699_;
}
}
}
v___jp_5735_:
{
lean_object* v___x_5739_; 
lean_inc_ref(v_pos_5737_);
v___x_5739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5739_, 0, v_pos_5737_);
lean_ctor_set(v___x_5739_, 1, v_err_5738_);
v_snd_5705_ = v_snd_5736_;
v___y_5706_ = v___x_5739_;
v_pos_5707_ = v_pos_5737_;
goto v___jp_5704_;
}
v___jp_5740_:
{
lean_object* v___x_5743_; 
v___x_5743_ = lean_box(0);
v_snd_5736_ = v_snd_5742_;
v_pos_5737_ = v___y_5741_;
v_err_5738_ = v___x_5743_;
goto v___jp_5735_;
}
v___jp_5745_:
{
lean_object* v_fst_5749_; lean_object* v_snd_5750_; uint8_t v_decide_5751_; 
v_fst_5749_ = lean_ctor_get(v_pos_5748_, 0);
v_snd_5750_ = lean_ctor_get(v_pos_5748_, 1);
lean_inc(v_snd_5750_);
v_decide_5751_ = lean_nat_dec_eq(v_snd_5746_, v_snd_5750_);
lean_dec(v_snd_5746_);
if (v_decide_5751_ == 0)
{
lean_dec(v_snd_5750_);
lean_dec_ref(v_pos_5748_);
return v___y_5747_;
}
else
{
lean_object* v___x_5752_; uint8_t v_decide_5753_; 
lean_dec_ref(v___y_5747_);
v___x_5752_ = lean_string_utf8_byte_size(v_fst_5749_);
v_decide_5753_ = lean_nat_dec_eq(v_snd_5750_, v___x_5752_);
if (v_decide_5753_ == 0)
{
if (v_decide_5751_ == 0)
{
v___y_5741_ = v_pos_5748_;
v_snd_5742_ = v_snd_5750_;
goto v___jp_5740_;
}
else
{
uint32_t v___x_5754_; uint32_t v_c_5755_; uint8_t v___x_5756_; 
v___x_5754_ = 89;
v_c_5755_ = lean_string_utf8_get_fast(v_fst_5749_, v_snd_5750_);
v___x_5756_ = lean_uint32_dec_eq(v_c_5755_, v___x_5754_);
if (v___x_5756_ == 0)
{
lean_object* v___x_5757_; 
v___x_5757_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1));
v_snd_5736_ = v_snd_5750_;
v_pos_5737_ = v_pos_5748_;
v_err_5738_ = v___x_5757_;
goto v___jp_5735_;
}
else
{
lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5773_; 
lean_inc(v_fst_5749_);
v_isSharedCheck_5773_ = !lean_is_exclusive(v_pos_5748_);
if (v_isSharedCheck_5773_ == 0)
{
lean_object* v_unused_5774_; lean_object* v_unused_5775_; 
v_unused_5774_ = lean_ctor_get(v_pos_5748_, 1);
lean_dec(v_unused_5774_);
v_unused_5775_ = lean_ctor_get(v_pos_5748_, 0);
lean_dec(v_unused_5775_);
v___x_5759_ = v_pos_5748_;
v_isShared_5760_ = v_isSharedCheck_5773_;
goto v_resetjp_5758_;
}
else
{
lean_dec(v_pos_5748_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5773_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5761_; lean_object* v_it_x27_5763_; 
v___x_5761_ = lean_string_utf8_next_fast(v_fst_5749_, v_snd_5750_);
if (v_isShared_5760_ == 0)
{
lean_ctor_set(v___x_5759_, 1, v___x_5761_);
v_it_x27_5763_ = v___x_5759_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_fst_5749_);
lean_ctor_set(v_reuseFailAlloc_5772_, 1, v___x_5761_);
v_it_x27_5763_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
lean_object* v___x_5764_; lean_object* v___x_5765_; 
v___x_5764_ = ((lean_object*)(l_Std_Time_parseModifier___closed__66));
v___x_5765_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(v___x_5764_, v_it_x27_5763_);
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v_pos_5766_; lean_object* v_res_5767_; lean_object* v___x_5768_; 
v_pos_5766_ = lean_ctor_get(v___x_5765_, 0);
lean_inc(v_pos_5766_);
v_res_5767_ = lean_ctor_get(v___x_5765_, 1);
lean_inc(v_res_5767_);
lean_dec_ref_known(v___x_5765_, 2);
v___x_5768_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5744_, v_res_5767_, v_pos_5766_);
if (lean_obj_tag(v___x_5768_) == 0)
{
lean_dec(v_snd_5750_);
return v___x_5768_;
}
else
{
lean_object* v_pos_5769_; 
v_pos_5769_ = lean_ctor_get(v___x_5768_, 0);
lean_inc(v_pos_5769_);
v_snd_5705_ = v_snd_5750_;
v___y_5706_ = v___x_5768_;
v_pos_5707_ = v_pos_5769_;
goto v___jp_5704_;
}
}
else
{
lean_object* v_pos_5770_; lean_object* v_err_5771_; 
v_pos_5770_ = lean_ctor_get(v___x_5765_, 0);
lean_inc(v_pos_5770_);
v_err_5771_ = lean_ctor_get(v___x_5765_, 1);
lean_inc(v_err_5771_);
lean_dec_ref_known(v___x_5765_, 2);
v_snd_5736_ = v_snd_5750_;
v_pos_5737_ = v_pos_5770_;
v_err_5738_ = v_err_5771_;
goto v___jp_5735_;
}
}
}
}
}
}
else
{
v___y_5741_ = v_pos_5748_;
v_snd_5742_ = v_snd_5750_;
goto v___jp_5740_;
}
}
}
v___jp_5776_:
{
lean_object* v___x_5780_; 
lean_inc_ref(v_pos_5778_);
v___x_5780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5780_, 0, v_pos_5778_);
lean_ctor_set(v___x_5780_, 1, v_err_5779_);
v_snd_5746_ = v_snd_5777_;
v___y_5747_ = v___x_5780_;
v_pos_5748_ = v_pos_5778_;
goto v___jp_5745_;
}
v___jp_5781_:
{
lean_object* v___x_5784_; 
v___x_5784_ = lean_box(0);
v_snd_5777_ = v_snd_5783_;
v_pos_5778_ = v___y_5782_;
v_err_5779_ = v___x_5784_;
goto v___jp_5776_;
}
v___jp_5786_:
{
lean_object* v_fst_5789_; lean_object* v_snd_5790_; uint8_t v_decide_5791_; 
v_fst_5789_ = lean_ctor_get(v_pos_5788_, 0);
v_snd_5790_ = lean_ctor_get(v_pos_5788_, 1);
lean_inc(v_snd_5790_);
v_decide_5791_ = lean_nat_dec_eq(v_snd_4324_, v_snd_5790_);
lean_dec(v_snd_4324_);
if (v_decide_5791_ == 0)
{
lean_dec(v_snd_5790_);
lean_dec_ref(v_pos_5788_);
return v___y_5787_;
}
else
{
lean_object* v___x_5792_; uint8_t v_decide_5793_; 
lean_dec_ref(v___y_5787_);
v___x_5792_ = lean_string_utf8_byte_size(v_fst_5789_);
v_decide_5793_ = lean_nat_dec_eq(v_snd_5790_, v___x_5792_);
if (v_decide_5793_ == 0)
{
if (v_decide_5791_ == 0)
{
v___y_5782_ = v_pos_5788_;
v_snd_5783_ = v_snd_5790_;
goto v___jp_5781_;
}
else
{
uint32_t v___x_5794_; uint32_t v_c_5795_; uint8_t v___x_5796_; 
v___x_5794_ = 121;
v_c_5795_ = lean_string_utf8_get_fast(v_fst_5789_, v_snd_5790_);
v___x_5796_ = lean_uint32_dec_eq(v_c_5795_, v___x_5794_);
if (v___x_5796_ == 0)
{
lean_object* v___x_5797_; 
v___x_5797_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1));
v_snd_5777_ = v_snd_5790_;
v_pos_5778_ = v_pos_5788_;
v_err_5779_ = v___x_5797_;
goto v___jp_5776_;
}
else
{
lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5813_; 
lean_inc(v_fst_5789_);
v_isSharedCheck_5813_ = !lean_is_exclusive(v_pos_5788_);
if (v_isSharedCheck_5813_ == 0)
{
lean_object* v_unused_5814_; lean_object* v_unused_5815_; 
v_unused_5814_ = lean_ctor_get(v_pos_5788_, 1);
lean_dec(v_unused_5814_);
v_unused_5815_ = lean_ctor_get(v_pos_5788_, 0);
lean_dec(v_unused_5815_);
v___x_5799_ = v_pos_5788_;
v_isShared_5800_ = v_isSharedCheck_5813_;
goto v_resetjp_5798_;
}
else
{
lean_dec(v_pos_5788_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5813_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v___x_5801_; lean_object* v_it_x27_5803_; 
v___x_5801_ = lean_string_utf8_next_fast(v_fst_5789_, v_snd_5790_);
if (v_isShared_5800_ == 0)
{
lean_ctor_set(v___x_5799_, 1, v___x_5801_);
v_it_x27_5803_ = v___x_5799_;
goto v_reusejp_5802_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v_fst_5789_);
lean_ctor_set(v_reuseFailAlloc_5812_, 1, v___x_5801_);
v_it_x27_5803_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5802_;
}
v_reusejp_5802_:
{
lean_object* v___x_5804_; lean_object* v___x_5805_; 
v___x_5804_ = ((lean_object*)(l_Std_Time_parseModifier___closed__68));
v___x_5805_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(v___x_5804_, v_it_x27_5803_);
if (lean_obj_tag(v___x_5805_) == 0)
{
lean_object* v_pos_5806_; lean_object* v_res_5807_; lean_object* v___x_5808_; 
v_pos_5806_ = lean_ctor_get(v___x_5805_, 0);
lean_inc(v_pos_5806_);
v_res_5807_ = lean_ctor_get(v___x_5805_, 1);
lean_inc(v_res_5807_);
lean_dec_ref_known(v___x_5805_, 2);
v___x_5808_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5785_, v_res_5807_, v_pos_5806_);
if (lean_obj_tag(v___x_5808_) == 0)
{
lean_dec(v_snd_5790_);
return v___x_5808_;
}
else
{
lean_object* v_pos_5809_; 
v_pos_5809_ = lean_ctor_get(v___x_5808_, 0);
lean_inc(v_pos_5809_);
v_snd_5746_ = v_snd_5790_;
v___y_5747_ = v___x_5808_;
v_pos_5748_ = v_pos_5809_;
goto v___jp_5745_;
}
}
else
{
lean_object* v_pos_5810_; lean_object* v_err_5811_; 
v_pos_5810_ = lean_ctor_get(v___x_5805_, 0);
lean_inc(v_pos_5810_);
v_err_5811_ = lean_ctor_get(v___x_5805_, 1);
lean_inc(v_err_5811_);
lean_dec_ref_known(v___x_5805_, 2);
v_snd_5777_ = v_snd_5790_;
v_pos_5778_ = v_pos_5810_;
v_err_5779_ = v_err_5811_;
goto v___jp_5776_;
}
}
}
}
}
}
else
{
v___y_5782_ = v_pos_5788_;
v_snd_5783_ = v_snd_5790_;
goto v___jp_5781_;
}
}
}
v___jp_5816_:
{
lean_object* v___x_5819_; 
lean_inc_ref(v_pos_5817_);
v___x_5819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5819_, 0, v_pos_5817_);
lean_ctor_set(v___x_5819_, 1, v_err_5818_);
v___y_5787_ = v___x_5819_;
v_pos_5788_ = v_pos_5817_;
goto v___jp_5786_;
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
