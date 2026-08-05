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
uint8_t v_x_233__boxed_140_; lean_object* v_res_141_; 
v_x_233__boxed_140_ = lean_unbox(v_x_138_);
v_res_141_ = l_Std_Time_instReprText_repr(v_x_233__boxed_140_, v_prec_139_);
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
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_nat_dec_eq(v_num_471_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(2u);
v___x_478_ = lean_nat_dec_eq(v_num_471_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(4u);
v___x_480_ = lean_nat_dec_eq(v_num_471_, v___x_479_);
if (v___x_480_ == 0)
{
uint8_t v___x_481_; 
v___x_481_ = lean_nat_dec_lt(v___x_479_, v_num_471_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(3u);
v___x_483_ = lean_nat_dec_eq(v_num_471_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec(v_num_471_);
v___x_484_ = lean_box(0);
return v___x_484_;
}
else
{
goto v___jp_472_;
}
}
else
{
goto v___jp_472_;
}
}
else
{
lean_object* v___x_485_; 
lean_dec(v_num_471_);
v___x_485_ = ((lean_object*)(l_Std_Time_Year_classify___closed__0));
return v___x_485_;
}
}
else
{
lean_object* v___x_486_; 
lean_dec(v_num_471_);
v___x_486_ = ((lean_object*)(l_Std_Time_Year_classify___closed__1));
return v___x_486_;
}
}
else
{
lean_object* v___x_487_; 
lean_dec(v_num_471_);
v___x_487_ = ((lean_object*)(l_Std_Time_Year_classify___closed__2));
return v___x_487_;
}
v___jp_472_:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_473_, 0, v_num_471_);
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx(uint8_t v_x_488_){
_start:
{
switch(v_x_488_)
{
case 0:
{
lean_object* v___x_489_; 
v___x_489_ = lean_unsigned_to_nat(0u);
return v___x_489_;
}
case 1:
{
lean_object* v___x_490_; 
v___x_490_ = lean_unsigned_to_nat(1u);
return v___x_490_;
}
default: 
{
lean_object* v___x_491_; 
v___x_491_ = lean_unsigned_to_nat(2u);
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx___boxed(lean_object* v_x_492_){
_start:
{
uint8_t v_x_boxed_493_; lean_object* v_res_494_; 
v_x_boxed_493_ = lean_unbox(v_x_492_);
v_res_494_ = l_Std_Time_ZoneId_ctorIdx(v_x_boxed_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___redArg(lean_object* v_k_495_){
_start:
{
lean_inc(v_k_495_);
return v_k_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___redArg___boxed(lean_object* v_k_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_Time_ZoneId_ctorElim___redArg(v_k_496_);
lean_dec(v_k_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim(lean_object* v_motive_498_, lean_object* v_ctorIdx_499_, uint8_t v_t_500_, lean_object* v_h_501_, lean_object* v_k_502_){
_start:
{
lean_inc(v_k_502_);
return v_k_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___boxed(lean_object* v_motive_503_, lean_object* v_ctorIdx_504_, lean_object* v_t_505_, lean_object* v_h_506_, lean_object* v_k_507_){
_start:
{
uint8_t v_t_boxed_508_; lean_object* v_res_509_; 
v_t_boxed_508_ = lean_unbox(v_t_505_);
v_res_509_ = l_Std_Time_ZoneId_ctorElim(v_motive_503_, v_ctorIdx_504_, v_t_boxed_508_, v_h_506_, v_k_507_);
lean_dec(v_k_507_);
lean_dec(v_ctorIdx_504_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg(lean_object* v_unknown_510_){
_start:
{
lean_inc(v_unknown_510_);
return v_unknown_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg___boxed(lean_object* v_unknown_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_Time_ZoneId_unknown_elim___redArg(v_unknown_511_);
lean_dec(v_unknown_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim(lean_object* v_motive_513_, uint8_t v_t_514_, lean_object* v_h_515_, lean_object* v_unknown_516_){
_start:
{
lean_inc(v_unknown_516_);
return v_unknown_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___boxed(lean_object* v_motive_517_, lean_object* v_t_518_, lean_object* v_h_519_, lean_object* v_unknown_520_){
_start:
{
uint8_t v_t_boxed_521_; lean_object* v_res_522_; 
v_t_boxed_521_ = lean_unbox(v_t_518_);
v_res_522_ = l_Std_Time_ZoneId_unknown_elim(v_motive_517_, v_t_boxed_521_, v_h_519_, v_unknown_520_);
lean_dec(v_unknown_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg(lean_object* v_short_523_){
_start:
{
lean_inc(v_short_523_);
return v_short_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg___boxed(lean_object* v_short_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_Time_ZoneId_short_elim___redArg(v_short_524_);
lean_dec(v_short_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim(lean_object* v_motive_526_, uint8_t v_t_527_, lean_object* v_h_528_, lean_object* v_short_529_){
_start:
{
lean_inc(v_short_529_);
return v_short_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___boxed(lean_object* v_motive_530_, lean_object* v_t_531_, lean_object* v_h_532_, lean_object* v_short_533_){
_start:
{
uint8_t v_t_boxed_534_; lean_object* v_res_535_; 
v_t_boxed_534_ = lean_unbox(v_t_531_);
v_res_535_ = l_Std_Time_ZoneId_short_elim(v_motive_530_, v_t_boxed_534_, v_h_532_, v_short_533_);
lean_dec(v_short_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg(lean_object* v_full_536_){
_start:
{
lean_inc(v_full_536_);
return v_full_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg___boxed(lean_object* v_full_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Time_ZoneId_full_elim___redArg(v_full_537_);
lean_dec(v_full_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim(lean_object* v_motive_539_, uint8_t v_t_540_, lean_object* v_h_541_, lean_object* v_full_542_){
_start:
{
lean_inc(v_full_542_);
return v_full_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___boxed(lean_object* v_motive_543_, lean_object* v_t_544_, lean_object* v_h_545_, lean_object* v_full_546_){
_start:
{
uint8_t v_t_boxed_547_; lean_object* v_res_548_; 
v_t_boxed_547_ = lean_unbox(v_t_544_);
v_res_548_ = l_Std_Time_ZoneId_full_elim(v_motive_543_, v_t_boxed_547_, v_h_545_, v_full_546_);
lean_dec(v_full_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr(uint8_t v_x_558_, lean_object* v_prec_559_){
_start:
{
lean_object* v___y_561_; lean_object* v___y_568_; lean_object* v___y_575_; 
switch(v_x_558_)
{
case 0:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(1024u);
v___x_582_ = lean_nat_dec_le(v___x_581_, v_prec_559_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_561_ = v___x_583_;
goto v___jp_560_;
}
else
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_561_ = v___x_584_;
goto v___jp_560_;
}
}
case 1:
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = lean_unsigned_to_nat(1024u);
v___x_586_ = lean_nat_dec_le(v___x_585_, v_prec_559_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_568_ = v___x_587_;
goto v___jp_567_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_568_ = v___x_588_;
goto v___jp_567_;
}
}
default: 
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(1024u);
v___x_590_ = lean_nat_dec_le(v___x_589_, v_prec_559_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_575_ = v___x_591_;
goto v___jp_574_;
}
else
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_575_ = v___x_592_;
goto v___jp_574_;
}
}
}
v___jp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_562_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__1));
lean_inc(v___y_561_);
v___x_563_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_563_, 0, v___y_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = 0;
v___x_565_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*1, v___x_564_);
v___x_566_ = l_Repr_addAppParen(v___x_565_, v_prec_559_);
return v___x_566_;
}
v___jp_567_:
{
lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_569_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__3));
lean_inc(v___y_568_);
v___x_570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = 0;
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_571_);
v___x_573_ = l_Repr_addAppParen(v___x_572_, v_prec_559_);
return v___x_573_;
}
v___jp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_576_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__5));
lean_inc(v___y_575_);
v___x_577_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_577_, 0, v___y_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = 0;
v___x_579_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*1, v___x_578_);
v___x_580_ = l_Repr_addAppParen(v___x_579_, v_prec_559_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr___boxed(lean_object* v_x_593_, lean_object* v_prec_594_){
_start:
{
uint8_t v_x_173__boxed_595_; lean_object* v_res_596_; 
v_x_173__boxed_595_ = lean_unbox(v_x_593_);
v_res_596_ = l_Std_Time_instReprZoneId_repr(v_x_173__boxed_595_, v_prec_594_);
lean_dec(v_prec_594_);
return v_res_596_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneId_default(void){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = 0;
return v___x_599_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneId(void){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = 0;
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify(lean_object* v_num_610_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_dec_eq(v_num_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(2u);
v___x_614_ = lean_nat_dec_eq(v_num_610_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(4u);
v___x_616_ = lean_nat_dec_eq(v_num_610_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
v___x_617_ = lean_box(0);
return v___x_617_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__0));
return v___x_618_;
}
}
else
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__1));
return v___x_619_;
}
}
else
{
lean_object* v___x_620_; 
v___x_620_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__2));
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify___boxed(lean_object* v_num_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Std_Time_ZoneId_classify(v_num_621_);
lean_dec(v_num_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx(uint8_t v_x_623_){
_start:
{
if (v_x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_unsigned_to_nat(0u);
return v___x_624_;
}
else
{
lean_object* v___x_625_; 
v___x_625_ = lean_unsigned_to_nat(1u);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx___boxed(lean_object* v_x_626_){
_start:
{
uint8_t v_x_boxed_627_; lean_object* v_res_628_; 
v_x_boxed_627_ = lean_unbox(v_x_626_);
v_res_628_ = l_Std_Time_ZoneName_ctorIdx(v_x_boxed_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg(lean_object* v_k_629_){
_start:
{
lean_inc(v_k_629_);
return v_k_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg___boxed(lean_object* v_k_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_Time_ZoneName_ctorElim___redArg(v_k_630_);
lean_dec(v_k_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim(lean_object* v_motive_632_, lean_object* v_ctorIdx_633_, uint8_t v_t_634_, lean_object* v_h_635_, lean_object* v_k_636_){
_start:
{
lean_inc(v_k_636_);
return v_k_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___boxed(lean_object* v_motive_637_, lean_object* v_ctorIdx_638_, lean_object* v_t_639_, lean_object* v_h_640_, lean_object* v_k_641_){
_start:
{
uint8_t v_t_boxed_642_; lean_object* v_res_643_; 
v_t_boxed_642_ = lean_unbox(v_t_639_);
v_res_643_ = l_Std_Time_ZoneName_ctorElim(v_motive_637_, v_ctorIdx_638_, v_t_boxed_642_, v_h_640_, v_k_641_);
lean_dec(v_k_641_);
lean_dec(v_ctorIdx_638_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg(lean_object* v_short_644_){
_start:
{
lean_inc(v_short_644_);
return v_short_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg___boxed(lean_object* v_short_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_Time_ZoneName_short_elim___redArg(v_short_645_);
lean_dec(v_short_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim(lean_object* v_motive_647_, uint8_t v_t_648_, lean_object* v_h_649_, lean_object* v_short_650_){
_start:
{
lean_inc(v_short_650_);
return v_short_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___boxed(lean_object* v_motive_651_, lean_object* v_t_652_, lean_object* v_h_653_, lean_object* v_short_654_){
_start:
{
uint8_t v_t_boxed_655_; lean_object* v_res_656_; 
v_t_boxed_655_ = lean_unbox(v_t_652_);
v_res_656_ = l_Std_Time_ZoneName_short_elim(v_motive_651_, v_t_boxed_655_, v_h_653_, v_short_654_);
lean_dec(v_short_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg(lean_object* v_full_657_){
_start:
{
lean_inc(v_full_657_);
return v_full_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg___boxed(lean_object* v_full_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Time_ZoneName_full_elim___redArg(v_full_658_);
lean_dec(v_full_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim(lean_object* v_motive_660_, uint8_t v_t_661_, lean_object* v_h_662_, lean_object* v_full_663_){
_start:
{
lean_inc(v_full_663_);
return v_full_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___boxed(lean_object* v_motive_664_, lean_object* v_t_665_, lean_object* v_h_666_, lean_object* v_full_667_){
_start:
{
uint8_t v_t_boxed_668_; lean_object* v_res_669_; 
v_t_boxed_668_ = lean_unbox(v_t_665_);
v_res_669_ = l_Std_Time_ZoneName_full_elim(v_motive_664_, v_t_boxed_668_, v_h_666_, v_full_667_);
lean_dec(v_full_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr(uint8_t v_x_676_, lean_object* v_prec_677_){
_start:
{
lean_object* v___y_679_; lean_object* v___y_686_; 
if (v_x_676_ == 0)
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(1024u);
v___x_693_ = lean_nat_dec_le(v___x_692_, v_prec_677_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
v___x_694_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_679_ = v___x_694_;
goto v___jp_678_;
}
else
{
lean_object* v___x_695_; 
v___x_695_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_679_ = v___x_695_;
goto v___jp_678_;
}
}
else
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_unsigned_to_nat(1024u);
v___x_697_ = lean_nat_dec_le(v___x_696_, v_prec_677_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
v___x_698_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_686_ = v___x_698_;
goto v___jp_685_;
}
else
{
lean_object* v___x_699_; 
v___x_699_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_686_ = v___x_699_;
goto v___jp_685_;
}
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_680_ = ((lean_object*)(l_Std_Time_instReprZoneName_repr___closed__1));
lean_inc(v___y_679_);
v___x_681_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_681_, 0, v___y_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = 0;
v___x_683_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*1, v___x_682_);
v___x_684_ = l_Repr_addAppParen(v___x_683_, v_prec_677_);
return v___x_684_;
}
v___jp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_687_ = ((lean_object*)(l_Std_Time_instReprZoneName_repr___closed__3));
lean_inc(v___y_686_);
v___x_688_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_688_, 0, v___y_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = 0;
v___x_690_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*1, v___x_689_);
v___x_691_ = l_Repr_addAppParen(v___x_690_, v_prec_677_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr___boxed(lean_object* v_x_700_, lean_object* v_prec_701_){
_start:
{
uint8_t v_x_117__boxed_702_; lean_object* v_res_703_; 
v_x_117__boxed_702_ = lean_unbox(v_x_700_);
v_res_703_ = l_Std_Time_instReprZoneName_repr(v_x_117__boxed_702_, v_prec_701_);
lean_dec(v_prec_701_);
return v_res_703_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneName_default(void){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = 0;
return v___x_706_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneName(void){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = 0;
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify(uint32_t v_letter_714_, lean_object* v_num_715_){
_start:
{
uint32_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = 122;
v___x_717_ = lean_uint32_dec_eq(v_letter_714_, v___x_716_);
if (v___x_717_ == 0)
{
uint32_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = 118;
v___x_719_ = lean_uint32_dec_eq(v_letter_714_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
v___x_720_ = lean_box(0);
return v___x_720_;
}
else
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_dec_eq(v_num_715_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(4u);
v___x_724_ = lean_nat_dec_eq(v_num_715_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_box(0);
return v___x_725_;
}
else
{
lean_object* v___x_726_; 
v___x_726_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__0));
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; 
v___x_727_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__1));
return v___x_727_;
}
}
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_unsigned_to_nat(4u);
v___x_729_ = lean_nat_dec_lt(v_num_715_, v___x_728_);
if (v___x_729_ == 0)
{
uint8_t v___x_730_; 
v___x_730_ = lean_nat_dec_eq(v_num_715_, v___x_728_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(0);
return v___x_731_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__0));
return v___x_732_;
}
}
else
{
lean_object* v___x_733_; 
v___x_733_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__1));
return v___x_733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify___boxed(lean_object* v_letter_734_, lean_object* v_num_735_){
_start:
{
uint32_t v_letter_boxed_736_; lean_object* v_res_737_; 
v_letter_boxed_736_ = lean_unbox_uint32(v_letter_734_);
lean_dec(v_letter_734_);
v_res_737_ = l_Std_Time_ZoneName_classify(v_letter_boxed_736_, v_num_735_);
lean_dec(v_num_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx(uint8_t v_x_738_){
_start:
{
switch(v_x_738_)
{
case 0:
{
lean_object* v___x_739_; 
v___x_739_ = lean_unsigned_to_nat(0u);
return v___x_739_;
}
case 1:
{
lean_object* v___x_740_; 
v___x_740_ = lean_unsigned_to_nat(1u);
return v___x_740_;
}
case 2:
{
lean_object* v___x_741_; 
v___x_741_ = lean_unsigned_to_nat(2u);
return v___x_741_;
}
case 3:
{
lean_object* v___x_742_; 
v___x_742_ = lean_unsigned_to_nat(3u);
return v___x_742_;
}
default: 
{
lean_object* v___x_743_; 
v___x_743_ = lean_unsigned_to_nat(4u);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx___boxed(lean_object* v_x_744_){
_start:
{
uint8_t v_x_boxed_745_; lean_object* v_res_746_; 
v_x_boxed_745_ = lean_unbox(v_x_744_);
v_res_746_ = l_Std_Time_OffsetX_ctorIdx(v_x_boxed_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg(lean_object* v_k_747_){
_start:
{
lean_inc(v_k_747_);
return v_k_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg___boxed(lean_object* v_k_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_Time_OffsetX_ctorElim___redArg(v_k_748_);
lean_dec(v_k_748_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim(lean_object* v_motive_750_, lean_object* v_ctorIdx_751_, uint8_t v_t_752_, lean_object* v_h_753_, lean_object* v_k_754_){
_start:
{
lean_inc(v_k_754_);
return v_k_754_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___boxed(lean_object* v_motive_755_, lean_object* v_ctorIdx_756_, lean_object* v_t_757_, lean_object* v_h_758_, lean_object* v_k_759_){
_start:
{
uint8_t v_t_boxed_760_; lean_object* v_res_761_; 
v_t_boxed_760_ = lean_unbox(v_t_757_);
v_res_761_ = l_Std_Time_OffsetX_ctorElim(v_motive_755_, v_ctorIdx_756_, v_t_boxed_760_, v_h_758_, v_k_759_);
lean_dec(v_k_759_);
lean_dec(v_ctorIdx_756_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg(lean_object* v_hour_762_){
_start:
{
lean_inc(v_hour_762_);
return v_hour_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg___boxed(lean_object* v_hour_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_Time_OffsetX_hour_elim___redArg(v_hour_763_);
lean_dec(v_hour_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim(lean_object* v_motive_765_, uint8_t v_t_766_, lean_object* v_h_767_, lean_object* v_hour_768_){
_start:
{
lean_inc(v_hour_768_);
return v_hour_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___boxed(lean_object* v_motive_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_hour_772_){
_start:
{
uint8_t v_t_boxed_773_; lean_object* v_res_774_; 
v_t_boxed_773_ = lean_unbox(v_t_770_);
v_res_774_ = l_Std_Time_OffsetX_hour_elim(v_motive_769_, v_t_boxed_773_, v_h_771_, v_hour_772_);
lean_dec(v_hour_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg(lean_object* v_hourMinute_775_){
_start:
{
lean_inc(v_hourMinute_775_);
return v_hourMinute_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg___boxed(lean_object* v_hourMinute_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_Time_OffsetX_hourMinute_elim___redArg(v_hourMinute_776_);
lean_dec(v_hourMinute_776_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim(lean_object* v_motive_778_, uint8_t v_t_779_, lean_object* v_h_780_, lean_object* v_hourMinute_781_){
_start:
{
lean_inc(v_hourMinute_781_);
return v_hourMinute_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___boxed(lean_object* v_motive_782_, lean_object* v_t_783_, lean_object* v_h_784_, lean_object* v_hourMinute_785_){
_start:
{
uint8_t v_t_boxed_786_; lean_object* v_res_787_; 
v_t_boxed_786_ = lean_unbox(v_t_783_);
v_res_787_ = l_Std_Time_OffsetX_hourMinute_elim(v_motive_782_, v_t_boxed_786_, v_h_784_, v_hourMinute_785_);
lean_dec(v_hourMinute_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(lean_object* v_hourMinuteColon_788_){
_start:
{
lean_inc(v_hourMinuteColon_788_);
return v_hourMinuteColon_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg___boxed(lean_object* v_hourMinuteColon_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(v_hourMinuteColon_789_);
lean_dec(v_hourMinuteColon_789_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim(lean_object* v_motive_791_, uint8_t v_t_792_, lean_object* v_h_793_, lean_object* v_hourMinuteColon_794_){
_start:
{
lean_inc(v_hourMinuteColon_794_);
return v_hourMinuteColon_794_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___boxed(lean_object* v_motive_795_, lean_object* v_t_796_, lean_object* v_h_797_, lean_object* v_hourMinuteColon_798_){
_start:
{
uint8_t v_t_boxed_799_; lean_object* v_res_800_; 
v_t_boxed_799_ = lean_unbox(v_t_796_);
v_res_800_ = l_Std_Time_OffsetX_hourMinuteColon_elim(v_motive_795_, v_t_boxed_799_, v_h_797_, v_hourMinuteColon_798_);
lean_dec(v_hourMinuteColon_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(lean_object* v_hourMinuteSecond_801_){
_start:
{
lean_inc(v_hourMinuteSecond_801_);
return v_hourMinuteSecond_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg___boxed(lean_object* v_hourMinuteSecond_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(v_hourMinuteSecond_802_);
lean_dec(v_hourMinuteSecond_802_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim(lean_object* v_motive_804_, uint8_t v_t_805_, lean_object* v_h_806_, lean_object* v_hourMinuteSecond_807_){
_start:
{
lean_inc(v_hourMinuteSecond_807_);
return v_hourMinuteSecond_807_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___boxed(lean_object* v_motive_808_, lean_object* v_t_809_, lean_object* v_h_810_, lean_object* v_hourMinuteSecond_811_){
_start:
{
uint8_t v_t_boxed_812_; lean_object* v_res_813_; 
v_t_boxed_812_ = lean_unbox(v_t_809_);
v_res_813_ = l_Std_Time_OffsetX_hourMinuteSecond_elim(v_motive_808_, v_t_boxed_812_, v_h_810_, v_hourMinuteSecond_811_);
lean_dec(v_hourMinuteSecond_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(lean_object* v_hourMinuteSecondColon_814_){
_start:
{
lean_inc(v_hourMinuteSecondColon_814_);
return v_hourMinuteSecondColon_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg___boxed(lean_object* v_hourMinuteSecondColon_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(v_hourMinuteSecondColon_815_);
lean_dec(v_hourMinuteSecondColon_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim(lean_object* v_motive_817_, uint8_t v_t_818_, lean_object* v_h_819_, lean_object* v_hourMinuteSecondColon_820_){
_start:
{
lean_inc(v_hourMinuteSecondColon_820_);
return v_hourMinuteSecondColon_820_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___boxed(lean_object* v_motive_821_, lean_object* v_t_822_, lean_object* v_h_823_, lean_object* v_hourMinuteSecondColon_824_){
_start:
{
uint8_t v_t_boxed_825_; lean_object* v_res_826_; 
v_t_boxed_825_ = lean_unbox(v_t_822_);
v_res_826_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim(v_motive_821_, v_t_boxed_825_, v_h_823_, v_hourMinuteSecondColon_824_);
lean_dec(v_hourMinuteSecondColon_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr(uint8_t v_x_842_, lean_object* v_prec_843_){
_start:
{
lean_object* v___y_845_; lean_object* v___y_852_; lean_object* v___y_859_; lean_object* v___y_866_; lean_object* v___y_873_; 
switch(v_x_842_)
{
case 0:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(1024u);
v___x_880_ = lean_nat_dec_le(v___x_879_, v_prec_843_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
v___x_881_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_845_ = v___x_881_;
goto v___jp_844_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_845_ = v___x_882_;
goto v___jp_844_;
}
}
case 1:
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(1024u);
v___x_884_ = lean_nat_dec_le(v___x_883_, v_prec_843_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_852_ = v___x_885_;
goto v___jp_851_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_852_ = v___x_886_;
goto v___jp_851_;
}
}
case 2:
{
lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_887_ = lean_unsigned_to_nat(1024u);
v___x_888_ = lean_nat_dec_le(v___x_887_, v_prec_843_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
v___x_889_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_859_ = v___x_889_;
goto v___jp_858_;
}
else
{
lean_object* v___x_890_; 
v___x_890_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_859_ = v___x_890_;
goto v___jp_858_;
}
}
case 3:
{
lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_891_ = lean_unsigned_to_nat(1024u);
v___x_892_ = lean_nat_dec_le(v___x_891_, v_prec_843_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_866_ = v___x_893_;
goto v___jp_865_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_866_ = v___x_894_;
goto v___jp_865_;
}
}
default: 
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(1024u);
v___x_896_ = lean_nat_dec_le(v___x_895_, v_prec_843_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_873_ = v___x_897_;
goto v___jp_872_;
}
else
{
lean_object* v___x_898_; 
v___x_898_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_873_ = v___x_898_;
goto v___jp_872_;
}
}
}
v___jp_844_:
{
lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_846_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__1));
lean_inc(v___y_845_);
v___x_847_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_847_, 0, v___y_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = 0;
v___x_849_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*1, v___x_848_);
v___x_850_ = l_Repr_addAppParen(v___x_849_, v_prec_843_);
return v___x_850_;
}
v___jp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_853_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__3));
lean_inc(v___y_852_);
v___x_854_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_854_, 0, v___y_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = 0;
v___x_856_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*1, v___x_855_);
v___x_857_ = l_Repr_addAppParen(v___x_856_, v_prec_843_);
return v___x_857_;
}
v___jp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_860_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__5));
lean_inc(v___y_859_);
v___x_861_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_861_, 0, v___y_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = 0;
v___x_863_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set_uint8(v___x_863_, sizeof(void*)*1, v___x_862_);
v___x_864_ = l_Repr_addAppParen(v___x_863_, v_prec_843_);
return v___x_864_;
}
v___jp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_867_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__7));
lean_inc(v___y_866_);
v___x_868_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_868_, 0, v___y_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = 0;
v___x_870_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*1, v___x_869_);
v___x_871_ = l_Repr_addAppParen(v___x_870_, v_prec_843_);
return v___x_871_;
}
v___jp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_874_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__9));
lean_inc(v___y_873_);
v___x_875_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_875_, 0, v___y_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = 0;
v___x_877_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*1, v___x_876_);
v___x_878_ = l_Repr_addAppParen(v___x_877_, v_prec_843_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr___boxed(lean_object* v_x_899_, lean_object* v_prec_900_){
_start:
{
uint8_t v_x_285__boxed_901_; lean_object* v_res_902_; 
v_x_285__boxed_901_ = lean_unbox(v_x_899_);
v_res_902_ = l_Std_Time_instReprOffsetX_repr(v_x_285__boxed_901_, v_prec_900_);
lean_dec(v_prec_900_);
return v_res_902_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetX_default(void){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = 0;
return v___x_905_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetX(void){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = 0;
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify(lean_object* v_num_922_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_dec_eq(v_num_922_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = lean_unsigned_to_nat(2u);
v___x_926_ = lean_nat_dec_eq(v_num_922_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_unsigned_to_nat(3u);
v___x_928_ = lean_nat_dec_eq(v_num_922_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = lean_unsigned_to_nat(4u);
v___x_930_ = lean_nat_dec_eq(v_num_922_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_unsigned_to_nat(5u);
v___x_932_ = lean_nat_dec_eq(v_num_922_, v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
v___x_933_ = lean_box(0);
return v___x_933_;
}
else
{
lean_object* v___x_934_; 
v___x_934_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__0));
return v___x_934_;
}
}
else
{
lean_object* v___x_935_; 
v___x_935_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__1));
return v___x_935_;
}
}
else
{
lean_object* v___x_936_; 
v___x_936_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__2));
return v___x_936_;
}
}
else
{
lean_object* v___x_937_; 
v___x_937_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__3));
return v___x_937_;
}
}
else
{
lean_object* v___x_938_; 
v___x_938_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__4));
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify___boxed(lean_object* v_num_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Std_Time_OffsetX_classify(v_num_939_);
lean_dec(v_num_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx(uint8_t v_x_941_){
_start:
{
if (v_x_941_ == 0)
{
lean_object* v___x_942_; 
v___x_942_ = lean_unsigned_to_nat(0u);
return v___x_942_;
}
else
{
lean_object* v___x_943_; 
v___x_943_ = lean_unsigned_to_nat(1u);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx___boxed(lean_object* v_x_944_){
_start:
{
uint8_t v_x_boxed_945_; lean_object* v_res_946_; 
v_x_boxed_945_ = lean_unbox(v_x_944_);
v_res_946_ = l_Std_Time_OffsetO_ctorIdx(v_x_boxed_945_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg(lean_object* v_k_947_){
_start:
{
lean_inc(v_k_947_);
return v_k_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg___boxed(lean_object* v_k_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_Time_OffsetO_ctorElim___redArg(v_k_948_);
lean_dec(v_k_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim(lean_object* v_motive_950_, lean_object* v_ctorIdx_951_, uint8_t v_t_952_, lean_object* v_h_953_, lean_object* v_k_954_){
_start:
{
lean_inc(v_k_954_);
return v_k_954_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___boxed(lean_object* v_motive_955_, lean_object* v_ctorIdx_956_, lean_object* v_t_957_, lean_object* v_h_958_, lean_object* v_k_959_){
_start:
{
uint8_t v_t_boxed_960_; lean_object* v_res_961_; 
v_t_boxed_960_ = lean_unbox(v_t_957_);
v_res_961_ = l_Std_Time_OffsetO_ctorElim(v_motive_955_, v_ctorIdx_956_, v_t_boxed_960_, v_h_958_, v_k_959_);
lean_dec(v_k_959_);
lean_dec(v_ctorIdx_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg(lean_object* v_short_962_){
_start:
{
lean_inc(v_short_962_);
return v_short_962_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg___boxed(lean_object* v_short_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_Time_OffsetO_short_elim___redArg(v_short_963_);
lean_dec(v_short_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim(lean_object* v_motive_965_, uint8_t v_t_966_, lean_object* v_h_967_, lean_object* v_short_968_){
_start:
{
lean_inc(v_short_968_);
return v_short_968_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___boxed(lean_object* v_motive_969_, lean_object* v_t_970_, lean_object* v_h_971_, lean_object* v_short_972_){
_start:
{
uint8_t v_t_boxed_973_; lean_object* v_res_974_; 
v_t_boxed_973_ = lean_unbox(v_t_970_);
v_res_974_ = l_Std_Time_OffsetO_short_elim(v_motive_969_, v_t_boxed_973_, v_h_971_, v_short_972_);
lean_dec(v_short_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg(lean_object* v_full_975_){
_start:
{
lean_inc(v_full_975_);
return v_full_975_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg___boxed(lean_object* v_full_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_Time_OffsetO_full_elim___redArg(v_full_976_);
lean_dec(v_full_976_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim(lean_object* v_motive_978_, uint8_t v_t_979_, lean_object* v_h_980_, lean_object* v_full_981_){
_start:
{
lean_inc(v_full_981_);
return v_full_981_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___boxed(lean_object* v_motive_982_, lean_object* v_t_983_, lean_object* v_h_984_, lean_object* v_full_985_){
_start:
{
uint8_t v_t_boxed_986_; lean_object* v_res_987_; 
v_t_boxed_986_ = lean_unbox(v_t_983_);
v_res_987_ = l_Std_Time_OffsetO_full_elim(v_motive_982_, v_t_boxed_986_, v_h_984_, v_full_985_);
lean_dec(v_full_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr(uint8_t v_x_994_, lean_object* v_prec_995_){
_start:
{
lean_object* v___y_997_; lean_object* v___y_1004_; 
if (v_x_994_ == 0)
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(1024u);
v___x_1011_ = lean_nat_dec_le(v___x_1010_, v_prec_995_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_997_ = v___x_1012_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_997_ = v___x_1013_;
goto v___jp_996_;
}
}
else
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_unsigned_to_nat(1024u);
v___x_1015_ = lean_nat_dec_le(v___x_1014_, v_prec_995_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1004_ = v___x_1016_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1004_ = v___x_1017_;
goto v___jp_1003_;
}
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_998_ = ((lean_object*)(l_Std_Time_instReprOffsetO_repr___closed__1));
lean_inc(v___y_997_);
v___x_999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_999_, 0, v___y_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = 0;
v___x_1001_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*1, v___x_1000_);
v___x_1002_ = l_Repr_addAppParen(v___x_1001_, v_prec_995_);
return v___x_1002_;
}
v___jp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1005_ = ((lean_object*)(l_Std_Time_instReprOffsetO_repr___closed__3));
lean_inc(v___y_1004_);
v___x_1006_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___y_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = 0;
v___x_1008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*1, v___x_1007_);
v___x_1009_ = l_Repr_addAppParen(v___x_1008_, v_prec_995_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr___boxed(lean_object* v_x_1018_, lean_object* v_prec_1019_){
_start:
{
uint8_t v_x_117__boxed_1020_; lean_object* v_res_1021_; 
v_x_117__boxed_1020_ = lean_unbox(v_x_1018_);
v_res_1021_ = l_Std_Time_instReprOffsetO_repr(v_x_117__boxed_1020_, v_prec_1019_);
lean_dec(v_prec_1019_);
return v_res_1021_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetO_default(void){
_start:
{
uint8_t v___x_1024_; 
v___x_1024_ = 0;
return v___x_1024_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetO(void){
_start:
{
uint8_t v___x_1025_; 
v___x_1025_ = 0;
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify(lean_object* v_num_1032_){
_start:
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = lean_unsigned_to_nat(1u);
v___x_1034_ = lean_nat_dec_eq(v_num_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(4u);
v___x_1036_ = lean_nat_dec_eq(v_num_1032_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = ((lean_object*)(l_Std_Time_OffsetO_classify___closed__0));
return v___x_1038_;
}
}
else
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Std_Time_OffsetO_classify___closed__1));
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify___boxed(lean_object* v_num_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_Time_OffsetO_classify(v_num_1040_);
lean_dec(v_num_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx(uint8_t v_x_1042_){
_start:
{
switch(v_x_1042_)
{
case 0:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_unsigned_to_nat(0u);
return v___x_1043_;
}
case 1:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_unsigned_to_nat(1u);
return v___x_1044_;
}
default: 
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_unsigned_to_nat(2u);
return v___x_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx___boxed(lean_object* v_x_1046_){
_start:
{
uint8_t v_x_boxed_1047_; lean_object* v_res_1048_; 
v_x_boxed_1047_ = lean_unbox(v_x_1046_);
v_res_1048_ = l_Std_Time_OffsetZ_ctorIdx(v_x_boxed_1047_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg(lean_object* v_k_1049_){
_start:
{
lean_inc(v_k_1049_);
return v_k_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg___boxed(lean_object* v_k_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Std_Time_OffsetZ_ctorElim___redArg(v_k_1050_);
lean_dec(v_k_1050_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim(lean_object* v_motive_1052_, lean_object* v_ctorIdx_1053_, uint8_t v_t_1054_, lean_object* v_h_1055_, lean_object* v_k_1056_){
_start:
{
lean_inc(v_k_1056_);
return v_k_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___boxed(lean_object* v_motive_1057_, lean_object* v_ctorIdx_1058_, lean_object* v_t_1059_, lean_object* v_h_1060_, lean_object* v_k_1061_){
_start:
{
uint8_t v_t_boxed_1062_; lean_object* v_res_1063_; 
v_t_boxed_1062_ = lean_unbox(v_t_1059_);
v_res_1063_ = l_Std_Time_OffsetZ_ctorElim(v_motive_1057_, v_ctorIdx_1058_, v_t_boxed_1062_, v_h_1060_, v_k_1061_);
lean_dec(v_k_1061_);
lean_dec(v_ctorIdx_1058_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg(lean_object* v_hourMinute_1064_){
_start:
{
lean_inc(v_hourMinute_1064_);
return v_hourMinute_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg___boxed(lean_object* v_hourMinute_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_Time_OffsetZ_hourMinute_elim___redArg(v_hourMinute_1065_);
lean_dec(v_hourMinute_1065_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim(lean_object* v_motive_1067_, uint8_t v_t_1068_, lean_object* v_h_1069_, lean_object* v_hourMinute_1070_){
_start:
{
lean_inc(v_hourMinute_1070_);
return v_hourMinute_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___boxed(lean_object* v_motive_1071_, lean_object* v_t_1072_, lean_object* v_h_1073_, lean_object* v_hourMinute_1074_){
_start:
{
uint8_t v_t_boxed_1075_; lean_object* v_res_1076_; 
v_t_boxed_1075_ = lean_unbox(v_t_1072_);
v_res_1076_ = l_Std_Time_OffsetZ_hourMinute_elim(v_motive_1071_, v_t_boxed_1075_, v_h_1073_, v_hourMinute_1074_);
lean_dec(v_hourMinute_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg(lean_object* v_full_1077_){
_start:
{
lean_inc(v_full_1077_);
return v_full_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg___boxed(lean_object* v_full_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Std_Time_OffsetZ_full_elim___redArg(v_full_1078_);
lean_dec(v_full_1078_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim(lean_object* v_motive_1080_, uint8_t v_t_1081_, lean_object* v_h_1082_, lean_object* v_full_1083_){
_start:
{
lean_inc(v_full_1083_);
return v_full_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___boxed(lean_object* v_motive_1084_, lean_object* v_t_1085_, lean_object* v_h_1086_, lean_object* v_full_1087_){
_start:
{
uint8_t v_t_boxed_1088_; lean_object* v_res_1089_; 
v_t_boxed_1088_ = lean_unbox(v_t_1085_);
v_res_1089_ = l_Std_Time_OffsetZ_full_elim(v_motive_1084_, v_t_boxed_1088_, v_h_1086_, v_full_1087_);
lean_dec(v_full_1087_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(lean_object* v_hourMinuteSecondColon_1090_){
_start:
{
lean_inc(v_hourMinuteSecondColon_1090_);
return v_hourMinuteSecondColon_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg___boxed(lean_object* v_hourMinuteSecondColon_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(v_hourMinuteSecondColon_1091_);
lean_dec(v_hourMinuteSecondColon_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(lean_object* v_motive_1093_, uint8_t v_t_1094_, lean_object* v_h_1095_, lean_object* v_hourMinuteSecondColon_1096_){
_start:
{
lean_inc(v_hourMinuteSecondColon_1096_);
return v_hourMinuteSecondColon_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___boxed(lean_object* v_motive_1097_, lean_object* v_t_1098_, lean_object* v_h_1099_, lean_object* v_hourMinuteSecondColon_1100_){
_start:
{
uint8_t v_t_boxed_1101_; lean_object* v_res_1102_; 
v_t_boxed_1101_ = lean_unbox(v_t_1098_);
v_res_1102_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(v_motive_1097_, v_t_boxed_1101_, v_h_1099_, v_hourMinuteSecondColon_1100_);
lean_dec(v_hourMinuteSecondColon_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr(uint8_t v_x_1112_, lean_object* v_prec_1113_){
_start:
{
lean_object* v___y_1115_; lean_object* v___y_1122_; lean_object* v___y_1129_; 
switch(v_x_1112_)
{
case 0:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_unsigned_to_nat(1024u);
v___x_1136_ = lean_nat_dec_le(v___x_1135_, v_prec_1113_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1115_ = v___x_1137_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1115_ = v___x_1138_;
goto v___jp_1114_;
}
}
case 1:
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_unsigned_to_nat(1024u);
v___x_1140_ = lean_nat_dec_le(v___x_1139_, v_prec_1113_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1122_ = v___x_1141_;
goto v___jp_1121_;
}
else
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1122_ = v___x_1142_;
goto v___jp_1121_;
}
}
default: 
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = lean_unsigned_to_nat(1024u);
v___x_1144_ = lean_nat_dec_le(v___x_1143_, v_prec_1113_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1129_ = v___x_1145_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1129_ = v___x_1146_;
goto v___jp_1128_;
}
}
}
v___jp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1116_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__1));
lean_inc(v___y_1115_);
v___x_1117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___y_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = 0;
v___x_1119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*1, v___x_1118_);
v___x_1120_ = l_Repr_addAppParen(v___x_1119_, v_prec_1113_);
return v___x_1120_;
}
v___jp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1123_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__3));
lean_inc(v___y_1122_);
v___x_1124_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___y_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = 0;
v___x_1126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set_uint8(v___x_1126_, sizeof(void*)*1, v___x_1125_);
v___x_1127_ = l_Repr_addAppParen(v___x_1126_, v_prec_1113_);
return v___x_1127_;
}
v___jp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1130_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__5));
lean_inc(v___y_1129_);
v___x_1131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___y_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = 0;
v___x_1133_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set_uint8(v___x_1133_, sizeof(void*)*1, v___x_1132_);
v___x_1134_ = l_Repr_addAppParen(v___x_1133_, v_prec_1113_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr___boxed(lean_object* v_x_1147_, lean_object* v_prec_1148_){
_start:
{
uint8_t v_x_173__boxed_1149_; lean_object* v_res_1150_; 
v_x_173__boxed_1149_ = lean_unbox(v_x_1147_);
v_res_1150_ = l_Std_Time_instReprOffsetZ_repr(v_x_173__boxed_1149_, v_prec_1148_);
lean_dec(v_prec_1148_);
return v_res_1150_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetZ_default(void){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = 0;
return v___x_1153_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetZ(void){
_start:
{
uint8_t v___x_1154_; 
v___x_1154_ = 0;
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify(lean_object* v_num_1164_){
_start:
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_unsigned_to_nat(1u);
v___x_1168_ = lean_nat_dec_eq(v_num_1164_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_unsigned_to_nat(2u);
v___x_1170_ = lean_nat_dec_eq(v_num_1164_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_unsigned_to_nat(3u);
v___x_1172_ = lean_nat_dec_eq(v_num_1164_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(4u);
v___x_1174_ = lean_nat_dec_eq(v_num_1164_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_unsigned_to_nat(5u);
v___x_1176_ = lean_nat_dec_eq(v_num_1164_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_box(0);
return v___x_1177_;
}
else
{
lean_object* v___x_1178_; 
v___x_1178_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__1));
return v___x_1178_;
}
}
else
{
lean_object* v___x_1179_; 
v___x_1179_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__2));
return v___x_1179_;
}
}
else
{
goto v___jp_1165_;
}
}
else
{
goto v___jp_1165_;
}
}
else
{
goto v___jp_1165_;
}
v___jp_1165_:
{
lean_object* v___x_1166_; 
v___x_1166_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__0));
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify___boxed(lean_object* v_num_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Std_Time_OffsetZ_classify(v_num_1180_);
lean_dec(v_num_1180_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx(uint8_t v_x_1182_){
_start:
{
switch(v_x_1182_)
{
case 0:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_unsigned_to_nat(0u);
return v___x_1183_;
}
case 1:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_unsigned_to_nat(1u);
return v___x_1184_;
}
case 2:
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_unsigned_to_nat(2u);
return v___x_1185_;
}
default: 
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_unsigned_to_nat(3u);
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx___boxed(lean_object* v_x_1187_){
_start:
{
uint8_t v_x_boxed_1188_; lean_object* v_res_1189_; 
v_x_boxed_1188_ = lean_unbox(v_x_1187_);
v_res_1189_ = l_Std_Time_DayPeriod_ctorIdx(v_x_boxed_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg(lean_object* v_k_1190_){
_start:
{
lean_inc(v_k_1190_);
return v_k_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg___boxed(lean_object* v_k_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Std_Time_DayPeriod_ctorElim___redArg(v_k_1191_);
lean_dec(v_k_1191_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim(lean_object* v_motive_1193_, lean_object* v_ctorIdx_1194_, uint8_t v_t_1195_, lean_object* v_h_1196_, lean_object* v_k_1197_){
_start:
{
lean_inc(v_k_1197_);
return v_k_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___boxed(lean_object* v_motive_1198_, lean_object* v_ctorIdx_1199_, lean_object* v_t_1200_, lean_object* v_h_1201_, lean_object* v_k_1202_){
_start:
{
uint8_t v_t_boxed_1203_; lean_object* v_res_1204_; 
v_t_boxed_1203_ = lean_unbox(v_t_1200_);
v_res_1204_ = l_Std_Time_DayPeriod_ctorElim(v_motive_1198_, v_ctorIdx_1199_, v_t_boxed_1203_, v_h_1201_, v_k_1202_);
lean_dec(v_k_1202_);
lean_dec(v_ctorIdx_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg(lean_object* v_am_1205_){
_start:
{
lean_inc(v_am_1205_);
return v_am_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg___boxed(lean_object* v_am_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_Time_DayPeriod_am_elim___redArg(v_am_1206_);
lean_dec(v_am_1206_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim(lean_object* v_motive_1208_, uint8_t v_t_1209_, lean_object* v_h_1210_, lean_object* v_am_1211_){
_start:
{
lean_inc(v_am_1211_);
return v_am_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___boxed(lean_object* v_motive_1212_, lean_object* v_t_1213_, lean_object* v_h_1214_, lean_object* v_am_1215_){
_start:
{
uint8_t v_t_boxed_1216_; lean_object* v_res_1217_; 
v_t_boxed_1216_ = lean_unbox(v_t_1213_);
v_res_1217_ = l_Std_Time_DayPeriod_am_elim(v_motive_1212_, v_t_boxed_1216_, v_h_1214_, v_am_1215_);
lean_dec(v_am_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg(lean_object* v_pm_1218_){
_start:
{
lean_inc(v_pm_1218_);
return v_pm_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg___boxed(lean_object* v_pm_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_Time_DayPeriod_pm_elim___redArg(v_pm_1219_);
lean_dec(v_pm_1219_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim(lean_object* v_motive_1221_, uint8_t v_t_1222_, lean_object* v_h_1223_, lean_object* v_pm_1224_){
_start:
{
lean_inc(v_pm_1224_);
return v_pm_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___boxed(lean_object* v_motive_1225_, lean_object* v_t_1226_, lean_object* v_h_1227_, lean_object* v_pm_1228_){
_start:
{
uint8_t v_t_boxed_1229_; lean_object* v_res_1230_; 
v_t_boxed_1229_ = lean_unbox(v_t_1226_);
v_res_1230_ = l_Std_Time_DayPeriod_pm_elim(v_motive_1225_, v_t_boxed_1229_, v_h_1227_, v_pm_1228_);
lean_dec(v_pm_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg(lean_object* v_noon_1231_){
_start:
{
lean_inc(v_noon_1231_);
return v_noon_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg___boxed(lean_object* v_noon_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_Time_DayPeriod_noon_elim___redArg(v_noon_1232_);
lean_dec(v_noon_1232_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim(lean_object* v_motive_1234_, uint8_t v_t_1235_, lean_object* v_h_1236_, lean_object* v_noon_1237_){
_start:
{
lean_inc(v_noon_1237_);
return v_noon_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___boxed(lean_object* v_motive_1238_, lean_object* v_t_1239_, lean_object* v_h_1240_, lean_object* v_noon_1241_){
_start:
{
uint8_t v_t_boxed_1242_; lean_object* v_res_1243_; 
v_t_boxed_1242_ = lean_unbox(v_t_1239_);
v_res_1243_ = l_Std_Time_DayPeriod_noon_elim(v_motive_1238_, v_t_boxed_1242_, v_h_1240_, v_noon_1241_);
lean_dec(v_noon_1241_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg(lean_object* v_midnight_1244_){
_start:
{
lean_inc(v_midnight_1244_);
return v_midnight_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg___boxed(lean_object* v_midnight_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Std_Time_DayPeriod_midnight_elim___redArg(v_midnight_1245_);
lean_dec(v_midnight_1245_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim(lean_object* v_motive_1247_, uint8_t v_t_1248_, lean_object* v_h_1249_, lean_object* v_midnight_1250_){
_start:
{
lean_inc(v_midnight_1250_);
return v_midnight_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___boxed(lean_object* v_motive_1251_, lean_object* v_t_1252_, lean_object* v_h_1253_, lean_object* v_midnight_1254_){
_start:
{
uint8_t v_t_boxed_1255_; lean_object* v_res_1256_; 
v_t_boxed_1255_ = lean_unbox(v_t_1252_);
v_res_1256_ = l_Std_Time_DayPeriod_midnight_elim(v_motive_1251_, v_t_boxed_1255_, v_h_1253_, v_midnight_1254_);
lean_dec(v_midnight_1254_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr(uint8_t v_x_1269_, lean_object* v_prec_1270_){
_start:
{
lean_object* v___y_1272_; lean_object* v___y_1279_; lean_object* v___y_1286_; lean_object* v___y_1293_; 
switch(v_x_1269_)
{
case 0:
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = lean_unsigned_to_nat(1024u);
v___x_1300_ = lean_nat_dec_le(v___x_1299_, v_prec_1270_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1272_ = v___x_1301_;
goto v___jp_1271_;
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1272_ = v___x_1302_;
goto v___jp_1271_;
}
}
case 1:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_unsigned_to_nat(1024u);
v___x_1304_ = lean_nat_dec_le(v___x_1303_, v_prec_1270_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1279_ = v___x_1305_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1279_ = v___x_1306_;
goto v___jp_1278_;
}
}
case 2:
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = lean_unsigned_to_nat(1024u);
v___x_1308_ = lean_nat_dec_le(v___x_1307_, v_prec_1270_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1286_ = v___x_1309_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1286_ = v___x_1310_;
goto v___jp_1285_;
}
}
default: 
{
lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = lean_unsigned_to_nat(1024u);
v___x_1312_ = lean_nat_dec_le(v___x_1311_, v_prec_1270_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1293_ = v___x_1313_;
goto v___jp_1292_;
}
else
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1293_ = v___x_1314_;
goto v___jp_1292_;
}
}
}
v___jp_1271_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1273_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__1));
lean_inc(v___y_1272_);
v___x_1274_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___y_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = 0;
v___x_1276_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set_uint8(v___x_1276_, sizeof(void*)*1, v___x_1275_);
v___x_1277_ = l_Repr_addAppParen(v___x_1276_, v_prec_1270_);
return v___x_1277_;
}
v___jp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1280_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__3));
lean_inc(v___y_1279_);
v___x_1281_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___y_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = 0;
v___x_1283_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*1, v___x_1282_);
v___x_1284_ = l_Repr_addAppParen(v___x_1283_, v_prec_1270_);
return v___x_1284_;
}
v___jp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1287_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__5));
lean_inc(v___y_1286_);
v___x_1288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___y_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = 0;
v___x_1290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*1, v___x_1289_);
v___x_1291_ = l_Repr_addAppParen(v___x_1290_, v_prec_1270_);
return v___x_1291_;
}
v___jp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1294_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__7));
lean_inc(v___y_1293_);
v___x_1295_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___y_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = 0;
v___x_1297_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1297_, 0, v___x_1295_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*1, v___x_1296_);
v___x_1298_ = l_Repr_addAppParen(v___x_1297_, v_prec_1270_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr___boxed(lean_object* v_x_1315_, lean_object* v_prec_1316_){
_start:
{
uint8_t v_x_229__boxed_1317_; lean_object* v_res_1318_; 
v_x_229__boxed_1317_ = lean_unbox(v_x_1315_);
v_res_1318_ = l_Std_Time_instReprDayPeriod_repr(v_x_229__boxed_1317_, v_prec_1316_);
lean_dec(v_prec_1316_);
return v_res_1318_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedDayPeriod_default(void){
_start:
{
uint8_t v___x_1321_; 
v___x_1321_ = 0;
return v___x_1321_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedDayPeriod(void){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = 0;
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx(uint8_t v_x_1323_){
_start:
{
switch(v_x_1323_)
{
case 0:
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_unsigned_to_nat(0u);
return v___x_1324_;
}
case 1:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_unsigned_to_nat(1u);
return v___x_1325_;
}
case 2:
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_unsigned_to_nat(2u);
return v___x_1326_;
}
case 3:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_unsigned_to_nat(3u);
return v___x_1327_;
}
case 4:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_unsigned_to_nat(4u);
return v___x_1328_;
}
default: 
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_unsigned_to_nat(5u);
return v___x_1329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx___boxed(lean_object* v_x_1330_){
_start:
{
uint8_t v_x_boxed_1331_; lean_object* v_res_1332_; 
v_x_boxed_1331_ = lean_unbox(v_x_1330_);
v_res_1332_ = l_Std_Time_ExtendedDayPeriod_ctorIdx(v_x_boxed_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(lean_object* v_k_1333_){
_start:
{
lean_inc(v_k_1333_);
return v_k_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg___boxed(lean_object* v_k_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(v_k_1334_);
lean_dec(v_k_1334_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim(lean_object* v_motive_1336_, lean_object* v_ctorIdx_1337_, uint8_t v_t_1338_, lean_object* v_h_1339_, lean_object* v_k_1340_){
_start:
{
lean_inc(v_k_1340_);
return v_k_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___boxed(lean_object* v_motive_1341_, lean_object* v_ctorIdx_1342_, lean_object* v_t_1343_, lean_object* v_h_1344_, lean_object* v_k_1345_){
_start:
{
uint8_t v_t_boxed_1346_; lean_object* v_res_1347_; 
v_t_boxed_1346_ = lean_unbox(v_t_1343_);
v_res_1347_ = l_Std_Time_ExtendedDayPeriod_ctorElim(v_motive_1341_, v_ctorIdx_1342_, v_t_boxed_1346_, v_h_1344_, v_k_1345_);
lean_dec(v_k_1345_);
lean_dec(v_ctorIdx_1342_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(lean_object* v_midnight_1348_){
_start:
{
lean_inc(v_midnight_1348_);
return v_midnight_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg___boxed(lean_object* v_midnight_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(v_midnight_1349_);
lean_dec(v_midnight_1349_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim(lean_object* v_motive_1351_, uint8_t v_t_1352_, lean_object* v_h_1353_, lean_object* v_midnight_1354_){
_start:
{
lean_inc(v_midnight_1354_);
return v_midnight_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___boxed(lean_object* v_motive_1355_, lean_object* v_t_1356_, lean_object* v_h_1357_, lean_object* v_midnight_1358_){
_start:
{
uint8_t v_t_boxed_1359_; lean_object* v_res_1360_; 
v_t_boxed_1359_ = lean_unbox(v_t_1356_);
v_res_1360_ = l_Std_Time_ExtendedDayPeriod_midnight_elim(v_motive_1355_, v_t_boxed_1359_, v_h_1357_, v_midnight_1358_);
lean_dec(v_midnight_1358_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg(lean_object* v_night_1361_){
_start:
{
lean_inc(v_night_1361_);
return v_night_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg___boxed(lean_object* v_night_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_Time_ExtendedDayPeriod_night_elim___redArg(v_night_1362_);
lean_dec(v_night_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim(lean_object* v_motive_1364_, uint8_t v_t_1365_, lean_object* v_h_1366_, lean_object* v_night_1367_){
_start:
{
lean_inc(v_night_1367_);
return v_night_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___boxed(lean_object* v_motive_1368_, lean_object* v_t_1369_, lean_object* v_h_1370_, lean_object* v_night_1371_){
_start:
{
uint8_t v_t_boxed_1372_; lean_object* v_res_1373_; 
v_t_boxed_1372_ = lean_unbox(v_t_1369_);
v_res_1373_ = l_Std_Time_ExtendedDayPeriod_night_elim(v_motive_1368_, v_t_boxed_1372_, v_h_1370_, v_night_1371_);
lean_dec(v_night_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(lean_object* v_morning_1374_){
_start:
{
lean_inc(v_morning_1374_);
return v_morning_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg___boxed(lean_object* v_morning_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(v_morning_1375_);
lean_dec(v_morning_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim(lean_object* v_motive_1377_, uint8_t v_t_1378_, lean_object* v_h_1379_, lean_object* v_morning_1380_){
_start:
{
lean_inc(v_morning_1380_);
return v_morning_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___boxed(lean_object* v_motive_1381_, lean_object* v_t_1382_, lean_object* v_h_1383_, lean_object* v_morning_1384_){
_start:
{
uint8_t v_t_boxed_1385_; lean_object* v_res_1386_; 
v_t_boxed_1385_ = lean_unbox(v_t_1382_);
v_res_1386_ = l_Std_Time_ExtendedDayPeriod_morning_elim(v_motive_1381_, v_t_boxed_1385_, v_h_1383_, v_morning_1384_);
lean_dec(v_morning_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(lean_object* v_noon_1387_){
_start:
{
lean_inc(v_noon_1387_);
return v_noon_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg___boxed(lean_object* v_noon_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(v_noon_1388_);
lean_dec(v_noon_1388_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim(lean_object* v_motive_1390_, uint8_t v_t_1391_, lean_object* v_h_1392_, lean_object* v_noon_1393_){
_start:
{
lean_inc(v_noon_1393_);
return v_noon_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___boxed(lean_object* v_motive_1394_, lean_object* v_t_1395_, lean_object* v_h_1396_, lean_object* v_noon_1397_){
_start:
{
uint8_t v_t_boxed_1398_; lean_object* v_res_1399_; 
v_t_boxed_1398_ = lean_unbox(v_t_1395_);
v_res_1399_ = l_Std_Time_ExtendedDayPeriod_noon_elim(v_motive_1394_, v_t_boxed_1398_, v_h_1396_, v_noon_1397_);
lean_dec(v_noon_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(lean_object* v_afternoon_1400_){
_start:
{
lean_inc(v_afternoon_1400_);
return v_afternoon_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg___boxed(lean_object* v_afternoon_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(v_afternoon_1401_);
lean_dec(v_afternoon_1401_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim(lean_object* v_motive_1403_, uint8_t v_t_1404_, lean_object* v_h_1405_, lean_object* v_afternoon_1406_){
_start:
{
lean_inc(v_afternoon_1406_);
return v_afternoon_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___boxed(lean_object* v_motive_1407_, lean_object* v_t_1408_, lean_object* v_h_1409_, lean_object* v_afternoon_1410_){
_start:
{
uint8_t v_t_boxed_1411_; lean_object* v_res_1412_; 
v_t_boxed_1411_ = lean_unbox(v_t_1408_);
v_res_1412_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim(v_motive_1407_, v_t_boxed_1411_, v_h_1409_, v_afternoon_1410_);
lean_dec(v_afternoon_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(lean_object* v_evening_1413_){
_start:
{
lean_inc(v_evening_1413_);
return v_evening_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg___boxed(lean_object* v_evening_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(v_evening_1414_);
lean_dec(v_evening_1414_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim(lean_object* v_motive_1416_, uint8_t v_t_1417_, lean_object* v_h_1418_, lean_object* v_evening_1419_){
_start:
{
lean_inc(v_evening_1419_);
return v_evening_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___boxed(lean_object* v_motive_1420_, lean_object* v_t_1421_, lean_object* v_h_1422_, lean_object* v_evening_1423_){
_start:
{
uint8_t v_t_boxed_1424_; lean_object* v_res_1425_; 
v_t_boxed_1424_ = lean_unbox(v_t_1421_);
v_res_1425_ = l_Std_Time_ExtendedDayPeriod_evening_elim(v_motive_1420_, v_t_boxed_1424_, v_h_1422_, v_evening_1423_);
lean_dec(v_evening_1423_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr(uint8_t v_x_1444_, lean_object* v_prec_1445_){
_start:
{
lean_object* v___y_1447_; lean_object* v___y_1454_; lean_object* v___y_1461_; lean_object* v___y_1468_; lean_object* v___y_1475_; lean_object* v___y_1482_; 
switch(v_x_1444_)
{
case 0:
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = lean_unsigned_to_nat(1024u);
v___x_1489_ = lean_nat_dec_le(v___x_1488_, v_prec_1445_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1447_ = v___x_1490_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1447_ = v___x_1491_;
goto v___jp_1446_;
}
}
case 1:
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = lean_unsigned_to_nat(1024u);
v___x_1493_ = lean_nat_dec_le(v___x_1492_, v_prec_1445_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1454_ = v___x_1494_;
goto v___jp_1453_;
}
else
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1454_ = v___x_1495_;
goto v___jp_1453_;
}
}
case 2:
{
lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1496_ = lean_unsigned_to_nat(1024u);
v___x_1497_ = lean_nat_dec_le(v___x_1496_, v_prec_1445_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1461_ = v___x_1498_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1461_ = v___x_1499_;
goto v___jp_1460_;
}
}
case 3:
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = lean_unsigned_to_nat(1024u);
v___x_1501_ = lean_nat_dec_le(v___x_1500_, v_prec_1445_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1468_ = v___x_1502_;
goto v___jp_1467_;
}
else
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1468_ = v___x_1503_;
goto v___jp_1467_;
}
}
case 4:
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = lean_unsigned_to_nat(1024u);
v___x_1505_ = lean_nat_dec_le(v___x_1504_, v_prec_1445_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1475_ = v___x_1506_;
goto v___jp_1474_;
}
else
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1475_ = v___x_1507_;
goto v___jp_1474_;
}
}
default: 
{
lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1508_ = lean_unsigned_to_nat(1024u);
v___x_1509_ = lean_nat_dec_le(v___x_1508_, v_prec_1445_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1482_ = v___x_1510_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1482_ = v___x_1511_;
goto v___jp_1481_;
}
}
}
v___jp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1448_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__1));
lean_inc(v___y_1447_);
v___x_1449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = 0;
v___x_1451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*1, v___x_1450_);
v___x_1452_ = l_Repr_addAppParen(v___x_1451_, v_prec_1445_);
return v___x_1452_;
}
v___jp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1455_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__3));
lean_inc(v___y_1454_);
v___x_1456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___y_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = 0;
v___x_1458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set_uint8(v___x_1458_, sizeof(void*)*1, v___x_1457_);
v___x_1459_ = l_Repr_addAppParen(v___x_1458_, v_prec_1445_);
return v___x_1459_;
}
v___jp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1462_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__5));
lean_inc(v___y_1461_);
v___x_1463_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___y_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = 0;
v___x_1465_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*1, v___x_1464_);
v___x_1466_ = l_Repr_addAppParen(v___x_1465_, v_prec_1445_);
return v___x_1466_;
}
v___jp_1467_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1469_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__7));
lean_inc(v___y_1468_);
v___x_1470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___y_1468_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = 0;
v___x_1472_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*1, v___x_1471_);
v___x_1473_ = l_Repr_addAppParen(v___x_1472_, v_prec_1445_);
return v___x_1473_;
}
v___jp_1474_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1476_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__9));
lean_inc(v___y_1475_);
v___x_1477_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___y_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = 0;
v___x_1479_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set_uint8(v___x_1479_, sizeof(void*)*1, v___x_1478_);
v___x_1480_ = l_Repr_addAppParen(v___x_1479_, v_prec_1445_);
return v___x_1480_;
}
v___jp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1483_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__11));
lean_inc(v___y_1482_);
v___x_1484_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___y_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = 0;
v___x_1486_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set_uint8(v___x_1486_, sizeof(void*)*1, v___x_1485_);
v___x_1487_ = l_Repr_addAppParen(v___x_1486_, v_prec_1445_);
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___boxed(lean_object* v_x_1512_, lean_object* v_prec_1513_){
_start:
{
uint8_t v_x_341__boxed_1514_; lean_object* v_res_1515_; 
v_x_341__boxed_1514_ = lean_unbox(v_x_1512_);
v_res_1515_ = l_Std_Time_instReprExtendedDayPeriod_repr(v_x_341__boxed_1514_, v_prec_1513_);
lean_dec(v_prec_1513_);
return v_res_1515_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedExtendedDayPeriod_default(void){
_start:
{
uint8_t v___x_1518_; 
v___x_1518_ = 0;
return v___x_1518_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedExtendedDayPeriod(void){
_start:
{
uint8_t v___x_1519_; 
v___x_1519_ = 0;
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx(lean_object* v_x_1520_){
_start:
{
switch(lean_obj_tag(v_x_1520_))
{
case 0:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_unsigned_to_nat(0u);
return v___x_1521_;
}
case 1:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_unsigned_to_nat(1u);
return v___x_1522_;
}
case 2:
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_unsigned_to_nat(2u);
return v___x_1523_;
}
case 3:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_unsigned_to_nat(3u);
return v___x_1524_;
}
case 4:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_unsigned_to_nat(4u);
return v___x_1525_;
}
case 5:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_unsigned_to_nat(5u);
return v___x_1526_;
}
case 6:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_unsigned_to_nat(6u);
return v___x_1527_;
}
case 7:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_unsigned_to_nat(7u);
return v___x_1528_;
}
case 8:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_unsigned_to_nat(8u);
return v___x_1529_;
}
case 9:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_unsigned_to_nat(9u);
return v___x_1530_;
}
case 10:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_unsigned_to_nat(10u);
return v___x_1531_;
}
case 11:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_unsigned_to_nat(11u);
return v___x_1532_;
}
case 12:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_unsigned_to_nat(12u);
return v___x_1533_;
}
case 13:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_unsigned_to_nat(13u);
return v___x_1534_;
}
case 14:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_unsigned_to_nat(14u);
return v___x_1535_;
}
case 15:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_unsigned_to_nat(15u);
return v___x_1536_;
}
case 16:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_unsigned_to_nat(16u);
return v___x_1537_;
}
case 17:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_unsigned_to_nat(17u);
return v___x_1538_;
}
case 18:
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_unsigned_to_nat(18u);
return v___x_1539_;
}
case 19:
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_unsigned_to_nat(19u);
return v___x_1540_;
}
case 20:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_unsigned_to_nat(20u);
return v___x_1541_;
}
case 21:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_unsigned_to_nat(21u);
return v___x_1542_;
}
case 22:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_unsigned_to_nat(22u);
return v___x_1543_;
}
case 23:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_unsigned_to_nat(23u);
return v___x_1544_;
}
case 24:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_unsigned_to_nat(24u);
return v___x_1545_;
}
case 25:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_unsigned_to_nat(25u);
return v___x_1546_;
}
case 26:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_unsigned_to_nat(26u);
return v___x_1547_;
}
case 27:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_unsigned_to_nat(27u);
return v___x_1548_;
}
case 28:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_unsigned_to_nat(28u);
return v___x_1549_;
}
case 29:
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_unsigned_to_nat(29u);
return v___x_1550_;
}
case 30:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_unsigned_to_nat(30u);
return v___x_1551_;
}
case 31:
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_unsigned_to_nat(31u);
return v___x_1552_;
}
case 32:
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_unsigned_to_nat(32u);
return v___x_1553_;
}
case 33:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_unsigned_to_nat(33u);
return v___x_1554_;
}
case 34:
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_unsigned_to_nat(34u);
return v___x_1555_;
}
default: 
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_unsigned_to_nat(35u);
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx___boxed(lean_object* v_x_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Std_Time_Modifier_ctorIdx(v_x_1557_);
lean_dec_ref(v_x_1557_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___redArg(lean_object* v_t_1559_, lean_object* v_k_1560_){
_start:
{
switch(lean_obj_tag(v_t_1559_))
{
case 0:
{
uint8_t v_presentation_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_presentation_1561_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1562_ = lean_box(v_presentation_1561_);
v___x_1563_ = lean_apply_1(v_k_1560_, v___x_1562_);
return v___x_1563_;
}
case 4:
{
lean_object* v_presentation_1564_; lean_object* v___x_1565_; 
v_presentation_1564_ = lean_ctor_get(v_t_1559_, 0);
lean_inc_ref(v_presentation_1564_);
lean_dec_ref_known(v_t_1559_, 1);
v___x_1565_ = lean_apply_1(v_k_1560_, v_presentation_1564_);
return v___x_1565_;
}
case 5:
{
lean_object* v_presentation_1566_; lean_object* v___x_1567_; 
v_presentation_1566_ = lean_ctor_get(v_t_1559_, 0);
lean_inc_ref(v_presentation_1566_);
lean_dec_ref_known(v_t_1559_, 1);
v___x_1567_ = lean_apply_1(v_k_1560_, v_presentation_1566_);
return v___x_1567_;
}
case 7:
{
lean_object* v_presentation_1568_; lean_object* v___x_1569_; 
v_presentation_1568_ = lean_ctor_get(v_t_1559_, 0);
lean_inc_ref(v_presentation_1568_);
lean_dec_ref_known(v_t_1559_, 1);
v___x_1569_ = lean_apply_1(v_k_1560_, v_presentation_1568_);
return v___x_1569_;
}
case 8:
{
lean_object* v_presentation_1570_; lean_object* v___x_1571_; 
v_presentation_1570_ = lean_ctor_get(v_t_1559_, 0);
lean_inc_ref(v_presentation_1570_);
lean_dec_ref_known(v_t_1559_, 1);
v___x_1571_ = lean_apply_1(v_k_1560_, v_presentation_1570_);
return v___x_1571_;
}
case 12:
{
uint8_t v_presentation_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_presentation_1572_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1573_ = lean_box(v_presentation_1572_);
v___x_1574_ = lean_apply_1(v_k_1560_, v___x_1573_);
return v___x_1574_;
}
case 13:
{
lean_object* v_presentation_1575_; lean_object* v___x_1576_; 
v_presentation_1575_ = lean_ctor_get(v_t_1559_, 0);
lean_inc_ref(v_presentation_1575_);
lean_dec_ref_known(v_t_1559_, 1);
v___x_1576_ = lean_apply_1(v_k_1560_, v_presentation_1575_);
return v___x_1576_;
}
case 14:
{
lean_object* v_presentation_1577_; lean_object* v___x_1578_; 
v_presentation_1577_ = lean_ctor_get(v_t_1559_, 0);
lean_inc_ref(v_presentation_1577_);
lean_dec_ref_known(v_t_1559_, 1);
v___x_1578_ = lean_apply_1(v_k_1560_, v_presentation_1577_);
return v___x_1578_;
}
case 16:
{
uint8_t v_presentation_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_presentation_1579_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1580_ = lean_box(v_presentation_1579_);
v___x_1581_ = lean_apply_1(v_k_1560_, v___x_1580_);
return v___x_1581_;
}
case 17:
{
uint8_t v_presentation_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_presentation_1582_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1583_ = lean_box(v_presentation_1582_);
v___x_1584_ = lean_apply_1(v_k_1560_, v___x_1583_);
return v___x_1584_;
}
case 18:
{
uint8_t v_presentation_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_presentation_1585_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1586_ = lean_box(v_presentation_1585_);
v___x_1587_ = lean_apply_1(v_k_1560_, v___x_1586_);
return v___x_1587_;
}
case 29:
{
uint8_t v_presentation_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_presentation_1588_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1589_ = lean_box(v_presentation_1588_);
v___x_1590_ = lean_apply_1(v_k_1560_, v___x_1589_);
return v___x_1590_;
}
case 30:
{
uint8_t v_presentation_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_presentation_1591_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1592_ = lean_box(v_presentation_1591_);
v___x_1593_ = lean_apply_1(v_k_1560_, v___x_1592_);
return v___x_1593_;
}
case 31:
{
uint8_t v_presentation_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_presentation_1594_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1595_ = lean_box(v_presentation_1594_);
v___x_1596_ = lean_apply_1(v_k_1560_, v___x_1595_);
return v___x_1596_;
}
case 32:
{
uint8_t v_presentation_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_presentation_1597_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1598_ = lean_box(v_presentation_1597_);
v___x_1599_ = lean_apply_1(v_k_1560_, v___x_1598_);
return v___x_1599_;
}
case 33:
{
uint8_t v_presentation_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_presentation_1600_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1601_ = lean_box(v_presentation_1600_);
v___x_1602_ = lean_apply_1(v_k_1560_, v___x_1601_);
return v___x_1602_;
}
case 34:
{
uint8_t v_presentation_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_presentation_1603_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1604_ = lean_box(v_presentation_1603_);
v___x_1605_ = lean_apply_1(v_k_1560_, v___x_1604_);
return v___x_1605_;
}
case 35:
{
uint8_t v_presentation_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_presentation_1606_ = lean_ctor_get_uint8(v_t_1559_, 0);
lean_dec_ref_known(v_t_1559_, 0);
v___x_1607_ = lean_box(v_presentation_1606_);
v___x_1608_ = lean_apply_1(v_k_1560_, v___x_1607_);
return v___x_1608_;
}
default: 
{
lean_object* v_presentation_1609_; lean_object* v___x_1610_; 
v_presentation_1609_ = lean_ctor_get(v_t_1559_, 0);
lean_inc(v_presentation_1609_);
lean_dec_ref(v_t_1559_);
v___x_1610_ = lean_apply_1(v_k_1560_, v_presentation_1609_);
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim(lean_object* v_motive_1611_, lean_object* v_ctorIdx_1612_, lean_object* v_t_1613_, lean_object* v_h_1614_, lean_object* v_k_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1613_, v_k_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___boxed(lean_object* v_motive_1617_, lean_object* v_ctorIdx_1618_, lean_object* v_t_1619_, lean_object* v_h_1620_, lean_object* v_k_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Std_Time_Modifier_ctorElim(v_motive_1617_, v_ctorIdx_1618_, v_t_1619_, v_h_1620_, v_k_1621_);
lean_dec(v_ctorIdx_1618_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim___redArg(lean_object* v_t_1623_, lean_object* v_G_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1623_, v_G_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim(lean_object* v_motive_1626_, lean_object* v_t_1627_, lean_object* v_h_1628_, lean_object* v_G_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1627_, v_G_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim___redArg(lean_object* v_t_1631_, lean_object* v_u_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1631_, v_u_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim(lean_object* v_motive_1634_, lean_object* v_t_1635_, lean_object* v_h_1636_, lean_object* v_u_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1635_, v_u_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim___redArg(lean_object* v_t_1639_, lean_object* v_y_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1639_, v_y_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim(lean_object* v_motive_1642_, lean_object* v_t_1643_, lean_object* v_h_1644_, lean_object* v_y_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1643_, v_y_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim___redArg(lean_object* v_t_1647_, lean_object* v_D_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1647_, v_D_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim(lean_object* v_motive_1650_, lean_object* v_t_1651_, lean_object* v_h_1652_, lean_object* v_D_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1651_, v_D_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim___redArg(lean_object* v_t_1655_, lean_object* v_M_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1655_, v_M_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim(lean_object* v_motive_1658_, lean_object* v_t_1659_, lean_object* v_h_1660_, lean_object* v_M_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1659_, v_M_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim___redArg(lean_object* v_t_1663_, lean_object* v_L_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1663_, v_L_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim(lean_object* v_motive_1666_, lean_object* v_t_1667_, lean_object* v_h_1668_, lean_object* v_L_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1667_, v_L_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim___redArg(lean_object* v_t_1671_, lean_object* v_d_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1671_, v_d_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim(lean_object* v_motive_1674_, lean_object* v_t_1675_, lean_object* v_h_1676_, lean_object* v_d_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1675_, v_d_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim___redArg(lean_object* v_t_1679_, lean_object* v_Q_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1679_, v_Q_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim(lean_object* v_motive_1682_, lean_object* v_t_1683_, lean_object* v_h_1684_, lean_object* v_Q_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1683_, v_Q_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim___redArg(lean_object* v_t_1687_, lean_object* v_q_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1687_, v_q_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim(lean_object* v_motive_1690_, lean_object* v_t_1691_, lean_object* v_h_1692_, lean_object* v_q_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1691_, v_q_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim___redArg(lean_object* v_t_1695_, lean_object* v_Y_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1695_, v_Y_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim(lean_object* v_motive_1698_, lean_object* v_t_1699_, lean_object* v_h_1700_, lean_object* v_Y_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1699_, v_Y_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim___redArg(lean_object* v_t_1703_, lean_object* v_w_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1703_, v_w_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim(lean_object* v_motive_1706_, lean_object* v_t_1707_, lean_object* v_h_1708_, lean_object* v_w_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1707_, v_w_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim___redArg(lean_object* v_t_1711_, lean_object* v_W_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1711_, v_W_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim(lean_object* v_motive_1714_, lean_object* v_t_1715_, lean_object* v_h_1716_, lean_object* v_W_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1715_, v_W_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim___redArg(lean_object* v_t_1719_, lean_object* v_E_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1719_, v_E_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim(lean_object* v_motive_1722_, lean_object* v_t_1723_, lean_object* v_h_1724_, lean_object* v_E_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1723_, v_E_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim___redArg(lean_object* v_t_1727_, lean_object* v_e_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1727_, v_e_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim(lean_object* v_motive_1730_, lean_object* v_t_1731_, lean_object* v_h_1732_, lean_object* v_e_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1731_, v_e_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim___redArg(lean_object* v_t_1735_, lean_object* v_c_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1735_, v_c_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim(lean_object* v_motive_1738_, lean_object* v_t_1739_, lean_object* v_h_1740_, lean_object* v_c_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1739_, v_c_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim___redArg(lean_object* v_t_1743_, lean_object* v_F_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1743_, v_F_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim(lean_object* v_motive_1746_, lean_object* v_t_1747_, lean_object* v_h_1748_, lean_object* v_F_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1747_, v_F_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim___redArg(lean_object* v_t_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1751_, v_a_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim(lean_object* v_motive_1754_, lean_object* v_t_1755_, lean_object* v_h_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1755_, v_a_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim___redArg(lean_object* v_t_1759_, lean_object* v_b_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1759_, v_b_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim(lean_object* v_motive_1762_, lean_object* v_t_1763_, lean_object* v_h_1764_, lean_object* v_b_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1763_, v_b_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim___redArg(lean_object* v_t_1767_, lean_object* v_B_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1767_, v_B_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim(lean_object* v_motive_1770_, lean_object* v_t_1771_, lean_object* v_h_1772_, lean_object* v_B_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1771_, v_B_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim___redArg(lean_object* v_t_1775_, lean_object* v_h_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1775_, v_h_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim(lean_object* v_motive_1778_, lean_object* v_t_1779_, lean_object* v_h_1780_, lean_object* v_h_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1779_, v_h_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim___redArg(lean_object* v_t_1783_, lean_object* v_K_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1783_, v_K_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim(lean_object* v_motive_1786_, lean_object* v_t_1787_, lean_object* v_h_1788_, lean_object* v_K_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1787_, v_K_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim___redArg(lean_object* v_t_1791_, lean_object* v_k_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1791_, v_k_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim(lean_object* v_motive_1794_, lean_object* v_t_1795_, lean_object* v_h_1796_, lean_object* v_k_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1795_, v_k_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim___redArg(lean_object* v_t_1799_, lean_object* v_H_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1799_, v_H_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim(lean_object* v_motive_1802_, lean_object* v_t_1803_, lean_object* v_h_1804_, lean_object* v_H_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1803_, v_H_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim___redArg(lean_object* v_t_1807_, lean_object* v_m_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1807_, v_m_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim(lean_object* v_motive_1810_, lean_object* v_t_1811_, lean_object* v_h_1812_, lean_object* v_m_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1811_, v_m_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim___redArg(lean_object* v_t_1815_, lean_object* v_s_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1815_, v_s_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim(lean_object* v_motive_1818_, lean_object* v_t_1819_, lean_object* v_h_1820_, lean_object* v_s_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1819_, v_s_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim___redArg(lean_object* v_t_1823_, lean_object* v_S_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1823_, v_S_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim(lean_object* v_motive_1826_, lean_object* v_t_1827_, lean_object* v_h_1828_, lean_object* v_S_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1827_, v_S_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim___redArg(lean_object* v_t_1831_, lean_object* v_A_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1831_, v_A_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim(lean_object* v_motive_1834_, lean_object* v_t_1835_, lean_object* v_h_1836_, lean_object* v_A_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1835_, v_A_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim___redArg(lean_object* v_t_1839_, lean_object* v_n_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1839_, v_n_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim(lean_object* v_motive_1842_, lean_object* v_t_1843_, lean_object* v_h_1844_, lean_object* v_n_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1843_, v_n_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim___redArg(lean_object* v_t_1847_, lean_object* v_N_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1847_, v_N_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim(lean_object* v_motive_1850_, lean_object* v_t_1851_, lean_object* v_h_1852_, lean_object* v_N_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1851_, v_N_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim___redArg(lean_object* v_t_1855_, lean_object* v_V_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1855_, v_V_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim(lean_object* v_motive_1858_, lean_object* v_t_1859_, lean_object* v_h_1860_, lean_object* v_V_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1859_, v_V_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim___redArg(lean_object* v_t_1863_, lean_object* v_z_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1863_, v_z_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim(lean_object* v_motive_1866_, lean_object* v_t_1867_, lean_object* v_h_1868_, lean_object* v_z_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1867_, v_z_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim___redArg(lean_object* v_t_1871_, lean_object* v_v_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1871_, v_v_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim(lean_object* v_motive_1874_, lean_object* v_t_1875_, lean_object* v_h_1876_, lean_object* v_v_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1875_, v_v_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim___redArg(lean_object* v_t_1879_, lean_object* v_O_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1879_, v_O_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim(lean_object* v_motive_1882_, lean_object* v_t_1883_, lean_object* v_h_1884_, lean_object* v_O_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1883_, v_O_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim___redArg(lean_object* v_t_1887_, lean_object* v_X_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1887_, v_X_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim(lean_object* v_motive_1890_, lean_object* v_t_1891_, lean_object* v_h_1892_, lean_object* v_X_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1891_, v_X_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim___redArg(lean_object* v_t_1895_, lean_object* v_x_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1895_, v_x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim(lean_object* v_motive_1898_, lean_object* v_t_1899_, lean_object* v_h_1900_, lean_object* v_x_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1899_, v_x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim___redArg(lean_object* v_t_1903_, lean_object* v_Z_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1903_, v_Z_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim(lean_object* v_motive_1906_, lean_object* v_t_1907_, lean_object* v_h_1908_, lean_object* v_Z_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1907_, v_Z_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(lean_object* v_x_1917_, lean_object* v_x_1918_){
_start:
{
if (lean_obj_tag(v_x_1917_) == 0)
{
lean_object* v_val_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_val_1919_ = lean_ctor_get(v_x_1917_, 0);
lean_inc(v_val_1919_);
lean_dec_ref_known(v_x_1917_, 1);
v___x_1920_ = ((lean_object*)(l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__1));
v___x_1921_ = l_Std_Time_instReprNumber_repr___redArg(v_val_1919_);
v___x_1922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l_Repr_addAppParen(v___x_1922_, v_x_1918_);
return v___x_1923_;
}
else
{
lean_object* v_val_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_val_1924_ = lean_ctor_get(v_x_1917_, 0);
lean_inc(v_val_1924_);
lean_dec_ref_known(v_x_1917_, 1);
v___x_1925_ = ((lean_object*)(l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__3));
v___x_1926_ = lean_unsigned_to_nat(1024u);
v___x_1927_ = lean_unbox(v_val_1924_);
lean_dec(v_val_1924_);
v___x_1928_ = l_Std_Time_instReprText_repr(v___x_1927_, v___x_1926_);
v___x_1929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1925_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Repr_addAppParen(v___x_1929_, v_x_1918_);
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___boxed(lean_object* v_x_1931_, lean_object* v_x_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_x_1931_, v_x_1932_);
lean_dec(v_x_1932_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr(lean_object* v_x_2150_, lean_object* v_prec_2151_){
_start:
{
switch(lean_obj_tag(v_x_2150_))
{
case 0:
{
uint8_t v_presentation_2152_; lean_object* v___y_2154_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_presentation_2152_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2163_ = lean_unsigned_to_nat(1024u);
v___x_2164_ = lean_nat_dec_le(v___x_2163_, v_prec_2151_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2154_ = v___x_2165_;
goto v___jp_2153_;
}
else
{
lean_object* v___x_2166_; 
v___x_2166_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2154_ = v___x_2166_;
goto v___jp_2153_;
}
v___jp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2155_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__2));
v___x_2156_ = lean_unsigned_to_nat(1024u);
v___x_2157_ = l_Std_Time_instReprText_repr(v_presentation_2152_, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2155_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
lean_inc(v___y_2154_);
v___x_2159_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___y_2154_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = 0;
v___x_2161_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set_uint8(v___x_2161_, sizeof(void*)*1, v___x_2160_);
v___x_2162_ = l_Repr_addAppParen(v___x_2161_, v_prec_2151_);
return v___x_2162_;
}
}
case 1:
{
lean_object* v_presentation_2167_; lean_object* v___y_2169_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v_presentation_2167_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2167_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2178_ = lean_unsigned_to_nat(1024u);
v___x_2179_ = lean_nat_dec_le(v___x_2178_, v_prec_2151_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2169_ = v___x_2180_;
goto v___jp_2168_;
}
else
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2169_ = v___x_2181_;
goto v___jp_2168_;
}
v___jp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2170_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__5));
v___x_2171_ = lean_unsigned_to_nat(1024u);
v___x_2172_ = l_Std_Time_instReprYear_repr(v_presentation_2167_, v___x_2171_);
v___x_2173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2170_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
lean_inc(v___y_2169_);
v___x_2174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___y_2169_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = 0;
v___x_2176_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*1, v___x_2175_);
v___x_2177_ = l_Repr_addAppParen(v___x_2176_, v_prec_2151_);
return v___x_2177_;
}
}
case 2:
{
lean_object* v_presentation_2182_; lean_object* v___y_2184_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v_presentation_2182_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2182_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2193_ = lean_unsigned_to_nat(1024u);
v___x_2194_ = lean_nat_dec_le(v___x_2193_, v_prec_2151_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2184_ = v___x_2195_;
goto v___jp_2183_;
}
else
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2184_ = v___x_2196_;
goto v___jp_2183_;
}
v___jp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2185_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__8));
v___x_2186_ = lean_unsigned_to_nat(1024u);
v___x_2187_ = l_Std_Time_instReprYear_repr(v_presentation_2182_, v___x_2186_);
v___x_2188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2185_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
lean_inc(v___y_2184_);
v___x_2189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___y_2184_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = 0;
v___x_2191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set_uint8(v___x_2191_, sizeof(void*)*1, v___x_2190_);
v___x_2192_ = l_Repr_addAppParen(v___x_2191_, v_prec_2151_);
return v___x_2192_;
}
}
case 3:
{
lean_object* v_presentation_2197_; lean_object* v___y_2199_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v_presentation_2197_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2197_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2207_ = lean_unsigned_to_nat(1024u);
v___x_2208_ = lean_nat_dec_le(v___x_2207_, v_prec_2151_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2199_ = v___x_2209_;
goto v___jp_2198_;
}
else
{
lean_object* v___x_2210_; 
v___x_2210_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2199_ = v___x_2210_;
goto v___jp_2198_;
}
v___jp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2200_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__11));
v___x_2201_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2197_);
v___x_2202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
lean_inc(v___y_2199_);
v___x_2203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___y_2199_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = 0;
v___x_2205_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*1, v___x_2204_);
v___x_2206_ = l_Repr_addAppParen(v___x_2205_, v_prec_2151_);
return v___x_2206_;
}
}
case 4:
{
lean_object* v_presentation_2211_; lean_object* v___y_2213_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v_presentation_2211_ = lean_ctor_get(v_x_2150_, 0);
lean_inc_ref(v_presentation_2211_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2222_ = lean_unsigned_to_nat(1024u);
v___x_2223_ = lean_nat_dec_le(v___x_2222_, v_prec_2151_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2213_ = v___x_2224_;
goto v___jp_2212_;
}
else
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2213_ = v___x_2225_;
goto v___jp_2212_;
}
v___jp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2214_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__14));
v___x_2215_ = lean_unsigned_to_nat(1024u);
v___x_2216_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2211_, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2214_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
lean_inc(v___y_2213_);
v___x_2218_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___y_2213_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = 0;
v___x_2220_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*1, v___x_2219_);
v___x_2221_ = l_Repr_addAppParen(v___x_2220_, v_prec_2151_);
return v___x_2221_;
}
}
case 5:
{
lean_object* v_presentation_2226_; lean_object* v___y_2228_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v_presentation_2226_ = lean_ctor_get(v_x_2150_, 0);
lean_inc_ref(v_presentation_2226_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2237_ = lean_unsigned_to_nat(1024u);
v___x_2238_ = lean_nat_dec_le(v___x_2237_, v_prec_2151_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2228_ = v___x_2239_;
goto v___jp_2227_;
}
else
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2228_ = v___x_2240_;
goto v___jp_2227_;
}
v___jp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2229_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__17));
v___x_2230_ = lean_unsigned_to_nat(1024u);
v___x_2231_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2226_, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2229_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
lean_inc(v___y_2228_);
v___x_2233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___y_2228_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = 0;
v___x_2235_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2235_, 0, v___x_2233_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*1, v___x_2234_);
v___x_2236_ = l_Repr_addAppParen(v___x_2235_, v_prec_2151_);
return v___x_2236_;
}
}
case 6:
{
lean_object* v_presentation_2241_; lean_object* v___y_2243_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v_presentation_2241_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2241_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2251_ = lean_unsigned_to_nat(1024u);
v___x_2252_ = lean_nat_dec_le(v___x_2251_, v_prec_2151_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2243_ = v___x_2253_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2243_ = v___x_2254_;
goto v___jp_2242_;
}
v___jp_2242_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2244_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__20));
v___x_2245_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2241_);
v___x_2246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2244_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
lean_inc(v___y_2243_);
v___x_2247_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___y_2243_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = 0;
v___x_2249_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*1, v___x_2248_);
v___x_2250_ = l_Repr_addAppParen(v___x_2249_, v_prec_2151_);
return v___x_2250_;
}
}
case 7:
{
lean_object* v_presentation_2255_; lean_object* v___y_2257_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v_presentation_2255_ = lean_ctor_get(v_x_2150_, 0);
lean_inc_ref(v_presentation_2255_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2266_ = lean_unsigned_to_nat(1024u);
v___x_2267_ = lean_nat_dec_le(v___x_2266_, v_prec_2151_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2257_ = v___x_2268_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2257_ = v___x_2269_;
goto v___jp_2256_;
}
v___jp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2258_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__23));
v___x_2259_ = lean_unsigned_to_nat(1024u);
v___x_2260_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2255_, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2258_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
lean_inc(v___y_2257_);
v___x_2262_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___y_2257_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = 0;
v___x_2264_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*1, v___x_2263_);
v___x_2265_ = l_Repr_addAppParen(v___x_2264_, v_prec_2151_);
return v___x_2265_;
}
}
case 8:
{
lean_object* v_presentation_2270_; lean_object* v___y_2272_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_presentation_2270_ = lean_ctor_get(v_x_2150_, 0);
lean_inc_ref(v_presentation_2270_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2281_ = lean_unsigned_to_nat(1024u);
v___x_2282_ = lean_nat_dec_le(v___x_2281_, v_prec_2151_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2272_ = v___x_2283_;
goto v___jp_2271_;
}
else
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2272_ = v___x_2284_;
goto v___jp_2271_;
}
v___jp_2271_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2273_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__26));
v___x_2274_ = lean_unsigned_to_nat(1024u);
v___x_2275_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2270_, v___x_2274_);
v___x_2276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2273_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
lean_inc(v___y_2272_);
v___x_2277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___y_2272_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = 0;
v___x_2279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set_uint8(v___x_2279_, sizeof(void*)*1, v___x_2278_);
v___x_2280_ = l_Repr_addAppParen(v___x_2279_, v_prec_2151_);
return v___x_2280_;
}
}
case 9:
{
lean_object* v_presentation_2285_; lean_object* v___y_2287_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v_presentation_2285_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2285_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2296_ = lean_unsigned_to_nat(1024u);
v___x_2297_ = lean_nat_dec_le(v___x_2296_, v_prec_2151_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2287_ = v___x_2298_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2287_ = v___x_2299_;
goto v___jp_2286_;
}
v___jp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2288_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__29));
v___x_2289_ = lean_unsigned_to_nat(1024u);
v___x_2290_ = l_Std_Time_instReprYear_repr(v_presentation_2285_, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2288_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
lean_inc(v___y_2287_);
v___x_2292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___y_2287_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = 0;
v___x_2294_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*1, v___x_2293_);
v___x_2295_ = l_Repr_addAppParen(v___x_2294_, v_prec_2151_);
return v___x_2295_;
}
}
case 10:
{
lean_object* v_presentation_2300_; lean_object* v___y_2302_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v_presentation_2300_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2300_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2310_ = lean_unsigned_to_nat(1024u);
v___x_2311_ = lean_nat_dec_le(v___x_2310_, v_prec_2151_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2302_ = v___x_2312_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2302_ = v___x_2313_;
goto v___jp_2301_;
}
v___jp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2303_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__32));
v___x_2304_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2300_);
v___x_2305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
lean_inc(v___y_2302_);
v___x_2306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___y_2302_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = 0;
v___x_2308_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*1, v___x_2307_);
v___x_2309_ = l_Repr_addAppParen(v___x_2308_, v_prec_2151_);
return v___x_2309_;
}
}
case 11:
{
lean_object* v_presentation_2314_; lean_object* v___y_2316_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v_presentation_2314_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2314_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2324_ = lean_unsigned_to_nat(1024u);
v___x_2325_ = lean_nat_dec_le(v___x_2324_, v_prec_2151_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2316_ = v___x_2326_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2316_ = v___x_2327_;
goto v___jp_2315_;
}
v___jp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2317_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__35));
v___x_2318_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2314_);
v___x_2319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
lean_inc(v___y_2316_);
v___x_2320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___y_2316_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = 0;
v___x_2322_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set_uint8(v___x_2322_, sizeof(void*)*1, v___x_2321_);
v___x_2323_ = l_Repr_addAppParen(v___x_2322_, v_prec_2151_);
return v___x_2323_;
}
}
case 12:
{
uint8_t v_presentation_2328_; lean_object* v___y_2330_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_presentation_2328_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2339_ = lean_unsigned_to_nat(1024u);
v___x_2340_ = lean_nat_dec_le(v___x_2339_, v_prec_2151_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2330_ = v___x_2341_;
goto v___jp_2329_;
}
else
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2330_ = v___x_2342_;
goto v___jp_2329_;
}
v___jp_2329_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2331_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__38));
v___x_2332_ = lean_unsigned_to_nat(1024u);
v___x_2333_ = l_Std_Time_instReprText_repr(v_presentation_2328_, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2331_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
lean_inc(v___y_2330_);
v___x_2335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___y_2330_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = 0;
v___x_2337_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1, v___x_2336_);
v___x_2338_ = l_Repr_addAppParen(v___x_2337_, v_prec_2151_);
return v___x_2338_;
}
}
case 13:
{
lean_object* v_presentation_2343_; lean_object* v___y_2345_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v_presentation_2343_ = lean_ctor_get(v_x_2150_, 0);
lean_inc_ref(v_presentation_2343_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2354_ = lean_unsigned_to_nat(1024u);
v___x_2355_ = lean_nat_dec_le(v___x_2354_, v_prec_2151_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2345_ = v___x_2356_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2345_ = v___x_2357_;
goto v___jp_2344_;
}
v___jp_2344_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2346_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__41));
v___x_2347_ = lean_unsigned_to_nat(1024u);
v___x_2348_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2343_, v___x_2347_);
v___x_2349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2346_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
lean_inc(v___y_2345_);
v___x_2350_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___y_2345_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = 0;
v___x_2352_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set_uint8(v___x_2352_, sizeof(void*)*1, v___x_2351_);
v___x_2353_ = l_Repr_addAppParen(v___x_2352_, v_prec_2151_);
return v___x_2353_;
}
}
case 14:
{
lean_object* v_presentation_2358_; lean_object* v___y_2360_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v_presentation_2358_ = lean_ctor_get(v_x_2150_, 0);
lean_inc_ref(v_presentation_2358_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2369_ = lean_unsigned_to_nat(1024u);
v___x_2370_ = lean_nat_dec_le(v___x_2369_, v_prec_2151_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2360_ = v___x_2371_;
goto v___jp_2359_;
}
else
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2360_ = v___x_2372_;
goto v___jp_2359_;
}
v___jp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2361_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__44));
v___x_2362_ = lean_unsigned_to_nat(1024u);
v___x_2363_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2358_, v___x_2362_);
v___x_2364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2361_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
lean_inc(v___y_2360_);
v___x_2365_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___y_2360_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = 0;
v___x_2367_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*1, v___x_2366_);
v___x_2368_ = l_Repr_addAppParen(v___x_2367_, v_prec_2151_);
return v___x_2368_;
}
}
case 15:
{
lean_object* v_presentation_2373_; lean_object* v___y_2375_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_presentation_2373_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2373_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2383_ = lean_unsigned_to_nat(1024u);
v___x_2384_ = lean_nat_dec_le(v___x_2383_, v_prec_2151_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2375_ = v___x_2385_;
goto v___jp_2374_;
}
else
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2375_ = v___x_2386_;
goto v___jp_2374_;
}
v___jp_2374_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2376_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__47));
v___x_2377_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2373_);
v___x_2378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
lean_inc(v___y_2375_);
v___x_2379_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___y_2375_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = 0;
v___x_2381_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*1, v___x_2380_);
v___x_2382_ = l_Repr_addAppParen(v___x_2381_, v_prec_2151_);
return v___x_2382_;
}
}
case 16:
{
uint8_t v_presentation_2387_; lean_object* v___y_2389_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_presentation_2387_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2398_ = lean_unsigned_to_nat(1024u);
v___x_2399_ = lean_nat_dec_le(v___x_2398_, v_prec_2151_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2389_ = v___x_2400_;
goto v___jp_2388_;
}
else
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2389_ = v___x_2401_;
goto v___jp_2388_;
}
v___jp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2390_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__50));
v___x_2391_ = lean_unsigned_to_nat(1024u);
v___x_2392_ = l_Std_Time_instReprText_repr(v_presentation_2387_, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2390_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
lean_inc(v___y_2389_);
v___x_2394_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___y_2389_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = 0;
v___x_2396_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*1, v___x_2395_);
v___x_2397_ = l_Repr_addAppParen(v___x_2396_, v_prec_2151_);
return v___x_2397_;
}
}
case 17:
{
uint8_t v_presentation_2402_; lean_object* v___y_2404_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v_presentation_2402_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2413_ = lean_unsigned_to_nat(1024u);
v___x_2414_ = lean_nat_dec_le(v___x_2413_, v_prec_2151_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2404_ = v___x_2415_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2404_ = v___x_2416_;
goto v___jp_2403_;
}
v___jp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2405_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__53));
v___x_2406_ = lean_unsigned_to_nat(1024u);
v___x_2407_ = l_Std_Time_instReprText_repr(v_presentation_2402_, v___x_2406_);
v___x_2408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2405_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
lean_inc(v___y_2404_);
v___x_2409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___y_2404_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = 0;
v___x_2411_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*1, v___x_2410_);
v___x_2412_ = l_Repr_addAppParen(v___x_2411_, v_prec_2151_);
return v___x_2412_;
}
}
case 18:
{
uint8_t v_presentation_2417_; lean_object* v___y_2419_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v_presentation_2417_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2428_ = lean_unsigned_to_nat(1024u);
v___x_2429_ = lean_nat_dec_le(v___x_2428_, v_prec_2151_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2419_ = v___x_2430_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2419_ = v___x_2431_;
goto v___jp_2418_;
}
v___jp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2420_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__56));
v___x_2421_ = lean_unsigned_to_nat(1024u);
v___x_2422_ = l_Std_Time_instReprText_repr(v_presentation_2417_, v___x_2421_);
v___x_2423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2420_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
lean_inc(v___y_2419_);
v___x_2424_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___y_2419_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = 0;
v___x_2426_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set_uint8(v___x_2426_, sizeof(void*)*1, v___x_2425_);
v___x_2427_ = l_Repr_addAppParen(v___x_2426_, v_prec_2151_);
return v___x_2427_;
}
}
case 19:
{
lean_object* v_presentation_2432_; lean_object* v___y_2434_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v_presentation_2432_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2432_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2442_ = lean_unsigned_to_nat(1024u);
v___x_2443_ = lean_nat_dec_le(v___x_2442_, v_prec_2151_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2434_ = v___x_2444_;
goto v___jp_2433_;
}
else
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2434_ = v___x_2445_;
goto v___jp_2433_;
}
v___jp_2433_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2435_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__59));
v___x_2436_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2432_);
v___x_2437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
lean_inc(v___y_2434_);
v___x_2438_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___y_2434_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = 0;
v___x_2440_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set_uint8(v___x_2440_, sizeof(void*)*1, v___x_2439_);
v___x_2441_ = l_Repr_addAppParen(v___x_2440_, v_prec_2151_);
return v___x_2441_;
}
}
case 20:
{
lean_object* v_presentation_2446_; lean_object* v___y_2448_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v_presentation_2446_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2446_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2456_ = lean_unsigned_to_nat(1024u);
v___x_2457_ = lean_nat_dec_le(v___x_2456_, v_prec_2151_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2448_ = v___x_2458_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2448_ = v___x_2459_;
goto v___jp_2447_;
}
v___jp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2449_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__62));
v___x_2450_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2446_);
v___x_2451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
lean_inc(v___y_2448_);
v___x_2452_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___y_2448_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = 0;
v___x_2454_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set_uint8(v___x_2454_, sizeof(void*)*1, v___x_2453_);
v___x_2455_ = l_Repr_addAppParen(v___x_2454_, v_prec_2151_);
return v___x_2455_;
}
}
case 21:
{
lean_object* v_presentation_2460_; lean_object* v___y_2462_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v_presentation_2460_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2460_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2470_ = lean_unsigned_to_nat(1024u);
v___x_2471_ = lean_nat_dec_le(v___x_2470_, v_prec_2151_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2462_ = v___x_2472_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2462_ = v___x_2473_;
goto v___jp_2461_;
}
v___jp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2463_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__65));
v___x_2464_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2460_);
v___x_2465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
lean_inc(v___y_2462_);
v___x_2466_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___y_2462_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = 0;
v___x_2468_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*1, v___x_2467_);
v___x_2469_ = l_Repr_addAppParen(v___x_2468_, v_prec_2151_);
return v___x_2469_;
}
}
case 22:
{
lean_object* v_presentation_2474_; lean_object* v___y_2476_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
v_presentation_2474_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2474_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2484_ = lean_unsigned_to_nat(1024u);
v___x_2485_ = lean_nat_dec_le(v___x_2484_, v_prec_2151_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2476_ = v___x_2486_;
goto v___jp_2475_;
}
else
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2476_ = v___x_2487_;
goto v___jp_2475_;
}
v___jp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2477_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__68));
v___x_2478_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2474_);
v___x_2479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
lean_inc(v___y_2476_);
v___x_2480_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___y_2476_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = 0;
v___x_2482_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*1, v___x_2481_);
v___x_2483_ = l_Repr_addAppParen(v___x_2482_, v_prec_2151_);
return v___x_2483_;
}
}
case 23:
{
lean_object* v_presentation_2488_; lean_object* v___y_2490_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v_presentation_2488_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2488_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2498_ = lean_unsigned_to_nat(1024u);
v___x_2499_ = lean_nat_dec_le(v___x_2498_, v_prec_2151_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2490_ = v___x_2500_;
goto v___jp_2489_;
}
else
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2490_ = v___x_2501_;
goto v___jp_2489_;
}
v___jp_2489_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2491_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__71));
v___x_2492_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2488_);
v___x_2493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
lean_inc(v___y_2490_);
v___x_2494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___y_2490_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = 0;
v___x_2496_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*1, v___x_2495_);
v___x_2497_ = l_Repr_addAppParen(v___x_2496_, v_prec_2151_);
return v___x_2497_;
}
}
case 24:
{
lean_object* v_presentation_2502_; lean_object* v___y_2504_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_presentation_2502_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2502_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2512_ = lean_unsigned_to_nat(1024u);
v___x_2513_ = lean_nat_dec_le(v___x_2512_, v_prec_2151_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2504_ = v___x_2514_;
goto v___jp_2503_;
}
else
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2504_ = v___x_2515_;
goto v___jp_2503_;
}
v___jp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2505_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__74));
v___x_2506_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2502_);
v___x_2507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
lean_inc(v___y_2504_);
v___x_2508_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___y_2504_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = 0;
v___x_2510_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set_uint8(v___x_2510_, sizeof(void*)*1, v___x_2509_);
v___x_2511_ = l_Repr_addAppParen(v___x_2510_, v_prec_2151_);
return v___x_2511_;
}
}
case 25:
{
lean_object* v_presentation_2516_; lean_object* v___y_2518_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
v_presentation_2516_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2516_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2527_ = lean_unsigned_to_nat(1024u);
v___x_2528_ = lean_nat_dec_le(v___x_2527_, v_prec_2151_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2518_ = v___x_2529_;
goto v___jp_2517_;
}
else
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2518_ = v___x_2530_;
goto v___jp_2517_;
}
v___jp_2517_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2519_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__77));
v___x_2520_ = lean_unsigned_to_nat(1024u);
v___x_2521_ = l_Std_Time_instReprFraction_repr(v_presentation_2516_, v___x_2520_);
v___x_2522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2519_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
lean_inc(v___y_2518_);
v___x_2523_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___y_2518_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = 0;
v___x_2525_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*1, v___x_2524_);
v___x_2526_ = l_Repr_addAppParen(v___x_2525_, v_prec_2151_);
return v___x_2526_;
}
}
case 26:
{
lean_object* v_presentation_2531_; lean_object* v___y_2533_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v_presentation_2531_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2531_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2541_ = lean_unsigned_to_nat(1024u);
v___x_2542_ = lean_nat_dec_le(v___x_2541_, v_prec_2151_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2533_ = v___x_2543_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2533_ = v___x_2544_;
goto v___jp_2532_;
}
v___jp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2534_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__80));
v___x_2535_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2531_);
v___x_2536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
lean_inc(v___y_2533_);
v___x_2537_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___y_2533_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = 0;
v___x_2539_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set_uint8(v___x_2539_, sizeof(void*)*1, v___x_2538_);
v___x_2540_ = l_Repr_addAppParen(v___x_2539_, v_prec_2151_);
return v___x_2540_;
}
}
case 27:
{
lean_object* v_presentation_2545_; lean_object* v___y_2547_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v_presentation_2545_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2545_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2555_ = lean_unsigned_to_nat(1024u);
v___x_2556_ = lean_nat_dec_le(v___x_2555_, v_prec_2151_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2547_ = v___x_2557_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2547_ = v___x_2558_;
goto v___jp_2546_;
}
v___jp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2548_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__83));
v___x_2549_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2545_);
v___x_2550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
lean_inc(v___y_2547_);
v___x_2551_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___y_2547_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = 0;
v___x_2553_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set_uint8(v___x_2553_, sizeof(void*)*1, v___x_2552_);
v___x_2554_ = l_Repr_addAppParen(v___x_2553_, v_prec_2151_);
return v___x_2554_;
}
}
case 28:
{
lean_object* v_presentation_2559_; lean_object* v___y_2561_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v_presentation_2559_ = lean_ctor_get(v_x_2150_, 0);
lean_inc(v_presentation_2559_);
lean_dec_ref_known(v_x_2150_, 1);
v___x_2569_ = lean_unsigned_to_nat(1024u);
v___x_2570_ = lean_nat_dec_le(v___x_2569_, v_prec_2151_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2561_ = v___x_2571_;
goto v___jp_2560_;
}
else
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2561_ = v___x_2572_;
goto v___jp_2560_;
}
v___jp_2560_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2562_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__86));
v___x_2563_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2559_);
v___x_2564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
lean_inc(v___y_2561_);
v___x_2565_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___y_2561_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = 0;
v___x_2567_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set_uint8(v___x_2567_, sizeof(void*)*1, v___x_2566_);
v___x_2568_ = l_Repr_addAppParen(v___x_2567_, v_prec_2151_);
return v___x_2568_;
}
}
case 29:
{
uint8_t v_presentation_2573_; lean_object* v___y_2575_; lean_object* v___x_2584_; uint8_t v___x_2585_; 
v_presentation_2573_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2584_ = lean_unsigned_to_nat(1024u);
v___x_2585_ = lean_nat_dec_le(v___x_2584_, v_prec_2151_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2575_ = v___x_2586_;
goto v___jp_2574_;
}
else
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2575_ = v___x_2587_;
goto v___jp_2574_;
}
v___jp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2576_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__89));
v___x_2577_ = lean_unsigned_to_nat(1024u);
v___x_2578_ = l_Std_Time_instReprZoneId_repr(v_presentation_2573_, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2576_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
lean_inc(v___y_2575_);
v___x_2580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___y_2575_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = 0;
v___x_2582_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*1, v___x_2581_);
v___x_2583_ = l_Repr_addAppParen(v___x_2582_, v_prec_2151_);
return v___x_2583_;
}
}
case 30:
{
uint8_t v_presentation_2588_; lean_object* v___y_2590_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
v_presentation_2588_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2599_ = lean_unsigned_to_nat(1024u);
v___x_2600_ = lean_nat_dec_le(v___x_2599_, v_prec_2151_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2590_ = v___x_2601_;
goto v___jp_2589_;
}
else
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2590_ = v___x_2602_;
goto v___jp_2589_;
}
v___jp_2589_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2591_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__92));
v___x_2592_ = lean_unsigned_to_nat(1024u);
v___x_2593_ = l_Std_Time_instReprZoneName_repr(v_presentation_2588_, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2591_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
lean_inc(v___y_2590_);
v___x_2595_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___y_2590_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = 0;
v___x_2597_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set_uint8(v___x_2597_, sizeof(void*)*1, v___x_2596_);
v___x_2598_ = l_Repr_addAppParen(v___x_2597_, v_prec_2151_);
return v___x_2598_;
}
}
case 31:
{
uint8_t v_presentation_2603_; lean_object* v___y_2605_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v_presentation_2603_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2614_ = lean_unsigned_to_nat(1024u);
v___x_2615_ = lean_nat_dec_le(v___x_2614_, v_prec_2151_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2605_ = v___x_2616_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2617_; 
v___x_2617_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2605_ = v___x_2617_;
goto v___jp_2604_;
}
v___jp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2606_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__95));
v___x_2607_ = lean_unsigned_to_nat(1024u);
v___x_2608_ = l_Std_Time_instReprZoneName_repr(v_presentation_2603_, v___x_2607_);
v___x_2609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2606_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
lean_inc(v___y_2605_);
v___x_2610_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___y_2605_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = 0;
v___x_2612_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2612_, 0, v___x_2610_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*1, v___x_2611_);
v___x_2613_ = l_Repr_addAppParen(v___x_2612_, v_prec_2151_);
return v___x_2613_;
}
}
case 32:
{
uint8_t v_presentation_2618_; lean_object* v___y_2620_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v_presentation_2618_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2629_ = lean_unsigned_to_nat(1024u);
v___x_2630_ = lean_nat_dec_le(v___x_2629_, v_prec_2151_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
v___x_2631_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2620_ = v___x_2631_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2620_ = v___x_2632_;
goto v___jp_2619_;
}
v___jp_2619_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2621_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__98));
v___x_2622_ = lean_unsigned_to_nat(1024u);
v___x_2623_ = l_Std_Time_instReprOffsetO_repr(v_presentation_2618_, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2621_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
lean_inc(v___y_2620_);
v___x_2625_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___y_2620_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = 0;
v___x_2627_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set_uint8(v___x_2627_, sizeof(void*)*1, v___x_2626_);
v___x_2628_ = l_Repr_addAppParen(v___x_2627_, v_prec_2151_);
return v___x_2628_;
}
}
case 33:
{
uint8_t v_presentation_2633_; lean_object* v___y_2635_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v_presentation_2633_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2644_ = lean_unsigned_to_nat(1024u);
v___x_2645_ = lean_nat_dec_le(v___x_2644_, v_prec_2151_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2635_ = v___x_2646_;
goto v___jp_2634_;
}
else
{
lean_object* v___x_2647_; 
v___x_2647_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2635_ = v___x_2647_;
goto v___jp_2634_;
}
v___jp_2634_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2636_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__101));
v___x_2637_ = lean_unsigned_to_nat(1024u);
v___x_2638_ = l_Std_Time_instReprOffsetX_repr(v_presentation_2633_, v___x_2637_);
v___x_2639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2636_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
lean_inc(v___y_2635_);
v___x_2640_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___y_2635_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = 0;
v___x_2642_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set_uint8(v___x_2642_, sizeof(void*)*1, v___x_2641_);
v___x_2643_ = l_Repr_addAppParen(v___x_2642_, v_prec_2151_);
return v___x_2643_;
}
}
case 34:
{
uint8_t v_presentation_2648_; lean_object* v___y_2650_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v_presentation_2648_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2659_ = lean_unsigned_to_nat(1024u);
v___x_2660_ = lean_nat_dec_le(v___x_2659_, v_prec_2151_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; 
v___x_2661_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2650_ = v___x_2661_;
goto v___jp_2649_;
}
else
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2650_ = v___x_2662_;
goto v___jp_2649_;
}
v___jp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2651_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__104));
v___x_2652_ = lean_unsigned_to_nat(1024u);
v___x_2653_ = l_Std_Time_instReprOffsetX_repr(v_presentation_2648_, v___x_2652_);
v___x_2654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2651_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
lean_inc(v___y_2650_);
v___x_2655_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___y_2650_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = 0;
v___x_2657_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set_uint8(v___x_2657_, sizeof(void*)*1, v___x_2656_);
v___x_2658_ = l_Repr_addAppParen(v___x_2657_, v_prec_2151_);
return v___x_2658_;
}
}
default: 
{
uint8_t v_presentation_2663_; lean_object* v___y_2665_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_presentation_2663_ = lean_ctor_get_uint8(v_x_2150_, 0);
lean_dec_ref_known(v_x_2150_, 0);
v___x_2674_ = lean_unsigned_to_nat(1024u);
v___x_2675_ = lean_nat_dec_le(v___x_2674_, v_prec_2151_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2665_ = v___x_2676_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2665_ = v___x_2677_;
goto v___jp_2664_;
}
v___jp_2664_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2666_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__107));
v___x_2667_ = lean_unsigned_to_nat(1024u);
v___x_2668_ = l_Std_Time_instReprOffsetZ_repr(v_presentation_2663_, v___x_2667_);
v___x_2669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2666_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
lean_inc(v___y_2665_);
v___x_2670_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___y_2665_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = 0;
v___x_2672_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*1, v___x_2671_);
v___x_2673_ = l_Repr_addAppParen(v___x_2672_, v_prec_2151_);
return v___x_2673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr___boxed(lean_object* v_x_2678_, lean_object* v_prec_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Std_Time_instReprModifier_repr(v_x_2678_, v_prec_2679_);
lean_dec(v_prec_2679_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(lean_object* v_constructor_2690_, lean_object* v_classify_2691_, lean_object* v_p_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_len_2694_; lean_object* v___x_2695_; 
v_len_2694_ = lean_string_length(v_p_2692_);
v___x_2695_ = lean_apply_1(v_classify_2691_, v_len_2694_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v___x_2696_; uint32_t v___y_2698_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec_ref(v_constructor_2690_);
v___x_2696_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = lean_string_utf8_byte_size(v_p_2692_);
v___x_2708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2708_, 0, v_p_2692_);
lean_ctor_set(v___x_2708_, 1, v___x_2706_);
lean_ctor_set(v___x_2708_, 2, v___x_2707_);
v___x_2709_ = l_String_Slice_Pos_get_x3f(v___x_2708_, v___x_2706_);
lean_dec_ref_known(v___x_2708_, 3);
if (lean_obj_tag(v___x_2709_) == 0)
{
uint32_t v___x_2710_; 
v___x_2710_ = 65;
v___y_2698_ = v___x_2710_;
goto v___jp_2697_;
}
else
{
lean_object* v_val_2711_; uint32_t v___x_2712_; 
v_val_2711_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_val_2711_);
lean_dec_ref_known(v___x_2709_, 1);
v___x_2712_ = lean_unbox_uint32(v_val_2711_);
lean_dec(v_val_2711_);
v___y_2698_ = v___x_2712_;
goto v___jp_2697_;
}
v___jp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2699_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2700_ = lean_string_push(v___x_2699_, v___y_2698_);
v___x_2701_ = lean_string_append(v___x_2696_, v___x_2700_);
lean_dec_ref(v___x_2700_);
v___x_2702_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_2703_ = lean_string_append(v___x_2701_, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2705_, 0, v_a_2693_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
return v___x_2705_;
}
}
else
{
lean_object* v_val_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_dec_ref(v_p_2692_);
v_val_2713_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_val_2713_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2714_ = lean_apply_1(v_constructor_2690_, v_val_2713_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_a_2693_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
return v___x_2715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod(lean_object* v_00_u03b1_2716_, lean_object* v_constructor_2717_, lean_object* v_classify_2718_, lean_object* v_p_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2717_, v_classify_2718_, v_p_2719_, v_a_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(lean_object* v_constructor_2723_, lean_object* v_p_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseText___closed__0));
v___x_2727_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2723_, v___x_2726_, v_p_2724_, v_a_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(lean_object* v_max_2728_, lean_object* v_x_2729_){
_start:
{
uint8_t v___x_2730_; 
v___x_2730_ = lean_nat_dec_le(v_x_2729_, v_max_2728_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_dec(v_x_2729_);
v___x_2731_ = lean_box(0);
return v___x_2731_;
}
else
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_x_2729_);
return v___x_2732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax___boxed(lean_object* v_max_2733_, lean_object* v_x_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(v_max_2733_, v_x_2734_);
lean_dec(v_max_2733_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(lean_object* v_x_2738_){
_start:
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = lean_unsigned_to_nat(1u);
v___x_2740_ = lean_nat_dec_eq(v_x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_box(0);
return v___x_2741_;
}
else
{
lean_object* v___x_2742_; 
v___x_2742_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___closed__0));
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___boxed(lean_object* v_x_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(v_x_2743_);
lean_dec(v_x_2743_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(lean_object* v_x_2748_){
_start:
{
lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2749_ = lean_unsigned_to_nat(6u);
v___x_2750_ = lean_nat_dec_eq(v_x_2748_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Std_Time_Text_classify(v_x_2748_);
return v___x_2751_;
}
else
{
lean_object* v___x_2752_; 
v___x_2752_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___closed__0));
return v___x_2752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___boxed(lean_object* v_x_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(v_x_2753_);
lean_dec(v_x_2753_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(lean_object* v_constructor_2756_, lean_object* v_p_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText___closed__0));
v___x_2760_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2756_, v___x_2759_, v_p_2757_, v_a_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(lean_object* v_constructor_2762_, lean_object* v_p_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction___closed__0));
v___x_2766_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2762_, v___x_2765_, v_p_2763_, v_a_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(lean_object* v_constructor_2767_, lean_object* v_p_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2770_ = lean_string_length(v_p_2768_);
v___x_2771_ = lean_apply_1(v_constructor_2767_, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v_a_2769_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber___boxed(lean_object* v_constructor_2773_, lean_object* v_p_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v_constructor_2773_, v_p_2774_, v_a_2775_);
lean_dec_ref(v_p_2774_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(lean_object* v_constructor_2778_, lean_object* v_p_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear___closed__0));
v___x_2782_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2778_, v___x_2781_, v_p_2779_, v_a_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(lean_object* v_constructor_2784_, lean_object* v_p_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX___closed__0));
v___x_2788_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2784_, v___x_2787_, v_p_2785_, v_a_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(lean_object* v_constructor_2790_, lean_object* v_p_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ___closed__0));
v___x_2794_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2790_, v___x_2793_, v_p_2791_, v_a_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(lean_object* v_constructor_2796_, lean_object* v_p_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO___closed__0));
v___x_2800_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2796_, v___x_2799_, v_p_2797_, v_a_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(lean_object* v_p_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2808_ = lean_string_length(v_p_2806_);
v___x_2809_ = lean_unsigned_to_nat(1u);
v___x_2810_ = lean_nat_dec_eq(v___x_2808_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2811_ = lean_unsigned_to_nat(2u);
v___x_2812_ = lean_nat_dec_eq(v___x_2808_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; uint32_t v___y_2815_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2813_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2823_ = lean_unsigned_to_nat(0u);
v___x_2824_ = lean_string_utf8_byte_size(v_p_2806_);
v___x_2825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2825_, 0, v_p_2806_);
lean_ctor_set(v___x_2825_, 1, v___x_2823_);
lean_ctor_set(v___x_2825_, 2, v___x_2824_);
v___x_2826_ = l_String_Slice_Pos_get_x3f(v___x_2825_, v___x_2823_);
lean_dec_ref_known(v___x_2825_, 3);
if (lean_obj_tag(v___x_2826_) == 0)
{
uint32_t v___x_2827_; 
v___x_2827_ = 65;
v___y_2815_ = v___x_2827_;
goto v___jp_2814_;
}
else
{
lean_object* v_val_2828_; uint32_t v___x_2829_; 
v_val_2828_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v___x_2826_, 1);
v___x_2829_ = lean_unbox_uint32(v_val_2828_);
lean_dec(v_val_2828_);
v___y_2815_ = v___x_2829_;
goto v___jp_2814_;
}
v___jp_2814_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2816_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2817_ = lean_string_push(v___x_2816_, v___y_2815_);
v___x_2818_ = lean_string_append(v___x_2813_, v___x_2817_);
lean_dec_ref(v___x_2817_);
v___x_2819_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__0));
v___x_2820_ = lean_string_append(v___x_2818_, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2807_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
return v___x_2822_;
}
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec_ref(v_p_2806_);
v___x_2830_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__1));
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v_a_2807_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
return v___x_2831_;
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_dec_ref(v_p_2806_);
v___x_2832_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__2));
v___x_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2807_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
return v___x_2833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(lean_object* v_constructor_2835_, lean_object* v_p_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText___closed__0));
v___x_2839_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2835_, v___x_2838_, v_p_2836_, v_a_2837_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText(lean_object* v_x_2845_){
_start:
{
lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2846_ = lean_unsigned_to_nat(3u);
v___x_2847_ = lean_nat_dec_lt(v_x_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2848_ = lean_unsigned_to_nat(6u);
v___x_2849_ = lean_nat_dec_eq(v_x_2845_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Std_Time_Text_classify(v_x_2845_);
lean_dec(v_x_2845_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_box(0);
return v___x_2851_;
}
else
{
lean_object* v_val_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2860_; 
v_val_2852_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2854_ = v___x_2850_;
v_isShared_2855_ = v_isSharedCheck_2860_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_val_2852_);
lean_dec(v___x_2850_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2860_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; lean_object* v___x_2858_; 
v___x_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2856_, 0, v_val_2852_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2856_);
v___x_2858_ = v___x_2854_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
else
{
lean_object* v___x_2861_; 
lean_dec(v_x_2845_);
v___x_2861_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1));
return v___x_2861_;
}
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v_x_2845_);
v___x_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
return v___x_2863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(lean_object* v_constructor_2865_, lean_object* v_p_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText___closed__0));
v___x_2869_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2865_, v___x_2868_, v_p_2866_, v_a_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(lean_object* v_x_2874_){
_start:
{
lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = lean_unsigned_to_nat(1u);
v___x_2876_ = lean_nat_dec_eq(v_x_2874_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = lean_unsigned_to_nat(6u);
v___x_2878_ = lean_nat_dec_eq(v_x_2874_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = lean_unsigned_to_nat(3u);
v___x_2880_ = lean_nat_dec_le(v___x_2879_, v_x_2874_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; 
v___x_2881_ = lean_box(0);
return v___x_2881_;
}
else
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Std_Time_Text_classify(v_x_2874_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_box(0);
return v___x_2883_;
}
else
{
lean_object* v_val_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2892_; 
v_val_2884_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2886_ = v___x_2882_;
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_val_2884_);
lean_dec(v___x_2882_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2888_, 0, v_val_2884_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2888_);
v___x_2890_ = v___x_2886_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
else
{
lean_object* v___x_2893_; 
v___x_2893_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1));
return v___x_2893_;
}
}
else
{
lean_object* v___x_2894_; 
v___x_2894_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__1));
return v___x_2894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___boxed(lean_object* v_x_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(v_x_2895_);
lean_dec(v_x_2895_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(lean_object* v_constructor_2898_, lean_object* v_p_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText___closed__0));
v___x_2902_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2898_, v___x_2901_, v_p_2899_, v_a_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(uint8_t v_presentation_2903_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_alloc_ctor(16, 0, 1);
lean_ctor_set_uint8(v___x_2904_, 0, v_presentation_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0___boxed(lean_object* v_presentation_2905_){
_start:
{
uint8_t v_presentation_boxed_2906_; lean_object* v_res_2907_; 
v_presentation_boxed_2906_ = lean_unbox(v_presentation_2905_);
v_res_2907_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(v_presentation_boxed_2906_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(lean_object* v_p_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v___f_2911_; lean_object* v___x_2912_; 
v___f_2911_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___closed__0));
v___x_2912_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2911_, v_p_2909_, v_a_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(uint8_t v_presentation_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = lean_alloc_ctor(17, 0, 1);
lean_ctor_set_uint8(v___x_2914_, 0, v_presentation_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0___boxed(lean_object* v_presentation_2915_){
_start:
{
uint8_t v_presentation_boxed_2916_; lean_object* v_res_2917_; 
v_presentation_boxed_2916_ = lean_unbox(v_presentation_2915_);
v_res_2917_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(v_presentation_boxed_2916_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(lean_object* v_p_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v___f_2921_; lean_object* v___x_2922_; 
v___f_2921_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___closed__0));
v___x_2922_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2921_, v_p_2919_, v_a_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(uint8_t v_presentation_2923_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = lean_alloc_ctor(18, 0, 1);
lean_ctor_set_uint8(v___x_2924_, 0, v_presentation_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0___boxed(lean_object* v_presentation_2925_){
_start:
{
uint8_t v_presentation_boxed_2926_; lean_object* v_res_2927_; 
v_presentation_boxed_2926_ = lean_unbox(v_presentation_2925_);
v_res_2927_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(v_presentation_boxed_2926_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(lean_object* v_p_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v___f_2931_; lean_object* v___x_2932_; 
v___f_2931_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___closed__0));
v___x_2932_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2931_, v_p_2929_, v_a_2930_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(lean_object* v_constructor_2933_, lean_object* v_p_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v___y_2937_; uint32_t v___y_2938_; lean_object* v_len_2946_; uint32_t v___y_2948_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_len_2946_ = lean_string_length(v_p_2934_);
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = lean_string_utf8_byte_size(v_p_2934_);
lean_inc_ref(v_p_2934_);
v___x_2963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2963_, 0, v_p_2934_);
lean_ctor_set(v___x_2963_, 1, v___x_2961_);
lean_ctor_set(v___x_2963_, 2, v___x_2962_);
v___x_2964_ = l_String_Slice_Pos_get_x3f(v___x_2963_, v___x_2961_);
lean_dec_ref_known(v___x_2963_, 3);
if (lean_obj_tag(v___x_2964_) == 0)
{
uint32_t v___x_2965_; 
v___x_2965_ = 65;
v___y_2948_ = v___x_2965_;
goto v___jp_2947_;
}
else
{
lean_object* v_val_2966_; uint32_t v___x_2967_; 
v_val_2966_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_val_2966_);
lean_dec_ref_known(v___x_2964_, 1);
v___x_2967_ = lean_unbox_uint32(v_val_2966_);
lean_dec(v_val_2966_);
v___y_2948_ = v___x_2967_;
goto v___jp_2947_;
}
v___jp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2939_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2940_ = lean_string_push(v___x_2939_, v___y_2938_);
lean_inc_ref(v___y_2937_);
v___x_2941_ = lean_string_append(v___y_2937_, v___x_2940_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_2943_ = lean_string_append(v___x_2941_, v___x_2942_);
v___x_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2945_, 0, v_a_2935_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
return v___x_2945_;
}
v___jp_2947_:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Std_Time_ZoneName_classify(v___y_2948_, v_len_2946_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec_ref(v_constructor_2933_);
v___x_2950_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2951_ = lean_unsigned_to_nat(0u);
v___x_2952_ = lean_string_utf8_byte_size(v_p_2934_);
v___x_2953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2953_, 0, v_p_2934_);
lean_ctor_set(v___x_2953_, 1, v___x_2951_);
lean_ctor_set(v___x_2953_, 2, v___x_2952_);
v___x_2954_ = l_String_Slice_Pos_get_x3f(v___x_2953_, v___x_2951_);
lean_dec_ref_known(v___x_2953_, 3);
if (lean_obj_tag(v___x_2954_) == 0)
{
uint32_t v___x_2955_; 
v___x_2955_ = 65;
v___y_2937_ = v___x_2950_;
v___y_2938_ = v___x_2955_;
goto v___jp_2936_;
}
else
{
lean_object* v_val_2956_; uint32_t v___x_2957_; 
v_val_2956_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_val_2956_);
lean_dec_ref_known(v___x_2954_, 1);
v___x_2957_ = lean_unbox_uint32(v_val_2956_);
lean_dec(v_val_2956_);
v___y_2937_ = v___x_2950_;
v___y_2938_ = v___x_2957_;
goto v___jp_2936_;
}
}
else
{
lean_object* v_val_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_dec_ref(v_p_2934_);
v_val_2958_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_val_2958_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2959_ = lean_apply_1(v_constructor_2933_, v_val_2958_);
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v_a_2935_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
return v___x_2960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0(uint8_t v_presentation_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_alloc_ctor(35, 0, 1);
lean_ctor_set_uint8(v___x_2969_, 0, v_presentation_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0___boxed(lean_object* v_presentation_2970_){
_start:
{
uint8_t v_presentation_boxed_2971_; lean_object* v_res_2972_; 
v_presentation_boxed_2971_ = lean_unbox(v_presentation_2970_);
v_res_2972_ = l_Std_Time_parseModifier___lam__0(v_presentation_boxed_2971_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1(uint8_t v_presentation_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_alloc_ctor(34, 0, 1);
lean_ctor_set_uint8(v___x_2974_, 0, v_presentation_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1___boxed(lean_object* v_presentation_2975_){
_start:
{
uint8_t v_presentation_boxed_2976_; lean_object* v_res_2977_; 
v_presentation_boxed_2976_ = lean_unbox(v_presentation_2975_);
v_res_2977_ = l_Std_Time_parseModifier___lam__1(v_presentation_boxed_2976_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2(uint8_t v_presentation_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_alloc_ctor(33, 0, 1);
lean_ctor_set_uint8(v___x_2979_, 0, v_presentation_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2___boxed(lean_object* v_presentation_2980_){
_start:
{
uint8_t v_presentation_boxed_2981_; lean_object* v_res_2982_; 
v_presentation_boxed_2981_ = lean_unbox(v_presentation_2980_);
v_res_2982_ = l_Std_Time_parseModifier___lam__2(v_presentation_boxed_2981_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3(uint8_t v_presentation_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_alloc_ctor(32, 0, 1);
lean_ctor_set_uint8(v___x_2984_, 0, v_presentation_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3___boxed(lean_object* v_presentation_2985_){
_start:
{
uint8_t v_presentation_boxed_2986_; lean_object* v_res_2987_; 
v_presentation_boxed_2986_ = lean_unbox(v_presentation_2985_);
v_res_2987_ = l_Std_Time_parseModifier___lam__3(v_presentation_boxed_2986_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4(uint8_t v_presentation_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = lean_alloc_ctor(31, 0, 1);
lean_ctor_set_uint8(v___x_2989_, 0, v_presentation_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4___boxed(lean_object* v_presentation_2990_){
_start:
{
uint8_t v_presentation_boxed_2991_; lean_object* v_res_2992_; 
v_presentation_boxed_2991_ = lean_unbox(v_presentation_2990_);
v_res_2992_ = l_Std_Time_parseModifier___lam__4(v_presentation_boxed_2991_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5(uint8_t v_presentation_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_alloc_ctor(30, 0, 1);
lean_ctor_set_uint8(v___x_2994_, 0, v_presentation_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5___boxed(lean_object* v_presentation_2995_){
_start:
{
uint8_t v_presentation_boxed_2996_; lean_object* v_res_2997_; 
v_presentation_boxed_2996_ = lean_unbox(v_presentation_2995_);
v_res_2997_ = l_Std_Time_parseModifier___lam__5(v_presentation_boxed_2996_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__6(lean_object* v_presentation_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_alloc_ctor(28, 1, 0);
lean_ctor_set(v___x_2999_, 0, v_presentation_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__7(lean_object* v_presentation_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_alloc_ctor(27, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_presentation_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__8(lean_object* v_presentation_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_alloc_ctor(26, 1, 0);
lean_ctor_set(v___x_3003_, 0, v_presentation_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__9(lean_object* v_presentation_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_alloc_ctor(25, 1, 0);
lean_ctor_set(v___x_3005_, 0, v_presentation_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__10(lean_object* v_presentation_3006_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_alloc_ctor(24, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_presentation_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__11(lean_object* v_presentation_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_alloc_ctor(23, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_presentation_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__12(lean_object* v_presentation_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(v___x_3011_, 0, v_presentation_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__13(lean_object* v_presentation_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_3013_, 0, v_presentation_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__14(lean_object* v_presentation_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_presentation_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__15(lean_object* v_presentation_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(19, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_presentation_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__16(lean_object* v_presentation_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_presentation_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__17(lean_object* v_presentation_3020_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_presentation_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__18(lean_object* v_presentation_3022_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_presentation_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19(uint8_t v_presentation_3024_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_alloc_ctor(12, 0, 1);
lean_ctor_set_uint8(v___x_3025_, 0, v_presentation_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19___boxed(lean_object* v_presentation_3026_){
_start:
{
uint8_t v_presentation_boxed_3027_; lean_object* v_res_3028_; 
v_presentation_boxed_3027_ = lean_unbox(v_presentation_3026_);
v_res_3028_ = l_Std_Time_parseModifier___lam__19(v_presentation_boxed_3027_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__20(lean_object* v_presentation_3029_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_3030_, 0, v_presentation_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__21(lean_object* v_presentation_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3032_, 0, v_presentation_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__22(lean_object* v_presentation_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3034_, 0, v_presentation_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__23(lean_object* v_presentation_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3036_, 0, v_presentation_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__24(lean_object* v_presentation_3037_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_presentation_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__25(lean_object* v_presentation_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_presentation_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__26(lean_object* v_presentation_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3042_, 0, v_presentation_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__27(lean_object* v_presentation_3043_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3044_, 0, v_presentation_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__28(lean_object* v_presentation_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3046_, 0, v_presentation_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__29(lean_object* v_presentation_3047_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3048_, 0, v_presentation_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__30(lean_object* v_presentation_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_presentation_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31(uint8_t v_presentation_3051_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3052_, 0, v_presentation_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31___boxed(lean_object* v_presentation_3053_){
_start:
{
uint8_t v_presentation_boxed_3054_; lean_object* v_res_3055_; 
v_presentation_boxed_3054_ = lean_unbox(v_presentation_3053_);
v_res_3055_ = l_Std_Time_parseModifier___lam__31(v_presentation_boxed_3054_);
return v_res_3055_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1(void){
_start:
{
uint32_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = 120;
v___x_3058_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3059_ = lean_string_push(v___x_3058_, v___x_3057_);
return v___x_3059_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1);
v___x_3061_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3062_ = lean_string_append(v___x_3061_, v___x_3060_);
return v___x_3062_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3064_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__2);
v___x_3065_ = lean_string_append(v___x_3064_, v___x_3063_);
return v___x_3065_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__3);
v___x_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(lean_object* v_acc_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_fst_3070_; lean_object* v_snd_3071_; lean_object* v_pos_3073_; lean_object* v_snd_3074_; lean_object* v_err_3075_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v_fst_3070_ = lean_ctor_get(v_a_3069_, 0);
v_snd_3071_ = lean_ctor_get(v_a_3069_, 1);
lean_inc(v_snd_3071_);
v___x_3079_ = lean_string_utf8_byte_size(v_fst_3070_);
v___x_3080_ = lean_nat_dec_eq(v_snd_3071_, v___x_3079_);
if (v___x_3080_ == 0)
{
uint32_t v___x_3081_; uint32_t v_c_3082_; uint8_t v___x_3083_; 
v___x_3081_ = 120;
v_c_3082_ = lean_string_utf8_get_fast(v_fst_3070_, v_snd_3071_);
v___x_3083_ = lean_uint32_dec_eq(v_c_3082_, v___x_3081_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; 
v___x_3084_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4);
lean_inc(v_snd_3071_);
v_pos_3073_ = v_a_3069_;
v_snd_3074_ = v_snd_3071_;
v_err_3075_ = v___x_3084_;
goto v___jp_3072_;
}
else
{
lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3094_; 
lean_inc(v_fst_3070_);
v_isSharedCheck_3094_ = !lean_is_exclusive(v_a_3069_);
if (v_isSharedCheck_3094_ == 0)
{
lean_object* v_unused_3095_; lean_object* v_unused_3096_; 
v_unused_3095_ = lean_ctor_get(v_a_3069_, 1);
lean_dec(v_unused_3095_);
v_unused_3096_ = lean_ctor_get(v_a_3069_, 0);
lean_dec(v_unused_3096_);
v___x_3086_ = v_a_3069_;
v_isShared_3087_ = v_isSharedCheck_3094_;
goto v_resetjp_3085_;
}
else
{
lean_dec(v_a_3069_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3094_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v_it_x27_3090_; 
v___x_3088_ = lean_string_utf8_next_fast(v_fst_3070_, v_snd_3071_);
lean_dec(v_snd_3071_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 1, v___x_3088_);
v_it_x27_3090_ = v___x_3086_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_fst_3070_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3088_);
v_it_x27_3090_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3091_; 
v___x_3091_ = lean_string_push(v_acc_3068_, v___x_3081_);
v_acc_3068_ = v___x_3091_;
v_a_3069_ = v_it_x27_3090_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_box(0);
lean_inc(v_snd_3071_);
v_pos_3073_ = v_a_3069_;
v_snd_3074_ = v_snd_3071_;
v_err_3075_ = v___x_3097_;
goto v___jp_3072_;
}
v___jp_3072_:
{
uint8_t v___x_3076_; 
v___x_3076_ = lean_nat_dec_eq(v_snd_3071_, v_snd_3074_);
lean_dec(v_snd_3074_);
lean_dec(v_snd_3071_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; 
lean_dec_ref(v_acc_3068_);
lean_inc(v_err_3075_);
v___x_3077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3077_, 0, v_pos_3073_);
lean_ctor_set(v___x_3077_, 1, v_err_3075_);
return v___x_3077_;
}
else
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3078_, 0, v_pos_3073_);
lean_ctor_set(v___x_3078_, 1, v_acc_3068_);
return v___x_3078_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0(void){
_start:
{
uint32_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = 89;
v___x_3099_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3100_ = lean_string_push(v___x_3099_, v___x_3098_);
return v___x_3100_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0);
v___x_3102_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3103_ = lean_string_append(v___x_3102_, v___x_3101_);
return v___x_3103_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3105_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1);
v___x_3106_ = lean_string_append(v___x_3105_, v___x_3104_);
return v___x_3106_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__2);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(lean_object* v_acc_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_fst_3111_; lean_object* v_snd_3112_; lean_object* v_pos_3114_; lean_object* v_snd_3115_; lean_object* v_err_3116_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v_fst_3111_ = lean_ctor_get(v_a_3110_, 0);
v_snd_3112_ = lean_ctor_get(v_a_3110_, 1);
lean_inc(v_snd_3112_);
v___x_3120_ = lean_string_utf8_byte_size(v_fst_3111_);
v___x_3121_ = lean_nat_dec_eq(v_snd_3112_, v___x_3120_);
if (v___x_3121_ == 0)
{
uint32_t v___x_3122_; uint32_t v_c_3123_; uint8_t v___x_3124_; 
v___x_3122_ = 89;
v_c_3123_ = lean_string_utf8_get_fast(v_fst_3111_, v_snd_3112_);
v___x_3124_ = lean_uint32_dec_eq(v_c_3123_, v___x_3122_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3);
lean_inc(v_snd_3112_);
v_pos_3114_ = v_a_3110_;
v_snd_3115_ = v_snd_3112_;
v_err_3116_ = v___x_3125_;
goto v___jp_3113_;
}
else
{
lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3135_; 
lean_inc(v_fst_3111_);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_a_3110_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; lean_object* v_unused_3137_; 
v_unused_3136_ = lean_ctor_get(v_a_3110_, 1);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_a_3110_, 0);
lean_dec(v_unused_3137_);
v___x_3127_ = v_a_3110_;
v_isShared_3128_ = v_isSharedCheck_3135_;
goto v_resetjp_3126_;
}
else
{
lean_dec(v_a_3110_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3135_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v_it_x27_3131_; 
v___x_3129_ = lean_string_utf8_next_fast(v_fst_3111_, v_snd_3112_);
lean_dec(v_snd_3112_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 1, v___x_3129_);
v_it_x27_3131_ = v___x_3127_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_fst_3111_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___x_3129_);
v_it_x27_3131_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_string_push(v_acc_3109_, v___x_3122_);
v_acc_3109_ = v___x_3132_;
v_a_3110_ = v_it_x27_3131_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_box(0);
lean_inc(v_snd_3112_);
v_pos_3114_ = v_a_3110_;
v_snd_3115_ = v_snd_3112_;
v_err_3116_ = v___x_3138_;
goto v___jp_3113_;
}
v___jp_3113_:
{
uint8_t v___x_3117_; 
v___x_3117_ = lean_nat_dec_eq(v_snd_3112_, v_snd_3115_);
lean_dec(v_snd_3115_);
lean_dec(v_snd_3112_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; 
lean_dec_ref(v_acc_3109_);
lean_inc(v_err_3116_);
v___x_3118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3118_, 0, v_pos_3114_);
lean_ctor_set(v___x_3118_, 1, v_err_3116_);
return v___x_3118_;
}
else
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_pos_3114_);
lean_ctor_set(v___x_3119_, 1, v_acc_3109_);
return v___x_3119_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0(void){
_start:
{
uint32_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = 110;
v___x_3140_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3141_ = lean_string_push(v___x_3140_, v___x_3139_);
return v___x_3141_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0);
v___x_3143_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3144_ = lean_string_append(v___x_3143_, v___x_3142_);
return v___x_3144_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3146_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1);
v___x_3147_ = lean_string_append(v___x_3146_, v___x_3145_);
return v___x_3147_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__2);
v___x_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(lean_object* v_acc_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v_fst_3152_; lean_object* v_snd_3153_; lean_object* v_pos_3155_; lean_object* v_snd_3156_; lean_object* v_err_3157_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v_fst_3152_ = lean_ctor_get(v_a_3151_, 0);
v_snd_3153_ = lean_ctor_get(v_a_3151_, 1);
lean_inc(v_snd_3153_);
v___x_3161_ = lean_string_utf8_byte_size(v_fst_3152_);
v___x_3162_ = lean_nat_dec_eq(v_snd_3153_, v___x_3161_);
if (v___x_3162_ == 0)
{
uint32_t v___x_3163_; uint32_t v_c_3164_; uint8_t v___x_3165_; 
v___x_3163_ = 110;
v_c_3164_ = lean_string_utf8_get_fast(v_fst_3152_, v_snd_3153_);
v___x_3165_ = lean_uint32_dec_eq(v_c_3164_, v___x_3163_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; 
v___x_3166_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3);
lean_inc(v_snd_3153_);
v_pos_3155_ = v_a_3151_;
v_snd_3156_ = v_snd_3153_;
v_err_3157_ = v___x_3166_;
goto v___jp_3154_;
}
else
{
lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3176_; 
lean_inc(v_fst_3152_);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_a_3151_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; lean_object* v_unused_3178_; 
v_unused_3177_ = lean_ctor_get(v_a_3151_, 1);
lean_dec(v_unused_3177_);
v_unused_3178_ = lean_ctor_get(v_a_3151_, 0);
lean_dec(v_unused_3178_);
v___x_3168_ = v_a_3151_;
v_isShared_3169_ = v_isSharedCheck_3176_;
goto v_resetjp_3167_;
}
else
{
lean_dec(v_a_3151_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3176_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v_it_x27_3172_; 
v___x_3170_ = lean_string_utf8_next_fast(v_fst_3152_, v_snd_3153_);
lean_dec(v_snd_3153_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 1, v___x_3170_);
v_it_x27_3172_ = v___x_3168_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_fst_3152_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v___x_3170_);
v_it_x27_3172_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; 
v___x_3173_ = lean_string_push(v_acc_3150_, v___x_3163_);
v_acc_3150_ = v___x_3173_;
v_a_3151_ = v_it_x27_3172_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3179_; 
v___x_3179_ = lean_box(0);
lean_inc(v_snd_3153_);
v_pos_3155_ = v_a_3151_;
v_snd_3156_ = v_snd_3153_;
v_err_3157_ = v___x_3179_;
goto v___jp_3154_;
}
v___jp_3154_:
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_nat_dec_eq(v_snd_3153_, v_snd_3156_);
lean_dec(v_snd_3156_);
lean_dec(v_snd_3153_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; 
lean_dec_ref(v_acc_3150_);
lean_inc(v_err_3157_);
v___x_3159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_pos_3155_);
lean_ctor_set(v___x_3159_, 1, v_err_3157_);
return v___x_3159_;
}
else
{
lean_object* v___x_3160_; 
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v_pos_3155_);
lean_ctor_set(v___x_3160_, 1, v_acc_3150_);
return v___x_3160_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0(void){
_start:
{
uint32_t v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3180_ = 71;
v___x_3181_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3182_ = lean_string_push(v___x_3181_, v___x_3180_);
return v___x_3182_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1(void){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0);
v___x_3184_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3185_ = lean_string_append(v___x_3184_, v___x_3183_);
return v___x_3185_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3187_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1);
v___x_3188_ = lean_string_append(v___x_3187_, v___x_3186_);
return v___x_3188_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__2);
v___x_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(lean_object* v_acc_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_fst_3193_; lean_object* v_snd_3194_; lean_object* v_pos_3196_; lean_object* v_snd_3197_; lean_object* v_err_3198_; lean_object* v___x_3202_; uint8_t v___x_3203_; 
v_fst_3193_ = lean_ctor_get(v_a_3192_, 0);
v_snd_3194_ = lean_ctor_get(v_a_3192_, 1);
lean_inc(v_snd_3194_);
v___x_3202_ = lean_string_utf8_byte_size(v_fst_3193_);
v___x_3203_ = lean_nat_dec_eq(v_snd_3194_, v___x_3202_);
if (v___x_3203_ == 0)
{
uint32_t v___x_3204_; uint32_t v_c_3205_; uint8_t v___x_3206_; 
v___x_3204_ = 71;
v_c_3205_ = lean_string_utf8_get_fast(v_fst_3193_, v_snd_3194_);
v___x_3206_ = lean_uint32_dec_eq(v_c_3205_, v___x_3204_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3);
lean_inc(v_snd_3194_);
v_pos_3196_ = v_a_3192_;
v_snd_3197_ = v_snd_3194_;
v_err_3198_ = v___x_3207_;
goto v___jp_3195_;
}
else
{
lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3217_; 
lean_inc(v_fst_3193_);
v_isSharedCheck_3217_ = !lean_is_exclusive(v_a_3192_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; lean_object* v_unused_3219_; 
v_unused_3218_ = lean_ctor_get(v_a_3192_, 1);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_a_3192_, 0);
lean_dec(v_unused_3219_);
v___x_3209_ = v_a_3192_;
v_isShared_3210_ = v_isSharedCheck_3217_;
goto v_resetjp_3208_;
}
else
{
lean_dec(v_a_3192_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3217_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3211_; lean_object* v_it_x27_3213_; 
v___x_3211_ = lean_string_utf8_next_fast(v_fst_3193_, v_snd_3194_);
lean_dec(v_snd_3194_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 1, v___x_3211_);
v_it_x27_3213_ = v___x_3209_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_fst_3193_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3211_);
v_it_x27_3213_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_string_push(v_acc_3191_, v___x_3204_);
v_acc_3191_ = v___x_3214_;
v_a_3192_ = v_it_x27_3213_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_box(0);
lean_inc(v_snd_3194_);
v_pos_3196_ = v_a_3192_;
v_snd_3197_ = v_snd_3194_;
v_err_3198_ = v___x_3220_;
goto v___jp_3195_;
}
v___jp_3195_:
{
uint8_t v___x_3199_; 
v___x_3199_ = lean_nat_dec_eq(v_snd_3194_, v_snd_3197_);
lean_dec(v_snd_3197_);
lean_dec(v_snd_3194_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; 
lean_dec_ref(v_acc_3191_);
lean_inc(v_err_3198_);
v___x_3200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3200_, 0, v_pos_3196_);
lean_ctor_set(v___x_3200_, 1, v_err_3198_);
return v___x_3200_;
}
else
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_pos_3196_);
lean_ctor_set(v___x_3201_, 1, v_acc_3191_);
return v___x_3201_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0(void){
_start:
{
uint32_t v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3221_ = 86;
v___x_3222_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3223_ = lean_string_push(v___x_3222_, v___x_3221_);
return v___x_3223_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0);
v___x_3225_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3226_ = lean_string_append(v___x_3225_, v___x_3224_);
return v___x_3226_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3228_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1);
v___x_3229_ = lean_string_append(v___x_3228_, v___x_3227_);
return v___x_3229_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__2);
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(lean_object* v_acc_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v_fst_3234_; lean_object* v_snd_3235_; lean_object* v_pos_3237_; lean_object* v_snd_3238_; lean_object* v_err_3239_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v_fst_3234_ = lean_ctor_get(v_a_3233_, 0);
v_snd_3235_ = lean_ctor_get(v_a_3233_, 1);
lean_inc(v_snd_3235_);
v___x_3243_ = lean_string_utf8_byte_size(v_fst_3234_);
v___x_3244_ = lean_nat_dec_eq(v_snd_3235_, v___x_3243_);
if (v___x_3244_ == 0)
{
uint32_t v___x_3245_; uint32_t v_c_3246_; uint8_t v___x_3247_; 
v___x_3245_ = 86;
v_c_3246_ = lean_string_utf8_get_fast(v_fst_3234_, v_snd_3235_);
v___x_3247_ = lean_uint32_dec_eq(v_c_3246_, v___x_3245_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3);
lean_inc(v_snd_3235_);
v_pos_3237_ = v_a_3233_;
v_snd_3238_ = v_snd_3235_;
v_err_3239_ = v___x_3248_;
goto v___jp_3236_;
}
else
{
lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3258_; 
lean_inc(v_fst_3234_);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_a_3233_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; lean_object* v_unused_3260_; 
v_unused_3259_ = lean_ctor_get(v_a_3233_, 1);
lean_dec(v_unused_3259_);
v_unused_3260_ = lean_ctor_get(v_a_3233_, 0);
lean_dec(v_unused_3260_);
v___x_3250_ = v_a_3233_;
v_isShared_3251_ = v_isSharedCheck_3258_;
goto v_resetjp_3249_;
}
else
{
lean_dec(v_a_3233_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3258_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3252_; lean_object* v_it_x27_3254_; 
v___x_3252_ = lean_string_utf8_next_fast(v_fst_3234_, v_snd_3235_);
lean_dec(v_snd_3235_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 1, v___x_3252_);
v_it_x27_3254_ = v___x_3250_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_fst_3234_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v___x_3252_);
v_it_x27_3254_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_string_push(v_acc_3232_, v___x_3245_);
v_acc_3232_ = v___x_3255_;
v_a_3233_ = v_it_x27_3254_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_box(0);
lean_inc(v_snd_3235_);
v_pos_3237_ = v_a_3233_;
v_snd_3238_ = v_snd_3235_;
v_err_3239_ = v___x_3261_;
goto v___jp_3236_;
}
v___jp_3236_:
{
uint8_t v___x_3240_; 
v___x_3240_ = lean_nat_dec_eq(v_snd_3235_, v_snd_3238_);
lean_dec(v_snd_3238_);
lean_dec(v_snd_3235_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; 
lean_dec_ref(v_acc_3232_);
lean_inc(v_err_3239_);
v___x_3241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3241_, 0, v_pos_3237_);
lean_ctor_set(v___x_3241_, 1, v_err_3239_);
return v___x_3241_;
}
else
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v_pos_3237_);
lean_ctor_set(v___x_3242_, 1, v_acc_3232_);
return v___x_3242_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0(void){
_start:
{
uint32_t v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = 83;
v___x_3263_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3264_ = lean_string_push(v___x_3263_, v___x_3262_);
return v___x_3264_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0);
v___x_3266_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3267_ = lean_string_append(v___x_3266_, v___x_3265_);
return v___x_3267_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3268_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3269_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1);
v___x_3270_ = lean_string_append(v___x_3269_, v___x_3268_);
return v___x_3270_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3(void){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__2);
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(lean_object* v_acc_3273_, lean_object* v_a_3274_){
_start:
{
lean_object* v_fst_3275_; lean_object* v_snd_3276_; lean_object* v_pos_3278_; lean_object* v_snd_3279_; lean_object* v_err_3280_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_fst_3275_ = lean_ctor_get(v_a_3274_, 0);
v_snd_3276_ = lean_ctor_get(v_a_3274_, 1);
lean_inc(v_snd_3276_);
v___x_3284_ = lean_string_utf8_byte_size(v_fst_3275_);
v___x_3285_ = lean_nat_dec_eq(v_snd_3276_, v___x_3284_);
if (v___x_3285_ == 0)
{
uint32_t v___x_3286_; uint32_t v_c_3287_; uint8_t v___x_3288_; 
v___x_3286_ = 83;
v_c_3287_ = lean_string_utf8_get_fast(v_fst_3275_, v_snd_3276_);
v___x_3288_ = lean_uint32_dec_eq(v_c_3287_, v___x_3286_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
v___x_3289_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3);
lean_inc(v_snd_3276_);
v_pos_3278_ = v_a_3274_;
v_snd_3279_ = v_snd_3276_;
v_err_3280_ = v___x_3289_;
goto v___jp_3277_;
}
else
{
lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3299_; 
lean_inc(v_fst_3275_);
v_isSharedCheck_3299_ = !lean_is_exclusive(v_a_3274_);
if (v_isSharedCheck_3299_ == 0)
{
lean_object* v_unused_3300_; lean_object* v_unused_3301_; 
v_unused_3300_ = lean_ctor_get(v_a_3274_, 1);
lean_dec(v_unused_3300_);
v_unused_3301_ = lean_ctor_get(v_a_3274_, 0);
lean_dec(v_unused_3301_);
v___x_3291_ = v_a_3274_;
v_isShared_3292_ = v_isSharedCheck_3299_;
goto v_resetjp_3290_;
}
else
{
lean_dec(v_a_3274_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3299_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v_it_x27_3295_; 
v___x_3293_ = lean_string_utf8_next_fast(v_fst_3275_, v_snd_3276_);
lean_dec(v_snd_3276_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v___x_3293_);
v_it_x27_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_fst_3275_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v___x_3293_);
v_it_x27_3295_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_string_push(v_acc_3273_, v___x_3286_);
v_acc_3273_ = v___x_3296_;
v_a_3274_ = v_it_x27_3295_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_box(0);
lean_inc(v_snd_3276_);
v_pos_3278_ = v_a_3274_;
v_snd_3279_ = v_snd_3276_;
v_err_3280_ = v___x_3302_;
goto v___jp_3277_;
}
v___jp_3277_:
{
uint8_t v___x_3281_; 
v___x_3281_ = lean_nat_dec_eq(v_snd_3276_, v_snd_3279_);
lean_dec(v_snd_3279_);
lean_dec(v_snd_3276_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; 
lean_dec_ref(v_acc_3273_);
lean_inc(v_err_3280_);
v___x_3282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3282_, 0, v_pos_3278_);
lean_ctor_set(v___x_3282_, 1, v_err_3280_);
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v_pos_3278_);
lean_ctor_set(v___x_3283_, 1, v_acc_3273_);
return v___x_3283_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0(void){
_start:
{
uint32_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = 104;
v___x_3304_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3305_ = lean_string_push(v___x_3304_, v___x_3303_);
return v___x_3305_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3306_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0);
v___x_3307_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3308_ = lean_string_append(v___x_3307_, v___x_3306_);
return v___x_3308_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3309_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3310_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1);
v___x_3311_ = lean_string_append(v___x_3310_, v___x_3309_);
return v___x_3311_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__2);
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(lean_object* v_acc_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_fst_3316_; lean_object* v_snd_3317_; lean_object* v_pos_3319_; lean_object* v_snd_3320_; lean_object* v_err_3321_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v_fst_3316_ = lean_ctor_get(v_a_3315_, 0);
v_snd_3317_ = lean_ctor_get(v_a_3315_, 1);
lean_inc(v_snd_3317_);
v___x_3325_ = lean_string_utf8_byte_size(v_fst_3316_);
v___x_3326_ = lean_nat_dec_eq(v_snd_3317_, v___x_3325_);
if (v___x_3326_ == 0)
{
uint32_t v___x_3327_; uint32_t v_c_3328_; uint8_t v___x_3329_; 
v___x_3327_ = 104;
v_c_3328_ = lean_string_utf8_get_fast(v_fst_3316_, v_snd_3317_);
v___x_3329_ = lean_uint32_dec_eq(v_c_3328_, v___x_3327_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3);
lean_inc(v_snd_3317_);
v_pos_3319_ = v_a_3315_;
v_snd_3320_ = v_snd_3317_;
v_err_3321_ = v___x_3330_;
goto v___jp_3318_;
}
else
{
lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3340_; 
lean_inc(v_fst_3316_);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_a_3315_);
if (v_isSharedCheck_3340_ == 0)
{
lean_object* v_unused_3341_; lean_object* v_unused_3342_; 
v_unused_3341_ = lean_ctor_get(v_a_3315_, 1);
lean_dec(v_unused_3341_);
v_unused_3342_ = lean_ctor_get(v_a_3315_, 0);
lean_dec(v_unused_3342_);
v___x_3332_ = v_a_3315_;
v_isShared_3333_ = v_isSharedCheck_3340_;
goto v_resetjp_3331_;
}
else
{
lean_dec(v_a_3315_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3340_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v_it_x27_3336_; 
v___x_3334_ = lean_string_utf8_next_fast(v_fst_3316_, v_snd_3317_);
lean_dec(v_snd_3317_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 1, v___x_3334_);
v_it_x27_3336_ = v___x_3332_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_fst_3316_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v___x_3334_);
v_it_x27_3336_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3337_; 
v___x_3337_ = lean_string_push(v_acc_3314_, v___x_3327_);
v_acc_3314_ = v___x_3337_;
v_a_3315_ = v_it_x27_3336_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3343_; 
v___x_3343_ = lean_box(0);
lean_inc(v_snd_3317_);
v_pos_3319_ = v_a_3315_;
v_snd_3320_ = v_snd_3317_;
v_err_3321_ = v___x_3343_;
goto v___jp_3318_;
}
v___jp_3318_:
{
uint8_t v___x_3322_; 
v___x_3322_ = lean_nat_dec_eq(v_snd_3317_, v_snd_3320_);
lean_dec(v_snd_3320_);
lean_dec(v_snd_3317_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; 
lean_dec_ref(v_acc_3314_);
lean_inc(v_err_3321_);
v___x_3323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3323_, 0, v_pos_3319_);
lean_ctor_set(v___x_3323_, 1, v_err_3321_);
return v___x_3323_;
}
else
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v_pos_3319_);
lean_ctor_set(v___x_3324_, 1, v_acc_3314_);
return v___x_3324_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0(void){
_start:
{
uint32_t v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3344_ = 81;
v___x_3345_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3346_ = lean_string_push(v___x_3345_, v___x_3344_);
return v___x_3346_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3347_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0);
v___x_3348_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3349_ = lean_string_append(v___x_3348_, v___x_3347_);
return v___x_3349_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3351_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1);
v___x_3352_ = lean_string_append(v___x_3351_, v___x_3350_);
return v___x_3352_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__2);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(lean_object* v_acc_3355_, lean_object* v_a_3356_){
_start:
{
lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v_pos_3360_; lean_object* v_snd_3361_; lean_object* v_err_3362_; lean_object* v___x_3366_; uint8_t v___x_3367_; 
v_fst_3357_ = lean_ctor_get(v_a_3356_, 0);
v_snd_3358_ = lean_ctor_get(v_a_3356_, 1);
lean_inc(v_snd_3358_);
v___x_3366_ = lean_string_utf8_byte_size(v_fst_3357_);
v___x_3367_ = lean_nat_dec_eq(v_snd_3358_, v___x_3366_);
if (v___x_3367_ == 0)
{
uint32_t v___x_3368_; uint32_t v_c_3369_; uint8_t v___x_3370_; 
v___x_3368_ = 81;
v_c_3369_ = lean_string_utf8_get_fast(v_fst_3357_, v_snd_3358_);
v___x_3370_ = lean_uint32_dec_eq(v_c_3369_, v___x_3368_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; 
v___x_3371_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3);
lean_inc(v_snd_3358_);
v_pos_3360_ = v_a_3356_;
v_snd_3361_ = v_snd_3358_;
v_err_3362_ = v___x_3371_;
goto v___jp_3359_;
}
else
{
lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3381_; 
lean_inc(v_fst_3357_);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_a_3356_);
if (v_isSharedCheck_3381_ == 0)
{
lean_object* v_unused_3382_; lean_object* v_unused_3383_; 
v_unused_3382_ = lean_ctor_get(v_a_3356_, 1);
lean_dec(v_unused_3382_);
v_unused_3383_ = lean_ctor_get(v_a_3356_, 0);
lean_dec(v_unused_3383_);
v___x_3373_ = v_a_3356_;
v_isShared_3374_ = v_isSharedCheck_3381_;
goto v_resetjp_3372_;
}
else
{
lean_dec(v_a_3356_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3381_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3375_; lean_object* v_it_x27_3377_; 
v___x_3375_ = lean_string_utf8_next_fast(v_fst_3357_, v_snd_3358_);
lean_dec(v_snd_3358_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 1, v___x_3375_);
v_it_x27_3377_ = v___x_3373_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_fst_3357_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v___x_3375_);
v_it_x27_3377_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_string_push(v_acc_3355_, v___x_3368_);
v_acc_3355_ = v___x_3378_;
v_a_3356_ = v_it_x27_3377_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3384_; 
v___x_3384_ = lean_box(0);
lean_inc(v_snd_3358_);
v_pos_3360_ = v_a_3356_;
v_snd_3361_ = v_snd_3358_;
v_err_3362_ = v___x_3384_;
goto v___jp_3359_;
}
v___jp_3359_:
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_nat_dec_eq(v_snd_3358_, v_snd_3361_);
lean_dec(v_snd_3361_);
lean_dec(v_snd_3358_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_dec_ref(v_acc_3355_);
lean_inc(v_err_3362_);
v___x_3364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3364_, 0, v_pos_3360_);
lean_ctor_set(v___x_3364_, 1, v_err_3362_);
return v___x_3364_;
}
else
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3365_, 0, v_pos_3360_);
lean_ctor_set(v___x_3365_, 1, v_acc_3355_);
return v___x_3365_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0(void){
_start:
{
uint32_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3385_ = 68;
v___x_3386_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3387_ = lean_string_push(v___x_3386_, v___x_3385_);
return v___x_3387_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1(void){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0);
v___x_3389_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3390_ = lean_string_append(v___x_3389_, v___x_3388_);
return v___x_3390_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3392_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1);
v___x_3393_ = lean_string_append(v___x_3392_, v___x_3391_);
return v___x_3393_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__2);
v___x_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(lean_object* v_acc_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_fst_3398_; lean_object* v_snd_3399_; lean_object* v_pos_3401_; lean_object* v_snd_3402_; lean_object* v_err_3403_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v_fst_3398_ = lean_ctor_get(v_a_3397_, 0);
v_snd_3399_ = lean_ctor_get(v_a_3397_, 1);
lean_inc(v_snd_3399_);
v___x_3407_ = lean_string_utf8_byte_size(v_fst_3398_);
v___x_3408_ = lean_nat_dec_eq(v_snd_3399_, v___x_3407_);
if (v___x_3408_ == 0)
{
uint32_t v___x_3409_; uint32_t v_c_3410_; uint8_t v___x_3411_; 
v___x_3409_ = 68;
v_c_3410_ = lean_string_utf8_get_fast(v_fst_3398_, v_snd_3399_);
v___x_3411_ = lean_uint32_dec_eq(v_c_3410_, v___x_3409_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3);
lean_inc(v_snd_3399_);
v_pos_3401_ = v_a_3397_;
v_snd_3402_ = v_snd_3399_;
v_err_3403_ = v___x_3412_;
goto v___jp_3400_;
}
else
{
lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3422_; 
lean_inc(v_fst_3398_);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_a_3397_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; lean_object* v_unused_3424_; 
v_unused_3423_ = lean_ctor_get(v_a_3397_, 1);
lean_dec(v_unused_3423_);
v_unused_3424_ = lean_ctor_get(v_a_3397_, 0);
lean_dec(v_unused_3424_);
v___x_3414_ = v_a_3397_;
v_isShared_3415_ = v_isSharedCheck_3422_;
goto v_resetjp_3413_;
}
else
{
lean_dec(v_a_3397_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3422_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v_it_x27_3418_; 
v___x_3416_ = lean_string_utf8_next_fast(v_fst_3398_, v_snd_3399_);
lean_dec(v_snd_3399_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 1, v___x_3416_);
v_it_x27_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_fst_3398_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v___x_3416_);
v_it_x27_3418_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3419_; 
v___x_3419_ = lean_string_push(v_acc_3396_, v___x_3409_);
v_acc_3396_ = v___x_3419_;
v_a_3397_ = v_it_x27_3418_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_box(0);
lean_inc(v_snd_3399_);
v_pos_3401_ = v_a_3397_;
v_snd_3402_ = v_snd_3399_;
v_err_3403_ = v___x_3425_;
goto v___jp_3400_;
}
v___jp_3400_:
{
uint8_t v___x_3404_; 
v___x_3404_ = lean_nat_dec_eq(v_snd_3399_, v_snd_3402_);
lean_dec(v_snd_3402_);
lean_dec(v_snd_3399_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; 
lean_dec_ref(v_acc_3396_);
lean_inc(v_err_3403_);
v___x_3405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3405_, 0, v_pos_3401_);
lean_ctor_set(v___x_3405_, 1, v_err_3403_);
return v___x_3405_;
}
else
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v_pos_3401_);
lean_ctor_set(v___x_3406_, 1, v_acc_3396_);
return v___x_3406_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0(void){
_start:
{
uint32_t v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3426_ = 88;
v___x_3427_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3428_ = lean_string_push(v___x_3427_, v___x_3426_);
return v___x_3428_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0);
v___x_3430_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3431_ = lean_string_append(v___x_3430_, v___x_3429_);
return v___x_3431_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3433_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1);
v___x_3434_ = lean_string_append(v___x_3433_, v___x_3432_);
return v___x_3434_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__2);
v___x_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(lean_object* v_acc_3437_, lean_object* v_a_3438_){
_start:
{
lean_object* v_fst_3439_; lean_object* v_snd_3440_; lean_object* v_pos_3442_; lean_object* v_snd_3443_; lean_object* v_err_3444_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v_fst_3439_ = lean_ctor_get(v_a_3438_, 0);
v_snd_3440_ = lean_ctor_get(v_a_3438_, 1);
lean_inc(v_snd_3440_);
v___x_3448_ = lean_string_utf8_byte_size(v_fst_3439_);
v___x_3449_ = lean_nat_dec_eq(v_snd_3440_, v___x_3448_);
if (v___x_3449_ == 0)
{
uint32_t v___x_3450_; uint32_t v_c_3451_; uint8_t v___x_3452_; 
v___x_3450_ = 88;
v_c_3451_ = lean_string_utf8_get_fast(v_fst_3439_, v_snd_3440_);
v___x_3452_ = lean_uint32_dec_eq(v_c_3451_, v___x_3450_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3);
lean_inc(v_snd_3440_);
v_pos_3442_ = v_a_3438_;
v_snd_3443_ = v_snd_3440_;
v_err_3444_ = v___x_3453_;
goto v___jp_3441_;
}
else
{
lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3463_; 
lean_inc(v_fst_3439_);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_a_3438_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; lean_object* v_unused_3465_; 
v_unused_3464_ = lean_ctor_get(v_a_3438_, 1);
lean_dec(v_unused_3464_);
v_unused_3465_ = lean_ctor_get(v_a_3438_, 0);
lean_dec(v_unused_3465_);
v___x_3455_ = v_a_3438_;
v_isShared_3456_ = v_isSharedCheck_3463_;
goto v_resetjp_3454_;
}
else
{
lean_dec(v_a_3438_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3463_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v_it_x27_3459_; 
v___x_3457_ = lean_string_utf8_next_fast(v_fst_3439_, v_snd_3440_);
lean_dec(v_snd_3440_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 1, v___x_3457_);
v_it_x27_3459_ = v___x_3455_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_fst_3439_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v___x_3457_);
v_it_x27_3459_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_string_push(v_acc_3437_, v___x_3450_);
v_acc_3437_ = v___x_3460_;
v_a_3438_ = v_it_x27_3459_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3466_; 
v___x_3466_ = lean_box(0);
lean_inc(v_snd_3440_);
v_pos_3442_ = v_a_3438_;
v_snd_3443_ = v_snd_3440_;
v_err_3444_ = v___x_3466_;
goto v___jp_3441_;
}
v___jp_3441_:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_nat_dec_eq(v_snd_3440_, v_snd_3443_);
lean_dec(v_snd_3443_);
lean_dec(v_snd_3440_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
lean_dec_ref(v_acc_3437_);
lean_inc(v_err_3444_);
v___x_3446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_pos_3442_);
lean_ctor_set(v___x_3446_, 1, v_err_3444_);
return v___x_3446_;
}
else
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v_pos_3442_);
lean_ctor_set(v___x_3447_, 1, v_acc_3437_);
return v___x_3447_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0(void){
_start:
{
uint32_t v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3467_ = 122;
v___x_3468_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3469_ = lean_string_push(v___x_3468_, v___x_3467_);
return v___x_3469_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1(void){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3470_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0);
v___x_3471_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3472_ = lean_string_append(v___x_3471_, v___x_3470_);
return v___x_3472_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3474_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1);
v___x_3475_ = lean_string_append(v___x_3474_, v___x_3473_);
return v___x_3475_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3476_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__2);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(lean_object* v_acc_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_fst_3480_; lean_object* v_snd_3481_; lean_object* v_pos_3483_; lean_object* v_snd_3484_; lean_object* v_err_3485_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v_fst_3480_ = lean_ctor_get(v_a_3479_, 0);
v_snd_3481_ = lean_ctor_get(v_a_3479_, 1);
lean_inc(v_snd_3481_);
v___x_3489_ = lean_string_utf8_byte_size(v_fst_3480_);
v___x_3490_ = lean_nat_dec_eq(v_snd_3481_, v___x_3489_);
if (v___x_3490_ == 0)
{
uint32_t v___x_3491_; uint32_t v_c_3492_; uint8_t v___x_3493_; 
v___x_3491_ = 122;
v_c_3492_ = lean_string_utf8_get_fast(v_fst_3480_, v_snd_3481_);
v___x_3493_ = lean_uint32_dec_eq(v_c_3492_, v___x_3491_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; 
v___x_3494_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3);
lean_inc(v_snd_3481_);
v_pos_3483_ = v_a_3479_;
v_snd_3484_ = v_snd_3481_;
v_err_3485_ = v___x_3494_;
goto v___jp_3482_;
}
else
{
lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3504_; 
lean_inc(v_fst_3480_);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_a_3479_);
if (v_isSharedCheck_3504_ == 0)
{
lean_object* v_unused_3505_; lean_object* v_unused_3506_; 
v_unused_3505_ = lean_ctor_get(v_a_3479_, 1);
lean_dec(v_unused_3505_);
v_unused_3506_ = lean_ctor_get(v_a_3479_, 0);
lean_dec(v_unused_3506_);
v___x_3496_ = v_a_3479_;
v_isShared_3497_ = v_isSharedCheck_3504_;
goto v_resetjp_3495_;
}
else
{
lean_dec(v_a_3479_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3504_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v_it_x27_3500_; 
v___x_3498_ = lean_string_utf8_next_fast(v_fst_3480_, v_snd_3481_);
lean_dec(v_snd_3481_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 1, v___x_3498_);
v_it_x27_3500_ = v___x_3496_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_fst_3480_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v___x_3498_);
v_it_x27_3500_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_string_push(v_acc_3478_, v___x_3491_);
v_acc_3478_ = v___x_3501_;
v_a_3479_ = v_it_x27_3500_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3507_; 
v___x_3507_ = lean_box(0);
lean_inc(v_snd_3481_);
v_pos_3483_ = v_a_3479_;
v_snd_3484_ = v_snd_3481_;
v_err_3485_ = v___x_3507_;
goto v___jp_3482_;
}
v___jp_3482_:
{
uint8_t v___x_3486_; 
v___x_3486_ = lean_nat_dec_eq(v_snd_3481_, v_snd_3484_);
lean_dec(v_snd_3484_);
lean_dec(v_snd_3481_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; 
lean_dec_ref(v_acc_3478_);
lean_inc(v_err_3485_);
v___x_3487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3487_, 0, v_pos_3483_);
lean_ctor_set(v___x_3487_, 1, v_err_3485_);
return v___x_3487_;
}
else
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v_pos_3483_);
lean_ctor_set(v___x_3488_, 1, v_acc_3478_);
return v___x_3488_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0(void){
_start:
{
uint32_t v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3508_ = 115;
v___x_3509_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3510_ = lean_string_push(v___x_3509_, v___x_3508_);
return v___x_3510_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0);
v___x_3512_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3513_ = lean_string_append(v___x_3512_, v___x_3511_);
return v___x_3513_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3515_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1);
v___x_3516_ = lean_string_append(v___x_3515_, v___x_3514_);
return v___x_3516_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__2);
v___x_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(lean_object* v_acc_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_fst_3521_; lean_object* v_snd_3522_; lean_object* v_pos_3524_; lean_object* v_snd_3525_; lean_object* v_err_3526_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v_fst_3521_ = lean_ctor_get(v_a_3520_, 0);
v_snd_3522_ = lean_ctor_get(v_a_3520_, 1);
lean_inc(v_snd_3522_);
v___x_3530_ = lean_string_utf8_byte_size(v_fst_3521_);
v___x_3531_ = lean_nat_dec_eq(v_snd_3522_, v___x_3530_);
if (v___x_3531_ == 0)
{
uint32_t v___x_3532_; uint32_t v_c_3533_; uint8_t v___x_3534_; 
v___x_3532_ = 115;
v_c_3533_ = lean_string_utf8_get_fast(v_fst_3521_, v_snd_3522_);
v___x_3534_ = lean_uint32_dec_eq(v_c_3533_, v___x_3532_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3);
lean_inc(v_snd_3522_);
v_pos_3524_ = v_a_3520_;
v_snd_3525_ = v_snd_3522_;
v_err_3526_ = v___x_3535_;
goto v___jp_3523_;
}
else
{
lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3545_; 
lean_inc(v_fst_3521_);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; lean_object* v_unused_3547_; 
v_unused_3546_ = lean_ctor_get(v_a_3520_, 1);
lean_dec(v_unused_3546_);
v_unused_3547_ = lean_ctor_get(v_a_3520_, 0);
lean_dec(v_unused_3547_);
v___x_3537_ = v_a_3520_;
v_isShared_3538_ = v_isSharedCheck_3545_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v_a_3520_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3545_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v_it_x27_3541_; 
v___x_3539_ = lean_string_utf8_next_fast(v_fst_3521_, v_snd_3522_);
lean_dec(v_snd_3522_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 1, v___x_3539_);
v_it_x27_3541_ = v___x_3537_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_fst_3521_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v___x_3539_);
v_it_x27_3541_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3542_; 
v___x_3542_ = lean_string_push(v_acc_3519_, v___x_3532_);
v_acc_3519_ = v___x_3542_;
v_a_3520_ = v_it_x27_3541_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3548_; 
v___x_3548_ = lean_box(0);
lean_inc(v_snd_3522_);
v_pos_3524_ = v_a_3520_;
v_snd_3525_ = v_snd_3522_;
v_err_3526_ = v___x_3548_;
goto v___jp_3523_;
}
v___jp_3523_:
{
uint8_t v___x_3527_; 
v___x_3527_ = lean_nat_dec_eq(v_snd_3522_, v_snd_3525_);
lean_dec(v_snd_3525_);
lean_dec(v_snd_3522_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; 
lean_dec_ref(v_acc_3519_);
lean_inc(v_err_3526_);
v___x_3528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3528_, 0, v_pos_3524_);
lean_ctor_set(v___x_3528_, 1, v_err_3526_);
return v___x_3528_;
}
else
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_pos_3524_);
lean_ctor_set(v___x_3529_, 1, v_acc_3519_);
return v___x_3529_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0(void){
_start:
{
uint32_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = 75;
v___x_3550_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3551_ = lean_string_push(v___x_3550_, v___x_3549_);
return v___x_3551_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0);
v___x_3553_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3554_ = lean_string_append(v___x_3553_, v___x_3552_);
return v___x_3554_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3556_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1);
v___x_3557_ = lean_string_append(v___x_3556_, v___x_3555_);
return v___x_3557_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__2);
v___x_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(lean_object* v_acc_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_fst_3562_; lean_object* v_snd_3563_; lean_object* v_pos_3565_; lean_object* v_snd_3566_; lean_object* v_err_3567_; lean_object* v___x_3571_; uint8_t v___x_3572_; 
v_fst_3562_ = lean_ctor_get(v_a_3561_, 0);
v_snd_3563_ = lean_ctor_get(v_a_3561_, 1);
lean_inc(v_snd_3563_);
v___x_3571_ = lean_string_utf8_byte_size(v_fst_3562_);
v___x_3572_ = lean_nat_dec_eq(v_snd_3563_, v___x_3571_);
if (v___x_3572_ == 0)
{
uint32_t v___x_3573_; uint32_t v_c_3574_; uint8_t v___x_3575_; 
v___x_3573_ = 75;
v_c_3574_ = lean_string_utf8_get_fast(v_fst_3562_, v_snd_3563_);
v___x_3575_ = lean_uint32_dec_eq(v_c_3574_, v___x_3573_);
if (v___x_3575_ == 0)
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3);
lean_inc(v_snd_3563_);
v_pos_3565_ = v_a_3561_;
v_snd_3566_ = v_snd_3563_;
v_err_3567_ = v___x_3576_;
goto v___jp_3564_;
}
else
{
lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3586_; 
lean_inc(v_fst_3562_);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_a_3561_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; lean_object* v_unused_3588_; 
v_unused_3587_ = lean_ctor_get(v_a_3561_, 1);
lean_dec(v_unused_3587_);
v_unused_3588_ = lean_ctor_get(v_a_3561_, 0);
lean_dec(v_unused_3588_);
v___x_3578_ = v_a_3561_;
v_isShared_3579_ = v_isSharedCheck_3586_;
goto v_resetjp_3577_;
}
else
{
lean_dec(v_a_3561_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3586_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v_it_x27_3582_; 
v___x_3580_ = lean_string_utf8_next_fast(v_fst_3562_, v_snd_3563_);
lean_dec(v_snd_3563_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 1, v___x_3580_);
v_it_x27_3582_ = v___x_3578_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_fst_3562_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v___x_3580_);
v_it_x27_3582_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3583_; 
v___x_3583_ = lean_string_push(v_acc_3560_, v___x_3573_);
v_acc_3560_ = v___x_3583_;
v_a_3561_ = v_it_x27_3582_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3589_; 
v___x_3589_ = lean_box(0);
lean_inc(v_snd_3563_);
v_pos_3565_ = v_a_3561_;
v_snd_3566_ = v_snd_3563_;
v_err_3567_ = v___x_3589_;
goto v___jp_3564_;
}
v___jp_3564_:
{
uint8_t v___x_3568_; 
v___x_3568_ = lean_nat_dec_eq(v_snd_3563_, v_snd_3566_);
lean_dec(v_snd_3566_);
lean_dec(v_snd_3563_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; 
lean_dec_ref(v_acc_3560_);
lean_inc(v_err_3567_);
v___x_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3569_, 0, v_pos_3565_);
lean_ctor_set(v___x_3569_, 1, v_err_3567_);
return v___x_3569_;
}
else
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_pos_3565_);
lean_ctor_set(v___x_3570_, 1, v_acc_3560_);
return v___x_3570_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0(void){
_start:
{
uint32_t v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = 101;
v___x_3591_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3592_ = lean_string_push(v___x_3591_, v___x_3590_);
return v___x_3592_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0);
v___x_3594_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3595_ = lean_string_append(v___x_3594_, v___x_3593_);
return v___x_3595_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3596_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3597_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1);
v___x_3598_ = lean_string_append(v___x_3597_, v___x_3596_);
return v___x_3598_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3(void){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__2);
v___x_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(lean_object* v_acc_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v_fst_3603_; lean_object* v_snd_3604_; lean_object* v_pos_3606_; lean_object* v_snd_3607_; lean_object* v_err_3608_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v_fst_3603_ = lean_ctor_get(v_a_3602_, 0);
v_snd_3604_ = lean_ctor_get(v_a_3602_, 1);
lean_inc(v_snd_3604_);
v___x_3612_ = lean_string_utf8_byte_size(v_fst_3603_);
v___x_3613_ = lean_nat_dec_eq(v_snd_3604_, v___x_3612_);
if (v___x_3613_ == 0)
{
uint32_t v___x_3614_; uint32_t v_c_3615_; uint8_t v___x_3616_; 
v___x_3614_ = 101;
v_c_3615_ = lean_string_utf8_get_fast(v_fst_3603_, v_snd_3604_);
v___x_3616_ = lean_uint32_dec_eq(v_c_3615_, v___x_3614_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; 
v___x_3617_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3);
lean_inc(v_snd_3604_);
v_pos_3606_ = v_a_3602_;
v_snd_3607_ = v_snd_3604_;
v_err_3608_ = v___x_3617_;
goto v___jp_3605_;
}
else
{
lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3627_; 
lean_inc(v_fst_3603_);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_a_3602_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; lean_object* v_unused_3629_; 
v_unused_3628_ = lean_ctor_get(v_a_3602_, 1);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_a_3602_, 0);
lean_dec(v_unused_3629_);
v___x_3619_ = v_a_3602_;
v_isShared_3620_ = v_isSharedCheck_3627_;
goto v_resetjp_3618_;
}
else
{
lean_dec(v_a_3602_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3627_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3621_; lean_object* v_it_x27_3623_; 
v___x_3621_ = lean_string_utf8_next_fast(v_fst_3603_, v_snd_3604_);
lean_dec(v_snd_3604_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3621_);
v_it_x27_3623_ = v___x_3619_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_fst_3603_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v___x_3621_);
v_it_x27_3623_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3624_; 
v___x_3624_ = lean_string_push(v_acc_3601_, v___x_3614_);
v_acc_3601_ = v___x_3624_;
v_a_3602_ = v_it_x27_3623_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3630_; 
v___x_3630_ = lean_box(0);
lean_inc(v_snd_3604_);
v_pos_3606_ = v_a_3602_;
v_snd_3607_ = v_snd_3604_;
v_err_3608_ = v___x_3630_;
goto v___jp_3605_;
}
v___jp_3605_:
{
uint8_t v___x_3609_; 
v___x_3609_ = lean_nat_dec_eq(v_snd_3604_, v_snd_3607_);
lean_dec(v_snd_3607_);
lean_dec(v_snd_3604_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
lean_dec_ref(v_acc_3601_);
lean_inc(v_err_3608_);
v___x_3610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3610_, 0, v_pos_3606_);
lean_ctor_set(v___x_3610_, 1, v_err_3608_);
return v___x_3610_;
}
else
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3611_, 0, v_pos_3606_);
lean_ctor_set(v___x_3611_, 1, v_acc_3601_);
return v___x_3611_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0(void){
_start:
{
uint32_t v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = 77;
v___x_3632_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3633_ = lean_string_push(v___x_3632_, v___x_3631_);
return v___x_3633_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3634_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0);
v___x_3635_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3636_ = lean_string_append(v___x_3635_, v___x_3634_);
return v___x_3636_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3638_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1);
v___x_3639_ = lean_string_append(v___x_3638_, v___x_3637_);
return v___x_3639_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__2);
v___x_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(lean_object* v_acc_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v_fst_3644_; lean_object* v_snd_3645_; lean_object* v_pos_3647_; lean_object* v_snd_3648_; lean_object* v_err_3649_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v_fst_3644_ = lean_ctor_get(v_a_3643_, 0);
v_snd_3645_ = lean_ctor_get(v_a_3643_, 1);
lean_inc(v_snd_3645_);
v___x_3653_ = lean_string_utf8_byte_size(v_fst_3644_);
v___x_3654_ = lean_nat_dec_eq(v_snd_3645_, v___x_3653_);
if (v___x_3654_ == 0)
{
uint32_t v___x_3655_; uint32_t v_c_3656_; uint8_t v___x_3657_; 
v___x_3655_ = 77;
v_c_3656_ = lean_string_utf8_get_fast(v_fst_3644_, v_snd_3645_);
v___x_3657_ = lean_uint32_dec_eq(v_c_3656_, v___x_3655_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; 
v___x_3658_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3);
lean_inc(v_snd_3645_);
v_pos_3647_ = v_a_3643_;
v_snd_3648_ = v_snd_3645_;
v_err_3649_ = v___x_3658_;
goto v___jp_3646_;
}
else
{
lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3668_; 
lean_inc(v_fst_3644_);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_a_3643_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; lean_object* v_unused_3670_; 
v_unused_3669_ = lean_ctor_get(v_a_3643_, 1);
lean_dec(v_unused_3669_);
v_unused_3670_ = lean_ctor_get(v_a_3643_, 0);
lean_dec(v_unused_3670_);
v___x_3660_ = v_a_3643_;
v_isShared_3661_ = v_isSharedCheck_3668_;
goto v_resetjp_3659_;
}
else
{
lean_dec(v_a_3643_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3668_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v_it_x27_3664_; 
v___x_3662_ = lean_string_utf8_next_fast(v_fst_3644_, v_snd_3645_);
lean_dec(v_snd_3645_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 1, v___x_3662_);
v_it_x27_3664_ = v___x_3660_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_fst_3644_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v___x_3662_);
v_it_x27_3664_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3665_; 
v___x_3665_ = lean_string_push(v_acc_3642_, v___x_3655_);
v_acc_3642_ = v___x_3665_;
v_a_3643_ = v_it_x27_3664_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3671_; 
v___x_3671_ = lean_box(0);
lean_inc(v_snd_3645_);
v_pos_3647_ = v_a_3643_;
v_snd_3648_ = v_snd_3645_;
v_err_3649_ = v___x_3671_;
goto v___jp_3646_;
}
v___jp_3646_:
{
uint8_t v___x_3650_; 
v___x_3650_ = lean_nat_dec_eq(v_snd_3645_, v_snd_3648_);
lean_dec(v_snd_3648_);
lean_dec(v_snd_3645_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; 
lean_dec_ref(v_acc_3642_);
lean_inc(v_err_3649_);
v___x_3651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3651_, 0, v_pos_3647_);
lean_ctor_set(v___x_3651_, 1, v_err_3649_);
return v___x_3651_;
}
else
{
lean_object* v___x_3652_; 
v___x_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3652_, 0, v_pos_3647_);
lean_ctor_set(v___x_3652_, 1, v_acc_3642_);
return v___x_3652_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0(void){
_start:
{
uint32_t v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = 119;
v___x_3673_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3674_ = lean_string_push(v___x_3673_, v___x_3672_);
return v___x_3674_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1(void){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3675_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0);
v___x_3676_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3677_ = lean_string_append(v___x_3676_, v___x_3675_);
return v___x_3677_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3678_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3679_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1);
v___x_3680_ = lean_string_append(v___x_3679_, v___x_3678_);
return v___x_3680_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3(void){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__2);
v___x_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(lean_object* v_acc_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v_fst_3685_; lean_object* v_snd_3686_; lean_object* v_pos_3688_; lean_object* v_snd_3689_; lean_object* v_err_3690_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
v_fst_3685_ = lean_ctor_get(v_a_3684_, 0);
v_snd_3686_ = lean_ctor_get(v_a_3684_, 1);
lean_inc(v_snd_3686_);
v___x_3694_ = lean_string_utf8_byte_size(v_fst_3685_);
v___x_3695_ = lean_nat_dec_eq(v_snd_3686_, v___x_3694_);
if (v___x_3695_ == 0)
{
uint32_t v___x_3696_; uint32_t v_c_3697_; uint8_t v___x_3698_; 
v___x_3696_ = 119;
v_c_3697_ = lean_string_utf8_get_fast(v_fst_3685_, v_snd_3686_);
v___x_3698_ = lean_uint32_dec_eq(v_c_3697_, v___x_3696_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; 
v___x_3699_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3);
lean_inc(v_snd_3686_);
v_pos_3688_ = v_a_3684_;
v_snd_3689_ = v_snd_3686_;
v_err_3690_ = v___x_3699_;
goto v___jp_3687_;
}
else
{
lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3709_; 
lean_inc(v_fst_3685_);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_a_3684_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; lean_object* v_unused_3711_; 
v_unused_3710_ = lean_ctor_get(v_a_3684_, 1);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_a_3684_, 0);
lean_dec(v_unused_3711_);
v___x_3701_ = v_a_3684_;
v_isShared_3702_ = v_isSharedCheck_3709_;
goto v_resetjp_3700_;
}
else
{
lean_dec(v_a_3684_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3709_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v_it_x27_3705_; 
v___x_3703_ = lean_string_utf8_next_fast(v_fst_3685_, v_snd_3686_);
lean_dec(v_snd_3686_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v___x_3703_);
v_it_x27_3705_ = v___x_3701_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_fst_3685_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3703_);
v_it_x27_3705_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_string_push(v_acc_3683_, v___x_3696_);
v_acc_3683_ = v___x_3706_;
v_a_3684_ = v_it_x27_3705_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_box(0);
lean_inc(v_snd_3686_);
v_pos_3688_ = v_a_3684_;
v_snd_3689_ = v_snd_3686_;
v_err_3690_ = v___x_3712_;
goto v___jp_3687_;
}
v___jp_3687_:
{
uint8_t v___x_3691_; 
v___x_3691_ = lean_nat_dec_eq(v_snd_3686_, v_snd_3689_);
lean_dec(v_snd_3689_);
lean_dec(v_snd_3686_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; 
lean_dec_ref(v_acc_3683_);
lean_inc(v_err_3690_);
v___x_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_pos_3688_);
lean_ctor_set(v___x_3692_, 1, v_err_3690_);
return v___x_3692_;
}
else
{
lean_object* v___x_3693_; 
v___x_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3693_, 0, v_pos_3688_);
lean_ctor_set(v___x_3693_, 1, v_acc_3683_);
return v___x_3693_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0(void){
_start:
{
uint32_t v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3713_ = 100;
v___x_3714_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3715_ = lean_string_push(v___x_3714_, v___x_3713_);
return v___x_3715_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1(void){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3716_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0);
v___x_3717_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3718_ = lean_string_append(v___x_3717_, v___x_3716_);
return v___x_3718_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3719_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3720_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1);
v___x_3721_ = lean_string_append(v___x_3720_, v___x_3719_);
return v___x_3721_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__2);
v___x_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(lean_object* v_acc_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v_fst_3726_; lean_object* v_snd_3727_; lean_object* v_pos_3729_; lean_object* v_snd_3730_; lean_object* v_err_3731_; lean_object* v___x_3735_; uint8_t v___x_3736_; 
v_fst_3726_ = lean_ctor_get(v_a_3725_, 0);
v_snd_3727_ = lean_ctor_get(v_a_3725_, 1);
lean_inc(v_snd_3727_);
v___x_3735_ = lean_string_utf8_byte_size(v_fst_3726_);
v___x_3736_ = lean_nat_dec_eq(v_snd_3727_, v___x_3735_);
if (v___x_3736_ == 0)
{
uint32_t v___x_3737_; uint32_t v_c_3738_; uint8_t v___x_3739_; 
v___x_3737_ = 100;
v_c_3738_ = lean_string_utf8_get_fast(v_fst_3726_, v_snd_3727_);
v___x_3739_ = lean_uint32_dec_eq(v_c_3738_, v___x_3737_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; 
v___x_3740_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3);
lean_inc(v_snd_3727_);
v_pos_3729_ = v_a_3725_;
v_snd_3730_ = v_snd_3727_;
v_err_3731_ = v___x_3740_;
goto v___jp_3728_;
}
else
{
lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3750_; 
lean_inc(v_fst_3726_);
v_isSharedCheck_3750_ = !lean_is_exclusive(v_a_3725_);
if (v_isSharedCheck_3750_ == 0)
{
lean_object* v_unused_3751_; lean_object* v_unused_3752_; 
v_unused_3751_ = lean_ctor_get(v_a_3725_, 1);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_a_3725_, 0);
lean_dec(v_unused_3752_);
v___x_3742_ = v_a_3725_;
v_isShared_3743_ = v_isSharedCheck_3750_;
goto v_resetjp_3741_;
}
else
{
lean_dec(v_a_3725_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3750_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v_it_x27_3746_; 
v___x_3744_ = lean_string_utf8_next_fast(v_fst_3726_, v_snd_3727_);
lean_dec(v_snd_3727_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 1, v___x_3744_);
v_it_x27_3746_ = v___x_3742_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_fst_3726_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v___x_3744_);
v_it_x27_3746_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3747_; 
v___x_3747_ = lean_string_push(v_acc_3724_, v___x_3737_);
v_acc_3724_ = v___x_3747_;
v_a_3725_ = v_it_x27_3746_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3753_; 
v___x_3753_ = lean_box(0);
lean_inc(v_snd_3727_);
v_pos_3729_ = v_a_3725_;
v_snd_3730_ = v_snd_3727_;
v_err_3731_ = v___x_3753_;
goto v___jp_3728_;
}
v___jp_3728_:
{
uint8_t v___x_3732_; 
v___x_3732_ = lean_nat_dec_eq(v_snd_3727_, v_snd_3730_);
lean_dec(v_snd_3730_);
lean_dec(v_snd_3727_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; 
lean_dec_ref(v_acc_3724_);
lean_inc(v_err_3731_);
v___x_3733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3733_, 0, v_pos_3729_);
lean_ctor_set(v___x_3733_, 1, v_err_3731_);
return v___x_3733_;
}
else
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3734_, 0, v_pos_3729_);
lean_ctor_set(v___x_3734_, 1, v_acc_3724_);
return v___x_3734_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0(void){
_start:
{
uint32_t v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3754_ = 99;
v___x_3755_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3756_ = lean_string_push(v___x_3755_, v___x_3754_);
return v___x_3756_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1(void){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3757_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0);
v___x_3758_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3759_ = lean_string_append(v___x_3758_, v___x_3757_);
return v___x_3759_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2(void){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3760_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3761_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1);
v___x_3762_ = lean_string_append(v___x_3761_, v___x_3760_);
return v___x_3762_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__2);
v___x_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(lean_object* v_acc_3765_, lean_object* v_a_3766_){
_start:
{
lean_object* v_fst_3767_; lean_object* v_snd_3768_; lean_object* v_pos_3770_; lean_object* v_snd_3771_; lean_object* v_err_3772_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v_fst_3767_ = lean_ctor_get(v_a_3766_, 0);
v_snd_3768_ = lean_ctor_get(v_a_3766_, 1);
lean_inc(v_snd_3768_);
v___x_3776_ = lean_string_utf8_byte_size(v_fst_3767_);
v___x_3777_ = lean_nat_dec_eq(v_snd_3768_, v___x_3776_);
if (v___x_3777_ == 0)
{
uint32_t v___x_3778_; uint32_t v_c_3779_; uint8_t v___x_3780_; 
v___x_3778_ = 99;
v_c_3779_ = lean_string_utf8_get_fast(v_fst_3767_, v_snd_3768_);
v___x_3780_ = lean_uint32_dec_eq(v_c_3779_, v___x_3778_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3);
lean_inc(v_snd_3768_);
v_pos_3770_ = v_a_3766_;
v_snd_3771_ = v_snd_3768_;
v_err_3772_ = v___x_3781_;
goto v___jp_3769_;
}
else
{
lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3791_; 
lean_inc(v_fst_3767_);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_a_3766_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; lean_object* v_unused_3793_; 
v_unused_3792_ = lean_ctor_get(v_a_3766_, 1);
lean_dec(v_unused_3792_);
v_unused_3793_ = lean_ctor_get(v_a_3766_, 0);
lean_dec(v_unused_3793_);
v___x_3783_ = v_a_3766_;
v_isShared_3784_ = v_isSharedCheck_3791_;
goto v_resetjp_3782_;
}
else
{
lean_dec(v_a_3766_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3791_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3785_; lean_object* v_it_x27_3787_; 
v___x_3785_ = lean_string_utf8_next_fast(v_fst_3767_, v_snd_3768_);
lean_dec(v_snd_3768_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 1, v___x_3785_);
v_it_x27_3787_ = v___x_3783_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_fst_3767_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v___x_3785_);
v_it_x27_3787_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
lean_object* v___x_3788_; 
v___x_3788_ = lean_string_push(v_acc_3765_, v___x_3778_);
v_acc_3765_ = v___x_3788_;
v_a_3766_ = v_it_x27_3787_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_box(0);
lean_inc(v_snd_3768_);
v_pos_3770_ = v_a_3766_;
v_snd_3771_ = v_snd_3768_;
v_err_3772_ = v___x_3794_;
goto v___jp_3769_;
}
v___jp_3769_:
{
uint8_t v___x_3773_; 
v___x_3773_ = lean_nat_dec_eq(v_snd_3768_, v_snd_3771_);
lean_dec(v_snd_3771_);
lean_dec(v_snd_3768_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; 
lean_dec_ref(v_acc_3765_);
lean_inc(v_err_3772_);
v___x_3774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_pos_3770_);
lean_ctor_set(v___x_3774_, 1, v_err_3772_);
return v___x_3774_;
}
else
{
lean_object* v___x_3775_; 
v___x_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3775_, 0, v_pos_3770_);
lean_ctor_set(v___x_3775_, 1, v_acc_3765_);
return v___x_3775_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0(void){
_start:
{
uint32_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3795_ = 69;
v___x_3796_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3797_ = lean_string_push(v___x_3796_, v___x_3795_);
return v___x_3797_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3798_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0);
v___x_3799_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3800_ = lean_string_append(v___x_3799_, v___x_3798_);
return v___x_3800_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3801_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3802_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1);
v___x_3803_ = lean_string_append(v___x_3802_, v___x_3801_);
return v___x_3803_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__2);
v___x_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3804_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(lean_object* v_acc_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v_fst_3808_; lean_object* v_snd_3809_; lean_object* v_pos_3811_; lean_object* v_snd_3812_; lean_object* v_err_3813_; lean_object* v___x_3817_; uint8_t v___x_3818_; 
v_fst_3808_ = lean_ctor_get(v_a_3807_, 0);
v_snd_3809_ = lean_ctor_get(v_a_3807_, 1);
lean_inc(v_snd_3809_);
v___x_3817_ = lean_string_utf8_byte_size(v_fst_3808_);
v___x_3818_ = lean_nat_dec_eq(v_snd_3809_, v___x_3817_);
if (v___x_3818_ == 0)
{
uint32_t v___x_3819_; uint32_t v_c_3820_; uint8_t v___x_3821_; 
v___x_3819_ = 69;
v_c_3820_ = lean_string_utf8_get_fast(v_fst_3808_, v_snd_3809_);
v___x_3821_ = lean_uint32_dec_eq(v_c_3820_, v___x_3819_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3822_; 
v___x_3822_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3);
lean_inc(v_snd_3809_);
v_pos_3811_ = v_a_3807_;
v_snd_3812_ = v_snd_3809_;
v_err_3813_ = v___x_3822_;
goto v___jp_3810_;
}
else
{
lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3832_; 
lean_inc(v_fst_3808_);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_a_3807_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; lean_object* v_unused_3834_; 
v_unused_3833_ = lean_ctor_get(v_a_3807_, 1);
lean_dec(v_unused_3833_);
v_unused_3834_ = lean_ctor_get(v_a_3807_, 0);
lean_dec(v_unused_3834_);
v___x_3824_ = v_a_3807_;
v_isShared_3825_ = v_isSharedCheck_3832_;
goto v_resetjp_3823_;
}
else
{
lean_dec(v_a_3807_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3832_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3826_; lean_object* v_it_x27_3828_; 
v___x_3826_ = lean_string_utf8_next_fast(v_fst_3808_, v_snd_3809_);
lean_dec(v_snd_3809_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 1, v___x_3826_);
v_it_x27_3828_ = v___x_3824_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_fst_3808_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v___x_3826_);
v_it_x27_3828_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3829_; 
v___x_3829_ = lean_string_push(v_acc_3806_, v___x_3819_);
v_acc_3806_ = v___x_3829_;
v_a_3807_ = v_it_x27_3828_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_box(0);
lean_inc(v_snd_3809_);
v_pos_3811_ = v_a_3807_;
v_snd_3812_ = v_snd_3809_;
v_err_3813_ = v___x_3835_;
goto v___jp_3810_;
}
v___jp_3810_:
{
uint8_t v___x_3814_; 
v___x_3814_ = lean_nat_dec_eq(v_snd_3809_, v_snd_3812_);
lean_dec(v_snd_3812_);
lean_dec(v_snd_3809_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
lean_dec_ref(v_acc_3806_);
lean_inc(v_err_3813_);
v___x_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3815_, 0, v_pos_3811_);
lean_ctor_set(v___x_3815_, 1, v_err_3813_);
return v___x_3815_;
}
else
{
lean_object* v___x_3816_; 
v___x_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3816_, 0, v_pos_3811_);
lean_ctor_set(v___x_3816_, 1, v_acc_3806_);
return v___x_3816_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0(void){
_start:
{
uint32_t v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3836_ = 97;
v___x_3837_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3838_ = lean_string_push(v___x_3837_, v___x_3836_);
return v___x_3838_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0);
v___x_3840_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3841_ = lean_string_append(v___x_3840_, v___x_3839_);
return v___x_3841_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3842_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3843_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1);
v___x_3844_ = lean_string_append(v___x_3843_, v___x_3842_);
return v___x_3844_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3(void){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__2);
v___x_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(lean_object* v_acc_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_fst_3849_; lean_object* v_snd_3850_; lean_object* v_pos_3852_; lean_object* v_snd_3853_; lean_object* v_err_3854_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v_fst_3849_ = lean_ctor_get(v_a_3848_, 0);
v_snd_3850_ = lean_ctor_get(v_a_3848_, 1);
lean_inc(v_snd_3850_);
v___x_3858_ = lean_string_utf8_byte_size(v_fst_3849_);
v___x_3859_ = lean_nat_dec_eq(v_snd_3850_, v___x_3858_);
if (v___x_3859_ == 0)
{
uint32_t v___x_3860_; uint32_t v_c_3861_; uint8_t v___x_3862_; 
v___x_3860_ = 97;
v_c_3861_ = lean_string_utf8_get_fast(v_fst_3849_, v_snd_3850_);
v___x_3862_ = lean_uint32_dec_eq(v_c_3861_, v___x_3860_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3);
lean_inc(v_snd_3850_);
v_pos_3852_ = v_a_3848_;
v_snd_3853_ = v_snd_3850_;
v_err_3854_ = v___x_3863_;
goto v___jp_3851_;
}
else
{
lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3873_; 
lean_inc(v_fst_3849_);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_a_3848_);
if (v_isSharedCheck_3873_ == 0)
{
lean_object* v_unused_3874_; lean_object* v_unused_3875_; 
v_unused_3874_ = lean_ctor_get(v_a_3848_, 1);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_a_3848_, 0);
lean_dec(v_unused_3875_);
v___x_3865_ = v_a_3848_;
v_isShared_3866_ = v_isSharedCheck_3873_;
goto v_resetjp_3864_;
}
else
{
lean_dec(v_a_3848_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3873_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3867_; lean_object* v_it_x27_3869_; 
v___x_3867_ = lean_string_utf8_next_fast(v_fst_3849_, v_snd_3850_);
lean_dec(v_snd_3850_);
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 1, v___x_3867_);
v_it_x27_3869_ = v___x_3865_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_fst_3849_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v___x_3867_);
v_it_x27_3869_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; 
v___x_3870_ = lean_string_push(v_acc_3847_, v___x_3860_);
v_acc_3847_ = v___x_3870_;
v_a_3848_ = v_it_x27_3869_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3876_; 
v___x_3876_ = lean_box(0);
lean_inc(v_snd_3850_);
v_pos_3852_ = v_a_3848_;
v_snd_3853_ = v_snd_3850_;
v_err_3854_ = v___x_3876_;
goto v___jp_3851_;
}
v___jp_3851_:
{
uint8_t v___x_3855_; 
v___x_3855_ = lean_nat_dec_eq(v_snd_3850_, v_snd_3853_);
lean_dec(v_snd_3853_);
lean_dec(v_snd_3850_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; 
lean_dec_ref(v_acc_3847_);
lean_inc(v_err_3854_);
v___x_3856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3856_, 0, v_pos_3852_);
lean_ctor_set(v___x_3856_, 1, v_err_3854_);
return v___x_3856_;
}
else
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3857_, 0, v_pos_3852_);
lean_ctor_set(v___x_3857_, 1, v_acc_3847_);
return v___x_3857_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0(void){
_start:
{
uint32_t v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3877_ = 79;
v___x_3878_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3879_ = lean_string_push(v___x_3878_, v___x_3877_);
return v___x_3879_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0);
v___x_3881_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3882_ = lean_string_append(v___x_3881_, v___x_3880_);
return v___x_3882_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3883_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3884_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1);
v___x_3885_ = lean_string_append(v___x_3884_, v___x_3883_);
return v___x_3885_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__2);
v___x_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(lean_object* v_acc_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_fst_3890_; lean_object* v_snd_3891_; lean_object* v_pos_3893_; lean_object* v_snd_3894_; lean_object* v_err_3895_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v_fst_3890_ = lean_ctor_get(v_a_3889_, 0);
v_snd_3891_ = lean_ctor_get(v_a_3889_, 1);
lean_inc(v_snd_3891_);
v___x_3899_ = lean_string_utf8_byte_size(v_fst_3890_);
v___x_3900_ = lean_nat_dec_eq(v_snd_3891_, v___x_3899_);
if (v___x_3900_ == 0)
{
uint32_t v___x_3901_; uint32_t v_c_3902_; uint8_t v___x_3903_; 
v___x_3901_ = 79;
v_c_3902_ = lean_string_utf8_get_fast(v_fst_3890_, v_snd_3891_);
v___x_3903_ = lean_uint32_dec_eq(v_c_3902_, v___x_3901_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; 
v___x_3904_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3);
lean_inc(v_snd_3891_);
v_pos_3893_ = v_a_3889_;
v_snd_3894_ = v_snd_3891_;
v_err_3895_ = v___x_3904_;
goto v___jp_3892_;
}
else
{
lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3914_; 
lean_inc(v_fst_3890_);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_a_3889_);
if (v_isSharedCheck_3914_ == 0)
{
lean_object* v_unused_3915_; lean_object* v_unused_3916_; 
v_unused_3915_ = lean_ctor_get(v_a_3889_, 1);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_a_3889_, 0);
lean_dec(v_unused_3916_);
v___x_3906_ = v_a_3889_;
v_isShared_3907_ = v_isSharedCheck_3914_;
goto v_resetjp_3905_;
}
else
{
lean_dec(v_a_3889_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3914_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3908_; lean_object* v_it_x27_3910_; 
v___x_3908_ = lean_string_utf8_next_fast(v_fst_3890_, v_snd_3891_);
lean_dec(v_snd_3891_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 1, v___x_3908_);
v_it_x27_3910_ = v___x_3906_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_fst_3890_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v___x_3908_);
v_it_x27_3910_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_string_push(v_acc_3888_, v___x_3901_);
v_acc_3888_ = v___x_3911_;
v_a_3889_ = v_it_x27_3910_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3917_; 
v___x_3917_ = lean_box(0);
lean_inc(v_snd_3891_);
v_pos_3893_ = v_a_3889_;
v_snd_3894_ = v_snd_3891_;
v_err_3895_ = v___x_3917_;
goto v___jp_3892_;
}
v___jp_3892_:
{
uint8_t v___x_3896_; 
v___x_3896_ = lean_nat_dec_eq(v_snd_3891_, v_snd_3894_);
lean_dec(v_snd_3894_);
lean_dec(v_snd_3891_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3897_; 
lean_dec_ref(v_acc_3888_);
lean_inc(v_err_3895_);
v___x_3897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3897_, 0, v_pos_3893_);
lean_ctor_set(v___x_3897_, 1, v_err_3895_);
return v___x_3897_;
}
else
{
lean_object* v___x_3898_; 
v___x_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3898_, 0, v_pos_3893_);
lean_ctor_set(v___x_3898_, 1, v_acc_3888_);
return v___x_3898_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0(void){
_start:
{
uint32_t v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3918_ = 65;
v___x_3919_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3920_ = lean_string_push(v___x_3919_, v___x_3918_);
return v___x_3920_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3921_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0);
v___x_3922_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3923_ = lean_string_append(v___x_3922_, v___x_3921_);
return v___x_3923_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2(void){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3924_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3925_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1);
v___x_3926_ = lean_string_append(v___x_3925_, v___x_3924_);
return v___x_3926_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3(void){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__2);
v___x_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(lean_object* v_acc_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v_fst_3931_; lean_object* v_snd_3932_; lean_object* v_pos_3934_; lean_object* v_snd_3935_; lean_object* v_err_3936_; lean_object* v___x_3940_; uint8_t v___x_3941_; 
v_fst_3931_ = lean_ctor_get(v_a_3930_, 0);
v_snd_3932_ = lean_ctor_get(v_a_3930_, 1);
lean_inc(v_snd_3932_);
v___x_3940_ = lean_string_utf8_byte_size(v_fst_3931_);
v___x_3941_ = lean_nat_dec_eq(v_snd_3932_, v___x_3940_);
if (v___x_3941_ == 0)
{
uint32_t v___x_3942_; uint32_t v_c_3943_; uint8_t v___x_3944_; 
v___x_3942_ = 65;
v_c_3943_ = lean_string_utf8_get_fast(v_fst_3931_, v_snd_3932_);
v___x_3944_ = lean_uint32_dec_eq(v_c_3943_, v___x_3942_);
if (v___x_3944_ == 0)
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3);
lean_inc(v_snd_3932_);
v_pos_3934_ = v_a_3930_;
v_snd_3935_ = v_snd_3932_;
v_err_3936_ = v___x_3945_;
goto v___jp_3933_;
}
else
{
lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3955_; 
lean_inc(v_fst_3931_);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_a_3930_);
if (v_isSharedCheck_3955_ == 0)
{
lean_object* v_unused_3956_; lean_object* v_unused_3957_; 
v_unused_3956_ = lean_ctor_get(v_a_3930_, 1);
lean_dec(v_unused_3956_);
v_unused_3957_ = lean_ctor_get(v_a_3930_, 0);
lean_dec(v_unused_3957_);
v___x_3947_ = v_a_3930_;
v_isShared_3948_ = v_isSharedCheck_3955_;
goto v_resetjp_3946_;
}
else
{
lean_dec(v_a_3930_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3955_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; lean_object* v_it_x27_3951_; 
v___x_3949_ = lean_string_utf8_next_fast(v_fst_3931_, v_snd_3932_);
lean_dec(v_snd_3932_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 1, v___x_3949_);
v_it_x27_3951_ = v___x_3947_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_fst_3931_);
lean_ctor_set(v_reuseFailAlloc_3954_, 1, v___x_3949_);
v_it_x27_3951_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_string_push(v_acc_3929_, v___x_3942_);
v_acc_3929_ = v___x_3952_;
v_a_3930_ = v_it_x27_3951_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_box(0);
lean_inc(v_snd_3932_);
v_pos_3934_ = v_a_3930_;
v_snd_3935_ = v_snd_3932_;
v_err_3936_ = v___x_3958_;
goto v___jp_3933_;
}
v___jp_3933_:
{
uint8_t v___x_3937_; 
v___x_3937_ = lean_nat_dec_eq(v_snd_3932_, v_snd_3935_);
lean_dec(v_snd_3935_);
lean_dec(v_snd_3932_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; 
lean_dec_ref(v_acc_3929_);
lean_inc(v_err_3936_);
v___x_3938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3938_, 0, v_pos_3934_);
lean_ctor_set(v___x_3938_, 1, v_err_3936_);
return v___x_3938_;
}
else
{
lean_object* v___x_3939_; 
v___x_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3939_, 0, v_pos_3934_);
lean_ctor_set(v___x_3939_, 1, v_acc_3929_);
return v___x_3939_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0(void){
_start:
{
uint32_t v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3959_ = 76;
v___x_3960_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_3961_ = lean_string_push(v___x_3960_, v___x_3959_);
return v___x_3961_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1(void){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3962_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0);
v___x_3963_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_3964_ = lean_string_append(v___x_3963_, v___x_3962_);
return v___x_3964_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2(void){
_start:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3965_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_3966_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1);
v___x_3967_ = lean_string_append(v___x_3966_, v___x_3965_);
return v___x_3967_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3968_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__2);
v___x_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(lean_object* v_acc_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v_fst_3972_; lean_object* v_snd_3973_; lean_object* v_pos_3975_; lean_object* v_snd_3976_; lean_object* v_err_3977_; lean_object* v___x_3981_; uint8_t v___x_3982_; 
v_fst_3972_ = lean_ctor_get(v_a_3971_, 0);
v_snd_3973_ = lean_ctor_get(v_a_3971_, 1);
lean_inc(v_snd_3973_);
v___x_3981_ = lean_string_utf8_byte_size(v_fst_3972_);
v___x_3982_ = lean_nat_dec_eq(v_snd_3973_, v___x_3981_);
if (v___x_3982_ == 0)
{
uint32_t v___x_3983_; uint32_t v_c_3984_; uint8_t v___x_3985_; 
v___x_3983_ = 76;
v_c_3984_ = lean_string_utf8_get_fast(v_fst_3972_, v_snd_3973_);
v___x_3985_ = lean_uint32_dec_eq(v_c_3984_, v___x_3983_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; 
v___x_3986_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3);
lean_inc(v_snd_3973_);
v_pos_3975_ = v_a_3971_;
v_snd_3976_ = v_snd_3973_;
v_err_3977_ = v___x_3986_;
goto v___jp_3974_;
}
else
{
lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3996_; 
lean_inc(v_fst_3972_);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_a_3971_);
if (v_isSharedCheck_3996_ == 0)
{
lean_object* v_unused_3997_; lean_object* v_unused_3998_; 
v_unused_3997_ = lean_ctor_get(v_a_3971_, 1);
lean_dec(v_unused_3997_);
v_unused_3998_ = lean_ctor_get(v_a_3971_, 0);
lean_dec(v_unused_3998_);
v___x_3988_ = v_a_3971_;
v_isShared_3989_ = v_isSharedCheck_3996_;
goto v_resetjp_3987_;
}
else
{
lean_dec(v_a_3971_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3996_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v_it_x27_3992_; 
v___x_3990_ = lean_string_utf8_next_fast(v_fst_3972_, v_snd_3973_);
lean_dec(v_snd_3973_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 1, v___x_3990_);
v_it_x27_3992_ = v___x_3988_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_fst_3972_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v___x_3990_);
v_it_x27_3992_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_string_push(v_acc_3970_, v___x_3983_);
v_acc_3970_ = v___x_3993_;
v_a_3971_ = v_it_x27_3992_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3999_; 
v___x_3999_ = lean_box(0);
lean_inc(v_snd_3973_);
v_pos_3975_ = v_a_3971_;
v_snd_3976_ = v_snd_3973_;
v_err_3977_ = v___x_3999_;
goto v___jp_3974_;
}
v___jp_3974_:
{
uint8_t v___x_3978_; 
v___x_3978_ = lean_nat_dec_eq(v_snd_3973_, v_snd_3976_);
lean_dec(v_snd_3976_);
lean_dec(v_snd_3973_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; 
lean_dec_ref(v_acc_3970_);
lean_inc(v_err_3977_);
v___x_3979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3979_, 0, v_pos_3975_);
lean_ctor_set(v___x_3979_, 1, v_err_3977_);
return v___x_3979_;
}
else
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3980_, 0, v_pos_3975_);
lean_ctor_set(v___x_3980_, 1, v_acc_3970_);
return v___x_3980_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0(void){
_start:
{
uint32_t v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = 113;
v___x_4001_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4002_ = lean_string_push(v___x_4001_, v___x_4000_);
return v___x_4002_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1(void){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4003_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0);
v___x_4004_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4005_ = lean_string_append(v___x_4004_, v___x_4003_);
return v___x_4005_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4007_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1);
v___x_4008_ = lean_string_append(v___x_4007_, v___x_4006_);
return v___x_4008_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3(void){
_start:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__2);
v___x_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(lean_object* v_acc_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v_fst_4013_; lean_object* v_snd_4014_; lean_object* v_pos_4016_; lean_object* v_snd_4017_; lean_object* v_err_4018_; lean_object* v___x_4022_; uint8_t v___x_4023_; 
v_fst_4013_ = lean_ctor_get(v_a_4012_, 0);
v_snd_4014_ = lean_ctor_get(v_a_4012_, 1);
lean_inc(v_snd_4014_);
v___x_4022_ = lean_string_utf8_byte_size(v_fst_4013_);
v___x_4023_ = lean_nat_dec_eq(v_snd_4014_, v___x_4022_);
if (v___x_4023_ == 0)
{
uint32_t v___x_4024_; uint32_t v_c_4025_; uint8_t v___x_4026_; 
v___x_4024_ = 113;
v_c_4025_ = lean_string_utf8_get_fast(v_fst_4013_, v_snd_4014_);
v___x_4026_ = lean_uint32_dec_eq(v_c_4025_, v___x_4024_);
if (v___x_4026_ == 0)
{
lean_object* v___x_4027_; 
v___x_4027_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3);
lean_inc(v_snd_4014_);
v_pos_4016_ = v_a_4012_;
v_snd_4017_ = v_snd_4014_;
v_err_4018_ = v___x_4027_;
goto v___jp_4015_;
}
else
{
lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4037_; 
lean_inc(v_fst_4013_);
v_isSharedCheck_4037_ = !lean_is_exclusive(v_a_4012_);
if (v_isSharedCheck_4037_ == 0)
{
lean_object* v_unused_4038_; lean_object* v_unused_4039_; 
v_unused_4038_ = lean_ctor_get(v_a_4012_, 1);
lean_dec(v_unused_4038_);
v_unused_4039_ = lean_ctor_get(v_a_4012_, 0);
lean_dec(v_unused_4039_);
v___x_4029_ = v_a_4012_;
v_isShared_4030_ = v_isSharedCheck_4037_;
goto v_resetjp_4028_;
}
else
{
lean_dec(v_a_4012_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4037_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4031_; lean_object* v_it_x27_4033_; 
v___x_4031_ = lean_string_utf8_next_fast(v_fst_4013_, v_snd_4014_);
lean_dec(v_snd_4014_);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 1, v___x_4031_);
v_it_x27_4033_ = v___x_4029_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_fst_4013_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v___x_4031_);
v_it_x27_4033_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v___x_4034_; 
v___x_4034_ = lean_string_push(v_acc_4011_, v___x_4024_);
v_acc_4011_ = v___x_4034_;
v_a_4012_ = v_it_x27_4033_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4040_; 
v___x_4040_ = lean_box(0);
lean_inc(v_snd_4014_);
v_pos_4016_ = v_a_4012_;
v_snd_4017_ = v_snd_4014_;
v_err_4018_ = v___x_4040_;
goto v___jp_4015_;
}
v___jp_4015_:
{
uint8_t v___x_4019_; 
v___x_4019_ = lean_nat_dec_eq(v_snd_4014_, v_snd_4017_);
lean_dec(v_snd_4017_);
lean_dec(v_snd_4014_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; 
lean_dec_ref(v_acc_4011_);
lean_inc(v_err_4018_);
v___x_4020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4020_, 0, v_pos_4016_);
lean_ctor_set(v___x_4020_, 1, v_err_4018_);
return v___x_4020_;
}
else
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4021_, 0, v_pos_4016_);
lean_ctor_set(v___x_4021_, 1, v_acc_4011_);
return v___x_4021_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0(void){
_start:
{
uint32_t v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4041_ = 72;
v___x_4042_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4043_ = lean_string_push(v___x_4042_, v___x_4041_);
return v___x_4043_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1(void){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4044_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0);
v___x_4045_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4046_ = lean_string_append(v___x_4045_, v___x_4044_);
return v___x_4046_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2(void){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4047_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4048_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1);
v___x_4049_ = lean_string_append(v___x_4048_, v___x_4047_);
return v___x_4049_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__2);
v___x_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(lean_object* v_acc_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_fst_4054_; lean_object* v_snd_4055_; lean_object* v_pos_4057_; lean_object* v_snd_4058_; lean_object* v_err_4059_; lean_object* v___x_4063_; uint8_t v___x_4064_; 
v_fst_4054_ = lean_ctor_get(v_a_4053_, 0);
v_snd_4055_ = lean_ctor_get(v_a_4053_, 1);
lean_inc(v_snd_4055_);
v___x_4063_ = lean_string_utf8_byte_size(v_fst_4054_);
v___x_4064_ = lean_nat_dec_eq(v_snd_4055_, v___x_4063_);
if (v___x_4064_ == 0)
{
uint32_t v___x_4065_; uint32_t v_c_4066_; uint8_t v___x_4067_; 
v___x_4065_ = 72;
v_c_4066_ = lean_string_utf8_get_fast(v_fst_4054_, v_snd_4055_);
v___x_4067_ = lean_uint32_dec_eq(v_c_4066_, v___x_4065_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4068_; 
v___x_4068_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3);
lean_inc(v_snd_4055_);
v_pos_4057_ = v_a_4053_;
v_snd_4058_ = v_snd_4055_;
v_err_4059_ = v___x_4068_;
goto v___jp_4056_;
}
else
{
lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4078_; 
lean_inc(v_fst_4054_);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_a_4053_);
if (v_isSharedCheck_4078_ == 0)
{
lean_object* v_unused_4079_; lean_object* v_unused_4080_; 
v_unused_4079_ = lean_ctor_get(v_a_4053_, 1);
lean_dec(v_unused_4079_);
v_unused_4080_ = lean_ctor_get(v_a_4053_, 0);
lean_dec(v_unused_4080_);
v___x_4070_ = v_a_4053_;
v_isShared_4071_ = v_isSharedCheck_4078_;
goto v_resetjp_4069_;
}
else
{
lean_dec(v_a_4053_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4078_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4072_; lean_object* v_it_x27_4074_; 
v___x_4072_ = lean_string_utf8_next_fast(v_fst_4054_, v_snd_4055_);
lean_dec(v_snd_4055_);
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 1, v___x_4072_);
v_it_x27_4074_ = v___x_4070_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_fst_4054_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v___x_4072_);
v_it_x27_4074_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_string_push(v_acc_4052_, v___x_4065_);
v_acc_4052_ = v___x_4075_;
v_a_4053_ = v_it_x27_4074_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4081_; 
v___x_4081_ = lean_box(0);
lean_inc(v_snd_4055_);
v_pos_4057_ = v_a_4053_;
v_snd_4058_ = v_snd_4055_;
v_err_4059_ = v___x_4081_;
goto v___jp_4056_;
}
v___jp_4056_:
{
uint8_t v___x_4060_; 
v___x_4060_ = lean_nat_dec_eq(v_snd_4055_, v_snd_4058_);
lean_dec(v_snd_4058_);
lean_dec(v_snd_4055_);
if (v___x_4060_ == 0)
{
lean_object* v___x_4061_; 
lean_dec_ref(v_acc_4052_);
lean_inc(v_err_4059_);
v___x_4061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4061_, 0, v_pos_4057_);
lean_ctor_set(v___x_4061_, 1, v_err_4059_);
return v___x_4061_;
}
else
{
lean_object* v___x_4062_; 
v___x_4062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4062_, 0, v_pos_4057_);
lean_ctor_set(v___x_4062_, 1, v_acc_4052_);
return v___x_4062_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0(void){
_start:
{
uint32_t v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = 118;
v___x_4083_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4084_ = lean_string_push(v___x_4083_, v___x_4082_);
return v___x_4084_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1(void){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0);
v___x_4086_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4087_ = lean_string_append(v___x_4086_, v___x_4085_);
return v___x_4087_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2(void){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4089_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1);
v___x_4090_ = lean_string_append(v___x_4089_, v___x_4088_);
return v___x_4090_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3(void){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4091_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__2);
v___x_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(lean_object* v_acc_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_fst_4095_; lean_object* v_snd_4096_; lean_object* v_pos_4098_; lean_object* v_snd_4099_; lean_object* v_err_4100_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v_fst_4095_ = lean_ctor_get(v_a_4094_, 0);
v_snd_4096_ = lean_ctor_get(v_a_4094_, 1);
lean_inc(v_snd_4096_);
v___x_4104_ = lean_string_utf8_byte_size(v_fst_4095_);
v___x_4105_ = lean_nat_dec_eq(v_snd_4096_, v___x_4104_);
if (v___x_4105_ == 0)
{
uint32_t v___x_4106_; uint32_t v_c_4107_; uint8_t v___x_4108_; 
v___x_4106_ = 118;
v_c_4107_ = lean_string_utf8_get_fast(v_fst_4095_, v_snd_4096_);
v___x_4108_ = lean_uint32_dec_eq(v_c_4107_, v___x_4106_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3);
lean_inc(v_snd_4096_);
v_pos_4098_ = v_a_4094_;
v_snd_4099_ = v_snd_4096_;
v_err_4100_ = v___x_4109_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4119_; 
lean_inc(v_fst_4095_);
v_isSharedCheck_4119_ = !lean_is_exclusive(v_a_4094_);
if (v_isSharedCheck_4119_ == 0)
{
lean_object* v_unused_4120_; lean_object* v_unused_4121_; 
v_unused_4120_ = lean_ctor_get(v_a_4094_, 1);
lean_dec(v_unused_4120_);
v_unused_4121_ = lean_ctor_get(v_a_4094_, 0);
lean_dec(v_unused_4121_);
v___x_4111_ = v_a_4094_;
v_isShared_4112_ = v_isSharedCheck_4119_;
goto v_resetjp_4110_;
}
else
{
lean_dec(v_a_4094_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4119_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4113_; lean_object* v_it_x27_4115_; 
v___x_4113_ = lean_string_utf8_next_fast(v_fst_4095_, v_snd_4096_);
lean_dec(v_snd_4096_);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 1, v___x_4113_);
v_it_x27_4115_ = v___x_4111_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_fst_4095_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v___x_4113_);
v_it_x27_4115_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4116_; 
v___x_4116_ = lean_string_push(v_acc_4093_, v___x_4106_);
v_acc_4093_ = v___x_4116_;
v_a_4094_ = v_it_x27_4115_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4122_; 
v___x_4122_ = lean_box(0);
lean_inc(v_snd_4096_);
v_pos_4098_ = v_a_4094_;
v_snd_4099_ = v_snd_4096_;
v_err_4100_ = v___x_4122_;
goto v___jp_4097_;
}
v___jp_4097_:
{
uint8_t v___x_4101_; 
v___x_4101_ = lean_nat_dec_eq(v_snd_4096_, v_snd_4099_);
lean_dec(v_snd_4099_);
lean_dec(v_snd_4096_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4102_; 
lean_dec_ref(v_acc_4093_);
lean_inc(v_err_4100_);
v___x_4102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4102_, 0, v_pos_4098_);
lean_ctor_set(v___x_4102_, 1, v_err_4100_);
return v___x_4102_;
}
else
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4103_, 0, v_pos_4098_);
lean_ctor_set(v___x_4103_, 1, v_acc_4093_);
return v___x_4103_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0(void){
_start:
{
uint32_t v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4123_ = 87;
v___x_4124_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4125_ = lean_string_push(v___x_4124_, v___x_4123_);
return v___x_4125_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1(void){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4126_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0);
v___x_4127_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4128_ = lean_string_append(v___x_4127_, v___x_4126_);
return v___x_4128_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4129_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4130_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1);
v___x_4131_ = lean_string_append(v___x_4130_, v___x_4129_);
return v___x_4131_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__2);
v___x_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(lean_object* v_acc_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v_fst_4136_; lean_object* v_snd_4137_; lean_object* v_pos_4139_; lean_object* v_snd_4140_; lean_object* v_err_4141_; lean_object* v___x_4145_; uint8_t v___x_4146_; 
v_fst_4136_ = lean_ctor_get(v_a_4135_, 0);
v_snd_4137_ = lean_ctor_get(v_a_4135_, 1);
lean_inc(v_snd_4137_);
v___x_4145_ = lean_string_utf8_byte_size(v_fst_4136_);
v___x_4146_ = lean_nat_dec_eq(v_snd_4137_, v___x_4145_);
if (v___x_4146_ == 0)
{
uint32_t v___x_4147_; uint32_t v_c_4148_; uint8_t v___x_4149_; 
v___x_4147_ = 87;
v_c_4148_ = lean_string_utf8_get_fast(v_fst_4136_, v_snd_4137_);
v___x_4149_ = lean_uint32_dec_eq(v_c_4148_, v___x_4147_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; 
v___x_4150_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3);
lean_inc(v_snd_4137_);
v_pos_4139_ = v_a_4135_;
v_snd_4140_ = v_snd_4137_;
v_err_4141_ = v___x_4150_;
goto v___jp_4138_;
}
else
{
lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4160_; 
lean_inc(v_fst_4136_);
v_isSharedCheck_4160_ = !lean_is_exclusive(v_a_4135_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; lean_object* v_unused_4162_; 
v_unused_4161_ = lean_ctor_get(v_a_4135_, 1);
lean_dec(v_unused_4161_);
v_unused_4162_ = lean_ctor_get(v_a_4135_, 0);
lean_dec(v_unused_4162_);
v___x_4152_ = v_a_4135_;
v_isShared_4153_ = v_isSharedCheck_4160_;
goto v_resetjp_4151_;
}
else
{
lean_dec(v_a_4135_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4160_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4154_; lean_object* v_it_x27_4156_; 
v___x_4154_ = lean_string_utf8_next_fast(v_fst_4136_, v_snd_4137_);
lean_dec(v_snd_4137_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 1, v___x_4154_);
v_it_x27_4156_ = v___x_4152_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_fst_4136_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v___x_4154_);
v_it_x27_4156_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
lean_object* v___x_4157_; 
v___x_4157_ = lean_string_push(v_acc_4134_, v___x_4147_);
v_acc_4134_ = v___x_4157_;
v_a_4135_ = v_it_x27_4156_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_box(0);
lean_inc(v_snd_4137_);
v_pos_4139_ = v_a_4135_;
v_snd_4140_ = v_snd_4137_;
v_err_4141_ = v___x_4163_;
goto v___jp_4138_;
}
v___jp_4138_:
{
uint8_t v___x_4142_; 
v___x_4142_ = lean_nat_dec_eq(v_snd_4137_, v_snd_4140_);
lean_dec(v_snd_4140_);
lean_dec(v_snd_4137_);
if (v___x_4142_ == 0)
{
lean_object* v___x_4143_; 
lean_dec_ref(v_acc_4134_);
lean_inc(v_err_4141_);
v___x_4143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4143_, 0, v_pos_4139_);
lean_ctor_set(v___x_4143_, 1, v_err_4141_);
return v___x_4143_;
}
else
{
lean_object* v___x_4144_; 
v___x_4144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4144_, 0, v_pos_4139_);
lean_ctor_set(v___x_4144_, 1, v_acc_4134_);
return v___x_4144_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0(void){
_start:
{
uint32_t v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4164_ = 107;
v___x_4165_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4166_ = lean_string_push(v___x_4165_, v___x_4164_);
return v___x_4166_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1(void){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4167_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0);
v___x_4168_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4169_ = lean_string_append(v___x_4168_, v___x_4167_);
return v___x_4169_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2(void){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4170_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4171_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1);
v___x_4172_ = lean_string_append(v___x_4171_, v___x_4170_);
return v___x_4172_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3(void){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__2);
v___x_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(lean_object* v_acc_4175_, lean_object* v_a_4176_){
_start:
{
lean_object* v_fst_4177_; lean_object* v_snd_4178_; lean_object* v_pos_4180_; lean_object* v_snd_4181_; lean_object* v_err_4182_; lean_object* v___x_4186_; uint8_t v___x_4187_; 
v_fst_4177_ = lean_ctor_get(v_a_4176_, 0);
v_snd_4178_ = lean_ctor_get(v_a_4176_, 1);
lean_inc(v_snd_4178_);
v___x_4186_ = lean_string_utf8_byte_size(v_fst_4177_);
v___x_4187_ = lean_nat_dec_eq(v_snd_4178_, v___x_4186_);
if (v___x_4187_ == 0)
{
uint32_t v___x_4188_; uint32_t v_c_4189_; uint8_t v___x_4190_; 
v___x_4188_ = 107;
v_c_4189_ = lean_string_utf8_get_fast(v_fst_4177_, v_snd_4178_);
v___x_4190_ = lean_uint32_dec_eq(v_c_4189_, v___x_4188_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; 
v___x_4191_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3);
lean_inc(v_snd_4178_);
v_pos_4180_ = v_a_4176_;
v_snd_4181_ = v_snd_4178_;
v_err_4182_ = v___x_4191_;
goto v___jp_4179_;
}
else
{
lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4201_; 
lean_inc(v_fst_4177_);
v_isSharedCheck_4201_ = !lean_is_exclusive(v_a_4176_);
if (v_isSharedCheck_4201_ == 0)
{
lean_object* v_unused_4202_; lean_object* v_unused_4203_; 
v_unused_4202_ = lean_ctor_get(v_a_4176_, 1);
lean_dec(v_unused_4202_);
v_unused_4203_ = lean_ctor_get(v_a_4176_, 0);
lean_dec(v_unused_4203_);
v___x_4193_ = v_a_4176_;
v_isShared_4194_ = v_isSharedCheck_4201_;
goto v_resetjp_4192_;
}
else
{
lean_dec(v_a_4176_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4201_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v_it_x27_4197_; 
v___x_4195_ = lean_string_utf8_next_fast(v_fst_4177_, v_snd_4178_);
lean_dec(v_snd_4178_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 1, v___x_4195_);
v_it_x27_4197_ = v___x_4193_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_fst_4177_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v___x_4195_);
v_it_x27_4197_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; 
v___x_4198_ = lean_string_push(v_acc_4175_, v___x_4188_);
v_acc_4175_ = v___x_4198_;
v_a_4176_ = v_it_x27_4197_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_box(0);
lean_inc(v_snd_4178_);
v_pos_4180_ = v_a_4176_;
v_snd_4181_ = v_snd_4178_;
v_err_4182_ = v___x_4204_;
goto v___jp_4179_;
}
v___jp_4179_:
{
uint8_t v___x_4183_; 
v___x_4183_ = lean_nat_dec_eq(v_snd_4178_, v_snd_4181_);
lean_dec(v_snd_4181_);
lean_dec(v_snd_4178_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; 
lean_dec_ref(v_acc_4175_);
lean_inc(v_err_4182_);
v___x_4184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4184_, 0, v_pos_4180_);
lean_ctor_set(v___x_4184_, 1, v_err_4182_);
return v___x_4184_;
}
else
{
lean_object* v___x_4185_; 
v___x_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4185_, 0, v_pos_4180_);
lean_ctor_set(v___x_4185_, 1, v_acc_4175_);
return v___x_4185_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0(void){
_start:
{
uint32_t v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4205_ = 121;
v___x_4206_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4207_ = lean_string_push(v___x_4206_, v___x_4205_);
return v___x_4207_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4208_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0);
v___x_4209_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4210_ = lean_string_append(v___x_4209_, v___x_4208_);
return v___x_4210_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4211_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4212_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1);
v___x_4213_ = lean_string_append(v___x_4212_, v___x_4211_);
return v___x_4213_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3(void){
_start:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__2);
v___x_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(lean_object* v_acc_4216_, lean_object* v_a_4217_){
_start:
{
lean_object* v_fst_4218_; lean_object* v_snd_4219_; lean_object* v_pos_4221_; lean_object* v_snd_4222_; lean_object* v_err_4223_; lean_object* v___x_4227_; uint8_t v___x_4228_; 
v_fst_4218_ = lean_ctor_get(v_a_4217_, 0);
v_snd_4219_ = lean_ctor_get(v_a_4217_, 1);
lean_inc(v_snd_4219_);
v___x_4227_ = lean_string_utf8_byte_size(v_fst_4218_);
v___x_4228_ = lean_nat_dec_eq(v_snd_4219_, v___x_4227_);
if (v___x_4228_ == 0)
{
uint32_t v___x_4229_; uint32_t v_c_4230_; uint8_t v___x_4231_; 
v___x_4229_ = 121;
v_c_4230_ = lean_string_utf8_get_fast(v_fst_4218_, v_snd_4219_);
v___x_4231_ = lean_uint32_dec_eq(v_c_4230_, v___x_4229_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; 
v___x_4232_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3);
lean_inc(v_snd_4219_);
v_pos_4221_ = v_a_4217_;
v_snd_4222_ = v_snd_4219_;
v_err_4223_ = v___x_4232_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4242_; 
lean_inc(v_fst_4218_);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_a_4217_);
if (v_isSharedCheck_4242_ == 0)
{
lean_object* v_unused_4243_; lean_object* v_unused_4244_; 
v_unused_4243_ = lean_ctor_get(v_a_4217_, 1);
lean_dec(v_unused_4243_);
v_unused_4244_ = lean_ctor_get(v_a_4217_, 0);
lean_dec(v_unused_4244_);
v___x_4234_ = v_a_4217_;
v_isShared_4235_ = v_isSharedCheck_4242_;
goto v_resetjp_4233_;
}
else
{
lean_dec(v_a_4217_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4242_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4236_; lean_object* v_it_x27_4238_; 
v___x_4236_ = lean_string_utf8_next_fast(v_fst_4218_, v_snd_4219_);
lean_dec(v_snd_4219_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 1, v___x_4236_);
v_it_x27_4238_ = v___x_4234_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_fst_4218_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v___x_4236_);
v_it_x27_4238_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
lean_object* v___x_4239_; 
v___x_4239_ = lean_string_push(v_acc_4216_, v___x_4229_);
v_acc_4216_ = v___x_4239_;
v_a_4217_ = v_it_x27_4238_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4245_; 
v___x_4245_ = lean_box(0);
lean_inc(v_snd_4219_);
v_pos_4221_ = v_a_4217_;
v_snd_4222_ = v_snd_4219_;
v_err_4223_ = v___x_4245_;
goto v___jp_4220_;
}
v___jp_4220_:
{
uint8_t v___x_4224_; 
v___x_4224_ = lean_nat_dec_eq(v_snd_4219_, v_snd_4222_);
lean_dec(v_snd_4222_);
lean_dec(v_snd_4219_);
if (v___x_4224_ == 0)
{
lean_object* v___x_4225_; 
lean_dec_ref(v_acc_4216_);
lean_inc(v_err_4223_);
v___x_4225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4225_, 0, v_pos_4221_);
lean_ctor_set(v___x_4225_, 1, v_err_4223_);
return v___x_4225_;
}
else
{
lean_object* v___x_4226_; 
v___x_4226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4226_, 0, v_pos_4221_);
lean_ctor_set(v___x_4226_, 1, v_acc_4216_);
return v___x_4226_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0(void){
_start:
{
uint32_t v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4246_ = 98;
v___x_4247_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4248_ = lean_string_push(v___x_4247_, v___x_4246_);
return v___x_4248_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1(void){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4249_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0);
v___x_4250_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4251_ = lean_string_append(v___x_4250_, v___x_4249_);
return v___x_4251_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2(void){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4252_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4253_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1);
v___x_4254_ = lean_string_append(v___x_4253_, v___x_4252_);
return v___x_4254_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3(void){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__2);
v___x_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(lean_object* v_acc_4257_, lean_object* v_a_4258_){
_start:
{
lean_object* v_fst_4259_; lean_object* v_snd_4260_; lean_object* v_pos_4262_; lean_object* v_snd_4263_; lean_object* v_err_4264_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v_fst_4259_ = lean_ctor_get(v_a_4258_, 0);
v_snd_4260_ = lean_ctor_get(v_a_4258_, 1);
lean_inc(v_snd_4260_);
v___x_4268_ = lean_string_utf8_byte_size(v_fst_4259_);
v___x_4269_ = lean_nat_dec_eq(v_snd_4260_, v___x_4268_);
if (v___x_4269_ == 0)
{
uint32_t v___x_4270_; uint32_t v_c_4271_; uint8_t v___x_4272_; 
v___x_4270_ = 98;
v_c_4271_ = lean_string_utf8_get_fast(v_fst_4259_, v_snd_4260_);
v___x_4272_ = lean_uint32_dec_eq(v_c_4271_, v___x_4270_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; 
v___x_4273_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3);
lean_inc(v_snd_4260_);
v_pos_4262_ = v_a_4258_;
v_snd_4263_ = v_snd_4260_;
v_err_4264_ = v___x_4273_;
goto v___jp_4261_;
}
else
{
lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4283_; 
lean_inc(v_fst_4259_);
v_isSharedCheck_4283_ = !lean_is_exclusive(v_a_4258_);
if (v_isSharedCheck_4283_ == 0)
{
lean_object* v_unused_4284_; lean_object* v_unused_4285_; 
v_unused_4284_ = lean_ctor_get(v_a_4258_, 1);
lean_dec(v_unused_4284_);
v_unused_4285_ = lean_ctor_get(v_a_4258_, 0);
lean_dec(v_unused_4285_);
v___x_4275_ = v_a_4258_;
v_isShared_4276_ = v_isSharedCheck_4283_;
goto v_resetjp_4274_;
}
else
{
lean_dec(v_a_4258_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4283_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4277_; lean_object* v_it_x27_4279_; 
v___x_4277_ = lean_string_utf8_next_fast(v_fst_4259_, v_snd_4260_);
lean_dec(v_snd_4260_);
if (v_isShared_4276_ == 0)
{
lean_ctor_set(v___x_4275_, 1, v___x_4277_);
v_it_x27_4279_ = v___x_4275_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_fst_4259_);
lean_ctor_set(v_reuseFailAlloc_4282_, 1, v___x_4277_);
v_it_x27_4279_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
lean_object* v___x_4280_; 
v___x_4280_ = lean_string_push(v_acc_4257_, v___x_4270_);
v_acc_4257_ = v___x_4280_;
v_a_4258_ = v_it_x27_4279_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4286_; 
v___x_4286_ = lean_box(0);
lean_inc(v_snd_4260_);
v_pos_4262_ = v_a_4258_;
v_snd_4263_ = v_snd_4260_;
v_err_4264_ = v___x_4286_;
goto v___jp_4261_;
}
v___jp_4261_:
{
uint8_t v___x_4265_; 
v___x_4265_ = lean_nat_dec_eq(v_snd_4260_, v_snd_4263_);
lean_dec(v_snd_4263_);
lean_dec(v_snd_4260_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; 
lean_dec_ref(v_acc_4257_);
lean_inc(v_err_4264_);
v___x_4266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4266_, 0, v_pos_4262_);
lean_ctor_set(v___x_4266_, 1, v_err_4264_);
return v___x_4266_;
}
else
{
lean_object* v___x_4267_; 
v___x_4267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4267_, 0, v_pos_4262_);
lean_ctor_set(v___x_4267_, 1, v_acc_4257_);
return v___x_4267_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0(void){
_start:
{
uint32_t v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4287_ = 109;
v___x_4288_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4289_ = lean_string_push(v___x_4288_, v___x_4287_);
return v___x_4289_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1(void){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4290_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0);
v___x_4291_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4292_ = lean_string_append(v___x_4291_, v___x_4290_);
return v___x_4292_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4293_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4294_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1);
v___x_4295_ = lean_string_append(v___x_4294_, v___x_4293_);
return v___x_4295_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3(void){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__2);
v___x_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(lean_object* v_acc_4298_, lean_object* v_a_4299_){
_start:
{
lean_object* v_fst_4300_; lean_object* v_snd_4301_; lean_object* v_pos_4303_; lean_object* v_snd_4304_; lean_object* v_err_4305_; lean_object* v___x_4309_; uint8_t v___x_4310_; 
v_fst_4300_ = lean_ctor_get(v_a_4299_, 0);
v_snd_4301_ = lean_ctor_get(v_a_4299_, 1);
lean_inc(v_snd_4301_);
v___x_4309_ = lean_string_utf8_byte_size(v_fst_4300_);
v___x_4310_ = lean_nat_dec_eq(v_snd_4301_, v___x_4309_);
if (v___x_4310_ == 0)
{
uint32_t v___x_4311_; uint32_t v_c_4312_; uint8_t v___x_4313_; 
v___x_4311_ = 109;
v_c_4312_ = lean_string_utf8_get_fast(v_fst_4300_, v_snd_4301_);
v___x_4313_ = lean_uint32_dec_eq(v_c_4312_, v___x_4311_);
if (v___x_4313_ == 0)
{
lean_object* v___x_4314_; 
v___x_4314_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3);
lean_inc(v_snd_4301_);
v_pos_4303_ = v_a_4299_;
v_snd_4304_ = v_snd_4301_;
v_err_4305_ = v___x_4314_;
goto v___jp_4302_;
}
else
{
lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4324_; 
lean_inc(v_fst_4300_);
v_isSharedCheck_4324_ = !lean_is_exclusive(v_a_4299_);
if (v_isSharedCheck_4324_ == 0)
{
lean_object* v_unused_4325_; lean_object* v_unused_4326_; 
v_unused_4325_ = lean_ctor_get(v_a_4299_, 1);
lean_dec(v_unused_4325_);
v_unused_4326_ = lean_ctor_get(v_a_4299_, 0);
lean_dec(v_unused_4326_);
v___x_4316_ = v_a_4299_;
v_isShared_4317_ = v_isSharedCheck_4324_;
goto v_resetjp_4315_;
}
else
{
lean_dec(v_a_4299_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4324_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4318_; lean_object* v_it_x27_4320_; 
v___x_4318_ = lean_string_utf8_next_fast(v_fst_4300_, v_snd_4301_);
lean_dec(v_snd_4301_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 1, v___x_4318_);
v_it_x27_4320_ = v___x_4316_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_fst_4300_);
lean_ctor_set(v_reuseFailAlloc_4323_, 1, v___x_4318_);
v_it_x27_4320_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
lean_object* v___x_4321_; 
v___x_4321_ = lean_string_push(v_acc_4298_, v___x_4311_);
v_acc_4298_ = v___x_4321_;
v_a_4299_ = v_it_x27_4320_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4327_; 
v___x_4327_ = lean_box(0);
lean_inc(v_snd_4301_);
v_pos_4303_ = v_a_4299_;
v_snd_4304_ = v_snd_4301_;
v_err_4305_ = v___x_4327_;
goto v___jp_4302_;
}
v___jp_4302_:
{
uint8_t v___x_4306_; 
v___x_4306_ = lean_nat_dec_eq(v_snd_4301_, v_snd_4304_);
lean_dec(v_snd_4304_);
lean_dec(v_snd_4301_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; 
lean_dec_ref(v_acc_4298_);
lean_inc(v_err_4305_);
v___x_4307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4307_, 0, v_pos_4303_);
lean_ctor_set(v___x_4307_, 1, v_err_4305_);
return v___x_4307_;
}
else
{
lean_object* v___x_4308_; 
v___x_4308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4308_, 0, v_pos_4303_);
lean_ctor_set(v___x_4308_, 1, v_acc_4298_);
return v___x_4308_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0(void){
_start:
{
uint32_t v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4328_ = 117;
v___x_4329_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4330_ = lean_string_push(v___x_4329_, v___x_4328_);
return v___x_4330_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1(void){
_start:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4331_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0);
v___x_4332_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4333_ = lean_string_append(v___x_4332_, v___x_4331_);
return v___x_4333_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4334_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4335_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1);
v___x_4336_ = lean_string_append(v___x_4335_, v___x_4334_);
return v___x_4336_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3(void){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__2);
v___x_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(lean_object* v_acc_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v_fst_4341_; lean_object* v_snd_4342_; lean_object* v_pos_4344_; lean_object* v_snd_4345_; lean_object* v_err_4346_; lean_object* v___x_4350_; uint8_t v___x_4351_; 
v_fst_4341_ = lean_ctor_get(v_a_4340_, 0);
v_snd_4342_ = lean_ctor_get(v_a_4340_, 1);
lean_inc(v_snd_4342_);
v___x_4350_ = lean_string_utf8_byte_size(v_fst_4341_);
v___x_4351_ = lean_nat_dec_eq(v_snd_4342_, v___x_4350_);
if (v___x_4351_ == 0)
{
uint32_t v___x_4352_; uint32_t v_c_4353_; uint8_t v___x_4354_; 
v___x_4352_ = 117;
v_c_4353_ = lean_string_utf8_get_fast(v_fst_4341_, v_snd_4342_);
v___x_4354_ = lean_uint32_dec_eq(v_c_4353_, v___x_4352_);
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; 
v___x_4355_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3);
lean_inc(v_snd_4342_);
v_pos_4344_ = v_a_4340_;
v_snd_4345_ = v_snd_4342_;
v_err_4346_ = v___x_4355_;
goto v___jp_4343_;
}
else
{
lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4365_; 
lean_inc(v_fst_4341_);
v_isSharedCheck_4365_ = !lean_is_exclusive(v_a_4340_);
if (v_isSharedCheck_4365_ == 0)
{
lean_object* v_unused_4366_; lean_object* v_unused_4367_; 
v_unused_4366_ = lean_ctor_get(v_a_4340_, 1);
lean_dec(v_unused_4366_);
v_unused_4367_ = lean_ctor_get(v_a_4340_, 0);
lean_dec(v_unused_4367_);
v___x_4357_ = v_a_4340_;
v_isShared_4358_ = v_isSharedCheck_4365_;
goto v_resetjp_4356_;
}
else
{
lean_dec(v_a_4340_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4365_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v_it_x27_4361_; 
v___x_4359_ = lean_string_utf8_next_fast(v_fst_4341_, v_snd_4342_);
lean_dec(v_snd_4342_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 1, v___x_4359_);
v_it_x27_4361_ = v___x_4357_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_fst_4341_);
lean_ctor_set(v_reuseFailAlloc_4364_, 1, v___x_4359_);
v_it_x27_4361_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4362_; 
v___x_4362_ = lean_string_push(v_acc_4339_, v___x_4352_);
v_acc_4339_ = v___x_4362_;
v_a_4340_ = v_it_x27_4361_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4368_; 
v___x_4368_ = lean_box(0);
lean_inc(v_snd_4342_);
v_pos_4344_ = v_a_4340_;
v_snd_4345_ = v_snd_4342_;
v_err_4346_ = v___x_4368_;
goto v___jp_4343_;
}
v___jp_4343_:
{
uint8_t v___x_4347_; 
v___x_4347_ = lean_nat_dec_eq(v_snd_4342_, v_snd_4345_);
lean_dec(v_snd_4345_);
lean_dec(v_snd_4342_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4348_; 
lean_dec_ref(v_acc_4339_);
lean_inc(v_err_4346_);
v___x_4348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4348_, 0, v_pos_4344_);
lean_ctor_set(v___x_4348_, 1, v_err_4346_);
return v___x_4348_;
}
else
{
lean_object* v___x_4349_; 
v___x_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4349_, 0, v_pos_4344_);
lean_ctor_set(v___x_4349_, 1, v_acc_4339_);
return v___x_4349_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0(void){
_start:
{
uint32_t v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = 90;
v___x_4370_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4371_ = lean_string_push(v___x_4370_, v___x_4369_);
return v___x_4371_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4372_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0);
v___x_4373_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4374_ = lean_string_append(v___x_4373_, v___x_4372_);
return v___x_4374_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4375_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4376_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1);
v___x_4377_ = lean_string_append(v___x_4376_, v___x_4375_);
return v___x_4377_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4378_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__2);
v___x_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(lean_object* v_acc_4380_, lean_object* v_a_4381_){
_start:
{
lean_object* v_fst_4382_; lean_object* v_snd_4383_; lean_object* v_pos_4385_; lean_object* v_snd_4386_; lean_object* v_err_4387_; lean_object* v___x_4391_; uint8_t v___x_4392_; 
v_fst_4382_ = lean_ctor_get(v_a_4381_, 0);
v_snd_4383_ = lean_ctor_get(v_a_4381_, 1);
lean_inc(v_snd_4383_);
v___x_4391_ = lean_string_utf8_byte_size(v_fst_4382_);
v___x_4392_ = lean_nat_dec_eq(v_snd_4383_, v___x_4391_);
if (v___x_4392_ == 0)
{
uint32_t v___x_4393_; uint32_t v_c_4394_; uint8_t v___x_4395_; 
v___x_4393_ = 90;
v_c_4394_ = lean_string_utf8_get_fast(v_fst_4382_, v_snd_4383_);
v___x_4395_ = lean_uint32_dec_eq(v_c_4394_, v___x_4393_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; 
v___x_4396_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3);
lean_inc(v_snd_4383_);
v_pos_4385_ = v_a_4381_;
v_snd_4386_ = v_snd_4383_;
v_err_4387_ = v___x_4396_;
goto v___jp_4384_;
}
else
{
lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4406_; 
lean_inc(v_fst_4382_);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_a_4381_);
if (v_isSharedCheck_4406_ == 0)
{
lean_object* v_unused_4407_; lean_object* v_unused_4408_; 
v_unused_4407_ = lean_ctor_get(v_a_4381_, 1);
lean_dec(v_unused_4407_);
v_unused_4408_ = lean_ctor_get(v_a_4381_, 0);
lean_dec(v_unused_4408_);
v___x_4398_ = v_a_4381_;
v_isShared_4399_ = v_isSharedCheck_4406_;
goto v_resetjp_4397_;
}
else
{
lean_dec(v_a_4381_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4406_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v_it_x27_4402_; 
v___x_4400_ = lean_string_utf8_next_fast(v_fst_4382_, v_snd_4383_);
lean_dec(v_snd_4383_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 1, v___x_4400_);
v_it_x27_4402_ = v___x_4398_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_fst_4382_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v___x_4400_);
v_it_x27_4402_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4403_; 
v___x_4403_ = lean_string_push(v_acc_4380_, v___x_4393_);
v_acc_4380_ = v___x_4403_;
v_a_4381_ = v_it_x27_4402_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4409_; 
v___x_4409_ = lean_box(0);
lean_inc(v_snd_4383_);
v_pos_4385_ = v_a_4381_;
v_snd_4386_ = v_snd_4383_;
v_err_4387_ = v___x_4409_;
goto v___jp_4384_;
}
v___jp_4384_:
{
uint8_t v___x_4388_; 
v___x_4388_ = lean_nat_dec_eq(v_snd_4383_, v_snd_4386_);
lean_dec(v_snd_4386_);
lean_dec(v_snd_4383_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; 
lean_dec_ref(v_acc_4380_);
lean_inc(v_err_4387_);
v___x_4389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4389_, 0, v_pos_4385_);
lean_ctor_set(v___x_4389_, 1, v_err_4387_);
return v___x_4389_;
}
else
{
lean_object* v___x_4390_; 
v___x_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4390_, 0, v_pos_4385_);
lean_ctor_set(v___x_4390_, 1, v_acc_4380_);
return v___x_4390_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0(void){
_start:
{
uint32_t v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4410_ = 78;
v___x_4411_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4412_ = lean_string_push(v___x_4411_, v___x_4410_);
return v___x_4412_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1(void){
_start:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4413_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0);
v___x_4414_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4415_ = lean_string_append(v___x_4414_, v___x_4413_);
return v___x_4415_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2(void){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4416_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4417_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1);
v___x_4418_ = lean_string_append(v___x_4417_, v___x_4416_);
return v___x_4418_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3(void){
_start:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4419_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__2);
v___x_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(lean_object* v_acc_4421_, lean_object* v_a_4422_){
_start:
{
lean_object* v_fst_4423_; lean_object* v_snd_4424_; lean_object* v_pos_4426_; lean_object* v_snd_4427_; lean_object* v_err_4428_; lean_object* v___x_4432_; uint8_t v___x_4433_; 
v_fst_4423_ = lean_ctor_get(v_a_4422_, 0);
v_snd_4424_ = lean_ctor_get(v_a_4422_, 1);
lean_inc(v_snd_4424_);
v___x_4432_ = lean_string_utf8_byte_size(v_fst_4423_);
v___x_4433_ = lean_nat_dec_eq(v_snd_4424_, v___x_4432_);
if (v___x_4433_ == 0)
{
uint32_t v___x_4434_; uint32_t v_c_4435_; uint8_t v___x_4436_; 
v___x_4434_ = 78;
v_c_4435_ = lean_string_utf8_get_fast(v_fst_4423_, v_snd_4424_);
v___x_4436_ = lean_uint32_dec_eq(v_c_4435_, v___x_4434_);
if (v___x_4436_ == 0)
{
lean_object* v___x_4437_; 
v___x_4437_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3);
lean_inc(v_snd_4424_);
v_pos_4426_ = v_a_4422_;
v_snd_4427_ = v_snd_4424_;
v_err_4428_ = v___x_4437_;
goto v___jp_4425_;
}
else
{
lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4447_; 
lean_inc(v_fst_4423_);
v_isSharedCheck_4447_ = !lean_is_exclusive(v_a_4422_);
if (v_isSharedCheck_4447_ == 0)
{
lean_object* v_unused_4448_; lean_object* v_unused_4449_; 
v_unused_4448_ = lean_ctor_get(v_a_4422_, 1);
lean_dec(v_unused_4448_);
v_unused_4449_ = lean_ctor_get(v_a_4422_, 0);
lean_dec(v_unused_4449_);
v___x_4439_ = v_a_4422_;
v_isShared_4440_ = v_isSharedCheck_4447_;
goto v_resetjp_4438_;
}
else
{
lean_dec(v_a_4422_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4447_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4441_; lean_object* v_it_x27_4443_; 
v___x_4441_ = lean_string_utf8_next_fast(v_fst_4423_, v_snd_4424_);
lean_dec(v_snd_4424_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 1, v___x_4441_);
v_it_x27_4443_ = v___x_4439_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_fst_4423_);
lean_ctor_set(v_reuseFailAlloc_4446_, 1, v___x_4441_);
v_it_x27_4443_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
lean_object* v___x_4444_; 
v___x_4444_ = lean_string_push(v_acc_4421_, v___x_4434_);
v_acc_4421_ = v___x_4444_;
v_a_4422_ = v_it_x27_4443_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4450_; 
v___x_4450_ = lean_box(0);
lean_inc(v_snd_4424_);
v_pos_4426_ = v_a_4422_;
v_snd_4427_ = v_snd_4424_;
v_err_4428_ = v___x_4450_;
goto v___jp_4425_;
}
v___jp_4425_:
{
uint8_t v___x_4429_; 
v___x_4429_ = lean_nat_dec_eq(v_snd_4424_, v_snd_4427_);
lean_dec(v_snd_4427_);
lean_dec(v_snd_4424_);
if (v___x_4429_ == 0)
{
lean_object* v___x_4430_; 
lean_dec_ref(v_acc_4421_);
lean_inc(v_err_4428_);
v___x_4430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4430_, 0, v_pos_4426_);
lean_ctor_set(v___x_4430_, 1, v_err_4428_);
return v___x_4430_;
}
else
{
lean_object* v___x_4431_; 
v___x_4431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4431_, 0, v_pos_4426_);
lean_ctor_set(v___x_4431_, 1, v_acc_4421_);
return v___x_4431_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0(void){
_start:
{
uint32_t v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4451_ = 70;
v___x_4452_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4453_ = lean_string_push(v___x_4452_, v___x_4451_);
return v___x_4453_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1(void){
_start:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4454_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0);
v___x_4455_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4456_ = lean_string_append(v___x_4455_, v___x_4454_);
return v___x_4456_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2(void){
_start:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4457_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4458_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1);
v___x_4459_ = lean_string_append(v___x_4458_, v___x_4457_);
return v___x_4459_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3(void){
_start:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4460_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__2);
v___x_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
return v___x_4461_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(lean_object* v_acc_4462_, lean_object* v_a_4463_){
_start:
{
lean_object* v_fst_4464_; lean_object* v_snd_4465_; lean_object* v_pos_4467_; lean_object* v_snd_4468_; lean_object* v_err_4469_; lean_object* v___x_4473_; uint8_t v___x_4474_; 
v_fst_4464_ = lean_ctor_get(v_a_4463_, 0);
v_snd_4465_ = lean_ctor_get(v_a_4463_, 1);
lean_inc(v_snd_4465_);
v___x_4473_ = lean_string_utf8_byte_size(v_fst_4464_);
v___x_4474_ = lean_nat_dec_eq(v_snd_4465_, v___x_4473_);
if (v___x_4474_ == 0)
{
uint32_t v___x_4475_; uint32_t v_c_4476_; uint8_t v___x_4477_; 
v___x_4475_ = 70;
v_c_4476_ = lean_string_utf8_get_fast(v_fst_4464_, v_snd_4465_);
v___x_4477_ = lean_uint32_dec_eq(v_c_4476_, v___x_4475_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4478_; 
v___x_4478_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3);
lean_inc(v_snd_4465_);
v_pos_4467_ = v_a_4463_;
v_snd_4468_ = v_snd_4465_;
v_err_4469_ = v___x_4478_;
goto v___jp_4466_;
}
else
{
lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4488_; 
lean_inc(v_fst_4464_);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_a_4463_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; lean_object* v_unused_4490_; 
v_unused_4489_ = lean_ctor_get(v_a_4463_, 1);
lean_dec(v_unused_4489_);
v_unused_4490_ = lean_ctor_get(v_a_4463_, 0);
lean_dec(v_unused_4490_);
v___x_4480_ = v_a_4463_;
v_isShared_4481_ = v_isSharedCheck_4488_;
goto v_resetjp_4479_;
}
else
{
lean_dec(v_a_4463_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4488_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4482_; lean_object* v_it_x27_4484_; 
v___x_4482_ = lean_string_utf8_next_fast(v_fst_4464_, v_snd_4465_);
lean_dec(v_snd_4465_);
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 1, v___x_4482_);
v_it_x27_4484_ = v___x_4480_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_fst_4464_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v___x_4482_);
v_it_x27_4484_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
lean_object* v___x_4485_; 
v___x_4485_ = lean_string_push(v_acc_4462_, v___x_4475_);
v_acc_4462_ = v___x_4485_;
v_a_4463_ = v_it_x27_4484_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4491_; 
v___x_4491_ = lean_box(0);
lean_inc(v_snd_4465_);
v_pos_4467_ = v_a_4463_;
v_snd_4468_ = v_snd_4465_;
v_err_4469_ = v___x_4491_;
goto v___jp_4466_;
}
v___jp_4466_:
{
uint8_t v___x_4470_; 
v___x_4470_ = lean_nat_dec_eq(v_snd_4465_, v_snd_4468_);
lean_dec(v_snd_4468_);
lean_dec(v_snd_4465_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4471_; 
lean_dec_ref(v_acc_4462_);
lean_inc(v_err_4469_);
v___x_4471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4471_, 0, v_pos_4467_);
lean_ctor_set(v___x_4471_, 1, v_err_4469_);
return v___x_4471_;
}
else
{
lean_object* v___x_4472_; 
v___x_4472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4472_, 0, v_pos_4467_);
lean_ctor_set(v___x_4472_, 1, v_acc_4462_);
return v___x_4472_;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0(void){
_start:
{
uint32_t v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4492_ = 66;
v___x_4493_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_4494_ = lean_string_push(v___x_4493_, v___x_4492_);
return v___x_4494_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1(void){
_start:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4495_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0);
v___x_4496_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__0));
v___x_4497_ = lean_string_append(v___x_4496_, v___x_4495_);
return v___x_4497_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2(void){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4498_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_4499_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1);
v___x_4500_ = lean_string_append(v___x_4499_, v___x_4498_);
return v___x_4500_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3(void){
_start:
{
lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4501_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__2);
v___x_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4501_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(lean_object* v_acc_4503_, lean_object* v_a_4504_){
_start:
{
lean_object* v_fst_4505_; lean_object* v_snd_4506_; lean_object* v_pos_4508_; lean_object* v_snd_4509_; lean_object* v_err_4510_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v_fst_4505_ = lean_ctor_get(v_a_4504_, 0);
v_snd_4506_ = lean_ctor_get(v_a_4504_, 1);
lean_inc(v_snd_4506_);
v___x_4514_ = lean_string_utf8_byte_size(v_fst_4505_);
v___x_4515_ = lean_nat_dec_eq(v_snd_4506_, v___x_4514_);
if (v___x_4515_ == 0)
{
uint32_t v___x_4516_; uint32_t v_c_4517_; uint8_t v___x_4518_; 
v___x_4516_ = 66;
v_c_4517_ = lean_string_utf8_get_fast(v_fst_4505_, v_snd_4506_);
v___x_4518_ = lean_uint32_dec_eq(v_c_4517_, v___x_4516_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; 
v___x_4519_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3);
lean_inc(v_snd_4506_);
v_pos_4508_ = v_a_4504_;
v_snd_4509_ = v_snd_4506_;
v_err_4510_ = v___x_4519_;
goto v___jp_4507_;
}
else
{
lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4529_; 
lean_inc(v_fst_4505_);
v_isSharedCheck_4529_ = !lean_is_exclusive(v_a_4504_);
if (v_isSharedCheck_4529_ == 0)
{
lean_object* v_unused_4530_; lean_object* v_unused_4531_; 
v_unused_4530_ = lean_ctor_get(v_a_4504_, 1);
lean_dec(v_unused_4530_);
v_unused_4531_ = lean_ctor_get(v_a_4504_, 0);
lean_dec(v_unused_4531_);
v___x_4521_ = v_a_4504_;
v_isShared_4522_ = v_isSharedCheck_4529_;
goto v_resetjp_4520_;
}
else
{
lean_dec(v_a_4504_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4529_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4523_; lean_object* v_it_x27_4525_; 
v___x_4523_ = lean_string_utf8_next_fast(v_fst_4505_, v_snd_4506_);
lean_dec(v_snd_4506_);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 1, v___x_4523_);
v_it_x27_4525_ = v___x_4521_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_fst_4505_);
lean_ctor_set(v_reuseFailAlloc_4528_, 1, v___x_4523_);
v_it_x27_4525_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
lean_object* v___x_4526_; 
v___x_4526_ = lean_string_push(v_acc_4503_, v___x_4516_);
v_acc_4503_ = v___x_4526_;
v_a_4504_ = v_it_x27_4525_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4532_; 
v___x_4532_ = lean_box(0);
lean_inc(v_snd_4506_);
v_pos_4508_ = v_a_4504_;
v_snd_4509_ = v_snd_4506_;
v_err_4510_ = v___x_4532_;
goto v___jp_4507_;
}
v___jp_4507_:
{
uint8_t v___x_4511_; 
v___x_4511_ = lean_nat_dec_eq(v_snd_4506_, v_snd_4509_);
lean_dec(v_snd_4509_);
lean_dec(v_snd_4506_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; 
lean_dec_ref(v_acc_4503_);
lean_inc(v_err_4510_);
v___x_4512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4512_, 0, v_pos_4508_);
lean_ctor_set(v___x_4512_, 1, v_err_4510_);
return v___x_4512_;
}
else
{
lean_object* v___x_4513_; 
v___x_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4513_, 0, v_pos_4508_);
lean_ctor_set(v___x_4513_, 1, v_acc_4503_);
return v___x_4513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier(lean_object* v_a_4570_){
_start:
{
lean_object* v___y_4572_; lean_object* v_fst_4575_; lean_object* v_snd_4576_; lean_object* v___f_4577_; lean_object* v_snd_4579_; lean_object* v___y_4580_; lean_object* v_pos_4581_; lean_object* v_snd_4617_; lean_object* v_pos_4618_; lean_object* v_err_4619_; lean_object* v___y_4622_; lean_object* v_snd_4623_; lean_object* v___f_4625_; lean_object* v_snd_4627_; lean_object* v___y_4628_; lean_object* v_pos_4629_; lean_object* v_snd_4658_; lean_object* v_pos_4659_; lean_object* v_err_4660_; lean_object* v___y_4663_; lean_object* v_snd_4664_; lean_object* v___f_4666_; lean_object* v_snd_4668_; lean_object* v___y_4669_; lean_object* v_pos_4670_; lean_object* v_snd_4699_; lean_object* v_pos_4700_; lean_object* v_err_4701_; lean_object* v___y_4704_; lean_object* v_snd_4705_; lean_object* v___f_4707_; lean_object* v_snd_4709_; lean_object* v___y_4710_; lean_object* v_pos_4711_; lean_object* v_snd_4740_; lean_object* v_pos_4741_; lean_object* v_err_4742_; lean_object* v___y_4745_; lean_object* v_snd_4746_; lean_object* v___f_4748_; lean_object* v_snd_4750_; lean_object* v___y_4751_; lean_object* v_pos_4752_; lean_object* v_snd_4781_; lean_object* v_pos_4782_; lean_object* v_err_4783_; lean_object* v___y_4786_; lean_object* v_snd_4787_; lean_object* v___f_4789_; lean_object* v_snd_4791_; lean_object* v___y_4792_; lean_object* v_pos_4793_; lean_object* v_snd_4822_; lean_object* v_pos_4823_; lean_object* v_err_4824_; lean_object* v___y_4827_; lean_object* v_snd_4828_; lean_object* v_snd_4831_; lean_object* v___y_4832_; lean_object* v_pos_4833_; lean_object* v_snd_4862_; lean_object* v_pos_4863_; lean_object* v_err_4864_; lean_object* v___y_4867_; lean_object* v_snd_4868_; lean_object* v___f_4870_; lean_object* v_snd_4872_; lean_object* v___y_4873_; lean_object* v_pos_4874_; lean_object* v_snd_4902_; lean_object* v_pos_4903_; lean_object* v_err_4904_; lean_object* v___y_4907_; lean_object* v_snd_4908_; lean_object* v___f_4910_; lean_object* v_snd_4912_; lean_object* v___y_4913_; lean_object* v_pos_4914_; lean_object* v_snd_4942_; lean_object* v_pos_4943_; lean_object* v_err_4944_; lean_object* v___y_4947_; lean_object* v_snd_4948_; lean_object* v___f_4950_; lean_object* v_snd_4952_; lean_object* v___y_4953_; lean_object* v_pos_4954_; lean_object* v_snd_4982_; lean_object* v_pos_4983_; lean_object* v_err_4984_; lean_object* v___y_4987_; lean_object* v_snd_4988_; lean_object* v___f_4990_; lean_object* v_snd_4992_; lean_object* v___y_4993_; lean_object* v_pos_4994_; lean_object* v_snd_5023_; lean_object* v_pos_5024_; lean_object* v_err_5025_; lean_object* v___y_5028_; lean_object* v_snd_5029_; lean_object* v___f_5031_; lean_object* v_snd_5033_; lean_object* v___y_5034_; lean_object* v___y_5035_; lean_object* v_pos_5036_; lean_object* v_snd_5065_; lean_object* v___y_5066_; lean_object* v_pos_5067_; lean_object* v_err_5068_; lean_object* v___y_5071_; lean_object* v_snd_5072_; lean_object* v___y_5073_; lean_object* v___f_5075_; lean_object* v_snd_5077_; lean_object* v___y_5078_; lean_object* v___y_5079_; lean_object* v_pos_5080_; lean_object* v_snd_5109_; lean_object* v___y_5110_; lean_object* v_pos_5111_; lean_object* v_err_5112_; lean_object* v___y_5115_; lean_object* v_snd_5116_; lean_object* v___y_5117_; lean_object* v___f_5119_; lean_object* v_snd_5121_; lean_object* v___y_5122_; lean_object* v___y_5123_; lean_object* v_pos_5124_; lean_object* v_snd_5153_; lean_object* v___y_5154_; lean_object* v_pos_5155_; lean_object* v_err_5156_; lean_object* v___y_5159_; lean_object* v_snd_5160_; lean_object* v___y_5161_; lean_object* v___f_5163_; lean_object* v_snd_5165_; lean_object* v___y_5166_; lean_object* v___y_5167_; lean_object* v_pos_5168_; lean_object* v_snd_5197_; lean_object* v___y_5198_; lean_object* v_pos_5199_; lean_object* v_err_5200_; lean_object* v___y_5203_; lean_object* v_snd_5204_; lean_object* v___y_5205_; lean_object* v___f_5207_; lean_object* v_snd_5209_; lean_object* v___y_5210_; lean_object* v___y_5211_; lean_object* v_pos_5212_; lean_object* v_snd_5241_; lean_object* v___y_5242_; lean_object* v_pos_5243_; lean_object* v_err_5244_; lean_object* v___y_5247_; lean_object* v_snd_5248_; lean_object* v___y_5249_; lean_object* v___f_5251_; lean_object* v_snd_5253_; lean_object* v___y_5254_; lean_object* v___y_5255_; lean_object* v_pos_5256_; lean_object* v_snd_5285_; lean_object* v___y_5286_; lean_object* v_pos_5287_; lean_object* v_err_5288_; lean_object* v___y_5291_; lean_object* v_snd_5292_; lean_object* v___y_5293_; lean_object* v_snd_5296_; lean_object* v___y_5297_; lean_object* v___y_5298_; lean_object* v_pos_5299_; lean_object* v_snd_5328_; lean_object* v___y_5329_; lean_object* v_pos_5330_; lean_object* v_err_5331_; lean_object* v___y_5334_; lean_object* v_snd_5335_; lean_object* v___y_5336_; lean_object* v_snd_5339_; lean_object* v___y_5340_; lean_object* v___y_5341_; lean_object* v_pos_5342_; lean_object* v_snd_5371_; lean_object* v___y_5372_; lean_object* v_pos_5373_; lean_object* v_err_5374_; lean_object* v___y_5377_; lean_object* v_snd_5378_; lean_object* v___y_5379_; lean_object* v_snd_5382_; lean_object* v___y_5383_; lean_object* v___y_5384_; lean_object* v_pos_5385_; lean_object* v_snd_5414_; lean_object* v___y_5415_; lean_object* v_pos_5416_; lean_object* v_err_5417_; lean_object* v___y_5420_; lean_object* v_snd_5421_; lean_object* v___y_5422_; lean_object* v___f_5424_; lean_object* v___y_5426_; lean_object* v_snd_5427_; lean_object* v___y_5428_; lean_object* v___y_5429_; lean_object* v_pos_5430_; lean_object* v___y_5459_; lean_object* v_snd_5460_; lean_object* v___y_5461_; lean_object* v_pos_5462_; lean_object* v_err_5463_; lean_object* v___y_5466_; lean_object* v___y_5467_; lean_object* v_snd_5468_; lean_object* v___y_5469_; lean_object* v___f_5471_; lean_object* v_snd_5473_; lean_object* v___y_5474_; lean_object* v___y_5475_; lean_object* v___y_5476_; lean_object* v_pos_5477_; lean_object* v_snd_5506_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v_pos_5509_; lean_object* v_err_5510_; lean_object* v___y_5513_; lean_object* v_snd_5514_; lean_object* v___y_5515_; lean_object* v___y_5516_; lean_object* v___f_5518_; lean_object* v___y_5520_; lean_object* v_snd_5521_; lean_object* v___y_5522_; lean_object* v___y_5523_; lean_object* v_pos_5524_; lean_object* v___y_5553_; lean_object* v_snd_5554_; lean_object* v___y_5555_; lean_object* v_pos_5556_; lean_object* v_err_5557_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v_snd_5562_; lean_object* v___y_5563_; lean_object* v___f_5565_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5569_; lean_object* v___y_5570_; lean_object* v_pos_5571_; lean_object* v___y_5600_; lean_object* v___y_5601_; lean_object* v___y_5602_; lean_object* v_pos_5603_; lean_object* v_err_5604_; lean_object* v___y_5607_; lean_object* v___y_5608_; lean_object* v___y_5609_; lean_object* v___y_5610_; lean_object* v___f_5612_; lean_object* v_snd_5614_; lean_object* v___y_5615_; lean_object* v___y_5616_; lean_object* v_pos_5617_; lean_object* v_snd_5647_; lean_object* v___y_5648_; lean_object* v_pos_5649_; lean_object* v_err_5650_; lean_object* v___y_5653_; lean_object* v_snd_5654_; lean_object* v___y_5655_; lean_object* v___f_5657_; lean_object* v_snd_5659_; lean_object* v___y_5660_; lean_object* v___y_5661_; lean_object* v_pos_5662_; lean_object* v_snd_5691_; lean_object* v___y_5692_; lean_object* v_pos_5693_; lean_object* v_err_5694_; lean_object* v___y_5697_; lean_object* v_snd_5698_; lean_object* v___y_5699_; lean_object* v___f_5701_; lean_object* v_snd_5703_; lean_object* v___y_5704_; lean_object* v___y_5705_; lean_object* v_pos_5706_; lean_object* v_snd_5735_; lean_object* v___y_5736_; lean_object* v_pos_5737_; lean_object* v_err_5738_; lean_object* v___y_5741_; lean_object* v_snd_5742_; lean_object* v___y_5743_; lean_object* v___f_5745_; lean_object* v___y_5747_; lean_object* v___y_5748_; lean_object* v___y_5749_; lean_object* v_pos_5750_; lean_object* v___y_5779_; lean_object* v___y_5780_; lean_object* v_pos_5781_; lean_object* v_err_5782_; lean_object* v___y_5785_; lean_object* v___y_5786_; lean_object* v___y_5787_; lean_object* v___f_5789_; lean_object* v_snd_5791_; lean_object* v___y_5792_; lean_object* v_pos_5793_; lean_object* v_snd_5823_; lean_object* v_pos_5824_; lean_object* v_err_5825_; lean_object* v___y_5828_; lean_object* v_snd_5829_; lean_object* v___f_5831_; lean_object* v_snd_5833_; lean_object* v___y_5834_; lean_object* v_pos_5835_; lean_object* v_snd_5864_; lean_object* v_pos_5865_; lean_object* v_err_5866_; lean_object* v___y_5869_; lean_object* v_snd_5870_; lean_object* v___f_5872_; lean_object* v_snd_5874_; lean_object* v___y_5875_; lean_object* v_pos_5876_; lean_object* v_snd_5905_; lean_object* v_pos_5906_; lean_object* v_err_5907_; lean_object* v___y_5910_; lean_object* v_snd_5911_; lean_object* v___f_5913_; lean_object* v_snd_5915_; lean_object* v___y_5916_; lean_object* v_pos_5917_; lean_object* v_snd_5947_; lean_object* v_pos_5948_; lean_object* v_err_5949_; lean_object* v___y_5952_; lean_object* v_snd_5953_; lean_object* v___f_5955_; lean_object* v_snd_5957_; lean_object* v___y_5958_; lean_object* v_pos_5959_; lean_object* v_snd_5988_; lean_object* v_pos_5989_; lean_object* v_err_5990_; lean_object* v___y_5993_; lean_object* v_snd_5994_; lean_object* v___f_5996_; lean_object* v_snd_5998_; lean_object* v___y_5999_; lean_object* v_pos_6000_; lean_object* v_snd_6029_; lean_object* v_pos_6030_; lean_object* v_err_6031_; lean_object* v___y_6034_; lean_object* v_snd_6035_; lean_object* v___f_6037_; lean_object* v___y_6039_; lean_object* v_pos_6040_; lean_object* v_pos_6069_; lean_object* v_err_6070_; lean_object* v___x_6072_; uint8_t v___x_6073_; 
v_fst_4575_ = lean_ctor_get(v_a_4570_, 0);
v_snd_4576_ = lean_ctor_get(v_a_4570_, 1);
lean_inc(v_snd_4576_);
v___f_4577_ = ((lean_object*)(l_Std_Time_parseModifier___closed__0));
v___f_4625_ = ((lean_object*)(l_Std_Time_parseModifier___closed__1));
v___f_4666_ = ((lean_object*)(l_Std_Time_parseModifier___closed__2));
v___f_4707_ = ((lean_object*)(l_Std_Time_parseModifier___closed__3));
v___f_4748_ = ((lean_object*)(l_Std_Time_parseModifier___closed__4));
v___f_4789_ = ((lean_object*)(l_Std_Time_parseModifier___closed__5));
v___f_4870_ = ((lean_object*)(l_Std_Time_parseModifier___closed__6));
v___f_4910_ = ((lean_object*)(l_Std_Time_parseModifier___closed__7));
v___f_4950_ = ((lean_object*)(l_Std_Time_parseModifier___closed__8));
v___f_4990_ = ((lean_object*)(l_Std_Time_parseModifier___closed__9));
v___f_5031_ = ((lean_object*)(l_Std_Time_parseModifier___closed__10));
v___f_5075_ = ((lean_object*)(l_Std_Time_parseModifier___closed__11));
v___f_5119_ = ((lean_object*)(l_Std_Time_parseModifier___closed__12));
v___f_5163_ = ((lean_object*)(l_Std_Time_parseModifier___closed__13));
v___f_5207_ = ((lean_object*)(l_Std_Time_parseModifier___closed__14));
v___f_5251_ = ((lean_object*)(l_Std_Time_parseModifier___closed__15));
v___f_5424_ = ((lean_object*)(l_Std_Time_parseModifier___closed__16));
v___f_5471_ = ((lean_object*)(l_Std_Time_parseModifier___closed__17));
v___f_5518_ = ((lean_object*)(l_Std_Time_parseModifier___closed__18));
v___f_5565_ = ((lean_object*)(l_Std_Time_parseModifier___closed__19));
v___f_5612_ = ((lean_object*)(l_Std_Time_parseModifier___closed__20));
v___f_5657_ = ((lean_object*)(l_Std_Time_parseModifier___closed__22));
v___f_5701_ = ((lean_object*)(l_Std_Time_parseModifier___closed__23));
v___f_5745_ = ((lean_object*)(l_Std_Time_parseModifier___closed__24));
v___f_5789_ = ((lean_object*)(l_Std_Time_parseModifier___closed__25));
v___f_5831_ = ((lean_object*)(l_Std_Time_parseModifier___closed__27));
v___f_5872_ = ((lean_object*)(l_Std_Time_parseModifier___closed__28));
v___f_5913_ = ((lean_object*)(l_Std_Time_parseModifier___closed__29));
v___f_5955_ = ((lean_object*)(l_Std_Time_parseModifier___closed__31));
v___f_5996_ = ((lean_object*)(l_Std_Time_parseModifier___closed__32));
v___f_6037_ = ((lean_object*)(l_Std_Time_parseModifier___closed__33));
v___x_6072_ = lean_string_utf8_byte_size(v_fst_4575_);
v___x_6073_ = lean_nat_dec_eq(v_snd_4576_, v___x_6072_);
if (v___x_6073_ == 0)
{
uint32_t v___x_6074_; uint32_t v_c_6075_; uint8_t v___x_6076_; 
v___x_6074_ = 71;
v_c_6075_ = lean_string_utf8_get_fast(v_fst_4575_, v_snd_4576_);
v___x_6076_ = lean_uint32_dec_eq(v_c_6075_, v___x_6074_);
if (v___x_6076_ == 0)
{
lean_object* v___x_6077_; 
v___x_6077_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__3);
v_pos_6069_ = v_a_4570_;
v_err_6070_ = v___x_6077_;
goto v___jp_6068_;
}
else
{
lean_object* v___x_6079_; uint8_t v_isShared_6080_; uint8_t v_isSharedCheck_6094_; 
lean_inc(v_fst_4575_);
v_isSharedCheck_6094_ = !lean_is_exclusive(v_a_4570_);
if (v_isSharedCheck_6094_ == 0)
{
lean_object* v_unused_6095_; lean_object* v_unused_6096_; 
v_unused_6095_ = lean_ctor_get(v_a_4570_, 1);
lean_dec(v_unused_6095_);
v_unused_6096_ = lean_ctor_get(v_a_4570_, 0);
lean_dec(v_unused_6096_);
v___x_6079_ = v_a_4570_;
v_isShared_6080_ = v_isSharedCheck_6094_;
goto v_resetjp_6078_;
}
else
{
lean_dec(v_a_4570_);
v___x_6079_ = lean_box(0);
v_isShared_6080_ = v_isSharedCheck_6094_;
goto v_resetjp_6078_;
}
v_resetjp_6078_:
{
lean_object* v___x_6081_; lean_object* v_it_x27_6083_; 
v___x_6081_ = lean_string_utf8_next_fast(v_fst_4575_, v_snd_4576_);
if (v_isShared_6080_ == 0)
{
lean_ctor_set(v___x_6079_, 1, v___x_6081_);
v_it_x27_6083_ = v___x_6079_;
goto v_reusejp_6082_;
}
else
{
lean_object* v_reuseFailAlloc_6093_; 
v_reuseFailAlloc_6093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6093_, 0, v_fst_4575_);
lean_ctor_set(v_reuseFailAlloc_6093_, 1, v___x_6081_);
v_it_x27_6083_ = v_reuseFailAlloc_6093_;
goto v_reusejp_6082_;
}
v_reusejp_6082_:
{
lean_object* v___x_6084_; lean_object* v___x_6085_; 
v___x_6084_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__0);
v___x_6085_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(v___x_6084_, v_it_x27_6083_);
if (lean_obj_tag(v___x_6085_) == 0)
{
lean_object* v_pos_6086_; lean_object* v_res_6087_; lean_object* v___f_6088_; lean_object* v___x_6089_; 
v_pos_6086_ = lean_ctor_get(v___x_6085_, 0);
lean_inc(v_pos_6086_);
v_res_6087_ = lean_ctor_get(v___x_6085_, 1);
lean_inc(v_res_6087_);
lean_dec_ref_known(v___x_6085_, 2);
v___f_6088_ = ((lean_object*)(l_Std_Time_parseModifier___closed__34));
v___x_6089_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_6088_, v_res_6087_, v_pos_6086_);
if (lean_obj_tag(v___x_6089_) == 0)
{
lean_dec(v_snd_4576_);
return v___x_6089_;
}
else
{
lean_object* v_pos_6090_; 
v_pos_6090_ = lean_ctor_get(v___x_6089_, 0);
lean_inc(v_pos_6090_);
v___y_6039_ = v___x_6089_;
v_pos_6040_ = v_pos_6090_;
goto v___jp_6038_;
}
}
else
{
lean_object* v_pos_6091_; lean_object* v_err_6092_; 
v_pos_6091_ = lean_ctor_get(v___x_6085_, 0);
lean_inc(v_pos_6091_);
v_err_6092_ = lean_ctor_get(v___x_6085_, 1);
lean_inc(v_err_6092_);
lean_dec_ref_known(v___x_6085_, 2);
v_pos_6069_ = v_pos_6091_;
v_err_6070_ = v_err_6092_;
goto v___jp_6068_;
}
}
}
}
}
else
{
lean_object* v___x_6097_; 
v___x_6097_ = lean_box(0);
v_pos_6069_ = v_a_4570_;
v_err_6070_ = v___x_6097_;
goto v___jp_6068_;
}
v___jp_4571_:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4573_ = lean_box(0);
v___x_4574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4574_, 0, v___y_4572_);
lean_ctor_set(v___x_4574_, 1, v___x_4573_);
return v___x_4574_;
}
v___jp_4578_:
{
lean_object* v_fst_4582_; lean_object* v_snd_4583_; uint8_t v___x_4584_; 
v_fst_4582_ = lean_ctor_get(v_pos_4581_, 0);
v_snd_4583_ = lean_ctor_get(v_pos_4581_, 1);
v___x_4584_ = lean_nat_dec_eq(v_snd_4579_, v_snd_4583_);
lean_dec(v_snd_4579_);
if (v___x_4584_ == 0)
{
lean_dec_ref(v_pos_4581_);
return v___y_4580_;
}
else
{
lean_object* v___x_4585_; uint8_t v___x_4586_; 
lean_dec_ref(v___y_4580_);
v___x_4585_ = lean_string_utf8_byte_size(v_fst_4582_);
v___x_4586_ = lean_nat_dec_eq(v_snd_4583_, v___x_4585_);
if (v___x_4586_ == 0)
{
if (v___x_4584_ == 0)
{
v___y_4572_ = v_pos_4581_;
goto v___jp_4571_;
}
else
{
uint32_t v___x_4587_; uint32_t v_c_4588_; uint8_t v___x_4589_; 
v___x_4587_ = 90;
v_c_4588_ = lean_string_utf8_get_fast(v_fst_4582_, v_snd_4583_);
v___x_4589_ = lean_uint32_dec_eq(v_c_4588_, v___x_4587_);
if (v___x_4589_ == 0)
{
lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4590_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__3);
v___x_4591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4591_, 0, v_pos_4581_);
lean_ctor_set(v___x_4591_, 1, v___x_4590_);
return v___x_4591_;
}
else
{
lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4613_; 
lean_inc(v_snd_4583_);
lean_inc(v_fst_4582_);
v_isSharedCheck_4613_ = !lean_is_exclusive(v_pos_4581_);
if (v_isSharedCheck_4613_ == 0)
{
lean_object* v_unused_4614_; lean_object* v_unused_4615_; 
v_unused_4614_ = lean_ctor_get(v_pos_4581_, 1);
lean_dec(v_unused_4614_);
v_unused_4615_ = lean_ctor_get(v_pos_4581_, 0);
lean_dec(v_unused_4615_);
v___x_4593_ = v_pos_4581_;
v_isShared_4594_ = v_isSharedCheck_4613_;
goto v_resetjp_4592_;
}
else
{
lean_dec(v_pos_4581_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4613_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v_it_x27_4597_; 
v___x_4595_ = lean_string_utf8_next_fast(v_fst_4582_, v_snd_4583_);
lean_dec(v_snd_4583_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 1, v___x_4595_);
v_it_x27_4597_ = v___x_4593_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_fst_4582_);
lean_ctor_set(v_reuseFailAlloc_4612_, 1, v___x_4595_);
v_it_x27_4597_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__0);
v___x_4599_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(v___x_4598_, v_it_x27_4597_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_pos_4600_; lean_object* v_res_4601_; lean_object* v___x_4602_; 
v_pos_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_pos_4600_);
v_res_4601_ = lean_ctor_get(v___x_4599_, 1);
lean_inc(v_res_4601_);
lean_dec_ref_known(v___x_4599_, 2);
v___x_4602_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(v___f_4577_, v_res_4601_, v_pos_4600_);
return v___x_4602_;
}
else
{
lean_object* v_pos_4603_; lean_object* v_err_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
v_pos_4603_ = lean_ctor_get(v___x_4599_, 0);
v_err_4604_ = lean_ctor_get(v___x_4599_, 1);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4599_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_err_4604_);
lean_inc(v_pos_4603_);
lean_dec(v___x_4599_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_pos_4603_);
lean_ctor_set(v_reuseFailAlloc_4610_, 1, v_err_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
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
v___y_4572_ = v_pos_4581_;
goto v___jp_4571_;
}
}
}
v___jp_4616_:
{
lean_object* v___x_4620_; 
lean_inc_ref(v_pos_4618_);
v___x_4620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4620_, 0, v_pos_4618_);
lean_ctor_set(v___x_4620_, 1, v_err_4619_);
v_snd_4579_ = v_snd_4617_;
v___y_4580_ = v___x_4620_;
v_pos_4581_ = v_pos_4618_;
goto v___jp_4578_;
}
v___jp_4621_:
{
lean_object* v___x_4624_; 
v___x_4624_ = lean_box(0);
v_snd_4617_ = v_snd_4623_;
v_pos_4618_ = v___y_4622_;
v_err_4619_ = v___x_4624_;
goto v___jp_4616_;
}
v___jp_4626_:
{
lean_object* v_fst_4630_; lean_object* v_snd_4631_; uint8_t v___x_4632_; 
v_fst_4630_ = lean_ctor_get(v_pos_4629_, 0);
v_snd_4631_ = lean_ctor_get(v_pos_4629_, 1);
lean_inc(v_snd_4631_);
v___x_4632_ = lean_nat_dec_eq(v_snd_4627_, v_snd_4631_);
lean_dec(v_snd_4627_);
if (v___x_4632_ == 0)
{
lean_dec(v_snd_4631_);
lean_dec_ref(v_pos_4629_);
return v___y_4628_;
}
else
{
lean_object* v___x_4633_; uint8_t v___x_4634_; 
lean_dec_ref(v___y_4628_);
v___x_4633_ = lean_string_utf8_byte_size(v_fst_4630_);
v___x_4634_ = lean_nat_dec_eq(v_snd_4631_, v___x_4633_);
if (v___x_4634_ == 0)
{
if (v___x_4632_ == 0)
{
v___y_4622_ = v_pos_4629_;
v_snd_4623_ = v_snd_4631_;
goto v___jp_4621_;
}
else
{
uint32_t v___x_4635_; uint32_t v_c_4636_; uint8_t v___x_4637_; 
v___x_4635_ = 120;
v_c_4636_ = lean_string_utf8_get_fast(v_fst_4630_, v_snd_4631_);
v___x_4637_ = lean_uint32_dec_eq(v_c_4636_, v___x_4635_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; 
v___x_4638_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__4);
v_snd_4617_ = v_snd_4631_;
v_pos_4618_ = v_pos_4629_;
v_err_4619_ = v___x_4638_;
goto v___jp_4616_;
}
else
{
lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4654_; 
lean_inc(v_fst_4630_);
v_isSharedCheck_4654_ = !lean_is_exclusive(v_pos_4629_);
if (v_isSharedCheck_4654_ == 0)
{
lean_object* v_unused_4655_; lean_object* v_unused_4656_; 
v_unused_4655_ = lean_ctor_get(v_pos_4629_, 1);
lean_dec(v_unused_4655_);
v_unused_4656_ = lean_ctor_get(v_pos_4629_, 0);
lean_dec(v_unused_4656_);
v___x_4640_ = v_pos_4629_;
v_isShared_4641_ = v_isSharedCheck_4654_;
goto v_resetjp_4639_;
}
else
{
lean_dec(v_pos_4629_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4654_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4642_; lean_object* v_it_x27_4644_; 
v___x_4642_ = lean_string_utf8_next_fast(v_fst_4630_, v_snd_4631_);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 1, v___x_4642_);
v_it_x27_4644_ = v___x_4640_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_fst_4630_);
lean_ctor_set(v_reuseFailAlloc_4653_, 1, v___x_4642_);
v_it_x27_4644_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1);
v___x_4646_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(v___x_4645_, v_it_x27_4644_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_pos_4647_; lean_object* v_res_4648_; lean_object* v___x_4649_; 
v_pos_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_pos_4647_);
v_res_4648_ = lean_ctor_get(v___x_4646_, 1);
lean_inc(v_res_4648_);
lean_dec_ref_known(v___x_4646_, 2);
v___x_4649_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4625_, v_res_4648_, v_pos_4647_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_dec(v_snd_4631_);
return v___x_4649_;
}
else
{
lean_object* v_pos_4650_; 
v_pos_4650_ = lean_ctor_get(v___x_4649_, 0);
lean_inc(v_pos_4650_);
v_snd_4579_ = v_snd_4631_;
v___y_4580_ = v___x_4649_;
v_pos_4581_ = v_pos_4650_;
goto v___jp_4578_;
}
}
else
{
lean_object* v_pos_4651_; lean_object* v_err_4652_; 
v_pos_4651_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_pos_4651_);
v_err_4652_ = lean_ctor_get(v___x_4646_, 1);
lean_inc(v_err_4652_);
lean_dec_ref_known(v___x_4646_, 2);
v_snd_4617_ = v_snd_4631_;
v_pos_4618_ = v_pos_4651_;
v_err_4619_ = v_err_4652_;
goto v___jp_4616_;
}
}
}
}
}
}
else
{
v___y_4622_ = v_pos_4629_;
v_snd_4623_ = v_snd_4631_;
goto v___jp_4621_;
}
}
}
v___jp_4657_:
{
lean_object* v___x_4661_; 
lean_inc_ref(v_pos_4659_);
v___x_4661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4661_, 0, v_pos_4659_);
lean_ctor_set(v___x_4661_, 1, v_err_4660_);
v_snd_4627_ = v_snd_4658_;
v___y_4628_ = v___x_4661_;
v_pos_4629_ = v_pos_4659_;
goto v___jp_4626_;
}
v___jp_4662_:
{
lean_object* v___x_4665_; 
v___x_4665_ = lean_box(0);
v_snd_4658_ = v_snd_4664_;
v_pos_4659_ = v___y_4663_;
v_err_4660_ = v___x_4665_;
goto v___jp_4657_;
}
v___jp_4667_:
{
lean_object* v_fst_4671_; lean_object* v_snd_4672_; uint8_t v___x_4673_; 
v_fst_4671_ = lean_ctor_get(v_pos_4670_, 0);
v_snd_4672_ = lean_ctor_get(v_pos_4670_, 1);
lean_inc(v_snd_4672_);
v___x_4673_ = lean_nat_dec_eq(v_snd_4668_, v_snd_4672_);
lean_dec(v_snd_4668_);
if (v___x_4673_ == 0)
{
lean_dec(v_snd_4672_);
lean_dec_ref(v_pos_4670_);
return v___y_4669_;
}
else
{
lean_object* v___x_4674_; uint8_t v___x_4675_; 
lean_dec_ref(v___y_4669_);
v___x_4674_ = lean_string_utf8_byte_size(v_fst_4671_);
v___x_4675_ = lean_nat_dec_eq(v_snd_4672_, v___x_4674_);
if (v___x_4675_ == 0)
{
if (v___x_4673_ == 0)
{
v___y_4663_ = v_pos_4670_;
v_snd_4664_ = v_snd_4672_;
goto v___jp_4662_;
}
else
{
uint32_t v___x_4676_; uint32_t v_c_4677_; uint8_t v___x_4678_; 
v___x_4676_ = 88;
v_c_4677_ = lean_string_utf8_get_fast(v_fst_4671_, v_snd_4672_);
v___x_4678_ = lean_uint32_dec_eq(v_c_4677_, v___x_4676_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4679_; 
v___x_4679_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__3);
v_snd_4658_ = v_snd_4672_;
v_pos_4659_ = v_pos_4670_;
v_err_4660_ = v___x_4679_;
goto v___jp_4657_;
}
else
{
lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4695_; 
lean_inc(v_fst_4671_);
v_isSharedCheck_4695_ = !lean_is_exclusive(v_pos_4670_);
if (v_isSharedCheck_4695_ == 0)
{
lean_object* v_unused_4696_; lean_object* v_unused_4697_; 
v_unused_4696_ = lean_ctor_get(v_pos_4670_, 1);
lean_dec(v_unused_4696_);
v_unused_4697_ = lean_ctor_get(v_pos_4670_, 0);
lean_dec(v_unused_4697_);
v___x_4681_ = v_pos_4670_;
v_isShared_4682_ = v_isSharedCheck_4695_;
goto v_resetjp_4680_;
}
else
{
lean_dec(v_pos_4670_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4695_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4683_; lean_object* v_it_x27_4685_; 
v___x_4683_ = lean_string_utf8_next_fast(v_fst_4671_, v_snd_4672_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 1, v___x_4683_);
v_it_x27_4685_ = v___x_4681_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_fst_4671_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v___x_4683_);
v_it_x27_4685_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4686_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__0);
v___x_4687_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(v___x_4686_, v_it_x27_4685_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_pos_4688_; lean_object* v_res_4689_; lean_object* v___x_4690_; 
v_pos_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_pos_4688_);
v_res_4689_ = lean_ctor_get(v___x_4687_, 1);
lean_inc(v_res_4689_);
lean_dec_ref_known(v___x_4687_, 2);
v___x_4690_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4666_, v_res_4689_, v_pos_4688_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_dec(v_snd_4672_);
return v___x_4690_;
}
else
{
lean_object* v_pos_4691_; 
v_pos_4691_ = lean_ctor_get(v___x_4690_, 0);
lean_inc(v_pos_4691_);
v_snd_4627_ = v_snd_4672_;
v___y_4628_ = v___x_4690_;
v_pos_4629_ = v_pos_4691_;
goto v___jp_4626_;
}
}
else
{
lean_object* v_pos_4692_; lean_object* v_err_4693_; 
v_pos_4692_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_pos_4692_);
v_err_4693_ = lean_ctor_get(v___x_4687_, 1);
lean_inc(v_err_4693_);
lean_dec_ref_known(v___x_4687_, 2);
v_snd_4658_ = v_snd_4672_;
v_pos_4659_ = v_pos_4692_;
v_err_4660_ = v_err_4693_;
goto v___jp_4657_;
}
}
}
}
}
}
else
{
v___y_4663_ = v_pos_4670_;
v_snd_4664_ = v_snd_4672_;
goto v___jp_4662_;
}
}
}
v___jp_4698_:
{
lean_object* v___x_4702_; 
lean_inc_ref(v_pos_4700_);
v___x_4702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4702_, 0, v_pos_4700_);
lean_ctor_set(v___x_4702_, 1, v_err_4701_);
v_snd_4668_ = v_snd_4699_;
v___y_4669_ = v___x_4702_;
v_pos_4670_ = v_pos_4700_;
goto v___jp_4667_;
}
v___jp_4703_:
{
lean_object* v___x_4706_; 
v___x_4706_ = lean_box(0);
v_snd_4699_ = v_snd_4705_;
v_pos_4700_ = v___y_4704_;
v_err_4701_ = v___x_4706_;
goto v___jp_4698_;
}
v___jp_4708_:
{
lean_object* v_fst_4712_; lean_object* v_snd_4713_; uint8_t v___x_4714_; 
v_fst_4712_ = lean_ctor_get(v_pos_4711_, 0);
v_snd_4713_ = lean_ctor_get(v_pos_4711_, 1);
lean_inc(v_snd_4713_);
v___x_4714_ = lean_nat_dec_eq(v_snd_4709_, v_snd_4713_);
lean_dec(v_snd_4709_);
if (v___x_4714_ == 0)
{
lean_dec(v_snd_4713_);
lean_dec_ref(v_pos_4711_);
return v___y_4710_;
}
else
{
lean_object* v___x_4715_; uint8_t v___x_4716_; 
lean_dec_ref(v___y_4710_);
v___x_4715_ = lean_string_utf8_byte_size(v_fst_4712_);
v___x_4716_ = lean_nat_dec_eq(v_snd_4713_, v___x_4715_);
if (v___x_4716_ == 0)
{
if (v___x_4714_ == 0)
{
v___y_4704_ = v_pos_4711_;
v_snd_4705_ = v_snd_4713_;
goto v___jp_4703_;
}
else
{
uint32_t v___x_4717_; uint32_t v_c_4718_; uint8_t v___x_4719_; 
v___x_4717_ = 79;
v_c_4718_ = lean_string_utf8_get_fast(v_fst_4712_, v_snd_4713_);
v___x_4719_ = lean_uint32_dec_eq(v_c_4718_, v___x_4717_);
if (v___x_4719_ == 0)
{
lean_object* v___x_4720_; 
v___x_4720_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__3);
v_snd_4699_ = v_snd_4713_;
v_pos_4700_ = v_pos_4711_;
v_err_4701_ = v___x_4720_;
goto v___jp_4698_;
}
else
{
lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4736_; 
lean_inc(v_fst_4712_);
v_isSharedCheck_4736_ = !lean_is_exclusive(v_pos_4711_);
if (v_isSharedCheck_4736_ == 0)
{
lean_object* v_unused_4737_; lean_object* v_unused_4738_; 
v_unused_4737_ = lean_ctor_get(v_pos_4711_, 1);
lean_dec(v_unused_4737_);
v_unused_4738_ = lean_ctor_get(v_pos_4711_, 0);
lean_dec(v_unused_4738_);
v___x_4722_ = v_pos_4711_;
v_isShared_4723_ = v_isSharedCheck_4736_;
goto v_resetjp_4721_;
}
else
{
lean_dec(v_pos_4711_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4736_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4724_; lean_object* v_it_x27_4726_; 
v___x_4724_ = lean_string_utf8_next_fast(v_fst_4712_, v_snd_4713_);
if (v_isShared_4723_ == 0)
{
lean_ctor_set(v___x_4722_, 1, v___x_4724_);
v_it_x27_4726_ = v___x_4722_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_fst_4712_);
lean_ctor_set(v_reuseFailAlloc_4735_, 1, v___x_4724_);
v_it_x27_4726_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4727_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__0);
v___x_4728_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(v___x_4727_, v_it_x27_4726_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_pos_4729_; lean_object* v_res_4730_; lean_object* v___x_4731_; 
v_pos_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc(v_pos_4729_);
v_res_4730_ = lean_ctor_get(v___x_4728_, 1);
lean_inc(v_res_4730_);
lean_dec_ref_known(v___x_4728_, 2);
v___x_4731_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(v___f_4707_, v_res_4730_, v_pos_4729_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_dec(v_snd_4713_);
return v___x_4731_;
}
else
{
lean_object* v_pos_4732_; 
v_pos_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_pos_4732_);
v_snd_4668_ = v_snd_4713_;
v___y_4669_ = v___x_4731_;
v_pos_4670_ = v_pos_4732_;
goto v___jp_4667_;
}
}
else
{
lean_object* v_pos_4733_; lean_object* v_err_4734_; 
v_pos_4733_ = lean_ctor_get(v___x_4728_, 0);
lean_inc(v_pos_4733_);
v_err_4734_ = lean_ctor_get(v___x_4728_, 1);
lean_inc(v_err_4734_);
lean_dec_ref_known(v___x_4728_, 2);
v_snd_4699_ = v_snd_4713_;
v_pos_4700_ = v_pos_4733_;
v_err_4701_ = v_err_4734_;
goto v___jp_4698_;
}
}
}
}
}
}
else
{
v___y_4704_ = v_pos_4711_;
v_snd_4705_ = v_snd_4713_;
goto v___jp_4703_;
}
}
}
v___jp_4739_:
{
lean_object* v___x_4743_; 
lean_inc_ref(v_pos_4741_);
v___x_4743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4743_, 0, v_pos_4741_);
lean_ctor_set(v___x_4743_, 1, v_err_4742_);
v_snd_4709_ = v_snd_4740_;
v___y_4710_ = v___x_4743_;
v_pos_4711_ = v_pos_4741_;
goto v___jp_4708_;
}
v___jp_4744_:
{
lean_object* v___x_4747_; 
v___x_4747_ = lean_box(0);
v_snd_4740_ = v_snd_4746_;
v_pos_4741_ = v___y_4745_;
v_err_4742_ = v___x_4747_;
goto v___jp_4739_;
}
v___jp_4749_:
{
lean_object* v_fst_4753_; lean_object* v_snd_4754_; uint8_t v___x_4755_; 
v_fst_4753_ = lean_ctor_get(v_pos_4752_, 0);
v_snd_4754_ = lean_ctor_get(v_pos_4752_, 1);
lean_inc(v_snd_4754_);
v___x_4755_ = lean_nat_dec_eq(v_snd_4750_, v_snd_4754_);
lean_dec(v_snd_4750_);
if (v___x_4755_ == 0)
{
lean_dec(v_snd_4754_);
lean_dec_ref(v_pos_4752_);
return v___y_4751_;
}
else
{
lean_object* v___x_4756_; uint8_t v___x_4757_; 
lean_dec_ref(v___y_4751_);
v___x_4756_ = lean_string_utf8_byte_size(v_fst_4753_);
v___x_4757_ = lean_nat_dec_eq(v_snd_4754_, v___x_4756_);
if (v___x_4757_ == 0)
{
if (v___x_4755_ == 0)
{
v___y_4745_ = v_pos_4752_;
v_snd_4746_ = v_snd_4754_;
goto v___jp_4744_;
}
else
{
uint32_t v___x_4758_; uint32_t v_c_4759_; uint8_t v___x_4760_; 
v___x_4758_ = 118;
v_c_4759_ = lean_string_utf8_get_fast(v_fst_4753_, v_snd_4754_);
v___x_4760_ = lean_uint32_dec_eq(v_c_4759_, v___x_4758_);
if (v___x_4760_ == 0)
{
lean_object* v___x_4761_; 
v___x_4761_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__3);
v_snd_4740_ = v_snd_4754_;
v_pos_4741_ = v_pos_4752_;
v_err_4742_ = v___x_4761_;
goto v___jp_4739_;
}
else
{
lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4777_; 
lean_inc(v_fst_4753_);
v_isSharedCheck_4777_ = !lean_is_exclusive(v_pos_4752_);
if (v_isSharedCheck_4777_ == 0)
{
lean_object* v_unused_4778_; lean_object* v_unused_4779_; 
v_unused_4778_ = lean_ctor_get(v_pos_4752_, 1);
lean_dec(v_unused_4778_);
v_unused_4779_ = lean_ctor_get(v_pos_4752_, 0);
lean_dec(v_unused_4779_);
v___x_4763_ = v_pos_4752_;
v_isShared_4764_ = v_isSharedCheck_4777_;
goto v_resetjp_4762_;
}
else
{
lean_dec(v_pos_4752_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4777_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4765_; lean_object* v_it_x27_4767_; 
v___x_4765_ = lean_string_utf8_next_fast(v_fst_4753_, v_snd_4754_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 1, v___x_4765_);
v_it_x27_4767_ = v___x_4763_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_fst_4753_);
lean_ctor_set(v_reuseFailAlloc_4776_, 1, v___x_4765_);
v_it_x27_4767_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4768_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__0);
v___x_4769_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(v___x_4768_, v_it_x27_4767_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_pos_4770_; lean_object* v_res_4771_; lean_object* v___x_4772_; 
v_pos_4770_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_pos_4770_);
v_res_4771_ = lean_ctor_get(v___x_4769_, 1);
lean_inc(v_res_4771_);
lean_dec_ref_known(v___x_4769_, 2);
v___x_4772_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4748_, v_res_4771_, v_pos_4770_);
if (lean_obj_tag(v___x_4772_) == 0)
{
lean_dec(v_snd_4754_);
return v___x_4772_;
}
else
{
lean_object* v_pos_4773_; 
v_pos_4773_ = lean_ctor_get(v___x_4772_, 0);
lean_inc(v_pos_4773_);
v_snd_4709_ = v_snd_4754_;
v___y_4710_ = v___x_4772_;
v_pos_4711_ = v_pos_4773_;
goto v___jp_4708_;
}
}
else
{
lean_object* v_pos_4774_; lean_object* v_err_4775_; 
v_pos_4774_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_pos_4774_);
v_err_4775_ = lean_ctor_get(v___x_4769_, 1);
lean_inc(v_err_4775_);
lean_dec_ref_known(v___x_4769_, 2);
v_snd_4740_ = v_snd_4754_;
v_pos_4741_ = v_pos_4774_;
v_err_4742_ = v_err_4775_;
goto v___jp_4739_;
}
}
}
}
}
}
else
{
v___y_4745_ = v_pos_4752_;
v_snd_4746_ = v_snd_4754_;
goto v___jp_4744_;
}
}
}
v___jp_4780_:
{
lean_object* v___x_4784_; 
lean_inc_ref(v_pos_4782_);
v___x_4784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4784_, 0, v_pos_4782_);
lean_ctor_set(v___x_4784_, 1, v_err_4783_);
v_snd_4750_ = v_snd_4781_;
v___y_4751_ = v___x_4784_;
v_pos_4752_ = v_pos_4782_;
goto v___jp_4749_;
}
v___jp_4785_:
{
lean_object* v___x_4788_; 
v___x_4788_ = lean_box(0);
v_snd_4781_ = v_snd_4787_;
v_pos_4782_ = v___y_4786_;
v_err_4783_ = v___x_4788_;
goto v___jp_4780_;
}
v___jp_4790_:
{
lean_object* v_fst_4794_; lean_object* v_snd_4795_; uint8_t v___x_4796_; 
v_fst_4794_ = lean_ctor_get(v_pos_4793_, 0);
v_snd_4795_ = lean_ctor_get(v_pos_4793_, 1);
lean_inc(v_snd_4795_);
v___x_4796_ = lean_nat_dec_eq(v_snd_4791_, v_snd_4795_);
lean_dec(v_snd_4791_);
if (v___x_4796_ == 0)
{
lean_dec(v_snd_4795_);
lean_dec_ref(v_pos_4793_);
return v___y_4792_;
}
else
{
lean_object* v___x_4797_; uint8_t v___x_4798_; 
lean_dec_ref(v___y_4792_);
v___x_4797_ = lean_string_utf8_byte_size(v_fst_4794_);
v___x_4798_ = lean_nat_dec_eq(v_snd_4795_, v___x_4797_);
if (v___x_4798_ == 0)
{
if (v___x_4796_ == 0)
{
v___y_4786_ = v_pos_4793_;
v_snd_4787_ = v_snd_4795_;
goto v___jp_4785_;
}
else
{
uint32_t v___x_4799_; uint32_t v_c_4800_; uint8_t v___x_4801_; 
v___x_4799_ = 122;
v_c_4800_ = lean_string_utf8_get_fast(v_fst_4794_, v_snd_4795_);
v___x_4801_ = lean_uint32_dec_eq(v_c_4800_, v___x_4799_);
if (v___x_4801_ == 0)
{
lean_object* v___x_4802_; 
v___x_4802_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__3);
v_snd_4781_ = v_snd_4795_;
v_pos_4782_ = v_pos_4793_;
v_err_4783_ = v___x_4802_;
goto v___jp_4780_;
}
else
{
lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4818_; 
lean_inc(v_fst_4794_);
v_isSharedCheck_4818_ = !lean_is_exclusive(v_pos_4793_);
if (v_isSharedCheck_4818_ == 0)
{
lean_object* v_unused_4819_; lean_object* v_unused_4820_; 
v_unused_4819_ = lean_ctor_get(v_pos_4793_, 1);
lean_dec(v_unused_4819_);
v_unused_4820_ = lean_ctor_get(v_pos_4793_, 0);
lean_dec(v_unused_4820_);
v___x_4804_ = v_pos_4793_;
v_isShared_4805_ = v_isSharedCheck_4818_;
goto v_resetjp_4803_;
}
else
{
lean_dec(v_pos_4793_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4818_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4806_; lean_object* v_it_x27_4808_; 
v___x_4806_ = lean_string_utf8_next_fast(v_fst_4794_, v_snd_4795_);
if (v_isShared_4805_ == 0)
{
lean_ctor_set(v___x_4804_, 1, v___x_4806_);
v_it_x27_4808_ = v___x_4804_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_fst_4794_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v___x_4806_);
v_it_x27_4808_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4809_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__0);
v___x_4810_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(v___x_4809_, v_it_x27_4808_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_pos_4811_; lean_object* v_res_4812_; lean_object* v___x_4813_; 
v_pos_4811_ = lean_ctor_get(v___x_4810_, 0);
lean_inc(v_pos_4811_);
v_res_4812_ = lean_ctor_get(v___x_4810_, 1);
lean_inc(v_res_4812_);
lean_dec_ref_known(v___x_4810_, 2);
v___x_4813_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4789_, v_res_4812_, v_pos_4811_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_dec(v_snd_4795_);
return v___x_4813_;
}
else
{
lean_object* v_pos_4814_; 
v_pos_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_pos_4814_);
v_snd_4750_ = v_snd_4795_;
v___y_4751_ = v___x_4813_;
v_pos_4752_ = v_pos_4814_;
goto v___jp_4749_;
}
}
else
{
lean_object* v_pos_4815_; lean_object* v_err_4816_; 
v_pos_4815_ = lean_ctor_get(v___x_4810_, 0);
lean_inc(v_pos_4815_);
v_err_4816_ = lean_ctor_get(v___x_4810_, 1);
lean_inc(v_err_4816_);
lean_dec_ref_known(v___x_4810_, 2);
v_snd_4781_ = v_snd_4795_;
v_pos_4782_ = v_pos_4815_;
v_err_4783_ = v_err_4816_;
goto v___jp_4780_;
}
}
}
}
}
}
else
{
v___y_4786_ = v_pos_4793_;
v_snd_4787_ = v_snd_4795_;
goto v___jp_4785_;
}
}
}
v___jp_4821_:
{
lean_object* v___x_4825_; 
lean_inc_ref(v_pos_4823_);
v___x_4825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4825_, 0, v_pos_4823_);
lean_ctor_set(v___x_4825_, 1, v_err_4824_);
v_snd_4791_ = v_snd_4822_;
v___y_4792_ = v___x_4825_;
v_pos_4793_ = v_pos_4823_;
goto v___jp_4790_;
}
v___jp_4826_:
{
lean_object* v___x_4829_; 
v___x_4829_ = lean_box(0);
v_snd_4822_ = v_snd_4828_;
v_pos_4823_ = v___y_4827_;
v_err_4824_ = v___x_4829_;
goto v___jp_4821_;
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
v___y_4827_ = v_pos_4833_;
v_snd_4828_ = v_snd_4835_;
goto v___jp_4826_;
}
else
{
uint32_t v___x_4839_; uint32_t v_c_4840_; uint8_t v___x_4841_; 
v___x_4839_ = 86;
v_c_4840_ = lean_string_utf8_get_fast(v_fst_4834_, v_snd_4835_);
v___x_4841_ = lean_uint32_dec_eq(v_c_4840_, v___x_4839_);
if (v___x_4841_ == 0)
{
lean_object* v___x_4842_; 
v___x_4842_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__3);
v_snd_4822_ = v_snd_4835_;
v_pos_4823_ = v_pos_4833_;
v_err_4824_ = v___x_4842_;
goto v___jp_4821_;
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
v___x_4849_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__0);
v___x_4850_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(v___x_4849_, v_it_x27_4848_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_pos_4851_; lean_object* v_res_4852_; lean_object* v___x_4853_; 
v_pos_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_pos_4851_);
v_res_4852_ = lean_ctor_get(v___x_4850_, 1);
lean_inc(v_res_4852_);
lean_dec_ref_known(v___x_4850_, 2);
v___x_4853_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(v_res_4852_, v_pos_4851_);
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
v_snd_4791_ = v_snd_4835_;
v___y_4792_ = v___x_4853_;
v_pos_4793_ = v_pos_4854_;
goto v___jp_4790_;
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
v_snd_4822_ = v_snd_4835_;
v_pos_4823_ = v_pos_4855_;
v_err_4824_ = v_err_4856_;
goto v___jp_4821_;
}
}
}
}
}
}
else
{
v___y_4827_ = v_pos_4833_;
v_snd_4828_ = v_snd_4835_;
goto v___jp_4826_;
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
v___jp_4871_:
{
lean_object* v_fst_4875_; lean_object* v_snd_4876_; uint8_t v___x_4877_; 
v_fst_4875_ = lean_ctor_get(v_pos_4874_, 0);
v_snd_4876_ = lean_ctor_get(v_pos_4874_, 1);
lean_inc(v_snd_4876_);
v___x_4877_ = lean_nat_dec_eq(v_snd_4872_, v_snd_4876_);
lean_dec(v_snd_4872_);
if (v___x_4877_ == 0)
{
lean_dec(v_snd_4876_);
lean_dec_ref(v_pos_4874_);
return v___y_4873_;
}
else
{
lean_object* v___x_4878_; uint8_t v___x_4879_; 
lean_dec_ref(v___y_4873_);
v___x_4878_ = lean_string_utf8_byte_size(v_fst_4875_);
v___x_4879_ = lean_nat_dec_eq(v_snd_4876_, v___x_4878_);
if (v___x_4879_ == 0)
{
if (v___x_4877_ == 0)
{
v___y_4867_ = v_pos_4874_;
v_snd_4868_ = v_snd_4876_;
goto v___jp_4866_;
}
else
{
uint32_t v___x_4880_; uint32_t v_c_4881_; uint8_t v___x_4882_; 
v___x_4880_ = 78;
v_c_4881_ = lean_string_utf8_get_fast(v_fst_4875_, v_snd_4876_);
v___x_4882_ = lean_uint32_dec_eq(v_c_4881_, v___x_4880_);
if (v___x_4882_ == 0)
{
lean_object* v___x_4883_; 
v___x_4883_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__3);
v_snd_4862_ = v_snd_4876_;
v_pos_4863_ = v_pos_4874_;
v_err_4864_ = v___x_4883_;
goto v___jp_4861_;
}
else
{
lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4898_; 
lean_inc(v_fst_4875_);
v_isSharedCheck_4898_ = !lean_is_exclusive(v_pos_4874_);
if (v_isSharedCheck_4898_ == 0)
{
lean_object* v_unused_4899_; lean_object* v_unused_4900_; 
v_unused_4899_ = lean_ctor_get(v_pos_4874_, 1);
lean_dec(v_unused_4899_);
v_unused_4900_ = lean_ctor_get(v_pos_4874_, 0);
lean_dec(v_unused_4900_);
v___x_4885_ = v_pos_4874_;
v_isShared_4886_ = v_isSharedCheck_4898_;
goto v_resetjp_4884_;
}
else
{
lean_dec(v_pos_4874_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4898_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4887_; lean_object* v_it_x27_4889_; 
v___x_4887_ = lean_string_utf8_next_fast(v_fst_4875_, v_snd_4876_);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 1, v___x_4887_);
v_it_x27_4889_ = v___x_4885_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_fst_4875_);
lean_ctor_set(v_reuseFailAlloc_4897_, 1, v___x_4887_);
v_it_x27_4889_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__0);
v___x_4891_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(v___x_4890_, v_it_x27_4889_);
if (lean_obj_tag(v___x_4891_) == 0)
{
lean_object* v_pos_4892_; lean_object* v_res_4893_; lean_object* v___x_4894_; 
lean_dec(v_snd_4876_);
v_pos_4892_ = lean_ctor_get(v___x_4891_, 0);
lean_inc(v_pos_4892_);
v_res_4893_ = lean_ctor_get(v___x_4891_, 1);
lean_inc(v_res_4893_);
lean_dec_ref_known(v___x_4891_, 2);
v___x_4894_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4870_, v_res_4893_, v_pos_4892_);
lean_dec(v_res_4893_);
return v___x_4894_;
}
else
{
lean_object* v_pos_4895_; lean_object* v_err_4896_; 
v_pos_4895_ = lean_ctor_get(v___x_4891_, 0);
lean_inc(v_pos_4895_);
v_err_4896_ = lean_ctor_get(v___x_4891_, 1);
lean_inc(v_err_4896_);
lean_dec_ref_known(v___x_4891_, 2);
v_snd_4862_ = v_snd_4876_;
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
v___y_4867_ = v_pos_4874_;
v_snd_4868_ = v_snd_4876_;
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
v_snd_4872_ = v_snd_4902_;
v___y_4873_ = v___x_4905_;
v_pos_4874_ = v_pos_4903_;
goto v___jp_4871_;
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
v___x_4920_ = 110;
v_c_4921_ = lean_string_utf8_get_fast(v_fst_4915_, v_snd_4916_);
v___x_4922_ = lean_uint32_dec_eq(v_c_4921_, v___x_4920_);
if (v___x_4922_ == 0)
{
lean_object* v___x_4923_; 
v___x_4923_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__3);
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
v___x_4930_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__0);
v___x_4931_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(v___x_4930_, v_it_x27_4929_);
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
v___x_4960_ = 65;
v_c_4961_ = lean_string_utf8_get_fast(v_fst_4955_, v_snd_4956_);
v___x_4962_ = lean_uint32_dec_eq(v_c_4961_, v___x_4960_);
if (v___x_4962_ == 0)
{
lean_object* v___x_4963_; 
v___x_4963_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__3);
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
v___x_4970_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__0);
v___x_4971_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(v___x_4970_, v_it_x27_4969_);
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
v___x_5000_ = 83;
v_c_5001_ = lean_string_utf8_get_fast(v_fst_4995_, v_snd_4996_);
v___x_5002_ = lean_uint32_dec_eq(v_c_5001_, v___x_5000_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; 
v___x_5003_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__3);
v_snd_4982_ = v_snd_4996_;
v_pos_4983_ = v_pos_4994_;
v_err_4984_ = v___x_5003_;
goto v___jp_4981_;
}
else
{
lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5019_; 
lean_inc(v_fst_4995_);
v_isSharedCheck_5019_ = !lean_is_exclusive(v_pos_4994_);
if (v_isSharedCheck_5019_ == 0)
{
lean_object* v_unused_5020_; lean_object* v_unused_5021_; 
v_unused_5020_ = lean_ctor_get(v_pos_4994_, 1);
lean_dec(v_unused_5020_);
v_unused_5021_ = lean_ctor_get(v_pos_4994_, 0);
lean_dec(v_unused_5021_);
v___x_5005_ = v_pos_4994_;
v_isShared_5006_ = v_isSharedCheck_5019_;
goto v_resetjp_5004_;
}
else
{
lean_dec(v_pos_4994_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5019_;
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
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_fst_4995_);
lean_ctor_set(v_reuseFailAlloc_5018_, 1, v___x_5007_);
v_it_x27_5009_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5010_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__0);
v___x_5011_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(v___x_5010_, v_it_x27_5009_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_pos_5012_; lean_object* v_res_5013_; lean_object* v___x_5014_; 
v_pos_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_pos_5012_);
v_res_5013_ = lean_ctor_get(v___x_5011_, 1);
lean_inc(v_res_5013_);
lean_dec_ref_known(v___x_5011_, 2);
v___x_5014_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(v___f_4990_, v_res_5013_, v_pos_5012_);
if (lean_obj_tag(v___x_5014_) == 0)
{
lean_dec(v_snd_4996_);
return v___x_5014_;
}
else
{
lean_object* v_pos_5015_; 
v_pos_5015_ = lean_ctor_get(v___x_5014_, 0);
lean_inc(v_pos_5015_);
v_snd_4952_ = v_snd_4996_;
v___y_4953_ = v___x_5014_;
v_pos_4954_ = v_pos_5015_;
goto v___jp_4951_;
}
}
else
{
lean_object* v_pos_5016_; lean_object* v_err_5017_; 
v_pos_5016_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_pos_5016_);
v_err_5017_ = lean_ctor_get(v___x_5011_, 1);
lean_inc(v_err_5017_);
lean_dec_ref_known(v___x_5011_, 2);
v_snd_4982_ = v_snd_4996_;
v_pos_4983_ = v_pos_5016_;
v_err_4984_ = v_err_5017_;
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
v___jp_5022_:
{
lean_object* v___x_5026_; 
lean_inc_ref(v_pos_5024_);
v___x_5026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5026_, 0, v_pos_5024_);
lean_ctor_set(v___x_5026_, 1, v_err_5025_);
v_snd_4992_ = v_snd_5023_;
v___y_4993_ = v___x_5026_;
v_pos_4994_ = v_pos_5024_;
goto v___jp_4991_;
}
v___jp_5027_:
{
lean_object* v___x_5030_; 
v___x_5030_ = lean_box(0);
v_snd_5023_ = v_snd_5029_;
v_pos_5024_ = v___y_5028_;
v_err_5025_ = v___x_5030_;
goto v___jp_5022_;
}
v___jp_5032_:
{
lean_object* v_fst_5037_; lean_object* v_snd_5038_; uint8_t v___x_5039_; 
v_fst_5037_ = lean_ctor_get(v_pos_5036_, 0);
v_snd_5038_ = lean_ctor_get(v_pos_5036_, 1);
lean_inc(v_snd_5038_);
v___x_5039_ = lean_nat_dec_eq(v_snd_5033_, v_snd_5038_);
lean_dec(v_snd_5033_);
if (v___x_5039_ == 0)
{
lean_dec(v_snd_5038_);
lean_dec_ref(v_pos_5036_);
lean_dec_ref(v___y_5034_);
return v___y_5035_;
}
else
{
lean_object* v___x_5040_; uint8_t v___x_5041_; 
lean_dec_ref(v___y_5035_);
v___x_5040_ = lean_string_utf8_byte_size(v_fst_5037_);
v___x_5041_ = lean_nat_dec_eq(v_snd_5038_, v___x_5040_);
if (v___x_5041_ == 0)
{
if (v___x_5039_ == 0)
{
lean_dec_ref(v___y_5034_);
v___y_5028_ = v_pos_5036_;
v_snd_5029_ = v_snd_5038_;
goto v___jp_5027_;
}
else
{
uint32_t v___x_5042_; uint32_t v_c_5043_; uint8_t v___x_5044_; 
v___x_5042_ = 115;
v_c_5043_ = lean_string_utf8_get_fast(v_fst_5037_, v_snd_5038_);
v___x_5044_ = lean_uint32_dec_eq(v_c_5043_, v___x_5042_);
if (v___x_5044_ == 0)
{
lean_object* v___x_5045_; 
lean_dec_ref(v___y_5034_);
v___x_5045_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__3);
v_snd_5023_ = v_snd_5038_;
v_pos_5024_ = v_pos_5036_;
v_err_5025_ = v___x_5045_;
goto v___jp_5022_;
}
else
{
lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5061_; 
lean_inc(v_fst_5037_);
v_isSharedCheck_5061_ = !lean_is_exclusive(v_pos_5036_);
if (v_isSharedCheck_5061_ == 0)
{
lean_object* v_unused_5062_; lean_object* v_unused_5063_; 
v_unused_5062_ = lean_ctor_get(v_pos_5036_, 1);
lean_dec(v_unused_5062_);
v_unused_5063_ = lean_ctor_get(v_pos_5036_, 0);
lean_dec(v_unused_5063_);
v___x_5047_ = v_pos_5036_;
v_isShared_5048_ = v_isSharedCheck_5061_;
goto v_resetjp_5046_;
}
else
{
lean_dec(v_pos_5036_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5061_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5049_; lean_object* v_it_x27_5051_; 
v___x_5049_ = lean_string_utf8_next_fast(v_fst_5037_, v_snd_5038_);
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 1, v___x_5049_);
v_it_x27_5051_ = v___x_5047_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_fst_5037_);
lean_ctor_set(v_reuseFailAlloc_5060_, 1, v___x_5049_);
v_it_x27_5051_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5052_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__0);
v___x_5053_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(v___x_5052_, v_it_x27_5051_);
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_object* v_pos_5054_; lean_object* v_res_5055_; lean_object* v___x_5056_; 
v_pos_5054_ = lean_ctor_get(v___x_5053_, 0);
lean_inc(v_pos_5054_);
v_res_5055_ = lean_ctor_get(v___x_5053_, 1);
lean_inc(v_res_5055_);
lean_dec_ref_known(v___x_5053_, 2);
v___x_5056_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5031_, v___y_5034_, v_res_5055_, v_pos_5054_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_dec(v_snd_5038_);
return v___x_5056_;
}
else
{
lean_object* v_pos_5057_; 
v_pos_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_pos_5057_);
v_snd_4992_ = v_snd_5038_;
v___y_4993_ = v___x_5056_;
v_pos_4994_ = v_pos_5057_;
goto v___jp_4991_;
}
}
else
{
lean_object* v_pos_5058_; lean_object* v_err_5059_; 
lean_dec_ref(v___y_5034_);
v_pos_5058_ = lean_ctor_get(v___x_5053_, 0);
lean_inc(v_pos_5058_);
v_err_5059_ = lean_ctor_get(v___x_5053_, 1);
lean_inc(v_err_5059_);
lean_dec_ref_known(v___x_5053_, 2);
v_snd_5023_ = v_snd_5038_;
v_pos_5024_ = v_pos_5058_;
v_err_5025_ = v_err_5059_;
goto v___jp_5022_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_5034_);
v___y_5028_ = v_pos_5036_;
v_snd_5029_ = v_snd_5038_;
goto v___jp_5027_;
}
}
}
v___jp_5064_:
{
lean_object* v___x_5069_; 
lean_inc_ref(v_pos_5067_);
v___x_5069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5069_, 0, v_pos_5067_);
lean_ctor_set(v___x_5069_, 1, v_err_5068_);
v_snd_5033_ = v_snd_5065_;
v___y_5034_ = v___y_5066_;
v___y_5035_ = v___x_5069_;
v_pos_5036_ = v_pos_5067_;
goto v___jp_5032_;
}
v___jp_5070_:
{
lean_object* v___x_5074_; 
v___x_5074_ = lean_box(0);
v_snd_5065_ = v_snd_5072_;
v___y_5066_ = v___y_5073_;
v_pos_5067_ = v___y_5071_;
v_err_5068_ = v___x_5074_;
goto v___jp_5064_;
}
v___jp_5076_:
{
lean_object* v_fst_5081_; lean_object* v_snd_5082_; uint8_t v___x_5083_; 
v_fst_5081_ = lean_ctor_get(v_pos_5080_, 0);
v_snd_5082_ = lean_ctor_get(v_pos_5080_, 1);
lean_inc(v_snd_5082_);
v___x_5083_ = lean_nat_dec_eq(v_snd_5077_, v_snd_5082_);
lean_dec(v_snd_5077_);
if (v___x_5083_ == 0)
{
lean_dec(v_snd_5082_);
lean_dec_ref(v_pos_5080_);
lean_dec_ref(v___y_5078_);
return v___y_5079_;
}
else
{
lean_object* v___x_5084_; uint8_t v___x_5085_; 
lean_dec_ref(v___y_5079_);
v___x_5084_ = lean_string_utf8_byte_size(v_fst_5081_);
v___x_5085_ = lean_nat_dec_eq(v_snd_5082_, v___x_5084_);
if (v___x_5085_ == 0)
{
if (v___x_5083_ == 0)
{
v___y_5071_ = v_pos_5080_;
v_snd_5072_ = v_snd_5082_;
v___y_5073_ = v___y_5078_;
goto v___jp_5070_;
}
else
{
uint32_t v___x_5086_; uint32_t v_c_5087_; uint8_t v___x_5088_; 
v___x_5086_ = 109;
v_c_5087_ = lean_string_utf8_get_fast(v_fst_5081_, v_snd_5082_);
v___x_5088_ = lean_uint32_dec_eq(v_c_5087_, v___x_5086_);
if (v___x_5088_ == 0)
{
lean_object* v___x_5089_; 
v___x_5089_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__3);
v_snd_5065_ = v_snd_5082_;
v___y_5066_ = v___y_5078_;
v_pos_5067_ = v_pos_5080_;
v_err_5068_ = v___x_5089_;
goto v___jp_5064_;
}
else
{
lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5105_; 
lean_inc(v_fst_5081_);
v_isSharedCheck_5105_ = !lean_is_exclusive(v_pos_5080_);
if (v_isSharedCheck_5105_ == 0)
{
lean_object* v_unused_5106_; lean_object* v_unused_5107_; 
v_unused_5106_ = lean_ctor_get(v_pos_5080_, 1);
lean_dec(v_unused_5106_);
v_unused_5107_ = lean_ctor_get(v_pos_5080_, 0);
lean_dec(v_unused_5107_);
v___x_5091_ = v_pos_5080_;
v_isShared_5092_ = v_isSharedCheck_5105_;
goto v_resetjp_5090_;
}
else
{
lean_dec(v_pos_5080_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5105_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5093_; lean_object* v_it_x27_5095_; 
v___x_5093_ = lean_string_utf8_next_fast(v_fst_5081_, v_snd_5082_);
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 1, v___x_5093_);
v_it_x27_5095_ = v___x_5091_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_fst_5081_);
lean_ctor_set(v_reuseFailAlloc_5104_, 1, v___x_5093_);
v_it_x27_5095_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5096_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__0);
v___x_5097_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(v___x_5096_, v_it_x27_5095_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v_pos_5098_; lean_object* v_res_5099_; lean_object* v___x_5100_; 
v_pos_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_pos_5098_);
v_res_5099_ = lean_ctor_get(v___x_5097_, 1);
lean_inc(v_res_5099_);
lean_dec_ref_known(v___x_5097_, 2);
lean_inc_ref(v___y_5078_);
v___x_5100_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5075_, v___y_5078_, v_res_5099_, v_pos_5098_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_dec(v_snd_5082_);
lean_dec_ref(v___y_5078_);
return v___x_5100_;
}
else
{
lean_object* v_pos_5101_; 
v_pos_5101_ = lean_ctor_get(v___x_5100_, 0);
lean_inc(v_pos_5101_);
v_snd_5033_ = v_snd_5082_;
v___y_5034_ = v___y_5078_;
v___y_5035_ = v___x_5100_;
v_pos_5036_ = v_pos_5101_;
goto v___jp_5032_;
}
}
else
{
lean_object* v_pos_5102_; lean_object* v_err_5103_; 
v_pos_5102_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_pos_5102_);
v_err_5103_ = lean_ctor_get(v___x_5097_, 1);
lean_inc(v_err_5103_);
lean_dec_ref_known(v___x_5097_, 2);
v_snd_5065_ = v_snd_5082_;
v___y_5066_ = v___y_5078_;
v_pos_5067_ = v_pos_5102_;
v_err_5068_ = v_err_5103_;
goto v___jp_5064_;
}
}
}
}
}
}
else
{
v___y_5071_ = v_pos_5080_;
v_snd_5072_ = v_snd_5082_;
v___y_5073_ = v___y_5078_;
goto v___jp_5070_;
}
}
}
v___jp_5108_:
{
lean_object* v___x_5113_; 
lean_inc_ref(v_pos_5111_);
v___x_5113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5113_, 0, v_pos_5111_);
lean_ctor_set(v___x_5113_, 1, v_err_5112_);
v_snd_5077_ = v_snd_5109_;
v___y_5078_ = v___y_5110_;
v___y_5079_ = v___x_5113_;
v_pos_5080_ = v_pos_5111_;
goto v___jp_5076_;
}
v___jp_5114_:
{
lean_object* v___x_5118_; 
v___x_5118_ = lean_box(0);
v_snd_5109_ = v_snd_5116_;
v___y_5110_ = v___y_5117_;
v_pos_5111_ = v___y_5115_;
v_err_5112_ = v___x_5118_;
goto v___jp_5108_;
}
v___jp_5120_:
{
lean_object* v_fst_5125_; lean_object* v_snd_5126_; uint8_t v___x_5127_; 
v_fst_5125_ = lean_ctor_get(v_pos_5124_, 0);
v_snd_5126_ = lean_ctor_get(v_pos_5124_, 1);
lean_inc(v_snd_5126_);
v___x_5127_ = lean_nat_dec_eq(v_snd_5121_, v_snd_5126_);
lean_dec(v_snd_5121_);
if (v___x_5127_ == 0)
{
lean_dec(v_snd_5126_);
lean_dec_ref(v_pos_5124_);
lean_dec_ref(v___y_5122_);
return v___y_5123_;
}
else
{
lean_object* v___x_5128_; uint8_t v___x_5129_; 
lean_dec_ref(v___y_5123_);
v___x_5128_ = lean_string_utf8_byte_size(v_fst_5125_);
v___x_5129_ = lean_nat_dec_eq(v_snd_5126_, v___x_5128_);
if (v___x_5129_ == 0)
{
if (v___x_5127_ == 0)
{
v___y_5115_ = v_pos_5124_;
v_snd_5116_ = v_snd_5126_;
v___y_5117_ = v___y_5122_;
goto v___jp_5114_;
}
else
{
uint32_t v___x_5130_; uint32_t v_c_5131_; uint8_t v___x_5132_; 
v___x_5130_ = 72;
v_c_5131_ = lean_string_utf8_get_fast(v_fst_5125_, v_snd_5126_);
v___x_5132_ = lean_uint32_dec_eq(v_c_5131_, v___x_5130_);
if (v___x_5132_ == 0)
{
lean_object* v___x_5133_; 
v___x_5133_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__3);
v_snd_5109_ = v_snd_5126_;
v___y_5110_ = v___y_5122_;
v_pos_5111_ = v_pos_5124_;
v_err_5112_ = v___x_5133_;
goto v___jp_5108_;
}
else
{
lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5149_; 
lean_inc(v_fst_5125_);
v_isSharedCheck_5149_ = !lean_is_exclusive(v_pos_5124_);
if (v_isSharedCheck_5149_ == 0)
{
lean_object* v_unused_5150_; lean_object* v_unused_5151_; 
v_unused_5150_ = lean_ctor_get(v_pos_5124_, 1);
lean_dec(v_unused_5150_);
v_unused_5151_ = lean_ctor_get(v_pos_5124_, 0);
lean_dec(v_unused_5151_);
v___x_5135_ = v_pos_5124_;
v_isShared_5136_ = v_isSharedCheck_5149_;
goto v_resetjp_5134_;
}
else
{
lean_dec(v_pos_5124_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5149_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5137_; lean_object* v_it_x27_5139_; 
v___x_5137_ = lean_string_utf8_next_fast(v_fst_5125_, v_snd_5126_);
if (v_isShared_5136_ == 0)
{
lean_ctor_set(v___x_5135_, 1, v___x_5137_);
v_it_x27_5139_ = v___x_5135_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_fst_5125_);
lean_ctor_set(v_reuseFailAlloc_5148_, 1, v___x_5137_);
v_it_x27_5139_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; 
v___x_5140_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__0);
v___x_5141_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(v___x_5140_, v_it_x27_5139_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v_pos_5142_; lean_object* v_res_5143_; lean_object* v___x_5144_; 
v_pos_5142_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_pos_5142_);
v_res_5143_ = lean_ctor_get(v___x_5141_, 1);
lean_inc(v_res_5143_);
lean_dec_ref_known(v___x_5141_, 2);
lean_inc_ref(v___y_5122_);
v___x_5144_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5119_, v___y_5122_, v_res_5143_, v_pos_5142_);
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_dec(v_snd_5126_);
lean_dec_ref(v___y_5122_);
return v___x_5144_;
}
else
{
lean_object* v_pos_5145_; 
v_pos_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_pos_5145_);
v_snd_5077_ = v_snd_5126_;
v___y_5078_ = v___y_5122_;
v___y_5079_ = v___x_5144_;
v_pos_5080_ = v_pos_5145_;
goto v___jp_5076_;
}
}
else
{
lean_object* v_pos_5146_; lean_object* v_err_5147_; 
v_pos_5146_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_pos_5146_);
v_err_5147_ = lean_ctor_get(v___x_5141_, 1);
lean_inc(v_err_5147_);
lean_dec_ref_known(v___x_5141_, 2);
v_snd_5109_ = v_snd_5126_;
v___y_5110_ = v___y_5122_;
v_pos_5111_ = v_pos_5146_;
v_err_5112_ = v_err_5147_;
goto v___jp_5108_;
}
}
}
}
}
}
else
{
v___y_5115_ = v_pos_5124_;
v_snd_5116_ = v_snd_5126_;
v___y_5117_ = v___y_5122_;
goto v___jp_5114_;
}
}
}
v___jp_5152_:
{
lean_object* v___x_5157_; 
lean_inc_ref(v_pos_5155_);
v___x_5157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5157_, 0, v_pos_5155_);
lean_ctor_set(v___x_5157_, 1, v_err_5156_);
v_snd_5121_ = v_snd_5153_;
v___y_5122_ = v___y_5154_;
v___y_5123_ = v___x_5157_;
v_pos_5124_ = v_pos_5155_;
goto v___jp_5120_;
}
v___jp_5158_:
{
lean_object* v___x_5162_; 
v___x_5162_ = lean_box(0);
v_snd_5153_ = v_snd_5160_;
v___y_5154_ = v___y_5161_;
v_pos_5155_ = v___y_5159_;
v_err_5156_ = v___x_5162_;
goto v___jp_5152_;
}
v___jp_5164_:
{
lean_object* v_fst_5169_; lean_object* v_snd_5170_; uint8_t v___x_5171_; 
v_fst_5169_ = lean_ctor_get(v_pos_5168_, 0);
v_snd_5170_ = lean_ctor_get(v_pos_5168_, 1);
lean_inc(v_snd_5170_);
v___x_5171_ = lean_nat_dec_eq(v_snd_5165_, v_snd_5170_);
lean_dec(v_snd_5165_);
if (v___x_5171_ == 0)
{
lean_dec(v_snd_5170_);
lean_dec_ref(v_pos_5168_);
lean_dec_ref(v___y_5166_);
return v___y_5167_;
}
else
{
lean_object* v___x_5172_; uint8_t v___x_5173_; 
lean_dec_ref(v___y_5167_);
v___x_5172_ = lean_string_utf8_byte_size(v_fst_5169_);
v___x_5173_ = lean_nat_dec_eq(v_snd_5170_, v___x_5172_);
if (v___x_5173_ == 0)
{
if (v___x_5171_ == 0)
{
v___y_5159_ = v_pos_5168_;
v_snd_5160_ = v_snd_5170_;
v___y_5161_ = v___y_5166_;
goto v___jp_5158_;
}
else
{
uint32_t v___x_5174_; uint32_t v_c_5175_; uint8_t v___x_5176_; 
v___x_5174_ = 107;
v_c_5175_ = lean_string_utf8_get_fast(v_fst_5169_, v_snd_5170_);
v___x_5176_ = lean_uint32_dec_eq(v_c_5175_, v___x_5174_);
if (v___x_5176_ == 0)
{
lean_object* v___x_5177_; 
v___x_5177_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__3);
v_snd_5153_ = v_snd_5170_;
v___y_5154_ = v___y_5166_;
v_pos_5155_ = v_pos_5168_;
v_err_5156_ = v___x_5177_;
goto v___jp_5152_;
}
else
{
lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5193_; 
lean_inc(v_fst_5169_);
v_isSharedCheck_5193_ = !lean_is_exclusive(v_pos_5168_);
if (v_isSharedCheck_5193_ == 0)
{
lean_object* v_unused_5194_; lean_object* v_unused_5195_; 
v_unused_5194_ = lean_ctor_get(v_pos_5168_, 1);
lean_dec(v_unused_5194_);
v_unused_5195_ = lean_ctor_get(v_pos_5168_, 0);
lean_dec(v_unused_5195_);
v___x_5179_ = v_pos_5168_;
v_isShared_5180_ = v_isSharedCheck_5193_;
goto v_resetjp_5178_;
}
else
{
lean_dec(v_pos_5168_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5193_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v___x_5181_; lean_object* v_it_x27_5183_; 
v___x_5181_ = lean_string_utf8_next_fast(v_fst_5169_, v_snd_5170_);
if (v_isShared_5180_ == 0)
{
lean_ctor_set(v___x_5179_, 1, v___x_5181_);
v_it_x27_5183_ = v___x_5179_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_fst_5169_);
lean_ctor_set(v_reuseFailAlloc_5192_, 1, v___x_5181_);
v_it_x27_5183_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
lean_object* v___x_5184_; lean_object* v___x_5185_; 
v___x_5184_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__0);
v___x_5185_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(v___x_5184_, v_it_x27_5183_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v_pos_5186_; lean_object* v_res_5187_; lean_object* v___x_5188_; 
v_pos_5186_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_pos_5186_);
v_res_5187_ = lean_ctor_get(v___x_5185_, 1);
lean_inc(v_res_5187_);
lean_dec_ref_known(v___x_5185_, 2);
lean_inc_ref(v___y_5166_);
v___x_5188_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5163_, v___y_5166_, v_res_5187_, v_pos_5186_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_dec(v_snd_5170_);
lean_dec_ref(v___y_5166_);
return v___x_5188_;
}
else
{
lean_object* v_pos_5189_; 
v_pos_5189_ = lean_ctor_get(v___x_5188_, 0);
lean_inc(v_pos_5189_);
v_snd_5121_ = v_snd_5170_;
v___y_5122_ = v___y_5166_;
v___y_5123_ = v___x_5188_;
v_pos_5124_ = v_pos_5189_;
goto v___jp_5120_;
}
}
else
{
lean_object* v_pos_5190_; lean_object* v_err_5191_; 
v_pos_5190_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_pos_5190_);
v_err_5191_ = lean_ctor_get(v___x_5185_, 1);
lean_inc(v_err_5191_);
lean_dec_ref_known(v___x_5185_, 2);
v_snd_5153_ = v_snd_5170_;
v___y_5154_ = v___y_5166_;
v_pos_5155_ = v_pos_5190_;
v_err_5156_ = v_err_5191_;
goto v___jp_5152_;
}
}
}
}
}
}
else
{
v___y_5159_ = v_pos_5168_;
v_snd_5160_ = v_snd_5170_;
v___y_5161_ = v___y_5166_;
goto v___jp_5158_;
}
}
}
v___jp_5196_:
{
lean_object* v___x_5201_; 
lean_inc_ref(v_pos_5199_);
v___x_5201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5201_, 0, v_pos_5199_);
lean_ctor_set(v___x_5201_, 1, v_err_5200_);
v_snd_5165_ = v_snd_5197_;
v___y_5166_ = v___y_5198_;
v___y_5167_ = v___x_5201_;
v_pos_5168_ = v_pos_5199_;
goto v___jp_5164_;
}
v___jp_5202_:
{
lean_object* v___x_5206_; 
v___x_5206_ = lean_box(0);
v_snd_5197_ = v_snd_5204_;
v___y_5198_ = v___y_5205_;
v_pos_5199_ = v___y_5203_;
v_err_5200_ = v___x_5206_;
goto v___jp_5196_;
}
v___jp_5208_:
{
lean_object* v_fst_5213_; lean_object* v_snd_5214_; uint8_t v___x_5215_; 
v_fst_5213_ = lean_ctor_get(v_pos_5212_, 0);
v_snd_5214_ = lean_ctor_get(v_pos_5212_, 1);
lean_inc(v_snd_5214_);
v___x_5215_ = lean_nat_dec_eq(v_snd_5209_, v_snd_5214_);
lean_dec(v_snd_5209_);
if (v___x_5215_ == 0)
{
lean_dec(v_snd_5214_);
lean_dec_ref(v_pos_5212_);
lean_dec_ref(v___y_5210_);
return v___y_5211_;
}
else
{
lean_object* v___x_5216_; uint8_t v___x_5217_; 
lean_dec_ref(v___y_5211_);
v___x_5216_ = lean_string_utf8_byte_size(v_fst_5213_);
v___x_5217_ = lean_nat_dec_eq(v_snd_5214_, v___x_5216_);
if (v___x_5217_ == 0)
{
if (v___x_5215_ == 0)
{
v___y_5203_ = v_pos_5212_;
v_snd_5204_ = v_snd_5214_;
v___y_5205_ = v___y_5210_;
goto v___jp_5202_;
}
else
{
uint32_t v___x_5218_; uint32_t v_c_5219_; uint8_t v___x_5220_; 
v___x_5218_ = 75;
v_c_5219_ = lean_string_utf8_get_fast(v_fst_5213_, v_snd_5214_);
v___x_5220_ = lean_uint32_dec_eq(v_c_5219_, v___x_5218_);
if (v___x_5220_ == 0)
{
lean_object* v___x_5221_; 
v___x_5221_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__3);
v_snd_5197_ = v_snd_5214_;
v___y_5198_ = v___y_5210_;
v_pos_5199_ = v_pos_5212_;
v_err_5200_ = v___x_5221_;
goto v___jp_5196_;
}
else
{
lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5237_; 
lean_inc(v_fst_5213_);
v_isSharedCheck_5237_ = !lean_is_exclusive(v_pos_5212_);
if (v_isSharedCheck_5237_ == 0)
{
lean_object* v_unused_5238_; lean_object* v_unused_5239_; 
v_unused_5238_ = lean_ctor_get(v_pos_5212_, 1);
lean_dec(v_unused_5238_);
v_unused_5239_ = lean_ctor_get(v_pos_5212_, 0);
lean_dec(v_unused_5239_);
v___x_5223_ = v_pos_5212_;
v_isShared_5224_ = v_isSharedCheck_5237_;
goto v_resetjp_5222_;
}
else
{
lean_dec(v_pos_5212_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5237_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5225_; lean_object* v_it_x27_5227_; 
v___x_5225_ = lean_string_utf8_next_fast(v_fst_5213_, v_snd_5214_);
if (v_isShared_5224_ == 0)
{
lean_ctor_set(v___x_5223_, 1, v___x_5225_);
v_it_x27_5227_ = v___x_5223_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_fst_5213_);
lean_ctor_set(v_reuseFailAlloc_5236_, 1, v___x_5225_);
v_it_x27_5227_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
lean_object* v___x_5228_; lean_object* v___x_5229_; 
v___x_5228_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__0);
v___x_5229_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(v___x_5228_, v_it_x27_5227_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_pos_5230_; lean_object* v_res_5231_; lean_object* v___x_5232_; 
v_pos_5230_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_pos_5230_);
v_res_5231_ = lean_ctor_get(v___x_5229_, 1);
lean_inc(v_res_5231_);
lean_dec_ref_known(v___x_5229_, 2);
lean_inc_ref(v___y_5210_);
v___x_5232_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5207_, v___y_5210_, v_res_5231_, v_pos_5230_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_dec(v_snd_5214_);
lean_dec_ref(v___y_5210_);
return v___x_5232_;
}
else
{
lean_object* v_pos_5233_; 
v_pos_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc(v_pos_5233_);
v_snd_5165_ = v_snd_5214_;
v___y_5166_ = v___y_5210_;
v___y_5167_ = v___x_5232_;
v_pos_5168_ = v_pos_5233_;
goto v___jp_5164_;
}
}
else
{
lean_object* v_pos_5234_; lean_object* v_err_5235_; 
v_pos_5234_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_pos_5234_);
v_err_5235_ = lean_ctor_get(v___x_5229_, 1);
lean_inc(v_err_5235_);
lean_dec_ref_known(v___x_5229_, 2);
v_snd_5197_ = v_snd_5214_;
v___y_5198_ = v___y_5210_;
v_pos_5199_ = v_pos_5234_;
v_err_5200_ = v_err_5235_;
goto v___jp_5196_;
}
}
}
}
}
}
else
{
v___y_5203_ = v_pos_5212_;
v_snd_5204_ = v_snd_5214_;
v___y_5205_ = v___y_5210_;
goto v___jp_5202_;
}
}
}
v___jp_5240_:
{
lean_object* v___x_5245_; 
lean_inc_ref(v_pos_5243_);
v___x_5245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5245_, 0, v_pos_5243_);
lean_ctor_set(v___x_5245_, 1, v_err_5244_);
v_snd_5209_ = v_snd_5241_;
v___y_5210_ = v___y_5242_;
v___y_5211_ = v___x_5245_;
v_pos_5212_ = v_pos_5243_;
goto v___jp_5208_;
}
v___jp_5246_:
{
lean_object* v___x_5250_; 
v___x_5250_ = lean_box(0);
v_snd_5241_ = v_snd_5248_;
v___y_5242_ = v___y_5249_;
v_pos_5243_ = v___y_5247_;
v_err_5244_ = v___x_5250_;
goto v___jp_5240_;
}
v___jp_5252_:
{
lean_object* v_fst_5257_; lean_object* v_snd_5258_; uint8_t v___x_5259_; 
v_fst_5257_ = lean_ctor_get(v_pos_5256_, 0);
v_snd_5258_ = lean_ctor_get(v_pos_5256_, 1);
lean_inc(v_snd_5258_);
v___x_5259_ = lean_nat_dec_eq(v_snd_5253_, v_snd_5258_);
lean_dec(v_snd_5253_);
if (v___x_5259_ == 0)
{
lean_dec(v_snd_5258_);
lean_dec_ref(v_pos_5256_);
lean_dec_ref(v___y_5254_);
return v___y_5255_;
}
else
{
lean_object* v___x_5260_; uint8_t v___x_5261_; 
lean_dec_ref(v___y_5255_);
v___x_5260_ = lean_string_utf8_byte_size(v_fst_5257_);
v___x_5261_ = lean_nat_dec_eq(v_snd_5258_, v___x_5260_);
if (v___x_5261_ == 0)
{
if (v___x_5259_ == 0)
{
v___y_5247_ = v_pos_5256_;
v_snd_5248_ = v_snd_5258_;
v___y_5249_ = v___y_5254_;
goto v___jp_5246_;
}
else
{
uint32_t v___x_5262_; uint32_t v_c_5263_; uint8_t v___x_5264_; 
v___x_5262_ = 104;
v_c_5263_ = lean_string_utf8_get_fast(v_fst_5257_, v_snd_5258_);
v___x_5264_ = lean_uint32_dec_eq(v_c_5263_, v___x_5262_);
if (v___x_5264_ == 0)
{
lean_object* v___x_5265_; 
v___x_5265_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__3);
v_snd_5241_ = v_snd_5258_;
v___y_5242_ = v___y_5254_;
v_pos_5243_ = v_pos_5256_;
v_err_5244_ = v___x_5265_;
goto v___jp_5240_;
}
else
{
lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5281_; 
lean_inc(v_fst_5257_);
v_isSharedCheck_5281_ = !lean_is_exclusive(v_pos_5256_);
if (v_isSharedCheck_5281_ == 0)
{
lean_object* v_unused_5282_; lean_object* v_unused_5283_; 
v_unused_5282_ = lean_ctor_get(v_pos_5256_, 1);
lean_dec(v_unused_5282_);
v_unused_5283_ = lean_ctor_get(v_pos_5256_, 0);
lean_dec(v_unused_5283_);
v___x_5267_ = v_pos_5256_;
v_isShared_5268_ = v_isSharedCheck_5281_;
goto v_resetjp_5266_;
}
else
{
lean_dec(v_pos_5256_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5281_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5269_; lean_object* v_it_x27_5271_; 
v___x_5269_ = lean_string_utf8_next_fast(v_fst_5257_, v_snd_5258_);
if (v_isShared_5268_ == 0)
{
lean_ctor_set(v___x_5267_, 1, v___x_5269_);
v_it_x27_5271_ = v___x_5267_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_fst_5257_);
lean_ctor_set(v_reuseFailAlloc_5280_, 1, v___x_5269_);
v_it_x27_5271_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
lean_object* v___x_5272_; lean_object* v___x_5273_; 
v___x_5272_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__0);
v___x_5273_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(v___x_5272_, v_it_x27_5271_);
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v_pos_5274_; lean_object* v_res_5275_; lean_object* v___x_5276_; 
v_pos_5274_ = lean_ctor_get(v___x_5273_, 0);
lean_inc(v_pos_5274_);
v_res_5275_ = lean_ctor_get(v___x_5273_, 1);
lean_inc(v_res_5275_);
lean_dec_ref_known(v___x_5273_, 2);
lean_inc_ref(v___y_5254_);
v___x_5276_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5251_, v___y_5254_, v_res_5275_, v_pos_5274_);
if (lean_obj_tag(v___x_5276_) == 0)
{
lean_dec(v_snd_5258_);
lean_dec_ref(v___y_5254_);
return v___x_5276_;
}
else
{
lean_object* v_pos_5277_; 
v_pos_5277_ = lean_ctor_get(v___x_5276_, 0);
lean_inc(v_pos_5277_);
v_snd_5209_ = v_snd_5258_;
v___y_5210_ = v___y_5254_;
v___y_5211_ = v___x_5276_;
v_pos_5212_ = v_pos_5277_;
goto v___jp_5208_;
}
}
else
{
lean_object* v_pos_5278_; lean_object* v_err_5279_; 
v_pos_5278_ = lean_ctor_get(v___x_5273_, 0);
lean_inc(v_pos_5278_);
v_err_5279_ = lean_ctor_get(v___x_5273_, 1);
lean_inc(v_err_5279_);
lean_dec_ref_known(v___x_5273_, 2);
v_snd_5241_ = v_snd_5258_;
v___y_5242_ = v___y_5254_;
v_pos_5243_ = v_pos_5278_;
v_err_5244_ = v_err_5279_;
goto v___jp_5240_;
}
}
}
}
}
}
else
{
v___y_5247_ = v_pos_5256_;
v_snd_5248_ = v_snd_5258_;
v___y_5249_ = v___y_5254_;
goto v___jp_5246_;
}
}
}
v___jp_5284_:
{
lean_object* v___x_5289_; 
lean_inc_ref(v_pos_5287_);
v___x_5289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5289_, 0, v_pos_5287_);
lean_ctor_set(v___x_5289_, 1, v_err_5288_);
v_snd_5253_ = v_snd_5285_;
v___y_5254_ = v___y_5286_;
v___y_5255_ = v___x_5289_;
v_pos_5256_ = v_pos_5287_;
goto v___jp_5252_;
}
v___jp_5290_:
{
lean_object* v___x_5294_; 
v___x_5294_ = lean_box(0);
v_snd_5285_ = v_snd_5292_;
v___y_5286_ = v___y_5293_;
v_pos_5287_ = v___y_5291_;
v_err_5288_ = v___x_5294_;
goto v___jp_5284_;
}
v___jp_5295_:
{
lean_object* v_fst_5300_; lean_object* v_snd_5301_; uint8_t v___x_5302_; 
v_fst_5300_ = lean_ctor_get(v_pos_5299_, 0);
v_snd_5301_ = lean_ctor_get(v_pos_5299_, 1);
lean_inc(v_snd_5301_);
v___x_5302_ = lean_nat_dec_eq(v_snd_5296_, v_snd_5301_);
lean_dec(v_snd_5296_);
if (v___x_5302_ == 0)
{
lean_dec(v_snd_5301_);
lean_dec_ref(v_pos_5299_);
lean_dec_ref(v___y_5297_);
return v___y_5298_;
}
else
{
lean_object* v___x_5303_; uint8_t v___x_5304_; 
lean_dec_ref(v___y_5298_);
v___x_5303_ = lean_string_utf8_byte_size(v_fst_5300_);
v___x_5304_ = lean_nat_dec_eq(v_snd_5301_, v___x_5303_);
if (v___x_5304_ == 0)
{
if (v___x_5302_ == 0)
{
v___y_5291_ = v_pos_5299_;
v_snd_5292_ = v_snd_5301_;
v___y_5293_ = v___y_5297_;
goto v___jp_5290_;
}
else
{
uint32_t v___x_5305_; uint32_t v_c_5306_; uint8_t v___x_5307_; 
v___x_5305_ = 66;
v_c_5306_ = lean_string_utf8_get_fast(v_fst_5300_, v_snd_5301_);
v___x_5307_ = lean_uint32_dec_eq(v_c_5306_, v___x_5305_);
if (v___x_5307_ == 0)
{
lean_object* v___x_5308_; 
v___x_5308_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__3);
v_snd_5285_ = v_snd_5301_;
v___y_5286_ = v___y_5297_;
v_pos_5287_ = v_pos_5299_;
v_err_5288_ = v___x_5308_;
goto v___jp_5284_;
}
else
{
lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5324_; 
lean_inc(v_fst_5300_);
v_isSharedCheck_5324_ = !lean_is_exclusive(v_pos_5299_);
if (v_isSharedCheck_5324_ == 0)
{
lean_object* v_unused_5325_; lean_object* v_unused_5326_; 
v_unused_5325_ = lean_ctor_get(v_pos_5299_, 1);
lean_dec(v_unused_5325_);
v_unused_5326_ = lean_ctor_get(v_pos_5299_, 0);
lean_dec(v_unused_5326_);
v___x_5310_ = v_pos_5299_;
v_isShared_5311_ = v_isSharedCheck_5324_;
goto v_resetjp_5309_;
}
else
{
lean_dec(v_pos_5299_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5324_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5312_; lean_object* v_it_x27_5314_; 
v___x_5312_ = lean_string_utf8_next_fast(v_fst_5300_, v_snd_5301_);
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 1, v___x_5312_);
v_it_x27_5314_ = v___x_5310_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_fst_5300_);
lean_ctor_set(v_reuseFailAlloc_5323_, 1, v___x_5312_);
v_it_x27_5314_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___x_5315_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__0);
v___x_5316_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(v___x_5315_, v_it_x27_5314_);
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_object* v_pos_5317_; lean_object* v_res_5318_; lean_object* v___x_5319_; 
v_pos_5317_ = lean_ctor_get(v___x_5316_, 0);
lean_inc(v_pos_5317_);
v_res_5318_ = lean_ctor_get(v___x_5316_, 1);
lean_inc(v_res_5318_);
lean_dec_ref_known(v___x_5316_, 2);
v___x_5319_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(v_res_5318_, v_pos_5317_);
if (lean_obj_tag(v___x_5319_) == 0)
{
lean_dec(v_snd_5301_);
lean_dec_ref(v___y_5297_);
return v___x_5319_;
}
else
{
lean_object* v_pos_5320_; 
v_pos_5320_ = lean_ctor_get(v___x_5319_, 0);
lean_inc(v_pos_5320_);
v_snd_5253_ = v_snd_5301_;
v___y_5254_ = v___y_5297_;
v___y_5255_ = v___x_5319_;
v_pos_5256_ = v_pos_5320_;
goto v___jp_5252_;
}
}
else
{
lean_object* v_pos_5321_; lean_object* v_err_5322_; 
v_pos_5321_ = lean_ctor_get(v___x_5316_, 0);
lean_inc(v_pos_5321_);
v_err_5322_ = lean_ctor_get(v___x_5316_, 1);
lean_inc(v_err_5322_);
lean_dec_ref_known(v___x_5316_, 2);
v_snd_5285_ = v_snd_5301_;
v___y_5286_ = v___y_5297_;
v_pos_5287_ = v_pos_5321_;
v_err_5288_ = v_err_5322_;
goto v___jp_5284_;
}
}
}
}
}
}
else
{
v___y_5291_ = v_pos_5299_;
v_snd_5292_ = v_snd_5301_;
v___y_5293_ = v___y_5297_;
goto v___jp_5290_;
}
}
}
v___jp_5327_:
{
lean_object* v___x_5332_; 
lean_inc_ref(v_pos_5330_);
v___x_5332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5332_, 0, v_pos_5330_);
lean_ctor_set(v___x_5332_, 1, v_err_5331_);
v_snd_5296_ = v_snd_5328_;
v___y_5297_ = v___y_5329_;
v___y_5298_ = v___x_5332_;
v_pos_5299_ = v_pos_5330_;
goto v___jp_5295_;
}
v___jp_5333_:
{
lean_object* v___x_5337_; 
v___x_5337_ = lean_box(0);
v_snd_5328_ = v_snd_5335_;
v___y_5329_ = v___y_5336_;
v_pos_5330_ = v___y_5334_;
v_err_5331_ = v___x_5337_;
goto v___jp_5327_;
}
v___jp_5338_:
{
lean_object* v_fst_5343_; lean_object* v_snd_5344_; uint8_t v___x_5345_; 
v_fst_5343_ = lean_ctor_get(v_pos_5342_, 0);
v_snd_5344_ = lean_ctor_get(v_pos_5342_, 1);
lean_inc(v_snd_5344_);
v___x_5345_ = lean_nat_dec_eq(v_snd_5339_, v_snd_5344_);
lean_dec(v_snd_5339_);
if (v___x_5345_ == 0)
{
lean_dec(v_snd_5344_);
lean_dec_ref(v_pos_5342_);
lean_dec_ref(v___y_5340_);
return v___y_5341_;
}
else
{
lean_object* v___x_5346_; uint8_t v___x_5347_; 
lean_dec_ref(v___y_5341_);
v___x_5346_ = lean_string_utf8_byte_size(v_fst_5343_);
v___x_5347_ = lean_nat_dec_eq(v_snd_5344_, v___x_5346_);
if (v___x_5347_ == 0)
{
if (v___x_5345_ == 0)
{
v___y_5334_ = v_pos_5342_;
v_snd_5335_ = v_snd_5344_;
v___y_5336_ = v___y_5340_;
goto v___jp_5333_;
}
else
{
uint32_t v___x_5348_; uint32_t v_c_5349_; uint8_t v___x_5350_; 
v___x_5348_ = 98;
v_c_5349_ = lean_string_utf8_get_fast(v_fst_5343_, v_snd_5344_);
v___x_5350_ = lean_uint32_dec_eq(v_c_5349_, v___x_5348_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; 
v___x_5351_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__3);
v_snd_5328_ = v_snd_5344_;
v___y_5329_ = v___y_5340_;
v_pos_5330_ = v_pos_5342_;
v_err_5331_ = v___x_5351_;
goto v___jp_5327_;
}
else
{
lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5367_; 
lean_inc(v_fst_5343_);
v_isSharedCheck_5367_ = !lean_is_exclusive(v_pos_5342_);
if (v_isSharedCheck_5367_ == 0)
{
lean_object* v_unused_5368_; lean_object* v_unused_5369_; 
v_unused_5368_ = lean_ctor_get(v_pos_5342_, 1);
lean_dec(v_unused_5368_);
v_unused_5369_ = lean_ctor_get(v_pos_5342_, 0);
lean_dec(v_unused_5369_);
v___x_5353_ = v_pos_5342_;
v_isShared_5354_ = v_isSharedCheck_5367_;
goto v_resetjp_5352_;
}
else
{
lean_dec(v_pos_5342_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5367_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v___x_5355_; lean_object* v_it_x27_5357_; 
v___x_5355_ = lean_string_utf8_next_fast(v_fst_5343_, v_snd_5344_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 1, v___x_5355_);
v_it_x27_5357_ = v___x_5353_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_fst_5343_);
lean_ctor_set(v_reuseFailAlloc_5366_, 1, v___x_5355_);
v_it_x27_5357_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5358_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__0);
v___x_5359_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(v___x_5358_, v_it_x27_5357_);
if (lean_obj_tag(v___x_5359_) == 0)
{
lean_object* v_pos_5360_; lean_object* v_res_5361_; lean_object* v___x_5362_; 
v_pos_5360_ = lean_ctor_get(v___x_5359_, 0);
lean_inc(v_pos_5360_);
v_res_5361_ = lean_ctor_get(v___x_5359_, 1);
lean_inc(v_res_5361_);
lean_dec_ref_known(v___x_5359_, 2);
v___x_5362_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(v_res_5361_, v_pos_5360_);
if (lean_obj_tag(v___x_5362_) == 0)
{
lean_dec(v_snd_5344_);
lean_dec_ref(v___y_5340_);
return v___x_5362_;
}
else
{
lean_object* v_pos_5363_; 
v_pos_5363_ = lean_ctor_get(v___x_5362_, 0);
lean_inc(v_pos_5363_);
v_snd_5296_ = v_snd_5344_;
v___y_5297_ = v___y_5340_;
v___y_5298_ = v___x_5362_;
v_pos_5299_ = v_pos_5363_;
goto v___jp_5295_;
}
}
else
{
lean_object* v_pos_5364_; lean_object* v_err_5365_; 
v_pos_5364_ = lean_ctor_get(v___x_5359_, 0);
lean_inc(v_pos_5364_);
v_err_5365_ = lean_ctor_get(v___x_5359_, 1);
lean_inc(v_err_5365_);
lean_dec_ref_known(v___x_5359_, 2);
v_snd_5328_ = v_snd_5344_;
v___y_5329_ = v___y_5340_;
v_pos_5330_ = v_pos_5364_;
v_err_5331_ = v_err_5365_;
goto v___jp_5327_;
}
}
}
}
}
}
else
{
v___y_5334_ = v_pos_5342_;
v_snd_5335_ = v_snd_5344_;
v___y_5336_ = v___y_5340_;
goto v___jp_5333_;
}
}
}
v___jp_5370_:
{
lean_object* v___x_5375_; 
lean_inc_ref(v_pos_5373_);
v___x_5375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5375_, 0, v_pos_5373_);
lean_ctor_set(v___x_5375_, 1, v_err_5374_);
v_snd_5339_ = v_snd_5371_;
v___y_5340_ = v___y_5372_;
v___y_5341_ = v___x_5375_;
v_pos_5342_ = v_pos_5373_;
goto v___jp_5338_;
}
v___jp_5376_:
{
lean_object* v___x_5380_; 
v___x_5380_ = lean_box(0);
v_snd_5371_ = v_snd_5378_;
v___y_5372_ = v___y_5379_;
v_pos_5373_ = v___y_5377_;
v_err_5374_ = v___x_5380_;
goto v___jp_5370_;
}
v___jp_5381_:
{
lean_object* v_fst_5386_; lean_object* v_snd_5387_; uint8_t v___x_5388_; 
v_fst_5386_ = lean_ctor_get(v_pos_5385_, 0);
v_snd_5387_ = lean_ctor_get(v_pos_5385_, 1);
lean_inc(v_snd_5387_);
v___x_5388_ = lean_nat_dec_eq(v_snd_5382_, v_snd_5387_);
lean_dec(v_snd_5382_);
if (v___x_5388_ == 0)
{
lean_dec(v_snd_5387_);
lean_dec_ref(v_pos_5385_);
lean_dec_ref(v___y_5383_);
return v___y_5384_;
}
else
{
lean_object* v___x_5389_; uint8_t v___x_5390_; 
lean_dec_ref(v___y_5384_);
v___x_5389_ = lean_string_utf8_byte_size(v_fst_5386_);
v___x_5390_ = lean_nat_dec_eq(v_snd_5387_, v___x_5389_);
if (v___x_5390_ == 0)
{
if (v___x_5388_ == 0)
{
v___y_5377_ = v_pos_5385_;
v_snd_5378_ = v_snd_5387_;
v___y_5379_ = v___y_5383_;
goto v___jp_5376_;
}
else
{
uint32_t v___x_5391_; uint32_t v_c_5392_; uint8_t v___x_5393_; 
v___x_5391_ = 97;
v_c_5392_ = lean_string_utf8_get_fast(v_fst_5386_, v_snd_5387_);
v___x_5393_ = lean_uint32_dec_eq(v_c_5392_, v___x_5391_);
if (v___x_5393_ == 0)
{
lean_object* v___x_5394_; 
v___x_5394_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__3);
v_snd_5371_ = v_snd_5387_;
v___y_5372_ = v___y_5383_;
v_pos_5373_ = v_pos_5385_;
v_err_5374_ = v___x_5394_;
goto v___jp_5370_;
}
else
{
lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5410_; 
lean_inc(v_fst_5386_);
v_isSharedCheck_5410_ = !lean_is_exclusive(v_pos_5385_);
if (v_isSharedCheck_5410_ == 0)
{
lean_object* v_unused_5411_; lean_object* v_unused_5412_; 
v_unused_5411_ = lean_ctor_get(v_pos_5385_, 1);
lean_dec(v_unused_5411_);
v_unused_5412_ = lean_ctor_get(v_pos_5385_, 0);
lean_dec(v_unused_5412_);
v___x_5396_ = v_pos_5385_;
v_isShared_5397_ = v_isSharedCheck_5410_;
goto v_resetjp_5395_;
}
else
{
lean_dec(v_pos_5385_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5410_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5398_; lean_object* v_it_x27_5400_; 
v___x_5398_ = lean_string_utf8_next_fast(v_fst_5386_, v_snd_5387_);
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 1, v___x_5398_);
v_it_x27_5400_ = v___x_5396_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_fst_5386_);
lean_ctor_set(v_reuseFailAlloc_5409_, 1, v___x_5398_);
v_it_x27_5400_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5401_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__0);
v___x_5402_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(v___x_5401_, v_it_x27_5400_);
if (lean_obj_tag(v___x_5402_) == 0)
{
lean_object* v_pos_5403_; lean_object* v_res_5404_; lean_object* v___x_5405_; 
v_pos_5403_ = lean_ctor_get(v___x_5402_, 0);
lean_inc(v_pos_5403_);
v_res_5404_ = lean_ctor_get(v___x_5402_, 1);
lean_inc(v_res_5404_);
lean_dec_ref_known(v___x_5402_, 2);
v___x_5405_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(v_res_5404_, v_pos_5403_);
if (lean_obj_tag(v___x_5405_) == 0)
{
lean_dec(v_snd_5387_);
lean_dec_ref(v___y_5383_);
return v___x_5405_;
}
else
{
lean_object* v_pos_5406_; 
v_pos_5406_ = lean_ctor_get(v___x_5405_, 0);
lean_inc(v_pos_5406_);
v_snd_5339_ = v_snd_5387_;
v___y_5340_ = v___y_5383_;
v___y_5341_ = v___x_5405_;
v_pos_5342_ = v_pos_5406_;
goto v___jp_5338_;
}
}
else
{
lean_object* v_pos_5407_; lean_object* v_err_5408_; 
v_pos_5407_ = lean_ctor_get(v___x_5402_, 0);
lean_inc(v_pos_5407_);
v_err_5408_ = lean_ctor_get(v___x_5402_, 1);
lean_inc(v_err_5408_);
lean_dec_ref_known(v___x_5402_, 2);
v_snd_5371_ = v_snd_5387_;
v___y_5372_ = v___y_5383_;
v_pos_5373_ = v_pos_5407_;
v_err_5374_ = v_err_5408_;
goto v___jp_5370_;
}
}
}
}
}
}
else
{
v___y_5377_ = v_pos_5385_;
v_snd_5378_ = v_snd_5387_;
v___y_5379_ = v___y_5383_;
goto v___jp_5376_;
}
}
}
v___jp_5413_:
{
lean_object* v___x_5418_; 
lean_inc_ref(v_pos_5416_);
v___x_5418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5418_, 0, v_pos_5416_);
lean_ctor_set(v___x_5418_, 1, v_err_5417_);
v_snd_5382_ = v_snd_5414_;
v___y_5383_ = v___y_5415_;
v___y_5384_ = v___x_5418_;
v_pos_5385_ = v_pos_5416_;
goto v___jp_5381_;
}
v___jp_5419_:
{
lean_object* v___x_5423_; 
v___x_5423_ = lean_box(0);
v_snd_5414_ = v_snd_5421_;
v___y_5415_ = v___y_5422_;
v_pos_5416_ = v___y_5420_;
v_err_5417_ = v___x_5423_;
goto v___jp_5413_;
}
v___jp_5425_:
{
lean_object* v_fst_5431_; lean_object* v_snd_5432_; uint8_t v___x_5433_; 
v_fst_5431_ = lean_ctor_get(v_pos_5430_, 0);
v_snd_5432_ = lean_ctor_get(v_pos_5430_, 1);
lean_inc(v_snd_5432_);
v___x_5433_ = lean_nat_dec_eq(v_snd_5427_, v_snd_5432_);
lean_dec(v_snd_5427_);
if (v___x_5433_ == 0)
{
lean_dec(v_snd_5432_);
lean_dec_ref(v_pos_5430_);
lean_dec_ref(v___y_5428_);
lean_dec_ref(v___y_5426_);
return v___y_5429_;
}
else
{
lean_object* v___x_5434_; uint8_t v___x_5435_; 
lean_dec_ref(v___y_5429_);
v___x_5434_ = lean_string_utf8_byte_size(v_fst_5431_);
v___x_5435_ = lean_nat_dec_eq(v_snd_5432_, v___x_5434_);
if (v___x_5435_ == 0)
{
if (v___x_5433_ == 0)
{
lean_dec_ref(v___y_5426_);
v___y_5420_ = v_pos_5430_;
v_snd_5421_ = v_snd_5432_;
v___y_5422_ = v___y_5428_;
goto v___jp_5419_;
}
else
{
uint32_t v___x_5436_; uint32_t v_c_5437_; uint8_t v___x_5438_; 
v___x_5436_ = 70;
v_c_5437_ = lean_string_utf8_get_fast(v_fst_5431_, v_snd_5432_);
v___x_5438_ = lean_uint32_dec_eq(v_c_5437_, v___x_5436_);
if (v___x_5438_ == 0)
{
lean_object* v___x_5439_; 
lean_dec_ref(v___y_5426_);
v___x_5439_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__3);
v_snd_5414_ = v_snd_5432_;
v___y_5415_ = v___y_5428_;
v_pos_5416_ = v_pos_5430_;
v_err_5417_ = v___x_5439_;
goto v___jp_5413_;
}
else
{
lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5455_; 
lean_inc(v_fst_5431_);
v_isSharedCheck_5455_ = !lean_is_exclusive(v_pos_5430_);
if (v_isSharedCheck_5455_ == 0)
{
lean_object* v_unused_5456_; lean_object* v_unused_5457_; 
v_unused_5456_ = lean_ctor_get(v_pos_5430_, 1);
lean_dec(v_unused_5456_);
v_unused_5457_ = lean_ctor_get(v_pos_5430_, 0);
lean_dec(v_unused_5457_);
v___x_5441_ = v_pos_5430_;
v_isShared_5442_ = v_isSharedCheck_5455_;
goto v_resetjp_5440_;
}
else
{
lean_dec(v_pos_5430_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5455_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5443_; lean_object* v_it_x27_5445_; 
v___x_5443_ = lean_string_utf8_next_fast(v_fst_5431_, v_snd_5432_);
if (v_isShared_5442_ == 0)
{
lean_ctor_set(v___x_5441_, 1, v___x_5443_);
v_it_x27_5445_ = v___x_5441_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v_fst_5431_);
lean_ctor_set(v_reuseFailAlloc_5454_, 1, v___x_5443_);
v_it_x27_5445_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___x_5446_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__0);
v___x_5447_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(v___x_5446_, v_it_x27_5445_);
if (lean_obj_tag(v___x_5447_) == 0)
{
lean_object* v_pos_5448_; lean_object* v_res_5449_; lean_object* v___x_5450_; 
v_pos_5448_ = lean_ctor_get(v___x_5447_, 0);
lean_inc(v_pos_5448_);
v_res_5449_ = lean_ctor_get(v___x_5447_, 1);
lean_inc(v_res_5449_);
lean_dec_ref_known(v___x_5447_, 2);
v___x_5450_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5424_, v___y_5426_, v_res_5449_, v_pos_5448_);
if (lean_obj_tag(v___x_5450_) == 0)
{
lean_dec(v_snd_5432_);
lean_dec_ref(v___y_5428_);
return v___x_5450_;
}
else
{
lean_object* v_pos_5451_; 
v_pos_5451_ = lean_ctor_get(v___x_5450_, 0);
lean_inc(v_pos_5451_);
v_snd_5382_ = v_snd_5432_;
v___y_5383_ = v___y_5428_;
v___y_5384_ = v___x_5450_;
v_pos_5385_ = v_pos_5451_;
goto v___jp_5381_;
}
}
else
{
lean_object* v_pos_5452_; lean_object* v_err_5453_; 
lean_dec_ref(v___y_5426_);
v_pos_5452_ = lean_ctor_get(v___x_5447_, 0);
lean_inc(v_pos_5452_);
v_err_5453_ = lean_ctor_get(v___x_5447_, 1);
lean_inc(v_err_5453_);
lean_dec_ref_known(v___x_5447_, 2);
v_snd_5414_ = v_snd_5432_;
v___y_5415_ = v___y_5428_;
v_pos_5416_ = v_pos_5452_;
v_err_5417_ = v_err_5453_;
goto v___jp_5413_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_5426_);
v___y_5420_ = v_pos_5430_;
v_snd_5421_ = v_snd_5432_;
v___y_5422_ = v___y_5428_;
goto v___jp_5419_;
}
}
}
v___jp_5458_:
{
lean_object* v___x_5464_; 
lean_inc_ref(v_pos_5462_);
v___x_5464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5464_, 0, v_pos_5462_);
lean_ctor_set(v___x_5464_, 1, v_err_5463_);
v___y_5426_ = v___y_5459_;
v_snd_5427_ = v_snd_5460_;
v___y_5428_ = v___y_5461_;
v___y_5429_ = v___x_5464_;
v_pos_5430_ = v_pos_5462_;
goto v___jp_5425_;
}
v___jp_5465_:
{
lean_object* v___x_5470_; 
v___x_5470_ = lean_box(0);
v___y_5459_ = v___y_5466_;
v_snd_5460_ = v_snd_5468_;
v___y_5461_ = v___y_5469_;
v_pos_5462_ = v___y_5467_;
v_err_5463_ = v___x_5470_;
goto v___jp_5458_;
}
v___jp_5472_:
{
lean_object* v_fst_5478_; lean_object* v_snd_5479_; uint8_t v___x_5480_; 
v_fst_5478_ = lean_ctor_get(v_pos_5477_, 0);
v_snd_5479_ = lean_ctor_get(v_pos_5477_, 1);
lean_inc(v_snd_5479_);
v___x_5480_ = lean_nat_dec_eq(v_snd_5473_, v_snd_5479_);
lean_dec(v_snd_5473_);
if (v___x_5480_ == 0)
{
lean_dec(v_snd_5479_);
lean_dec_ref(v_pos_5477_);
lean_dec_ref(v___y_5475_);
lean_dec_ref(v___y_5474_);
return v___y_5476_;
}
else
{
lean_object* v___x_5481_; uint8_t v___x_5482_; 
lean_dec_ref(v___y_5476_);
v___x_5481_ = lean_string_utf8_byte_size(v_fst_5478_);
v___x_5482_ = lean_nat_dec_eq(v_snd_5479_, v___x_5481_);
if (v___x_5482_ == 0)
{
if (v___x_5480_ == 0)
{
v___y_5466_ = v___y_5474_;
v___y_5467_ = v_pos_5477_;
v_snd_5468_ = v_snd_5479_;
v___y_5469_ = v___y_5475_;
goto v___jp_5465_;
}
else
{
uint32_t v___x_5483_; uint32_t v_c_5484_; uint8_t v___x_5485_; 
v___x_5483_ = 99;
v_c_5484_ = lean_string_utf8_get_fast(v_fst_5478_, v_snd_5479_);
v___x_5485_ = lean_uint32_dec_eq(v_c_5484_, v___x_5483_);
if (v___x_5485_ == 0)
{
lean_object* v___x_5486_; 
v___x_5486_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__3);
v___y_5459_ = v___y_5474_;
v_snd_5460_ = v_snd_5479_;
v___y_5461_ = v___y_5475_;
v_pos_5462_ = v_pos_5477_;
v_err_5463_ = v___x_5486_;
goto v___jp_5458_;
}
else
{
lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5502_; 
lean_inc(v_fst_5478_);
v_isSharedCheck_5502_ = !lean_is_exclusive(v_pos_5477_);
if (v_isSharedCheck_5502_ == 0)
{
lean_object* v_unused_5503_; lean_object* v_unused_5504_; 
v_unused_5503_ = lean_ctor_get(v_pos_5477_, 1);
lean_dec(v_unused_5503_);
v_unused_5504_ = lean_ctor_get(v_pos_5477_, 0);
lean_dec(v_unused_5504_);
v___x_5488_ = v_pos_5477_;
v_isShared_5489_ = v_isSharedCheck_5502_;
goto v_resetjp_5487_;
}
else
{
lean_dec(v_pos_5477_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5502_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5490_; lean_object* v_it_x27_5492_; 
v___x_5490_ = lean_string_utf8_next_fast(v_fst_5478_, v_snd_5479_);
if (v_isShared_5489_ == 0)
{
lean_ctor_set(v___x_5488_, 1, v___x_5490_);
v_it_x27_5492_ = v___x_5488_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_fst_5478_);
lean_ctor_set(v_reuseFailAlloc_5501_, 1, v___x_5490_);
v_it_x27_5492_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5493_; lean_object* v___x_5494_; 
v___x_5493_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__0);
v___x_5494_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(v___x_5493_, v_it_x27_5492_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_pos_5495_; lean_object* v_res_5496_; lean_object* v___x_5497_; 
v_pos_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_pos_5495_);
v_res_5496_ = lean_ctor_get(v___x_5494_, 1);
lean_inc(v_res_5496_);
lean_dec_ref_known(v___x_5494_, 2);
v___x_5497_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(v___f_5471_, v_res_5496_, v_pos_5495_);
if (lean_obj_tag(v___x_5497_) == 0)
{
lean_dec(v_snd_5479_);
lean_dec_ref(v___y_5475_);
lean_dec_ref(v___y_5474_);
return v___x_5497_;
}
else
{
lean_object* v_pos_5498_; 
v_pos_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc(v_pos_5498_);
v___y_5426_ = v___y_5474_;
v_snd_5427_ = v_snd_5479_;
v___y_5428_ = v___y_5475_;
v___y_5429_ = v___x_5497_;
v_pos_5430_ = v_pos_5498_;
goto v___jp_5425_;
}
}
else
{
lean_object* v_pos_5499_; lean_object* v_err_5500_; 
v_pos_5499_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_pos_5499_);
v_err_5500_ = lean_ctor_get(v___x_5494_, 1);
lean_inc(v_err_5500_);
lean_dec_ref_known(v___x_5494_, 2);
v___y_5459_ = v___y_5474_;
v_snd_5460_ = v_snd_5479_;
v___y_5461_ = v___y_5475_;
v_pos_5462_ = v_pos_5499_;
v_err_5463_ = v_err_5500_;
goto v___jp_5458_;
}
}
}
}
}
}
else
{
v___y_5466_ = v___y_5474_;
v___y_5467_ = v_pos_5477_;
v_snd_5468_ = v_snd_5479_;
v___y_5469_ = v___y_5475_;
goto v___jp_5465_;
}
}
}
v___jp_5505_:
{
lean_object* v___x_5511_; 
lean_inc_ref(v_pos_5509_);
v___x_5511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5511_, 0, v_pos_5509_);
lean_ctor_set(v___x_5511_, 1, v_err_5510_);
v_snd_5473_ = v_snd_5506_;
v___y_5474_ = v___y_5507_;
v___y_5475_ = v___y_5508_;
v___y_5476_ = v___x_5511_;
v_pos_5477_ = v_pos_5509_;
goto v___jp_5472_;
}
v___jp_5512_:
{
lean_object* v___x_5517_; 
v___x_5517_ = lean_box(0);
v_snd_5506_ = v_snd_5514_;
v___y_5507_ = v___y_5515_;
v___y_5508_ = v___y_5516_;
v_pos_5509_ = v___y_5513_;
v_err_5510_ = v___x_5517_;
goto v___jp_5505_;
}
v___jp_5519_:
{
lean_object* v_fst_5525_; lean_object* v_snd_5526_; uint8_t v___x_5527_; 
v_fst_5525_ = lean_ctor_get(v_pos_5524_, 0);
v_snd_5526_ = lean_ctor_get(v_pos_5524_, 1);
lean_inc(v_snd_5526_);
v___x_5527_ = lean_nat_dec_eq(v_snd_5521_, v_snd_5526_);
lean_dec(v_snd_5521_);
if (v___x_5527_ == 0)
{
lean_dec(v_snd_5526_);
lean_dec_ref(v_pos_5524_);
lean_dec_ref(v___y_5522_);
lean_dec_ref(v___y_5520_);
return v___y_5523_;
}
else
{
lean_object* v___x_5528_; uint8_t v___x_5529_; 
lean_dec_ref(v___y_5523_);
v___x_5528_ = lean_string_utf8_byte_size(v_fst_5525_);
v___x_5529_ = lean_nat_dec_eq(v_snd_5526_, v___x_5528_);
if (v___x_5529_ == 0)
{
if (v___x_5527_ == 0)
{
v___y_5513_ = v_pos_5524_;
v_snd_5514_ = v_snd_5526_;
v___y_5515_ = v___y_5520_;
v___y_5516_ = v___y_5522_;
goto v___jp_5512_;
}
else
{
uint32_t v___x_5530_; uint32_t v_c_5531_; uint8_t v___x_5532_; 
v___x_5530_ = 101;
v_c_5531_ = lean_string_utf8_get_fast(v_fst_5525_, v_snd_5526_);
v___x_5532_ = lean_uint32_dec_eq(v_c_5531_, v___x_5530_);
if (v___x_5532_ == 0)
{
lean_object* v___x_5533_; 
v___x_5533_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__3);
v_snd_5506_ = v_snd_5526_;
v___y_5507_ = v___y_5520_;
v___y_5508_ = v___y_5522_;
v_pos_5509_ = v_pos_5524_;
v_err_5510_ = v___x_5533_;
goto v___jp_5505_;
}
else
{
lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5549_; 
lean_inc(v_fst_5525_);
v_isSharedCheck_5549_ = !lean_is_exclusive(v_pos_5524_);
if (v_isSharedCheck_5549_ == 0)
{
lean_object* v_unused_5550_; lean_object* v_unused_5551_; 
v_unused_5550_ = lean_ctor_get(v_pos_5524_, 1);
lean_dec(v_unused_5550_);
v_unused_5551_ = lean_ctor_get(v_pos_5524_, 0);
lean_dec(v_unused_5551_);
v___x_5535_ = v_pos_5524_;
v_isShared_5536_ = v_isSharedCheck_5549_;
goto v_resetjp_5534_;
}
else
{
lean_dec(v_pos_5524_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5549_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___x_5537_; lean_object* v_it_x27_5539_; 
v___x_5537_ = lean_string_utf8_next_fast(v_fst_5525_, v_snd_5526_);
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 1, v___x_5537_);
v_it_x27_5539_ = v___x_5535_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_fst_5525_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v___x_5537_);
v_it_x27_5539_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
lean_object* v___x_5540_; lean_object* v___x_5541_; 
v___x_5540_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__0);
v___x_5541_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(v___x_5540_, v_it_x27_5539_);
if (lean_obj_tag(v___x_5541_) == 0)
{
lean_object* v_pos_5542_; lean_object* v_res_5543_; lean_object* v___x_5544_; 
v_pos_5542_ = lean_ctor_get(v___x_5541_, 0);
lean_inc(v_pos_5542_);
v_res_5543_ = lean_ctor_get(v___x_5541_, 1);
lean_inc(v_res_5543_);
lean_dec_ref_known(v___x_5541_, 2);
v___x_5544_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(v___f_5518_, v_res_5543_, v_pos_5542_);
if (lean_obj_tag(v___x_5544_) == 0)
{
lean_dec(v_snd_5526_);
lean_dec_ref(v___y_5522_);
lean_dec_ref(v___y_5520_);
return v___x_5544_;
}
else
{
lean_object* v_pos_5545_; 
v_pos_5545_ = lean_ctor_get(v___x_5544_, 0);
lean_inc(v_pos_5545_);
v_snd_5473_ = v_snd_5526_;
v___y_5474_ = v___y_5520_;
v___y_5475_ = v___y_5522_;
v___y_5476_ = v___x_5544_;
v_pos_5477_ = v_pos_5545_;
goto v___jp_5472_;
}
}
else
{
lean_object* v_pos_5546_; lean_object* v_err_5547_; 
v_pos_5546_ = lean_ctor_get(v___x_5541_, 0);
lean_inc(v_pos_5546_);
v_err_5547_ = lean_ctor_get(v___x_5541_, 1);
lean_inc(v_err_5547_);
lean_dec_ref_known(v___x_5541_, 2);
v_snd_5506_ = v_snd_5526_;
v___y_5507_ = v___y_5520_;
v___y_5508_ = v___y_5522_;
v_pos_5509_ = v_pos_5546_;
v_err_5510_ = v_err_5547_;
goto v___jp_5505_;
}
}
}
}
}
}
else
{
v___y_5513_ = v_pos_5524_;
v_snd_5514_ = v_snd_5526_;
v___y_5515_ = v___y_5520_;
v___y_5516_ = v___y_5522_;
goto v___jp_5512_;
}
}
}
v___jp_5552_:
{
lean_object* v___x_5558_; 
lean_inc_ref(v_pos_5556_);
v___x_5558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5558_, 0, v_pos_5556_);
lean_ctor_set(v___x_5558_, 1, v_err_5557_);
v___y_5520_ = v___y_5553_;
v_snd_5521_ = v_snd_5554_;
v___y_5522_ = v___y_5555_;
v___y_5523_ = v___x_5558_;
v_pos_5524_ = v_pos_5556_;
goto v___jp_5519_;
}
v___jp_5559_:
{
lean_object* v___x_5564_; 
v___x_5564_ = lean_box(0);
v___y_5553_ = v___y_5560_;
v_snd_5554_ = v_snd_5562_;
v___y_5555_ = v___y_5563_;
v_pos_5556_ = v___y_5561_;
v_err_5557_ = v___x_5564_;
goto v___jp_5552_;
}
v___jp_5566_:
{
lean_object* v_fst_5572_; lean_object* v_snd_5573_; uint8_t v___x_5574_; 
v_fst_5572_ = lean_ctor_get(v_pos_5571_, 0);
v_snd_5573_ = lean_ctor_get(v_pos_5571_, 1);
lean_inc(v_snd_5573_);
v___x_5574_ = lean_nat_dec_eq(v___y_5567_, v_snd_5573_);
lean_dec(v___y_5567_);
if (v___x_5574_ == 0)
{
lean_dec(v_snd_5573_);
lean_dec_ref(v_pos_5571_);
lean_dec_ref(v___y_5569_);
lean_dec_ref(v___y_5568_);
return v___y_5570_;
}
else
{
lean_object* v___x_5575_; uint8_t v___x_5576_; 
lean_dec_ref(v___y_5570_);
v___x_5575_ = lean_string_utf8_byte_size(v_fst_5572_);
v___x_5576_ = lean_nat_dec_eq(v_snd_5573_, v___x_5575_);
if (v___x_5576_ == 0)
{
if (v___x_5574_ == 0)
{
v___y_5560_ = v___y_5568_;
v___y_5561_ = v_pos_5571_;
v_snd_5562_ = v_snd_5573_;
v___y_5563_ = v___y_5569_;
goto v___jp_5559_;
}
else
{
uint32_t v___x_5577_; uint32_t v_c_5578_; uint8_t v___x_5579_; 
v___x_5577_ = 69;
v_c_5578_ = lean_string_utf8_get_fast(v_fst_5572_, v_snd_5573_);
v___x_5579_ = lean_uint32_dec_eq(v_c_5578_, v___x_5577_);
if (v___x_5579_ == 0)
{
lean_object* v___x_5580_; 
v___x_5580_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__3);
v___y_5553_ = v___y_5568_;
v_snd_5554_ = v_snd_5573_;
v___y_5555_ = v___y_5569_;
v_pos_5556_ = v_pos_5571_;
v_err_5557_ = v___x_5580_;
goto v___jp_5552_;
}
else
{
lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5596_; 
lean_inc(v_fst_5572_);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_pos_5571_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; lean_object* v_unused_5598_; 
v_unused_5597_ = lean_ctor_get(v_pos_5571_, 1);
lean_dec(v_unused_5597_);
v_unused_5598_ = lean_ctor_get(v_pos_5571_, 0);
lean_dec(v_unused_5598_);
v___x_5582_ = v_pos_5571_;
v_isShared_5583_ = v_isSharedCheck_5596_;
goto v_resetjp_5581_;
}
else
{
lean_dec(v_pos_5571_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5596_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___x_5584_; lean_object* v_it_x27_5586_; 
v___x_5584_ = lean_string_utf8_next_fast(v_fst_5572_, v_snd_5573_);
if (v_isShared_5583_ == 0)
{
lean_ctor_set(v___x_5582_, 1, v___x_5584_);
v_it_x27_5586_ = v___x_5582_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_fst_5572_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v___x_5584_);
v_it_x27_5586_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
lean_object* v___x_5587_; lean_object* v___x_5588_; 
v___x_5587_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__0);
v___x_5588_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(v___x_5587_, v_it_x27_5586_);
if (lean_obj_tag(v___x_5588_) == 0)
{
lean_object* v_pos_5589_; lean_object* v_res_5590_; lean_object* v___x_5591_; 
v_pos_5589_ = lean_ctor_get(v___x_5588_, 0);
lean_inc(v_pos_5589_);
v_res_5590_ = lean_ctor_get(v___x_5588_, 1);
lean_inc(v_res_5590_);
lean_dec_ref_known(v___x_5588_, 2);
v___x_5591_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(v___f_5565_, v_res_5590_, v_pos_5589_);
if (lean_obj_tag(v___x_5591_) == 0)
{
lean_dec(v_snd_5573_);
lean_dec_ref(v___y_5569_);
lean_dec_ref(v___y_5568_);
return v___x_5591_;
}
else
{
lean_object* v_pos_5592_; 
v_pos_5592_ = lean_ctor_get(v___x_5591_, 0);
lean_inc(v_pos_5592_);
v___y_5520_ = v___y_5568_;
v_snd_5521_ = v_snd_5573_;
v___y_5522_ = v___y_5569_;
v___y_5523_ = v___x_5591_;
v_pos_5524_ = v_pos_5592_;
goto v___jp_5519_;
}
}
else
{
lean_object* v_pos_5593_; lean_object* v_err_5594_; 
v_pos_5593_ = lean_ctor_get(v___x_5588_, 0);
lean_inc(v_pos_5593_);
v_err_5594_ = lean_ctor_get(v___x_5588_, 1);
lean_inc(v_err_5594_);
lean_dec_ref_known(v___x_5588_, 2);
v___y_5553_ = v___y_5568_;
v_snd_5554_ = v_snd_5573_;
v___y_5555_ = v___y_5569_;
v_pos_5556_ = v_pos_5593_;
v_err_5557_ = v_err_5594_;
goto v___jp_5552_;
}
}
}
}
}
}
else
{
v___y_5560_ = v___y_5568_;
v___y_5561_ = v_pos_5571_;
v_snd_5562_ = v_snd_5573_;
v___y_5563_ = v___y_5569_;
goto v___jp_5559_;
}
}
}
v___jp_5599_:
{
lean_object* v___x_5605_; 
lean_inc_ref(v_pos_5603_);
v___x_5605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5605_, 0, v_pos_5603_);
lean_ctor_set(v___x_5605_, 1, v_err_5604_);
v___y_5567_ = v___y_5600_;
v___y_5568_ = v___y_5601_;
v___y_5569_ = v___y_5602_;
v___y_5570_ = v___x_5605_;
v_pos_5571_ = v_pos_5603_;
goto v___jp_5566_;
}
v___jp_5606_:
{
lean_object* v___x_5611_; 
v___x_5611_ = lean_box(0);
v___y_5600_ = v___y_5607_;
v___y_5601_ = v___y_5608_;
v___y_5602_ = v___y_5610_;
v_pos_5603_ = v___y_5609_;
v_err_5604_ = v___x_5611_;
goto v___jp_5599_;
}
v___jp_5613_:
{
lean_object* v_fst_5618_; lean_object* v_snd_5619_; uint8_t v___x_5620_; 
v_fst_5618_ = lean_ctor_get(v_pos_5617_, 0);
v_snd_5619_ = lean_ctor_get(v_pos_5617_, 1);
lean_inc(v_snd_5619_);
v___x_5620_ = lean_nat_dec_eq(v_snd_5614_, v_snd_5619_);
lean_dec(v_snd_5614_);
if (v___x_5620_ == 0)
{
lean_dec(v_snd_5619_);
lean_dec_ref(v_pos_5617_);
lean_dec_ref(v___y_5615_);
return v___y_5616_;
}
else
{
lean_object* v___x_5621_; lean_object* v___x_5622_; uint8_t v___x_5623_; 
lean_dec_ref(v___y_5616_);
v___x_5621_ = ((lean_object*)(l_Std_Time_parseModifier___closed__21));
v___x_5622_ = lean_string_utf8_byte_size(v_fst_5618_);
v___x_5623_ = lean_nat_dec_eq(v_snd_5619_, v___x_5622_);
if (v___x_5623_ == 0)
{
if (v___x_5620_ == 0)
{
v___y_5607_ = v_snd_5619_;
v___y_5608_ = v___x_5621_;
v___y_5609_ = v_pos_5617_;
v___y_5610_ = v___y_5615_;
goto v___jp_5606_;
}
else
{
uint32_t v___x_5624_; uint32_t v_c_5625_; uint8_t v___x_5626_; 
v___x_5624_ = 87;
v_c_5625_ = lean_string_utf8_get_fast(v_fst_5618_, v_snd_5619_);
v___x_5626_ = lean_uint32_dec_eq(v_c_5625_, v___x_5624_);
if (v___x_5626_ == 0)
{
lean_object* v___x_5627_; 
v___x_5627_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__3);
v___y_5600_ = v_snd_5619_;
v___y_5601_ = v___x_5621_;
v___y_5602_ = v___y_5615_;
v_pos_5603_ = v_pos_5617_;
v_err_5604_ = v___x_5627_;
goto v___jp_5599_;
}
else
{
lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5643_; 
lean_inc(v_fst_5618_);
v_isSharedCheck_5643_ = !lean_is_exclusive(v_pos_5617_);
if (v_isSharedCheck_5643_ == 0)
{
lean_object* v_unused_5644_; lean_object* v_unused_5645_; 
v_unused_5644_ = lean_ctor_get(v_pos_5617_, 1);
lean_dec(v_unused_5644_);
v_unused_5645_ = lean_ctor_get(v_pos_5617_, 0);
lean_dec(v_unused_5645_);
v___x_5629_ = v_pos_5617_;
v_isShared_5630_ = v_isSharedCheck_5643_;
goto v_resetjp_5628_;
}
else
{
lean_dec(v_pos_5617_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5643_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
lean_object* v___x_5631_; lean_object* v_it_x27_5633_; 
v___x_5631_ = lean_string_utf8_next_fast(v_fst_5618_, v_snd_5619_);
if (v_isShared_5630_ == 0)
{
lean_ctor_set(v___x_5629_, 1, v___x_5631_);
v_it_x27_5633_ = v___x_5629_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5642_; 
v_reuseFailAlloc_5642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5642_, 0, v_fst_5618_);
lean_ctor_set(v_reuseFailAlloc_5642_, 1, v___x_5631_);
v_it_x27_5633_ = v_reuseFailAlloc_5642_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
lean_object* v___x_5634_; lean_object* v___x_5635_; 
v___x_5634_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__0);
v___x_5635_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(v___x_5634_, v_it_x27_5633_);
if (lean_obj_tag(v___x_5635_) == 0)
{
lean_object* v_pos_5636_; lean_object* v_res_5637_; lean_object* v___x_5638_; 
v_pos_5636_ = lean_ctor_get(v___x_5635_, 0);
lean_inc(v_pos_5636_);
v_res_5637_ = lean_ctor_get(v___x_5635_, 1);
lean_inc(v_res_5637_);
lean_dec_ref_known(v___x_5635_, 2);
v___x_5638_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5612_, v___x_5621_, v_res_5637_, v_pos_5636_);
if (lean_obj_tag(v___x_5638_) == 0)
{
lean_dec(v_snd_5619_);
lean_dec_ref(v___y_5615_);
return v___x_5638_;
}
else
{
lean_object* v_pos_5639_; 
v_pos_5639_ = lean_ctor_get(v___x_5638_, 0);
lean_inc(v_pos_5639_);
v___y_5567_ = v_snd_5619_;
v___y_5568_ = v___x_5621_;
v___y_5569_ = v___y_5615_;
v___y_5570_ = v___x_5638_;
v_pos_5571_ = v_pos_5639_;
goto v___jp_5566_;
}
}
else
{
lean_object* v_pos_5640_; lean_object* v_err_5641_; 
v_pos_5640_ = lean_ctor_get(v___x_5635_, 0);
lean_inc(v_pos_5640_);
v_err_5641_ = lean_ctor_get(v___x_5635_, 1);
lean_inc(v_err_5641_);
lean_dec_ref_known(v___x_5635_, 2);
v___y_5600_ = v_snd_5619_;
v___y_5601_ = v___x_5621_;
v___y_5602_ = v___y_5615_;
v_pos_5603_ = v_pos_5640_;
v_err_5604_ = v_err_5641_;
goto v___jp_5599_;
}
}
}
}
}
}
else
{
v___y_5607_ = v_snd_5619_;
v___y_5608_ = v___x_5621_;
v___y_5609_ = v_pos_5617_;
v___y_5610_ = v___y_5615_;
goto v___jp_5606_;
}
}
}
v___jp_5646_:
{
lean_object* v___x_5651_; 
lean_inc_ref(v_pos_5649_);
v___x_5651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5651_, 0, v_pos_5649_);
lean_ctor_set(v___x_5651_, 1, v_err_5650_);
v_snd_5614_ = v_snd_5647_;
v___y_5615_ = v___y_5648_;
v___y_5616_ = v___x_5651_;
v_pos_5617_ = v_pos_5649_;
goto v___jp_5613_;
}
v___jp_5652_:
{
lean_object* v___x_5656_; 
v___x_5656_ = lean_box(0);
v_snd_5647_ = v_snd_5654_;
v___y_5648_ = v___y_5655_;
v_pos_5649_ = v___y_5653_;
v_err_5650_ = v___x_5656_;
goto v___jp_5646_;
}
v___jp_5658_:
{
lean_object* v_fst_5663_; lean_object* v_snd_5664_; uint8_t v___x_5665_; 
v_fst_5663_ = lean_ctor_get(v_pos_5662_, 0);
v_snd_5664_ = lean_ctor_get(v_pos_5662_, 1);
lean_inc(v_snd_5664_);
v___x_5665_ = lean_nat_dec_eq(v_snd_5659_, v_snd_5664_);
lean_dec(v_snd_5659_);
if (v___x_5665_ == 0)
{
lean_dec(v_snd_5664_);
lean_dec_ref(v_pos_5662_);
lean_dec_ref(v___y_5660_);
return v___y_5661_;
}
else
{
lean_object* v___x_5666_; uint8_t v___x_5667_; 
lean_dec_ref(v___y_5661_);
v___x_5666_ = lean_string_utf8_byte_size(v_fst_5663_);
v___x_5667_ = lean_nat_dec_eq(v_snd_5664_, v___x_5666_);
if (v___x_5667_ == 0)
{
if (v___x_5665_ == 0)
{
v___y_5653_ = v_pos_5662_;
v_snd_5654_ = v_snd_5664_;
v___y_5655_ = v___y_5660_;
goto v___jp_5652_;
}
else
{
uint32_t v___x_5668_; uint32_t v_c_5669_; uint8_t v___x_5670_; 
v___x_5668_ = 119;
v_c_5669_ = lean_string_utf8_get_fast(v_fst_5663_, v_snd_5664_);
v___x_5670_ = lean_uint32_dec_eq(v_c_5669_, v___x_5668_);
if (v___x_5670_ == 0)
{
lean_object* v___x_5671_; 
v___x_5671_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__3);
v_snd_5647_ = v_snd_5664_;
v___y_5648_ = v___y_5660_;
v_pos_5649_ = v_pos_5662_;
v_err_5650_ = v___x_5671_;
goto v___jp_5646_;
}
else
{
lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5687_; 
lean_inc(v_fst_5663_);
v_isSharedCheck_5687_ = !lean_is_exclusive(v_pos_5662_);
if (v_isSharedCheck_5687_ == 0)
{
lean_object* v_unused_5688_; lean_object* v_unused_5689_; 
v_unused_5688_ = lean_ctor_get(v_pos_5662_, 1);
lean_dec(v_unused_5688_);
v_unused_5689_ = lean_ctor_get(v_pos_5662_, 0);
lean_dec(v_unused_5689_);
v___x_5673_ = v_pos_5662_;
v_isShared_5674_ = v_isSharedCheck_5687_;
goto v_resetjp_5672_;
}
else
{
lean_dec(v_pos_5662_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5687_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
lean_object* v___x_5675_; lean_object* v_it_x27_5677_; 
v___x_5675_ = lean_string_utf8_next_fast(v_fst_5663_, v_snd_5664_);
if (v_isShared_5674_ == 0)
{
lean_ctor_set(v___x_5673_, 1, v___x_5675_);
v_it_x27_5677_ = v___x_5673_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_fst_5663_);
lean_ctor_set(v_reuseFailAlloc_5686_, 1, v___x_5675_);
v_it_x27_5677_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
lean_object* v___x_5678_; lean_object* v___x_5679_; 
v___x_5678_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__0);
v___x_5679_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(v___x_5678_, v_it_x27_5677_);
if (lean_obj_tag(v___x_5679_) == 0)
{
lean_object* v_pos_5680_; lean_object* v_res_5681_; lean_object* v___x_5682_; 
v_pos_5680_ = lean_ctor_get(v___x_5679_, 0);
lean_inc(v_pos_5680_);
v_res_5681_ = lean_ctor_get(v___x_5679_, 1);
lean_inc(v_res_5681_);
lean_dec_ref_known(v___x_5679_, 2);
lean_inc_ref(v___y_5660_);
v___x_5682_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5657_, v___y_5660_, v_res_5681_, v_pos_5680_);
if (lean_obj_tag(v___x_5682_) == 0)
{
lean_dec(v_snd_5664_);
lean_dec_ref(v___y_5660_);
return v___x_5682_;
}
else
{
lean_object* v_pos_5683_; 
v_pos_5683_ = lean_ctor_get(v___x_5682_, 0);
lean_inc(v_pos_5683_);
v_snd_5614_ = v_snd_5664_;
v___y_5615_ = v___y_5660_;
v___y_5616_ = v___x_5682_;
v_pos_5617_ = v_pos_5683_;
goto v___jp_5613_;
}
}
else
{
lean_object* v_pos_5684_; lean_object* v_err_5685_; 
v_pos_5684_ = lean_ctor_get(v___x_5679_, 0);
lean_inc(v_pos_5684_);
v_err_5685_ = lean_ctor_get(v___x_5679_, 1);
lean_inc(v_err_5685_);
lean_dec_ref_known(v___x_5679_, 2);
v_snd_5647_ = v_snd_5664_;
v___y_5648_ = v___y_5660_;
v_pos_5649_ = v_pos_5684_;
v_err_5650_ = v_err_5685_;
goto v___jp_5646_;
}
}
}
}
}
}
else
{
v___y_5653_ = v_pos_5662_;
v_snd_5654_ = v_snd_5664_;
v___y_5655_ = v___y_5660_;
goto v___jp_5652_;
}
}
}
v___jp_5690_:
{
lean_object* v___x_5695_; 
lean_inc_ref(v_pos_5693_);
v___x_5695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5695_, 0, v_pos_5693_);
lean_ctor_set(v___x_5695_, 1, v_err_5694_);
v_snd_5659_ = v_snd_5691_;
v___y_5660_ = v___y_5692_;
v___y_5661_ = v___x_5695_;
v_pos_5662_ = v_pos_5693_;
goto v___jp_5658_;
}
v___jp_5696_:
{
lean_object* v___x_5700_; 
v___x_5700_ = lean_box(0);
v_snd_5691_ = v_snd_5698_;
v___y_5692_ = v___y_5699_;
v_pos_5693_ = v___y_5697_;
v_err_5694_ = v___x_5700_;
goto v___jp_5690_;
}
v___jp_5702_:
{
lean_object* v_fst_5707_; lean_object* v_snd_5708_; uint8_t v___x_5709_; 
v_fst_5707_ = lean_ctor_get(v_pos_5706_, 0);
v_snd_5708_ = lean_ctor_get(v_pos_5706_, 1);
lean_inc(v_snd_5708_);
v___x_5709_ = lean_nat_dec_eq(v_snd_5703_, v_snd_5708_);
lean_dec(v_snd_5703_);
if (v___x_5709_ == 0)
{
lean_dec(v_snd_5708_);
lean_dec_ref(v_pos_5706_);
lean_dec_ref(v___y_5704_);
return v___y_5705_;
}
else
{
lean_object* v___x_5710_; uint8_t v___x_5711_; 
lean_dec_ref(v___y_5705_);
v___x_5710_ = lean_string_utf8_byte_size(v_fst_5707_);
v___x_5711_ = lean_nat_dec_eq(v_snd_5708_, v___x_5710_);
if (v___x_5711_ == 0)
{
if (v___x_5709_ == 0)
{
v___y_5697_ = v_pos_5706_;
v_snd_5698_ = v_snd_5708_;
v___y_5699_ = v___y_5704_;
goto v___jp_5696_;
}
else
{
uint32_t v___x_5712_; uint32_t v_c_5713_; uint8_t v___x_5714_; 
v___x_5712_ = 113;
v_c_5713_ = lean_string_utf8_get_fast(v_fst_5707_, v_snd_5708_);
v___x_5714_ = lean_uint32_dec_eq(v_c_5713_, v___x_5712_);
if (v___x_5714_ == 0)
{
lean_object* v___x_5715_; 
v___x_5715_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__3);
v_snd_5691_ = v_snd_5708_;
v___y_5692_ = v___y_5704_;
v_pos_5693_ = v_pos_5706_;
v_err_5694_ = v___x_5715_;
goto v___jp_5690_;
}
else
{
lean_object* v___x_5717_; uint8_t v_isShared_5718_; uint8_t v_isSharedCheck_5731_; 
lean_inc(v_fst_5707_);
v_isSharedCheck_5731_ = !lean_is_exclusive(v_pos_5706_);
if (v_isSharedCheck_5731_ == 0)
{
lean_object* v_unused_5732_; lean_object* v_unused_5733_; 
v_unused_5732_ = lean_ctor_get(v_pos_5706_, 1);
lean_dec(v_unused_5732_);
v_unused_5733_ = lean_ctor_get(v_pos_5706_, 0);
lean_dec(v_unused_5733_);
v___x_5717_ = v_pos_5706_;
v_isShared_5718_ = v_isSharedCheck_5731_;
goto v_resetjp_5716_;
}
else
{
lean_dec(v_pos_5706_);
v___x_5717_ = lean_box(0);
v_isShared_5718_ = v_isSharedCheck_5731_;
goto v_resetjp_5716_;
}
v_resetjp_5716_:
{
lean_object* v___x_5719_; lean_object* v_it_x27_5721_; 
v___x_5719_ = lean_string_utf8_next_fast(v_fst_5707_, v_snd_5708_);
if (v_isShared_5718_ == 0)
{
lean_ctor_set(v___x_5717_, 1, v___x_5719_);
v_it_x27_5721_ = v___x_5717_;
goto v_reusejp_5720_;
}
else
{
lean_object* v_reuseFailAlloc_5730_; 
v_reuseFailAlloc_5730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5730_, 0, v_fst_5707_);
lean_ctor_set(v_reuseFailAlloc_5730_, 1, v___x_5719_);
v_it_x27_5721_ = v_reuseFailAlloc_5730_;
goto v_reusejp_5720_;
}
v_reusejp_5720_:
{
lean_object* v___x_5722_; lean_object* v___x_5723_; 
v___x_5722_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__0);
v___x_5723_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(v___x_5722_, v_it_x27_5721_);
if (lean_obj_tag(v___x_5723_) == 0)
{
lean_object* v_pos_5724_; lean_object* v_res_5725_; lean_object* v___x_5726_; 
v_pos_5724_ = lean_ctor_get(v___x_5723_, 0);
lean_inc(v_pos_5724_);
v_res_5725_ = lean_ctor_get(v___x_5723_, 1);
lean_inc(v_res_5725_);
lean_dec_ref_known(v___x_5723_, 2);
v___x_5726_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5701_, v_res_5725_, v_pos_5724_);
if (lean_obj_tag(v___x_5726_) == 0)
{
lean_dec(v_snd_5708_);
lean_dec_ref(v___y_5704_);
return v___x_5726_;
}
else
{
lean_object* v_pos_5727_; 
v_pos_5727_ = lean_ctor_get(v___x_5726_, 0);
lean_inc(v_pos_5727_);
v_snd_5659_ = v_snd_5708_;
v___y_5660_ = v___y_5704_;
v___y_5661_ = v___x_5726_;
v_pos_5662_ = v_pos_5727_;
goto v___jp_5658_;
}
}
else
{
lean_object* v_pos_5728_; lean_object* v_err_5729_; 
v_pos_5728_ = lean_ctor_get(v___x_5723_, 0);
lean_inc(v_pos_5728_);
v_err_5729_ = lean_ctor_get(v___x_5723_, 1);
lean_inc(v_err_5729_);
lean_dec_ref_known(v___x_5723_, 2);
v_snd_5691_ = v_snd_5708_;
v___y_5692_ = v___y_5704_;
v_pos_5693_ = v_pos_5728_;
v_err_5694_ = v_err_5729_;
goto v___jp_5690_;
}
}
}
}
}
}
else
{
v___y_5697_ = v_pos_5706_;
v_snd_5698_ = v_snd_5708_;
v___y_5699_ = v___y_5704_;
goto v___jp_5696_;
}
}
}
v___jp_5734_:
{
lean_object* v___x_5739_; 
lean_inc_ref(v_pos_5737_);
v___x_5739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5739_, 0, v_pos_5737_);
lean_ctor_set(v___x_5739_, 1, v_err_5738_);
v_snd_5703_ = v_snd_5735_;
v___y_5704_ = v___y_5736_;
v___y_5705_ = v___x_5739_;
v_pos_5706_ = v_pos_5737_;
goto v___jp_5702_;
}
v___jp_5740_:
{
lean_object* v___x_5744_; 
v___x_5744_ = lean_box(0);
v_snd_5735_ = v_snd_5742_;
v___y_5736_ = v___y_5743_;
v_pos_5737_ = v___y_5741_;
v_err_5738_ = v___x_5744_;
goto v___jp_5734_;
}
v___jp_5746_:
{
lean_object* v_fst_5751_; lean_object* v_snd_5752_; uint8_t v___x_5753_; 
v_fst_5751_ = lean_ctor_get(v_pos_5750_, 0);
v_snd_5752_ = lean_ctor_get(v_pos_5750_, 1);
lean_inc(v_snd_5752_);
v___x_5753_ = lean_nat_dec_eq(v___y_5747_, v_snd_5752_);
lean_dec(v___y_5747_);
if (v___x_5753_ == 0)
{
lean_dec(v_snd_5752_);
lean_dec_ref(v_pos_5750_);
lean_dec_ref(v___y_5748_);
return v___y_5749_;
}
else
{
lean_object* v___x_5754_; uint8_t v___x_5755_; 
lean_dec_ref(v___y_5749_);
v___x_5754_ = lean_string_utf8_byte_size(v_fst_5751_);
v___x_5755_ = lean_nat_dec_eq(v_snd_5752_, v___x_5754_);
if (v___x_5755_ == 0)
{
if (v___x_5753_ == 0)
{
v___y_5741_ = v_pos_5750_;
v_snd_5742_ = v_snd_5752_;
v___y_5743_ = v___y_5748_;
goto v___jp_5740_;
}
else
{
uint32_t v___x_5756_; uint32_t v_c_5757_; uint8_t v___x_5758_; 
v___x_5756_ = 81;
v_c_5757_ = lean_string_utf8_get_fast(v_fst_5751_, v_snd_5752_);
v___x_5758_ = lean_uint32_dec_eq(v_c_5757_, v___x_5756_);
if (v___x_5758_ == 0)
{
lean_object* v___x_5759_; 
v___x_5759_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__3);
v_snd_5735_ = v_snd_5752_;
v___y_5736_ = v___y_5748_;
v_pos_5737_ = v_pos_5750_;
v_err_5738_ = v___x_5759_;
goto v___jp_5734_;
}
else
{
lean_object* v___x_5761_; uint8_t v_isShared_5762_; uint8_t v_isSharedCheck_5775_; 
lean_inc(v_fst_5751_);
v_isSharedCheck_5775_ = !lean_is_exclusive(v_pos_5750_);
if (v_isSharedCheck_5775_ == 0)
{
lean_object* v_unused_5776_; lean_object* v_unused_5777_; 
v_unused_5776_ = lean_ctor_get(v_pos_5750_, 1);
lean_dec(v_unused_5776_);
v_unused_5777_ = lean_ctor_get(v_pos_5750_, 0);
lean_dec(v_unused_5777_);
v___x_5761_ = v_pos_5750_;
v_isShared_5762_ = v_isSharedCheck_5775_;
goto v_resetjp_5760_;
}
else
{
lean_dec(v_pos_5750_);
v___x_5761_ = lean_box(0);
v_isShared_5762_ = v_isSharedCheck_5775_;
goto v_resetjp_5760_;
}
v_resetjp_5760_:
{
lean_object* v___x_5763_; lean_object* v_it_x27_5765_; 
v___x_5763_ = lean_string_utf8_next_fast(v_fst_5751_, v_snd_5752_);
if (v_isShared_5762_ == 0)
{
lean_ctor_set(v___x_5761_, 1, v___x_5763_);
v_it_x27_5765_ = v___x_5761_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_fst_5751_);
lean_ctor_set(v_reuseFailAlloc_5774_, 1, v___x_5763_);
v_it_x27_5765_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
lean_object* v___x_5766_; lean_object* v___x_5767_; 
v___x_5766_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__0);
v___x_5767_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(v___x_5766_, v_it_x27_5765_);
if (lean_obj_tag(v___x_5767_) == 0)
{
lean_object* v_pos_5768_; lean_object* v_res_5769_; lean_object* v___x_5770_; 
v_pos_5768_ = lean_ctor_get(v___x_5767_, 0);
lean_inc(v_pos_5768_);
v_res_5769_ = lean_ctor_get(v___x_5767_, 1);
lean_inc(v_res_5769_);
lean_dec_ref_known(v___x_5767_, 2);
v___x_5770_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5745_, v_res_5769_, v_pos_5768_);
if (lean_obj_tag(v___x_5770_) == 0)
{
lean_dec(v_snd_5752_);
lean_dec_ref(v___y_5748_);
return v___x_5770_;
}
else
{
lean_object* v_pos_5771_; 
v_pos_5771_ = lean_ctor_get(v___x_5770_, 0);
lean_inc(v_pos_5771_);
v_snd_5703_ = v_snd_5752_;
v___y_5704_ = v___y_5748_;
v___y_5705_ = v___x_5770_;
v_pos_5706_ = v_pos_5771_;
goto v___jp_5702_;
}
}
else
{
lean_object* v_pos_5772_; lean_object* v_err_5773_; 
v_pos_5772_ = lean_ctor_get(v___x_5767_, 0);
lean_inc(v_pos_5772_);
v_err_5773_ = lean_ctor_get(v___x_5767_, 1);
lean_inc(v_err_5773_);
lean_dec_ref_known(v___x_5767_, 2);
v_snd_5735_ = v_snd_5752_;
v___y_5736_ = v___y_5748_;
v_pos_5737_ = v_pos_5772_;
v_err_5738_ = v_err_5773_;
goto v___jp_5734_;
}
}
}
}
}
}
else
{
v___y_5741_ = v_pos_5750_;
v_snd_5742_ = v_snd_5752_;
v___y_5743_ = v___y_5748_;
goto v___jp_5740_;
}
}
}
v___jp_5778_:
{
lean_object* v___x_5783_; 
lean_inc_ref(v_pos_5781_);
v___x_5783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5783_, 0, v_pos_5781_);
lean_ctor_set(v___x_5783_, 1, v_err_5782_);
v___y_5747_ = v___y_5780_;
v___y_5748_ = v___y_5779_;
v___y_5749_ = v___x_5783_;
v_pos_5750_ = v_pos_5781_;
goto v___jp_5746_;
}
v___jp_5784_:
{
lean_object* v___x_5788_; 
v___x_5788_ = lean_box(0);
v___y_5779_ = v___y_5787_;
v___y_5780_ = v___y_5786_;
v_pos_5781_ = v___y_5785_;
v_err_5782_ = v___x_5788_;
goto v___jp_5778_;
}
v___jp_5790_:
{
lean_object* v_fst_5794_; lean_object* v_snd_5795_; uint8_t v___x_5796_; 
v_fst_5794_ = lean_ctor_get(v_pos_5793_, 0);
v_snd_5795_ = lean_ctor_get(v_pos_5793_, 1);
lean_inc(v_snd_5795_);
v___x_5796_ = lean_nat_dec_eq(v_snd_5791_, v_snd_5795_);
lean_dec(v_snd_5791_);
if (v___x_5796_ == 0)
{
lean_dec(v_snd_5795_);
lean_dec_ref(v_pos_5793_);
return v___y_5792_;
}
else
{
lean_object* v___x_5797_; lean_object* v___x_5798_; uint8_t v___x_5799_; 
lean_dec_ref(v___y_5792_);
v___x_5797_ = ((lean_object*)(l_Std_Time_parseModifier___closed__26));
v___x_5798_ = lean_string_utf8_byte_size(v_fst_5794_);
v___x_5799_ = lean_nat_dec_eq(v_snd_5795_, v___x_5798_);
if (v___x_5799_ == 0)
{
if (v___x_5796_ == 0)
{
v___y_5785_ = v_pos_5793_;
v___y_5786_ = v_snd_5795_;
v___y_5787_ = v___x_5797_;
goto v___jp_5784_;
}
else
{
uint32_t v___x_5800_; uint32_t v_c_5801_; uint8_t v___x_5802_; 
v___x_5800_ = 100;
v_c_5801_ = lean_string_utf8_get_fast(v_fst_5794_, v_snd_5795_);
v___x_5802_ = lean_uint32_dec_eq(v_c_5801_, v___x_5800_);
if (v___x_5802_ == 0)
{
lean_object* v___x_5803_; 
v___x_5803_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__3);
v___y_5779_ = v___x_5797_;
v___y_5780_ = v_snd_5795_;
v_pos_5781_ = v_pos_5793_;
v_err_5782_ = v___x_5803_;
goto v___jp_5778_;
}
else
{
lean_object* v___x_5805_; uint8_t v_isShared_5806_; uint8_t v_isSharedCheck_5819_; 
lean_inc(v_fst_5794_);
v_isSharedCheck_5819_ = !lean_is_exclusive(v_pos_5793_);
if (v_isSharedCheck_5819_ == 0)
{
lean_object* v_unused_5820_; lean_object* v_unused_5821_; 
v_unused_5820_ = lean_ctor_get(v_pos_5793_, 1);
lean_dec(v_unused_5820_);
v_unused_5821_ = lean_ctor_get(v_pos_5793_, 0);
lean_dec(v_unused_5821_);
v___x_5805_ = v_pos_5793_;
v_isShared_5806_ = v_isSharedCheck_5819_;
goto v_resetjp_5804_;
}
else
{
lean_dec(v_pos_5793_);
v___x_5805_ = lean_box(0);
v_isShared_5806_ = v_isSharedCheck_5819_;
goto v_resetjp_5804_;
}
v_resetjp_5804_:
{
lean_object* v___x_5807_; lean_object* v_it_x27_5809_; 
v___x_5807_ = lean_string_utf8_next_fast(v_fst_5794_, v_snd_5795_);
if (v_isShared_5806_ == 0)
{
lean_ctor_set(v___x_5805_, 1, v___x_5807_);
v_it_x27_5809_ = v___x_5805_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_fst_5794_);
lean_ctor_set(v_reuseFailAlloc_5818_, 1, v___x_5807_);
v_it_x27_5809_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5808_;
}
v_reusejp_5808_:
{
lean_object* v___x_5810_; lean_object* v___x_5811_; 
v___x_5810_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__0);
v___x_5811_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(v___x_5810_, v_it_x27_5809_);
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v_pos_5812_; lean_object* v_res_5813_; lean_object* v___x_5814_; 
v_pos_5812_ = lean_ctor_get(v___x_5811_, 0);
lean_inc(v_pos_5812_);
v_res_5813_ = lean_ctor_get(v___x_5811_, 1);
lean_inc(v_res_5813_);
lean_dec_ref_known(v___x_5811_, 2);
v___x_5814_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5789_, v___x_5797_, v_res_5813_, v_pos_5812_);
if (lean_obj_tag(v___x_5814_) == 0)
{
lean_dec(v_snd_5795_);
return v___x_5814_;
}
else
{
lean_object* v_pos_5815_; 
v_pos_5815_ = lean_ctor_get(v___x_5814_, 0);
lean_inc(v_pos_5815_);
v___y_5747_ = v_snd_5795_;
v___y_5748_ = v___x_5797_;
v___y_5749_ = v___x_5814_;
v_pos_5750_ = v_pos_5815_;
goto v___jp_5746_;
}
}
else
{
lean_object* v_pos_5816_; lean_object* v_err_5817_; 
v_pos_5816_ = lean_ctor_get(v___x_5811_, 0);
lean_inc(v_pos_5816_);
v_err_5817_ = lean_ctor_get(v___x_5811_, 1);
lean_inc(v_err_5817_);
lean_dec_ref_known(v___x_5811_, 2);
v___y_5779_ = v___x_5797_;
v___y_5780_ = v_snd_5795_;
v_pos_5781_ = v_pos_5816_;
v_err_5782_ = v_err_5817_;
goto v___jp_5778_;
}
}
}
}
}
}
else
{
v___y_5785_ = v_pos_5793_;
v___y_5786_ = v_snd_5795_;
v___y_5787_ = v___x_5797_;
goto v___jp_5784_;
}
}
}
v___jp_5822_:
{
lean_object* v___x_5826_; 
lean_inc_ref(v_pos_5824_);
v___x_5826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5826_, 0, v_pos_5824_);
lean_ctor_set(v___x_5826_, 1, v_err_5825_);
v_snd_5791_ = v_snd_5823_;
v___y_5792_ = v___x_5826_;
v_pos_5793_ = v_pos_5824_;
goto v___jp_5790_;
}
v___jp_5827_:
{
lean_object* v___x_5830_; 
v___x_5830_ = lean_box(0);
v_snd_5823_ = v_snd_5829_;
v_pos_5824_ = v___y_5828_;
v_err_5825_ = v___x_5830_;
goto v___jp_5822_;
}
v___jp_5832_:
{
lean_object* v_fst_5836_; lean_object* v_snd_5837_; uint8_t v___x_5838_; 
v_fst_5836_ = lean_ctor_get(v_pos_5835_, 0);
v_snd_5837_ = lean_ctor_get(v_pos_5835_, 1);
lean_inc(v_snd_5837_);
v___x_5838_ = lean_nat_dec_eq(v_snd_5833_, v_snd_5837_);
lean_dec(v_snd_5833_);
if (v___x_5838_ == 0)
{
lean_dec(v_snd_5837_);
lean_dec_ref(v_pos_5835_);
return v___y_5834_;
}
else
{
lean_object* v___x_5839_; uint8_t v___x_5840_; 
lean_dec_ref(v___y_5834_);
v___x_5839_ = lean_string_utf8_byte_size(v_fst_5836_);
v___x_5840_ = lean_nat_dec_eq(v_snd_5837_, v___x_5839_);
if (v___x_5840_ == 0)
{
if (v___x_5838_ == 0)
{
v___y_5828_ = v_pos_5835_;
v_snd_5829_ = v_snd_5837_;
goto v___jp_5827_;
}
else
{
uint32_t v___x_5841_; uint32_t v_c_5842_; uint8_t v___x_5843_; 
v___x_5841_ = 76;
v_c_5842_ = lean_string_utf8_get_fast(v_fst_5836_, v_snd_5837_);
v___x_5843_ = lean_uint32_dec_eq(v_c_5842_, v___x_5841_);
if (v___x_5843_ == 0)
{
lean_object* v___x_5844_; 
v___x_5844_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__3);
v_snd_5823_ = v_snd_5837_;
v_pos_5824_ = v_pos_5835_;
v_err_5825_ = v___x_5844_;
goto v___jp_5822_;
}
else
{
lean_object* v___x_5846_; uint8_t v_isShared_5847_; uint8_t v_isSharedCheck_5860_; 
lean_inc(v_fst_5836_);
v_isSharedCheck_5860_ = !lean_is_exclusive(v_pos_5835_);
if (v_isSharedCheck_5860_ == 0)
{
lean_object* v_unused_5861_; lean_object* v_unused_5862_; 
v_unused_5861_ = lean_ctor_get(v_pos_5835_, 1);
lean_dec(v_unused_5861_);
v_unused_5862_ = lean_ctor_get(v_pos_5835_, 0);
lean_dec(v_unused_5862_);
v___x_5846_ = v_pos_5835_;
v_isShared_5847_ = v_isSharedCheck_5860_;
goto v_resetjp_5845_;
}
else
{
lean_dec(v_pos_5835_);
v___x_5846_ = lean_box(0);
v_isShared_5847_ = v_isSharedCheck_5860_;
goto v_resetjp_5845_;
}
v_resetjp_5845_:
{
lean_object* v___x_5848_; lean_object* v_it_x27_5850_; 
v___x_5848_ = lean_string_utf8_next_fast(v_fst_5836_, v_snd_5837_);
if (v_isShared_5847_ == 0)
{
lean_ctor_set(v___x_5846_, 1, v___x_5848_);
v_it_x27_5850_ = v___x_5846_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_fst_5836_);
lean_ctor_set(v_reuseFailAlloc_5859_, 1, v___x_5848_);
v_it_x27_5850_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5851_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__0);
v___x_5852_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(v___x_5851_, v_it_x27_5850_);
if (lean_obj_tag(v___x_5852_) == 0)
{
lean_object* v_pos_5853_; lean_object* v_res_5854_; lean_object* v___x_5855_; 
v_pos_5853_ = lean_ctor_get(v___x_5852_, 0);
lean_inc(v_pos_5853_);
v_res_5854_ = lean_ctor_get(v___x_5852_, 1);
lean_inc(v_res_5854_);
lean_dec_ref_known(v___x_5852_, 2);
v___x_5855_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5831_, v_res_5854_, v_pos_5853_);
if (lean_obj_tag(v___x_5855_) == 0)
{
lean_dec(v_snd_5837_);
return v___x_5855_;
}
else
{
lean_object* v_pos_5856_; 
v_pos_5856_ = lean_ctor_get(v___x_5855_, 0);
lean_inc(v_pos_5856_);
v_snd_5791_ = v_snd_5837_;
v___y_5792_ = v___x_5855_;
v_pos_5793_ = v_pos_5856_;
goto v___jp_5790_;
}
}
else
{
lean_object* v_pos_5857_; lean_object* v_err_5858_; 
v_pos_5857_ = lean_ctor_get(v___x_5852_, 0);
lean_inc(v_pos_5857_);
v_err_5858_ = lean_ctor_get(v___x_5852_, 1);
lean_inc(v_err_5858_);
lean_dec_ref_known(v___x_5852_, 2);
v_snd_5823_ = v_snd_5837_;
v_pos_5824_ = v_pos_5857_;
v_err_5825_ = v_err_5858_;
goto v___jp_5822_;
}
}
}
}
}
}
else
{
v___y_5828_ = v_pos_5835_;
v_snd_5829_ = v_snd_5837_;
goto v___jp_5827_;
}
}
}
v___jp_5863_:
{
lean_object* v___x_5867_; 
lean_inc_ref(v_pos_5865_);
v___x_5867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5867_, 0, v_pos_5865_);
lean_ctor_set(v___x_5867_, 1, v_err_5866_);
v_snd_5833_ = v_snd_5864_;
v___y_5834_ = v___x_5867_;
v_pos_5835_ = v_pos_5865_;
goto v___jp_5832_;
}
v___jp_5868_:
{
lean_object* v___x_5871_; 
v___x_5871_ = lean_box(0);
v_snd_5864_ = v_snd_5870_;
v_pos_5865_ = v___y_5869_;
v_err_5866_ = v___x_5871_;
goto v___jp_5863_;
}
v___jp_5873_:
{
lean_object* v_fst_5877_; lean_object* v_snd_5878_; uint8_t v___x_5879_; 
v_fst_5877_ = lean_ctor_get(v_pos_5876_, 0);
v_snd_5878_ = lean_ctor_get(v_pos_5876_, 1);
lean_inc(v_snd_5878_);
v___x_5879_ = lean_nat_dec_eq(v_snd_5874_, v_snd_5878_);
lean_dec(v_snd_5874_);
if (v___x_5879_ == 0)
{
lean_dec(v_snd_5878_);
lean_dec_ref(v_pos_5876_);
return v___y_5875_;
}
else
{
lean_object* v___x_5880_; uint8_t v___x_5881_; 
lean_dec_ref(v___y_5875_);
v___x_5880_ = lean_string_utf8_byte_size(v_fst_5877_);
v___x_5881_ = lean_nat_dec_eq(v_snd_5878_, v___x_5880_);
if (v___x_5881_ == 0)
{
if (v___x_5879_ == 0)
{
v___y_5869_ = v_pos_5876_;
v_snd_5870_ = v_snd_5878_;
goto v___jp_5868_;
}
else
{
uint32_t v___x_5882_; uint32_t v_c_5883_; uint8_t v___x_5884_; 
v___x_5882_ = 77;
v_c_5883_ = lean_string_utf8_get_fast(v_fst_5877_, v_snd_5878_);
v___x_5884_ = lean_uint32_dec_eq(v_c_5883_, v___x_5882_);
if (v___x_5884_ == 0)
{
lean_object* v___x_5885_; 
v___x_5885_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__3);
v_snd_5864_ = v_snd_5878_;
v_pos_5865_ = v_pos_5876_;
v_err_5866_ = v___x_5885_;
goto v___jp_5863_;
}
else
{
lean_object* v___x_5887_; uint8_t v_isShared_5888_; uint8_t v_isSharedCheck_5901_; 
lean_inc(v_fst_5877_);
v_isSharedCheck_5901_ = !lean_is_exclusive(v_pos_5876_);
if (v_isSharedCheck_5901_ == 0)
{
lean_object* v_unused_5902_; lean_object* v_unused_5903_; 
v_unused_5902_ = lean_ctor_get(v_pos_5876_, 1);
lean_dec(v_unused_5902_);
v_unused_5903_ = lean_ctor_get(v_pos_5876_, 0);
lean_dec(v_unused_5903_);
v___x_5887_ = v_pos_5876_;
v_isShared_5888_ = v_isSharedCheck_5901_;
goto v_resetjp_5886_;
}
else
{
lean_dec(v_pos_5876_);
v___x_5887_ = lean_box(0);
v_isShared_5888_ = v_isSharedCheck_5901_;
goto v_resetjp_5886_;
}
v_resetjp_5886_:
{
lean_object* v___x_5889_; lean_object* v_it_x27_5891_; 
v___x_5889_ = lean_string_utf8_next_fast(v_fst_5877_, v_snd_5878_);
if (v_isShared_5888_ == 0)
{
lean_ctor_set(v___x_5887_, 1, v___x_5889_);
v_it_x27_5891_ = v___x_5887_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_5900_; 
v_reuseFailAlloc_5900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5900_, 0, v_fst_5877_);
lean_ctor_set(v_reuseFailAlloc_5900_, 1, v___x_5889_);
v_it_x27_5891_ = v_reuseFailAlloc_5900_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
lean_object* v___x_5892_; lean_object* v___x_5893_; 
v___x_5892_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__0);
v___x_5893_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(v___x_5892_, v_it_x27_5891_);
if (lean_obj_tag(v___x_5893_) == 0)
{
lean_object* v_pos_5894_; lean_object* v_res_5895_; lean_object* v___x_5896_; 
v_pos_5894_ = lean_ctor_get(v___x_5893_, 0);
lean_inc(v_pos_5894_);
v_res_5895_ = lean_ctor_get(v___x_5893_, 1);
lean_inc(v_res_5895_);
lean_dec_ref_known(v___x_5893_, 2);
v___x_5896_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5872_, v_res_5895_, v_pos_5894_);
if (lean_obj_tag(v___x_5896_) == 0)
{
lean_dec(v_snd_5878_);
return v___x_5896_;
}
else
{
lean_object* v_pos_5897_; 
v_pos_5897_ = lean_ctor_get(v___x_5896_, 0);
lean_inc(v_pos_5897_);
v_snd_5833_ = v_snd_5878_;
v___y_5834_ = v___x_5896_;
v_pos_5835_ = v_pos_5897_;
goto v___jp_5832_;
}
}
else
{
lean_object* v_pos_5898_; lean_object* v_err_5899_; 
v_pos_5898_ = lean_ctor_get(v___x_5893_, 0);
lean_inc(v_pos_5898_);
v_err_5899_ = lean_ctor_get(v___x_5893_, 1);
lean_inc(v_err_5899_);
lean_dec_ref_known(v___x_5893_, 2);
v_snd_5864_ = v_snd_5878_;
v_pos_5865_ = v_pos_5898_;
v_err_5866_ = v_err_5899_;
goto v___jp_5863_;
}
}
}
}
}
}
else
{
v___y_5869_ = v_pos_5876_;
v_snd_5870_ = v_snd_5878_;
goto v___jp_5868_;
}
}
}
v___jp_5904_:
{
lean_object* v___x_5908_; 
lean_inc_ref(v_pos_5906_);
v___x_5908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5908_, 0, v_pos_5906_);
lean_ctor_set(v___x_5908_, 1, v_err_5907_);
v_snd_5874_ = v_snd_5905_;
v___y_5875_ = v___x_5908_;
v_pos_5876_ = v_pos_5906_;
goto v___jp_5873_;
}
v___jp_5909_:
{
lean_object* v___x_5912_; 
v___x_5912_ = lean_box(0);
v_snd_5905_ = v_snd_5911_;
v_pos_5906_ = v___y_5910_;
v_err_5907_ = v___x_5912_;
goto v___jp_5904_;
}
v___jp_5914_:
{
lean_object* v_fst_5918_; lean_object* v_snd_5919_; uint8_t v___x_5920_; 
v_fst_5918_ = lean_ctor_get(v_pos_5917_, 0);
v_snd_5919_ = lean_ctor_get(v_pos_5917_, 1);
lean_inc(v_snd_5919_);
v___x_5920_ = lean_nat_dec_eq(v_snd_5915_, v_snd_5919_);
lean_dec(v_snd_5915_);
if (v___x_5920_ == 0)
{
lean_dec(v_snd_5919_);
lean_dec_ref(v_pos_5917_);
return v___y_5916_;
}
else
{
lean_object* v___x_5921_; uint8_t v___x_5922_; 
lean_dec_ref(v___y_5916_);
v___x_5921_ = lean_string_utf8_byte_size(v_fst_5918_);
v___x_5922_ = lean_nat_dec_eq(v_snd_5919_, v___x_5921_);
if (v___x_5922_ == 0)
{
if (v___x_5920_ == 0)
{
v___y_5910_ = v_pos_5917_;
v_snd_5911_ = v_snd_5919_;
goto v___jp_5909_;
}
else
{
uint32_t v___x_5923_; uint32_t v_c_5924_; uint8_t v___x_5925_; 
v___x_5923_ = 68;
v_c_5924_ = lean_string_utf8_get_fast(v_fst_5918_, v_snd_5919_);
v___x_5925_ = lean_uint32_dec_eq(v_c_5924_, v___x_5923_);
if (v___x_5925_ == 0)
{
lean_object* v___x_5926_; 
v___x_5926_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__3);
v_snd_5905_ = v_snd_5919_;
v_pos_5906_ = v_pos_5917_;
v_err_5907_ = v___x_5926_;
goto v___jp_5904_;
}
else
{
lean_object* v___x_5928_; uint8_t v_isShared_5929_; uint8_t v_isSharedCheck_5943_; 
lean_inc(v_fst_5918_);
v_isSharedCheck_5943_ = !lean_is_exclusive(v_pos_5917_);
if (v_isSharedCheck_5943_ == 0)
{
lean_object* v_unused_5944_; lean_object* v_unused_5945_; 
v_unused_5944_ = lean_ctor_get(v_pos_5917_, 1);
lean_dec(v_unused_5944_);
v_unused_5945_ = lean_ctor_get(v_pos_5917_, 0);
lean_dec(v_unused_5945_);
v___x_5928_ = v_pos_5917_;
v_isShared_5929_ = v_isSharedCheck_5943_;
goto v_resetjp_5927_;
}
else
{
lean_dec(v_pos_5917_);
v___x_5928_ = lean_box(0);
v_isShared_5929_ = v_isSharedCheck_5943_;
goto v_resetjp_5927_;
}
v_resetjp_5927_:
{
lean_object* v___x_5930_; lean_object* v_it_x27_5932_; 
v___x_5930_ = lean_string_utf8_next_fast(v_fst_5918_, v_snd_5919_);
if (v_isShared_5929_ == 0)
{
lean_ctor_set(v___x_5928_, 1, v___x_5930_);
v_it_x27_5932_ = v___x_5928_;
goto v_reusejp_5931_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_fst_5918_);
lean_ctor_set(v_reuseFailAlloc_5942_, 1, v___x_5930_);
v_it_x27_5932_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5931_;
}
v_reusejp_5931_:
{
lean_object* v___x_5933_; lean_object* v___x_5934_; 
v___x_5933_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__0);
v___x_5934_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(v___x_5933_, v_it_x27_5932_);
if (lean_obj_tag(v___x_5934_) == 0)
{
lean_object* v_pos_5935_; lean_object* v_res_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; 
v_pos_5935_ = lean_ctor_get(v___x_5934_, 0);
lean_inc(v_pos_5935_);
v_res_5936_ = lean_ctor_get(v___x_5934_, 1);
lean_inc(v_res_5936_);
lean_dec_ref_known(v___x_5934_, 2);
v___x_5937_ = ((lean_object*)(l_Std_Time_parseModifier___closed__30));
v___x_5938_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5913_, v___x_5937_, v_res_5936_, v_pos_5935_);
if (lean_obj_tag(v___x_5938_) == 0)
{
lean_dec(v_snd_5919_);
return v___x_5938_;
}
else
{
lean_object* v_pos_5939_; 
v_pos_5939_ = lean_ctor_get(v___x_5938_, 0);
lean_inc(v_pos_5939_);
v_snd_5874_ = v_snd_5919_;
v___y_5875_ = v___x_5938_;
v_pos_5876_ = v_pos_5939_;
goto v___jp_5873_;
}
}
else
{
lean_object* v_pos_5940_; lean_object* v_err_5941_; 
v_pos_5940_ = lean_ctor_get(v___x_5934_, 0);
lean_inc(v_pos_5940_);
v_err_5941_ = lean_ctor_get(v___x_5934_, 1);
lean_inc(v_err_5941_);
lean_dec_ref_known(v___x_5934_, 2);
v_snd_5905_ = v_snd_5919_;
v_pos_5906_ = v_pos_5940_;
v_err_5907_ = v_err_5941_;
goto v___jp_5904_;
}
}
}
}
}
}
else
{
v___y_5910_ = v_pos_5917_;
v_snd_5911_ = v_snd_5919_;
goto v___jp_5909_;
}
}
}
v___jp_5946_:
{
lean_object* v___x_5950_; 
lean_inc_ref(v_pos_5948_);
v___x_5950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5950_, 0, v_pos_5948_);
lean_ctor_set(v___x_5950_, 1, v_err_5949_);
v_snd_5915_ = v_snd_5947_;
v___y_5916_ = v___x_5950_;
v_pos_5917_ = v_pos_5948_;
goto v___jp_5914_;
}
v___jp_5951_:
{
lean_object* v___x_5954_; 
v___x_5954_ = lean_box(0);
v_snd_5947_ = v_snd_5953_;
v_pos_5948_ = v___y_5952_;
v_err_5949_ = v___x_5954_;
goto v___jp_5946_;
}
v___jp_5956_:
{
lean_object* v_fst_5960_; lean_object* v_snd_5961_; uint8_t v___x_5962_; 
v_fst_5960_ = lean_ctor_get(v_pos_5959_, 0);
v_snd_5961_ = lean_ctor_get(v_pos_5959_, 1);
lean_inc(v_snd_5961_);
v___x_5962_ = lean_nat_dec_eq(v_snd_5957_, v_snd_5961_);
lean_dec(v_snd_5957_);
if (v___x_5962_ == 0)
{
lean_dec(v_snd_5961_);
lean_dec_ref(v_pos_5959_);
return v___y_5958_;
}
else
{
lean_object* v___x_5963_; uint8_t v___x_5964_; 
lean_dec_ref(v___y_5958_);
v___x_5963_ = lean_string_utf8_byte_size(v_fst_5960_);
v___x_5964_ = lean_nat_dec_eq(v_snd_5961_, v___x_5963_);
if (v___x_5964_ == 0)
{
if (v___x_5962_ == 0)
{
v___y_5952_ = v_pos_5959_;
v_snd_5953_ = v_snd_5961_;
goto v___jp_5951_;
}
else
{
uint32_t v___x_5965_; uint32_t v_c_5966_; uint8_t v___x_5967_; 
v___x_5965_ = 117;
v_c_5966_ = lean_string_utf8_get_fast(v_fst_5960_, v_snd_5961_);
v___x_5967_ = lean_uint32_dec_eq(v_c_5966_, v___x_5965_);
if (v___x_5967_ == 0)
{
lean_object* v___x_5968_; 
v___x_5968_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__3);
v_snd_5947_ = v_snd_5961_;
v_pos_5948_ = v_pos_5959_;
v_err_5949_ = v___x_5968_;
goto v___jp_5946_;
}
else
{
lean_object* v___x_5970_; uint8_t v_isShared_5971_; uint8_t v_isSharedCheck_5984_; 
lean_inc(v_fst_5960_);
v_isSharedCheck_5984_ = !lean_is_exclusive(v_pos_5959_);
if (v_isSharedCheck_5984_ == 0)
{
lean_object* v_unused_5985_; lean_object* v_unused_5986_; 
v_unused_5985_ = lean_ctor_get(v_pos_5959_, 1);
lean_dec(v_unused_5985_);
v_unused_5986_ = lean_ctor_get(v_pos_5959_, 0);
lean_dec(v_unused_5986_);
v___x_5970_ = v_pos_5959_;
v_isShared_5971_ = v_isSharedCheck_5984_;
goto v_resetjp_5969_;
}
else
{
lean_dec(v_pos_5959_);
v___x_5970_ = lean_box(0);
v_isShared_5971_ = v_isSharedCheck_5984_;
goto v_resetjp_5969_;
}
v_resetjp_5969_:
{
lean_object* v___x_5972_; lean_object* v_it_x27_5974_; 
v___x_5972_ = lean_string_utf8_next_fast(v_fst_5960_, v_snd_5961_);
if (v_isShared_5971_ == 0)
{
lean_ctor_set(v___x_5970_, 1, v___x_5972_);
v_it_x27_5974_ = v___x_5970_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v_fst_5960_);
lean_ctor_set(v_reuseFailAlloc_5983_, 1, v___x_5972_);
v_it_x27_5974_ = v_reuseFailAlloc_5983_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
lean_object* v___x_5975_; lean_object* v___x_5976_; 
v___x_5975_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__0);
v___x_5976_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(v___x_5975_, v_it_x27_5974_);
if (lean_obj_tag(v___x_5976_) == 0)
{
lean_object* v_pos_5977_; lean_object* v_res_5978_; lean_object* v___x_5979_; 
v_pos_5977_ = lean_ctor_get(v___x_5976_, 0);
lean_inc(v_pos_5977_);
v_res_5978_ = lean_ctor_get(v___x_5976_, 1);
lean_inc(v_res_5978_);
lean_dec_ref_known(v___x_5976_, 2);
v___x_5979_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5955_, v_res_5978_, v_pos_5977_);
if (lean_obj_tag(v___x_5979_) == 0)
{
lean_dec(v_snd_5961_);
return v___x_5979_;
}
else
{
lean_object* v_pos_5980_; 
v_pos_5980_ = lean_ctor_get(v___x_5979_, 0);
lean_inc(v_pos_5980_);
v_snd_5915_ = v_snd_5961_;
v___y_5916_ = v___x_5979_;
v_pos_5917_ = v_pos_5980_;
goto v___jp_5914_;
}
}
else
{
lean_object* v_pos_5981_; lean_object* v_err_5982_; 
v_pos_5981_ = lean_ctor_get(v___x_5976_, 0);
lean_inc(v_pos_5981_);
v_err_5982_ = lean_ctor_get(v___x_5976_, 1);
lean_inc(v_err_5982_);
lean_dec_ref_known(v___x_5976_, 2);
v_snd_5947_ = v_snd_5961_;
v_pos_5948_ = v_pos_5981_;
v_err_5949_ = v_err_5982_;
goto v___jp_5946_;
}
}
}
}
}
}
else
{
v___y_5952_ = v_pos_5959_;
v_snd_5953_ = v_snd_5961_;
goto v___jp_5951_;
}
}
}
v___jp_5987_:
{
lean_object* v___x_5991_; 
lean_inc_ref(v_pos_5989_);
v___x_5991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5991_, 0, v_pos_5989_);
lean_ctor_set(v___x_5991_, 1, v_err_5990_);
v_snd_5957_ = v_snd_5988_;
v___y_5958_ = v___x_5991_;
v_pos_5959_ = v_pos_5989_;
goto v___jp_5956_;
}
v___jp_5992_:
{
lean_object* v___x_5995_; 
v___x_5995_ = lean_box(0);
v_snd_5988_ = v_snd_5994_;
v_pos_5989_ = v___y_5993_;
v_err_5990_ = v___x_5995_;
goto v___jp_5987_;
}
v___jp_5997_:
{
lean_object* v_fst_6001_; lean_object* v_snd_6002_; uint8_t v___x_6003_; 
v_fst_6001_ = lean_ctor_get(v_pos_6000_, 0);
v_snd_6002_ = lean_ctor_get(v_pos_6000_, 1);
lean_inc(v_snd_6002_);
v___x_6003_ = lean_nat_dec_eq(v_snd_5998_, v_snd_6002_);
lean_dec(v_snd_5998_);
if (v___x_6003_ == 0)
{
lean_dec(v_snd_6002_);
lean_dec_ref(v_pos_6000_);
return v___y_5999_;
}
else
{
lean_object* v___x_6004_; uint8_t v___x_6005_; 
lean_dec_ref(v___y_5999_);
v___x_6004_ = lean_string_utf8_byte_size(v_fst_6001_);
v___x_6005_ = lean_nat_dec_eq(v_snd_6002_, v___x_6004_);
if (v___x_6005_ == 0)
{
if (v___x_6003_ == 0)
{
v___y_5993_ = v_pos_6000_;
v_snd_5994_ = v_snd_6002_;
goto v___jp_5992_;
}
else
{
uint32_t v___x_6006_; uint32_t v_c_6007_; uint8_t v___x_6008_; 
v___x_6006_ = 89;
v_c_6007_ = lean_string_utf8_get_fast(v_fst_6001_, v_snd_6002_);
v___x_6008_ = lean_uint32_dec_eq(v_c_6007_, v___x_6006_);
if (v___x_6008_ == 0)
{
lean_object* v___x_6009_; 
v___x_6009_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__3);
v_snd_5988_ = v_snd_6002_;
v_pos_5989_ = v_pos_6000_;
v_err_5990_ = v___x_6009_;
goto v___jp_5987_;
}
else
{
lean_object* v___x_6011_; uint8_t v_isShared_6012_; uint8_t v_isSharedCheck_6025_; 
lean_inc(v_fst_6001_);
v_isSharedCheck_6025_ = !lean_is_exclusive(v_pos_6000_);
if (v_isSharedCheck_6025_ == 0)
{
lean_object* v_unused_6026_; lean_object* v_unused_6027_; 
v_unused_6026_ = lean_ctor_get(v_pos_6000_, 1);
lean_dec(v_unused_6026_);
v_unused_6027_ = lean_ctor_get(v_pos_6000_, 0);
lean_dec(v_unused_6027_);
v___x_6011_ = v_pos_6000_;
v_isShared_6012_ = v_isSharedCheck_6025_;
goto v_resetjp_6010_;
}
else
{
lean_dec(v_pos_6000_);
v___x_6011_ = lean_box(0);
v_isShared_6012_ = v_isSharedCheck_6025_;
goto v_resetjp_6010_;
}
v_resetjp_6010_:
{
lean_object* v___x_6013_; lean_object* v_it_x27_6015_; 
v___x_6013_ = lean_string_utf8_next_fast(v_fst_6001_, v_snd_6002_);
if (v_isShared_6012_ == 0)
{
lean_ctor_set(v___x_6011_, 1, v___x_6013_);
v_it_x27_6015_ = v___x_6011_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v_fst_6001_);
lean_ctor_set(v_reuseFailAlloc_6024_, 1, v___x_6013_);
v_it_x27_6015_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
lean_object* v___x_6016_; lean_object* v___x_6017_; 
v___x_6016_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__0);
v___x_6017_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(v___x_6016_, v_it_x27_6015_);
if (lean_obj_tag(v___x_6017_) == 0)
{
lean_object* v_pos_6018_; lean_object* v_res_6019_; lean_object* v___x_6020_; 
v_pos_6018_ = lean_ctor_get(v___x_6017_, 0);
lean_inc(v_pos_6018_);
v_res_6019_ = lean_ctor_get(v___x_6017_, 1);
lean_inc(v_res_6019_);
lean_dec_ref_known(v___x_6017_, 2);
v___x_6020_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5996_, v_res_6019_, v_pos_6018_);
if (lean_obj_tag(v___x_6020_) == 0)
{
lean_dec(v_snd_6002_);
return v___x_6020_;
}
else
{
lean_object* v_pos_6021_; 
v_pos_6021_ = lean_ctor_get(v___x_6020_, 0);
lean_inc(v_pos_6021_);
v_snd_5957_ = v_snd_6002_;
v___y_5958_ = v___x_6020_;
v_pos_5959_ = v_pos_6021_;
goto v___jp_5956_;
}
}
else
{
lean_object* v_pos_6022_; lean_object* v_err_6023_; 
v_pos_6022_ = lean_ctor_get(v___x_6017_, 0);
lean_inc(v_pos_6022_);
v_err_6023_ = lean_ctor_get(v___x_6017_, 1);
lean_inc(v_err_6023_);
lean_dec_ref_known(v___x_6017_, 2);
v_snd_5988_ = v_snd_6002_;
v_pos_5989_ = v_pos_6022_;
v_err_5990_ = v_err_6023_;
goto v___jp_5987_;
}
}
}
}
}
}
else
{
v___y_5993_ = v_pos_6000_;
v_snd_5994_ = v_snd_6002_;
goto v___jp_5992_;
}
}
}
v___jp_6028_:
{
lean_object* v___x_6032_; 
lean_inc_ref(v_pos_6030_);
v___x_6032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6032_, 0, v_pos_6030_);
lean_ctor_set(v___x_6032_, 1, v_err_6031_);
v_snd_5998_ = v_snd_6029_;
v___y_5999_ = v___x_6032_;
v_pos_6000_ = v_pos_6030_;
goto v___jp_5997_;
}
v___jp_6033_:
{
lean_object* v___x_6036_; 
v___x_6036_ = lean_box(0);
v_snd_6029_ = v_snd_6035_;
v_pos_6030_ = v___y_6034_;
v_err_6031_ = v___x_6036_;
goto v___jp_6028_;
}
v___jp_6038_:
{
lean_object* v_fst_6041_; lean_object* v_snd_6042_; uint8_t v___x_6043_; 
v_fst_6041_ = lean_ctor_get(v_pos_6040_, 0);
v_snd_6042_ = lean_ctor_get(v_pos_6040_, 1);
lean_inc(v_snd_6042_);
v___x_6043_ = lean_nat_dec_eq(v_snd_4576_, v_snd_6042_);
lean_dec(v_snd_4576_);
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
v___y_6034_ = v_pos_6040_;
v_snd_6035_ = v_snd_6042_;
goto v___jp_6033_;
}
else
{
uint32_t v___x_6046_; uint32_t v_c_6047_; uint8_t v___x_6048_; 
v___x_6046_ = 121;
v_c_6047_ = lean_string_utf8_get_fast(v_fst_6041_, v_snd_6042_);
v___x_6048_ = lean_uint32_dec_eq(v_c_6047_, v___x_6046_);
if (v___x_6048_ == 0)
{
lean_object* v___x_6049_; 
v___x_6049_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__3);
v_snd_6029_ = v_snd_6042_;
v_pos_6030_ = v_pos_6040_;
v_err_6031_ = v___x_6049_;
goto v___jp_6028_;
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
v___x_6056_ = lean_obj_once(&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0, &l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0_once, _init_l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__0);
v___x_6057_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(v___x_6056_, v_it_x27_6055_);
if (lean_obj_tag(v___x_6057_) == 0)
{
lean_object* v_pos_6058_; lean_object* v_res_6059_; lean_object* v___x_6060_; 
v_pos_6058_ = lean_ctor_get(v___x_6057_, 0);
lean_inc(v_pos_6058_);
v_res_6059_ = lean_ctor_get(v___x_6057_, 1);
lean_inc(v_res_6059_);
lean_dec_ref_known(v___x_6057_, 2);
v___x_6060_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_6037_, v_res_6059_, v_pos_6058_);
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
v_snd_5998_ = v_snd_6042_;
v___y_5999_ = v___x_6060_;
v_pos_6000_ = v_pos_6061_;
goto v___jp_5997_;
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
v_snd_6029_ = v_snd_6042_;
v_pos_6030_ = v_pos_6062_;
v_err_6031_ = v_err_6063_;
goto v___jp_6028_;
}
}
}
}
}
}
else
{
v___y_6034_ = v_pos_6040_;
v_snd_6035_ = v_snd_6042_;
goto v___jp_6033_;
}
}
}
v___jp_6068_:
{
lean_object* v___x_6071_; 
lean_inc_ref(v_pos_6069_);
v___x_6071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6071_, 0, v_pos_6069_);
lean_ctor_set(v___x_6071_, 1, v_err_6070_);
v___y_6039_ = v___x_6071_;
v_pos_6040_ = v_pos_6069_;
goto v___jp_6038_;
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
