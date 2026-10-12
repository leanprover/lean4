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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_Std_Time_Text_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Time_Text_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Time_Text_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Time_Text_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Time_Text_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Std_Time_Text_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Time_Text_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Time_Text_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
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
lean_object* l_Std_Time_Text_short_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_short_30_){
_start:
{
lean_inc(v_short_30_);
return v_short_30_;
}
}
LEAN_EXPORT void l_Std_Time_Text_short_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_short_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Time_Text_short_elim(lean_box(0), v_t_28_, lean_box(0), v_short_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_short_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Time_Text_short_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_short_35_);
lean_dec(v_short_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___redArg(lean_object* v_full_38_){
_start:
{
lean_inc(v_full_38_);
return v_full_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___redArg___boxed(lean_object* v_full_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Time_Text_full_elim___redArg(v_full_39_);
lean_dec(v_full_39_);
return v_res_40_;
}
}
lean_object* l_Std_Time_Text_full_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_full_44_){
_start:
{
lean_inc(v_full_44_);
return v_full_44_;
}
}
LEAN_EXPORT void l_Std_Time_Text_full_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_full_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Time_Text_full_elim(lean_box(0), v_t_42_, lean_box(0), v_full_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_full_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Time_Text_full_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_full_49_);
lean_dec(v_full_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___redArg(lean_object* v_narrow_52_){
_start:
{
lean_inc(v_narrow_52_);
return v_narrow_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___redArg___boxed(lean_object* v_narrow_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Time_Text_narrow_elim___redArg(v_narrow_53_);
lean_dec(v_narrow_53_);
return v_res_54_;
}
}
lean_object* l_Std_Time_Text_narrow_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_narrow_58_){
_start:
{
lean_inc(v_narrow_58_);
return v_narrow_58_;
}
}
LEAN_EXPORT void l_Std_Time_Text_narrow_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_narrow_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Std_Time_Text_narrow_elim(lean_box(0), v_t_56_, lean_box(0), v_narrow_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_narrow_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Std_Time_Text_narrow_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_narrow_63_);
lean_dec(v_narrow_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___redArg(lean_object* v_twoLetterShort_66_){
_start:
{
lean_inc(v_twoLetterShort_66_);
return v_twoLetterShort_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___redArg___boxed(lean_object* v_twoLetterShort_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_Time_Text_twoLetterShort_elim___redArg(v_twoLetterShort_67_);
lean_dec(v_twoLetterShort_67_);
return v_res_68_;
}
}
lean_object* l_Std_Time_Text_twoLetterShort_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_twoLetterShort_72_){
_start:
{
lean_inc(v_twoLetterShort_72_);
return v_twoLetterShort_72_;
}
}
LEAN_EXPORT void l_Std_Time_Text_twoLetterShort_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_twoLetterShort_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Std_Time_Text_twoLetterShort_elim(lean_box(0), v_t_70_, lean_box(0), v_twoLetterShort_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_twoLetterShort_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l_Std_Time_Text_twoLetterShort_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_twoLetterShort_77_);
lean_dec(v_twoLetterShort_77_);
return v_res_79_;
}
}
static lean_object* _init_l_Std_Time_instReprText_repr___closed__8(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(2u);
v___x_93_ = lean_nat_to_int(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Std_Time_instReprText_repr___closed__9(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_nat_to_int(v___x_94_);
return v___x_95_;
}
}
lean_object* l_Std_Time_instReprText_repr(uint8_t v_x_96_, lean_object* v_prec_97_){
_start:
{
lean_object* v___y_99_; lean_object* v___y_106_; lean_object* v___y_113_; lean_object* v___y_120_; 
switch(v_x_96_)
{
case 0:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1024u);
v___x_127_ = lean_nat_dec_le(v___x_126_, v_prec_97_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_99_ = v___x_128_;
goto v___jp_98_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_99_ = v___x_129_;
goto v___jp_98_;
}
}
case 1:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1024u);
v___x_131_ = lean_nat_dec_le(v___x_130_, v_prec_97_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_106_ = v___x_132_;
goto v___jp_105_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_106_ = v___x_133_;
goto v___jp_105_;
}
}
case 2:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(1024u);
v___x_135_ = lean_nat_dec_le(v___x_134_, v_prec_97_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_113_ = v___x_136_;
goto v___jp_112_;
}
else
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_113_ = v___x_137_;
goto v___jp_112_;
}
}
default: 
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1024u);
v___x_139_ = lean_nat_dec_le(v___x_138_, v_prec_97_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_120_ = v___x_140_;
goto v___jp_119_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_120_ = v___x_141_;
goto v___jp_119_;
}
}
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__1));
lean_inc(v___y_99_);
v___x_101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_101_, 0, v___y_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = 0;
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
v___x_104_ = l_Repr_addAppParen(v___x_103_, v_prec_97_);
return v___x_104_;
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_107_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__3));
lean_inc(v___y_106_);
v___x_108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_108_, 0, v___y_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = 0;
v___x_110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v___x_109_);
v___x_111_ = l_Repr_addAppParen(v___x_110_, v_prec_97_);
return v___x_111_;
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_114_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__5));
lean_inc(v___y_113_);
v___x_115_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_115_, 0, v___y_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = 0;
v___x_117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
v___x_118_ = l_Repr_addAppParen(v___x_117_, v_prec_97_);
return v___x_118_;
}
v___jp_119_:
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_121_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__7));
lean_inc(v___y_120_);
v___x_122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_122_, 0, v___y_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = 0;
v___x_124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set_uint8(v___x_124_, sizeof(void*)*1, v___x_123_);
v___x_125_ = l_Repr_addAppParen(v___x_124_, v_prec_97_);
return v___x_125_;
}
}
}
LEAN_EXPORT void l_Std_Time_instReprText_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_96_ = stack[0].m_num;
lean_object* v_prec_97_ = stack[1].m_obj;
lean_object* v_res_142_;
v_res_142_ = l_Std_Time_instReprText_repr(v_x_96_, v_prec_97_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l_Std_Time_instReprText_repr___boxed(lean_object* v_x_143_, lean_object* v_prec_144_){
_start:
{
uint8_t v_x_225__boxed_145_; lean_object* v_res_146_; 
v_x_225__boxed_145_ = lean_unbox(v_x_143_);
v_res_146_ = l_Std_Time_instReprText_repr(v_x_225__boxed_145_, v_prec_144_);
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
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx___impl(lean_object* v_x_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_tag_nat(v_x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx___impl___boxed(lean_object* v_x_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_Time_Fraction_ctorIdx___impl(v_x_242_);
lean_dec(v_x_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim___redArg(lean_object* v_t_244_, lean_object* v_k_245_){
_start:
{
if (lean_obj_tag(v_t_244_) == 0)
{
return v_k_245_;
}
else
{
lean_object* v_digits_246_; lean_object* v___x_247_; 
v_digits_246_ = lean_ctor_get(v_t_244_, 0);
lean_inc(v_digits_246_);
lean_dec_ref_known(v_t_244_, 1);
v___x_247_ = lean_apply_1(v_k_245_, v_digits_246_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim(lean_object* v_motive_248_, lean_object* v_ctorIdx_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_k_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_250_, v_k_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim___boxed(lean_object* v_motive_254_, lean_object* v_ctorIdx_255_, lean_object* v_t_256_, lean_object* v_h_257_, lean_object* v_k_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Time_Fraction_ctorElim(v_motive_254_, v_ctorIdx_255_, v_t_256_, v_h_257_, v_k_258_);
lean_dec(v_ctorIdx_255_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_nano_elim___redArg(lean_object* v_t_260_, lean_object* v_nano_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_260_, v_nano_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_nano_elim(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_nano_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_264_, v_nano_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_truncated_elim___redArg(lean_object* v_t_268_, lean_object* v_truncated_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_268_, v_truncated_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_truncated_elim(lean_object* v_motive_271_, lean_object* v_t_272_, lean_object* v_h_273_, lean_object* v_truncated_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_272_, v_truncated_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFraction_repr(lean_object* v_x_285_, lean_object* v_prec_286_){
_start:
{
lean_object* v___y_288_; 
if (lean_obj_tag(v_x_285_) == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(1024u);
v___x_295_ = lean_nat_dec_le(v___x_294_, v_prec_286_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_288_ = v___x_296_;
goto v___jp_287_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_288_ = v___x_297_;
goto v___jp_287_;
}
}
else
{
lean_object* v_digits_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_318_; 
v_digits_298_ = lean_ctor_get(v_x_285_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v_x_285_);
if (v_isSharedCheck_318_ == 0)
{
v___x_300_ = v_x_285_;
v_isShared_301_ = v_isSharedCheck_318_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_digits_298_);
lean_dec(v_x_285_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_318_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___y_303_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(1024u);
v___x_315_ = lean_nat_dec_le(v___x_314_, v_prec_286_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
v___x_316_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_303_ = v___x_316_;
goto v___jp_302_;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_303_ = v___x_317_;
goto v___jp_302_;
}
v___jp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = ((lean_object*)(l_Std_Time_instReprFraction_repr___closed__4));
v___x_305_ = l_Nat_reprFast(v_digits_298_);
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 3);
lean_ctor_set(v___x_300_, 0, v___x_305_);
v___x_307_ = v___x_300_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_313_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_304_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
lean_inc(v___y_303_);
v___x_309_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_309_, 0, v___y_303_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = 0;
v___x_311_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set_uint8(v___x_311_, sizeof(void*)*1, v___x_310_);
v___x_312_ = l_Repr_addAppParen(v___x_311_, v_prec_286_);
return v___x_312_;
}
}
}
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_289_ = ((lean_object*)(l_Std_Time_instReprFraction_repr___closed__1));
lean_inc(v___y_288_);
v___x_290_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_290_, 0, v___y_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = 0;
v___x_292_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1, v___x_291_);
v___x_293_ = l_Repr_addAppParen(v___x_292_, v_prec_286_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFraction_repr___boxed(lean_object* v_x_319_, lean_object* v_prec_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Std_Time_instReprFraction_repr(v_x_319_, v_prec_320_);
lean_dec(v_prec_320_);
return v_res_321_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFraction_default(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_box(0);
return v___x_324_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFraction(void){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(0);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_classify(lean_object* v_nat_328_){
_start:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(9u);
v___x_330_ = lean_nat_dec_lt(v_nat_328_, v___x_329_);
if (v___x_330_ == 0)
{
uint8_t v___x_331_; 
v___x_331_ = lean_nat_dec_eq(v_nat_328_, v___x_329_);
lean_dec(v_nat_328_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_box(0);
return v___x_332_;
}
else
{
lean_object* v___x_333_; 
v___x_333_ = ((lean_object*)(l_Std_Time_Fraction_classify___closed__0));
return v___x_333_;
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v_nat_328_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx___impl(lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_obj_tag_nat(v_x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx___impl___boxed(lean_object* v_x_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Std_Time_Year_ctorIdx___impl(v_x_338_);
lean_dec(v_x_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim___redArg(lean_object* v_t_340_, lean_object* v_k_341_){
_start:
{
if (lean_obj_tag(v_t_340_) == 3)
{
lean_object* v_num_342_; lean_object* v___x_343_; 
v_num_342_ = lean_ctor_get(v_t_340_, 0);
lean_inc(v_num_342_);
lean_dec_ref_known(v_t_340_, 1);
v___x_343_ = lean_apply_1(v_k_341_, v_num_342_);
return v___x_343_;
}
else
{
lean_dec(v_t_340_);
return v_k_341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim(lean_object* v_motive_344_, lean_object* v_ctorIdx_345_, lean_object* v_t_346_, lean_object* v_h_347_, lean_object* v_k_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Std_Time_Year_ctorElim___redArg(v_t_346_, v_k_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim___boxed(lean_object* v_motive_350_, lean_object* v_ctorIdx_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_k_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_Time_Year_ctorElim(v_motive_350_, v_ctorIdx_351_, v_t_352_, v_h_353_, v_k_354_);
lean_dec(v_ctorIdx_351_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_any_elim___redArg(lean_object* v_t_356_, lean_object* v_any_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_Time_Year_ctorElim___redArg(v_t_356_, v_any_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_any_elim(lean_object* v_motive_359_, lean_object* v_t_360_, lean_object* v_h_361_, lean_object* v_any_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Std_Time_Year_ctorElim___redArg(v_t_360_, v_any_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_twoDigit_elim___redArg(lean_object* v_t_364_, lean_object* v_twoDigit_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Std_Time_Year_ctorElim___redArg(v_t_364_, v_twoDigit_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_twoDigit_elim(lean_object* v_motive_367_, lean_object* v_t_368_, lean_object* v_h_369_, lean_object* v_twoDigit_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_Time_Year_ctorElim___redArg(v_t_368_, v_twoDigit_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_fourDigit_elim___redArg(lean_object* v_t_372_, lean_object* v_fourDigit_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_Time_Year_ctorElim___redArg(v_t_372_, v_fourDigit_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_fourDigit_elim(lean_object* v_motive_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_fourDigit_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_Time_Year_ctorElim___redArg(v_t_376_, v_fourDigit_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_extended_elim___redArg(lean_object* v_t_380_, lean_object* v_extended_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_Time_Year_ctorElim___redArg(v_t_380_, v_extended_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_extended_elim(lean_object* v_motive_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_extended_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_Time_Year_ctorElim___redArg(v_t_384_, v_extended_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprYear_repr(lean_object* v_x_403_, lean_object* v_prec_404_){
_start:
{
lean_object* v___y_406_; lean_object* v___y_413_; lean_object* v___y_420_; 
switch(lean_obj_tag(v_x_403_))
{
case 0:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(1024u);
v___x_427_ = lean_nat_dec_le(v___x_426_, v_prec_404_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
v___x_428_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_420_ = v___x_428_;
goto v___jp_419_;
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_420_ = v___x_429_;
goto v___jp_419_;
}
}
case 1:
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(1024u);
v___x_431_ = lean_nat_dec_le(v___x_430_, v_prec_404_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_413_ = v___x_432_;
goto v___jp_412_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_413_ = v___x_433_;
goto v___jp_412_;
}
}
case 2:
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(1024u);
v___x_435_ = lean_nat_dec_le(v___x_434_, v_prec_404_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_406_ = v___x_436_;
goto v___jp_405_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_406_ = v___x_437_;
goto v___jp_405_;
}
}
default: 
{
lean_object* v_num_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_458_; 
v_num_438_ = lean_ctor_get(v_x_403_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_403_);
if (v_isSharedCheck_458_ == 0)
{
v___x_440_ = v_x_403_;
v_isShared_441_ = v_isSharedCheck_458_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_num_438_);
lean_dec(v_x_403_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_458_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___y_443_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_unsigned_to_nat(1024u);
v___x_455_ = lean_nat_dec_le(v___x_454_, v_prec_404_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_443_ = v___x_456_;
goto v___jp_442_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_443_ = v___x_457_;
goto v___jp_442_;
}
v___jp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_444_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__8));
v___x_445_ = l_Nat_reprFast(v_num_438_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_445_);
v___x_447_ = v___x_440_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_453_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_444_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
lean_inc(v___y_443_);
v___x_449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_443_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = 0;
v___x_451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
v___x_452_ = l_Repr_addAppParen(v___x_451_, v_prec_404_);
return v___x_452_;
}
}
}
}
}
v___jp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_407_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__1));
lean_inc(v___y_406_);
v___x_408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_408_, 0, v___y_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = 0;
v___x_410_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*1, v___x_409_);
v___x_411_ = l_Repr_addAppParen(v___x_410_, v_prec_404_);
return v___x_411_;
}
v___jp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_414_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__3));
lean_inc(v___y_413_);
v___x_415_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_415_, 0, v___y_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = 0;
v___x_417_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_416_);
v___x_418_ = l_Repr_addAppParen(v___x_417_, v_prec_404_);
return v___x_418_;
}
v___jp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_421_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__5));
lean_inc(v___y_420_);
v___x_422_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_422_, 0, v___y_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = 0;
v___x_424_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*1, v___x_423_);
v___x_425_ = l_Repr_addAppParen(v___x_424_, v_prec_404_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprYear_repr___boxed(lean_object* v_x_459_, lean_object* v_prec_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_Time_instReprYear_repr(v_x_459_, v_prec_460_);
lean_dec(v_prec_460_);
return v_res_461_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedYear_default(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_box(0);
return v___x_464_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedYear(void){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_box(0);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_classify(lean_object* v_num_472_){
_start:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_dec_eq(v_num_472_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(2u);
v___x_479_ = lean_nat_dec_eq(v_num_472_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(4u);
v___x_481_ = lean_nat_dec_eq(v_num_472_, v___x_480_);
if (v___x_481_ == 0)
{
uint8_t v___x_482_; 
v___x_482_ = lean_nat_dec_lt(v___x_480_, v_num_472_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(3u);
v___x_484_ = lean_nat_dec_eq(v_num_472_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
lean_dec(v_num_472_);
v___x_485_ = lean_box(0);
return v___x_485_;
}
else
{
goto v___jp_473_;
}
}
else
{
goto v___jp_473_;
}
}
else
{
lean_object* v___x_486_; 
lean_dec(v_num_472_);
v___x_486_ = ((lean_object*)(l_Std_Time_Year_classify___closed__0));
return v___x_486_;
}
}
else
{
lean_object* v___x_487_; 
lean_dec(v_num_472_);
v___x_487_ = ((lean_object*)(l_Std_Time_Year_classify___closed__1));
return v___x_487_;
}
}
else
{
lean_object* v___x_488_; 
lean_dec(v_num_472_);
v___x_488_ = ((lean_object*)(l_Std_Time_Year_classify___closed__2));
return v___x_488_;
}
v___jp_473_:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_474_, 0, v_num_472_);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
}
lean_object* l_Std_Time_ZoneId_ctorIdx___impl(uint8_t v_x_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_box(v_x_489_);
v___x_491_ = lean_obj_tag_nat(v___x_490_);
lean_dec(v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT void l_Std_Time_ZoneId_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_489_ = stack[0].m_num;
lean_object* v_res_492_;
v_res_492_ = l_Std_Time_ZoneId_ctorIdx___impl(v_x_489_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx___impl___boxed(lean_object* v_x_493_){
_start:
{
uint8_t v_x_4__boxed_494_; lean_object* v_res_495_; 
v_x_4__boxed_494_ = lean_unbox(v_x_493_);
v_res_495_ = l_Std_Time_ZoneId_ctorIdx___impl(v_x_4__boxed_494_);
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
lean_object* l_Std_Time_ZoneId_ctorElim(lean_object* v_motive_499_, lean_object* v_ctorIdx_500_, uint8_t v_t_501_, lean_object* v_h_502_, lean_object* v_k_503_){
_start:
{
lean_inc(v_k_503_);
return v_k_503_;
}
}
LEAN_EXPORT void l_Std_Time_ZoneId_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_500_ = stack[1].m_obj;
uint8_t v_t_501_ = stack[2].m_num;
lean_object* v_k_503_ = stack[4].m_obj;
lean_object* v_res_504_;
v_res_504_ = l_Std_Time_ZoneId_ctorElim(lean_box(0), v_ctorIdx_500_, v_t_501_, lean_box(0), v_k_503_);
stack->m_obj
 = v_res_504_;
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___boxed(lean_object* v_motive_505_, lean_object* v_ctorIdx_506_, lean_object* v_t_507_, lean_object* v_h_508_, lean_object* v_k_509_){
_start:
{
uint8_t v_t_boxed_510_; lean_object* v_res_511_; 
v_t_boxed_510_ = lean_unbox(v_t_507_);
v_res_511_ = l_Std_Time_ZoneId_ctorElim(v_motive_505_, v_ctorIdx_506_, v_t_boxed_510_, v_h_508_, v_k_509_);
lean_dec(v_k_509_);
lean_dec(v_ctorIdx_506_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg(lean_object* v_unknown_512_){
_start:
{
lean_inc(v_unknown_512_);
return v_unknown_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg___boxed(lean_object* v_unknown_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_Time_ZoneId_unknown_elim___redArg(v_unknown_513_);
lean_dec(v_unknown_513_);
return v_res_514_;
}
}
lean_object* l_Std_Time_ZoneId_unknown_elim(lean_object* v_motive_515_, uint8_t v_t_516_, lean_object* v_h_517_, lean_object* v_unknown_518_){
_start:
{
lean_inc(v_unknown_518_);
return v_unknown_518_;
}
}
LEAN_EXPORT void l_Std_Time_ZoneId_unknown_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_516_ = stack[1].m_num;
lean_object* v_unknown_518_ = stack[3].m_obj;
lean_object* v_res_519_;
v_res_519_ = l_Std_Time_ZoneId_unknown_elim(lean_box(0), v_t_516_, lean_box(0), v_unknown_518_);
stack->m_obj
 = v_res_519_;
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___boxed(lean_object* v_motive_520_, lean_object* v_t_521_, lean_object* v_h_522_, lean_object* v_unknown_523_){
_start:
{
uint8_t v_t_boxed_524_; lean_object* v_res_525_; 
v_t_boxed_524_ = lean_unbox(v_t_521_);
v_res_525_ = l_Std_Time_ZoneId_unknown_elim(v_motive_520_, v_t_boxed_524_, v_h_522_, v_unknown_523_);
lean_dec(v_unknown_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg(lean_object* v_short_526_){
_start:
{
lean_inc(v_short_526_);
return v_short_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg___boxed(lean_object* v_short_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Time_ZoneId_short_elim___redArg(v_short_527_);
lean_dec(v_short_527_);
return v_res_528_;
}
}
lean_object* l_Std_Time_ZoneId_short_elim(lean_object* v_motive_529_, uint8_t v_t_530_, lean_object* v_h_531_, lean_object* v_short_532_){
_start:
{
lean_inc(v_short_532_);
return v_short_532_;
}
}
LEAN_EXPORT void l_Std_Time_ZoneId_short_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_530_ = stack[1].m_num;
lean_object* v_short_532_ = stack[3].m_obj;
lean_object* v_res_533_;
v_res_533_ = l_Std_Time_ZoneId_short_elim(lean_box(0), v_t_530_, lean_box(0), v_short_532_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___boxed(lean_object* v_motive_534_, lean_object* v_t_535_, lean_object* v_h_536_, lean_object* v_short_537_){
_start:
{
uint8_t v_t_boxed_538_; lean_object* v_res_539_; 
v_t_boxed_538_ = lean_unbox(v_t_535_);
v_res_539_ = l_Std_Time_ZoneId_short_elim(v_motive_534_, v_t_boxed_538_, v_h_536_, v_short_537_);
lean_dec(v_short_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg(lean_object* v_full_540_){
_start:
{
lean_inc(v_full_540_);
return v_full_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg___boxed(lean_object* v_full_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_Time_ZoneId_full_elim___redArg(v_full_541_);
lean_dec(v_full_541_);
return v_res_542_;
}
}
lean_object* l_Std_Time_ZoneId_full_elim(lean_object* v_motive_543_, uint8_t v_t_544_, lean_object* v_h_545_, lean_object* v_full_546_){
_start:
{
lean_inc(v_full_546_);
return v_full_546_;
}
}
LEAN_EXPORT void l_Std_Time_ZoneId_full_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_544_ = stack[1].m_num;
lean_object* v_full_546_ = stack[3].m_obj;
lean_object* v_res_547_;
v_res_547_ = l_Std_Time_ZoneId_full_elim(lean_box(0), v_t_544_, lean_box(0), v_full_546_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___boxed(lean_object* v_motive_548_, lean_object* v_t_549_, lean_object* v_h_550_, lean_object* v_full_551_){
_start:
{
uint8_t v_t_boxed_552_; lean_object* v_res_553_; 
v_t_boxed_552_ = lean_unbox(v_t_549_);
v_res_553_ = l_Std_Time_ZoneId_full_elim(v_motive_548_, v_t_boxed_552_, v_h_550_, v_full_551_);
lean_dec(v_full_551_);
return v_res_553_;
}
}
lean_object* l_Std_Time_instReprZoneId_repr(uint8_t v_x_563_, lean_object* v_prec_564_){
_start:
{
lean_object* v___y_566_; lean_object* v___y_573_; lean_object* v___y_580_; 
switch(v_x_563_)
{
case 0:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1024u);
v___x_587_ = lean_nat_dec_le(v___x_586_, v_prec_564_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_566_ = v___x_588_;
goto v___jp_565_;
}
else
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_566_ = v___x_589_;
goto v___jp_565_;
}
}
case 1:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(1024u);
v___x_591_ = lean_nat_dec_le(v___x_590_, v_prec_564_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_573_ = v___x_592_;
goto v___jp_572_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_573_ = v___x_593_;
goto v___jp_572_;
}
}
default: 
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(1024u);
v___x_595_ = lean_nat_dec_le(v___x_594_, v_prec_564_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_580_ = v___x_596_;
goto v___jp_579_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_580_ = v___x_597_;
goto v___jp_579_;
}
}
}
v___jp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_567_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__1));
lean_inc(v___y_566_);
v___x_568_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_568_, 0, v___y_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = 0;
v___x_570_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*1, v___x_569_);
v___x_571_ = l_Repr_addAppParen(v___x_570_, v_prec_564_);
return v___x_571_;
}
v___jp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_574_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__3));
lean_inc(v___y_573_);
v___x_575_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_575_, 0, v___y_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = 0;
v___x_577_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*1, v___x_576_);
v___x_578_ = l_Repr_addAppParen(v___x_577_, v_prec_564_);
return v___x_578_;
}
v___jp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_581_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__5));
lean_inc(v___y_580_);
v___x_582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_582_, 0, v___y_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = 0;
v___x_584_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*1, v___x_583_);
v___x_585_ = l_Repr_addAppParen(v___x_584_, v_prec_564_);
return v___x_585_;
}
}
}
LEAN_EXPORT void l_Std_Time_instReprZoneId_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_563_ = stack[0].m_num;
lean_object* v_prec_564_ = stack[1].m_obj;
lean_object* v_res_598_;
v_res_598_ = l_Std_Time_instReprZoneId_repr(v_x_563_, v_prec_564_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr___boxed(lean_object* v_x_599_, lean_object* v_prec_600_){
_start:
{
uint8_t v_x_167__boxed_601_; lean_object* v_res_602_; 
v_x_167__boxed_601_ = lean_unbox(v_x_599_);
v_res_602_ = l_Std_Time_instReprZoneId_repr(v_x_167__boxed_601_, v_prec_600_);
lean_dec(v_prec_600_);
return v_res_602_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneId_default(void){
_start:
{
uint8_t v___x_605_; 
v___x_605_ = 0;
return v___x_605_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneId(void){
_start:
{
uint8_t v___x_606_; 
v___x_606_ = 0;
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify(lean_object* v_num_616_){
_start:
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_dec_eq(v_num_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_unsigned_to_nat(2u);
v___x_620_ = lean_nat_dec_eq(v_num_616_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(4u);
v___x_622_ = lean_nat_dec_eq(v_num_616_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
v___x_623_ = lean_box(0);
return v___x_623_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__0));
return v___x_624_;
}
}
else
{
lean_object* v___x_625_; 
v___x_625_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__1));
return v___x_625_;
}
}
else
{
lean_object* v___x_626_; 
v___x_626_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__2));
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify___boxed(lean_object* v_num_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_Time_ZoneId_classify(v_num_627_);
lean_dec(v_num_627_);
return v_res_628_;
}
}
lean_object* l_Std_Time_ZoneName_ctorIdx___impl(uint8_t v_x_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_box(v_x_629_);
v___x_631_ = lean_obj_tag_nat(v___x_630_);
lean_dec(v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT void l_Std_Time_ZoneName_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_629_ = stack[0].m_num;
lean_object* v_res_632_;
v_res_632_ = l_Std_Time_ZoneName_ctorIdx___impl(v_x_629_);
stack->m_obj
 = v_res_632_;
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx___impl___boxed(lean_object* v_x_633_){
_start:
{
uint8_t v_x_4__boxed_634_; lean_object* v_res_635_; 
v_x_4__boxed_634_ = lean_unbox(v_x_633_);
v_res_635_ = l_Std_Time_ZoneName_ctorIdx___impl(v_x_4__boxed_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg(lean_object* v_k_636_){
_start:
{
lean_inc(v_k_636_);
return v_k_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg___boxed(lean_object* v_k_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_Time_ZoneName_ctorElim___redArg(v_k_637_);
lean_dec(v_k_637_);
return v_res_638_;
}
}
lean_object* l_Std_Time_ZoneName_ctorElim(lean_object* v_motive_639_, lean_object* v_ctorIdx_640_, uint8_t v_t_641_, lean_object* v_h_642_, lean_object* v_k_643_){
_start:
{
lean_inc(v_k_643_);
return v_k_643_;
}
}
LEAN_EXPORT void l_Std_Time_ZoneName_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_640_ = stack[1].m_obj;
uint8_t v_t_641_ = stack[2].m_num;
lean_object* v_k_643_ = stack[4].m_obj;
lean_object* v_res_644_;
v_res_644_ = l_Std_Time_ZoneName_ctorElim(lean_box(0), v_ctorIdx_640_, v_t_641_, lean_box(0), v_k_643_);
stack->m_obj
 = v_res_644_;
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___boxed(lean_object* v_motive_645_, lean_object* v_ctorIdx_646_, lean_object* v_t_647_, lean_object* v_h_648_, lean_object* v_k_649_){
_start:
{
uint8_t v_t_boxed_650_; lean_object* v_res_651_; 
v_t_boxed_650_ = lean_unbox(v_t_647_);
v_res_651_ = l_Std_Time_ZoneName_ctorElim(v_motive_645_, v_ctorIdx_646_, v_t_boxed_650_, v_h_648_, v_k_649_);
lean_dec(v_k_649_);
lean_dec(v_ctorIdx_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg(lean_object* v_short_652_){
_start:
{
lean_inc(v_short_652_);
return v_short_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg___boxed(lean_object* v_short_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Time_ZoneName_short_elim___redArg(v_short_653_);
lean_dec(v_short_653_);
return v_res_654_;
}
}
lean_object* l_Std_Time_ZoneName_short_elim(lean_object* v_motive_655_, uint8_t v_t_656_, lean_object* v_h_657_, lean_object* v_short_658_){
_start:
{
lean_inc(v_short_658_);
return v_short_658_;
}
}
LEAN_EXPORT void l_Std_Time_ZoneName_short_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_656_ = stack[1].m_num;
lean_object* v_short_658_ = stack[3].m_obj;
lean_object* v_res_659_;
v_res_659_ = l_Std_Time_ZoneName_short_elim(lean_box(0), v_t_656_, lean_box(0), v_short_658_);
stack->m_obj
 = v_res_659_;
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___boxed(lean_object* v_motive_660_, lean_object* v_t_661_, lean_object* v_h_662_, lean_object* v_short_663_){
_start:
{
uint8_t v_t_boxed_664_; lean_object* v_res_665_; 
v_t_boxed_664_ = lean_unbox(v_t_661_);
v_res_665_ = l_Std_Time_ZoneName_short_elim(v_motive_660_, v_t_boxed_664_, v_h_662_, v_short_663_);
lean_dec(v_short_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg(lean_object* v_full_666_){
_start:
{
lean_inc(v_full_666_);
return v_full_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg___boxed(lean_object* v_full_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_Time_ZoneName_full_elim___redArg(v_full_667_);
lean_dec(v_full_667_);
return v_res_668_;
}
}
lean_object* l_Std_Time_ZoneName_full_elim(lean_object* v_motive_669_, uint8_t v_t_670_, lean_object* v_h_671_, lean_object* v_full_672_){
_start:
{
lean_inc(v_full_672_);
return v_full_672_;
}
}
LEAN_EXPORT void l_Std_Time_ZoneName_full_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_670_ = stack[1].m_num;
lean_object* v_full_672_ = stack[3].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_Std_Time_ZoneName_full_elim(lean_box(0), v_t_670_, lean_box(0), v_full_672_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___boxed(lean_object* v_motive_674_, lean_object* v_t_675_, lean_object* v_h_676_, lean_object* v_full_677_){
_start:
{
uint8_t v_t_boxed_678_; lean_object* v_res_679_; 
v_t_boxed_678_ = lean_unbox(v_t_675_);
v_res_679_ = l_Std_Time_ZoneName_full_elim(v_motive_674_, v_t_boxed_678_, v_h_676_, v_full_677_);
lean_dec(v_full_677_);
return v_res_679_;
}
}
lean_object* l_Std_Time_instReprZoneName_repr(uint8_t v_x_686_, lean_object* v_prec_687_){
_start:
{
lean_object* v___y_689_; lean_object* v___y_696_; 
if (v_x_686_ == 0)
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(1024u);
v___x_703_ = lean_nat_dec_le(v___x_702_, v_prec_687_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_689_ = v___x_704_;
goto v___jp_688_;
}
else
{
lean_object* v___x_705_; 
v___x_705_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_689_ = v___x_705_;
goto v___jp_688_;
}
}
else
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_unsigned_to_nat(1024u);
v___x_707_ = lean_nat_dec_le(v___x_706_, v_prec_687_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_696_ = v___x_708_;
goto v___jp_695_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_696_ = v___x_709_;
goto v___jp_695_;
}
}
v___jp_688_:
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_690_ = ((lean_object*)(l_Std_Time_instReprZoneName_repr___closed__1));
lean_inc(v___y_689_);
v___x_691_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_691_, 0, v___y_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = 0;
v___x_693_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*1, v___x_692_);
v___x_694_ = l_Repr_addAppParen(v___x_693_, v_prec_687_);
return v___x_694_;
}
v___jp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_697_ = ((lean_object*)(l_Std_Time_instReprZoneName_repr___closed__3));
lean_inc(v___y_696_);
v___x_698_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_698_, 0, v___y_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = 0;
v___x_700_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*1, v___x_699_);
v___x_701_ = l_Repr_addAppParen(v___x_700_, v_prec_687_);
return v___x_701_;
}
}
}
LEAN_EXPORT void l_Std_Time_instReprZoneName_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_686_ = stack[0].m_num;
lean_object* v_prec_687_ = stack[1].m_obj;
lean_object* v_res_710_;
v_res_710_ = l_Std_Time_instReprZoneName_repr(v_x_686_, v_prec_687_);
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr___boxed(lean_object* v_x_711_, lean_object* v_prec_712_){
_start:
{
uint8_t v_x_113__boxed_713_; lean_object* v_res_714_; 
v_x_113__boxed_713_ = lean_unbox(v_x_711_);
v_res_714_ = l_Std_Time_instReprZoneName_repr(v_x_113__boxed_713_, v_prec_712_);
lean_dec(v_prec_712_);
return v_res_714_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneName_default(void){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = 0;
return v___x_717_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneName(void){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = 0;
return v___x_718_;
}
}
lean_object* l_Std_Time_ZoneName_classify(uint32_t v_letter_725_, lean_object* v_num_726_){
_start:
{
uint32_t v___x_727_; uint8_t v___x_728_; 
v___x_727_ = 122;
v___x_728_ = lean_uint32_dec_eq(v_letter_725_, v___x_727_);
if (v___x_728_ == 0)
{
uint32_t v___x_729_; uint8_t v___x_730_; 
v___x_729_ = 118;
v___x_730_ = lean_uint32_dec_eq(v_letter_725_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(0);
return v___x_731_;
}
else
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_dec_eq(v_num_726_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(4u);
v___x_735_ = lean_nat_dec_eq(v_num_726_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_box(0);
return v___x_736_;
}
else
{
lean_object* v___x_737_; 
v___x_737_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__0));
return v___x_737_;
}
}
else
{
lean_object* v___x_738_; 
v___x_738_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__1));
return v___x_738_;
}
}
}
else
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_unsigned_to_nat(4u);
v___x_740_ = lean_nat_dec_lt(v_num_726_, v___x_739_);
if (v___x_740_ == 0)
{
uint8_t v___x_741_; 
v___x_741_ = lean_nat_dec_eq(v_num_726_, v___x_739_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
v___x_742_ = lean_box(0);
return v___x_742_;
}
else
{
lean_object* v___x_743_; 
v___x_743_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__0));
return v___x_743_;
}
}
else
{
lean_object* v___x_744_; 
v___x_744_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__1));
return v___x_744_;
}
}
}
}
LEAN_EXPORT void l_Std_Time_ZoneName_classify_0interp(lean_interpreter_value* stack)
{
uint32_t v_letter_725_ = stack[0].m_num;
lean_object* v_num_726_ = stack[1].m_obj;
lean_object* v_res_745_;
v_res_745_ = l_Std_Time_ZoneName_classify(v_letter_725_, v_num_726_);
stack->m_obj
 = v_res_745_;
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify___boxed(lean_object* v_letter_746_, lean_object* v_num_747_){
_start:
{
uint32_t v_letter_boxed_748_; lean_object* v_res_749_; 
v_letter_boxed_748_ = lean_unbox_uint32(v_letter_746_);
lean_dec(v_letter_746_);
v_res_749_ = l_Std_Time_ZoneName_classify(v_letter_boxed_748_, v_num_747_);
lean_dec(v_num_747_);
return v_res_749_;
}
}
lean_object* l_Std_Time_OffsetX_ctorIdx___impl(uint8_t v_x_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_box(v_x_750_);
v___x_752_ = lean_obj_tag_nat(v___x_751_);
lean_dec(v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetX_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_750_ = stack[0].m_num;
lean_object* v_res_753_;
v_res_753_ = l_Std_Time_OffsetX_ctorIdx___impl(v_x_750_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx___impl___boxed(lean_object* v_x_754_){
_start:
{
uint8_t v_x_4__boxed_755_; lean_object* v_res_756_; 
v_x_4__boxed_755_ = lean_unbox(v_x_754_);
v_res_756_ = l_Std_Time_OffsetX_ctorIdx___impl(v_x_4__boxed_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg(lean_object* v_k_757_){
_start:
{
lean_inc(v_k_757_);
return v_k_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg___boxed(lean_object* v_k_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_Time_OffsetX_ctorElim___redArg(v_k_758_);
lean_dec(v_k_758_);
return v_res_759_;
}
}
lean_object* l_Std_Time_OffsetX_ctorElim(lean_object* v_motive_760_, lean_object* v_ctorIdx_761_, uint8_t v_t_762_, lean_object* v_h_763_, lean_object* v_k_764_){
_start:
{
lean_inc(v_k_764_);
return v_k_764_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetX_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_761_ = stack[1].m_obj;
uint8_t v_t_762_ = stack[2].m_num;
lean_object* v_k_764_ = stack[4].m_obj;
lean_object* v_res_765_;
v_res_765_ = l_Std_Time_OffsetX_ctorElim(lean_box(0), v_ctorIdx_761_, v_t_762_, lean_box(0), v_k_764_);
stack->m_obj
 = v_res_765_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___boxed(lean_object* v_motive_766_, lean_object* v_ctorIdx_767_, lean_object* v_t_768_, lean_object* v_h_769_, lean_object* v_k_770_){
_start:
{
uint8_t v_t_boxed_771_; lean_object* v_res_772_; 
v_t_boxed_771_ = lean_unbox(v_t_768_);
v_res_772_ = l_Std_Time_OffsetX_ctorElim(v_motive_766_, v_ctorIdx_767_, v_t_boxed_771_, v_h_769_, v_k_770_);
lean_dec(v_k_770_);
lean_dec(v_ctorIdx_767_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg(lean_object* v_hour_773_){
_start:
{
lean_inc(v_hour_773_);
return v_hour_773_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg___boxed(lean_object* v_hour_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_Time_OffsetX_hour_elim___redArg(v_hour_774_);
lean_dec(v_hour_774_);
return v_res_775_;
}
}
lean_object* l_Std_Time_OffsetX_hour_elim(lean_object* v_motive_776_, uint8_t v_t_777_, lean_object* v_h_778_, lean_object* v_hour_779_){
_start:
{
lean_inc(v_hour_779_);
return v_hour_779_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetX_hour_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_777_ = stack[1].m_num;
lean_object* v_hour_779_ = stack[3].m_obj;
lean_object* v_res_780_;
v_res_780_ = l_Std_Time_OffsetX_hour_elim(lean_box(0), v_t_777_, lean_box(0), v_hour_779_);
stack->m_obj
 = v_res_780_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___boxed(lean_object* v_motive_781_, lean_object* v_t_782_, lean_object* v_h_783_, lean_object* v_hour_784_){
_start:
{
uint8_t v_t_boxed_785_; lean_object* v_res_786_; 
v_t_boxed_785_ = lean_unbox(v_t_782_);
v_res_786_ = l_Std_Time_OffsetX_hour_elim(v_motive_781_, v_t_boxed_785_, v_h_783_, v_hour_784_);
lean_dec(v_hour_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg(lean_object* v_hourMinute_787_){
_start:
{
lean_inc(v_hourMinute_787_);
return v_hourMinute_787_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg___boxed(lean_object* v_hourMinute_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_Time_OffsetX_hourMinute_elim___redArg(v_hourMinute_788_);
lean_dec(v_hourMinute_788_);
return v_res_789_;
}
}
lean_object* l_Std_Time_OffsetX_hourMinute_elim(lean_object* v_motive_790_, uint8_t v_t_791_, lean_object* v_h_792_, lean_object* v_hourMinute_793_){
_start:
{
lean_inc(v_hourMinute_793_);
return v_hourMinute_793_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetX_hourMinute_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_791_ = stack[1].m_num;
lean_object* v_hourMinute_793_ = stack[3].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Std_Time_OffsetX_hourMinute_elim(lean_box(0), v_t_791_, lean_box(0), v_hourMinute_793_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___boxed(lean_object* v_motive_795_, lean_object* v_t_796_, lean_object* v_h_797_, lean_object* v_hourMinute_798_){
_start:
{
uint8_t v_t_boxed_799_; lean_object* v_res_800_; 
v_t_boxed_799_ = lean_unbox(v_t_796_);
v_res_800_ = l_Std_Time_OffsetX_hourMinute_elim(v_motive_795_, v_t_boxed_799_, v_h_797_, v_hourMinute_798_);
lean_dec(v_hourMinute_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(lean_object* v_hourMinuteColon_801_){
_start:
{
lean_inc(v_hourMinuteColon_801_);
return v_hourMinuteColon_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg___boxed(lean_object* v_hourMinuteColon_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(v_hourMinuteColon_802_);
lean_dec(v_hourMinuteColon_802_);
return v_res_803_;
}
}
lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim(lean_object* v_motive_804_, uint8_t v_t_805_, lean_object* v_h_806_, lean_object* v_hourMinuteColon_807_){
_start:
{
lean_inc(v_hourMinuteColon_807_);
return v_hourMinuteColon_807_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetX_hourMinuteColon_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_805_ = stack[1].m_num;
lean_object* v_hourMinuteColon_807_ = stack[3].m_obj;
lean_object* v_res_808_;
v_res_808_ = l_Std_Time_OffsetX_hourMinuteColon_elim(lean_box(0), v_t_805_, lean_box(0), v_hourMinuteColon_807_);
stack->m_obj
 = v_res_808_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___boxed(lean_object* v_motive_809_, lean_object* v_t_810_, lean_object* v_h_811_, lean_object* v_hourMinuteColon_812_){
_start:
{
uint8_t v_t_boxed_813_; lean_object* v_res_814_; 
v_t_boxed_813_ = lean_unbox(v_t_810_);
v_res_814_ = l_Std_Time_OffsetX_hourMinuteColon_elim(v_motive_809_, v_t_boxed_813_, v_h_811_, v_hourMinuteColon_812_);
lean_dec(v_hourMinuteColon_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(lean_object* v_hourMinuteSecond_815_){
_start:
{
lean_inc(v_hourMinuteSecond_815_);
return v_hourMinuteSecond_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg___boxed(lean_object* v_hourMinuteSecond_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(v_hourMinuteSecond_816_);
lean_dec(v_hourMinuteSecond_816_);
return v_res_817_;
}
}
lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim(lean_object* v_motive_818_, uint8_t v_t_819_, lean_object* v_h_820_, lean_object* v_hourMinuteSecond_821_){
_start:
{
lean_inc(v_hourMinuteSecond_821_);
return v_hourMinuteSecond_821_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetX_hourMinuteSecond_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_819_ = stack[1].m_num;
lean_object* v_hourMinuteSecond_821_ = stack[3].m_obj;
lean_object* v_res_822_;
v_res_822_ = l_Std_Time_OffsetX_hourMinuteSecond_elim(lean_box(0), v_t_819_, lean_box(0), v_hourMinuteSecond_821_);
stack->m_obj
 = v_res_822_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___boxed(lean_object* v_motive_823_, lean_object* v_t_824_, lean_object* v_h_825_, lean_object* v_hourMinuteSecond_826_){
_start:
{
uint8_t v_t_boxed_827_; lean_object* v_res_828_; 
v_t_boxed_827_ = lean_unbox(v_t_824_);
v_res_828_ = l_Std_Time_OffsetX_hourMinuteSecond_elim(v_motive_823_, v_t_boxed_827_, v_h_825_, v_hourMinuteSecond_826_);
lean_dec(v_hourMinuteSecond_826_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(lean_object* v_hourMinuteSecondColon_829_){
_start:
{
lean_inc(v_hourMinuteSecondColon_829_);
return v_hourMinuteSecondColon_829_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg___boxed(lean_object* v_hourMinuteSecondColon_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(v_hourMinuteSecondColon_830_);
lean_dec(v_hourMinuteSecondColon_830_);
return v_res_831_;
}
}
lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim(lean_object* v_motive_832_, uint8_t v_t_833_, lean_object* v_h_834_, lean_object* v_hourMinuteSecondColon_835_){
_start:
{
lean_inc(v_hourMinuteSecondColon_835_);
return v_hourMinuteSecondColon_835_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetX_hourMinuteSecondColon_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_833_ = stack[1].m_num;
lean_object* v_hourMinuteSecondColon_835_ = stack[3].m_obj;
lean_object* v_res_836_;
v_res_836_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim(lean_box(0), v_t_833_, lean_box(0), v_hourMinuteSecondColon_835_);
stack->m_obj
 = v_res_836_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___boxed(lean_object* v_motive_837_, lean_object* v_t_838_, lean_object* v_h_839_, lean_object* v_hourMinuteSecondColon_840_){
_start:
{
uint8_t v_t_boxed_841_; lean_object* v_res_842_; 
v_t_boxed_841_ = lean_unbox(v_t_838_);
v_res_842_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim(v_motive_837_, v_t_boxed_841_, v_h_839_, v_hourMinuteSecondColon_840_);
lean_dec(v_hourMinuteSecondColon_840_);
return v_res_842_;
}
}
lean_object* l_Std_Time_instReprOffsetX_repr(uint8_t v_x_858_, lean_object* v_prec_859_){
_start:
{
lean_object* v___y_861_; lean_object* v___y_868_; lean_object* v___y_875_; lean_object* v___y_882_; lean_object* v___y_889_; 
switch(v_x_858_)
{
case 0:
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(1024u);
v___x_896_ = lean_nat_dec_le(v___x_895_, v_prec_859_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_861_ = v___x_897_;
goto v___jp_860_;
}
else
{
lean_object* v___x_898_; 
v___x_898_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_861_ = v___x_898_;
goto v___jp_860_;
}
}
case 1:
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_unsigned_to_nat(1024u);
v___x_900_ = lean_nat_dec_le(v___x_899_, v_prec_859_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
v___x_901_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_868_ = v___x_901_;
goto v___jp_867_;
}
else
{
lean_object* v___x_902_; 
v___x_902_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_868_ = v___x_902_;
goto v___jp_867_;
}
}
case 2:
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(1024u);
v___x_904_ = lean_nat_dec_le(v___x_903_, v_prec_859_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
v___x_905_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_875_ = v___x_905_;
goto v___jp_874_;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_875_ = v___x_906_;
goto v___jp_874_;
}
}
case 3:
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_unsigned_to_nat(1024u);
v___x_908_ = lean_nat_dec_le(v___x_907_, v_prec_859_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_882_ = v___x_909_;
goto v___jp_881_;
}
else
{
lean_object* v___x_910_; 
v___x_910_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_882_ = v___x_910_;
goto v___jp_881_;
}
}
default: 
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(1024u);
v___x_912_ = lean_nat_dec_le(v___x_911_, v_prec_859_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
v___x_913_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_889_ = v___x_913_;
goto v___jp_888_;
}
else
{
lean_object* v___x_914_; 
v___x_914_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_889_ = v___x_914_;
goto v___jp_888_;
}
}
}
v___jp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_862_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__1));
lean_inc(v___y_861_);
v___x_863_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_863_, 0, v___y_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = 0;
v___x_865_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*1, v___x_864_);
v___x_866_ = l_Repr_addAppParen(v___x_865_, v_prec_859_);
return v___x_866_;
}
v___jp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_869_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__3));
lean_inc(v___y_868_);
v___x_870_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_870_, 0, v___y_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = 0;
v___x_872_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*1, v___x_871_);
v___x_873_ = l_Repr_addAppParen(v___x_872_, v_prec_859_);
return v___x_873_;
}
v___jp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_876_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__5));
lean_inc(v___y_875_);
v___x_877_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_877_, 0, v___y_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = 0;
v___x_879_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*1, v___x_878_);
v___x_880_ = l_Repr_addAppParen(v___x_879_, v_prec_859_);
return v___x_880_;
}
v___jp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_883_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__7));
lean_inc(v___y_882_);
v___x_884_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_884_, 0, v___y_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = 0;
v___x_886_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1, v___x_885_);
v___x_887_ = l_Repr_addAppParen(v___x_886_, v_prec_859_);
return v___x_887_;
}
v___jp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_890_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__9));
lean_inc(v___y_889_);
v___x_891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_891_, 0, v___y_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = 0;
v___x_893_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*1, v___x_892_);
v___x_894_ = l_Repr_addAppParen(v___x_893_, v_prec_859_);
return v___x_894_;
}
}
}
LEAN_EXPORT void l_Std_Time_instReprOffsetX_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_858_ = stack[0].m_num;
lean_object* v_prec_859_ = stack[1].m_obj;
lean_object* v_res_915_;
v_res_915_ = l_Std_Time_instReprOffsetX_repr(v_x_858_, v_prec_859_);
stack->m_obj
 = v_res_915_;
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr___boxed(lean_object* v_x_916_, lean_object* v_prec_917_){
_start:
{
uint8_t v_x_275__boxed_918_; lean_object* v_res_919_; 
v_x_275__boxed_918_ = lean_unbox(v_x_916_);
v_res_919_ = l_Std_Time_instReprOffsetX_repr(v_x_275__boxed_918_, v_prec_917_);
lean_dec(v_prec_917_);
return v_res_919_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetX_default(void){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = 0;
return v___x_922_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetX(void){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = 0;
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify(lean_object* v_num_939_){
_start:
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_nat_dec_eq(v_num_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(2u);
v___x_943_ = lean_nat_dec_eq(v_num_939_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(3u);
v___x_945_ = lean_nat_dec_eq(v_num_939_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_unsigned_to_nat(4u);
v___x_947_ = lean_nat_dec_eq(v_num_939_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_unsigned_to_nat(5u);
v___x_949_ = lean_nat_dec_eq(v_num_939_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
v___x_950_ = lean_box(0);
return v___x_950_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__0));
return v___x_951_;
}
}
else
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__1));
return v___x_952_;
}
}
else
{
lean_object* v___x_953_; 
v___x_953_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__2));
return v___x_953_;
}
}
else
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__3));
return v___x_954_;
}
}
else
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__4));
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify___boxed(lean_object* v_num_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Std_Time_OffsetX_classify(v_num_956_);
lean_dec(v_num_956_);
return v_res_957_;
}
}
lean_object* l_Std_Time_OffsetO_ctorIdx___impl(uint8_t v_x_958_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_box(v_x_958_);
v___x_960_ = lean_obj_tag_nat(v___x_959_);
lean_dec(v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetO_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_958_ = stack[0].m_num;
lean_object* v_res_961_;
v_res_961_ = l_Std_Time_OffsetO_ctorIdx___impl(v_x_958_);
stack->m_obj
 = v_res_961_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx___impl___boxed(lean_object* v_x_962_){
_start:
{
uint8_t v_x_4__boxed_963_; lean_object* v_res_964_; 
v_x_4__boxed_963_ = lean_unbox(v_x_962_);
v_res_964_ = l_Std_Time_OffsetO_ctorIdx___impl(v_x_4__boxed_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg(lean_object* v_k_965_){
_start:
{
lean_inc(v_k_965_);
return v_k_965_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg___boxed(lean_object* v_k_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Std_Time_OffsetO_ctorElim___redArg(v_k_966_);
lean_dec(v_k_966_);
return v_res_967_;
}
}
lean_object* l_Std_Time_OffsetO_ctorElim(lean_object* v_motive_968_, lean_object* v_ctorIdx_969_, uint8_t v_t_970_, lean_object* v_h_971_, lean_object* v_k_972_){
_start:
{
lean_inc(v_k_972_);
return v_k_972_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetO_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_969_ = stack[1].m_obj;
uint8_t v_t_970_ = stack[2].m_num;
lean_object* v_k_972_ = stack[4].m_obj;
lean_object* v_res_973_;
v_res_973_ = l_Std_Time_OffsetO_ctorElim(lean_box(0), v_ctorIdx_969_, v_t_970_, lean_box(0), v_k_972_);
stack->m_obj
 = v_res_973_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___boxed(lean_object* v_motive_974_, lean_object* v_ctorIdx_975_, lean_object* v_t_976_, lean_object* v_h_977_, lean_object* v_k_978_){
_start:
{
uint8_t v_t_boxed_979_; lean_object* v_res_980_; 
v_t_boxed_979_ = lean_unbox(v_t_976_);
v_res_980_ = l_Std_Time_OffsetO_ctorElim(v_motive_974_, v_ctorIdx_975_, v_t_boxed_979_, v_h_977_, v_k_978_);
lean_dec(v_k_978_);
lean_dec(v_ctorIdx_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg(lean_object* v_short_981_){
_start:
{
lean_inc(v_short_981_);
return v_short_981_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg___boxed(lean_object* v_short_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Std_Time_OffsetO_short_elim___redArg(v_short_982_);
lean_dec(v_short_982_);
return v_res_983_;
}
}
lean_object* l_Std_Time_OffsetO_short_elim(lean_object* v_motive_984_, uint8_t v_t_985_, lean_object* v_h_986_, lean_object* v_short_987_){
_start:
{
lean_inc(v_short_987_);
return v_short_987_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetO_short_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_985_ = stack[1].m_num;
lean_object* v_short_987_ = stack[3].m_obj;
lean_object* v_res_988_;
v_res_988_ = l_Std_Time_OffsetO_short_elim(lean_box(0), v_t_985_, lean_box(0), v_short_987_);
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___boxed(lean_object* v_motive_989_, lean_object* v_t_990_, lean_object* v_h_991_, lean_object* v_short_992_){
_start:
{
uint8_t v_t_boxed_993_; lean_object* v_res_994_; 
v_t_boxed_993_ = lean_unbox(v_t_990_);
v_res_994_ = l_Std_Time_OffsetO_short_elim(v_motive_989_, v_t_boxed_993_, v_h_991_, v_short_992_);
lean_dec(v_short_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg(lean_object* v_full_995_){
_start:
{
lean_inc(v_full_995_);
return v_full_995_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg___boxed(lean_object* v_full_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_Time_OffsetO_full_elim___redArg(v_full_996_);
lean_dec(v_full_996_);
return v_res_997_;
}
}
lean_object* l_Std_Time_OffsetO_full_elim(lean_object* v_motive_998_, uint8_t v_t_999_, lean_object* v_h_1000_, lean_object* v_full_1001_){
_start:
{
lean_inc(v_full_1001_);
return v_full_1001_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetO_full_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_999_ = stack[1].m_num;
lean_object* v_full_1001_ = stack[3].m_obj;
lean_object* v_res_1002_;
v_res_1002_ = l_Std_Time_OffsetO_full_elim(lean_box(0), v_t_999_, lean_box(0), v_full_1001_);
stack->m_obj
 = v_res_1002_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___boxed(lean_object* v_motive_1003_, lean_object* v_t_1004_, lean_object* v_h_1005_, lean_object* v_full_1006_){
_start:
{
uint8_t v_t_boxed_1007_; lean_object* v_res_1008_; 
v_t_boxed_1007_ = lean_unbox(v_t_1004_);
v_res_1008_ = l_Std_Time_OffsetO_full_elim(v_motive_1003_, v_t_boxed_1007_, v_h_1005_, v_full_1006_);
lean_dec(v_full_1006_);
return v_res_1008_;
}
}
lean_object* l_Std_Time_instReprOffsetO_repr(uint8_t v_x_1015_, lean_object* v_prec_1016_){
_start:
{
lean_object* v___y_1018_; lean_object* v___y_1025_; 
if (v_x_1015_ == 0)
{
lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1031_ = lean_unsigned_to_nat(1024u);
v___x_1032_ = lean_nat_dec_le(v___x_1031_, v_prec_1016_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1018_ = v___x_1033_;
goto v___jp_1017_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1018_ = v___x_1034_;
goto v___jp_1017_;
}
}
else
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(1024u);
v___x_1036_ = lean_nat_dec_le(v___x_1035_, v_prec_1016_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1025_ = v___x_1037_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1025_ = v___x_1038_;
goto v___jp_1024_;
}
}
v___jp_1017_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1019_ = ((lean_object*)(l_Std_Time_instReprOffsetO_repr___closed__1));
lean_inc(v___y_1018_);
v___x_1020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___y_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = 0;
v___x_1022_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set_uint8(v___x_1022_, sizeof(void*)*1, v___x_1021_);
v___x_1023_ = l_Repr_addAppParen(v___x_1022_, v_prec_1016_);
return v___x_1023_;
}
v___jp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1026_ = ((lean_object*)(l_Std_Time_instReprOffsetO_repr___closed__3));
lean_inc(v___y_1025_);
v___x_1027_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___y_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = 0;
v___x_1029_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set_uint8(v___x_1029_, sizeof(void*)*1, v___x_1028_);
v___x_1030_ = l_Repr_addAppParen(v___x_1029_, v_prec_1016_);
return v___x_1030_;
}
}
}
LEAN_EXPORT void l_Std_Time_instReprOffsetO_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1015_ = stack[0].m_num;
lean_object* v_prec_1016_ = stack[1].m_obj;
lean_object* v_res_1039_;
v_res_1039_ = l_Std_Time_instReprOffsetO_repr(v_x_1015_, v_prec_1016_);
stack->m_obj
 = v_res_1039_;
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr___boxed(lean_object* v_x_1040_, lean_object* v_prec_1041_){
_start:
{
uint8_t v_x_113__boxed_1042_; lean_object* v_res_1043_; 
v_x_113__boxed_1042_ = lean_unbox(v_x_1040_);
v_res_1043_ = l_Std_Time_instReprOffsetO_repr(v_x_113__boxed_1042_, v_prec_1041_);
lean_dec(v_prec_1041_);
return v_res_1043_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetO_default(void){
_start:
{
uint8_t v___x_1046_; 
v___x_1046_ = 0;
return v___x_1046_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetO(void){
_start:
{
uint8_t v___x_1047_; 
v___x_1047_ = 0;
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify(lean_object* v_num_1054_){
_start:
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_dec_eq(v_num_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(4u);
v___x_1058_ = lean_nat_dec_eq(v_num_1054_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_box(0);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = ((lean_object*)(l_Std_Time_OffsetO_classify___closed__0));
return v___x_1060_;
}
}
else
{
lean_object* v___x_1061_; 
v___x_1061_ = ((lean_object*)(l_Std_Time_OffsetO_classify___closed__1));
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify___boxed(lean_object* v_num_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_Time_OffsetO_classify(v_num_1062_);
lean_dec(v_num_1062_);
return v_res_1063_;
}
}
lean_object* l_Std_Time_OffsetZ_ctorIdx___impl(uint8_t v_x_1064_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_box(v_x_1064_);
v___x_1066_ = lean_obj_tag_nat(v___x_1065_);
lean_dec(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetZ_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1064_ = stack[0].m_num;
lean_object* v_res_1067_;
v_res_1067_ = l_Std_Time_OffsetZ_ctorIdx___impl(v_x_1064_);
stack->m_obj
 = v_res_1067_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx___impl___boxed(lean_object* v_x_1068_){
_start:
{
uint8_t v_x_4__boxed_1069_; lean_object* v_res_1070_; 
v_x_4__boxed_1069_ = lean_unbox(v_x_1068_);
v_res_1070_ = l_Std_Time_OffsetZ_ctorIdx___impl(v_x_4__boxed_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg(lean_object* v_k_1071_){
_start:
{
lean_inc(v_k_1071_);
return v_k_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg___boxed(lean_object* v_k_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_Time_OffsetZ_ctorElim___redArg(v_k_1072_);
lean_dec(v_k_1072_);
return v_res_1073_;
}
}
lean_object* l_Std_Time_OffsetZ_ctorElim(lean_object* v_motive_1074_, lean_object* v_ctorIdx_1075_, uint8_t v_t_1076_, lean_object* v_h_1077_, lean_object* v_k_1078_){
_start:
{
lean_inc(v_k_1078_);
return v_k_1078_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetZ_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_1075_ = stack[1].m_obj;
uint8_t v_t_1076_ = stack[2].m_num;
lean_object* v_k_1078_ = stack[4].m_obj;
lean_object* v_res_1079_;
v_res_1079_ = l_Std_Time_OffsetZ_ctorElim(lean_box(0), v_ctorIdx_1075_, v_t_1076_, lean_box(0), v_k_1078_);
stack->m_obj
 = v_res_1079_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___boxed(lean_object* v_motive_1080_, lean_object* v_ctorIdx_1081_, lean_object* v_t_1082_, lean_object* v_h_1083_, lean_object* v_k_1084_){
_start:
{
uint8_t v_t_boxed_1085_; lean_object* v_res_1086_; 
v_t_boxed_1085_ = lean_unbox(v_t_1082_);
v_res_1086_ = l_Std_Time_OffsetZ_ctorElim(v_motive_1080_, v_ctorIdx_1081_, v_t_boxed_1085_, v_h_1083_, v_k_1084_);
lean_dec(v_k_1084_);
lean_dec(v_ctorIdx_1081_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg(lean_object* v_hourMinute_1087_){
_start:
{
lean_inc(v_hourMinute_1087_);
return v_hourMinute_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg___boxed(lean_object* v_hourMinute_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Std_Time_OffsetZ_hourMinute_elim___redArg(v_hourMinute_1088_);
lean_dec(v_hourMinute_1088_);
return v_res_1089_;
}
}
lean_object* l_Std_Time_OffsetZ_hourMinute_elim(lean_object* v_motive_1090_, uint8_t v_t_1091_, lean_object* v_h_1092_, lean_object* v_hourMinute_1093_){
_start:
{
lean_inc(v_hourMinute_1093_);
return v_hourMinute_1093_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetZ_hourMinute_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1091_ = stack[1].m_num;
lean_object* v_hourMinute_1093_ = stack[3].m_obj;
lean_object* v_res_1094_;
v_res_1094_ = l_Std_Time_OffsetZ_hourMinute_elim(lean_box(0), v_t_1091_, lean_box(0), v_hourMinute_1093_);
stack->m_obj
 = v_res_1094_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___boxed(lean_object* v_motive_1095_, lean_object* v_t_1096_, lean_object* v_h_1097_, lean_object* v_hourMinute_1098_){
_start:
{
uint8_t v_t_boxed_1099_; lean_object* v_res_1100_; 
v_t_boxed_1099_ = lean_unbox(v_t_1096_);
v_res_1100_ = l_Std_Time_OffsetZ_hourMinute_elim(v_motive_1095_, v_t_boxed_1099_, v_h_1097_, v_hourMinute_1098_);
lean_dec(v_hourMinute_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg(lean_object* v_full_1101_){
_start:
{
lean_inc(v_full_1101_);
return v_full_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg___boxed(lean_object* v_full_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_Time_OffsetZ_full_elim___redArg(v_full_1102_);
lean_dec(v_full_1102_);
return v_res_1103_;
}
}
lean_object* l_Std_Time_OffsetZ_full_elim(lean_object* v_motive_1104_, uint8_t v_t_1105_, lean_object* v_h_1106_, lean_object* v_full_1107_){
_start:
{
lean_inc(v_full_1107_);
return v_full_1107_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetZ_full_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1105_ = stack[1].m_num;
lean_object* v_full_1107_ = stack[3].m_obj;
lean_object* v_res_1108_;
v_res_1108_ = l_Std_Time_OffsetZ_full_elim(lean_box(0), v_t_1105_, lean_box(0), v_full_1107_);
stack->m_obj
 = v_res_1108_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___boxed(lean_object* v_motive_1109_, lean_object* v_t_1110_, lean_object* v_h_1111_, lean_object* v_full_1112_){
_start:
{
uint8_t v_t_boxed_1113_; lean_object* v_res_1114_; 
v_t_boxed_1113_ = lean_unbox(v_t_1110_);
v_res_1114_ = l_Std_Time_OffsetZ_full_elim(v_motive_1109_, v_t_boxed_1113_, v_h_1111_, v_full_1112_);
lean_dec(v_full_1112_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(lean_object* v_hourMinuteSecondColon_1115_){
_start:
{
lean_inc(v_hourMinuteSecondColon_1115_);
return v_hourMinuteSecondColon_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg___boxed(lean_object* v_hourMinuteSecondColon_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(v_hourMinuteSecondColon_1116_);
lean_dec(v_hourMinuteSecondColon_1116_);
return v_res_1117_;
}
}
lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(lean_object* v_motive_1118_, uint8_t v_t_1119_, lean_object* v_h_1120_, lean_object* v_hourMinuteSecondColon_1121_){
_start:
{
lean_inc(v_hourMinuteSecondColon_1121_);
return v_hourMinuteSecondColon_1121_;
}
}
LEAN_EXPORT void l_Std_Time_OffsetZ_hourMinuteSecondColon_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1119_ = stack[1].m_num;
lean_object* v_hourMinuteSecondColon_1121_ = stack[3].m_obj;
lean_object* v_res_1122_;
v_res_1122_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(lean_box(0), v_t_1119_, lean_box(0), v_hourMinuteSecondColon_1121_);
stack->m_obj
 = v_res_1122_;
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___boxed(lean_object* v_motive_1123_, lean_object* v_t_1124_, lean_object* v_h_1125_, lean_object* v_hourMinuteSecondColon_1126_){
_start:
{
uint8_t v_t_boxed_1127_; lean_object* v_res_1128_; 
v_t_boxed_1127_ = lean_unbox(v_t_1124_);
v_res_1128_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(v_motive_1123_, v_t_boxed_1127_, v_h_1125_, v_hourMinuteSecondColon_1126_);
lean_dec(v_hourMinuteSecondColon_1126_);
return v_res_1128_;
}
}
lean_object* l_Std_Time_instReprOffsetZ_repr(uint8_t v_x_1138_, lean_object* v_prec_1139_){
_start:
{
lean_object* v___y_1141_; lean_object* v___y_1148_; lean_object* v___y_1155_; 
switch(v_x_1138_)
{
case 0:
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = lean_unsigned_to_nat(1024u);
v___x_1162_ = lean_nat_dec_le(v___x_1161_, v_prec_1139_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1141_ = v___x_1163_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1141_ = v___x_1164_;
goto v___jp_1140_;
}
}
case 1:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(1024u);
v___x_1166_ = lean_nat_dec_le(v___x_1165_, v_prec_1139_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1148_ = v___x_1167_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1148_ = v___x_1168_;
goto v___jp_1147_;
}
}
default: 
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_unsigned_to_nat(1024u);
v___x_1170_ = lean_nat_dec_le(v___x_1169_, v_prec_1139_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1155_ = v___x_1171_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1155_ = v___x_1172_;
goto v___jp_1154_;
}
}
}
v___jp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1142_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__1));
lean_inc(v___y_1141_);
v___x_1143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___y_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = 0;
v___x_1145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*1, v___x_1144_);
v___x_1146_ = l_Repr_addAppParen(v___x_1145_, v_prec_1139_);
return v___x_1146_;
}
v___jp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1149_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__3));
lean_inc(v___y_1148_);
v___x_1150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___y_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = 0;
v___x_1152_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set_uint8(v___x_1152_, sizeof(void*)*1, v___x_1151_);
v___x_1153_ = l_Repr_addAppParen(v___x_1152_, v_prec_1139_);
return v___x_1153_;
}
v___jp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1156_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__5));
lean_inc(v___y_1155_);
v___x_1157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___y_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = 0;
v___x_1159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*1, v___x_1158_);
v___x_1160_ = l_Repr_addAppParen(v___x_1159_, v_prec_1139_);
return v___x_1160_;
}
}
}
LEAN_EXPORT void l_Std_Time_instReprOffsetZ_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1138_ = stack[0].m_num;
lean_object* v_prec_1139_ = stack[1].m_obj;
lean_object* v_res_1173_;
v_res_1173_ = l_Std_Time_instReprOffsetZ_repr(v_x_1138_, v_prec_1139_);
stack->m_obj
 = v_res_1173_;
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr___boxed(lean_object* v_x_1174_, lean_object* v_prec_1175_){
_start:
{
uint8_t v_x_167__boxed_1176_; lean_object* v_res_1177_; 
v_x_167__boxed_1176_ = lean_unbox(v_x_1174_);
v_res_1177_ = l_Std_Time_instReprOffsetZ_repr(v_x_167__boxed_1176_, v_prec_1175_);
lean_dec(v_prec_1175_);
return v_res_1177_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetZ_default(void){
_start:
{
uint8_t v___x_1180_; 
v___x_1180_ = 0;
return v___x_1180_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetZ(void){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = 0;
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify(lean_object* v_num_1191_){
_start:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_dec_eq(v_num_1191_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(2u);
v___x_1197_ = lean_nat_dec_eq(v_num_1191_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = lean_unsigned_to_nat(3u);
v___x_1199_ = lean_nat_dec_eq(v_num_1191_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = lean_unsigned_to_nat(4u);
v___x_1201_ = lean_nat_dec_eq(v_num_1191_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = lean_unsigned_to_nat(5u);
v___x_1203_ = lean_nat_dec_eq(v_num_1191_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_box(0);
return v___x_1204_;
}
else
{
lean_object* v___x_1205_; 
v___x_1205_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__1));
return v___x_1205_;
}
}
else
{
lean_object* v___x_1206_; 
v___x_1206_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__2));
return v___x_1206_;
}
}
else
{
goto v___jp_1192_;
}
}
else
{
goto v___jp_1192_;
}
}
else
{
goto v___jp_1192_;
}
v___jp_1192_:
{
lean_object* v___x_1193_; 
v___x_1193_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__0));
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify___boxed(lean_object* v_num_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Std_Time_OffsetZ_classify(v_num_1207_);
lean_dec(v_num_1207_);
return v_res_1208_;
}
}
lean_object* l_Std_Time_DayPeriod_ctorIdx___impl(uint8_t v_x_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_box(v_x_1209_);
v___x_1211_ = lean_obj_tag_nat(v___x_1210_);
lean_dec(v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT void l_Std_Time_DayPeriod_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1209_ = stack[0].m_num;
lean_object* v_res_1212_;
v_res_1212_ = l_Std_Time_DayPeriod_ctorIdx___impl(v_x_1209_);
stack->m_obj
 = v_res_1212_;
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx___impl___boxed(lean_object* v_x_1213_){
_start:
{
uint8_t v_x_4__boxed_1214_; lean_object* v_res_1215_; 
v_x_4__boxed_1214_ = lean_unbox(v_x_1213_);
v_res_1215_ = l_Std_Time_DayPeriod_ctorIdx___impl(v_x_4__boxed_1214_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg(lean_object* v_k_1216_){
_start:
{
lean_inc(v_k_1216_);
return v_k_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg___boxed(lean_object* v_k_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Std_Time_DayPeriod_ctorElim___redArg(v_k_1217_);
lean_dec(v_k_1217_);
return v_res_1218_;
}
}
lean_object* l_Std_Time_DayPeriod_ctorElim(lean_object* v_motive_1219_, lean_object* v_ctorIdx_1220_, uint8_t v_t_1221_, lean_object* v_h_1222_, lean_object* v_k_1223_){
_start:
{
lean_inc(v_k_1223_);
return v_k_1223_;
}
}
LEAN_EXPORT void l_Std_Time_DayPeriod_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_1220_ = stack[1].m_obj;
uint8_t v_t_1221_ = stack[2].m_num;
lean_object* v_k_1223_ = stack[4].m_obj;
lean_object* v_res_1224_;
v_res_1224_ = l_Std_Time_DayPeriod_ctorElim(lean_box(0), v_ctorIdx_1220_, v_t_1221_, lean_box(0), v_k_1223_);
stack->m_obj
 = v_res_1224_;
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___boxed(lean_object* v_motive_1225_, lean_object* v_ctorIdx_1226_, lean_object* v_t_1227_, lean_object* v_h_1228_, lean_object* v_k_1229_){
_start:
{
uint8_t v_t_boxed_1230_; lean_object* v_res_1231_; 
v_t_boxed_1230_ = lean_unbox(v_t_1227_);
v_res_1231_ = l_Std_Time_DayPeriod_ctorElim(v_motive_1225_, v_ctorIdx_1226_, v_t_boxed_1230_, v_h_1228_, v_k_1229_);
lean_dec(v_k_1229_);
lean_dec(v_ctorIdx_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg(lean_object* v_am_1232_){
_start:
{
lean_inc(v_am_1232_);
return v_am_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg___boxed(lean_object* v_am_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_Time_DayPeriod_am_elim___redArg(v_am_1233_);
lean_dec(v_am_1233_);
return v_res_1234_;
}
}
lean_object* l_Std_Time_DayPeriod_am_elim(lean_object* v_motive_1235_, uint8_t v_t_1236_, lean_object* v_h_1237_, lean_object* v_am_1238_){
_start:
{
lean_inc(v_am_1238_);
return v_am_1238_;
}
}
LEAN_EXPORT void l_Std_Time_DayPeriod_am_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1236_ = stack[1].m_num;
lean_object* v_am_1238_ = stack[3].m_obj;
lean_object* v_res_1239_;
v_res_1239_ = l_Std_Time_DayPeriod_am_elim(lean_box(0), v_t_1236_, lean_box(0), v_am_1238_);
stack->m_obj
 = v_res_1239_;
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___boxed(lean_object* v_motive_1240_, lean_object* v_t_1241_, lean_object* v_h_1242_, lean_object* v_am_1243_){
_start:
{
uint8_t v_t_boxed_1244_; lean_object* v_res_1245_; 
v_t_boxed_1244_ = lean_unbox(v_t_1241_);
v_res_1245_ = l_Std_Time_DayPeriod_am_elim(v_motive_1240_, v_t_boxed_1244_, v_h_1242_, v_am_1243_);
lean_dec(v_am_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg(lean_object* v_pm_1246_){
_start:
{
lean_inc(v_pm_1246_);
return v_pm_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg___boxed(lean_object* v_pm_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_Time_DayPeriod_pm_elim___redArg(v_pm_1247_);
lean_dec(v_pm_1247_);
return v_res_1248_;
}
}
lean_object* l_Std_Time_DayPeriod_pm_elim(lean_object* v_motive_1249_, uint8_t v_t_1250_, lean_object* v_h_1251_, lean_object* v_pm_1252_){
_start:
{
lean_inc(v_pm_1252_);
return v_pm_1252_;
}
}
LEAN_EXPORT void l_Std_Time_DayPeriod_pm_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1250_ = stack[1].m_num;
lean_object* v_pm_1252_ = stack[3].m_obj;
lean_object* v_res_1253_;
v_res_1253_ = l_Std_Time_DayPeriod_pm_elim(lean_box(0), v_t_1250_, lean_box(0), v_pm_1252_);
stack->m_obj
 = v_res_1253_;
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___boxed(lean_object* v_motive_1254_, lean_object* v_t_1255_, lean_object* v_h_1256_, lean_object* v_pm_1257_){
_start:
{
uint8_t v_t_boxed_1258_; lean_object* v_res_1259_; 
v_t_boxed_1258_ = lean_unbox(v_t_1255_);
v_res_1259_ = l_Std_Time_DayPeriod_pm_elim(v_motive_1254_, v_t_boxed_1258_, v_h_1256_, v_pm_1257_);
lean_dec(v_pm_1257_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg(lean_object* v_noon_1260_){
_start:
{
lean_inc(v_noon_1260_);
return v_noon_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg___boxed(lean_object* v_noon_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_Time_DayPeriod_noon_elim___redArg(v_noon_1261_);
lean_dec(v_noon_1261_);
return v_res_1262_;
}
}
lean_object* l_Std_Time_DayPeriod_noon_elim(lean_object* v_motive_1263_, uint8_t v_t_1264_, lean_object* v_h_1265_, lean_object* v_noon_1266_){
_start:
{
lean_inc(v_noon_1266_);
return v_noon_1266_;
}
}
LEAN_EXPORT void l_Std_Time_DayPeriod_noon_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1264_ = stack[1].m_num;
lean_object* v_noon_1266_ = stack[3].m_obj;
lean_object* v_res_1267_;
v_res_1267_ = l_Std_Time_DayPeriod_noon_elim(lean_box(0), v_t_1264_, lean_box(0), v_noon_1266_);
stack->m_obj
 = v_res_1267_;
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___boxed(lean_object* v_motive_1268_, lean_object* v_t_1269_, lean_object* v_h_1270_, lean_object* v_noon_1271_){
_start:
{
uint8_t v_t_boxed_1272_; lean_object* v_res_1273_; 
v_t_boxed_1272_ = lean_unbox(v_t_1269_);
v_res_1273_ = l_Std_Time_DayPeriod_noon_elim(v_motive_1268_, v_t_boxed_1272_, v_h_1270_, v_noon_1271_);
lean_dec(v_noon_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg(lean_object* v_midnight_1274_){
_start:
{
lean_inc(v_midnight_1274_);
return v_midnight_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg___boxed(lean_object* v_midnight_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_Time_DayPeriod_midnight_elim___redArg(v_midnight_1275_);
lean_dec(v_midnight_1275_);
return v_res_1276_;
}
}
lean_object* l_Std_Time_DayPeriod_midnight_elim(lean_object* v_motive_1277_, uint8_t v_t_1278_, lean_object* v_h_1279_, lean_object* v_midnight_1280_){
_start:
{
lean_inc(v_midnight_1280_);
return v_midnight_1280_;
}
}
LEAN_EXPORT void l_Std_Time_DayPeriod_midnight_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1278_ = stack[1].m_num;
lean_object* v_midnight_1280_ = stack[3].m_obj;
lean_object* v_res_1281_;
v_res_1281_ = l_Std_Time_DayPeriod_midnight_elim(lean_box(0), v_t_1278_, lean_box(0), v_midnight_1280_);
stack->m_obj
 = v_res_1281_;
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___boxed(lean_object* v_motive_1282_, lean_object* v_t_1283_, lean_object* v_h_1284_, lean_object* v_midnight_1285_){
_start:
{
uint8_t v_t_boxed_1286_; lean_object* v_res_1287_; 
v_t_boxed_1286_ = lean_unbox(v_t_1283_);
v_res_1287_ = l_Std_Time_DayPeriod_midnight_elim(v_motive_1282_, v_t_boxed_1286_, v_h_1284_, v_midnight_1285_);
lean_dec(v_midnight_1285_);
return v_res_1287_;
}
}
lean_object* l_Std_Time_instReprDayPeriod_repr(uint8_t v_x_1300_, lean_object* v_prec_1301_){
_start:
{
lean_object* v___y_1303_; lean_object* v___y_1310_; lean_object* v___y_1317_; lean_object* v___y_1324_; 
switch(v_x_1300_)
{
case 0:
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_unsigned_to_nat(1024u);
v___x_1331_ = lean_nat_dec_le(v___x_1330_, v_prec_1301_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1303_ = v___x_1332_;
goto v___jp_1302_;
}
else
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1303_ = v___x_1333_;
goto v___jp_1302_;
}
}
case 1:
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(1024u);
v___x_1335_ = lean_nat_dec_le(v___x_1334_, v_prec_1301_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1310_ = v___x_1336_;
goto v___jp_1309_;
}
else
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1310_ = v___x_1337_;
goto v___jp_1309_;
}
}
case 2:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = lean_unsigned_to_nat(1024u);
v___x_1339_ = lean_nat_dec_le(v___x_1338_, v_prec_1301_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1317_ = v___x_1340_;
goto v___jp_1316_;
}
else
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1317_ = v___x_1341_;
goto v___jp_1316_;
}
}
default: 
{
lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = lean_unsigned_to_nat(1024u);
v___x_1343_ = lean_nat_dec_le(v___x_1342_, v_prec_1301_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1324_ = v___x_1344_;
goto v___jp_1323_;
}
else
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1324_ = v___x_1345_;
goto v___jp_1323_;
}
}
}
v___jp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1304_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__1));
lean_inc(v___y_1303_);
v___x_1305_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___y_1303_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = 0;
v___x_1307_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set_uint8(v___x_1307_, sizeof(void*)*1, v___x_1306_);
v___x_1308_ = l_Repr_addAppParen(v___x_1307_, v_prec_1301_);
return v___x_1308_;
}
v___jp_1309_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1311_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__3));
lean_inc(v___y_1310_);
v___x_1312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___y_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = 0;
v___x_1314_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*1, v___x_1313_);
v___x_1315_ = l_Repr_addAppParen(v___x_1314_, v_prec_1301_);
return v___x_1315_;
}
v___jp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1318_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__5));
lean_inc(v___y_1317_);
v___x_1319_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___y_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = 0;
v___x_1321_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1321_, 0, v___x_1319_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*1, v___x_1320_);
v___x_1322_ = l_Repr_addAppParen(v___x_1321_, v_prec_1301_);
return v___x_1322_;
}
v___jp_1323_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1325_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__7));
lean_inc(v___y_1324_);
v___x_1326_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___y_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = 0;
v___x_1328_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set_uint8(v___x_1328_, sizeof(void*)*1, v___x_1327_);
v___x_1329_ = l_Repr_addAppParen(v___x_1328_, v_prec_1301_);
return v___x_1329_;
}
}
}
LEAN_EXPORT void l_Std_Time_instReprDayPeriod_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1300_ = stack[0].m_num;
lean_object* v_prec_1301_ = stack[1].m_obj;
lean_object* v_res_1346_;
v_res_1346_ = l_Std_Time_instReprDayPeriod_repr(v_x_1300_, v_prec_1301_);
stack->m_obj
 = v_res_1346_;
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr___boxed(lean_object* v_x_1347_, lean_object* v_prec_1348_){
_start:
{
uint8_t v_x_221__boxed_1349_; lean_object* v_res_1350_; 
v_x_221__boxed_1349_ = lean_unbox(v_x_1347_);
v_res_1350_ = l_Std_Time_instReprDayPeriod_repr(v_x_221__boxed_1349_, v_prec_1348_);
lean_dec(v_prec_1348_);
return v_res_1350_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedDayPeriod_default(void){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = 0;
return v___x_1353_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedDayPeriod(void){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = 0;
return v___x_1354_;
}
}
lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx___impl(uint8_t v_x_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_box(v_x_1355_);
v___x_1357_ = lean_obj_tag_nat(v___x_1356_);
lean_dec(v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT void l_Std_Time_ExtendedDayPeriod_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1355_ = stack[0].m_num;
lean_object* v_res_1358_;
v_res_1358_ = l_Std_Time_ExtendedDayPeriod_ctorIdx___impl(v_x_1355_);
stack->m_obj
 = v_res_1358_;
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx___impl___boxed(lean_object* v_x_1359_){
_start:
{
uint8_t v_x_4__boxed_1360_; lean_object* v_res_1361_; 
v_x_4__boxed_1360_ = lean_unbox(v_x_1359_);
v_res_1361_ = l_Std_Time_ExtendedDayPeriod_ctorIdx___impl(v_x_4__boxed_1360_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(lean_object* v_k_1362_){
_start:
{
lean_inc(v_k_1362_);
return v_k_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg___boxed(lean_object* v_k_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(v_k_1363_);
lean_dec(v_k_1363_);
return v_res_1364_;
}
}
lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim(lean_object* v_motive_1365_, lean_object* v_ctorIdx_1366_, uint8_t v_t_1367_, lean_object* v_h_1368_, lean_object* v_k_1369_){
_start:
{
lean_inc(v_k_1369_);
return v_k_1369_;
}
}
LEAN_EXPORT void l_Std_Time_ExtendedDayPeriod_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_1366_ = stack[1].m_obj;
uint8_t v_t_1367_ = stack[2].m_num;
lean_object* v_k_1369_ = stack[4].m_obj;
lean_object* v_res_1370_;
v_res_1370_ = l_Std_Time_ExtendedDayPeriod_ctorElim(lean_box(0), v_ctorIdx_1366_, v_t_1367_, lean_box(0), v_k_1369_);
stack->m_obj
 = v_res_1370_;
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___boxed(lean_object* v_motive_1371_, lean_object* v_ctorIdx_1372_, lean_object* v_t_1373_, lean_object* v_h_1374_, lean_object* v_k_1375_){
_start:
{
uint8_t v_t_boxed_1376_; lean_object* v_res_1377_; 
v_t_boxed_1376_ = lean_unbox(v_t_1373_);
v_res_1377_ = l_Std_Time_ExtendedDayPeriod_ctorElim(v_motive_1371_, v_ctorIdx_1372_, v_t_boxed_1376_, v_h_1374_, v_k_1375_);
lean_dec(v_k_1375_);
lean_dec(v_ctorIdx_1372_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(lean_object* v_midnight_1378_){
_start:
{
lean_inc(v_midnight_1378_);
return v_midnight_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg___boxed(lean_object* v_midnight_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(v_midnight_1379_);
lean_dec(v_midnight_1379_);
return v_res_1380_;
}
}
lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim(lean_object* v_motive_1381_, uint8_t v_t_1382_, lean_object* v_h_1383_, lean_object* v_midnight_1384_){
_start:
{
lean_inc(v_midnight_1384_);
return v_midnight_1384_;
}
}
LEAN_EXPORT void l_Std_Time_ExtendedDayPeriod_midnight_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1382_ = stack[1].m_num;
lean_object* v_midnight_1384_ = stack[3].m_obj;
lean_object* v_res_1385_;
v_res_1385_ = l_Std_Time_ExtendedDayPeriod_midnight_elim(lean_box(0), v_t_1382_, lean_box(0), v_midnight_1384_);
stack->m_obj
 = v_res_1385_;
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___boxed(lean_object* v_motive_1386_, lean_object* v_t_1387_, lean_object* v_h_1388_, lean_object* v_midnight_1389_){
_start:
{
uint8_t v_t_boxed_1390_; lean_object* v_res_1391_; 
v_t_boxed_1390_ = lean_unbox(v_t_1387_);
v_res_1391_ = l_Std_Time_ExtendedDayPeriod_midnight_elim(v_motive_1386_, v_t_boxed_1390_, v_h_1388_, v_midnight_1389_);
lean_dec(v_midnight_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg(lean_object* v_night_1392_){
_start:
{
lean_inc(v_night_1392_);
return v_night_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg___boxed(lean_object* v_night_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Std_Time_ExtendedDayPeriod_night_elim___redArg(v_night_1393_);
lean_dec(v_night_1393_);
return v_res_1394_;
}
}
lean_object* l_Std_Time_ExtendedDayPeriod_night_elim(lean_object* v_motive_1395_, uint8_t v_t_1396_, lean_object* v_h_1397_, lean_object* v_night_1398_){
_start:
{
lean_inc(v_night_1398_);
return v_night_1398_;
}
}
LEAN_EXPORT void l_Std_Time_ExtendedDayPeriod_night_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1396_ = stack[1].m_num;
lean_object* v_night_1398_ = stack[3].m_obj;
lean_object* v_res_1399_;
v_res_1399_ = l_Std_Time_ExtendedDayPeriod_night_elim(lean_box(0), v_t_1396_, lean_box(0), v_night_1398_);
stack->m_obj
 = v_res_1399_;
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___boxed(lean_object* v_motive_1400_, lean_object* v_t_1401_, lean_object* v_h_1402_, lean_object* v_night_1403_){
_start:
{
uint8_t v_t_boxed_1404_; lean_object* v_res_1405_; 
v_t_boxed_1404_ = lean_unbox(v_t_1401_);
v_res_1405_ = l_Std_Time_ExtendedDayPeriod_night_elim(v_motive_1400_, v_t_boxed_1404_, v_h_1402_, v_night_1403_);
lean_dec(v_night_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(lean_object* v_morning_1406_){
_start:
{
lean_inc(v_morning_1406_);
return v_morning_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg___boxed(lean_object* v_morning_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(v_morning_1407_);
lean_dec(v_morning_1407_);
return v_res_1408_;
}
}
lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim(lean_object* v_motive_1409_, uint8_t v_t_1410_, lean_object* v_h_1411_, lean_object* v_morning_1412_){
_start:
{
lean_inc(v_morning_1412_);
return v_morning_1412_;
}
}
LEAN_EXPORT void l_Std_Time_ExtendedDayPeriod_morning_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1410_ = stack[1].m_num;
lean_object* v_morning_1412_ = stack[3].m_obj;
lean_object* v_res_1413_;
v_res_1413_ = l_Std_Time_ExtendedDayPeriod_morning_elim(lean_box(0), v_t_1410_, lean_box(0), v_morning_1412_);
stack->m_obj
 = v_res_1413_;
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___boxed(lean_object* v_motive_1414_, lean_object* v_t_1415_, lean_object* v_h_1416_, lean_object* v_morning_1417_){
_start:
{
uint8_t v_t_boxed_1418_; lean_object* v_res_1419_; 
v_t_boxed_1418_ = lean_unbox(v_t_1415_);
v_res_1419_ = l_Std_Time_ExtendedDayPeriod_morning_elim(v_motive_1414_, v_t_boxed_1418_, v_h_1416_, v_morning_1417_);
lean_dec(v_morning_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(lean_object* v_noon_1420_){
_start:
{
lean_inc(v_noon_1420_);
return v_noon_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg___boxed(lean_object* v_noon_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(v_noon_1421_);
lean_dec(v_noon_1421_);
return v_res_1422_;
}
}
lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim(lean_object* v_motive_1423_, uint8_t v_t_1424_, lean_object* v_h_1425_, lean_object* v_noon_1426_){
_start:
{
lean_inc(v_noon_1426_);
return v_noon_1426_;
}
}
LEAN_EXPORT void l_Std_Time_ExtendedDayPeriod_noon_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1424_ = stack[1].m_num;
lean_object* v_noon_1426_ = stack[3].m_obj;
lean_object* v_res_1427_;
v_res_1427_ = l_Std_Time_ExtendedDayPeriod_noon_elim(lean_box(0), v_t_1424_, lean_box(0), v_noon_1426_);
stack->m_obj
 = v_res_1427_;
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___boxed(lean_object* v_motive_1428_, lean_object* v_t_1429_, lean_object* v_h_1430_, lean_object* v_noon_1431_){
_start:
{
uint8_t v_t_boxed_1432_; lean_object* v_res_1433_; 
v_t_boxed_1432_ = lean_unbox(v_t_1429_);
v_res_1433_ = l_Std_Time_ExtendedDayPeriod_noon_elim(v_motive_1428_, v_t_boxed_1432_, v_h_1430_, v_noon_1431_);
lean_dec(v_noon_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(lean_object* v_afternoon_1434_){
_start:
{
lean_inc(v_afternoon_1434_);
return v_afternoon_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg___boxed(lean_object* v_afternoon_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(v_afternoon_1435_);
lean_dec(v_afternoon_1435_);
return v_res_1436_;
}
}
lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim(lean_object* v_motive_1437_, uint8_t v_t_1438_, lean_object* v_h_1439_, lean_object* v_afternoon_1440_){
_start:
{
lean_inc(v_afternoon_1440_);
return v_afternoon_1440_;
}
}
LEAN_EXPORT void l_Std_Time_ExtendedDayPeriod_afternoon_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1438_ = stack[1].m_num;
lean_object* v_afternoon_1440_ = stack[3].m_obj;
lean_object* v_res_1441_;
v_res_1441_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim(lean_box(0), v_t_1438_, lean_box(0), v_afternoon_1440_);
stack->m_obj
 = v_res_1441_;
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___boxed(lean_object* v_motive_1442_, lean_object* v_t_1443_, lean_object* v_h_1444_, lean_object* v_afternoon_1445_){
_start:
{
uint8_t v_t_boxed_1446_; lean_object* v_res_1447_; 
v_t_boxed_1446_ = lean_unbox(v_t_1443_);
v_res_1447_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim(v_motive_1442_, v_t_boxed_1446_, v_h_1444_, v_afternoon_1445_);
lean_dec(v_afternoon_1445_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(lean_object* v_evening_1448_){
_start:
{
lean_inc(v_evening_1448_);
return v_evening_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg___boxed(lean_object* v_evening_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(v_evening_1449_);
lean_dec(v_evening_1449_);
return v_res_1450_;
}
}
lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim(lean_object* v_motive_1451_, uint8_t v_t_1452_, lean_object* v_h_1453_, lean_object* v_evening_1454_){
_start:
{
lean_inc(v_evening_1454_);
return v_evening_1454_;
}
}
LEAN_EXPORT void l_Std_Time_ExtendedDayPeriod_evening_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1452_ = stack[1].m_num;
lean_object* v_evening_1454_ = stack[3].m_obj;
lean_object* v_res_1455_;
v_res_1455_ = l_Std_Time_ExtendedDayPeriod_evening_elim(lean_box(0), v_t_1452_, lean_box(0), v_evening_1454_);
stack->m_obj
 = v_res_1455_;
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___boxed(lean_object* v_motive_1456_, lean_object* v_t_1457_, lean_object* v_h_1458_, lean_object* v_evening_1459_){
_start:
{
uint8_t v_t_boxed_1460_; lean_object* v_res_1461_; 
v_t_boxed_1460_ = lean_unbox(v_t_1457_);
v_res_1461_ = l_Std_Time_ExtendedDayPeriod_evening_elim(v_motive_1456_, v_t_boxed_1460_, v_h_1458_, v_evening_1459_);
lean_dec(v_evening_1459_);
return v_res_1461_;
}
}
lean_object* l_Std_Time_instReprExtendedDayPeriod_repr(uint8_t v_x_1480_, lean_object* v_prec_1481_){
_start:
{
lean_object* v___y_1483_; lean_object* v___y_1490_; lean_object* v___y_1497_; lean_object* v___y_1504_; lean_object* v___y_1511_; lean_object* v___y_1518_; 
switch(v_x_1480_)
{
case 0:
{
lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = lean_unsigned_to_nat(1024u);
v___x_1525_ = lean_nat_dec_le(v___x_1524_, v_prec_1481_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1483_ = v___x_1526_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1483_ = v___x_1527_;
goto v___jp_1482_;
}
}
case 1:
{
lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1528_ = lean_unsigned_to_nat(1024u);
v___x_1529_ = lean_nat_dec_le(v___x_1528_, v_prec_1481_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1490_ = v___x_1530_;
goto v___jp_1489_;
}
else
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1490_ = v___x_1531_;
goto v___jp_1489_;
}
}
case 2:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = lean_unsigned_to_nat(1024u);
v___x_1533_ = lean_nat_dec_le(v___x_1532_, v_prec_1481_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1497_ = v___x_1534_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1497_ = v___x_1535_;
goto v___jp_1496_;
}
}
case 3:
{
lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1536_ = lean_unsigned_to_nat(1024u);
v___x_1537_ = lean_nat_dec_le(v___x_1536_, v_prec_1481_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1504_ = v___x_1538_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1504_ = v___x_1539_;
goto v___jp_1503_;
}
}
case 4:
{
lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1540_ = lean_unsigned_to_nat(1024u);
v___x_1541_ = lean_nat_dec_le(v___x_1540_, v_prec_1481_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1511_ = v___x_1542_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1511_ = v___x_1543_;
goto v___jp_1510_;
}
}
default: 
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = lean_unsigned_to_nat(1024u);
v___x_1545_ = lean_nat_dec_le(v___x_1544_, v_prec_1481_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1518_ = v___x_1546_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1518_ = v___x_1547_;
goto v___jp_1517_;
}
}
}
v___jp_1482_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1484_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__1));
lean_inc(v___y_1483_);
v___x_1485_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___y_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = 0;
v___x_1487_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*1, v___x_1486_);
v___x_1488_ = l_Repr_addAppParen(v___x_1487_, v_prec_1481_);
return v___x_1488_;
}
v___jp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1491_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__3));
lean_inc(v___y_1490_);
v___x_1492_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1490_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
v___x_1493_ = 0;
v___x_1494_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*1, v___x_1493_);
v___x_1495_ = l_Repr_addAppParen(v___x_1494_, v_prec_1481_);
return v___x_1495_;
}
v___jp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1498_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__5));
lean_inc(v___y_1497_);
v___x_1499_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___y_1497_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = 0;
v___x_1501_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set_uint8(v___x_1501_, sizeof(void*)*1, v___x_1500_);
v___x_1502_ = l_Repr_addAppParen(v___x_1501_, v_prec_1481_);
return v___x_1502_;
}
v___jp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1505_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__7));
lean_inc(v___y_1504_);
v___x_1506_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___y_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = 0;
v___x_1508_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*1, v___x_1507_);
v___x_1509_ = l_Repr_addAppParen(v___x_1508_, v_prec_1481_);
return v___x_1509_;
}
v___jp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1512_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__9));
lean_inc(v___y_1511_);
v___x_1513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___y_1511_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = 0;
v___x_1515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set_uint8(v___x_1515_, sizeof(void*)*1, v___x_1514_);
v___x_1516_ = l_Repr_addAppParen(v___x_1515_, v_prec_1481_);
return v___x_1516_;
}
v___jp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1519_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__11));
lean_inc(v___y_1518_);
v___x_1520_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___y_1518_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = 0;
v___x_1522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set_uint8(v___x_1522_, sizeof(void*)*1, v___x_1521_);
v___x_1523_ = l_Repr_addAppParen(v___x_1522_, v_prec_1481_);
return v___x_1523_;
}
}
}
LEAN_EXPORT void l_Std_Time_instReprExtendedDayPeriod_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1480_ = stack[0].m_num;
lean_object* v_prec_1481_ = stack[1].m_obj;
lean_object* v_res_1548_;
v_res_1548_ = l_Std_Time_instReprExtendedDayPeriod_repr(v_x_1480_, v_prec_1481_);
stack->m_obj
 = v_res_1548_;
}
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___boxed(lean_object* v_x_1549_, lean_object* v_prec_1550_){
_start:
{
uint8_t v_x_329__boxed_1551_; lean_object* v_res_1552_; 
v_x_329__boxed_1551_ = lean_unbox(v_x_1549_);
v_res_1552_ = l_Std_Time_instReprExtendedDayPeriod_repr(v_x_329__boxed_1551_, v_prec_1550_);
lean_dec(v_prec_1550_);
return v_res_1552_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedExtendedDayPeriod_default(void){
_start:
{
uint8_t v___x_1555_; 
v___x_1555_ = 0;
return v___x_1555_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedExtendedDayPeriod(void){
_start:
{
uint8_t v___x_1556_; 
v___x_1556_ = 0;
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx___impl(lean_object* v_x_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_obj_tag_nat(v_x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx___impl___boxed(lean_object* v_x_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Std_Time_Modifier_ctorIdx___impl(v_x_1559_);
lean_dec_ref(v_x_1559_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___redArg(lean_object* v_t_1561_, lean_object* v_k_1562_){
_start:
{
switch(lean_obj_tag(v_t_1561_))
{
case 0:
{
uint8_t v_presentation_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_presentation_1563_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1564_ = lean_box(v_presentation_1563_);
v___x_1565_ = lean_apply_1(v_k_1562_, v___x_1564_);
return v___x_1565_;
}
case 4:
{
lean_object* v_presentation_1566_; lean_object* v___x_1567_; 
v_presentation_1566_ = lean_ctor_get(v_t_1561_, 0);
lean_inc_ref(v_presentation_1566_);
lean_dec_ref_known(v_t_1561_, 1);
v___x_1567_ = lean_apply_1(v_k_1562_, v_presentation_1566_);
return v___x_1567_;
}
case 5:
{
lean_object* v_presentation_1568_; lean_object* v___x_1569_; 
v_presentation_1568_ = lean_ctor_get(v_t_1561_, 0);
lean_inc_ref(v_presentation_1568_);
lean_dec_ref_known(v_t_1561_, 1);
v___x_1569_ = lean_apply_1(v_k_1562_, v_presentation_1568_);
return v___x_1569_;
}
case 7:
{
lean_object* v_presentation_1570_; lean_object* v___x_1571_; 
v_presentation_1570_ = lean_ctor_get(v_t_1561_, 0);
lean_inc_ref(v_presentation_1570_);
lean_dec_ref_known(v_t_1561_, 1);
v___x_1571_ = lean_apply_1(v_k_1562_, v_presentation_1570_);
return v___x_1571_;
}
case 8:
{
lean_object* v_presentation_1572_; lean_object* v___x_1573_; 
v_presentation_1572_ = lean_ctor_get(v_t_1561_, 0);
lean_inc_ref(v_presentation_1572_);
lean_dec_ref_known(v_t_1561_, 1);
v___x_1573_ = lean_apply_1(v_k_1562_, v_presentation_1572_);
return v___x_1573_;
}
case 12:
{
uint8_t v_presentation_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_presentation_1574_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1575_ = lean_box(v_presentation_1574_);
v___x_1576_ = lean_apply_1(v_k_1562_, v___x_1575_);
return v___x_1576_;
}
case 13:
{
lean_object* v_presentation_1577_; lean_object* v___x_1578_; 
v_presentation_1577_ = lean_ctor_get(v_t_1561_, 0);
lean_inc_ref(v_presentation_1577_);
lean_dec_ref_known(v_t_1561_, 1);
v___x_1578_ = lean_apply_1(v_k_1562_, v_presentation_1577_);
return v___x_1578_;
}
case 14:
{
lean_object* v_presentation_1579_; lean_object* v___x_1580_; 
v_presentation_1579_ = lean_ctor_get(v_t_1561_, 0);
lean_inc_ref(v_presentation_1579_);
lean_dec_ref_known(v_t_1561_, 1);
v___x_1580_ = lean_apply_1(v_k_1562_, v_presentation_1579_);
return v___x_1580_;
}
case 16:
{
uint8_t v_presentation_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_presentation_1581_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1582_ = lean_box(v_presentation_1581_);
v___x_1583_ = lean_apply_1(v_k_1562_, v___x_1582_);
return v___x_1583_;
}
case 17:
{
uint8_t v_presentation_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_presentation_1584_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1585_ = lean_box(v_presentation_1584_);
v___x_1586_ = lean_apply_1(v_k_1562_, v___x_1585_);
return v___x_1586_;
}
case 18:
{
uint8_t v_presentation_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_presentation_1587_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1588_ = lean_box(v_presentation_1587_);
v___x_1589_ = lean_apply_1(v_k_1562_, v___x_1588_);
return v___x_1589_;
}
case 29:
{
uint8_t v_presentation_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_presentation_1590_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1591_ = lean_box(v_presentation_1590_);
v___x_1592_ = lean_apply_1(v_k_1562_, v___x_1591_);
return v___x_1592_;
}
case 30:
{
uint8_t v_presentation_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_presentation_1593_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1594_ = lean_box(v_presentation_1593_);
v___x_1595_ = lean_apply_1(v_k_1562_, v___x_1594_);
return v___x_1595_;
}
case 31:
{
uint8_t v_presentation_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_presentation_1596_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1597_ = lean_box(v_presentation_1596_);
v___x_1598_ = lean_apply_1(v_k_1562_, v___x_1597_);
return v___x_1598_;
}
case 32:
{
uint8_t v_presentation_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_presentation_1599_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1600_ = lean_box(v_presentation_1599_);
v___x_1601_ = lean_apply_1(v_k_1562_, v___x_1600_);
return v___x_1601_;
}
case 33:
{
uint8_t v_presentation_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_presentation_1602_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1603_ = lean_box(v_presentation_1602_);
v___x_1604_ = lean_apply_1(v_k_1562_, v___x_1603_);
return v___x_1604_;
}
case 34:
{
uint8_t v_presentation_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_presentation_1605_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1606_ = lean_box(v_presentation_1605_);
v___x_1607_ = lean_apply_1(v_k_1562_, v___x_1606_);
return v___x_1607_;
}
case 35:
{
uint8_t v_presentation_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_presentation_1608_ = lean_ctor_get_uint8(v_t_1561_, 0);
lean_dec_ref_known(v_t_1561_, 0);
v___x_1609_ = lean_box(v_presentation_1608_);
v___x_1610_ = lean_apply_1(v_k_1562_, v___x_1609_);
return v___x_1610_;
}
default: 
{
lean_object* v_presentation_1611_; lean_object* v___x_1612_; 
v_presentation_1611_ = lean_ctor_get(v_t_1561_, 0);
lean_inc(v_presentation_1611_);
lean_dec_ref(v_t_1561_);
v___x_1612_ = lean_apply_1(v_k_1562_, v_presentation_1611_);
return v___x_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim(lean_object* v_motive_1613_, lean_object* v_ctorIdx_1614_, lean_object* v_t_1615_, lean_object* v_h_1616_, lean_object* v_k_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1615_, v_k_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___boxed(lean_object* v_motive_1619_, lean_object* v_ctorIdx_1620_, lean_object* v_t_1621_, lean_object* v_h_1622_, lean_object* v_k_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Std_Time_Modifier_ctorElim(v_motive_1619_, v_ctorIdx_1620_, v_t_1621_, v_h_1622_, v_k_1623_);
lean_dec(v_ctorIdx_1620_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim___redArg(lean_object* v_t_1625_, lean_object* v_G_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1625_, v_G_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim(lean_object* v_motive_1628_, lean_object* v_t_1629_, lean_object* v_h_1630_, lean_object* v_G_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1629_, v_G_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim___redArg(lean_object* v_t_1633_, lean_object* v_u_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1633_, v_u_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim(lean_object* v_motive_1636_, lean_object* v_t_1637_, lean_object* v_h_1638_, lean_object* v_u_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1637_, v_u_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim___redArg(lean_object* v_t_1641_, lean_object* v_y_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1641_, v_y_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim(lean_object* v_motive_1644_, lean_object* v_t_1645_, lean_object* v_h_1646_, lean_object* v_y_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1645_, v_y_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim___redArg(lean_object* v_t_1649_, lean_object* v_D_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1649_, v_D_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim(lean_object* v_motive_1652_, lean_object* v_t_1653_, lean_object* v_h_1654_, lean_object* v_D_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1653_, v_D_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim___redArg(lean_object* v_t_1657_, lean_object* v_M_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1657_, v_M_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim(lean_object* v_motive_1660_, lean_object* v_t_1661_, lean_object* v_h_1662_, lean_object* v_M_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1661_, v_M_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim___redArg(lean_object* v_t_1665_, lean_object* v_L_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1665_, v_L_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim(lean_object* v_motive_1668_, lean_object* v_t_1669_, lean_object* v_h_1670_, lean_object* v_L_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1669_, v_L_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim___redArg(lean_object* v_t_1673_, lean_object* v_d_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1673_, v_d_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim(lean_object* v_motive_1676_, lean_object* v_t_1677_, lean_object* v_h_1678_, lean_object* v_d_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1677_, v_d_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim___redArg(lean_object* v_t_1681_, lean_object* v_Q_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1681_, v_Q_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim(lean_object* v_motive_1684_, lean_object* v_t_1685_, lean_object* v_h_1686_, lean_object* v_Q_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1685_, v_Q_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim___redArg(lean_object* v_t_1689_, lean_object* v_q_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1689_, v_q_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim(lean_object* v_motive_1692_, lean_object* v_t_1693_, lean_object* v_h_1694_, lean_object* v_q_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1693_, v_q_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim___redArg(lean_object* v_t_1697_, lean_object* v_Y_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1697_, v_Y_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim(lean_object* v_motive_1700_, lean_object* v_t_1701_, lean_object* v_h_1702_, lean_object* v_Y_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1701_, v_Y_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim___redArg(lean_object* v_t_1705_, lean_object* v_w_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1705_, v_w_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim(lean_object* v_motive_1708_, lean_object* v_t_1709_, lean_object* v_h_1710_, lean_object* v_w_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1709_, v_w_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim___redArg(lean_object* v_t_1713_, lean_object* v_W_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1713_, v_W_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim(lean_object* v_motive_1716_, lean_object* v_t_1717_, lean_object* v_h_1718_, lean_object* v_W_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1717_, v_W_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim___redArg(lean_object* v_t_1721_, lean_object* v_E_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1721_, v_E_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim(lean_object* v_motive_1724_, lean_object* v_t_1725_, lean_object* v_h_1726_, lean_object* v_E_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1725_, v_E_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim___redArg(lean_object* v_t_1729_, lean_object* v_e_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1729_, v_e_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim(lean_object* v_motive_1732_, lean_object* v_t_1733_, lean_object* v_h_1734_, lean_object* v_e_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1733_, v_e_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim___redArg(lean_object* v_t_1737_, lean_object* v_c_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1737_, v_c_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim(lean_object* v_motive_1740_, lean_object* v_t_1741_, lean_object* v_h_1742_, lean_object* v_c_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1741_, v_c_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim___redArg(lean_object* v_t_1745_, lean_object* v_F_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1745_, v_F_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim(lean_object* v_motive_1748_, lean_object* v_t_1749_, lean_object* v_h_1750_, lean_object* v_F_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1749_, v_F_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim___redArg(lean_object* v_t_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1753_, v_a_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim(lean_object* v_motive_1756_, lean_object* v_t_1757_, lean_object* v_h_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1757_, v_a_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim___redArg(lean_object* v_t_1761_, lean_object* v_b_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1761_, v_b_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim(lean_object* v_motive_1764_, lean_object* v_t_1765_, lean_object* v_h_1766_, lean_object* v_b_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1765_, v_b_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim___redArg(lean_object* v_t_1769_, lean_object* v_B_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1769_, v_B_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim(lean_object* v_motive_1772_, lean_object* v_t_1773_, lean_object* v_h_1774_, lean_object* v_B_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1773_, v_B_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim___redArg(lean_object* v_t_1777_, lean_object* v_h_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1777_, v_h_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim(lean_object* v_motive_1780_, lean_object* v_t_1781_, lean_object* v_h_1782_, lean_object* v_h_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1781_, v_h_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim___redArg(lean_object* v_t_1785_, lean_object* v_K_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1785_, v_K_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim(lean_object* v_motive_1788_, lean_object* v_t_1789_, lean_object* v_h_1790_, lean_object* v_K_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1789_, v_K_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim___redArg(lean_object* v_t_1793_, lean_object* v_k_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1793_, v_k_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim(lean_object* v_motive_1796_, lean_object* v_t_1797_, lean_object* v_h_1798_, lean_object* v_k_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1797_, v_k_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim___redArg(lean_object* v_t_1801_, lean_object* v_H_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1801_, v_H_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim(lean_object* v_motive_1804_, lean_object* v_t_1805_, lean_object* v_h_1806_, lean_object* v_H_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1805_, v_H_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim___redArg(lean_object* v_t_1809_, lean_object* v_m_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1809_, v_m_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim(lean_object* v_motive_1812_, lean_object* v_t_1813_, lean_object* v_h_1814_, lean_object* v_m_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1813_, v_m_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim___redArg(lean_object* v_t_1817_, lean_object* v_s_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1817_, v_s_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim(lean_object* v_motive_1820_, lean_object* v_t_1821_, lean_object* v_h_1822_, lean_object* v_s_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1821_, v_s_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim___redArg(lean_object* v_t_1825_, lean_object* v_S_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1825_, v_S_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim(lean_object* v_motive_1828_, lean_object* v_t_1829_, lean_object* v_h_1830_, lean_object* v_S_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1829_, v_S_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim___redArg(lean_object* v_t_1833_, lean_object* v_A_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1833_, v_A_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim(lean_object* v_motive_1836_, lean_object* v_t_1837_, lean_object* v_h_1838_, lean_object* v_A_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1837_, v_A_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim___redArg(lean_object* v_t_1841_, lean_object* v_n_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1841_, v_n_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim(lean_object* v_motive_1844_, lean_object* v_t_1845_, lean_object* v_h_1846_, lean_object* v_n_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1845_, v_n_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim___redArg(lean_object* v_t_1849_, lean_object* v_N_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1849_, v_N_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim(lean_object* v_motive_1852_, lean_object* v_t_1853_, lean_object* v_h_1854_, lean_object* v_N_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1853_, v_N_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim___redArg(lean_object* v_t_1857_, lean_object* v_V_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1857_, v_V_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim(lean_object* v_motive_1860_, lean_object* v_t_1861_, lean_object* v_h_1862_, lean_object* v_V_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1861_, v_V_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim___redArg(lean_object* v_t_1865_, lean_object* v_z_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1865_, v_z_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim(lean_object* v_motive_1868_, lean_object* v_t_1869_, lean_object* v_h_1870_, lean_object* v_z_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1869_, v_z_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim___redArg(lean_object* v_t_1873_, lean_object* v_v_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1873_, v_v_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim(lean_object* v_motive_1876_, lean_object* v_t_1877_, lean_object* v_h_1878_, lean_object* v_v_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1877_, v_v_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim___redArg(lean_object* v_t_1881_, lean_object* v_O_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1881_, v_O_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim(lean_object* v_motive_1884_, lean_object* v_t_1885_, lean_object* v_h_1886_, lean_object* v_O_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1885_, v_O_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim___redArg(lean_object* v_t_1889_, lean_object* v_X_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1889_, v_X_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim(lean_object* v_motive_1892_, lean_object* v_t_1893_, lean_object* v_h_1894_, lean_object* v_X_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1893_, v_X_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim___redArg(lean_object* v_t_1897_, lean_object* v_x_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1897_, v_x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim(lean_object* v_motive_1900_, lean_object* v_t_1901_, lean_object* v_h_1902_, lean_object* v_x_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1901_, v_x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim___redArg(lean_object* v_t_1905_, lean_object* v_Z_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1905_, v_Z_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim(lean_object* v_motive_1908_, lean_object* v_t_1909_, lean_object* v_h_1910_, lean_object* v_Z_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1909_, v_Z_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(lean_object* v_x_1919_, lean_object* v_x_1920_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
lean_object* v_val_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_val_1921_ = lean_ctor_get(v_x_1919_, 0);
lean_inc(v_val_1921_);
lean_dec_ref_known(v_x_1919_, 1);
v___x_1922_ = ((lean_object*)(l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__1));
v___x_1923_ = l_Std_Time_instReprNumber_repr___redArg(v_val_1921_);
v___x_1924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = l_Repr_addAppParen(v___x_1924_, v_x_1920_);
return v___x_1925_;
}
else
{
lean_object* v_val_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_val_1926_ = lean_ctor_get(v_x_1919_, 0);
lean_inc(v_val_1926_);
lean_dec_ref_known(v_x_1919_, 1);
v___x_1927_ = ((lean_object*)(l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__3));
v___x_1928_ = lean_unsigned_to_nat(1024u);
v___x_1929_ = lean_unbox(v_val_1926_);
lean_dec(v_val_1926_);
v___x_1930_ = l_Std_Time_instReprText_repr(v___x_1929_, v___x_1928_);
v___x_1931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1927_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l_Repr_addAppParen(v___x_1931_, v_x_1920_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___boxed(lean_object* v_x_1933_, lean_object* v_x_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_x_1933_, v_x_1934_);
lean_dec(v_x_1934_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr(lean_object* v_x_2152_, lean_object* v_prec_2153_){
_start:
{
switch(lean_obj_tag(v_x_2152_))
{
case 0:
{
uint8_t v_presentation_2154_; lean_object* v___y_2156_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v_presentation_2154_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2165_ = lean_unsigned_to_nat(1024u);
v___x_2166_ = lean_nat_dec_le(v___x_2165_, v_prec_2153_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2156_ = v___x_2167_;
goto v___jp_2155_;
}
else
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2156_ = v___x_2168_;
goto v___jp_2155_;
}
v___jp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2157_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__2));
v___x_2158_ = lean_unsigned_to_nat(1024u);
v___x_2159_ = l_Std_Time_instReprText_repr(v_presentation_2154_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2157_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
lean_inc(v___y_2156_);
v___x_2161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___y_2156_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = 0;
v___x_2163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set_uint8(v___x_2163_, sizeof(void*)*1, v___x_2162_);
v___x_2164_ = l_Repr_addAppParen(v___x_2163_, v_prec_2153_);
return v___x_2164_;
}
}
case 1:
{
lean_object* v_presentation_2169_; lean_object* v___y_2171_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v_presentation_2169_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2169_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2180_ = lean_unsigned_to_nat(1024u);
v___x_2181_ = lean_nat_dec_le(v___x_2180_, v_prec_2153_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2171_ = v___x_2182_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2171_ = v___x_2183_;
goto v___jp_2170_;
}
v___jp_2170_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2172_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__5));
v___x_2173_ = lean_unsigned_to_nat(1024u);
v___x_2174_ = l_Std_Time_instReprYear_repr(v_presentation_2169_, v___x_2173_);
v___x_2175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2172_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
lean_inc(v___y_2171_);
v___x_2176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___y_2171_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = 0;
v___x_2178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*1, v___x_2177_);
v___x_2179_ = l_Repr_addAppParen(v___x_2178_, v_prec_2153_);
return v___x_2179_;
}
}
case 2:
{
lean_object* v_presentation_2184_; lean_object* v___y_2186_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_presentation_2184_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2184_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2195_ = lean_unsigned_to_nat(1024u);
v___x_2196_ = lean_nat_dec_le(v___x_2195_, v_prec_2153_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2186_ = v___x_2197_;
goto v___jp_2185_;
}
else
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2186_ = v___x_2198_;
goto v___jp_2185_;
}
v___jp_2185_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2187_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__8));
v___x_2188_ = lean_unsigned_to_nat(1024u);
v___x_2189_ = l_Std_Time_instReprYear_repr(v_presentation_2184_, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2187_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
lean_inc(v___y_2186_);
v___x_2191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___y_2186_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = 0;
v___x_2193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set_uint8(v___x_2193_, sizeof(void*)*1, v___x_2192_);
v___x_2194_ = l_Repr_addAppParen(v___x_2193_, v_prec_2153_);
return v___x_2194_;
}
}
case 3:
{
lean_object* v_presentation_2199_; lean_object* v___y_2201_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v_presentation_2199_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2199_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2209_ = lean_unsigned_to_nat(1024u);
v___x_2210_ = lean_nat_dec_le(v___x_2209_, v_prec_2153_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2201_ = v___x_2211_;
goto v___jp_2200_;
}
else
{
lean_object* v___x_2212_; 
v___x_2212_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2201_ = v___x_2212_;
goto v___jp_2200_;
}
v___jp_2200_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2202_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__11));
v___x_2203_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2199_);
v___x_2204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
lean_inc(v___y_2201_);
v___x_2205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___y_2201_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = 0;
v___x_2207_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*1, v___x_2206_);
v___x_2208_ = l_Repr_addAppParen(v___x_2207_, v_prec_2153_);
return v___x_2208_;
}
}
case 4:
{
lean_object* v_presentation_2213_; lean_object* v___y_2215_; lean_object* v___x_2224_; uint8_t v___x_2225_; 
v_presentation_2213_ = lean_ctor_get(v_x_2152_, 0);
lean_inc_ref(v_presentation_2213_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2224_ = lean_unsigned_to_nat(1024u);
v___x_2225_ = lean_nat_dec_le(v___x_2224_, v_prec_2153_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2215_ = v___x_2226_;
goto v___jp_2214_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2215_ = v___x_2227_;
goto v___jp_2214_;
}
v___jp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2216_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__14));
v___x_2217_ = lean_unsigned_to_nat(1024u);
v___x_2218_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2213_, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2216_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
lean_inc(v___y_2215_);
v___x_2220_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___y_2215_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = 0;
v___x_2222_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*1, v___x_2221_);
v___x_2223_ = l_Repr_addAppParen(v___x_2222_, v_prec_2153_);
return v___x_2223_;
}
}
case 5:
{
lean_object* v_presentation_2228_; lean_object* v___y_2230_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_presentation_2228_ = lean_ctor_get(v_x_2152_, 0);
lean_inc_ref(v_presentation_2228_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2239_ = lean_unsigned_to_nat(1024u);
v___x_2240_ = lean_nat_dec_le(v___x_2239_, v_prec_2153_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2230_ = v___x_2241_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2230_ = v___x_2242_;
goto v___jp_2229_;
}
v___jp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2231_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__17));
v___x_2232_ = lean_unsigned_to_nat(1024u);
v___x_2233_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2228_, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2231_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
lean_inc(v___y_2230_);
v___x_2235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___y_2230_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = 0;
v___x_2237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set_uint8(v___x_2237_, sizeof(void*)*1, v___x_2236_);
v___x_2238_ = l_Repr_addAppParen(v___x_2237_, v_prec_2153_);
return v___x_2238_;
}
}
case 6:
{
lean_object* v_presentation_2243_; lean_object* v___y_2245_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v_presentation_2243_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2243_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2253_ = lean_unsigned_to_nat(1024u);
v___x_2254_ = lean_nat_dec_le(v___x_2253_, v_prec_2153_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2245_ = v___x_2255_;
goto v___jp_2244_;
}
else
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2245_ = v___x_2256_;
goto v___jp_2244_;
}
v___jp_2244_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2246_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__20));
v___x_2247_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2243_);
v___x_2248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
lean_inc(v___y_2245_);
v___x_2249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___y_2245_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = 0;
v___x_2251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set_uint8(v___x_2251_, sizeof(void*)*1, v___x_2250_);
v___x_2252_ = l_Repr_addAppParen(v___x_2251_, v_prec_2153_);
return v___x_2252_;
}
}
case 7:
{
lean_object* v_presentation_2257_; lean_object* v___y_2259_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_presentation_2257_ = lean_ctor_get(v_x_2152_, 0);
lean_inc_ref(v_presentation_2257_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2268_ = lean_unsigned_to_nat(1024u);
v___x_2269_ = lean_nat_dec_le(v___x_2268_, v_prec_2153_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
v___x_2270_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2259_ = v___x_2270_;
goto v___jp_2258_;
}
else
{
lean_object* v___x_2271_; 
v___x_2271_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2259_ = v___x_2271_;
goto v___jp_2258_;
}
v___jp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2260_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__23));
v___x_2261_ = lean_unsigned_to_nat(1024u);
v___x_2262_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2257_, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2260_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
lean_inc(v___y_2259_);
v___x_2264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___y_2259_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = 0;
v___x_2266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set_uint8(v___x_2266_, sizeof(void*)*1, v___x_2265_);
v___x_2267_ = l_Repr_addAppParen(v___x_2266_, v_prec_2153_);
return v___x_2267_;
}
}
case 8:
{
lean_object* v_presentation_2272_; lean_object* v___y_2274_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_presentation_2272_ = lean_ctor_get(v_x_2152_, 0);
lean_inc_ref(v_presentation_2272_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2283_ = lean_unsigned_to_nat(1024u);
v___x_2284_ = lean_nat_dec_le(v___x_2283_, v_prec_2153_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2274_ = v___x_2285_;
goto v___jp_2273_;
}
else
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2274_ = v___x_2286_;
goto v___jp_2273_;
}
v___jp_2273_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2275_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__26));
v___x_2276_ = lean_unsigned_to_nat(1024u);
v___x_2277_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2272_, v___x_2276_);
v___x_2278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2275_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
lean_inc(v___y_2274_);
v___x_2279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___y_2274_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = 0;
v___x_2281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set_uint8(v___x_2281_, sizeof(void*)*1, v___x_2280_);
v___x_2282_ = l_Repr_addAppParen(v___x_2281_, v_prec_2153_);
return v___x_2282_;
}
}
case 9:
{
lean_object* v_presentation_2287_; lean_object* v___y_2289_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v_presentation_2287_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2287_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2298_ = lean_unsigned_to_nat(1024u);
v___x_2299_ = lean_nat_dec_le(v___x_2298_, v_prec_2153_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2289_ = v___x_2300_;
goto v___jp_2288_;
}
else
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2289_ = v___x_2301_;
goto v___jp_2288_;
}
v___jp_2288_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2290_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__29));
v___x_2291_ = lean_unsigned_to_nat(1024u);
v___x_2292_ = l_Std_Time_instReprYear_repr(v_presentation_2287_, v___x_2291_);
v___x_2293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2290_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
lean_inc(v___y_2289_);
v___x_2294_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___y_2289_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = 0;
v___x_2296_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*1, v___x_2295_);
v___x_2297_ = l_Repr_addAppParen(v___x_2296_, v_prec_2153_);
return v___x_2297_;
}
}
case 10:
{
lean_object* v_presentation_2302_; lean_object* v___y_2304_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v_presentation_2302_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2302_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2312_ = lean_unsigned_to_nat(1024u);
v___x_2313_ = lean_nat_dec_le(v___x_2312_, v_prec_2153_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2304_ = v___x_2314_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2304_ = v___x_2315_;
goto v___jp_2303_;
}
v___jp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2305_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__32));
v___x_2306_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2302_);
v___x_2307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
lean_inc(v___y_2304_);
v___x_2308_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___y_2304_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = 0;
v___x_2310_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*1, v___x_2309_);
v___x_2311_ = l_Repr_addAppParen(v___x_2310_, v_prec_2153_);
return v___x_2311_;
}
}
case 11:
{
lean_object* v_presentation_2316_; lean_object* v___y_2318_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_presentation_2316_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2316_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2326_ = lean_unsigned_to_nat(1024u);
v___x_2327_ = lean_nat_dec_le(v___x_2326_, v_prec_2153_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2318_ = v___x_2328_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2318_ = v___x_2329_;
goto v___jp_2317_;
}
v___jp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2319_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__35));
v___x_2320_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2316_);
v___x_2321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
lean_inc(v___y_2318_);
v___x_2322_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___y_2318_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = 0;
v___x_2324_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*1, v___x_2323_);
v___x_2325_ = l_Repr_addAppParen(v___x_2324_, v_prec_2153_);
return v___x_2325_;
}
}
case 12:
{
uint8_t v_presentation_2330_; lean_object* v___y_2332_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v_presentation_2330_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2341_ = lean_unsigned_to_nat(1024u);
v___x_2342_ = lean_nat_dec_le(v___x_2341_, v_prec_2153_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2332_ = v___x_2343_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2332_ = v___x_2344_;
goto v___jp_2331_;
}
v___jp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2333_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__38));
v___x_2334_ = lean_unsigned_to_nat(1024u);
v___x_2335_ = l_Std_Time_instReprText_repr(v_presentation_2330_, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2333_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
lean_inc(v___y_2332_);
v___x_2337_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___y_2332_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = 0;
v___x_2339_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set_uint8(v___x_2339_, sizeof(void*)*1, v___x_2338_);
v___x_2340_ = l_Repr_addAppParen(v___x_2339_, v_prec_2153_);
return v___x_2340_;
}
}
case 13:
{
lean_object* v_presentation_2345_; lean_object* v___y_2347_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v_presentation_2345_ = lean_ctor_get(v_x_2152_, 0);
lean_inc_ref(v_presentation_2345_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2356_ = lean_unsigned_to_nat(1024u);
v___x_2357_ = lean_nat_dec_le(v___x_2356_, v_prec_2153_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2347_ = v___x_2358_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2347_ = v___x_2359_;
goto v___jp_2346_;
}
v___jp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2348_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__41));
v___x_2349_ = lean_unsigned_to_nat(1024u);
v___x_2350_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2345_, v___x_2349_);
v___x_2351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2348_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
lean_inc(v___y_2347_);
v___x_2352_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___y_2347_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = 0;
v___x_2354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set_uint8(v___x_2354_, sizeof(void*)*1, v___x_2353_);
v___x_2355_ = l_Repr_addAppParen(v___x_2354_, v_prec_2153_);
return v___x_2355_;
}
}
case 14:
{
lean_object* v_presentation_2360_; lean_object* v___y_2362_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_presentation_2360_ = lean_ctor_get(v_x_2152_, 0);
lean_inc_ref(v_presentation_2360_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2371_ = lean_unsigned_to_nat(1024u);
v___x_2372_ = lean_nat_dec_le(v___x_2371_, v_prec_2153_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2362_ = v___x_2373_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2362_ = v___x_2374_;
goto v___jp_2361_;
}
v___jp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2363_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__44));
v___x_2364_ = lean_unsigned_to_nat(1024u);
v___x_2365_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2360_, v___x_2364_);
v___x_2366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2363_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
lean_inc(v___y_2362_);
v___x_2367_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___y_2362_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = 0;
v___x_2369_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*1, v___x_2368_);
v___x_2370_ = l_Repr_addAppParen(v___x_2369_, v_prec_2153_);
return v___x_2370_;
}
}
case 15:
{
lean_object* v_presentation_2375_; lean_object* v___y_2377_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v_presentation_2375_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2375_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2385_ = lean_unsigned_to_nat(1024u);
v___x_2386_ = lean_nat_dec_le(v___x_2385_, v_prec_2153_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2377_ = v___x_2387_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2377_ = v___x_2388_;
goto v___jp_2376_;
}
v___jp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2378_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__47));
v___x_2379_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2375_);
v___x_2380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
lean_inc(v___y_2377_);
v___x_2381_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___y_2377_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = 0;
v___x_2383_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*1, v___x_2382_);
v___x_2384_ = l_Repr_addAppParen(v___x_2383_, v_prec_2153_);
return v___x_2384_;
}
}
case 16:
{
uint8_t v_presentation_2389_; lean_object* v___y_2391_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
v_presentation_2389_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2400_ = lean_unsigned_to_nat(1024u);
v___x_2401_ = lean_nat_dec_le(v___x_2400_, v_prec_2153_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2391_ = v___x_2402_;
goto v___jp_2390_;
}
else
{
lean_object* v___x_2403_; 
v___x_2403_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2391_ = v___x_2403_;
goto v___jp_2390_;
}
v___jp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2392_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__50));
v___x_2393_ = lean_unsigned_to_nat(1024u);
v___x_2394_ = l_Std_Time_instReprText_repr(v_presentation_2389_, v___x_2393_);
v___x_2395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2392_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
lean_inc(v___y_2391_);
v___x_2396_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___y_2391_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = 0;
v___x_2398_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set_uint8(v___x_2398_, sizeof(void*)*1, v___x_2397_);
v___x_2399_ = l_Repr_addAppParen(v___x_2398_, v_prec_2153_);
return v___x_2399_;
}
}
case 17:
{
uint8_t v_presentation_2404_; lean_object* v___y_2406_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v_presentation_2404_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2415_ = lean_unsigned_to_nat(1024u);
v___x_2416_ = lean_nat_dec_le(v___x_2415_, v_prec_2153_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2406_ = v___x_2417_;
goto v___jp_2405_;
}
else
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2406_ = v___x_2418_;
goto v___jp_2405_;
}
v___jp_2405_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2407_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__53));
v___x_2408_ = lean_unsigned_to_nat(1024u);
v___x_2409_ = l_Std_Time_instReprText_repr(v_presentation_2404_, v___x_2408_);
v___x_2410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2407_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
lean_inc(v___y_2406_);
v___x_2411_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___y_2406_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = 0;
v___x_2413_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set_uint8(v___x_2413_, sizeof(void*)*1, v___x_2412_);
v___x_2414_ = l_Repr_addAppParen(v___x_2413_, v_prec_2153_);
return v___x_2414_;
}
}
case 18:
{
uint8_t v_presentation_2419_; lean_object* v___y_2421_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
v_presentation_2419_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2430_ = lean_unsigned_to_nat(1024u);
v___x_2431_ = lean_nat_dec_le(v___x_2430_, v_prec_2153_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; 
v___x_2432_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2421_ = v___x_2432_;
goto v___jp_2420_;
}
else
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2421_ = v___x_2433_;
goto v___jp_2420_;
}
v___jp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2422_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__56));
v___x_2423_ = lean_unsigned_to_nat(1024u);
v___x_2424_ = l_Std_Time_instReprText_repr(v_presentation_2419_, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2422_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
lean_inc(v___y_2421_);
v___x_2426_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___y_2421_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = 0;
v___x_2428_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*1, v___x_2427_);
v___x_2429_ = l_Repr_addAppParen(v___x_2428_, v_prec_2153_);
return v___x_2429_;
}
}
case 19:
{
lean_object* v_presentation_2434_; lean_object* v___y_2436_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v_presentation_2434_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2434_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2444_ = lean_unsigned_to_nat(1024u);
v___x_2445_ = lean_nat_dec_le(v___x_2444_, v_prec_2153_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2436_ = v___x_2446_;
goto v___jp_2435_;
}
else
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2436_ = v___x_2447_;
goto v___jp_2435_;
}
v___jp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2437_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__59));
v___x_2438_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2434_);
v___x_2439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
lean_inc(v___y_2436_);
v___x_2440_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___y_2436_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = 0;
v___x_2442_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set_uint8(v___x_2442_, sizeof(void*)*1, v___x_2441_);
v___x_2443_ = l_Repr_addAppParen(v___x_2442_, v_prec_2153_);
return v___x_2443_;
}
}
case 20:
{
lean_object* v_presentation_2448_; lean_object* v___y_2450_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v_presentation_2448_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2448_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2458_ = lean_unsigned_to_nat(1024u);
v___x_2459_ = lean_nat_dec_le(v___x_2458_, v_prec_2153_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2450_ = v___x_2460_;
goto v___jp_2449_;
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2450_ = v___x_2461_;
goto v___jp_2449_;
}
v___jp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2451_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__62));
v___x_2452_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2448_);
v___x_2453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
lean_inc(v___y_2450_);
v___x_2454_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___y_2450_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = 0;
v___x_2456_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set_uint8(v___x_2456_, sizeof(void*)*1, v___x_2455_);
v___x_2457_ = l_Repr_addAppParen(v___x_2456_, v_prec_2153_);
return v___x_2457_;
}
}
case 21:
{
lean_object* v_presentation_2462_; lean_object* v___y_2464_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v_presentation_2462_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2462_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2472_ = lean_unsigned_to_nat(1024u);
v___x_2473_ = lean_nat_dec_le(v___x_2472_, v_prec_2153_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2464_ = v___x_2474_;
goto v___jp_2463_;
}
else
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2464_ = v___x_2475_;
goto v___jp_2463_;
}
v___jp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2465_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__65));
v___x_2466_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2462_);
v___x_2467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
lean_inc(v___y_2464_);
v___x_2468_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___y_2464_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = 0;
v___x_2470_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*1, v___x_2469_);
v___x_2471_ = l_Repr_addAppParen(v___x_2470_, v_prec_2153_);
return v___x_2471_;
}
}
case 22:
{
lean_object* v_presentation_2476_; lean_object* v___y_2478_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v_presentation_2476_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2476_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2486_ = lean_unsigned_to_nat(1024u);
v___x_2487_ = lean_nat_dec_le(v___x_2486_, v_prec_2153_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2478_ = v___x_2488_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2478_ = v___x_2489_;
goto v___jp_2477_;
}
v___jp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2479_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__68));
v___x_2480_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2476_);
v___x_2481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
lean_inc(v___y_2478_);
v___x_2482_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___y_2478_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = 0;
v___x_2484_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2484_, 0, v___x_2482_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*1, v___x_2483_);
v___x_2485_ = l_Repr_addAppParen(v___x_2484_, v_prec_2153_);
return v___x_2485_;
}
}
case 23:
{
lean_object* v_presentation_2490_; lean_object* v___y_2492_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v_presentation_2490_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2490_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2500_ = lean_unsigned_to_nat(1024u);
v___x_2501_ = lean_nat_dec_le(v___x_2500_, v_prec_2153_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2492_ = v___x_2502_;
goto v___jp_2491_;
}
else
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2492_ = v___x_2503_;
goto v___jp_2491_;
}
v___jp_2491_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2493_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__71));
v___x_2494_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2490_);
v___x_2495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
lean_inc(v___y_2492_);
v___x_2496_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___y_2492_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = 0;
v___x_2498_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*1, v___x_2497_);
v___x_2499_ = l_Repr_addAppParen(v___x_2498_, v_prec_2153_);
return v___x_2499_;
}
}
case 24:
{
lean_object* v_presentation_2504_; lean_object* v___y_2506_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v_presentation_2504_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2504_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2514_ = lean_unsigned_to_nat(1024u);
v___x_2515_ = lean_nat_dec_le(v___x_2514_, v_prec_2153_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2506_ = v___x_2516_;
goto v___jp_2505_;
}
else
{
lean_object* v___x_2517_; 
v___x_2517_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2506_ = v___x_2517_;
goto v___jp_2505_;
}
v___jp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2507_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__74));
v___x_2508_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2504_);
v___x_2509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
lean_inc(v___y_2506_);
v___x_2510_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___y_2506_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
v___x_2511_ = 0;
v___x_2512_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set_uint8(v___x_2512_, sizeof(void*)*1, v___x_2511_);
v___x_2513_ = l_Repr_addAppParen(v___x_2512_, v_prec_2153_);
return v___x_2513_;
}
}
case 25:
{
lean_object* v_presentation_2518_; lean_object* v___y_2520_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v_presentation_2518_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2518_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2529_ = lean_unsigned_to_nat(1024u);
v___x_2530_ = lean_nat_dec_le(v___x_2529_, v_prec_2153_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2520_ = v___x_2531_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2520_ = v___x_2532_;
goto v___jp_2519_;
}
v___jp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2521_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__77));
v___x_2522_ = lean_unsigned_to_nat(1024u);
v___x_2523_ = l_Std_Time_instReprFraction_repr(v_presentation_2518_, v___x_2522_);
v___x_2524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2521_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
lean_inc(v___y_2520_);
v___x_2525_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___y_2520_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = 0;
v___x_2527_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*1, v___x_2526_);
v___x_2528_ = l_Repr_addAppParen(v___x_2527_, v_prec_2153_);
return v___x_2528_;
}
}
case 26:
{
lean_object* v_presentation_2533_; lean_object* v___y_2535_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v_presentation_2533_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2533_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2543_ = lean_unsigned_to_nat(1024u);
v___x_2544_ = lean_nat_dec_le(v___x_2543_, v_prec_2153_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2535_ = v___x_2545_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2535_ = v___x_2546_;
goto v___jp_2534_;
}
v___jp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2536_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__80));
v___x_2537_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2533_);
v___x_2538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
lean_inc(v___y_2535_);
v___x_2539_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___y_2535_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = 0;
v___x_2541_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2539_);
lean_ctor_set_uint8(v___x_2541_, sizeof(void*)*1, v___x_2540_);
v___x_2542_ = l_Repr_addAppParen(v___x_2541_, v_prec_2153_);
return v___x_2542_;
}
}
case 27:
{
lean_object* v_presentation_2547_; lean_object* v___y_2549_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v_presentation_2547_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2547_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2557_ = lean_unsigned_to_nat(1024u);
v___x_2558_ = lean_nat_dec_le(v___x_2557_, v_prec_2153_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2549_ = v___x_2559_;
goto v___jp_2548_;
}
else
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2549_ = v___x_2560_;
goto v___jp_2548_;
}
v___jp_2548_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2550_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__83));
v___x_2551_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2547_);
v___x_2552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
lean_inc(v___y_2549_);
v___x_2553_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___y_2549_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = 0;
v___x_2555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*1, v___x_2554_);
v___x_2556_ = l_Repr_addAppParen(v___x_2555_, v_prec_2153_);
return v___x_2556_;
}
}
case 28:
{
lean_object* v_presentation_2561_; lean_object* v___y_2563_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v_presentation_2561_ = lean_ctor_get(v_x_2152_, 0);
lean_inc(v_presentation_2561_);
lean_dec_ref_known(v_x_2152_, 1);
v___x_2571_ = lean_unsigned_to_nat(1024u);
v___x_2572_ = lean_nat_dec_le(v___x_2571_, v_prec_2153_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2563_ = v___x_2573_;
goto v___jp_2562_;
}
else
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2563_ = v___x_2574_;
goto v___jp_2562_;
}
v___jp_2562_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2564_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__86));
v___x_2565_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2561_);
v___x_2566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
lean_inc(v___y_2563_);
v___x_2567_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___y_2563_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = 0;
v___x_2569_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2569_, 0, v___x_2567_);
lean_ctor_set_uint8(v___x_2569_, sizeof(void*)*1, v___x_2568_);
v___x_2570_ = l_Repr_addAppParen(v___x_2569_, v_prec_2153_);
return v___x_2570_;
}
}
case 29:
{
uint8_t v_presentation_2575_; lean_object* v___y_2577_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v_presentation_2575_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2586_ = lean_unsigned_to_nat(1024u);
v___x_2587_ = lean_nat_dec_le(v___x_2586_, v_prec_2153_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2577_ = v___x_2588_;
goto v___jp_2576_;
}
else
{
lean_object* v___x_2589_; 
v___x_2589_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2577_ = v___x_2589_;
goto v___jp_2576_;
}
v___jp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2578_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__89));
v___x_2579_ = lean_unsigned_to_nat(1024u);
v___x_2580_ = l_Std_Time_instReprZoneId_repr(v_presentation_2575_, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2578_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
lean_inc(v___y_2577_);
v___x_2582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___y_2577_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = 0;
v___x_2584_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set_uint8(v___x_2584_, sizeof(void*)*1, v___x_2583_);
v___x_2585_ = l_Repr_addAppParen(v___x_2584_, v_prec_2153_);
return v___x_2585_;
}
}
case 30:
{
uint8_t v_presentation_2590_; lean_object* v___y_2592_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v_presentation_2590_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2601_ = lean_unsigned_to_nat(1024u);
v___x_2602_ = lean_nat_dec_le(v___x_2601_, v_prec_2153_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2592_ = v___x_2603_;
goto v___jp_2591_;
}
else
{
lean_object* v___x_2604_; 
v___x_2604_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2592_ = v___x_2604_;
goto v___jp_2591_;
}
v___jp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2593_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__92));
v___x_2594_ = lean_unsigned_to_nat(1024u);
v___x_2595_ = l_Std_Time_instReprZoneName_repr(v_presentation_2590_, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2593_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
lean_inc(v___y_2592_);
v___x_2597_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___y_2592_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = 0;
v___x_2599_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*1, v___x_2598_);
v___x_2600_ = l_Repr_addAppParen(v___x_2599_, v_prec_2153_);
return v___x_2600_;
}
}
case 31:
{
uint8_t v_presentation_2605_; lean_object* v___y_2607_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v_presentation_2605_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2616_ = lean_unsigned_to_nat(1024u);
v___x_2617_ = lean_nat_dec_le(v___x_2616_, v_prec_2153_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2607_ = v___x_2618_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2607_ = v___x_2619_;
goto v___jp_2606_;
}
v___jp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2608_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__95));
v___x_2609_ = lean_unsigned_to_nat(1024u);
v___x_2610_ = l_Std_Time_instReprZoneName_repr(v_presentation_2605_, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2608_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
lean_inc(v___y_2607_);
v___x_2612_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___y_2607_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = 0;
v___x_2614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*1, v___x_2613_);
v___x_2615_ = l_Repr_addAppParen(v___x_2614_, v_prec_2153_);
return v___x_2615_;
}
}
case 32:
{
uint8_t v_presentation_2620_; lean_object* v___y_2622_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v_presentation_2620_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2631_ = lean_unsigned_to_nat(1024u);
v___x_2632_ = lean_nat_dec_le(v___x_2631_, v_prec_2153_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2622_ = v___x_2633_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2622_ = v___x_2634_;
goto v___jp_2621_;
}
v___jp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2623_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__98));
v___x_2624_ = lean_unsigned_to_nat(1024u);
v___x_2625_ = l_Std_Time_instReprOffsetO_repr(v_presentation_2620_, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2623_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
lean_inc(v___y_2622_);
v___x_2627_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___y_2622_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = 0;
v___x_2629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2629_, 0, v___x_2627_);
lean_ctor_set_uint8(v___x_2629_, sizeof(void*)*1, v___x_2628_);
v___x_2630_ = l_Repr_addAppParen(v___x_2629_, v_prec_2153_);
return v___x_2630_;
}
}
case 33:
{
uint8_t v_presentation_2635_; lean_object* v___y_2637_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v_presentation_2635_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2646_ = lean_unsigned_to_nat(1024u);
v___x_2647_ = lean_nat_dec_le(v___x_2646_, v_prec_2153_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2637_ = v___x_2648_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2649_; 
v___x_2649_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2637_ = v___x_2649_;
goto v___jp_2636_;
}
v___jp_2636_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2638_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__101));
v___x_2639_ = lean_unsigned_to_nat(1024u);
v___x_2640_ = l_Std_Time_instReprOffsetX_repr(v_presentation_2635_, v___x_2639_);
v___x_2641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2638_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
lean_inc(v___y_2637_);
v___x_2642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___y_2637_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = 0;
v___x_2644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set_uint8(v___x_2644_, sizeof(void*)*1, v___x_2643_);
v___x_2645_ = l_Repr_addAppParen(v___x_2644_, v_prec_2153_);
return v___x_2645_;
}
}
case 34:
{
uint8_t v_presentation_2650_; lean_object* v___y_2652_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v_presentation_2650_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2661_ = lean_unsigned_to_nat(1024u);
v___x_2662_ = lean_nat_dec_le(v___x_2661_, v_prec_2153_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2652_ = v___x_2663_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2664_; 
v___x_2664_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2652_ = v___x_2664_;
goto v___jp_2651_;
}
v___jp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2653_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__104));
v___x_2654_ = lean_unsigned_to_nat(1024u);
v___x_2655_ = l_Std_Time_instReprOffsetX_repr(v_presentation_2650_, v___x_2654_);
v___x_2656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2653_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
lean_inc(v___y_2652_);
v___x_2657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___y_2652_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = 0;
v___x_2659_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set_uint8(v___x_2659_, sizeof(void*)*1, v___x_2658_);
v___x_2660_ = l_Repr_addAppParen(v___x_2659_, v_prec_2153_);
return v___x_2660_;
}
}
default: 
{
uint8_t v_presentation_2665_; lean_object* v___y_2667_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v_presentation_2665_ = lean_ctor_get_uint8(v_x_2152_, 0);
lean_dec_ref_known(v_x_2152_, 0);
v___x_2676_ = lean_unsigned_to_nat(1024u);
v___x_2677_ = lean_nat_dec_le(v___x_2676_, v_prec_2153_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2667_ = v___x_2678_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2667_ = v___x_2679_;
goto v___jp_2666_;
}
v___jp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2668_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__107));
v___x_2669_ = lean_unsigned_to_nat(1024u);
v___x_2670_ = l_Std_Time_instReprOffsetZ_repr(v_presentation_2665_, v___x_2669_);
v___x_2671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2668_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
lean_inc(v___y_2667_);
v___x_2672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___y_2667_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = 0;
v___x_2674_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set_uint8(v___x_2674_, sizeof(void*)*1, v___x_2673_);
v___x_2675_ = l_Repr_addAppParen(v___x_2674_, v_prec_2153_);
return v___x_2675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr___boxed(lean_object* v_x_2680_, lean_object* v_prec_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Std_Time_instReprModifier_repr(v_x_2680_, v_prec_2681_);
lean_dec(v_prec_2681_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(lean_object* v_constructor_2692_, lean_object* v_classify_2693_, lean_object* v_p_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_len_2696_; lean_object* v___x_2697_; 
v_len_2696_ = lean_string_length(v_p_2694_);
v___x_2697_ = lean_apply_1(v_classify_2693_, v_len_2696_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v___x_2698_; uint32_t v___y_2700_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec_ref(v_constructor_2692_);
v___x_2698_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2708_ = lean_unsigned_to_nat(0u);
v___x_2709_ = lean_string_utf8_byte_size(v_p_2694_);
v___x_2710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2710_, 0, v_p_2694_);
lean_ctor_set(v___x_2710_, 1, v___x_2708_);
lean_ctor_set(v___x_2710_, 2, v___x_2709_);
v___x_2711_ = l_String_Slice_Pos_get_x3f(v___x_2710_, v___x_2708_);
lean_dec_ref_known(v___x_2710_, 3);
if (lean_obj_tag(v___x_2711_) == 0)
{
uint32_t v___x_2712_; 
v___x_2712_ = 65;
v___y_2700_ = v___x_2712_;
goto v___jp_2699_;
}
else
{
lean_object* v_val_2713_; uint32_t v___x_2714_; 
v_val_2713_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_val_2713_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2714_ = lean_unbox_uint32(v_val_2713_);
lean_dec(v_val_2713_);
v___y_2700_ = v___x_2714_;
goto v___jp_2699_;
}
v___jp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2701_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2702_ = lean_string_push(v___x_2701_, v___y_2700_);
v___x_2703_ = lean_string_append(v___x_2698_, v___x_2702_);
lean_dec_ref(v___x_2702_);
v___x_2704_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_2705_ = lean_string_append(v___x_2703_, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
v___x_2707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_a_2695_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
return v___x_2707_;
}
}
else
{
lean_object* v_val_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_dec_ref(v_p_2694_);
v_val_2715_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_val_2715_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2716_ = lean_apply_1(v_constructor_2692_, v_val_2715_);
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v_a_2695_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod(lean_object* v_00_u03b1_2718_, lean_object* v_constructor_2719_, lean_object* v_classify_2720_, lean_object* v_p_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2719_, v_classify_2720_, v_p_2721_, v_a_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(lean_object* v_constructor_2725_, lean_object* v_p_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseText___closed__0));
v___x_2729_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2725_, v___x_2728_, v_p_2726_, v_a_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(lean_object* v_max_2730_, lean_object* v_x_2731_){
_start:
{
uint8_t v___x_2732_; 
v___x_2732_ = lean_nat_dec_le(v_x_2731_, v_max_2730_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
lean_dec(v_x_2731_);
v___x_2733_ = lean_box(0);
return v___x_2733_;
}
else
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2734_, 0, v_x_2731_);
return v___x_2734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax___boxed(lean_object* v_max_2735_, lean_object* v_x_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(v_max_2735_, v_x_2736_);
lean_dec(v_max_2735_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(lean_object* v_x_2740_){
_start:
{
lean_object* v___x_2741_; uint8_t v___x_2742_; 
v___x_2741_ = lean_unsigned_to_nat(1u);
v___x_2742_ = lean_nat_dec_eq(v_x_2740_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; 
v___x_2743_ = lean_box(0);
return v___x_2743_;
}
else
{
lean_object* v___x_2744_; 
v___x_2744_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___closed__0));
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___boxed(lean_object* v_x_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(v_x_2745_);
lean_dec(v_x_2745_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(lean_object* v_x_2750_){
_start:
{
lean_object* v___x_2751_; uint8_t v___x_2752_; 
v___x_2751_ = lean_unsigned_to_nat(6u);
v___x_2752_ = lean_nat_dec_eq(v_x_2750_, v___x_2751_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Std_Time_Text_classify(v_x_2750_);
return v___x_2753_;
}
else
{
lean_object* v___x_2754_; 
v___x_2754_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___closed__0));
return v___x_2754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___boxed(lean_object* v_x_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(v_x_2755_);
lean_dec(v_x_2755_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(lean_object* v_constructor_2758_, lean_object* v_p_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText___closed__0));
v___x_2762_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2758_, v___x_2761_, v_p_2759_, v_a_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(lean_object* v_constructor_2764_, lean_object* v_p_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction___closed__0));
v___x_2768_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2764_, v___x_2767_, v_p_2765_, v_a_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(lean_object* v_constructor_2769_, lean_object* v_p_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = lean_string_length(v_p_2770_);
v___x_2773_ = lean_apply_1(v_constructor_2769_, v___x_2772_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v_a_2771_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber___boxed(lean_object* v_constructor_2775_, lean_object* v_p_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v_constructor_2775_, v_p_2776_, v_a_2777_);
lean_dec_ref(v_p_2776_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(lean_object* v_constructor_2780_, lean_object* v_p_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear___closed__0));
v___x_2784_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2780_, v___x_2783_, v_p_2781_, v_a_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(lean_object* v_constructor_2786_, lean_object* v_p_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX___closed__0));
v___x_2790_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2786_, v___x_2789_, v_p_2787_, v_a_2788_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(lean_object* v_constructor_2792_, lean_object* v_p_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ___closed__0));
v___x_2796_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2792_, v___x_2795_, v_p_2793_, v_a_2794_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(lean_object* v_constructor_2798_, lean_object* v_p_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO___closed__0));
v___x_2802_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2798_, v___x_2801_, v_p_2799_, v_a_2800_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(lean_object* v_p_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2810_ = lean_string_length(v_p_2808_);
v___x_2811_ = lean_unsigned_to_nat(1u);
v___x_2812_ = lean_nat_dec_eq(v___x_2810_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2813_ = lean_unsigned_to_nat(2u);
v___x_2814_ = lean_nat_dec_eq(v___x_2810_, v___x_2813_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; uint32_t v___y_2817_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2815_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2825_ = lean_unsigned_to_nat(0u);
v___x_2826_ = lean_string_utf8_byte_size(v_p_2808_);
v___x_2827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2827_, 0, v_p_2808_);
lean_ctor_set(v___x_2827_, 1, v___x_2825_);
lean_ctor_set(v___x_2827_, 2, v___x_2826_);
v___x_2828_ = l_String_Slice_Pos_get_x3f(v___x_2827_, v___x_2825_);
lean_dec_ref_known(v___x_2827_, 3);
if (lean_obj_tag(v___x_2828_) == 0)
{
uint32_t v___x_2829_; 
v___x_2829_ = 65;
v___y_2817_ = v___x_2829_;
goto v___jp_2816_;
}
else
{
lean_object* v_val_2830_; uint32_t v___x_2831_; 
v_val_2830_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v___x_2828_, 1);
v___x_2831_ = lean_unbox_uint32(v_val_2830_);
lean_dec(v_val_2830_);
v___y_2817_ = v___x_2831_;
goto v___jp_2816_;
}
v___jp_2816_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2818_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2819_ = lean_string_push(v___x_2818_, v___y_2817_);
v___x_2820_ = lean_string_append(v___x_2815_, v___x_2819_);
lean_dec_ref(v___x_2819_);
v___x_2821_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__0));
v___x_2822_ = lean_string_append(v___x_2820_, v___x_2821_);
v___x_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
v___x_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2824_, 0, v_a_2809_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
return v___x_2824_;
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_dec_ref(v_p_2808_);
v___x_2832_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__1));
v___x_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2809_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
return v___x_2833_;
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_dec_ref(v_p_2808_);
v___x_2834_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__2));
v___x_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2835_, 0, v_a_2809_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
return v___x_2835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(lean_object* v_constructor_2837_, lean_object* v_p_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText___closed__0));
v___x_2841_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2837_, v___x_2840_, v_p_2838_, v_a_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText(lean_object* v_x_2847_){
_start:
{
lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2848_ = lean_unsigned_to_nat(3u);
v___x_2849_ = lean_nat_dec_lt(v_x_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2850_ = lean_unsigned_to_nat(6u);
v___x_2851_ = lean_nat_dec_eq(v_x_2847_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Std_Time_Text_classify(v_x_2847_);
lean_dec(v_x_2847_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_box(0);
return v___x_2853_;
}
else
{
lean_object* v_val_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2862_; 
v_val_2854_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2856_ = v___x_2852_;
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_val_2854_);
lean_dec(v___x_2852_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2858_, 0, v_val_2854_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2858_);
v___x_2860_ = v___x_2856_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v___x_2863_; 
lean_dec(v_x_2847_);
v___x_2863_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1));
return v___x_2863_;
}
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_x_2847_);
v___x_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
return v___x_2865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(lean_object* v_constructor_2867_, lean_object* v_p_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText___closed__0));
v___x_2871_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2867_, v___x_2870_, v_p_2868_, v_a_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(lean_object* v_x_2876_){
_start:
{
lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = lean_unsigned_to_nat(1u);
v___x_2878_ = lean_nat_dec_eq(v_x_2876_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = lean_unsigned_to_nat(6u);
v___x_2880_ = lean_nat_dec_eq(v_x_2876_, v___x_2879_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; uint8_t v___x_2882_; 
v___x_2881_ = lean_unsigned_to_nat(3u);
v___x_2882_ = lean_nat_dec_le(v___x_2881_, v_x_2876_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_box(0);
return v___x_2883_;
}
else
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Std_Time_Text_classify(v_x_2876_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2885_; 
v___x_2885_ = lean_box(0);
return v___x_2885_;
}
else
{
lean_object* v_val_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2894_; 
v_val_2886_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2888_ = v___x_2884_;
v_isShared_2889_ = v_isSharedCheck_2894_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_val_2886_);
lean_dec(v___x_2884_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2894_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2890_, 0, v_val_2886_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2890_);
v___x_2892_ = v___x_2888_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
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
else
{
lean_object* v___x_2895_; 
v___x_2895_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1));
return v___x_2895_;
}
}
else
{
lean_object* v___x_2896_; 
v___x_2896_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__1));
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___boxed(lean_object* v_x_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(v_x_2897_);
lean_dec(v_x_2897_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(lean_object* v_constructor_2900_, lean_object* v_p_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText___closed__0));
v___x_2904_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2900_, v___x_2903_, v_p_2901_, v_a_2902_);
return v___x_2904_;
}
}
lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(uint8_t v_presentation_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_alloc_ctor(16, 0, 1);
lean_ctor_set_uint8(v___x_2906_, 0, v_presentation_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_2905_ = stack[0].m_num;
lean_object* v_res_2907_;
v_res_2907_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(v_presentation_2905_);
stack->m_obj
 = v_res_2907_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0___boxed(lean_object* v_presentation_2908_){
_start:
{
uint8_t v_presentation_boxed_2909_; lean_object* v_res_2910_; 
v_presentation_boxed_2909_ = lean_unbox(v_presentation_2908_);
v_res_2910_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(v_presentation_boxed_2909_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(lean_object* v_p_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v___f_2914_; lean_object* v___x_2915_; 
v___f_2914_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___closed__0));
v___x_2915_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2914_, v_p_2912_, v_a_2913_);
return v___x_2915_;
}
}
lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(uint8_t v_presentation_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_alloc_ctor(17, 0, 1);
lean_ctor_set_uint8(v___x_2917_, 0, v_presentation_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_2916_ = stack[0].m_num;
lean_object* v_res_2918_;
v_res_2918_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(v_presentation_2916_);
stack->m_obj
 = v_res_2918_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0___boxed(lean_object* v_presentation_2919_){
_start:
{
uint8_t v_presentation_boxed_2920_; lean_object* v_res_2921_; 
v_presentation_boxed_2920_ = lean_unbox(v_presentation_2919_);
v_res_2921_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(v_presentation_boxed_2920_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(lean_object* v_p_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v___f_2925_; lean_object* v___x_2926_; 
v___f_2925_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___closed__0));
v___x_2926_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2925_, v_p_2923_, v_a_2924_);
return v___x_2926_;
}
}
lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(uint8_t v_presentation_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_alloc_ctor(18, 0, 1);
lean_ctor_set_uint8(v___x_2928_, 0, v_presentation_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT void l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_2927_ = stack[0].m_num;
lean_object* v_res_2929_;
v_res_2929_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(v_presentation_2927_);
stack->m_obj
 = v_res_2929_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0___boxed(lean_object* v_presentation_2930_){
_start:
{
uint8_t v_presentation_boxed_2931_; lean_object* v_res_2932_; 
v_presentation_boxed_2931_ = lean_unbox(v_presentation_2930_);
v_res_2932_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(v_presentation_boxed_2931_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(lean_object* v_p_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v___f_2936_; lean_object* v___x_2937_; 
v___f_2936_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___closed__0));
v___x_2937_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2936_, v_p_2934_, v_a_2935_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(lean_object* v_constructor_2938_, lean_object* v_p_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___y_2942_; uint32_t v___y_2943_; lean_object* v_len_2951_; uint32_t v___y_2953_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_len_2951_ = lean_string_length(v_p_2939_);
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = lean_string_utf8_byte_size(v_p_2939_);
lean_inc_ref(v_p_2939_);
v___x_2968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2968_, 0, v_p_2939_);
lean_ctor_set(v___x_2968_, 1, v___x_2966_);
lean_ctor_set(v___x_2968_, 2, v___x_2967_);
v___x_2969_ = l_String_Slice_Pos_get_x3f(v___x_2968_, v___x_2966_);
lean_dec_ref_known(v___x_2968_, 3);
if (lean_obj_tag(v___x_2969_) == 0)
{
uint32_t v___x_2970_; 
v___x_2970_ = 65;
v___y_2953_ = v___x_2970_;
goto v___jp_2952_;
}
else
{
lean_object* v_val_2971_; uint32_t v___x_2972_; 
v_val_2971_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_val_2971_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2972_ = lean_unbox_uint32(v_val_2971_);
lean_dec(v_val_2971_);
v___y_2953_ = v___x_2972_;
goto v___jp_2952_;
}
v___jp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2944_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2945_ = lean_string_push(v___x_2944_, v___y_2943_);
lean_inc_ref(v___y_2942_);
v___x_2946_ = lean_string_append(v___y_2942_, v___x_2945_);
lean_dec_ref(v___x_2945_);
v___x_2947_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_2948_ = lean_string_append(v___x_2946_, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
v___x_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2950_, 0, v_a_2940_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
return v___x_2950_;
}
v___jp_2952_:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Std_Time_ZoneName_classify(v___y_2953_, v_len_2951_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_dec_ref(v_constructor_2938_);
v___x_2955_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2956_ = lean_unsigned_to_nat(0u);
v___x_2957_ = lean_string_utf8_byte_size(v_p_2939_);
v___x_2958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2958_, 0, v_p_2939_);
lean_ctor_set(v___x_2958_, 1, v___x_2956_);
lean_ctor_set(v___x_2958_, 2, v___x_2957_);
v___x_2959_ = l_String_Slice_Pos_get_x3f(v___x_2958_, v___x_2956_);
lean_dec_ref_known(v___x_2958_, 3);
if (lean_obj_tag(v___x_2959_) == 0)
{
uint32_t v___x_2960_; 
v___x_2960_ = 65;
v___y_2942_ = v___x_2955_;
v___y_2943_ = v___x_2960_;
goto v___jp_2941_;
}
else
{
lean_object* v_val_2961_; uint32_t v___x_2962_; 
v_val_2961_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_val_2961_);
lean_dec_ref_known(v___x_2959_, 1);
v___x_2962_ = lean_unbox_uint32(v_val_2961_);
lean_dec(v_val_2961_);
v___y_2942_ = v___x_2955_;
v___y_2943_ = v___x_2962_;
goto v___jp_2941_;
}
}
else
{
lean_object* v_val_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref(v_p_2939_);
v_val_2963_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_val_2963_);
lean_dec_ref_known(v___x_2954_, 1);
v___x_2964_ = lean_apply_1(v_constructor_2938_, v_val_2963_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v_a_2940_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
return v___x_2965_;
}
}
}
}
lean_object* l_Std_Time_parseModifier___lam__0(uint8_t v_presentation_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_alloc_ctor(35, 0, 1);
lean_ctor_set_uint8(v___x_2974_, 0, v_presentation_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT void l_Std_Time_parseModifier___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_2973_ = stack[0].m_num;
lean_object* v_res_2975_;
v_res_2975_ = l_Std_Time_parseModifier___lam__0(v_presentation_2973_);
stack->m_obj
 = v_res_2975_;
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0___boxed(lean_object* v_presentation_2976_){
_start:
{
uint8_t v_presentation_boxed_2977_; lean_object* v_res_2978_; 
v_presentation_boxed_2977_ = lean_unbox(v_presentation_2976_);
v_res_2978_ = l_Std_Time_parseModifier___lam__0(v_presentation_boxed_2977_);
return v_res_2978_;
}
}
lean_object* l_Std_Time_parseModifier___lam__1(uint8_t v_presentation_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_alloc_ctor(34, 0, 1);
lean_ctor_set_uint8(v___x_2980_, 0, v_presentation_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT void l_Std_Time_parseModifier___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_2979_ = stack[0].m_num;
lean_object* v_res_2981_;
v_res_2981_ = l_Std_Time_parseModifier___lam__1(v_presentation_2979_);
stack->m_obj
 = v_res_2981_;
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1___boxed(lean_object* v_presentation_2982_){
_start:
{
uint8_t v_presentation_boxed_2983_; lean_object* v_res_2984_; 
v_presentation_boxed_2983_ = lean_unbox(v_presentation_2982_);
v_res_2984_ = l_Std_Time_parseModifier___lam__1(v_presentation_boxed_2983_);
return v_res_2984_;
}
}
lean_object* l_Std_Time_parseModifier___lam__2(uint8_t v_presentation_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_alloc_ctor(33, 0, 1);
lean_ctor_set_uint8(v___x_2986_, 0, v_presentation_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT void l_Std_Time_parseModifier___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_2985_ = stack[0].m_num;
lean_object* v_res_2987_;
v_res_2987_ = l_Std_Time_parseModifier___lam__2(v_presentation_2985_);
stack->m_obj
 = v_res_2987_;
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2___boxed(lean_object* v_presentation_2988_){
_start:
{
uint8_t v_presentation_boxed_2989_; lean_object* v_res_2990_; 
v_presentation_boxed_2989_ = lean_unbox(v_presentation_2988_);
v_res_2990_ = l_Std_Time_parseModifier___lam__2(v_presentation_boxed_2989_);
return v_res_2990_;
}
}
lean_object* l_Std_Time_parseModifier___lam__3(uint8_t v_presentation_2991_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_alloc_ctor(32, 0, 1);
lean_ctor_set_uint8(v___x_2992_, 0, v_presentation_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT void l_Std_Time_parseModifier___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_2991_ = stack[0].m_num;
lean_object* v_res_2993_;
v_res_2993_ = l_Std_Time_parseModifier___lam__3(v_presentation_2991_);
stack->m_obj
 = v_res_2993_;
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3___boxed(lean_object* v_presentation_2994_){
_start:
{
uint8_t v_presentation_boxed_2995_; lean_object* v_res_2996_; 
v_presentation_boxed_2995_ = lean_unbox(v_presentation_2994_);
v_res_2996_ = l_Std_Time_parseModifier___lam__3(v_presentation_boxed_2995_);
return v_res_2996_;
}
}
lean_object* l_Std_Time_parseModifier___lam__4(uint8_t v_presentation_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(31, 0, 1);
lean_ctor_set_uint8(v___x_2998_, 0, v_presentation_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT void l_Std_Time_parseModifier___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_2997_ = stack[0].m_num;
lean_object* v_res_2999_;
v_res_2999_ = l_Std_Time_parseModifier___lam__4(v_presentation_2997_);
stack->m_obj
 = v_res_2999_;
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4___boxed(lean_object* v_presentation_3000_){
_start:
{
uint8_t v_presentation_boxed_3001_; lean_object* v_res_3002_; 
v_presentation_boxed_3001_ = lean_unbox(v_presentation_3000_);
v_res_3002_ = l_Std_Time_parseModifier___lam__4(v_presentation_boxed_3001_);
return v_res_3002_;
}
}
lean_object* l_Std_Time_parseModifier___lam__5(uint8_t v_presentation_3003_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_alloc_ctor(30, 0, 1);
lean_ctor_set_uint8(v___x_3004_, 0, v_presentation_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT void l_Std_Time_parseModifier___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_3003_ = stack[0].m_num;
lean_object* v_res_3005_;
v_res_3005_ = l_Std_Time_parseModifier___lam__5(v_presentation_3003_);
stack->m_obj
 = v_res_3005_;
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5___boxed(lean_object* v_presentation_3006_){
_start:
{
uint8_t v_presentation_boxed_3007_; lean_object* v_res_3008_; 
v_presentation_boxed_3007_ = lean_unbox(v_presentation_3006_);
v_res_3008_ = l_Std_Time_parseModifier___lam__5(v_presentation_boxed_3007_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__6(lean_object* v_presentation_3009_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_alloc_ctor(28, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_presentation_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__7(lean_object* v_presentation_3011_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_alloc_ctor(27, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_presentation_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__8(lean_object* v_presentation_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_alloc_ctor(26, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_presentation_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__9(lean_object* v_presentation_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_alloc_ctor(25, 1, 0);
lean_ctor_set(v___x_3016_, 0, v_presentation_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__10(lean_object* v_presentation_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_alloc_ctor(24, 1, 0);
lean_ctor_set(v___x_3018_, 0, v_presentation_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__11(lean_object* v_presentation_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_alloc_ctor(23, 1, 0);
lean_ctor_set(v___x_3020_, 0, v_presentation_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__12(lean_object* v_presentation_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(v___x_3022_, 0, v_presentation_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__13(lean_object* v_presentation_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_3024_, 0, v_presentation_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__14(lean_object* v_presentation_3025_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_presentation_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__15(lean_object* v_presentation_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = lean_alloc_ctor(19, 1, 0);
lean_ctor_set(v___x_3028_, 0, v_presentation_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__16(lean_object* v_presentation_3029_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_3030_, 0, v_presentation_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__17(lean_object* v_presentation_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_3032_, 0, v_presentation_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__18(lean_object* v_presentation_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_3034_, 0, v_presentation_3033_);
return v___x_3034_;
}
}
lean_object* l_Std_Time_parseModifier___lam__19(uint8_t v_presentation_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_alloc_ctor(12, 0, 1);
lean_ctor_set_uint8(v___x_3036_, 0, v_presentation_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT void l_Std_Time_parseModifier___lam__19_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_3035_ = stack[0].m_num;
lean_object* v_res_3037_;
v_res_3037_ = l_Std_Time_parseModifier___lam__19(v_presentation_3035_);
stack->m_obj
 = v_res_3037_;
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19___boxed(lean_object* v_presentation_3038_){
_start:
{
uint8_t v_presentation_boxed_3039_; lean_object* v_res_3040_; 
v_presentation_boxed_3039_ = lean_unbox(v_presentation_3038_);
v_res_3040_ = l_Std_Time_parseModifier___lam__19(v_presentation_boxed_3039_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__20(lean_object* v_presentation_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_3042_, 0, v_presentation_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__21(lean_object* v_presentation_3043_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3044_, 0, v_presentation_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__22(lean_object* v_presentation_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3046_, 0, v_presentation_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__23(lean_object* v_presentation_3047_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3048_, 0, v_presentation_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__24(lean_object* v_presentation_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_presentation_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__25(lean_object* v_presentation_3051_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3052_, 0, v_presentation_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__26(lean_object* v_presentation_3053_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3054_, 0, v_presentation_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__27(lean_object* v_presentation_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_presentation_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__28(lean_object* v_presentation_3057_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3058_, 0, v_presentation_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__29(lean_object* v_presentation_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3060_, 0, v_presentation_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__30(lean_object* v_presentation_3061_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3062_, 0, v_presentation_3061_);
return v___x_3062_;
}
}
lean_object* l_Std_Time_parseModifier___lam__31(uint8_t v_presentation_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3064_, 0, v_presentation_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT void l_Std_Time_parseModifier___lam__31_0interp(lean_interpreter_value* stack)
{
uint8_t v_presentation_3063_ = stack[0].m_num;
lean_object* v_res_3065_;
v_res_3065_ = l_Std_Time_parseModifier___lam__31(v_presentation_3063_);
stack->m_obj
 = v_res_3065_;
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31___boxed(lean_object* v_presentation_3066_){
_start:
{
uint8_t v_presentation_boxed_3067_; lean_object* v_res_3068_; 
v_presentation_boxed_3067_ = lean_unbox(v_presentation_3066_);
v_res_3068_ = l_Std_Time_parseModifier___lam__31(v_presentation_boxed_3067_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(lean_object* v_acc_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_fst_3074_; lean_object* v_snd_3075_; lean_object* v_pos_3077_; lean_object* v_snd_3078_; lean_object* v_err_3079_; lean_object* v___x_3083_; uint8_t v_decide_3084_; 
v_fst_3074_ = lean_ctor_get(v_a_3073_, 0);
v_snd_3075_ = lean_ctor_get(v_a_3073_, 1);
lean_inc(v_snd_3075_);
v___x_3083_ = lean_string_utf8_byte_size(v_fst_3074_);
v_decide_3084_ = lean_nat_dec_eq(v_snd_3075_, v___x_3083_);
if (v_decide_3084_ == 0)
{
uint32_t v___x_3085_; uint32_t v_c_3086_; uint8_t v___x_3087_; 
v___x_3085_ = 120;
v_c_3086_ = lean_string_utf8_get_fast(v_fst_3074_, v_snd_3075_);
v___x_3087_ = lean_uint32_dec_eq(v_c_3086_, v___x_3085_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; 
v___x_3088_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1));
lean_inc(v_snd_3075_);
v_pos_3077_ = v_a_3073_;
v_snd_3078_ = v_snd_3075_;
v_err_3079_ = v___x_3088_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3098_; 
lean_inc(v_fst_3074_);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_a_3073_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; lean_object* v_unused_3100_; 
v_unused_3099_ = lean_ctor_get(v_a_3073_, 1);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_a_3073_, 0);
lean_dec(v_unused_3100_);
v___x_3090_ = v_a_3073_;
v_isShared_3091_ = v_isSharedCheck_3098_;
goto v_resetjp_3089_;
}
else
{
lean_dec(v_a_3073_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3098_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3092_; lean_object* v_it_x27_3094_; 
v___x_3092_ = lean_string_utf8_next_fast(v_fst_3074_, v_snd_3075_);
lean_dec(v_snd_3075_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 1, v___x_3092_);
v_it_x27_3094_ = v___x_3090_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_fst_3074_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3092_);
v_it_x27_3094_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_string_push(v_acc_3072_, v___x_3085_);
v_acc_3072_ = v___x_3095_;
v_a_3073_ = v_it_x27_3094_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_box(0);
lean_inc(v_snd_3075_);
v_pos_3077_ = v_a_3073_;
v_snd_3078_ = v_snd_3075_;
v_err_3079_ = v___x_3101_;
goto v___jp_3076_;
}
v___jp_3076_:
{
uint8_t v_decide_3080_; 
v_decide_3080_ = lean_nat_dec_eq(v_snd_3075_, v_snd_3078_);
lean_dec(v_snd_3078_);
lean_dec(v_snd_3075_);
if (v_decide_3080_ == 0)
{
lean_object* v___x_3081_; 
lean_dec_ref(v_acc_3072_);
lean_inc(v_err_3079_);
v___x_3081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3081_, 0, v_pos_3077_);
lean_ctor_set(v___x_3081_, 1, v_err_3079_);
return v___x_3081_;
}
else
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v_pos_3077_);
lean_ctor_set(v___x_3082_, 1, v_acc_3072_);
return v___x_3082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(lean_object* v_acc_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_fst_3107_; lean_object* v_snd_3108_; lean_object* v_pos_3110_; lean_object* v_snd_3111_; lean_object* v_err_3112_; lean_object* v___x_3116_; uint8_t v_decide_3117_; 
v_fst_3107_ = lean_ctor_get(v_a_3106_, 0);
v_snd_3108_ = lean_ctor_get(v_a_3106_, 1);
lean_inc(v_snd_3108_);
v___x_3116_ = lean_string_utf8_byte_size(v_fst_3107_);
v_decide_3117_ = lean_nat_dec_eq(v_snd_3108_, v___x_3116_);
if (v_decide_3117_ == 0)
{
uint32_t v___x_3118_; uint32_t v_c_3119_; uint8_t v___x_3120_; 
v___x_3118_ = 89;
v_c_3119_ = lean_string_utf8_get_fast(v_fst_3107_, v_snd_3108_);
v___x_3120_ = lean_uint32_dec_eq(v_c_3119_, v___x_3118_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1));
lean_inc(v_snd_3108_);
v_pos_3110_ = v_a_3106_;
v_snd_3111_ = v_snd_3108_;
v_err_3112_ = v___x_3121_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3131_; 
lean_inc(v_fst_3107_);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_a_3106_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; lean_object* v_unused_3133_; 
v_unused_3132_ = lean_ctor_get(v_a_3106_, 1);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v_a_3106_, 0);
lean_dec(v_unused_3133_);
v___x_3123_ = v_a_3106_;
v_isShared_3124_ = v_isSharedCheck_3131_;
goto v_resetjp_3122_;
}
else
{
lean_dec(v_a_3106_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3131_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v_it_x27_3127_; 
v___x_3125_ = lean_string_utf8_next_fast(v_fst_3107_, v_snd_3108_);
lean_dec(v_snd_3108_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 1, v___x_3125_);
v_it_x27_3127_ = v___x_3123_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_fst_3107_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_3125_);
v_it_x27_3127_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_string_push(v_acc_3105_, v___x_3118_);
v_acc_3105_ = v___x_3128_;
v_a_3106_ = v_it_x27_3127_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_box(0);
lean_inc(v_snd_3108_);
v_pos_3110_ = v_a_3106_;
v_snd_3111_ = v_snd_3108_;
v_err_3112_ = v___x_3134_;
goto v___jp_3109_;
}
v___jp_3109_:
{
uint8_t v_decide_3113_; 
v_decide_3113_ = lean_nat_dec_eq(v_snd_3108_, v_snd_3111_);
lean_dec(v_snd_3111_);
lean_dec(v_snd_3108_);
if (v_decide_3113_ == 0)
{
lean_object* v___x_3114_; 
lean_dec_ref(v_acc_3105_);
lean_inc(v_err_3112_);
v___x_3114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3114_, 0, v_pos_3110_);
lean_ctor_set(v___x_3114_, 1, v_err_3112_);
return v___x_3114_;
}
else
{
lean_object* v___x_3115_; 
v___x_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3115_, 0, v_pos_3110_);
lean_ctor_set(v___x_3115_, 1, v_acc_3105_);
return v___x_3115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(lean_object* v_acc_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_fst_3140_; lean_object* v_snd_3141_; lean_object* v_pos_3143_; lean_object* v_snd_3144_; lean_object* v_err_3145_; lean_object* v___x_3149_; uint8_t v_decide_3150_; 
v_fst_3140_ = lean_ctor_get(v_a_3139_, 0);
v_snd_3141_ = lean_ctor_get(v_a_3139_, 1);
lean_inc(v_snd_3141_);
v___x_3149_ = lean_string_utf8_byte_size(v_fst_3140_);
v_decide_3150_ = lean_nat_dec_eq(v_snd_3141_, v___x_3149_);
if (v_decide_3150_ == 0)
{
uint32_t v___x_3151_; uint32_t v_c_3152_; uint8_t v___x_3153_; 
v___x_3151_ = 110;
v_c_3152_ = lean_string_utf8_get_fast(v_fst_3140_, v_snd_3141_);
v___x_3153_ = lean_uint32_dec_eq(v_c_3152_, v___x_3151_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; 
v___x_3154_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1));
lean_inc(v_snd_3141_);
v_pos_3143_ = v_a_3139_;
v_snd_3144_ = v_snd_3141_;
v_err_3145_ = v___x_3154_;
goto v___jp_3142_;
}
else
{
lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3164_; 
lean_inc(v_fst_3140_);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_a_3139_);
if (v_isSharedCheck_3164_ == 0)
{
lean_object* v_unused_3165_; lean_object* v_unused_3166_; 
v_unused_3165_ = lean_ctor_get(v_a_3139_, 1);
lean_dec(v_unused_3165_);
v_unused_3166_ = lean_ctor_get(v_a_3139_, 0);
lean_dec(v_unused_3166_);
v___x_3156_ = v_a_3139_;
v_isShared_3157_ = v_isSharedCheck_3164_;
goto v_resetjp_3155_;
}
else
{
lean_dec(v_a_3139_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3164_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3158_; lean_object* v_it_x27_3160_; 
v___x_3158_ = lean_string_utf8_next_fast(v_fst_3140_, v_snd_3141_);
lean_dec(v_snd_3141_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 1, v___x_3158_);
v_it_x27_3160_ = v___x_3156_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_fst_3140_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v___x_3158_);
v_it_x27_3160_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_string_push(v_acc_3138_, v___x_3151_);
v_acc_3138_ = v___x_3161_;
v_a_3139_ = v_it_x27_3160_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3167_; 
v___x_3167_ = lean_box(0);
lean_inc(v_snd_3141_);
v_pos_3143_ = v_a_3139_;
v_snd_3144_ = v_snd_3141_;
v_err_3145_ = v___x_3167_;
goto v___jp_3142_;
}
v___jp_3142_:
{
uint8_t v_decide_3146_; 
v_decide_3146_ = lean_nat_dec_eq(v_snd_3141_, v_snd_3144_);
lean_dec(v_snd_3144_);
lean_dec(v_snd_3141_);
if (v_decide_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_dec_ref(v_acc_3138_);
lean_inc(v_err_3145_);
v___x_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_pos_3143_);
lean_ctor_set(v___x_3147_, 1, v_err_3145_);
return v___x_3147_;
}
else
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3148_, 0, v_pos_3143_);
lean_ctor_set(v___x_3148_, 1, v_acc_3138_);
return v___x_3148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(lean_object* v_acc_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_fst_3173_; lean_object* v_snd_3174_; lean_object* v_pos_3176_; lean_object* v_snd_3177_; lean_object* v_err_3178_; lean_object* v___x_3182_; uint8_t v_decide_3183_; 
v_fst_3173_ = lean_ctor_get(v_a_3172_, 0);
v_snd_3174_ = lean_ctor_get(v_a_3172_, 1);
lean_inc(v_snd_3174_);
v___x_3182_ = lean_string_utf8_byte_size(v_fst_3173_);
v_decide_3183_ = lean_nat_dec_eq(v_snd_3174_, v___x_3182_);
if (v_decide_3183_ == 0)
{
uint32_t v___x_3184_; uint32_t v_c_3185_; uint8_t v___x_3186_; 
v___x_3184_ = 71;
v_c_3185_ = lean_string_utf8_get_fast(v_fst_3173_, v_snd_3174_);
v___x_3186_ = lean_uint32_dec_eq(v_c_3185_, v___x_3184_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
v___x_3187_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1));
lean_inc(v_snd_3174_);
v_pos_3176_ = v_a_3172_;
v_snd_3177_ = v_snd_3174_;
v_err_3178_ = v___x_3187_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3197_; 
lean_inc(v_fst_3173_);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_a_3172_);
if (v_isSharedCheck_3197_ == 0)
{
lean_object* v_unused_3198_; lean_object* v_unused_3199_; 
v_unused_3198_ = lean_ctor_get(v_a_3172_, 1);
lean_dec(v_unused_3198_);
v_unused_3199_ = lean_ctor_get(v_a_3172_, 0);
lean_dec(v_unused_3199_);
v___x_3189_ = v_a_3172_;
v_isShared_3190_ = v_isSharedCheck_3197_;
goto v_resetjp_3188_;
}
else
{
lean_dec(v_a_3172_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3197_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; lean_object* v_it_x27_3193_; 
v___x_3191_ = lean_string_utf8_next_fast(v_fst_3173_, v_snd_3174_);
lean_dec(v_snd_3174_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 1, v___x_3191_);
v_it_x27_3193_ = v___x_3189_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_fst_3173_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3191_);
v_it_x27_3193_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; 
v___x_3194_ = lean_string_push(v_acc_3171_, v___x_3184_);
v_acc_3171_ = v___x_3194_;
v_a_3172_ = v_it_x27_3193_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_box(0);
lean_inc(v_snd_3174_);
v_pos_3176_ = v_a_3172_;
v_snd_3177_ = v_snd_3174_;
v_err_3178_ = v___x_3200_;
goto v___jp_3175_;
}
v___jp_3175_:
{
uint8_t v_decide_3179_; 
v_decide_3179_ = lean_nat_dec_eq(v_snd_3174_, v_snd_3177_);
lean_dec(v_snd_3177_);
lean_dec(v_snd_3174_);
if (v_decide_3179_ == 0)
{
lean_object* v___x_3180_; 
lean_dec_ref(v_acc_3171_);
lean_inc(v_err_3178_);
v___x_3180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3180_, 0, v_pos_3176_);
lean_ctor_set(v___x_3180_, 1, v_err_3178_);
return v___x_3180_;
}
else
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v_pos_3176_);
lean_ctor_set(v___x_3181_, 1, v_acc_3171_);
return v___x_3181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(lean_object* v_acc_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v_fst_3206_; lean_object* v_snd_3207_; lean_object* v_pos_3209_; lean_object* v_snd_3210_; lean_object* v_err_3211_; lean_object* v___x_3215_; uint8_t v_decide_3216_; 
v_fst_3206_ = lean_ctor_get(v_a_3205_, 0);
v_snd_3207_ = lean_ctor_get(v_a_3205_, 1);
lean_inc(v_snd_3207_);
v___x_3215_ = lean_string_utf8_byte_size(v_fst_3206_);
v_decide_3216_ = lean_nat_dec_eq(v_snd_3207_, v___x_3215_);
if (v_decide_3216_ == 0)
{
uint32_t v___x_3217_; uint32_t v_c_3218_; uint8_t v___x_3219_; 
v___x_3217_ = 86;
v_c_3218_ = lean_string_utf8_get_fast(v_fst_3206_, v_snd_3207_);
v___x_3219_ = lean_uint32_dec_eq(v_c_3218_, v___x_3217_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
v___x_3220_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1));
lean_inc(v_snd_3207_);
v_pos_3209_ = v_a_3205_;
v_snd_3210_ = v_snd_3207_;
v_err_3211_ = v___x_3220_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3230_; 
lean_inc(v_fst_3206_);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_a_3205_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; lean_object* v_unused_3232_; 
v_unused_3231_ = lean_ctor_get(v_a_3205_, 1);
lean_dec(v_unused_3231_);
v_unused_3232_ = lean_ctor_get(v_a_3205_, 0);
lean_dec(v_unused_3232_);
v___x_3222_ = v_a_3205_;
v_isShared_3223_ = v_isSharedCheck_3230_;
goto v_resetjp_3221_;
}
else
{
lean_dec(v_a_3205_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3230_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; lean_object* v_it_x27_3226_; 
v___x_3224_ = lean_string_utf8_next_fast(v_fst_3206_, v_snd_3207_);
lean_dec(v_snd_3207_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 1, v___x_3224_);
v_it_x27_3226_ = v___x_3222_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_fst_3206_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v___x_3224_);
v_it_x27_3226_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_string_push(v_acc_3204_, v___x_3217_);
v_acc_3204_ = v___x_3227_;
v_a_3205_ = v_it_x27_3226_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_box(0);
lean_inc(v_snd_3207_);
v_pos_3209_ = v_a_3205_;
v_snd_3210_ = v_snd_3207_;
v_err_3211_ = v___x_3233_;
goto v___jp_3208_;
}
v___jp_3208_:
{
uint8_t v_decide_3212_; 
v_decide_3212_ = lean_nat_dec_eq(v_snd_3207_, v_snd_3210_);
lean_dec(v_snd_3210_);
lean_dec(v_snd_3207_);
if (v_decide_3212_ == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref(v_acc_3204_);
lean_inc(v_err_3211_);
v___x_3213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3213_, 0, v_pos_3209_);
lean_ctor_set(v___x_3213_, 1, v_err_3211_);
return v___x_3213_;
}
else
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v_pos_3209_);
lean_ctor_set(v___x_3214_, 1, v_acc_3204_);
return v___x_3214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(lean_object* v_acc_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_fst_3239_; lean_object* v_snd_3240_; lean_object* v_pos_3242_; lean_object* v_snd_3243_; lean_object* v_err_3244_; lean_object* v___x_3248_; uint8_t v_decide_3249_; 
v_fst_3239_ = lean_ctor_get(v_a_3238_, 0);
v_snd_3240_ = lean_ctor_get(v_a_3238_, 1);
lean_inc(v_snd_3240_);
v___x_3248_ = lean_string_utf8_byte_size(v_fst_3239_);
v_decide_3249_ = lean_nat_dec_eq(v_snd_3240_, v___x_3248_);
if (v_decide_3249_ == 0)
{
uint32_t v___x_3250_; uint32_t v_c_3251_; uint8_t v___x_3252_; 
v___x_3250_ = 83;
v_c_3251_ = lean_string_utf8_get_fast(v_fst_3239_, v_snd_3240_);
v___x_3252_ = lean_uint32_dec_eq(v_c_3251_, v___x_3250_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; 
v___x_3253_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1));
lean_inc(v_snd_3240_);
v_pos_3242_ = v_a_3238_;
v_snd_3243_ = v_snd_3240_;
v_err_3244_ = v___x_3253_;
goto v___jp_3241_;
}
else
{
lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3263_; 
lean_inc(v_fst_3239_);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_a_3238_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; lean_object* v_unused_3265_; 
v_unused_3264_ = lean_ctor_get(v_a_3238_, 1);
lean_dec(v_unused_3264_);
v_unused_3265_ = lean_ctor_get(v_a_3238_, 0);
lean_dec(v_unused_3265_);
v___x_3255_ = v_a_3238_;
v_isShared_3256_ = v_isSharedCheck_3263_;
goto v_resetjp_3254_;
}
else
{
lean_dec(v_a_3238_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3263_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3257_; lean_object* v_it_x27_3259_; 
v___x_3257_ = lean_string_utf8_next_fast(v_fst_3239_, v_snd_3240_);
lean_dec(v_snd_3240_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 1, v___x_3257_);
v_it_x27_3259_ = v___x_3255_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_fst_3239_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___x_3257_);
v_it_x27_3259_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3260_; 
v___x_3260_ = lean_string_push(v_acc_3237_, v___x_3250_);
v_acc_3237_ = v___x_3260_;
v_a_3238_ = v_it_x27_3259_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_box(0);
lean_inc(v_snd_3240_);
v_pos_3242_ = v_a_3238_;
v_snd_3243_ = v_snd_3240_;
v_err_3244_ = v___x_3266_;
goto v___jp_3241_;
}
v___jp_3241_:
{
uint8_t v_decide_3245_; 
v_decide_3245_ = lean_nat_dec_eq(v_snd_3240_, v_snd_3243_);
lean_dec(v_snd_3243_);
lean_dec(v_snd_3240_);
if (v_decide_3245_ == 0)
{
lean_object* v___x_3246_; 
lean_dec_ref(v_acc_3237_);
lean_inc(v_err_3244_);
v___x_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3246_, 0, v_pos_3242_);
lean_ctor_set(v___x_3246_, 1, v_err_3244_);
return v___x_3246_;
}
else
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3247_, 0, v_pos_3242_);
lean_ctor_set(v___x_3247_, 1, v_acc_3237_);
return v___x_3247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(lean_object* v_acc_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_fst_3272_; lean_object* v_snd_3273_; lean_object* v_pos_3275_; lean_object* v_snd_3276_; lean_object* v_err_3277_; lean_object* v___x_3281_; uint8_t v_decide_3282_; 
v_fst_3272_ = lean_ctor_get(v_a_3271_, 0);
v_snd_3273_ = lean_ctor_get(v_a_3271_, 1);
lean_inc(v_snd_3273_);
v___x_3281_ = lean_string_utf8_byte_size(v_fst_3272_);
v_decide_3282_ = lean_nat_dec_eq(v_snd_3273_, v___x_3281_);
if (v_decide_3282_ == 0)
{
uint32_t v___x_3283_; uint32_t v_c_3284_; uint8_t v___x_3285_; 
v___x_3283_ = 104;
v_c_3284_ = lean_string_utf8_get_fast(v_fst_3272_, v_snd_3273_);
v___x_3285_ = lean_uint32_dec_eq(v_c_3284_, v___x_3283_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; 
v___x_3286_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1));
lean_inc(v_snd_3273_);
v_pos_3275_ = v_a_3271_;
v_snd_3276_ = v_snd_3273_;
v_err_3277_ = v___x_3286_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3296_; 
lean_inc(v_fst_3272_);
v_isSharedCheck_3296_ = !lean_is_exclusive(v_a_3271_);
if (v_isSharedCheck_3296_ == 0)
{
lean_object* v_unused_3297_; lean_object* v_unused_3298_; 
v_unused_3297_ = lean_ctor_get(v_a_3271_, 1);
lean_dec(v_unused_3297_);
v_unused_3298_ = lean_ctor_get(v_a_3271_, 0);
lean_dec(v_unused_3298_);
v___x_3288_ = v_a_3271_;
v_isShared_3289_ = v_isSharedCheck_3296_;
goto v_resetjp_3287_;
}
else
{
lean_dec(v_a_3271_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3296_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3290_; lean_object* v_it_x27_3292_; 
v___x_3290_ = lean_string_utf8_next_fast(v_fst_3272_, v_snd_3273_);
lean_dec(v_snd_3273_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 1, v___x_3290_);
v_it_x27_3292_ = v___x_3288_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_fst_3272_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v___x_3290_);
v_it_x27_3292_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3293_; 
v___x_3293_ = lean_string_push(v_acc_3270_, v___x_3283_);
v_acc_3270_ = v___x_3293_;
v_a_3271_ = v_it_x27_3292_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_box(0);
lean_inc(v_snd_3273_);
v_pos_3275_ = v_a_3271_;
v_snd_3276_ = v_snd_3273_;
v_err_3277_ = v___x_3299_;
goto v___jp_3274_;
}
v___jp_3274_:
{
uint8_t v_decide_3278_; 
v_decide_3278_ = lean_nat_dec_eq(v_snd_3273_, v_snd_3276_);
lean_dec(v_snd_3276_);
lean_dec(v_snd_3273_);
if (v_decide_3278_ == 0)
{
lean_object* v___x_3279_; 
lean_dec_ref(v_acc_3270_);
lean_inc(v_err_3277_);
v___x_3279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3279_, 0, v_pos_3275_);
lean_ctor_set(v___x_3279_, 1, v_err_3277_);
return v___x_3279_;
}
else
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_pos_3275_);
lean_ctor_set(v___x_3280_, 1, v_acc_3270_);
return v___x_3280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(lean_object* v_acc_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v_fst_3305_; lean_object* v_snd_3306_; lean_object* v_pos_3308_; lean_object* v_snd_3309_; lean_object* v_err_3310_; lean_object* v___x_3314_; uint8_t v_decide_3315_; 
v_fst_3305_ = lean_ctor_get(v_a_3304_, 0);
v_snd_3306_ = lean_ctor_get(v_a_3304_, 1);
lean_inc(v_snd_3306_);
v___x_3314_ = lean_string_utf8_byte_size(v_fst_3305_);
v_decide_3315_ = lean_nat_dec_eq(v_snd_3306_, v___x_3314_);
if (v_decide_3315_ == 0)
{
uint32_t v___x_3316_; uint32_t v_c_3317_; uint8_t v___x_3318_; 
v___x_3316_ = 81;
v_c_3317_ = lean_string_utf8_get_fast(v_fst_3305_, v_snd_3306_);
v___x_3318_ = lean_uint32_dec_eq(v_c_3317_, v___x_3316_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1));
lean_inc(v_snd_3306_);
v_pos_3308_ = v_a_3304_;
v_snd_3309_ = v_snd_3306_;
v_err_3310_ = v___x_3319_;
goto v___jp_3307_;
}
else
{
lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3329_; 
lean_inc(v_fst_3305_);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_a_3304_);
if (v_isSharedCheck_3329_ == 0)
{
lean_object* v_unused_3330_; lean_object* v_unused_3331_; 
v_unused_3330_ = lean_ctor_get(v_a_3304_, 1);
lean_dec(v_unused_3330_);
v_unused_3331_ = lean_ctor_get(v_a_3304_, 0);
lean_dec(v_unused_3331_);
v___x_3321_ = v_a_3304_;
v_isShared_3322_ = v_isSharedCheck_3329_;
goto v_resetjp_3320_;
}
else
{
lean_dec(v_a_3304_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3329_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; lean_object* v_it_x27_3325_; 
v___x_3323_ = lean_string_utf8_next_fast(v_fst_3305_, v_snd_3306_);
lean_dec(v_snd_3306_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 1, v___x_3323_);
v_it_x27_3325_ = v___x_3321_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_fst_3305_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v___x_3323_);
v_it_x27_3325_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_string_push(v_acc_3303_, v___x_3316_);
v_acc_3303_ = v___x_3326_;
v_a_3304_ = v_it_x27_3325_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_box(0);
lean_inc(v_snd_3306_);
v_pos_3308_ = v_a_3304_;
v_snd_3309_ = v_snd_3306_;
v_err_3310_ = v___x_3332_;
goto v___jp_3307_;
}
v___jp_3307_:
{
uint8_t v_decide_3311_; 
v_decide_3311_ = lean_nat_dec_eq(v_snd_3306_, v_snd_3309_);
lean_dec(v_snd_3309_);
lean_dec(v_snd_3306_);
if (v_decide_3311_ == 0)
{
lean_object* v___x_3312_; 
lean_dec_ref(v_acc_3303_);
lean_inc(v_err_3310_);
v___x_3312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3312_, 0, v_pos_3308_);
lean_ctor_set(v___x_3312_, 1, v_err_3310_);
return v___x_3312_;
}
else
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_pos_3308_);
lean_ctor_set(v___x_3313_, 1, v_acc_3303_);
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(lean_object* v_acc_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v_fst_3338_; lean_object* v_snd_3339_; lean_object* v_pos_3341_; lean_object* v_snd_3342_; lean_object* v_err_3343_; lean_object* v___x_3347_; uint8_t v_decide_3348_; 
v_fst_3338_ = lean_ctor_get(v_a_3337_, 0);
v_snd_3339_ = lean_ctor_get(v_a_3337_, 1);
lean_inc(v_snd_3339_);
v___x_3347_ = lean_string_utf8_byte_size(v_fst_3338_);
v_decide_3348_ = lean_nat_dec_eq(v_snd_3339_, v___x_3347_);
if (v_decide_3348_ == 0)
{
uint32_t v___x_3349_; uint32_t v_c_3350_; uint8_t v___x_3351_; 
v___x_3349_ = 68;
v_c_3350_ = lean_string_utf8_get_fast(v_fst_3338_, v_snd_3339_);
v___x_3351_ = lean_uint32_dec_eq(v_c_3350_, v___x_3349_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; 
v___x_3352_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1));
lean_inc(v_snd_3339_);
v_pos_3341_ = v_a_3337_;
v_snd_3342_ = v_snd_3339_;
v_err_3343_ = v___x_3352_;
goto v___jp_3340_;
}
else
{
lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3362_; 
lean_inc(v_fst_3338_);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_a_3337_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; lean_object* v_unused_3364_; 
v_unused_3363_ = lean_ctor_get(v_a_3337_, 1);
lean_dec(v_unused_3363_);
v_unused_3364_ = lean_ctor_get(v_a_3337_, 0);
lean_dec(v_unused_3364_);
v___x_3354_ = v_a_3337_;
v_isShared_3355_ = v_isSharedCheck_3362_;
goto v_resetjp_3353_;
}
else
{
lean_dec(v_a_3337_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3362_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v_it_x27_3358_; 
v___x_3356_ = lean_string_utf8_next_fast(v_fst_3338_, v_snd_3339_);
lean_dec(v_snd_3339_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 1, v___x_3356_);
v_it_x27_3358_ = v___x_3354_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_fst_3338_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v___x_3356_);
v_it_x27_3358_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_string_push(v_acc_3336_, v___x_3349_);
v_acc_3336_ = v___x_3359_;
v_a_3337_ = v_it_x27_3358_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_box(0);
lean_inc(v_snd_3339_);
v_pos_3341_ = v_a_3337_;
v_snd_3342_ = v_snd_3339_;
v_err_3343_ = v___x_3365_;
goto v___jp_3340_;
}
v___jp_3340_:
{
uint8_t v_decide_3344_; 
v_decide_3344_ = lean_nat_dec_eq(v_snd_3339_, v_snd_3342_);
lean_dec(v_snd_3342_);
lean_dec(v_snd_3339_);
if (v_decide_3344_ == 0)
{
lean_object* v___x_3345_; 
lean_dec_ref(v_acc_3336_);
lean_inc(v_err_3343_);
v___x_3345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3345_, 0, v_pos_3341_);
lean_ctor_set(v___x_3345_, 1, v_err_3343_);
return v___x_3345_;
}
else
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3346_, 0, v_pos_3341_);
lean_ctor_set(v___x_3346_, 1, v_acc_3336_);
return v___x_3346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(lean_object* v_acc_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_fst_3371_; lean_object* v_snd_3372_; lean_object* v_pos_3374_; lean_object* v_snd_3375_; lean_object* v_err_3376_; lean_object* v___x_3380_; uint8_t v_decide_3381_; 
v_fst_3371_ = lean_ctor_get(v_a_3370_, 0);
v_snd_3372_ = lean_ctor_get(v_a_3370_, 1);
lean_inc(v_snd_3372_);
v___x_3380_ = lean_string_utf8_byte_size(v_fst_3371_);
v_decide_3381_ = lean_nat_dec_eq(v_snd_3372_, v___x_3380_);
if (v_decide_3381_ == 0)
{
uint32_t v___x_3382_; uint32_t v_c_3383_; uint8_t v___x_3384_; 
v___x_3382_ = 88;
v_c_3383_ = lean_string_utf8_get_fast(v_fst_3371_, v_snd_3372_);
v___x_3384_ = lean_uint32_dec_eq(v_c_3383_, v___x_3382_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; 
v___x_3385_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1));
lean_inc(v_snd_3372_);
v_pos_3374_ = v_a_3370_;
v_snd_3375_ = v_snd_3372_;
v_err_3376_ = v___x_3385_;
goto v___jp_3373_;
}
else
{
lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3395_; 
lean_inc(v_fst_3371_);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_a_3370_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; lean_object* v_unused_3397_; 
v_unused_3396_ = lean_ctor_get(v_a_3370_, 1);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_a_3370_, 0);
lean_dec(v_unused_3397_);
v___x_3387_ = v_a_3370_;
v_isShared_3388_ = v_isSharedCheck_3395_;
goto v_resetjp_3386_;
}
else
{
lean_dec(v_a_3370_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3395_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v_it_x27_3391_; 
v___x_3389_ = lean_string_utf8_next_fast(v_fst_3371_, v_snd_3372_);
lean_dec(v_snd_3372_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 1, v___x_3389_);
v_it_x27_3391_ = v___x_3387_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_fst_3371_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___x_3389_);
v_it_x27_3391_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_string_push(v_acc_3369_, v___x_3382_);
v_acc_3369_ = v___x_3392_;
v_a_3370_ = v_it_x27_3391_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_box(0);
lean_inc(v_snd_3372_);
v_pos_3374_ = v_a_3370_;
v_snd_3375_ = v_snd_3372_;
v_err_3376_ = v___x_3398_;
goto v___jp_3373_;
}
v___jp_3373_:
{
uint8_t v_decide_3377_; 
v_decide_3377_ = lean_nat_dec_eq(v_snd_3372_, v_snd_3375_);
lean_dec(v_snd_3375_);
lean_dec(v_snd_3372_);
if (v_decide_3377_ == 0)
{
lean_object* v___x_3378_; 
lean_dec_ref(v_acc_3369_);
lean_inc(v_err_3376_);
v___x_3378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3378_, 0, v_pos_3374_);
lean_ctor_set(v___x_3378_, 1, v_err_3376_);
return v___x_3378_;
}
else
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3379_, 0, v_pos_3374_);
lean_ctor_set(v___x_3379_, 1, v_acc_3369_);
return v___x_3379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(lean_object* v_acc_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v_fst_3404_; lean_object* v_snd_3405_; lean_object* v_pos_3407_; lean_object* v_snd_3408_; lean_object* v_err_3409_; lean_object* v___x_3413_; uint8_t v_decide_3414_; 
v_fst_3404_ = lean_ctor_get(v_a_3403_, 0);
v_snd_3405_ = lean_ctor_get(v_a_3403_, 1);
lean_inc(v_snd_3405_);
v___x_3413_ = lean_string_utf8_byte_size(v_fst_3404_);
v_decide_3414_ = lean_nat_dec_eq(v_snd_3405_, v___x_3413_);
if (v_decide_3414_ == 0)
{
uint32_t v___x_3415_; uint32_t v_c_3416_; uint8_t v___x_3417_; 
v___x_3415_ = 122;
v_c_3416_ = lean_string_utf8_get_fast(v_fst_3404_, v_snd_3405_);
v___x_3417_ = lean_uint32_dec_eq(v_c_3416_, v___x_3415_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; 
v___x_3418_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1));
lean_inc(v_snd_3405_);
v_pos_3407_ = v_a_3403_;
v_snd_3408_ = v_snd_3405_;
v_err_3409_ = v___x_3418_;
goto v___jp_3406_;
}
else
{
lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3428_; 
lean_inc(v_fst_3404_);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_a_3403_);
if (v_isSharedCheck_3428_ == 0)
{
lean_object* v_unused_3429_; lean_object* v_unused_3430_; 
v_unused_3429_ = lean_ctor_get(v_a_3403_, 1);
lean_dec(v_unused_3429_);
v_unused_3430_ = lean_ctor_get(v_a_3403_, 0);
lean_dec(v_unused_3430_);
v___x_3420_ = v_a_3403_;
v_isShared_3421_ = v_isSharedCheck_3428_;
goto v_resetjp_3419_;
}
else
{
lean_dec(v_a_3403_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3428_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v_it_x27_3424_; 
v___x_3422_ = lean_string_utf8_next_fast(v_fst_3404_, v_snd_3405_);
lean_dec(v_snd_3405_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 1, v___x_3422_);
v_it_x27_3424_ = v___x_3420_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_fst_3404_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v___x_3422_);
v_it_x27_3424_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_string_push(v_acc_3402_, v___x_3415_);
v_acc_3402_ = v___x_3425_;
v_a_3403_ = v_it_x27_3424_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3431_; 
v___x_3431_ = lean_box(0);
lean_inc(v_snd_3405_);
v_pos_3407_ = v_a_3403_;
v_snd_3408_ = v_snd_3405_;
v_err_3409_ = v___x_3431_;
goto v___jp_3406_;
}
v___jp_3406_:
{
uint8_t v_decide_3410_; 
v_decide_3410_ = lean_nat_dec_eq(v_snd_3405_, v_snd_3408_);
lean_dec(v_snd_3408_);
lean_dec(v_snd_3405_);
if (v_decide_3410_ == 0)
{
lean_object* v___x_3411_; 
lean_dec_ref(v_acc_3402_);
lean_inc(v_err_3409_);
v___x_3411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3411_, 0, v_pos_3407_);
lean_ctor_set(v___x_3411_, 1, v_err_3409_);
return v___x_3411_;
}
else
{
lean_object* v___x_3412_; 
v___x_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3412_, 0, v_pos_3407_);
lean_ctor_set(v___x_3412_, 1, v_acc_3402_);
return v___x_3412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(lean_object* v_acc_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v_fst_3437_; lean_object* v_snd_3438_; lean_object* v_pos_3440_; lean_object* v_snd_3441_; lean_object* v_err_3442_; lean_object* v___x_3446_; uint8_t v_decide_3447_; 
v_fst_3437_ = lean_ctor_get(v_a_3436_, 0);
v_snd_3438_ = lean_ctor_get(v_a_3436_, 1);
lean_inc(v_snd_3438_);
v___x_3446_ = lean_string_utf8_byte_size(v_fst_3437_);
v_decide_3447_ = lean_nat_dec_eq(v_snd_3438_, v___x_3446_);
if (v_decide_3447_ == 0)
{
uint32_t v___x_3448_; uint32_t v_c_3449_; uint8_t v___x_3450_; 
v___x_3448_ = 115;
v_c_3449_ = lean_string_utf8_get_fast(v_fst_3437_, v_snd_3438_);
v___x_3450_ = lean_uint32_dec_eq(v_c_3449_, v___x_3448_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
v___x_3451_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1));
lean_inc(v_snd_3438_);
v_pos_3440_ = v_a_3436_;
v_snd_3441_ = v_snd_3438_;
v_err_3442_ = v___x_3451_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3461_; 
lean_inc(v_fst_3437_);
v_isSharedCheck_3461_ = !lean_is_exclusive(v_a_3436_);
if (v_isSharedCheck_3461_ == 0)
{
lean_object* v_unused_3462_; lean_object* v_unused_3463_; 
v_unused_3462_ = lean_ctor_get(v_a_3436_, 1);
lean_dec(v_unused_3462_);
v_unused_3463_ = lean_ctor_get(v_a_3436_, 0);
lean_dec(v_unused_3463_);
v___x_3453_ = v_a_3436_;
v_isShared_3454_ = v_isSharedCheck_3461_;
goto v_resetjp_3452_;
}
else
{
lean_dec(v_a_3436_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3461_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v_it_x27_3457_; 
v___x_3455_ = lean_string_utf8_next_fast(v_fst_3437_, v_snd_3438_);
lean_dec(v_snd_3438_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v___x_3455_);
v_it_x27_3457_ = v___x_3453_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_fst_3437_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v___x_3455_);
v_it_x27_3457_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_string_push(v_acc_3435_, v___x_3448_);
v_acc_3435_ = v___x_3458_;
v_a_3436_ = v_it_x27_3457_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3464_; 
v___x_3464_ = lean_box(0);
lean_inc(v_snd_3438_);
v_pos_3440_ = v_a_3436_;
v_snd_3441_ = v_snd_3438_;
v_err_3442_ = v___x_3464_;
goto v___jp_3439_;
}
v___jp_3439_:
{
uint8_t v_decide_3443_; 
v_decide_3443_ = lean_nat_dec_eq(v_snd_3438_, v_snd_3441_);
lean_dec(v_snd_3441_);
lean_dec(v_snd_3438_);
if (v_decide_3443_ == 0)
{
lean_object* v___x_3444_; 
lean_dec_ref(v_acc_3435_);
lean_inc(v_err_3442_);
v___x_3444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3444_, 0, v_pos_3440_);
lean_ctor_set(v___x_3444_, 1, v_err_3442_);
return v___x_3444_;
}
else
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3445_, 0, v_pos_3440_);
lean_ctor_set(v___x_3445_, 1, v_acc_3435_);
return v___x_3445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(lean_object* v_acc_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v_fst_3470_; lean_object* v_snd_3471_; lean_object* v_pos_3473_; lean_object* v_snd_3474_; lean_object* v_err_3475_; lean_object* v___x_3479_; uint8_t v_decide_3480_; 
v_fst_3470_ = lean_ctor_get(v_a_3469_, 0);
v_snd_3471_ = lean_ctor_get(v_a_3469_, 1);
lean_inc(v_snd_3471_);
v___x_3479_ = lean_string_utf8_byte_size(v_fst_3470_);
v_decide_3480_ = lean_nat_dec_eq(v_snd_3471_, v___x_3479_);
if (v_decide_3480_ == 0)
{
uint32_t v___x_3481_; uint32_t v_c_3482_; uint8_t v___x_3483_; 
v___x_3481_ = 75;
v_c_3482_ = lean_string_utf8_get_fast(v_fst_3470_, v_snd_3471_);
v___x_3483_ = lean_uint32_dec_eq(v_c_3482_, v___x_3481_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; 
v___x_3484_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1));
lean_inc(v_snd_3471_);
v_pos_3473_ = v_a_3469_;
v_snd_3474_ = v_snd_3471_;
v_err_3475_ = v___x_3484_;
goto v___jp_3472_;
}
else
{
lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3494_; 
lean_inc(v_fst_3470_);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_a_3469_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; lean_object* v_unused_3496_; 
v_unused_3495_ = lean_ctor_get(v_a_3469_, 1);
lean_dec(v_unused_3495_);
v_unused_3496_ = lean_ctor_get(v_a_3469_, 0);
lean_dec(v_unused_3496_);
v___x_3486_ = v_a_3469_;
v_isShared_3487_ = v_isSharedCheck_3494_;
goto v_resetjp_3485_;
}
else
{
lean_dec(v_a_3469_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3494_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v_it_x27_3490_; 
v___x_3488_ = lean_string_utf8_next_fast(v_fst_3470_, v_snd_3471_);
lean_dec(v_snd_3471_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 1, v___x_3488_);
v_it_x27_3490_ = v___x_3486_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_fst_3470_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v___x_3488_);
v_it_x27_3490_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_string_push(v_acc_3468_, v___x_3481_);
v_acc_3468_ = v___x_3491_;
v_a_3469_ = v_it_x27_3490_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_box(0);
lean_inc(v_snd_3471_);
v_pos_3473_ = v_a_3469_;
v_snd_3474_ = v_snd_3471_;
v_err_3475_ = v___x_3497_;
goto v___jp_3472_;
}
v___jp_3472_:
{
uint8_t v_decide_3476_; 
v_decide_3476_ = lean_nat_dec_eq(v_snd_3471_, v_snd_3474_);
lean_dec(v_snd_3474_);
lean_dec(v_snd_3471_);
if (v_decide_3476_ == 0)
{
lean_object* v___x_3477_; 
lean_dec_ref(v_acc_3468_);
lean_inc(v_err_3475_);
v___x_3477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3477_, 0, v_pos_3473_);
lean_ctor_set(v___x_3477_, 1, v_err_3475_);
return v___x_3477_;
}
else
{
lean_object* v___x_3478_; 
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v_pos_3473_);
lean_ctor_set(v___x_3478_, 1, v_acc_3468_);
return v___x_3478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(lean_object* v_acc_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_fst_3503_; lean_object* v_snd_3504_; lean_object* v_pos_3506_; lean_object* v_snd_3507_; lean_object* v_err_3508_; lean_object* v___x_3512_; uint8_t v_decide_3513_; 
v_fst_3503_ = lean_ctor_get(v_a_3502_, 0);
v_snd_3504_ = lean_ctor_get(v_a_3502_, 1);
lean_inc(v_snd_3504_);
v___x_3512_ = lean_string_utf8_byte_size(v_fst_3503_);
v_decide_3513_ = lean_nat_dec_eq(v_snd_3504_, v___x_3512_);
if (v_decide_3513_ == 0)
{
uint32_t v___x_3514_; uint32_t v_c_3515_; uint8_t v___x_3516_; 
v___x_3514_ = 101;
v_c_3515_ = lean_string_utf8_get_fast(v_fst_3503_, v_snd_3504_);
v___x_3516_ = lean_uint32_dec_eq(v_c_3515_, v___x_3514_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
v___x_3517_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1));
lean_inc(v_snd_3504_);
v_pos_3506_ = v_a_3502_;
v_snd_3507_ = v_snd_3504_;
v_err_3508_ = v___x_3517_;
goto v___jp_3505_;
}
else
{
lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3527_; 
lean_inc(v_fst_3503_);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_a_3502_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; lean_object* v_unused_3529_; 
v_unused_3528_ = lean_ctor_get(v_a_3502_, 1);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v_a_3502_, 0);
lean_dec(v_unused_3529_);
v___x_3519_ = v_a_3502_;
v_isShared_3520_ = v_isSharedCheck_3527_;
goto v_resetjp_3518_;
}
else
{
lean_dec(v_a_3502_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3527_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v_it_x27_3523_; 
v___x_3521_ = lean_string_utf8_next_fast(v_fst_3503_, v_snd_3504_);
lean_dec(v_snd_3504_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v___x_3521_);
v_it_x27_3523_ = v___x_3519_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_fst_3503_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v___x_3521_);
v_it_x27_3523_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3524_; 
v___x_3524_ = lean_string_push(v_acc_3501_, v___x_3514_);
v_acc_3501_ = v___x_3524_;
v_a_3502_ = v_it_x27_3523_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_box(0);
lean_inc(v_snd_3504_);
v_pos_3506_ = v_a_3502_;
v_snd_3507_ = v_snd_3504_;
v_err_3508_ = v___x_3530_;
goto v___jp_3505_;
}
v___jp_3505_:
{
uint8_t v_decide_3509_; 
v_decide_3509_ = lean_nat_dec_eq(v_snd_3504_, v_snd_3507_);
lean_dec(v_snd_3507_);
lean_dec(v_snd_3504_);
if (v_decide_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_dec_ref(v_acc_3501_);
lean_inc(v_err_3508_);
v___x_3510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3510_, 0, v_pos_3506_);
lean_ctor_set(v___x_3510_, 1, v_err_3508_);
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; 
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v_pos_3506_);
lean_ctor_set(v___x_3511_, 1, v_acc_3501_);
return v___x_3511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(lean_object* v_acc_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_fst_3536_; lean_object* v_snd_3537_; lean_object* v_pos_3539_; lean_object* v_snd_3540_; lean_object* v_err_3541_; lean_object* v___x_3545_; uint8_t v_decide_3546_; 
v_fst_3536_ = lean_ctor_get(v_a_3535_, 0);
v_snd_3537_ = lean_ctor_get(v_a_3535_, 1);
lean_inc(v_snd_3537_);
v___x_3545_ = lean_string_utf8_byte_size(v_fst_3536_);
v_decide_3546_ = lean_nat_dec_eq(v_snd_3537_, v___x_3545_);
if (v_decide_3546_ == 0)
{
uint32_t v___x_3547_; uint32_t v_c_3548_; uint8_t v___x_3549_; 
v___x_3547_ = 77;
v_c_3548_ = lean_string_utf8_get_fast(v_fst_3536_, v_snd_3537_);
v___x_3549_ = lean_uint32_dec_eq(v_c_3548_, v___x_3547_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; 
v___x_3550_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1));
lean_inc(v_snd_3537_);
v_pos_3539_ = v_a_3535_;
v_snd_3540_ = v_snd_3537_;
v_err_3541_ = v___x_3550_;
goto v___jp_3538_;
}
else
{
lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3560_; 
lean_inc(v_fst_3536_);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_a_3535_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; lean_object* v_unused_3562_; 
v_unused_3561_ = lean_ctor_get(v_a_3535_, 1);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_a_3535_, 0);
lean_dec(v_unused_3562_);
v___x_3552_ = v_a_3535_;
v_isShared_3553_ = v_isSharedCheck_3560_;
goto v_resetjp_3551_;
}
else
{
lean_dec(v_a_3535_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3560_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v_it_x27_3556_; 
v___x_3554_ = lean_string_utf8_next_fast(v_fst_3536_, v_snd_3537_);
lean_dec(v_snd_3537_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v___x_3554_);
v_it_x27_3556_ = v___x_3552_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_fst_3536_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v___x_3554_);
v_it_x27_3556_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_string_push(v_acc_3534_, v___x_3547_);
v_acc_3534_ = v___x_3557_;
v_a_3535_ = v_it_x27_3556_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_box(0);
lean_inc(v_snd_3537_);
v_pos_3539_ = v_a_3535_;
v_snd_3540_ = v_snd_3537_;
v_err_3541_ = v___x_3563_;
goto v___jp_3538_;
}
v___jp_3538_:
{
uint8_t v_decide_3542_; 
v_decide_3542_ = lean_nat_dec_eq(v_snd_3537_, v_snd_3540_);
lean_dec(v_snd_3540_);
lean_dec(v_snd_3537_);
if (v_decide_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_dec_ref(v_acc_3534_);
lean_inc(v_err_3541_);
v___x_3543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3543_, 0, v_pos_3539_);
lean_ctor_set(v___x_3543_, 1, v_err_3541_);
return v___x_3543_;
}
else
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3544_, 0, v_pos_3539_);
lean_ctor_set(v___x_3544_, 1, v_acc_3534_);
return v___x_3544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(lean_object* v_acc_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v_fst_3569_; lean_object* v_snd_3570_; lean_object* v_pos_3572_; lean_object* v_snd_3573_; lean_object* v_err_3574_; lean_object* v___x_3578_; uint8_t v_decide_3579_; 
v_fst_3569_ = lean_ctor_get(v_a_3568_, 0);
v_snd_3570_ = lean_ctor_get(v_a_3568_, 1);
lean_inc(v_snd_3570_);
v___x_3578_ = lean_string_utf8_byte_size(v_fst_3569_);
v_decide_3579_ = lean_nat_dec_eq(v_snd_3570_, v___x_3578_);
if (v_decide_3579_ == 0)
{
uint32_t v___x_3580_; uint32_t v_c_3581_; uint8_t v___x_3582_; 
v___x_3580_ = 119;
v_c_3581_ = lean_string_utf8_get_fast(v_fst_3569_, v_snd_3570_);
v___x_3582_ = lean_uint32_dec_eq(v_c_3581_, v___x_3580_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; 
v___x_3583_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1));
lean_inc(v_snd_3570_);
v_pos_3572_ = v_a_3568_;
v_snd_3573_ = v_snd_3570_;
v_err_3574_ = v___x_3583_;
goto v___jp_3571_;
}
else
{
lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3593_; 
lean_inc(v_fst_3569_);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_a_3568_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; lean_object* v_unused_3595_; 
v_unused_3594_ = lean_ctor_get(v_a_3568_, 1);
lean_dec(v_unused_3594_);
v_unused_3595_ = lean_ctor_get(v_a_3568_, 0);
lean_dec(v_unused_3595_);
v___x_3585_ = v_a_3568_;
v_isShared_3586_ = v_isSharedCheck_3593_;
goto v_resetjp_3584_;
}
else
{
lean_dec(v_a_3568_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3593_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; lean_object* v_it_x27_3589_; 
v___x_3587_ = lean_string_utf8_next_fast(v_fst_3569_, v_snd_3570_);
lean_dec(v_snd_3570_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 1, v___x_3587_);
v_it_x27_3589_ = v___x_3585_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_fst_3569_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v___x_3587_);
v_it_x27_3589_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_string_push(v_acc_3567_, v___x_3580_);
v_acc_3567_ = v___x_3590_;
v_a_3568_ = v_it_x27_3589_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3596_; 
v___x_3596_ = lean_box(0);
lean_inc(v_snd_3570_);
v_pos_3572_ = v_a_3568_;
v_snd_3573_ = v_snd_3570_;
v_err_3574_ = v___x_3596_;
goto v___jp_3571_;
}
v___jp_3571_:
{
uint8_t v_decide_3575_; 
v_decide_3575_ = lean_nat_dec_eq(v_snd_3570_, v_snd_3573_);
lean_dec(v_snd_3573_);
lean_dec(v_snd_3570_);
if (v_decide_3575_ == 0)
{
lean_object* v___x_3576_; 
lean_dec_ref(v_acc_3567_);
lean_inc(v_err_3574_);
v___x_3576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3576_, 0, v_pos_3572_);
lean_ctor_set(v___x_3576_, 1, v_err_3574_);
return v___x_3576_;
}
else
{
lean_object* v___x_3577_; 
v___x_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3577_, 0, v_pos_3572_);
lean_ctor_set(v___x_3577_, 1, v_acc_3567_);
return v___x_3577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(lean_object* v_acc_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v_fst_3602_; lean_object* v_snd_3603_; lean_object* v_pos_3605_; lean_object* v_snd_3606_; lean_object* v_err_3607_; lean_object* v___x_3611_; uint8_t v_decide_3612_; 
v_fst_3602_ = lean_ctor_get(v_a_3601_, 0);
v_snd_3603_ = lean_ctor_get(v_a_3601_, 1);
lean_inc(v_snd_3603_);
v___x_3611_ = lean_string_utf8_byte_size(v_fst_3602_);
v_decide_3612_ = lean_nat_dec_eq(v_snd_3603_, v___x_3611_);
if (v_decide_3612_ == 0)
{
uint32_t v___x_3613_; uint32_t v_c_3614_; uint8_t v___x_3615_; 
v___x_3613_ = 100;
v_c_3614_ = lean_string_utf8_get_fast(v_fst_3602_, v_snd_3603_);
v___x_3615_ = lean_uint32_dec_eq(v_c_3614_, v___x_3613_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; 
v___x_3616_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1));
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
uint8_t v_decide_3608_; 
v_decide_3608_ = lean_nat_dec_eq(v_snd_3603_, v_snd_3606_);
lean_dec(v_snd_3606_);
lean_dec(v_snd_3603_);
if (v_decide_3608_ == 0)
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(lean_object* v_acc_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v_fst_3635_; lean_object* v_snd_3636_; lean_object* v_pos_3638_; lean_object* v_snd_3639_; lean_object* v_err_3640_; lean_object* v___x_3644_; uint8_t v_decide_3645_; 
v_fst_3635_ = lean_ctor_get(v_a_3634_, 0);
v_snd_3636_ = lean_ctor_get(v_a_3634_, 1);
lean_inc(v_snd_3636_);
v___x_3644_ = lean_string_utf8_byte_size(v_fst_3635_);
v_decide_3645_ = lean_nat_dec_eq(v_snd_3636_, v___x_3644_);
if (v_decide_3645_ == 0)
{
uint32_t v___x_3646_; uint32_t v_c_3647_; uint8_t v___x_3648_; 
v___x_3646_ = 99;
v_c_3647_ = lean_string_utf8_get_fast(v_fst_3635_, v_snd_3636_);
v___x_3648_ = lean_uint32_dec_eq(v_c_3647_, v___x_3646_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; 
v___x_3649_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1));
lean_inc(v_snd_3636_);
v_pos_3638_ = v_a_3634_;
v_snd_3639_ = v_snd_3636_;
v_err_3640_ = v___x_3649_;
goto v___jp_3637_;
}
else
{
lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3659_; 
lean_inc(v_fst_3635_);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_a_3634_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; lean_object* v_unused_3661_; 
v_unused_3660_ = lean_ctor_get(v_a_3634_, 1);
lean_dec(v_unused_3660_);
v_unused_3661_ = lean_ctor_get(v_a_3634_, 0);
lean_dec(v_unused_3661_);
v___x_3651_ = v_a_3634_;
v_isShared_3652_ = v_isSharedCheck_3659_;
goto v_resetjp_3650_;
}
else
{
lean_dec(v_a_3634_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3659_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3653_; lean_object* v_it_x27_3655_; 
v___x_3653_ = lean_string_utf8_next_fast(v_fst_3635_, v_snd_3636_);
lean_dec(v_snd_3636_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 1, v___x_3653_);
v_it_x27_3655_ = v___x_3651_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_fst_3635_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v___x_3653_);
v_it_x27_3655_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_string_push(v_acc_3633_, v___x_3646_);
v_acc_3633_ = v___x_3656_;
v_a_3634_ = v_it_x27_3655_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_box(0);
lean_inc(v_snd_3636_);
v_pos_3638_ = v_a_3634_;
v_snd_3639_ = v_snd_3636_;
v_err_3640_ = v___x_3662_;
goto v___jp_3637_;
}
v___jp_3637_:
{
uint8_t v_decide_3641_; 
v_decide_3641_ = lean_nat_dec_eq(v_snd_3636_, v_snd_3639_);
lean_dec(v_snd_3639_);
lean_dec(v_snd_3636_);
if (v_decide_3641_ == 0)
{
lean_object* v___x_3642_; 
lean_dec_ref(v_acc_3633_);
lean_inc(v_err_3640_);
v___x_3642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3642_, 0, v_pos_3638_);
lean_ctor_set(v___x_3642_, 1, v_err_3640_);
return v___x_3642_;
}
else
{
lean_object* v___x_3643_; 
v___x_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3643_, 0, v_pos_3638_);
lean_ctor_set(v___x_3643_, 1, v_acc_3633_);
return v___x_3643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(lean_object* v_acc_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v_fst_3668_; lean_object* v_snd_3669_; lean_object* v_pos_3671_; lean_object* v_snd_3672_; lean_object* v_err_3673_; lean_object* v___x_3677_; uint8_t v_decide_3678_; 
v_fst_3668_ = lean_ctor_get(v_a_3667_, 0);
v_snd_3669_ = lean_ctor_get(v_a_3667_, 1);
lean_inc(v_snd_3669_);
v___x_3677_ = lean_string_utf8_byte_size(v_fst_3668_);
v_decide_3678_ = lean_nat_dec_eq(v_snd_3669_, v___x_3677_);
if (v_decide_3678_ == 0)
{
uint32_t v___x_3679_; uint32_t v_c_3680_; uint8_t v___x_3681_; 
v___x_3679_ = 69;
v_c_3680_ = lean_string_utf8_get_fast(v_fst_3668_, v_snd_3669_);
v___x_3681_ = lean_uint32_dec_eq(v_c_3680_, v___x_3679_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; 
v___x_3682_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1));
lean_inc(v_snd_3669_);
v_pos_3671_ = v_a_3667_;
v_snd_3672_ = v_snd_3669_;
v_err_3673_ = v___x_3682_;
goto v___jp_3670_;
}
else
{
lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3692_; 
lean_inc(v_fst_3668_);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_a_3667_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; lean_object* v_unused_3694_; 
v_unused_3693_ = lean_ctor_get(v_a_3667_, 1);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_a_3667_, 0);
lean_dec(v_unused_3694_);
v___x_3684_ = v_a_3667_;
v_isShared_3685_ = v_isSharedCheck_3692_;
goto v_resetjp_3683_;
}
else
{
lean_dec(v_a_3667_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3692_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v_it_x27_3688_; 
v___x_3686_ = lean_string_utf8_next_fast(v_fst_3668_, v_snd_3669_);
lean_dec(v_snd_3669_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 1, v___x_3686_);
v_it_x27_3688_ = v___x_3684_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_fst_3668_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v___x_3686_);
v_it_x27_3688_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; 
v___x_3689_ = lean_string_push(v_acc_3666_, v___x_3679_);
v_acc_3666_ = v___x_3689_;
v_a_3667_ = v_it_x27_3688_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3695_; 
v___x_3695_ = lean_box(0);
lean_inc(v_snd_3669_);
v_pos_3671_ = v_a_3667_;
v_snd_3672_ = v_snd_3669_;
v_err_3673_ = v___x_3695_;
goto v___jp_3670_;
}
v___jp_3670_:
{
uint8_t v_decide_3674_; 
v_decide_3674_ = lean_nat_dec_eq(v_snd_3669_, v_snd_3672_);
lean_dec(v_snd_3672_);
lean_dec(v_snd_3669_);
if (v_decide_3674_ == 0)
{
lean_object* v___x_3675_; 
lean_dec_ref(v_acc_3666_);
lean_inc(v_err_3673_);
v___x_3675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3675_, 0, v_pos_3671_);
lean_ctor_set(v___x_3675_, 1, v_err_3673_);
return v___x_3675_;
}
else
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3676_, 0, v_pos_3671_);
lean_ctor_set(v___x_3676_, 1, v_acc_3666_);
return v___x_3676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(lean_object* v_acc_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v_fst_3701_; lean_object* v_snd_3702_; lean_object* v_pos_3704_; lean_object* v_snd_3705_; lean_object* v_err_3706_; lean_object* v___x_3710_; uint8_t v_decide_3711_; 
v_fst_3701_ = lean_ctor_get(v_a_3700_, 0);
v_snd_3702_ = lean_ctor_get(v_a_3700_, 1);
lean_inc(v_snd_3702_);
v___x_3710_ = lean_string_utf8_byte_size(v_fst_3701_);
v_decide_3711_ = lean_nat_dec_eq(v_snd_3702_, v___x_3710_);
if (v_decide_3711_ == 0)
{
uint32_t v___x_3712_; uint32_t v_c_3713_; uint8_t v___x_3714_; 
v___x_3712_ = 97;
v_c_3713_ = lean_string_utf8_get_fast(v_fst_3701_, v_snd_3702_);
v___x_3714_ = lean_uint32_dec_eq(v_c_3713_, v___x_3712_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; 
v___x_3715_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1));
lean_inc(v_snd_3702_);
v_pos_3704_ = v_a_3700_;
v_snd_3705_ = v_snd_3702_;
v_err_3706_ = v___x_3715_;
goto v___jp_3703_;
}
else
{
lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3725_; 
lean_inc(v_fst_3701_);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_a_3700_);
if (v_isSharedCheck_3725_ == 0)
{
lean_object* v_unused_3726_; lean_object* v_unused_3727_; 
v_unused_3726_ = lean_ctor_get(v_a_3700_, 1);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_a_3700_, 0);
lean_dec(v_unused_3727_);
v___x_3717_ = v_a_3700_;
v_isShared_3718_ = v_isSharedCheck_3725_;
goto v_resetjp_3716_;
}
else
{
lean_dec(v_a_3700_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3725_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3719_; lean_object* v_it_x27_3721_; 
v___x_3719_ = lean_string_utf8_next_fast(v_fst_3701_, v_snd_3702_);
lean_dec(v_snd_3702_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 1, v___x_3719_);
v_it_x27_3721_ = v___x_3717_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_fst_3701_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v___x_3719_);
v_it_x27_3721_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_string_push(v_acc_3699_, v___x_3712_);
v_acc_3699_ = v___x_3722_;
v_a_3700_ = v_it_x27_3721_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_box(0);
lean_inc(v_snd_3702_);
v_pos_3704_ = v_a_3700_;
v_snd_3705_ = v_snd_3702_;
v_err_3706_ = v___x_3728_;
goto v___jp_3703_;
}
v___jp_3703_:
{
uint8_t v_decide_3707_; 
v_decide_3707_ = lean_nat_dec_eq(v_snd_3702_, v_snd_3705_);
lean_dec(v_snd_3705_);
lean_dec(v_snd_3702_);
if (v_decide_3707_ == 0)
{
lean_object* v___x_3708_; 
lean_dec_ref(v_acc_3699_);
lean_inc(v_err_3706_);
v___x_3708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3708_, 0, v_pos_3704_);
lean_ctor_set(v___x_3708_, 1, v_err_3706_);
return v___x_3708_;
}
else
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3709_, 0, v_pos_3704_);
lean_ctor_set(v___x_3709_, 1, v_acc_3699_);
return v___x_3709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(lean_object* v_acc_3732_, lean_object* v_a_3733_){
_start:
{
lean_object* v_fst_3734_; lean_object* v_snd_3735_; lean_object* v_pos_3737_; lean_object* v_snd_3738_; lean_object* v_err_3739_; lean_object* v___x_3743_; uint8_t v_decide_3744_; 
v_fst_3734_ = lean_ctor_get(v_a_3733_, 0);
v_snd_3735_ = lean_ctor_get(v_a_3733_, 1);
lean_inc(v_snd_3735_);
v___x_3743_ = lean_string_utf8_byte_size(v_fst_3734_);
v_decide_3744_ = lean_nat_dec_eq(v_snd_3735_, v___x_3743_);
if (v_decide_3744_ == 0)
{
uint32_t v___x_3745_; uint32_t v_c_3746_; uint8_t v___x_3747_; 
v___x_3745_ = 79;
v_c_3746_ = lean_string_utf8_get_fast(v_fst_3734_, v_snd_3735_);
v___x_3747_ = lean_uint32_dec_eq(v_c_3746_, v___x_3745_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; 
v___x_3748_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1));
lean_inc(v_snd_3735_);
v_pos_3737_ = v_a_3733_;
v_snd_3738_ = v_snd_3735_;
v_err_3739_ = v___x_3748_;
goto v___jp_3736_;
}
else
{
lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3758_; 
lean_inc(v_fst_3734_);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_a_3733_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; lean_object* v_unused_3760_; 
v_unused_3759_ = lean_ctor_get(v_a_3733_, 1);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_a_3733_, 0);
lean_dec(v_unused_3760_);
v___x_3750_ = v_a_3733_;
v_isShared_3751_ = v_isSharedCheck_3758_;
goto v_resetjp_3749_;
}
else
{
lean_dec(v_a_3733_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3758_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; lean_object* v_it_x27_3754_; 
v___x_3752_ = lean_string_utf8_next_fast(v_fst_3734_, v_snd_3735_);
lean_dec(v_snd_3735_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v___x_3752_);
v_it_x27_3754_ = v___x_3750_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_fst_3734_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v___x_3752_);
v_it_x27_3754_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_string_push(v_acc_3732_, v___x_3745_);
v_acc_3732_ = v___x_3755_;
v_a_3733_ = v_it_x27_3754_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3761_; 
v___x_3761_ = lean_box(0);
lean_inc(v_snd_3735_);
v_pos_3737_ = v_a_3733_;
v_snd_3738_ = v_snd_3735_;
v_err_3739_ = v___x_3761_;
goto v___jp_3736_;
}
v___jp_3736_:
{
uint8_t v_decide_3740_; 
v_decide_3740_ = lean_nat_dec_eq(v_snd_3735_, v_snd_3738_);
lean_dec(v_snd_3738_);
lean_dec(v_snd_3735_);
if (v_decide_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec_ref(v_acc_3732_);
lean_inc(v_err_3739_);
v___x_3741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3741_, 0, v_pos_3737_);
lean_ctor_set(v___x_3741_, 1, v_err_3739_);
return v___x_3741_;
}
else
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3742_, 0, v_pos_3737_);
lean_ctor_set(v___x_3742_, 1, v_acc_3732_);
return v___x_3742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(lean_object* v_acc_3765_, lean_object* v_a_3766_){
_start:
{
lean_object* v_fst_3767_; lean_object* v_snd_3768_; lean_object* v_pos_3770_; lean_object* v_snd_3771_; lean_object* v_err_3772_; lean_object* v___x_3776_; uint8_t v_decide_3777_; 
v_fst_3767_ = lean_ctor_get(v_a_3766_, 0);
v_snd_3768_ = lean_ctor_get(v_a_3766_, 1);
lean_inc(v_snd_3768_);
v___x_3776_ = lean_string_utf8_byte_size(v_fst_3767_);
v_decide_3777_ = lean_nat_dec_eq(v_snd_3768_, v___x_3776_);
if (v_decide_3777_ == 0)
{
uint32_t v___x_3778_; uint32_t v_c_3779_; uint8_t v___x_3780_; 
v___x_3778_ = 65;
v_c_3779_ = lean_string_utf8_get_fast(v_fst_3767_, v_snd_3768_);
v___x_3780_ = lean_uint32_dec_eq(v_c_3779_, v___x_3778_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; 
v___x_3781_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1));
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
uint8_t v_decide_3773_; 
v_decide_3773_ = lean_nat_dec_eq(v_snd_3768_, v_snd_3771_);
lean_dec(v_snd_3771_);
lean_dec(v_snd_3768_);
if (v_decide_3773_ == 0)
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(lean_object* v_acc_3798_, lean_object* v_a_3799_){
_start:
{
lean_object* v_fst_3800_; lean_object* v_snd_3801_; lean_object* v_pos_3803_; lean_object* v_snd_3804_; lean_object* v_err_3805_; lean_object* v___x_3809_; uint8_t v_decide_3810_; 
v_fst_3800_ = lean_ctor_get(v_a_3799_, 0);
v_snd_3801_ = lean_ctor_get(v_a_3799_, 1);
lean_inc(v_snd_3801_);
v___x_3809_ = lean_string_utf8_byte_size(v_fst_3800_);
v_decide_3810_ = lean_nat_dec_eq(v_snd_3801_, v___x_3809_);
if (v_decide_3810_ == 0)
{
uint32_t v___x_3811_; uint32_t v_c_3812_; uint8_t v___x_3813_; 
v___x_3811_ = 76;
v_c_3812_ = lean_string_utf8_get_fast(v_fst_3800_, v_snd_3801_);
v___x_3813_ = lean_uint32_dec_eq(v_c_3812_, v___x_3811_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; 
v___x_3814_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1));
lean_inc(v_snd_3801_);
v_pos_3803_ = v_a_3799_;
v_snd_3804_ = v_snd_3801_;
v_err_3805_ = v___x_3814_;
goto v___jp_3802_;
}
else
{
lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3824_; 
lean_inc(v_fst_3800_);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_a_3799_);
if (v_isSharedCheck_3824_ == 0)
{
lean_object* v_unused_3825_; lean_object* v_unused_3826_; 
v_unused_3825_ = lean_ctor_get(v_a_3799_, 1);
lean_dec(v_unused_3825_);
v_unused_3826_ = lean_ctor_get(v_a_3799_, 0);
lean_dec(v_unused_3826_);
v___x_3816_ = v_a_3799_;
v_isShared_3817_ = v_isSharedCheck_3824_;
goto v_resetjp_3815_;
}
else
{
lean_dec(v_a_3799_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3824_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3818_; lean_object* v_it_x27_3820_; 
v___x_3818_ = lean_string_utf8_next_fast(v_fst_3800_, v_snd_3801_);
lean_dec(v_snd_3801_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 1, v___x_3818_);
v_it_x27_3820_ = v___x_3816_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_fst_3800_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v___x_3818_);
v_it_x27_3820_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_string_push(v_acc_3798_, v___x_3811_);
v_acc_3798_ = v___x_3821_;
v_a_3799_ = v_it_x27_3820_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_box(0);
lean_inc(v_snd_3801_);
v_pos_3803_ = v_a_3799_;
v_snd_3804_ = v_snd_3801_;
v_err_3805_ = v___x_3827_;
goto v___jp_3802_;
}
v___jp_3802_:
{
uint8_t v_decide_3806_; 
v_decide_3806_ = lean_nat_dec_eq(v_snd_3801_, v_snd_3804_);
lean_dec(v_snd_3804_);
lean_dec(v_snd_3801_);
if (v_decide_3806_ == 0)
{
lean_object* v___x_3807_; 
lean_dec_ref(v_acc_3798_);
lean_inc(v_err_3805_);
v___x_3807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3807_, 0, v_pos_3803_);
lean_ctor_set(v___x_3807_, 1, v_err_3805_);
return v___x_3807_;
}
else
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v_pos_3803_);
lean_ctor_set(v___x_3808_, 1, v_acc_3798_);
return v___x_3808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(lean_object* v_acc_3831_, lean_object* v_a_3832_){
_start:
{
lean_object* v_fst_3833_; lean_object* v_snd_3834_; lean_object* v_pos_3836_; lean_object* v_snd_3837_; lean_object* v_err_3838_; lean_object* v___x_3842_; uint8_t v_decide_3843_; 
v_fst_3833_ = lean_ctor_get(v_a_3832_, 0);
v_snd_3834_ = lean_ctor_get(v_a_3832_, 1);
lean_inc(v_snd_3834_);
v___x_3842_ = lean_string_utf8_byte_size(v_fst_3833_);
v_decide_3843_ = lean_nat_dec_eq(v_snd_3834_, v___x_3842_);
if (v_decide_3843_ == 0)
{
uint32_t v___x_3844_; uint32_t v_c_3845_; uint8_t v___x_3846_; 
v___x_3844_ = 113;
v_c_3845_ = lean_string_utf8_get_fast(v_fst_3833_, v_snd_3834_);
v___x_3846_ = lean_uint32_dec_eq(v_c_3845_, v___x_3844_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
v___x_3847_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1));
lean_inc(v_snd_3834_);
v_pos_3836_ = v_a_3832_;
v_snd_3837_ = v_snd_3834_;
v_err_3838_ = v___x_3847_;
goto v___jp_3835_;
}
else
{
lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3857_; 
lean_inc(v_fst_3833_);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_a_3832_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; lean_object* v_unused_3859_; 
v_unused_3858_ = lean_ctor_get(v_a_3832_, 1);
lean_dec(v_unused_3858_);
v_unused_3859_ = lean_ctor_get(v_a_3832_, 0);
lean_dec(v_unused_3859_);
v___x_3849_ = v_a_3832_;
v_isShared_3850_ = v_isSharedCheck_3857_;
goto v_resetjp_3848_;
}
else
{
lean_dec(v_a_3832_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3857_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v_it_x27_3853_; 
v___x_3851_ = lean_string_utf8_next_fast(v_fst_3833_, v_snd_3834_);
lean_dec(v_snd_3834_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 1, v___x_3851_);
v_it_x27_3853_ = v___x_3849_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_fst_3833_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v___x_3851_);
v_it_x27_3853_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3854_; 
v___x_3854_ = lean_string_push(v_acc_3831_, v___x_3844_);
v_acc_3831_ = v___x_3854_;
v_a_3832_ = v_it_x27_3853_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3860_; 
v___x_3860_ = lean_box(0);
lean_inc(v_snd_3834_);
v_pos_3836_ = v_a_3832_;
v_snd_3837_ = v_snd_3834_;
v_err_3838_ = v___x_3860_;
goto v___jp_3835_;
}
v___jp_3835_:
{
uint8_t v_decide_3839_; 
v_decide_3839_ = lean_nat_dec_eq(v_snd_3834_, v_snd_3837_);
lean_dec(v_snd_3837_);
lean_dec(v_snd_3834_);
if (v_decide_3839_ == 0)
{
lean_object* v___x_3840_; 
lean_dec_ref(v_acc_3831_);
lean_inc(v_err_3838_);
v___x_3840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3840_, 0, v_pos_3836_);
lean_ctor_set(v___x_3840_, 1, v_err_3838_);
return v___x_3840_;
}
else
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3841_, 0, v_pos_3836_);
lean_ctor_set(v___x_3841_, 1, v_acc_3831_);
return v___x_3841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(lean_object* v_acc_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_fst_3866_; lean_object* v_snd_3867_; lean_object* v_pos_3869_; lean_object* v_snd_3870_; lean_object* v_err_3871_; lean_object* v___x_3875_; uint8_t v_decide_3876_; 
v_fst_3866_ = lean_ctor_get(v_a_3865_, 0);
v_snd_3867_ = lean_ctor_get(v_a_3865_, 1);
lean_inc(v_snd_3867_);
v___x_3875_ = lean_string_utf8_byte_size(v_fst_3866_);
v_decide_3876_ = lean_nat_dec_eq(v_snd_3867_, v___x_3875_);
if (v_decide_3876_ == 0)
{
uint32_t v___x_3877_; uint32_t v_c_3878_; uint8_t v___x_3879_; 
v___x_3877_ = 72;
v_c_3878_ = lean_string_utf8_get_fast(v_fst_3866_, v_snd_3867_);
v___x_3879_ = lean_uint32_dec_eq(v_c_3878_, v___x_3877_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; 
v___x_3880_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1));
lean_inc(v_snd_3867_);
v_pos_3869_ = v_a_3865_;
v_snd_3870_ = v_snd_3867_;
v_err_3871_ = v___x_3880_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3890_; 
lean_inc(v_fst_3866_);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_a_3865_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; lean_object* v_unused_3892_; 
v_unused_3891_ = lean_ctor_get(v_a_3865_, 1);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_a_3865_, 0);
lean_dec(v_unused_3892_);
v___x_3882_ = v_a_3865_;
v_isShared_3883_ = v_isSharedCheck_3890_;
goto v_resetjp_3881_;
}
else
{
lean_dec(v_a_3865_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3890_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v_it_x27_3886_; 
v___x_3884_ = lean_string_utf8_next_fast(v_fst_3866_, v_snd_3867_);
lean_dec(v_snd_3867_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v___x_3884_);
v_it_x27_3886_ = v___x_3882_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_fst_3866_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v___x_3884_);
v_it_x27_3886_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3887_; 
v___x_3887_ = lean_string_push(v_acc_3864_, v___x_3877_);
v_acc_3864_ = v___x_3887_;
v_a_3865_ = v_it_x27_3886_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3893_; 
v___x_3893_ = lean_box(0);
lean_inc(v_snd_3867_);
v_pos_3869_ = v_a_3865_;
v_snd_3870_ = v_snd_3867_;
v_err_3871_ = v___x_3893_;
goto v___jp_3868_;
}
v___jp_3868_:
{
uint8_t v_decide_3872_; 
v_decide_3872_ = lean_nat_dec_eq(v_snd_3867_, v_snd_3870_);
lean_dec(v_snd_3870_);
lean_dec(v_snd_3867_);
if (v_decide_3872_ == 0)
{
lean_object* v___x_3873_; 
lean_dec_ref(v_acc_3864_);
lean_inc(v_err_3871_);
v___x_3873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3873_, 0, v_pos_3869_);
lean_ctor_set(v___x_3873_, 1, v_err_3871_);
return v___x_3873_;
}
else
{
lean_object* v___x_3874_; 
v___x_3874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3874_, 0, v_pos_3869_);
lean_ctor_set(v___x_3874_, 1, v_acc_3864_);
return v___x_3874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(lean_object* v_acc_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_fst_3899_; lean_object* v_snd_3900_; lean_object* v_pos_3902_; lean_object* v_snd_3903_; lean_object* v_err_3904_; lean_object* v___x_3908_; uint8_t v_decide_3909_; 
v_fst_3899_ = lean_ctor_get(v_a_3898_, 0);
v_snd_3900_ = lean_ctor_get(v_a_3898_, 1);
lean_inc(v_snd_3900_);
v___x_3908_ = lean_string_utf8_byte_size(v_fst_3899_);
v_decide_3909_ = lean_nat_dec_eq(v_snd_3900_, v___x_3908_);
if (v_decide_3909_ == 0)
{
uint32_t v___x_3910_; uint32_t v_c_3911_; uint8_t v___x_3912_; 
v___x_3910_ = 118;
v_c_3911_ = lean_string_utf8_get_fast(v_fst_3899_, v_snd_3900_);
v___x_3912_ = lean_uint32_dec_eq(v_c_3911_, v___x_3910_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; 
v___x_3913_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1));
lean_inc(v_snd_3900_);
v_pos_3902_ = v_a_3898_;
v_snd_3903_ = v_snd_3900_;
v_err_3904_ = v___x_3913_;
goto v___jp_3901_;
}
else
{
lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3923_; 
lean_inc(v_fst_3899_);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_a_3898_);
if (v_isSharedCheck_3923_ == 0)
{
lean_object* v_unused_3924_; lean_object* v_unused_3925_; 
v_unused_3924_ = lean_ctor_get(v_a_3898_, 1);
lean_dec(v_unused_3924_);
v_unused_3925_ = lean_ctor_get(v_a_3898_, 0);
lean_dec(v_unused_3925_);
v___x_3915_ = v_a_3898_;
v_isShared_3916_ = v_isSharedCheck_3923_;
goto v_resetjp_3914_;
}
else
{
lean_dec(v_a_3898_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3923_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3917_; lean_object* v_it_x27_3919_; 
v___x_3917_ = lean_string_utf8_next_fast(v_fst_3899_, v_snd_3900_);
lean_dec(v_snd_3900_);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 1, v___x_3917_);
v_it_x27_3919_ = v___x_3915_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_fst_3899_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v___x_3917_);
v_it_x27_3919_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3920_; 
v___x_3920_ = lean_string_push(v_acc_3897_, v___x_3910_);
v_acc_3897_ = v___x_3920_;
v_a_3898_ = v_it_x27_3919_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3926_; 
v___x_3926_ = lean_box(0);
lean_inc(v_snd_3900_);
v_pos_3902_ = v_a_3898_;
v_snd_3903_ = v_snd_3900_;
v_err_3904_ = v___x_3926_;
goto v___jp_3901_;
}
v___jp_3901_:
{
uint8_t v_decide_3905_; 
v_decide_3905_ = lean_nat_dec_eq(v_snd_3900_, v_snd_3903_);
lean_dec(v_snd_3903_);
lean_dec(v_snd_3900_);
if (v_decide_3905_ == 0)
{
lean_object* v___x_3906_; 
lean_dec_ref(v_acc_3897_);
lean_inc(v_err_3904_);
v___x_3906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3906_, 0, v_pos_3902_);
lean_ctor_set(v___x_3906_, 1, v_err_3904_);
return v___x_3906_;
}
else
{
lean_object* v___x_3907_; 
v___x_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3907_, 0, v_pos_3902_);
lean_ctor_set(v___x_3907_, 1, v_acc_3897_);
return v___x_3907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(lean_object* v_acc_3930_, lean_object* v_a_3931_){
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
v___x_3943_ = 87;
v_c_3944_ = lean_string_utf8_get_fast(v_fst_3932_, v_snd_3933_);
v___x_3945_ = lean_uint32_dec_eq(v_c_3944_, v___x_3943_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3946_; 
v___x_3946_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1));
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(lean_object* v_acc_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_fst_3965_; lean_object* v_snd_3966_; lean_object* v_pos_3968_; lean_object* v_snd_3969_; lean_object* v_err_3970_; lean_object* v___x_3974_; uint8_t v_decide_3975_; 
v_fst_3965_ = lean_ctor_get(v_a_3964_, 0);
v_snd_3966_ = lean_ctor_get(v_a_3964_, 1);
lean_inc(v_snd_3966_);
v___x_3974_ = lean_string_utf8_byte_size(v_fst_3965_);
v_decide_3975_ = lean_nat_dec_eq(v_snd_3966_, v___x_3974_);
if (v_decide_3975_ == 0)
{
uint32_t v___x_3976_; uint32_t v_c_3977_; uint8_t v___x_3978_; 
v___x_3976_ = 107;
v_c_3977_ = lean_string_utf8_get_fast(v_fst_3965_, v_snd_3966_);
v___x_3978_ = lean_uint32_dec_eq(v_c_3977_, v___x_3976_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; 
v___x_3979_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1));
lean_inc(v_snd_3966_);
v_pos_3968_ = v_a_3964_;
v_snd_3969_ = v_snd_3966_;
v_err_3970_ = v___x_3979_;
goto v___jp_3967_;
}
else
{
lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3989_; 
lean_inc(v_fst_3965_);
v_isSharedCheck_3989_ = !lean_is_exclusive(v_a_3964_);
if (v_isSharedCheck_3989_ == 0)
{
lean_object* v_unused_3990_; lean_object* v_unused_3991_; 
v_unused_3990_ = lean_ctor_get(v_a_3964_, 1);
lean_dec(v_unused_3990_);
v_unused_3991_ = lean_ctor_get(v_a_3964_, 0);
lean_dec(v_unused_3991_);
v___x_3981_ = v_a_3964_;
v_isShared_3982_ = v_isSharedCheck_3989_;
goto v_resetjp_3980_;
}
else
{
lean_dec(v_a_3964_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3989_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3983_; lean_object* v_it_x27_3985_; 
v___x_3983_ = lean_string_utf8_next_fast(v_fst_3965_, v_snd_3966_);
lean_dec(v_snd_3966_);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 1, v___x_3983_);
v_it_x27_3985_ = v___x_3981_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_fst_3965_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v___x_3983_);
v_it_x27_3985_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3986_; 
v___x_3986_ = lean_string_push(v_acc_3963_, v___x_3976_);
v_acc_3963_ = v___x_3986_;
v_a_3964_ = v_it_x27_3985_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_box(0);
lean_inc(v_snd_3966_);
v_pos_3968_ = v_a_3964_;
v_snd_3969_ = v_snd_3966_;
v_err_3970_ = v___x_3992_;
goto v___jp_3967_;
}
v___jp_3967_:
{
uint8_t v_decide_3971_; 
v_decide_3971_ = lean_nat_dec_eq(v_snd_3966_, v_snd_3969_);
lean_dec(v_snd_3969_);
lean_dec(v_snd_3966_);
if (v_decide_3971_ == 0)
{
lean_object* v___x_3972_; 
lean_dec_ref(v_acc_3963_);
lean_inc(v_err_3970_);
v___x_3972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3972_, 0, v_pos_3968_);
lean_ctor_set(v___x_3972_, 1, v_err_3970_);
return v___x_3972_;
}
else
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3973_, 0, v_pos_3968_);
lean_ctor_set(v___x_3973_, 1, v_acc_3963_);
return v___x_3973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(lean_object* v_acc_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_fst_3998_; lean_object* v_snd_3999_; lean_object* v_pos_4001_; lean_object* v_snd_4002_; lean_object* v_err_4003_; lean_object* v___x_4007_; uint8_t v_decide_4008_; 
v_fst_3998_ = lean_ctor_get(v_a_3997_, 0);
v_snd_3999_ = lean_ctor_get(v_a_3997_, 1);
lean_inc(v_snd_3999_);
v___x_4007_ = lean_string_utf8_byte_size(v_fst_3998_);
v_decide_4008_ = lean_nat_dec_eq(v_snd_3999_, v___x_4007_);
if (v_decide_4008_ == 0)
{
uint32_t v___x_4009_; uint32_t v_c_4010_; uint8_t v___x_4011_; 
v___x_4009_ = 121;
v_c_4010_ = lean_string_utf8_get_fast(v_fst_3998_, v_snd_3999_);
v___x_4011_ = lean_uint32_dec_eq(v_c_4010_, v___x_4009_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; 
v___x_4012_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1));
lean_inc(v_snd_3999_);
v_pos_4001_ = v_a_3997_;
v_snd_4002_ = v_snd_3999_;
v_err_4003_ = v___x_4012_;
goto v___jp_4000_;
}
else
{
lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4022_; 
lean_inc(v_fst_3998_);
v_isSharedCheck_4022_ = !lean_is_exclusive(v_a_3997_);
if (v_isSharedCheck_4022_ == 0)
{
lean_object* v_unused_4023_; lean_object* v_unused_4024_; 
v_unused_4023_ = lean_ctor_get(v_a_3997_, 1);
lean_dec(v_unused_4023_);
v_unused_4024_ = lean_ctor_get(v_a_3997_, 0);
lean_dec(v_unused_4024_);
v___x_4014_ = v_a_3997_;
v_isShared_4015_ = v_isSharedCheck_4022_;
goto v_resetjp_4013_;
}
else
{
lean_dec(v_a_3997_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4022_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; lean_object* v_it_x27_4018_; 
v___x_4016_ = lean_string_utf8_next_fast(v_fst_3998_, v_snd_3999_);
lean_dec(v_snd_3999_);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 1, v___x_4016_);
v_it_x27_4018_ = v___x_4014_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_fst_3998_);
lean_ctor_set(v_reuseFailAlloc_4021_, 1, v___x_4016_);
v_it_x27_4018_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_string_push(v_acc_3996_, v___x_4009_);
v_acc_3996_ = v___x_4019_;
v_a_3997_ = v_it_x27_4018_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_box(0);
lean_inc(v_snd_3999_);
v_pos_4001_ = v_a_3997_;
v_snd_4002_ = v_snd_3999_;
v_err_4003_ = v___x_4025_;
goto v___jp_4000_;
}
v___jp_4000_:
{
uint8_t v_decide_4004_; 
v_decide_4004_ = lean_nat_dec_eq(v_snd_3999_, v_snd_4002_);
lean_dec(v_snd_4002_);
lean_dec(v_snd_3999_);
if (v_decide_4004_ == 0)
{
lean_object* v___x_4005_; 
lean_dec_ref(v_acc_3996_);
lean_inc(v_err_4003_);
v___x_4005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4005_, 0, v_pos_4001_);
lean_ctor_set(v___x_4005_, 1, v_err_4003_);
return v___x_4005_;
}
else
{
lean_object* v___x_4006_; 
v___x_4006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4006_, 0, v_pos_4001_);
lean_ctor_set(v___x_4006_, 1, v_acc_3996_);
return v___x_4006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(lean_object* v_acc_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v_fst_4031_; lean_object* v_snd_4032_; lean_object* v_pos_4034_; lean_object* v_snd_4035_; lean_object* v_err_4036_; lean_object* v___x_4040_; uint8_t v_decide_4041_; 
v_fst_4031_ = lean_ctor_get(v_a_4030_, 0);
v_snd_4032_ = lean_ctor_get(v_a_4030_, 1);
lean_inc(v_snd_4032_);
v___x_4040_ = lean_string_utf8_byte_size(v_fst_4031_);
v_decide_4041_ = lean_nat_dec_eq(v_snd_4032_, v___x_4040_);
if (v_decide_4041_ == 0)
{
uint32_t v___x_4042_; uint32_t v_c_4043_; uint8_t v___x_4044_; 
v___x_4042_ = 98;
v_c_4043_ = lean_string_utf8_get_fast(v_fst_4031_, v_snd_4032_);
v___x_4044_ = lean_uint32_dec_eq(v_c_4043_, v___x_4042_);
if (v___x_4044_ == 0)
{
lean_object* v___x_4045_; 
v___x_4045_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1));
lean_inc(v_snd_4032_);
v_pos_4034_ = v_a_4030_;
v_snd_4035_ = v_snd_4032_;
v_err_4036_ = v___x_4045_;
goto v___jp_4033_;
}
else
{
lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4055_; 
lean_inc(v_fst_4031_);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_a_4030_);
if (v_isSharedCheck_4055_ == 0)
{
lean_object* v_unused_4056_; lean_object* v_unused_4057_; 
v_unused_4056_ = lean_ctor_get(v_a_4030_, 1);
lean_dec(v_unused_4056_);
v_unused_4057_ = lean_ctor_get(v_a_4030_, 0);
lean_dec(v_unused_4057_);
v___x_4047_ = v_a_4030_;
v_isShared_4048_ = v_isSharedCheck_4055_;
goto v_resetjp_4046_;
}
else
{
lean_dec(v_a_4030_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4055_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4049_; lean_object* v_it_x27_4051_; 
v___x_4049_ = lean_string_utf8_next_fast(v_fst_4031_, v_snd_4032_);
lean_dec(v_snd_4032_);
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 1, v___x_4049_);
v_it_x27_4051_ = v___x_4047_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_fst_4031_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v___x_4049_);
v_it_x27_4051_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4052_; 
v___x_4052_ = lean_string_push(v_acc_4029_, v___x_4042_);
v_acc_4029_ = v___x_4052_;
v_a_4030_ = v_it_x27_4051_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4058_; 
v___x_4058_ = lean_box(0);
lean_inc(v_snd_4032_);
v_pos_4034_ = v_a_4030_;
v_snd_4035_ = v_snd_4032_;
v_err_4036_ = v___x_4058_;
goto v___jp_4033_;
}
v___jp_4033_:
{
uint8_t v_decide_4037_; 
v_decide_4037_ = lean_nat_dec_eq(v_snd_4032_, v_snd_4035_);
lean_dec(v_snd_4035_);
lean_dec(v_snd_4032_);
if (v_decide_4037_ == 0)
{
lean_object* v___x_4038_; 
lean_dec_ref(v_acc_4029_);
lean_inc(v_err_4036_);
v___x_4038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4038_, 0, v_pos_4034_);
lean_ctor_set(v___x_4038_, 1, v_err_4036_);
return v___x_4038_;
}
else
{
lean_object* v___x_4039_; 
v___x_4039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4039_, 0, v_pos_4034_);
lean_ctor_set(v___x_4039_, 1, v_acc_4029_);
return v___x_4039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(lean_object* v_acc_4062_, lean_object* v_a_4063_){
_start:
{
lean_object* v_fst_4064_; lean_object* v_snd_4065_; lean_object* v_pos_4067_; lean_object* v_snd_4068_; lean_object* v_err_4069_; lean_object* v___x_4073_; uint8_t v_decide_4074_; 
v_fst_4064_ = lean_ctor_get(v_a_4063_, 0);
v_snd_4065_ = lean_ctor_get(v_a_4063_, 1);
lean_inc(v_snd_4065_);
v___x_4073_ = lean_string_utf8_byte_size(v_fst_4064_);
v_decide_4074_ = lean_nat_dec_eq(v_snd_4065_, v___x_4073_);
if (v_decide_4074_ == 0)
{
uint32_t v___x_4075_; uint32_t v_c_4076_; uint8_t v___x_4077_; 
v___x_4075_ = 109;
v_c_4076_ = lean_string_utf8_get_fast(v_fst_4064_, v_snd_4065_);
v___x_4077_ = lean_uint32_dec_eq(v_c_4076_, v___x_4075_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; 
v___x_4078_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1));
lean_inc(v_snd_4065_);
v_pos_4067_ = v_a_4063_;
v_snd_4068_ = v_snd_4065_;
v_err_4069_ = v___x_4078_;
goto v___jp_4066_;
}
else
{
lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4088_; 
lean_inc(v_fst_4064_);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_a_4063_);
if (v_isSharedCheck_4088_ == 0)
{
lean_object* v_unused_4089_; lean_object* v_unused_4090_; 
v_unused_4089_ = lean_ctor_get(v_a_4063_, 1);
lean_dec(v_unused_4089_);
v_unused_4090_ = lean_ctor_get(v_a_4063_, 0);
lean_dec(v_unused_4090_);
v___x_4080_ = v_a_4063_;
v_isShared_4081_ = v_isSharedCheck_4088_;
goto v_resetjp_4079_;
}
else
{
lean_dec(v_a_4063_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4088_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v_it_x27_4084_; 
v___x_4082_ = lean_string_utf8_next_fast(v_fst_4064_, v_snd_4065_);
lean_dec(v_snd_4065_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 1, v___x_4082_);
v_it_x27_4084_ = v___x_4080_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_fst_4064_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v___x_4082_);
v_it_x27_4084_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4085_; 
v___x_4085_ = lean_string_push(v_acc_4062_, v___x_4075_);
v_acc_4062_ = v___x_4085_;
v_a_4063_ = v_it_x27_4084_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4091_; 
v___x_4091_ = lean_box(0);
lean_inc(v_snd_4065_);
v_pos_4067_ = v_a_4063_;
v_snd_4068_ = v_snd_4065_;
v_err_4069_ = v___x_4091_;
goto v___jp_4066_;
}
v___jp_4066_:
{
uint8_t v_decide_4070_; 
v_decide_4070_ = lean_nat_dec_eq(v_snd_4065_, v_snd_4068_);
lean_dec(v_snd_4068_);
lean_dec(v_snd_4065_);
if (v_decide_4070_ == 0)
{
lean_object* v___x_4071_; 
lean_dec_ref(v_acc_4062_);
lean_inc(v_err_4069_);
v___x_4071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4071_, 0, v_pos_4067_);
lean_ctor_set(v___x_4071_, 1, v_err_4069_);
return v___x_4071_;
}
else
{
lean_object* v___x_4072_; 
v___x_4072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4072_, 0, v_pos_4067_);
lean_ctor_set(v___x_4072_, 1, v_acc_4062_);
return v___x_4072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(lean_object* v_acc_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v_fst_4097_; lean_object* v_snd_4098_; lean_object* v_pos_4100_; lean_object* v_snd_4101_; lean_object* v_err_4102_; lean_object* v___x_4106_; uint8_t v_decide_4107_; 
v_fst_4097_ = lean_ctor_get(v_a_4096_, 0);
v_snd_4098_ = lean_ctor_get(v_a_4096_, 1);
lean_inc(v_snd_4098_);
v___x_4106_ = lean_string_utf8_byte_size(v_fst_4097_);
v_decide_4107_ = lean_nat_dec_eq(v_snd_4098_, v___x_4106_);
if (v_decide_4107_ == 0)
{
uint32_t v___x_4108_; uint32_t v_c_4109_; uint8_t v___x_4110_; 
v___x_4108_ = 117;
v_c_4109_ = lean_string_utf8_get_fast(v_fst_4097_, v_snd_4098_);
v___x_4110_ = lean_uint32_dec_eq(v_c_4109_, v___x_4108_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; 
v___x_4111_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1));
lean_inc(v_snd_4098_);
v_pos_4100_ = v_a_4096_;
v_snd_4101_ = v_snd_4098_;
v_err_4102_ = v___x_4111_;
goto v___jp_4099_;
}
else
{
lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4121_; 
lean_inc(v_fst_4097_);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_a_4096_);
if (v_isSharedCheck_4121_ == 0)
{
lean_object* v_unused_4122_; lean_object* v_unused_4123_; 
v_unused_4122_ = lean_ctor_get(v_a_4096_, 1);
lean_dec(v_unused_4122_);
v_unused_4123_ = lean_ctor_get(v_a_4096_, 0);
lean_dec(v_unused_4123_);
v___x_4113_ = v_a_4096_;
v_isShared_4114_ = v_isSharedCheck_4121_;
goto v_resetjp_4112_;
}
else
{
lean_dec(v_a_4096_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4121_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4115_; lean_object* v_it_x27_4117_; 
v___x_4115_ = lean_string_utf8_next_fast(v_fst_4097_, v_snd_4098_);
lean_dec(v_snd_4098_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 1, v___x_4115_);
v_it_x27_4117_ = v___x_4113_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_fst_4097_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4115_);
v_it_x27_4117_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
lean_object* v___x_4118_; 
v___x_4118_ = lean_string_push(v_acc_4095_, v___x_4108_);
v_acc_4095_ = v___x_4118_;
v_a_4096_ = v_it_x27_4117_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4124_; 
v___x_4124_ = lean_box(0);
lean_inc(v_snd_4098_);
v_pos_4100_ = v_a_4096_;
v_snd_4101_ = v_snd_4098_;
v_err_4102_ = v___x_4124_;
goto v___jp_4099_;
}
v___jp_4099_:
{
uint8_t v_decide_4103_; 
v_decide_4103_ = lean_nat_dec_eq(v_snd_4098_, v_snd_4101_);
lean_dec(v_snd_4101_);
lean_dec(v_snd_4098_);
if (v_decide_4103_ == 0)
{
lean_object* v___x_4104_; 
lean_dec_ref(v_acc_4095_);
lean_inc(v_err_4102_);
v___x_4104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4104_, 0, v_pos_4100_);
lean_ctor_set(v___x_4104_, 1, v_err_4102_);
return v___x_4104_;
}
else
{
lean_object* v___x_4105_; 
v___x_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4105_, 0, v_pos_4100_);
lean_ctor_set(v___x_4105_, 1, v_acc_4095_);
return v___x_4105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(lean_object* v_acc_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v_fst_4130_; lean_object* v_snd_4131_; lean_object* v_pos_4133_; lean_object* v_snd_4134_; lean_object* v_err_4135_; lean_object* v___x_4139_; uint8_t v_decide_4140_; 
v_fst_4130_ = lean_ctor_get(v_a_4129_, 0);
v_snd_4131_ = lean_ctor_get(v_a_4129_, 1);
lean_inc(v_snd_4131_);
v___x_4139_ = lean_string_utf8_byte_size(v_fst_4130_);
v_decide_4140_ = lean_nat_dec_eq(v_snd_4131_, v___x_4139_);
if (v_decide_4140_ == 0)
{
uint32_t v___x_4141_; uint32_t v_c_4142_; uint8_t v___x_4143_; 
v___x_4141_ = 90;
v_c_4142_ = lean_string_utf8_get_fast(v_fst_4130_, v_snd_4131_);
v___x_4143_ = lean_uint32_dec_eq(v_c_4142_, v___x_4141_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; 
v___x_4144_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1));
lean_inc(v_snd_4131_);
v_pos_4133_ = v_a_4129_;
v_snd_4134_ = v_snd_4131_;
v_err_4135_ = v___x_4144_;
goto v___jp_4132_;
}
else
{
lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4154_; 
lean_inc(v_fst_4130_);
v_isSharedCheck_4154_ = !lean_is_exclusive(v_a_4129_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; lean_object* v_unused_4156_; 
v_unused_4155_ = lean_ctor_get(v_a_4129_, 1);
lean_dec(v_unused_4155_);
v_unused_4156_ = lean_ctor_get(v_a_4129_, 0);
lean_dec(v_unused_4156_);
v___x_4146_ = v_a_4129_;
v_isShared_4147_ = v_isSharedCheck_4154_;
goto v_resetjp_4145_;
}
else
{
lean_dec(v_a_4129_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4154_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4148_; lean_object* v_it_x27_4150_; 
v___x_4148_ = lean_string_utf8_next_fast(v_fst_4130_, v_snd_4131_);
lean_dec(v_snd_4131_);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 1, v___x_4148_);
v_it_x27_4150_ = v___x_4146_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_fst_4130_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v___x_4148_);
v_it_x27_4150_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
lean_object* v___x_4151_; 
v___x_4151_ = lean_string_push(v_acc_4128_, v___x_4141_);
v_acc_4128_ = v___x_4151_;
v_a_4129_ = v_it_x27_4150_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4157_; 
v___x_4157_ = lean_box(0);
lean_inc(v_snd_4131_);
v_pos_4133_ = v_a_4129_;
v_snd_4134_ = v_snd_4131_;
v_err_4135_ = v___x_4157_;
goto v___jp_4132_;
}
v___jp_4132_:
{
uint8_t v_decide_4136_; 
v_decide_4136_ = lean_nat_dec_eq(v_snd_4131_, v_snd_4134_);
lean_dec(v_snd_4134_);
lean_dec(v_snd_4131_);
if (v_decide_4136_ == 0)
{
lean_object* v___x_4137_; 
lean_dec_ref(v_acc_4128_);
lean_inc(v_err_4135_);
v___x_4137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4137_, 0, v_pos_4133_);
lean_ctor_set(v___x_4137_, 1, v_err_4135_);
return v___x_4137_;
}
else
{
lean_object* v___x_4138_; 
v___x_4138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4138_, 0, v_pos_4133_);
lean_ctor_set(v___x_4138_, 1, v_acc_4128_);
return v___x_4138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(lean_object* v_acc_4161_, lean_object* v_a_4162_){
_start:
{
lean_object* v_fst_4163_; lean_object* v_snd_4164_; lean_object* v_pos_4166_; lean_object* v_snd_4167_; lean_object* v_err_4168_; lean_object* v___x_4172_; uint8_t v_decide_4173_; 
v_fst_4163_ = lean_ctor_get(v_a_4162_, 0);
v_snd_4164_ = lean_ctor_get(v_a_4162_, 1);
lean_inc(v_snd_4164_);
v___x_4172_ = lean_string_utf8_byte_size(v_fst_4163_);
v_decide_4173_ = lean_nat_dec_eq(v_snd_4164_, v___x_4172_);
if (v_decide_4173_ == 0)
{
uint32_t v___x_4174_; uint32_t v_c_4175_; uint8_t v___x_4176_; 
v___x_4174_ = 78;
v_c_4175_ = lean_string_utf8_get_fast(v_fst_4163_, v_snd_4164_);
v___x_4176_ = lean_uint32_dec_eq(v_c_4175_, v___x_4174_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; 
v___x_4177_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1));
lean_inc(v_snd_4164_);
v_pos_4166_ = v_a_4162_;
v_snd_4167_ = v_snd_4164_;
v_err_4168_ = v___x_4177_;
goto v___jp_4165_;
}
else
{
lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4187_; 
lean_inc(v_fst_4163_);
v_isSharedCheck_4187_ = !lean_is_exclusive(v_a_4162_);
if (v_isSharedCheck_4187_ == 0)
{
lean_object* v_unused_4188_; lean_object* v_unused_4189_; 
v_unused_4188_ = lean_ctor_get(v_a_4162_, 1);
lean_dec(v_unused_4188_);
v_unused_4189_ = lean_ctor_get(v_a_4162_, 0);
lean_dec(v_unused_4189_);
v___x_4179_ = v_a_4162_;
v_isShared_4180_ = v_isSharedCheck_4187_;
goto v_resetjp_4178_;
}
else
{
lean_dec(v_a_4162_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4187_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v_it_x27_4183_; 
v___x_4181_ = lean_string_utf8_next_fast(v_fst_4163_, v_snd_4164_);
lean_dec(v_snd_4164_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 1, v___x_4181_);
v_it_x27_4183_ = v___x_4179_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_fst_4163_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v___x_4181_);
v_it_x27_4183_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; 
v___x_4184_ = lean_string_push(v_acc_4161_, v___x_4174_);
v_acc_4161_ = v___x_4184_;
v_a_4162_ = v_it_x27_4183_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4190_; 
v___x_4190_ = lean_box(0);
lean_inc(v_snd_4164_);
v_pos_4166_ = v_a_4162_;
v_snd_4167_ = v_snd_4164_;
v_err_4168_ = v___x_4190_;
goto v___jp_4165_;
}
v___jp_4165_:
{
uint8_t v_decide_4169_; 
v_decide_4169_ = lean_nat_dec_eq(v_snd_4164_, v_snd_4167_);
lean_dec(v_snd_4167_);
lean_dec(v_snd_4164_);
if (v_decide_4169_ == 0)
{
lean_object* v___x_4170_; 
lean_dec_ref(v_acc_4161_);
lean_inc(v_err_4168_);
v___x_4170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4170_, 0, v_pos_4166_);
lean_ctor_set(v___x_4170_, 1, v_err_4168_);
return v___x_4170_;
}
else
{
lean_object* v___x_4171_; 
v___x_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4171_, 0, v_pos_4166_);
lean_ctor_set(v___x_4171_, 1, v_acc_4161_);
return v___x_4171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(lean_object* v_acc_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v_fst_4196_; lean_object* v_snd_4197_; lean_object* v_pos_4199_; lean_object* v_snd_4200_; lean_object* v_err_4201_; lean_object* v___x_4205_; uint8_t v_decide_4206_; 
v_fst_4196_ = lean_ctor_get(v_a_4195_, 0);
v_snd_4197_ = lean_ctor_get(v_a_4195_, 1);
lean_inc(v_snd_4197_);
v___x_4205_ = lean_string_utf8_byte_size(v_fst_4196_);
v_decide_4206_ = lean_nat_dec_eq(v_snd_4197_, v___x_4205_);
if (v_decide_4206_ == 0)
{
uint32_t v___x_4207_; uint32_t v_c_4208_; uint8_t v___x_4209_; 
v___x_4207_ = 70;
v_c_4208_ = lean_string_utf8_get_fast(v_fst_4196_, v_snd_4197_);
v___x_4209_ = lean_uint32_dec_eq(v_c_4208_, v___x_4207_);
if (v___x_4209_ == 0)
{
lean_object* v___x_4210_; 
v___x_4210_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1));
lean_inc(v_snd_4197_);
v_pos_4199_ = v_a_4195_;
v_snd_4200_ = v_snd_4197_;
v_err_4201_ = v___x_4210_;
goto v___jp_4198_;
}
else
{
lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4220_; 
lean_inc(v_fst_4196_);
v_isSharedCheck_4220_ = !lean_is_exclusive(v_a_4195_);
if (v_isSharedCheck_4220_ == 0)
{
lean_object* v_unused_4221_; lean_object* v_unused_4222_; 
v_unused_4221_ = lean_ctor_get(v_a_4195_, 1);
lean_dec(v_unused_4221_);
v_unused_4222_ = lean_ctor_get(v_a_4195_, 0);
lean_dec(v_unused_4222_);
v___x_4212_ = v_a_4195_;
v_isShared_4213_ = v_isSharedCheck_4220_;
goto v_resetjp_4211_;
}
else
{
lean_dec(v_a_4195_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4220_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4214_; lean_object* v_it_x27_4216_; 
v___x_4214_ = lean_string_utf8_next_fast(v_fst_4196_, v_snd_4197_);
lean_dec(v_snd_4197_);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 1, v___x_4214_);
v_it_x27_4216_ = v___x_4212_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_fst_4196_);
lean_ctor_set(v_reuseFailAlloc_4219_, 1, v___x_4214_);
v_it_x27_4216_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
lean_object* v___x_4217_; 
v___x_4217_ = lean_string_push(v_acc_4194_, v___x_4207_);
v_acc_4194_ = v___x_4217_;
v_a_4195_ = v_it_x27_4216_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4223_; 
v___x_4223_ = lean_box(0);
lean_inc(v_snd_4197_);
v_pos_4199_ = v_a_4195_;
v_snd_4200_ = v_snd_4197_;
v_err_4201_ = v___x_4223_;
goto v___jp_4198_;
}
v___jp_4198_:
{
uint8_t v_decide_4202_; 
v_decide_4202_ = lean_nat_dec_eq(v_snd_4197_, v_snd_4200_);
lean_dec(v_snd_4200_);
lean_dec(v_snd_4197_);
if (v_decide_4202_ == 0)
{
lean_object* v___x_4203_; 
lean_dec_ref(v_acc_4194_);
lean_inc(v_err_4201_);
v___x_4203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4203_, 0, v_pos_4199_);
lean_ctor_set(v___x_4203_, 1, v_err_4201_);
return v___x_4203_;
}
else
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_pos_4199_);
lean_ctor_set(v___x_4204_, 1, v_acc_4194_);
return v___x_4204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(lean_object* v_acc_4227_, lean_object* v_a_4228_){
_start:
{
lean_object* v_fst_4229_; lean_object* v_snd_4230_; lean_object* v_pos_4232_; lean_object* v_snd_4233_; lean_object* v_err_4234_; lean_object* v___x_4238_; uint8_t v_decide_4239_; 
v_fst_4229_ = lean_ctor_get(v_a_4228_, 0);
v_snd_4230_ = lean_ctor_get(v_a_4228_, 1);
lean_inc(v_snd_4230_);
v___x_4238_ = lean_string_utf8_byte_size(v_fst_4229_);
v_decide_4239_ = lean_nat_dec_eq(v_snd_4230_, v___x_4238_);
if (v_decide_4239_ == 0)
{
uint32_t v___x_4240_; uint32_t v_c_4241_; uint8_t v___x_4242_; 
v___x_4240_ = 66;
v_c_4241_ = lean_string_utf8_get_fast(v_fst_4229_, v_snd_4230_);
v___x_4242_ = lean_uint32_dec_eq(v_c_4241_, v___x_4240_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; 
v___x_4243_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1));
lean_inc(v_snd_4230_);
v_pos_4232_ = v_a_4228_;
v_snd_4233_ = v_snd_4230_;
v_err_4234_ = v___x_4243_;
goto v___jp_4231_;
}
else
{
lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4253_; 
lean_inc(v_fst_4229_);
v_isSharedCheck_4253_ = !lean_is_exclusive(v_a_4228_);
if (v_isSharedCheck_4253_ == 0)
{
lean_object* v_unused_4254_; lean_object* v_unused_4255_; 
v_unused_4254_ = lean_ctor_get(v_a_4228_, 1);
lean_dec(v_unused_4254_);
v_unused_4255_ = lean_ctor_get(v_a_4228_, 0);
lean_dec(v_unused_4255_);
v___x_4245_ = v_a_4228_;
v_isShared_4246_ = v_isSharedCheck_4253_;
goto v_resetjp_4244_;
}
else
{
lean_dec(v_a_4228_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4253_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4247_; lean_object* v_it_x27_4249_; 
v___x_4247_ = lean_string_utf8_next_fast(v_fst_4229_, v_snd_4230_);
lean_dec(v_snd_4230_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 1, v___x_4247_);
v_it_x27_4249_ = v___x_4245_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_fst_4229_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v___x_4247_);
v_it_x27_4249_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4250_; 
v___x_4250_ = lean_string_push(v_acc_4227_, v___x_4240_);
v_acc_4227_ = v___x_4250_;
v_a_4228_ = v_it_x27_4249_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4256_; 
v___x_4256_ = lean_box(0);
lean_inc(v_snd_4230_);
v_pos_4232_ = v_a_4228_;
v_snd_4233_ = v_snd_4230_;
v_err_4234_ = v___x_4256_;
goto v___jp_4231_;
}
v___jp_4231_:
{
uint8_t v_decide_4235_; 
v_decide_4235_ = lean_nat_dec_eq(v_snd_4230_, v_snd_4233_);
lean_dec(v_snd_4233_);
lean_dec(v_snd_4230_);
if (v_decide_4235_ == 0)
{
lean_object* v___x_4236_; 
lean_dec_ref(v_acc_4227_);
lean_inc(v_err_4234_);
v___x_4236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4236_, 0, v_pos_4232_);
lean_ctor_set(v___x_4236_, 1, v_err_4234_);
return v___x_4236_;
}
else
{
lean_object* v___x_4237_; 
v___x_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4237_, 0, v_pos_4232_);
lean_ctor_set(v___x_4237_, 1, v_acc_4227_);
return v___x_4237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier(lean_object* v_a_4330_){
_start:
{
lean_object* v___y_4332_; lean_object* v_fst_4335_; lean_object* v_snd_4336_; lean_object* v___f_4337_; lean_object* v_snd_4339_; lean_object* v___y_4340_; lean_object* v_pos_4341_; lean_object* v_snd_4377_; lean_object* v_pos_4378_; lean_object* v_err_4379_; lean_object* v___y_4382_; lean_object* v_snd_4383_; lean_object* v___f_4385_; lean_object* v_snd_4387_; lean_object* v___y_4388_; lean_object* v_pos_4389_; lean_object* v_snd_4418_; lean_object* v_pos_4419_; lean_object* v_err_4420_; lean_object* v___y_4423_; lean_object* v_snd_4424_; lean_object* v___f_4426_; lean_object* v_snd_4428_; lean_object* v___y_4429_; lean_object* v_pos_4430_; lean_object* v_snd_4459_; lean_object* v_pos_4460_; lean_object* v_err_4461_; lean_object* v___y_4464_; lean_object* v_snd_4465_; lean_object* v___f_4467_; lean_object* v_snd_4469_; lean_object* v___y_4470_; lean_object* v_pos_4471_; lean_object* v_snd_4500_; lean_object* v_pos_4501_; lean_object* v_err_4502_; lean_object* v___y_4505_; lean_object* v_snd_4506_; lean_object* v___f_4508_; lean_object* v_snd_4510_; lean_object* v___y_4511_; lean_object* v_pos_4512_; lean_object* v_snd_4541_; lean_object* v_pos_4542_; lean_object* v_err_4543_; lean_object* v___y_4546_; lean_object* v_snd_4547_; lean_object* v___f_4549_; lean_object* v_snd_4551_; lean_object* v___y_4552_; lean_object* v_pos_4553_; lean_object* v_snd_4582_; lean_object* v_pos_4583_; lean_object* v_err_4584_; lean_object* v___y_4587_; lean_object* v_snd_4588_; lean_object* v_snd_4591_; lean_object* v___y_4592_; lean_object* v_pos_4593_; lean_object* v_snd_4622_; lean_object* v_pos_4623_; lean_object* v_err_4624_; lean_object* v___y_4627_; lean_object* v_snd_4628_; lean_object* v___f_4630_; lean_object* v_snd_4632_; lean_object* v___y_4633_; lean_object* v_pos_4634_; lean_object* v_snd_4662_; lean_object* v_pos_4663_; lean_object* v_err_4664_; lean_object* v___y_4667_; lean_object* v_snd_4668_; lean_object* v___f_4670_; lean_object* v_snd_4672_; lean_object* v___y_4673_; lean_object* v_pos_4674_; lean_object* v_snd_4702_; lean_object* v_pos_4703_; lean_object* v_err_4704_; lean_object* v___y_4707_; lean_object* v_snd_4708_; lean_object* v___f_4710_; lean_object* v_snd_4712_; lean_object* v___y_4713_; lean_object* v_pos_4714_; lean_object* v_snd_4742_; lean_object* v_pos_4743_; lean_object* v_err_4744_; lean_object* v___y_4747_; lean_object* v_snd_4748_; lean_object* v___f_4750_; lean_object* v_snd_4752_; lean_object* v___y_4753_; lean_object* v_pos_4754_; lean_object* v_snd_4783_; lean_object* v_pos_4784_; lean_object* v_err_4785_; lean_object* v___y_4788_; lean_object* v_snd_4789_; lean_object* v___f_4791_; lean_object* v___y_4793_; lean_object* v_snd_4794_; lean_object* v___y_4795_; lean_object* v_pos_4796_; lean_object* v___y_4825_; lean_object* v_snd_4826_; lean_object* v_pos_4827_; lean_object* v_err_4828_; lean_object* v___y_4831_; lean_object* v___y_4832_; lean_object* v_snd_4833_; lean_object* v___f_4835_; lean_object* v___y_4837_; lean_object* v_snd_4838_; lean_object* v___y_4839_; lean_object* v_pos_4840_; lean_object* v___y_4869_; lean_object* v_snd_4870_; lean_object* v_pos_4871_; lean_object* v_err_4872_; lean_object* v___y_4875_; lean_object* v___y_4876_; lean_object* v_snd_4877_; lean_object* v___f_4879_; lean_object* v_snd_4881_; lean_object* v___y_4882_; lean_object* v___y_4883_; lean_object* v_pos_4884_; lean_object* v_snd_4913_; lean_object* v___y_4914_; lean_object* v_pos_4915_; lean_object* v_err_4916_; lean_object* v___y_4919_; lean_object* v_snd_4920_; lean_object* v___y_4921_; lean_object* v___f_4923_; lean_object* v___y_4925_; lean_object* v_snd_4926_; lean_object* v___y_4927_; lean_object* v_pos_4928_; lean_object* v___y_4957_; lean_object* v_snd_4958_; lean_object* v_pos_4959_; lean_object* v_err_4960_; lean_object* v___y_4963_; lean_object* v___y_4964_; lean_object* v_snd_4965_; lean_object* v___f_4967_; lean_object* v_snd_4969_; lean_object* v___y_4970_; lean_object* v___y_4971_; lean_object* v_pos_4972_; lean_object* v___y_5001_; lean_object* v_snd_5002_; lean_object* v_pos_5003_; lean_object* v_err_5004_; lean_object* v___y_5007_; lean_object* v___y_5008_; lean_object* v_snd_5009_; lean_object* v___f_5011_; lean_object* v_snd_5013_; lean_object* v___y_5014_; lean_object* v___y_5015_; lean_object* v_pos_5016_; lean_object* v___y_5045_; lean_object* v_snd_5046_; lean_object* v_pos_5047_; lean_object* v_err_5048_; lean_object* v___y_5051_; lean_object* v___y_5052_; lean_object* v_snd_5053_; lean_object* v___y_5056_; lean_object* v_snd_5057_; lean_object* v___y_5058_; lean_object* v_pos_5059_; lean_object* v___y_5088_; lean_object* v_snd_5089_; lean_object* v_pos_5090_; lean_object* v_err_5091_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v_snd_5096_; lean_object* v___y_5099_; lean_object* v_snd_5100_; lean_object* v___y_5101_; lean_object* v_pos_5102_; lean_object* v___y_5131_; lean_object* v_snd_5132_; lean_object* v_pos_5133_; lean_object* v_err_5134_; lean_object* v___y_5137_; lean_object* v___y_5138_; lean_object* v_snd_5139_; lean_object* v___y_5142_; lean_object* v_snd_5143_; lean_object* v___y_5144_; lean_object* v_pos_5145_; lean_object* v___y_5174_; lean_object* v_snd_5175_; lean_object* v_pos_5176_; lean_object* v_err_5177_; lean_object* v___y_5180_; lean_object* v___y_5181_; lean_object* v_snd_5182_; lean_object* v___f_5184_; lean_object* v_snd_5186_; lean_object* v___y_5187_; lean_object* v___y_5188_; lean_object* v___y_5189_; lean_object* v_pos_5190_; lean_object* v_snd_5219_; lean_object* v___y_5220_; lean_object* v___y_5221_; lean_object* v_pos_5222_; lean_object* v_err_5223_; lean_object* v___y_5226_; lean_object* v_snd_5227_; lean_object* v___y_5228_; lean_object* v___y_5229_; lean_object* v___f_5231_; lean_object* v_snd_5233_; lean_object* v___y_5234_; lean_object* v___y_5235_; lean_object* v___y_5236_; lean_object* v_pos_5237_; lean_object* v___y_5266_; lean_object* v_snd_5267_; lean_object* v___y_5268_; lean_object* v_pos_5269_; lean_object* v_err_5270_; lean_object* v___y_5273_; lean_object* v___y_5274_; lean_object* v_snd_5275_; lean_object* v___y_5276_; lean_object* v___f_5278_; lean_object* v___y_5280_; lean_object* v_snd_5281_; lean_object* v___y_5282_; lean_object* v___y_5283_; lean_object* v_pos_5284_; lean_object* v___y_5313_; lean_object* v_snd_5314_; lean_object* v___y_5315_; lean_object* v_pos_5316_; lean_object* v_err_5317_; lean_object* v___y_5320_; lean_object* v___y_5321_; lean_object* v_snd_5322_; lean_object* v___y_5323_; lean_object* v___f_5325_; lean_object* v___y_5327_; lean_object* v___y_5328_; lean_object* v___y_5329_; lean_object* v___y_5330_; lean_object* v_pos_5331_; lean_object* v___y_5360_; lean_object* v___y_5361_; lean_object* v___y_5362_; lean_object* v_pos_5363_; lean_object* v_err_5364_; lean_object* v___y_5367_; lean_object* v___y_5368_; lean_object* v___y_5369_; lean_object* v___y_5370_; lean_object* v___f_5372_; lean_object* v_snd_5374_; lean_object* v___y_5375_; lean_object* v___y_5376_; lean_object* v_pos_5377_; lean_object* v_snd_5407_; lean_object* v___y_5408_; lean_object* v_pos_5409_; lean_object* v_err_5410_; lean_object* v___y_5413_; lean_object* v_snd_5414_; lean_object* v___y_5415_; lean_object* v___f_5417_; lean_object* v_snd_5419_; lean_object* v___y_5420_; lean_object* v___y_5421_; lean_object* v_pos_5422_; lean_object* v_snd_5451_; lean_object* v___y_5452_; lean_object* v_pos_5453_; lean_object* v_err_5454_; lean_object* v___y_5457_; lean_object* v_snd_5458_; lean_object* v___y_5459_; lean_object* v___f_5461_; lean_object* v_snd_5463_; lean_object* v___y_5464_; lean_object* v___y_5465_; lean_object* v_pos_5466_; lean_object* v_snd_5495_; lean_object* v___y_5496_; lean_object* v_pos_5497_; lean_object* v_err_5498_; lean_object* v___y_5501_; lean_object* v_snd_5502_; lean_object* v___y_5503_; lean_object* v___f_5505_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v_pos_5510_; lean_object* v___y_5539_; lean_object* v___y_5540_; lean_object* v_pos_5541_; lean_object* v_err_5542_; lean_object* v___y_5545_; lean_object* v___y_5546_; lean_object* v___y_5547_; lean_object* v___f_5549_; lean_object* v_snd_5551_; lean_object* v___y_5552_; lean_object* v_pos_5553_; lean_object* v_snd_5583_; lean_object* v_pos_5584_; lean_object* v_err_5585_; lean_object* v___y_5588_; lean_object* v_snd_5589_; lean_object* v___f_5591_; lean_object* v_snd_5593_; lean_object* v___y_5594_; lean_object* v_pos_5595_; lean_object* v_snd_5624_; lean_object* v_pos_5625_; lean_object* v_err_5626_; lean_object* v___y_5629_; lean_object* v_snd_5630_; lean_object* v___f_5632_; lean_object* v_snd_5634_; lean_object* v___y_5635_; lean_object* v_pos_5636_; lean_object* v_snd_5665_; lean_object* v_pos_5666_; lean_object* v_err_5667_; lean_object* v___y_5670_; lean_object* v_snd_5671_; lean_object* v___f_5673_; lean_object* v_snd_5675_; lean_object* v___y_5676_; lean_object* v_pos_5677_; lean_object* v_snd_5707_; lean_object* v_pos_5708_; lean_object* v_err_5709_; lean_object* v___y_5712_; lean_object* v_snd_5713_; lean_object* v___f_5715_; lean_object* v_snd_5717_; lean_object* v___y_5718_; lean_object* v_pos_5719_; lean_object* v_snd_5748_; lean_object* v_pos_5749_; lean_object* v_err_5750_; lean_object* v___y_5753_; lean_object* v_snd_5754_; lean_object* v___f_5756_; lean_object* v_snd_5758_; lean_object* v___y_5759_; lean_object* v_pos_5760_; lean_object* v_snd_5789_; lean_object* v_pos_5790_; lean_object* v_err_5791_; lean_object* v___y_5794_; lean_object* v_snd_5795_; lean_object* v___f_5797_; lean_object* v___y_5799_; lean_object* v_pos_5800_; lean_object* v_pos_5829_; lean_object* v_err_5830_; lean_object* v___x_5832_; uint8_t v_decide_5833_; 
v_fst_4335_ = lean_ctor_get(v_a_4330_, 0);
v_snd_4336_ = lean_ctor_get(v_a_4330_, 1);
lean_inc(v_snd_4336_);
v___f_4337_ = ((lean_object*)(l_Std_Time_parseModifier___closed__0));
v___f_4385_ = ((lean_object*)(l_Std_Time_parseModifier___closed__2));
v___f_4426_ = ((lean_object*)(l_Std_Time_parseModifier___closed__4));
v___f_4467_ = ((lean_object*)(l_Std_Time_parseModifier___closed__6));
v___f_4508_ = ((lean_object*)(l_Std_Time_parseModifier___closed__8));
v___f_4549_ = ((lean_object*)(l_Std_Time_parseModifier___closed__10));
v___f_4630_ = ((lean_object*)(l_Std_Time_parseModifier___closed__13));
v___f_4670_ = ((lean_object*)(l_Std_Time_parseModifier___closed__15));
v___f_4710_ = ((lean_object*)(l_Std_Time_parseModifier___closed__17));
v___f_4750_ = ((lean_object*)(l_Std_Time_parseModifier___closed__19));
v___f_4791_ = ((lean_object*)(l_Std_Time_parseModifier___closed__21));
v___f_4835_ = ((lean_object*)(l_Std_Time_parseModifier___closed__23));
v___f_4879_ = ((lean_object*)(l_Std_Time_parseModifier___closed__25));
v___f_4923_ = ((lean_object*)(l_Std_Time_parseModifier___closed__27));
v___f_4967_ = ((lean_object*)(l_Std_Time_parseModifier___closed__29));
v___f_5011_ = ((lean_object*)(l_Std_Time_parseModifier___closed__31));
v___f_5184_ = ((lean_object*)(l_Std_Time_parseModifier___closed__36));
v___f_5231_ = ((lean_object*)(l_Std_Time_parseModifier___closed__38));
v___f_5278_ = ((lean_object*)(l_Std_Time_parseModifier___closed__40));
v___f_5325_ = ((lean_object*)(l_Std_Time_parseModifier___closed__42));
v___f_5372_ = ((lean_object*)(l_Std_Time_parseModifier___closed__44));
v___f_5417_ = ((lean_object*)(l_Std_Time_parseModifier___closed__47));
v___f_5461_ = ((lean_object*)(l_Std_Time_parseModifier___closed__49));
v___f_5505_ = ((lean_object*)(l_Std_Time_parseModifier___closed__51));
v___f_5549_ = ((lean_object*)(l_Std_Time_parseModifier___closed__53));
v___f_5591_ = ((lean_object*)(l_Std_Time_parseModifier___closed__56));
v___f_5632_ = ((lean_object*)(l_Std_Time_parseModifier___closed__58));
v___f_5673_ = ((lean_object*)(l_Std_Time_parseModifier___closed__60));
v___f_5715_ = ((lean_object*)(l_Std_Time_parseModifier___closed__63));
v___f_5756_ = ((lean_object*)(l_Std_Time_parseModifier___closed__65));
v___f_5797_ = ((lean_object*)(l_Std_Time_parseModifier___closed__67));
v___x_5832_ = lean_string_utf8_byte_size(v_fst_4335_);
v_decide_5833_ = lean_nat_dec_eq(v_snd_4336_, v___x_5832_);
if (v_decide_5833_ == 0)
{
uint32_t v___x_5834_; uint32_t v_c_5835_; uint8_t v___x_5836_; 
v___x_5834_ = 71;
v_c_5835_ = lean_string_utf8_get_fast(v_fst_4335_, v_snd_4336_);
v___x_5836_ = lean_uint32_dec_eq(v_c_5835_, v___x_5834_);
if (v___x_5836_ == 0)
{
lean_object* v___x_5837_; 
v___x_5837_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1));
v_pos_5829_ = v_a_4330_;
v_err_5830_ = v___x_5837_;
goto v___jp_5828_;
}
else
{
lean_object* v___x_5839_; uint8_t v_isShared_5840_; uint8_t v_isSharedCheck_5854_; 
lean_inc(v_fst_4335_);
v_isSharedCheck_5854_ = !lean_is_exclusive(v_a_4330_);
if (v_isSharedCheck_5854_ == 0)
{
lean_object* v_unused_5855_; lean_object* v_unused_5856_; 
v_unused_5855_ = lean_ctor_get(v_a_4330_, 1);
lean_dec(v_unused_5855_);
v_unused_5856_ = lean_ctor_get(v_a_4330_, 0);
lean_dec(v_unused_5856_);
v___x_5839_ = v_a_4330_;
v_isShared_5840_ = v_isSharedCheck_5854_;
goto v_resetjp_5838_;
}
else
{
lean_dec(v_a_4330_);
v___x_5839_ = lean_box(0);
v_isShared_5840_ = v_isSharedCheck_5854_;
goto v_resetjp_5838_;
}
v_resetjp_5838_:
{
lean_object* v___x_5841_; lean_object* v_it_x27_5843_; 
v___x_5841_ = lean_string_utf8_next_fast(v_fst_4335_, v_snd_4336_);
if (v_isShared_5840_ == 0)
{
lean_ctor_set(v___x_5839_, 1, v___x_5841_);
v_it_x27_5843_ = v___x_5839_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5853_; 
v_reuseFailAlloc_5853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5853_, 0, v_fst_4335_);
lean_ctor_set(v_reuseFailAlloc_5853_, 1, v___x_5841_);
v_it_x27_5843_ = v_reuseFailAlloc_5853_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
lean_object* v___x_5844_; lean_object* v___x_5845_; 
v___x_5844_ = ((lean_object*)(l_Std_Time_parseModifier___closed__69));
v___x_5845_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(v___x_5844_, v_it_x27_5843_);
if (lean_obj_tag(v___x_5845_) == 0)
{
lean_object* v_pos_5846_; lean_object* v_res_5847_; lean_object* v___f_5848_; lean_object* v___x_5849_; 
v_pos_5846_ = lean_ctor_get(v___x_5845_, 0);
lean_inc(v_pos_5846_);
v_res_5847_ = lean_ctor_get(v___x_5845_, 1);
lean_inc(v_res_5847_);
lean_dec_ref_known(v___x_5845_, 2);
v___f_5848_ = ((lean_object*)(l_Std_Time_parseModifier___closed__70));
v___x_5849_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_5848_, v_res_5847_, v_pos_5846_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_dec(v_snd_4336_);
return v___x_5849_;
}
else
{
lean_object* v_pos_5850_; 
v_pos_5850_ = lean_ctor_get(v___x_5849_, 0);
lean_inc(v_pos_5850_);
v___y_5799_ = v___x_5849_;
v_pos_5800_ = v_pos_5850_;
goto v___jp_5798_;
}
}
else
{
lean_object* v_pos_5851_; lean_object* v_err_5852_; 
v_pos_5851_ = lean_ctor_get(v___x_5845_, 0);
lean_inc(v_pos_5851_);
v_err_5852_ = lean_ctor_get(v___x_5845_, 1);
lean_inc(v_err_5852_);
lean_dec_ref_known(v___x_5845_, 2);
v_pos_5829_ = v_pos_5851_;
v_err_5830_ = v_err_5852_;
goto v___jp_5828_;
}
}
}
}
}
else
{
lean_object* v___x_5857_; 
v___x_5857_ = lean_box(0);
v_pos_5829_ = v_a_4330_;
v_err_5830_ = v___x_5857_;
goto v___jp_5828_;
}
v___jp_4331_:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = lean_box(0);
v___x_4334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___y_4332_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
return v___x_4334_;
}
v___jp_4338_:
{
lean_object* v_fst_4342_; lean_object* v_snd_4343_; uint8_t v_decide_4344_; 
v_fst_4342_ = lean_ctor_get(v_pos_4341_, 0);
v_snd_4343_ = lean_ctor_get(v_pos_4341_, 1);
v_decide_4344_ = lean_nat_dec_eq(v_snd_4339_, v_snd_4343_);
lean_dec(v_snd_4339_);
if (v_decide_4344_ == 0)
{
lean_dec_ref(v_pos_4341_);
return v___y_4340_;
}
else
{
lean_object* v___x_4345_; uint8_t v_decide_4346_; 
lean_dec_ref(v___y_4340_);
v___x_4345_ = lean_string_utf8_byte_size(v_fst_4342_);
v_decide_4346_ = lean_nat_dec_eq(v_snd_4343_, v___x_4345_);
if (v_decide_4346_ == 0)
{
if (v_decide_4344_ == 0)
{
v___y_4332_ = v_pos_4341_;
goto v___jp_4331_;
}
else
{
uint32_t v___x_4347_; uint32_t v_c_4348_; uint8_t v___x_4349_; 
v___x_4347_ = 90;
v_c_4348_ = lean_string_utf8_get_fast(v_fst_4342_, v_snd_4343_);
v___x_4349_ = lean_uint32_dec_eq(v_c_4348_, v___x_4347_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4350_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1));
v___x_4351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4351_, 0, v_pos_4341_);
lean_ctor_set(v___x_4351_, 1, v___x_4350_);
return v___x_4351_;
}
else
{
lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4373_; 
lean_inc(v_snd_4343_);
lean_inc(v_fst_4342_);
v_isSharedCheck_4373_ = !lean_is_exclusive(v_pos_4341_);
if (v_isSharedCheck_4373_ == 0)
{
lean_object* v_unused_4374_; lean_object* v_unused_4375_; 
v_unused_4374_ = lean_ctor_get(v_pos_4341_, 1);
lean_dec(v_unused_4374_);
v_unused_4375_ = lean_ctor_get(v_pos_4341_, 0);
lean_dec(v_unused_4375_);
v___x_4353_ = v_pos_4341_;
v_isShared_4354_ = v_isSharedCheck_4373_;
goto v_resetjp_4352_;
}
else
{
lean_dec(v_pos_4341_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4373_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4355_; lean_object* v_it_x27_4357_; 
v___x_4355_ = lean_string_utf8_next_fast(v_fst_4342_, v_snd_4343_);
lean_dec(v_snd_4343_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 1, v___x_4355_);
v_it_x27_4357_ = v___x_4353_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_fst_4342_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v___x_4355_);
v_it_x27_4357_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4358_ = ((lean_object*)(l_Std_Time_parseModifier___closed__1));
v___x_4359_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(v___x_4358_, v_it_x27_4357_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_pos_4360_; lean_object* v_res_4361_; lean_object* v___x_4362_; 
v_pos_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_pos_4360_);
v_res_4361_ = lean_ctor_get(v___x_4359_, 1);
lean_inc(v_res_4361_);
lean_dec_ref_known(v___x_4359_, 2);
v___x_4362_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(v___f_4337_, v_res_4361_, v_pos_4360_);
return v___x_4362_;
}
else
{
lean_object* v_pos_4363_; lean_object* v_err_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
v_pos_4363_ = lean_ctor_get(v___x_4359_, 0);
v_err_4364_ = lean_ctor_get(v___x_4359_, 1);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4359_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_err_4364_);
lean_inc(v_pos_4363_);
lean_dec(v___x_4359_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_pos_4363_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_err_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
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
v___y_4332_ = v_pos_4341_;
goto v___jp_4331_;
}
}
}
v___jp_4376_:
{
lean_object* v___x_4380_; 
lean_inc_ref(v_pos_4378_);
v___x_4380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4380_, 0, v_pos_4378_);
lean_ctor_set(v___x_4380_, 1, v_err_4379_);
v_snd_4339_ = v_snd_4377_;
v___y_4340_ = v___x_4380_;
v_pos_4341_ = v_pos_4378_;
goto v___jp_4338_;
}
v___jp_4381_:
{
lean_object* v___x_4384_; 
v___x_4384_ = lean_box(0);
v_snd_4377_ = v_snd_4383_;
v_pos_4378_ = v___y_4382_;
v_err_4379_ = v___x_4384_;
goto v___jp_4376_;
}
v___jp_4386_:
{
lean_object* v_fst_4390_; lean_object* v_snd_4391_; uint8_t v_decide_4392_; 
v_fst_4390_ = lean_ctor_get(v_pos_4389_, 0);
v_snd_4391_ = lean_ctor_get(v_pos_4389_, 1);
lean_inc(v_snd_4391_);
v_decide_4392_ = lean_nat_dec_eq(v_snd_4387_, v_snd_4391_);
lean_dec(v_snd_4387_);
if (v_decide_4392_ == 0)
{
lean_dec(v_snd_4391_);
lean_dec_ref(v_pos_4389_);
return v___y_4388_;
}
else
{
lean_object* v___x_4393_; uint8_t v_decide_4394_; 
lean_dec_ref(v___y_4388_);
v___x_4393_ = lean_string_utf8_byte_size(v_fst_4390_);
v_decide_4394_ = lean_nat_dec_eq(v_snd_4391_, v___x_4393_);
if (v_decide_4394_ == 0)
{
if (v_decide_4392_ == 0)
{
v___y_4382_ = v_pos_4389_;
v_snd_4383_ = v_snd_4391_;
goto v___jp_4381_;
}
else
{
uint32_t v___x_4395_; uint32_t v_c_4396_; uint8_t v___x_4397_; 
v___x_4395_ = 120;
v_c_4396_ = lean_string_utf8_get_fast(v_fst_4390_, v_snd_4391_);
v___x_4397_ = lean_uint32_dec_eq(v_c_4396_, v___x_4395_);
if (v___x_4397_ == 0)
{
lean_object* v___x_4398_; 
v___x_4398_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1));
v_snd_4377_ = v_snd_4391_;
v_pos_4378_ = v_pos_4389_;
v_err_4379_ = v___x_4398_;
goto v___jp_4376_;
}
else
{
lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4414_; 
lean_inc(v_fst_4390_);
v_isSharedCheck_4414_ = !lean_is_exclusive(v_pos_4389_);
if (v_isSharedCheck_4414_ == 0)
{
lean_object* v_unused_4415_; lean_object* v_unused_4416_; 
v_unused_4415_ = lean_ctor_get(v_pos_4389_, 1);
lean_dec(v_unused_4415_);
v_unused_4416_ = lean_ctor_get(v_pos_4389_, 0);
lean_dec(v_unused_4416_);
v___x_4400_ = v_pos_4389_;
v_isShared_4401_ = v_isSharedCheck_4414_;
goto v_resetjp_4399_;
}
else
{
lean_dec(v_pos_4389_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4414_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4402_; lean_object* v_it_x27_4404_; 
v___x_4402_ = lean_string_utf8_next_fast(v_fst_4390_, v_snd_4391_);
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 1, v___x_4402_);
v_it_x27_4404_ = v___x_4400_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_fst_4390_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v___x_4402_);
v_it_x27_4404_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4405_ = ((lean_object*)(l_Std_Time_parseModifier___closed__3));
v___x_4406_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(v___x_4405_, v_it_x27_4404_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_pos_4407_; lean_object* v_res_4408_; lean_object* v___x_4409_; 
v_pos_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_pos_4407_);
v_res_4408_ = lean_ctor_get(v___x_4406_, 1);
lean_inc(v_res_4408_);
lean_dec_ref_known(v___x_4406_, 2);
v___x_4409_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4385_, v_res_4408_, v_pos_4407_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_dec(v_snd_4391_);
return v___x_4409_;
}
else
{
lean_object* v_pos_4410_; 
v_pos_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_pos_4410_);
v_snd_4339_ = v_snd_4391_;
v___y_4340_ = v___x_4409_;
v_pos_4341_ = v_pos_4410_;
goto v___jp_4338_;
}
}
else
{
lean_object* v_pos_4411_; lean_object* v_err_4412_; 
v_pos_4411_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_pos_4411_);
v_err_4412_ = lean_ctor_get(v___x_4406_, 1);
lean_inc(v_err_4412_);
lean_dec_ref_known(v___x_4406_, 2);
v_snd_4377_ = v_snd_4391_;
v_pos_4378_ = v_pos_4411_;
v_err_4379_ = v_err_4412_;
goto v___jp_4376_;
}
}
}
}
}
}
else
{
v___y_4382_ = v_pos_4389_;
v_snd_4383_ = v_snd_4391_;
goto v___jp_4381_;
}
}
}
v___jp_4417_:
{
lean_object* v___x_4421_; 
lean_inc_ref(v_pos_4419_);
v___x_4421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4421_, 0, v_pos_4419_);
lean_ctor_set(v___x_4421_, 1, v_err_4420_);
v_snd_4387_ = v_snd_4418_;
v___y_4388_ = v___x_4421_;
v_pos_4389_ = v_pos_4419_;
goto v___jp_4386_;
}
v___jp_4422_:
{
lean_object* v___x_4425_; 
v___x_4425_ = lean_box(0);
v_snd_4418_ = v_snd_4424_;
v_pos_4419_ = v___y_4423_;
v_err_4420_ = v___x_4425_;
goto v___jp_4417_;
}
v___jp_4427_:
{
lean_object* v_fst_4431_; lean_object* v_snd_4432_; uint8_t v_decide_4433_; 
v_fst_4431_ = lean_ctor_get(v_pos_4430_, 0);
v_snd_4432_ = lean_ctor_get(v_pos_4430_, 1);
lean_inc(v_snd_4432_);
v_decide_4433_ = lean_nat_dec_eq(v_snd_4428_, v_snd_4432_);
lean_dec(v_snd_4428_);
if (v_decide_4433_ == 0)
{
lean_dec(v_snd_4432_);
lean_dec_ref(v_pos_4430_);
return v___y_4429_;
}
else
{
lean_object* v___x_4434_; uint8_t v_decide_4435_; 
lean_dec_ref(v___y_4429_);
v___x_4434_ = lean_string_utf8_byte_size(v_fst_4431_);
v_decide_4435_ = lean_nat_dec_eq(v_snd_4432_, v___x_4434_);
if (v_decide_4435_ == 0)
{
if (v_decide_4433_ == 0)
{
v___y_4423_ = v_pos_4430_;
v_snd_4424_ = v_snd_4432_;
goto v___jp_4422_;
}
else
{
uint32_t v___x_4436_; uint32_t v_c_4437_; uint8_t v___x_4438_; 
v___x_4436_ = 88;
v_c_4437_ = lean_string_utf8_get_fast(v_fst_4431_, v_snd_4432_);
v___x_4438_ = lean_uint32_dec_eq(v_c_4437_, v___x_4436_);
if (v___x_4438_ == 0)
{
lean_object* v___x_4439_; 
v___x_4439_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1));
v_snd_4418_ = v_snd_4432_;
v_pos_4419_ = v_pos_4430_;
v_err_4420_ = v___x_4439_;
goto v___jp_4417_;
}
else
{
lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4455_; 
lean_inc(v_fst_4431_);
v_isSharedCheck_4455_ = !lean_is_exclusive(v_pos_4430_);
if (v_isSharedCheck_4455_ == 0)
{
lean_object* v_unused_4456_; lean_object* v_unused_4457_; 
v_unused_4456_ = lean_ctor_get(v_pos_4430_, 1);
lean_dec(v_unused_4456_);
v_unused_4457_ = lean_ctor_get(v_pos_4430_, 0);
lean_dec(v_unused_4457_);
v___x_4441_ = v_pos_4430_;
v_isShared_4442_ = v_isSharedCheck_4455_;
goto v_resetjp_4440_;
}
else
{
lean_dec(v_pos_4430_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4455_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4443_; lean_object* v_it_x27_4445_; 
v___x_4443_ = lean_string_utf8_next_fast(v_fst_4431_, v_snd_4432_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 1, v___x_4443_);
v_it_x27_4445_ = v___x_4441_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_fst_4431_);
lean_ctor_set(v_reuseFailAlloc_4454_, 1, v___x_4443_);
v_it_x27_4445_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4446_ = ((lean_object*)(l_Std_Time_parseModifier___closed__5));
v___x_4447_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(v___x_4446_, v_it_x27_4445_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_pos_4448_; lean_object* v_res_4449_; lean_object* v___x_4450_; 
v_pos_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_pos_4448_);
v_res_4449_ = lean_ctor_get(v___x_4447_, 1);
lean_inc(v_res_4449_);
lean_dec_ref_known(v___x_4447_, 2);
v___x_4450_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4426_, v_res_4449_, v_pos_4448_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_dec(v_snd_4432_);
return v___x_4450_;
}
else
{
lean_object* v_pos_4451_; 
v_pos_4451_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_pos_4451_);
v_snd_4387_ = v_snd_4432_;
v___y_4388_ = v___x_4450_;
v_pos_4389_ = v_pos_4451_;
goto v___jp_4386_;
}
}
else
{
lean_object* v_pos_4452_; lean_object* v_err_4453_; 
v_pos_4452_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_pos_4452_);
v_err_4453_ = lean_ctor_get(v___x_4447_, 1);
lean_inc(v_err_4453_);
lean_dec_ref_known(v___x_4447_, 2);
v_snd_4418_ = v_snd_4432_;
v_pos_4419_ = v_pos_4452_;
v_err_4420_ = v_err_4453_;
goto v___jp_4417_;
}
}
}
}
}
}
else
{
v___y_4423_ = v_pos_4430_;
v_snd_4424_ = v_snd_4432_;
goto v___jp_4422_;
}
}
}
v___jp_4458_:
{
lean_object* v___x_4462_; 
lean_inc_ref(v_pos_4460_);
v___x_4462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4462_, 0, v_pos_4460_);
lean_ctor_set(v___x_4462_, 1, v_err_4461_);
v_snd_4428_ = v_snd_4459_;
v___y_4429_ = v___x_4462_;
v_pos_4430_ = v_pos_4460_;
goto v___jp_4427_;
}
v___jp_4463_:
{
lean_object* v___x_4466_; 
v___x_4466_ = lean_box(0);
v_snd_4459_ = v_snd_4465_;
v_pos_4460_ = v___y_4464_;
v_err_4461_ = v___x_4466_;
goto v___jp_4458_;
}
v___jp_4468_:
{
lean_object* v_fst_4472_; lean_object* v_snd_4473_; uint8_t v_decide_4474_; 
v_fst_4472_ = lean_ctor_get(v_pos_4471_, 0);
v_snd_4473_ = lean_ctor_get(v_pos_4471_, 1);
lean_inc(v_snd_4473_);
v_decide_4474_ = lean_nat_dec_eq(v_snd_4469_, v_snd_4473_);
lean_dec(v_snd_4469_);
if (v_decide_4474_ == 0)
{
lean_dec(v_snd_4473_);
lean_dec_ref(v_pos_4471_);
return v___y_4470_;
}
else
{
lean_object* v___x_4475_; uint8_t v_decide_4476_; 
lean_dec_ref(v___y_4470_);
v___x_4475_ = lean_string_utf8_byte_size(v_fst_4472_);
v_decide_4476_ = lean_nat_dec_eq(v_snd_4473_, v___x_4475_);
if (v_decide_4476_ == 0)
{
if (v_decide_4474_ == 0)
{
v___y_4464_ = v_pos_4471_;
v_snd_4465_ = v_snd_4473_;
goto v___jp_4463_;
}
else
{
uint32_t v___x_4477_; uint32_t v_c_4478_; uint8_t v___x_4479_; 
v___x_4477_ = 79;
v_c_4478_ = lean_string_utf8_get_fast(v_fst_4472_, v_snd_4473_);
v___x_4479_ = lean_uint32_dec_eq(v_c_4478_, v___x_4477_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4480_; 
v___x_4480_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1));
v_snd_4459_ = v_snd_4473_;
v_pos_4460_ = v_pos_4471_;
v_err_4461_ = v___x_4480_;
goto v___jp_4458_;
}
else
{
lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4496_; 
lean_inc(v_fst_4472_);
v_isSharedCheck_4496_ = !lean_is_exclusive(v_pos_4471_);
if (v_isSharedCheck_4496_ == 0)
{
lean_object* v_unused_4497_; lean_object* v_unused_4498_; 
v_unused_4497_ = lean_ctor_get(v_pos_4471_, 1);
lean_dec(v_unused_4497_);
v_unused_4498_ = lean_ctor_get(v_pos_4471_, 0);
lean_dec(v_unused_4498_);
v___x_4482_ = v_pos_4471_;
v_isShared_4483_ = v_isSharedCheck_4496_;
goto v_resetjp_4481_;
}
else
{
lean_dec(v_pos_4471_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4496_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4484_; lean_object* v_it_x27_4486_; 
v___x_4484_ = lean_string_utf8_next_fast(v_fst_4472_, v_snd_4473_);
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 1, v___x_4484_);
v_it_x27_4486_ = v___x_4482_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_fst_4472_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v___x_4484_);
v_it_x27_4486_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = ((lean_object*)(l_Std_Time_parseModifier___closed__7));
v___x_4488_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(v___x_4487_, v_it_x27_4486_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_pos_4489_; lean_object* v_res_4490_; lean_object* v___x_4491_; 
v_pos_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_pos_4489_);
v_res_4490_ = lean_ctor_get(v___x_4488_, 1);
lean_inc(v_res_4490_);
lean_dec_ref_known(v___x_4488_, 2);
v___x_4491_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(v___f_4467_, v_res_4490_, v_pos_4489_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_dec(v_snd_4473_);
return v___x_4491_;
}
else
{
lean_object* v_pos_4492_; 
v_pos_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_pos_4492_);
v_snd_4428_ = v_snd_4473_;
v___y_4429_ = v___x_4491_;
v_pos_4430_ = v_pos_4492_;
goto v___jp_4427_;
}
}
else
{
lean_object* v_pos_4493_; lean_object* v_err_4494_; 
v_pos_4493_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_pos_4493_);
v_err_4494_ = lean_ctor_get(v___x_4488_, 1);
lean_inc(v_err_4494_);
lean_dec_ref_known(v___x_4488_, 2);
v_snd_4459_ = v_snd_4473_;
v_pos_4460_ = v_pos_4493_;
v_err_4461_ = v_err_4494_;
goto v___jp_4458_;
}
}
}
}
}
}
else
{
v___y_4464_ = v_pos_4471_;
v_snd_4465_ = v_snd_4473_;
goto v___jp_4463_;
}
}
}
v___jp_4499_:
{
lean_object* v___x_4503_; 
lean_inc_ref(v_pos_4501_);
v___x_4503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4503_, 0, v_pos_4501_);
lean_ctor_set(v___x_4503_, 1, v_err_4502_);
v_snd_4469_ = v_snd_4500_;
v___y_4470_ = v___x_4503_;
v_pos_4471_ = v_pos_4501_;
goto v___jp_4468_;
}
v___jp_4504_:
{
lean_object* v___x_4507_; 
v___x_4507_ = lean_box(0);
v_snd_4500_ = v_snd_4506_;
v_pos_4501_ = v___y_4505_;
v_err_4502_ = v___x_4507_;
goto v___jp_4499_;
}
v___jp_4509_:
{
lean_object* v_fst_4513_; lean_object* v_snd_4514_; uint8_t v_decide_4515_; 
v_fst_4513_ = lean_ctor_get(v_pos_4512_, 0);
v_snd_4514_ = lean_ctor_get(v_pos_4512_, 1);
lean_inc(v_snd_4514_);
v_decide_4515_ = lean_nat_dec_eq(v_snd_4510_, v_snd_4514_);
lean_dec(v_snd_4510_);
if (v_decide_4515_ == 0)
{
lean_dec(v_snd_4514_);
lean_dec_ref(v_pos_4512_);
return v___y_4511_;
}
else
{
lean_object* v___x_4516_; uint8_t v_decide_4517_; 
lean_dec_ref(v___y_4511_);
v___x_4516_ = lean_string_utf8_byte_size(v_fst_4513_);
v_decide_4517_ = lean_nat_dec_eq(v_snd_4514_, v___x_4516_);
if (v_decide_4517_ == 0)
{
if (v_decide_4515_ == 0)
{
v___y_4505_ = v_pos_4512_;
v_snd_4506_ = v_snd_4514_;
goto v___jp_4504_;
}
else
{
uint32_t v___x_4518_; uint32_t v_c_4519_; uint8_t v___x_4520_; 
v___x_4518_ = 118;
v_c_4519_ = lean_string_utf8_get_fast(v_fst_4513_, v_snd_4514_);
v___x_4520_ = lean_uint32_dec_eq(v_c_4519_, v___x_4518_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; 
v___x_4521_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1));
v_snd_4500_ = v_snd_4514_;
v_pos_4501_ = v_pos_4512_;
v_err_4502_ = v___x_4521_;
goto v___jp_4499_;
}
else
{
lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4537_; 
lean_inc(v_fst_4513_);
v_isSharedCheck_4537_ = !lean_is_exclusive(v_pos_4512_);
if (v_isSharedCheck_4537_ == 0)
{
lean_object* v_unused_4538_; lean_object* v_unused_4539_; 
v_unused_4538_ = lean_ctor_get(v_pos_4512_, 1);
lean_dec(v_unused_4538_);
v_unused_4539_ = lean_ctor_get(v_pos_4512_, 0);
lean_dec(v_unused_4539_);
v___x_4523_ = v_pos_4512_;
v_isShared_4524_ = v_isSharedCheck_4537_;
goto v_resetjp_4522_;
}
else
{
lean_dec(v_pos_4512_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4537_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4525_; lean_object* v_it_x27_4527_; 
v___x_4525_ = lean_string_utf8_next_fast(v_fst_4513_, v_snd_4514_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 1, v___x_4525_);
v_it_x27_4527_ = v___x_4523_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_fst_4513_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v___x_4525_);
v_it_x27_4527_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4528_ = ((lean_object*)(l_Std_Time_parseModifier___closed__9));
v___x_4529_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(v___x_4528_, v_it_x27_4527_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_pos_4530_; lean_object* v_res_4531_; lean_object* v___x_4532_; 
v_pos_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_pos_4530_);
v_res_4531_ = lean_ctor_get(v___x_4529_, 1);
lean_inc(v_res_4531_);
lean_dec_ref_known(v___x_4529_, 2);
v___x_4532_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4508_, v_res_4531_, v_pos_4530_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_dec(v_snd_4514_);
return v___x_4532_;
}
else
{
lean_object* v_pos_4533_; 
v_pos_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_pos_4533_);
v_snd_4469_ = v_snd_4514_;
v___y_4470_ = v___x_4532_;
v_pos_4471_ = v_pos_4533_;
goto v___jp_4468_;
}
}
else
{
lean_object* v_pos_4534_; lean_object* v_err_4535_; 
v_pos_4534_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_pos_4534_);
v_err_4535_ = lean_ctor_get(v___x_4529_, 1);
lean_inc(v_err_4535_);
lean_dec_ref_known(v___x_4529_, 2);
v_snd_4500_ = v_snd_4514_;
v_pos_4501_ = v_pos_4534_;
v_err_4502_ = v_err_4535_;
goto v___jp_4499_;
}
}
}
}
}
}
else
{
v___y_4505_ = v_pos_4512_;
v_snd_4506_ = v_snd_4514_;
goto v___jp_4504_;
}
}
}
v___jp_4540_:
{
lean_object* v___x_4544_; 
lean_inc_ref(v_pos_4542_);
v___x_4544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4544_, 0, v_pos_4542_);
lean_ctor_set(v___x_4544_, 1, v_err_4543_);
v_snd_4510_ = v_snd_4541_;
v___y_4511_ = v___x_4544_;
v_pos_4512_ = v_pos_4542_;
goto v___jp_4509_;
}
v___jp_4545_:
{
lean_object* v___x_4548_; 
v___x_4548_ = lean_box(0);
v_snd_4541_ = v_snd_4547_;
v_pos_4542_ = v___y_4546_;
v_err_4543_ = v___x_4548_;
goto v___jp_4540_;
}
v___jp_4550_:
{
lean_object* v_fst_4554_; lean_object* v_snd_4555_; uint8_t v_decide_4556_; 
v_fst_4554_ = lean_ctor_get(v_pos_4553_, 0);
v_snd_4555_ = lean_ctor_get(v_pos_4553_, 1);
lean_inc(v_snd_4555_);
v_decide_4556_ = lean_nat_dec_eq(v_snd_4551_, v_snd_4555_);
lean_dec(v_snd_4551_);
if (v_decide_4556_ == 0)
{
lean_dec(v_snd_4555_);
lean_dec_ref(v_pos_4553_);
return v___y_4552_;
}
else
{
lean_object* v___x_4557_; uint8_t v_decide_4558_; 
lean_dec_ref(v___y_4552_);
v___x_4557_ = lean_string_utf8_byte_size(v_fst_4554_);
v_decide_4558_ = lean_nat_dec_eq(v_snd_4555_, v___x_4557_);
if (v_decide_4558_ == 0)
{
if (v_decide_4556_ == 0)
{
v___y_4546_ = v_pos_4553_;
v_snd_4547_ = v_snd_4555_;
goto v___jp_4545_;
}
else
{
uint32_t v___x_4559_; uint32_t v_c_4560_; uint8_t v___x_4561_; 
v___x_4559_ = 122;
v_c_4560_ = lean_string_utf8_get_fast(v_fst_4554_, v_snd_4555_);
v___x_4561_ = lean_uint32_dec_eq(v_c_4560_, v___x_4559_);
if (v___x_4561_ == 0)
{
lean_object* v___x_4562_; 
v___x_4562_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1));
v_snd_4541_ = v_snd_4555_;
v_pos_4542_ = v_pos_4553_;
v_err_4543_ = v___x_4562_;
goto v___jp_4540_;
}
else
{
lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4578_; 
lean_inc(v_fst_4554_);
v_isSharedCheck_4578_ = !lean_is_exclusive(v_pos_4553_);
if (v_isSharedCheck_4578_ == 0)
{
lean_object* v_unused_4579_; lean_object* v_unused_4580_; 
v_unused_4579_ = lean_ctor_get(v_pos_4553_, 1);
lean_dec(v_unused_4579_);
v_unused_4580_ = lean_ctor_get(v_pos_4553_, 0);
lean_dec(v_unused_4580_);
v___x_4564_ = v_pos_4553_;
v_isShared_4565_ = v_isSharedCheck_4578_;
goto v_resetjp_4563_;
}
else
{
lean_dec(v_pos_4553_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4578_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4566_; lean_object* v_it_x27_4568_; 
v___x_4566_ = lean_string_utf8_next_fast(v_fst_4554_, v_snd_4555_);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 1, v___x_4566_);
v_it_x27_4568_ = v___x_4564_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_fst_4554_);
lean_ctor_set(v_reuseFailAlloc_4577_, 1, v___x_4566_);
v_it_x27_4568_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4569_ = ((lean_object*)(l_Std_Time_parseModifier___closed__11));
v___x_4570_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(v___x_4569_, v_it_x27_4568_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_pos_4571_; lean_object* v_res_4572_; lean_object* v___x_4573_; 
v_pos_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_pos_4571_);
v_res_4572_ = lean_ctor_get(v___x_4570_, 1);
lean_inc(v_res_4572_);
lean_dec_ref_known(v___x_4570_, 2);
v___x_4573_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4549_, v_res_4572_, v_pos_4571_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_dec(v_snd_4555_);
return v___x_4573_;
}
else
{
lean_object* v_pos_4574_; 
v_pos_4574_ = lean_ctor_get(v___x_4573_, 0);
lean_inc(v_pos_4574_);
v_snd_4510_ = v_snd_4555_;
v___y_4511_ = v___x_4573_;
v_pos_4512_ = v_pos_4574_;
goto v___jp_4509_;
}
}
else
{
lean_object* v_pos_4575_; lean_object* v_err_4576_; 
v_pos_4575_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_pos_4575_);
v_err_4576_ = lean_ctor_get(v___x_4570_, 1);
lean_inc(v_err_4576_);
lean_dec_ref_known(v___x_4570_, 2);
v_snd_4541_ = v_snd_4555_;
v_pos_4542_ = v_pos_4575_;
v_err_4543_ = v_err_4576_;
goto v___jp_4540_;
}
}
}
}
}
}
else
{
v___y_4546_ = v_pos_4553_;
v_snd_4547_ = v_snd_4555_;
goto v___jp_4545_;
}
}
}
v___jp_4581_:
{
lean_object* v___x_4585_; 
lean_inc_ref(v_pos_4583_);
v___x_4585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4585_, 0, v_pos_4583_);
lean_ctor_set(v___x_4585_, 1, v_err_4584_);
v_snd_4551_ = v_snd_4582_;
v___y_4552_ = v___x_4585_;
v_pos_4553_ = v_pos_4583_;
goto v___jp_4550_;
}
v___jp_4586_:
{
lean_object* v___x_4589_; 
v___x_4589_ = lean_box(0);
v_snd_4582_ = v_snd_4588_;
v_pos_4583_ = v___y_4587_;
v_err_4584_ = v___x_4589_;
goto v___jp_4581_;
}
v___jp_4590_:
{
lean_object* v_fst_4594_; lean_object* v_snd_4595_; uint8_t v_decide_4596_; 
v_fst_4594_ = lean_ctor_get(v_pos_4593_, 0);
v_snd_4595_ = lean_ctor_get(v_pos_4593_, 1);
lean_inc(v_snd_4595_);
v_decide_4596_ = lean_nat_dec_eq(v_snd_4591_, v_snd_4595_);
lean_dec(v_snd_4591_);
if (v_decide_4596_ == 0)
{
lean_dec(v_snd_4595_);
lean_dec_ref(v_pos_4593_);
return v___y_4592_;
}
else
{
lean_object* v___x_4597_; uint8_t v_decide_4598_; 
lean_dec_ref(v___y_4592_);
v___x_4597_ = lean_string_utf8_byte_size(v_fst_4594_);
v_decide_4598_ = lean_nat_dec_eq(v_snd_4595_, v___x_4597_);
if (v_decide_4598_ == 0)
{
if (v_decide_4596_ == 0)
{
v___y_4587_ = v_pos_4593_;
v_snd_4588_ = v_snd_4595_;
goto v___jp_4586_;
}
else
{
uint32_t v___x_4599_; uint32_t v_c_4600_; uint8_t v___x_4601_; 
v___x_4599_ = 86;
v_c_4600_ = lean_string_utf8_get_fast(v_fst_4594_, v_snd_4595_);
v___x_4601_ = lean_uint32_dec_eq(v_c_4600_, v___x_4599_);
if (v___x_4601_ == 0)
{
lean_object* v___x_4602_; 
v___x_4602_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1));
v_snd_4582_ = v_snd_4595_;
v_pos_4583_ = v_pos_4593_;
v_err_4584_ = v___x_4602_;
goto v___jp_4581_;
}
else
{
lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4618_; 
lean_inc(v_fst_4594_);
v_isSharedCheck_4618_ = !lean_is_exclusive(v_pos_4593_);
if (v_isSharedCheck_4618_ == 0)
{
lean_object* v_unused_4619_; lean_object* v_unused_4620_; 
v_unused_4619_ = lean_ctor_get(v_pos_4593_, 1);
lean_dec(v_unused_4619_);
v_unused_4620_ = lean_ctor_get(v_pos_4593_, 0);
lean_dec(v_unused_4620_);
v___x_4604_ = v_pos_4593_;
v_isShared_4605_ = v_isSharedCheck_4618_;
goto v_resetjp_4603_;
}
else
{
lean_dec(v_pos_4593_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4618_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4606_; lean_object* v_it_x27_4608_; 
v___x_4606_ = lean_string_utf8_next_fast(v_fst_4594_, v_snd_4595_);
if (v_isShared_4605_ == 0)
{
lean_ctor_set(v___x_4604_, 1, v___x_4606_);
v_it_x27_4608_ = v___x_4604_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_fst_4594_);
lean_ctor_set(v_reuseFailAlloc_4617_, 1, v___x_4606_);
v_it_x27_4608_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4609_ = ((lean_object*)(l_Std_Time_parseModifier___closed__12));
v___x_4610_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(v___x_4609_, v_it_x27_4608_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_pos_4611_; lean_object* v_res_4612_; lean_object* v___x_4613_; 
v_pos_4611_ = lean_ctor_get(v___x_4610_, 0);
lean_inc(v_pos_4611_);
v_res_4612_ = lean_ctor_get(v___x_4610_, 1);
lean_inc(v_res_4612_);
lean_dec_ref_known(v___x_4610_, 2);
v___x_4613_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(v_res_4612_, v_pos_4611_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_dec(v_snd_4595_);
return v___x_4613_;
}
else
{
lean_object* v_pos_4614_; 
v_pos_4614_ = lean_ctor_get(v___x_4613_, 0);
lean_inc(v_pos_4614_);
v_snd_4551_ = v_snd_4595_;
v___y_4552_ = v___x_4613_;
v_pos_4553_ = v_pos_4614_;
goto v___jp_4550_;
}
}
else
{
lean_object* v_pos_4615_; lean_object* v_err_4616_; 
v_pos_4615_ = lean_ctor_get(v___x_4610_, 0);
lean_inc(v_pos_4615_);
v_err_4616_ = lean_ctor_get(v___x_4610_, 1);
lean_inc(v_err_4616_);
lean_dec_ref_known(v___x_4610_, 2);
v_snd_4582_ = v_snd_4595_;
v_pos_4583_ = v_pos_4615_;
v_err_4584_ = v_err_4616_;
goto v___jp_4581_;
}
}
}
}
}
}
else
{
v___y_4587_ = v_pos_4593_;
v_snd_4588_ = v_snd_4595_;
goto v___jp_4586_;
}
}
}
v___jp_4621_:
{
lean_object* v___x_4625_; 
lean_inc_ref(v_pos_4623_);
v___x_4625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4625_, 0, v_pos_4623_);
lean_ctor_set(v___x_4625_, 1, v_err_4624_);
v_snd_4591_ = v_snd_4622_;
v___y_4592_ = v___x_4625_;
v_pos_4593_ = v_pos_4623_;
goto v___jp_4590_;
}
v___jp_4626_:
{
lean_object* v___x_4629_; 
v___x_4629_ = lean_box(0);
v_snd_4622_ = v_snd_4628_;
v_pos_4623_ = v___y_4627_;
v_err_4624_ = v___x_4629_;
goto v___jp_4621_;
}
v___jp_4631_:
{
lean_object* v_fst_4635_; lean_object* v_snd_4636_; uint8_t v_decide_4637_; 
v_fst_4635_ = lean_ctor_get(v_pos_4634_, 0);
v_snd_4636_ = lean_ctor_get(v_pos_4634_, 1);
lean_inc(v_snd_4636_);
v_decide_4637_ = lean_nat_dec_eq(v_snd_4632_, v_snd_4636_);
lean_dec(v_snd_4632_);
if (v_decide_4637_ == 0)
{
lean_dec(v_snd_4636_);
lean_dec_ref(v_pos_4634_);
return v___y_4633_;
}
else
{
lean_object* v___x_4638_; uint8_t v_decide_4639_; 
lean_dec_ref(v___y_4633_);
v___x_4638_ = lean_string_utf8_byte_size(v_fst_4635_);
v_decide_4639_ = lean_nat_dec_eq(v_snd_4636_, v___x_4638_);
if (v_decide_4639_ == 0)
{
if (v_decide_4637_ == 0)
{
v___y_4627_ = v_pos_4634_;
v_snd_4628_ = v_snd_4636_;
goto v___jp_4626_;
}
else
{
uint32_t v___x_4640_; uint32_t v_c_4641_; uint8_t v___x_4642_; 
v___x_4640_ = 78;
v_c_4641_ = lean_string_utf8_get_fast(v_fst_4635_, v_snd_4636_);
v___x_4642_ = lean_uint32_dec_eq(v_c_4641_, v___x_4640_);
if (v___x_4642_ == 0)
{
lean_object* v___x_4643_; 
v___x_4643_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1));
v_snd_4622_ = v_snd_4636_;
v_pos_4623_ = v_pos_4634_;
v_err_4624_ = v___x_4643_;
goto v___jp_4621_;
}
else
{
lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4658_; 
lean_inc(v_fst_4635_);
v_isSharedCheck_4658_ = !lean_is_exclusive(v_pos_4634_);
if (v_isSharedCheck_4658_ == 0)
{
lean_object* v_unused_4659_; lean_object* v_unused_4660_; 
v_unused_4659_ = lean_ctor_get(v_pos_4634_, 1);
lean_dec(v_unused_4659_);
v_unused_4660_ = lean_ctor_get(v_pos_4634_, 0);
lean_dec(v_unused_4660_);
v___x_4645_ = v_pos_4634_;
v_isShared_4646_ = v_isSharedCheck_4658_;
goto v_resetjp_4644_;
}
else
{
lean_dec(v_pos_4634_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4658_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4647_; lean_object* v_it_x27_4649_; 
v___x_4647_ = lean_string_utf8_next_fast(v_fst_4635_, v_snd_4636_);
if (v_isShared_4646_ == 0)
{
lean_ctor_set(v___x_4645_, 1, v___x_4647_);
v_it_x27_4649_ = v___x_4645_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_fst_4635_);
lean_ctor_set(v_reuseFailAlloc_4657_, 1, v___x_4647_);
v_it_x27_4649_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = ((lean_object*)(l_Std_Time_parseModifier___closed__14));
v___x_4651_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(v___x_4650_, v_it_x27_4649_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v_pos_4652_; lean_object* v_res_4653_; lean_object* v___x_4654_; 
lean_dec(v_snd_4636_);
v_pos_4652_ = lean_ctor_get(v___x_4651_, 0);
lean_inc(v_pos_4652_);
v_res_4653_ = lean_ctor_get(v___x_4651_, 1);
lean_inc(v_res_4653_);
lean_dec_ref_known(v___x_4651_, 2);
v___x_4654_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4630_, v_res_4653_, v_pos_4652_);
lean_dec(v_res_4653_);
return v___x_4654_;
}
else
{
lean_object* v_pos_4655_; lean_object* v_err_4656_; 
v_pos_4655_ = lean_ctor_get(v___x_4651_, 0);
lean_inc(v_pos_4655_);
v_err_4656_ = lean_ctor_get(v___x_4651_, 1);
lean_inc(v_err_4656_);
lean_dec_ref_known(v___x_4651_, 2);
v_snd_4622_ = v_snd_4636_;
v_pos_4623_ = v_pos_4655_;
v_err_4624_ = v_err_4656_;
goto v___jp_4621_;
}
}
}
}
}
}
else
{
v___y_4627_ = v_pos_4634_;
v_snd_4628_ = v_snd_4636_;
goto v___jp_4626_;
}
}
}
v___jp_4661_:
{
lean_object* v___x_4665_; 
lean_inc_ref(v_pos_4663_);
v___x_4665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4665_, 0, v_pos_4663_);
lean_ctor_set(v___x_4665_, 1, v_err_4664_);
v_snd_4632_ = v_snd_4662_;
v___y_4633_ = v___x_4665_;
v_pos_4634_ = v_pos_4663_;
goto v___jp_4631_;
}
v___jp_4666_:
{
lean_object* v___x_4669_; 
v___x_4669_ = lean_box(0);
v_snd_4662_ = v_snd_4668_;
v_pos_4663_ = v___y_4667_;
v_err_4664_ = v___x_4669_;
goto v___jp_4661_;
}
v___jp_4671_:
{
lean_object* v_fst_4675_; lean_object* v_snd_4676_; uint8_t v_decide_4677_; 
v_fst_4675_ = lean_ctor_get(v_pos_4674_, 0);
v_snd_4676_ = lean_ctor_get(v_pos_4674_, 1);
lean_inc(v_snd_4676_);
v_decide_4677_ = lean_nat_dec_eq(v_snd_4672_, v_snd_4676_);
lean_dec(v_snd_4672_);
if (v_decide_4677_ == 0)
{
lean_dec(v_snd_4676_);
lean_dec_ref(v_pos_4674_);
return v___y_4673_;
}
else
{
lean_object* v___x_4678_; uint8_t v_decide_4679_; 
lean_dec_ref(v___y_4673_);
v___x_4678_ = lean_string_utf8_byte_size(v_fst_4675_);
v_decide_4679_ = lean_nat_dec_eq(v_snd_4676_, v___x_4678_);
if (v_decide_4679_ == 0)
{
if (v_decide_4677_ == 0)
{
v___y_4667_ = v_pos_4674_;
v_snd_4668_ = v_snd_4676_;
goto v___jp_4666_;
}
else
{
uint32_t v___x_4680_; uint32_t v_c_4681_; uint8_t v___x_4682_; 
v___x_4680_ = 110;
v_c_4681_ = lean_string_utf8_get_fast(v_fst_4675_, v_snd_4676_);
v___x_4682_ = lean_uint32_dec_eq(v_c_4681_, v___x_4680_);
if (v___x_4682_ == 0)
{
lean_object* v___x_4683_; 
v___x_4683_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1));
v_snd_4662_ = v_snd_4676_;
v_pos_4663_ = v_pos_4674_;
v_err_4664_ = v___x_4683_;
goto v___jp_4661_;
}
else
{
lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4698_; 
lean_inc(v_fst_4675_);
v_isSharedCheck_4698_ = !lean_is_exclusive(v_pos_4674_);
if (v_isSharedCheck_4698_ == 0)
{
lean_object* v_unused_4699_; lean_object* v_unused_4700_; 
v_unused_4699_ = lean_ctor_get(v_pos_4674_, 1);
lean_dec(v_unused_4699_);
v_unused_4700_ = lean_ctor_get(v_pos_4674_, 0);
lean_dec(v_unused_4700_);
v___x_4685_ = v_pos_4674_;
v_isShared_4686_ = v_isSharedCheck_4698_;
goto v_resetjp_4684_;
}
else
{
lean_dec(v_pos_4674_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4698_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4687_; lean_object* v_it_x27_4689_; 
v___x_4687_ = lean_string_utf8_next_fast(v_fst_4675_, v_snd_4676_);
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 1, v___x_4687_);
v_it_x27_4689_ = v___x_4685_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_fst_4675_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v___x_4687_);
v_it_x27_4689_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4690_ = ((lean_object*)(l_Std_Time_parseModifier___closed__16));
v___x_4691_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(v___x_4690_, v_it_x27_4689_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_pos_4692_; lean_object* v_res_4693_; lean_object* v___x_4694_; 
lean_dec(v_snd_4676_);
v_pos_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_pos_4692_);
v_res_4693_ = lean_ctor_get(v___x_4691_, 1);
lean_inc(v_res_4693_);
lean_dec_ref_known(v___x_4691_, 2);
v___x_4694_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4670_, v_res_4693_, v_pos_4692_);
lean_dec(v_res_4693_);
return v___x_4694_;
}
else
{
lean_object* v_pos_4695_; lean_object* v_err_4696_; 
v_pos_4695_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_pos_4695_);
v_err_4696_ = lean_ctor_get(v___x_4691_, 1);
lean_inc(v_err_4696_);
lean_dec_ref_known(v___x_4691_, 2);
v_snd_4662_ = v_snd_4676_;
v_pos_4663_ = v_pos_4695_;
v_err_4664_ = v_err_4696_;
goto v___jp_4661_;
}
}
}
}
}
}
else
{
v___y_4667_ = v_pos_4674_;
v_snd_4668_ = v_snd_4676_;
goto v___jp_4666_;
}
}
}
v___jp_4701_:
{
lean_object* v___x_4705_; 
lean_inc_ref(v_pos_4703_);
v___x_4705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4705_, 0, v_pos_4703_);
lean_ctor_set(v___x_4705_, 1, v_err_4704_);
v_snd_4672_ = v_snd_4702_;
v___y_4673_ = v___x_4705_;
v_pos_4674_ = v_pos_4703_;
goto v___jp_4671_;
}
v___jp_4706_:
{
lean_object* v___x_4709_; 
v___x_4709_ = lean_box(0);
v_snd_4702_ = v_snd_4708_;
v_pos_4703_ = v___y_4707_;
v_err_4704_ = v___x_4709_;
goto v___jp_4701_;
}
v___jp_4711_:
{
lean_object* v_fst_4715_; lean_object* v_snd_4716_; uint8_t v_decide_4717_; 
v_fst_4715_ = lean_ctor_get(v_pos_4714_, 0);
v_snd_4716_ = lean_ctor_get(v_pos_4714_, 1);
lean_inc(v_snd_4716_);
v_decide_4717_ = lean_nat_dec_eq(v_snd_4712_, v_snd_4716_);
lean_dec(v_snd_4712_);
if (v_decide_4717_ == 0)
{
lean_dec(v_snd_4716_);
lean_dec_ref(v_pos_4714_);
return v___y_4713_;
}
else
{
lean_object* v___x_4718_; uint8_t v_decide_4719_; 
lean_dec_ref(v___y_4713_);
v___x_4718_ = lean_string_utf8_byte_size(v_fst_4715_);
v_decide_4719_ = lean_nat_dec_eq(v_snd_4716_, v___x_4718_);
if (v_decide_4719_ == 0)
{
if (v_decide_4717_ == 0)
{
v___y_4707_ = v_pos_4714_;
v_snd_4708_ = v_snd_4716_;
goto v___jp_4706_;
}
else
{
uint32_t v___x_4720_; uint32_t v_c_4721_; uint8_t v___x_4722_; 
v___x_4720_ = 65;
v_c_4721_ = lean_string_utf8_get_fast(v_fst_4715_, v_snd_4716_);
v___x_4722_ = lean_uint32_dec_eq(v_c_4721_, v___x_4720_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4723_; 
v___x_4723_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1));
v_snd_4702_ = v_snd_4716_;
v_pos_4703_ = v_pos_4714_;
v_err_4704_ = v___x_4723_;
goto v___jp_4701_;
}
else
{
lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4738_; 
lean_inc(v_fst_4715_);
v_isSharedCheck_4738_ = !lean_is_exclusive(v_pos_4714_);
if (v_isSharedCheck_4738_ == 0)
{
lean_object* v_unused_4739_; lean_object* v_unused_4740_; 
v_unused_4739_ = lean_ctor_get(v_pos_4714_, 1);
lean_dec(v_unused_4739_);
v_unused_4740_ = lean_ctor_get(v_pos_4714_, 0);
lean_dec(v_unused_4740_);
v___x_4725_ = v_pos_4714_;
v_isShared_4726_ = v_isSharedCheck_4738_;
goto v_resetjp_4724_;
}
else
{
lean_dec(v_pos_4714_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4738_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
lean_object* v___x_4727_; lean_object* v_it_x27_4729_; 
v___x_4727_ = lean_string_utf8_next_fast(v_fst_4715_, v_snd_4716_);
if (v_isShared_4726_ == 0)
{
lean_ctor_set(v___x_4725_, 1, v___x_4727_);
v_it_x27_4729_ = v___x_4725_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_fst_4715_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v___x_4727_);
v_it_x27_4729_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4730_ = ((lean_object*)(l_Std_Time_parseModifier___closed__18));
v___x_4731_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(v___x_4730_, v_it_x27_4729_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_pos_4732_; lean_object* v_res_4733_; lean_object* v___x_4734_; 
lean_dec(v_snd_4716_);
v_pos_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_pos_4732_);
v_res_4733_ = lean_ctor_get(v___x_4731_, 1);
lean_inc(v_res_4733_);
lean_dec_ref_known(v___x_4731_, 2);
v___x_4734_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4710_, v_res_4733_, v_pos_4732_);
lean_dec(v_res_4733_);
return v___x_4734_;
}
else
{
lean_object* v_pos_4735_; lean_object* v_err_4736_; 
v_pos_4735_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_pos_4735_);
v_err_4736_ = lean_ctor_get(v___x_4731_, 1);
lean_inc(v_err_4736_);
lean_dec_ref_known(v___x_4731_, 2);
v_snd_4702_ = v_snd_4716_;
v_pos_4703_ = v_pos_4735_;
v_err_4704_ = v_err_4736_;
goto v___jp_4701_;
}
}
}
}
}
}
else
{
v___y_4707_ = v_pos_4714_;
v_snd_4708_ = v_snd_4716_;
goto v___jp_4706_;
}
}
}
v___jp_4741_:
{
lean_object* v___x_4745_; 
lean_inc_ref(v_pos_4743_);
v___x_4745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4745_, 0, v_pos_4743_);
lean_ctor_set(v___x_4745_, 1, v_err_4744_);
v_snd_4712_ = v_snd_4742_;
v___y_4713_ = v___x_4745_;
v_pos_4714_ = v_pos_4743_;
goto v___jp_4711_;
}
v___jp_4746_:
{
lean_object* v___x_4749_; 
v___x_4749_ = lean_box(0);
v_snd_4742_ = v_snd_4748_;
v_pos_4743_ = v___y_4747_;
v_err_4744_ = v___x_4749_;
goto v___jp_4741_;
}
v___jp_4751_:
{
lean_object* v_fst_4755_; lean_object* v_snd_4756_; uint8_t v_decide_4757_; 
v_fst_4755_ = lean_ctor_get(v_pos_4754_, 0);
v_snd_4756_ = lean_ctor_get(v_pos_4754_, 1);
lean_inc(v_snd_4756_);
v_decide_4757_ = lean_nat_dec_eq(v_snd_4752_, v_snd_4756_);
lean_dec(v_snd_4752_);
if (v_decide_4757_ == 0)
{
lean_dec(v_snd_4756_);
lean_dec_ref(v_pos_4754_);
return v___y_4753_;
}
else
{
lean_object* v___x_4758_; uint8_t v_decide_4759_; 
lean_dec_ref(v___y_4753_);
v___x_4758_ = lean_string_utf8_byte_size(v_fst_4755_);
v_decide_4759_ = lean_nat_dec_eq(v_snd_4756_, v___x_4758_);
if (v_decide_4759_ == 0)
{
if (v_decide_4757_ == 0)
{
v___y_4747_ = v_pos_4754_;
v_snd_4748_ = v_snd_4756_;
goto v___jp_4746_;
}
else
{
uint32_t v___x_4760_; uint32_t v_c_4761_; uint8_t v___x_4762_; 
v___x_4760_ = 83;
v_c_4761_ = lean_string_utf8_get_fast(v_fst_4755_, v_snd_4756_);
v___x_4762_ = lean_uint32_dec_eq(v_c_4761_, v___x_4760_);
if (v___x_4762_ == 0)
{
lean_object* v___x_4763_; 
v___x_4763_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1));
v_snd_4742_ = v_snd_4756_;
v_pos_4743_ = v_pos_4754_;
v_err_4744_ = v___x_4763_;
goto v___jp_4741_;
}
else
{
lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4779_; 
lean_inc(v_fst_4755_);
v_isSharedCheck_4779_ = !lean_is_exclusive(v_pos_4754_);
if (v_isSharedCheck_4779_ == 0)
{
lean_object* v_unused_4780_; lean_object* v_unused_4781_; 
v_unused_4780_ = lean_ctor_get(v_pos_4754_, 1);
lean_dec(v_unused_4780_);
v_unused_4781_ = lean_ctor_get(v_pos_4754_, 0);
lean_dec(v_unused_4781_);
v___x_4765_ = v_pos_4754_;
v_isShared_4766_ = v_isSharedCheck_4779_;
goto v_resetjp_4764_;
}
else
{
lean_dec(v_pos_4754_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4779_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4767_; lean_object* v_it_x27_4769_; 
v___x_4767_ = lean_string_utf8_next_fast(v_fst_4755_, v_snd_4756_);
if (v_isShared_4766_ == 0)
{
lean_ctor_set(v___x_4765_, 1, v___x_4767_);
v_it_x27_4769_ = v___x_4765_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_fst_4755_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v___x_4767_);
v_it_x27_4769_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4770_ = ((lean_object*)(l_Std_Time_parseModifier___closed__20));
v___x_4771_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(v___x_4770_, v_it_x27_4769_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_pos_4772_; lean_object* v_res_4773_; lean_object* v___x_4774_; 
v_pos_4772_ = lean_ctor_get(v___x_4771_, 0);
lean_inc(v_pos_4772_);
v_res_4773_ = lean_ctor_get(v___x_4771_, 1);
lean_inc(v_res_4773_);
lean_dec_ref_known(v___x_4771_, 2);
v___x_4774_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(v___f_4750_, v_res_4773_, v_pos_4772_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_dec(v_snd_4756_);
return v___x_4774_;
}
else
{
lean_object* v_pos_4775_; 
v_pos_4775_ = lean_ctor_get(v___x_4774_, 0);
lean_inc(v_pos_4775_);
v_snd_4712_ = v_snd_4756_;
v___y_4713_ = v___x_4774_;
v_pos_4714_ = v_pos_4775_;
goto v___jp_4711_;
}
}
else
{
lean_object* v_pos_4776_; lean_object* v_err_4777_; 
v_pos_4776_ = lean_ctor_get(v___x_4771_, 0);
lean_inc(v_pos_4776_);
v_err_4777_ = lean_ctor_get(v___x_4771_, 1);
lean_inc(v_err_4777_);
lean_dec_ref_known(v___x_4771_, 2);
v_snd_4742_ = v_snd_4756_;
v_pos_4743_ = v_pos_4776_;
v_err_4744_ = v_err_4777_;
goto v___jp_4741_;
}
}
}
}
}
}
else
{
v___y_4747_ = v_pos_4754_;
v_snd_4748_ = v_snd_4756_;
goto v___jp_4746_;
}
}
}
v___jp_4782_:
{
lean_object* v___x_4786_; 
lean_inc_ref(v_pos_4784_);
v___x_4786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4786_, 0, v_pos_4784_);
lean_ctor_set(v___x_4786_, 1, v_err_4785_);
v_snd_4752_ = v_snd_4783_;
v___y_4753_ = v___x_4786_;
v_pos_4754_ = v_pos_4784_;
goto v___jp_4751_;
}
v___jp_4787_:
{
lean_object* v___x_4790_; 
v___x_4790_ = lean_box(0);
v_snd_4783_ = v_snd_4789_;
v_pos_4784_ = v___y_4788_;
v_err_4785_ = v___x_4790_;
goto v___jp_4782_;
}
v___jp_4792_:
{
lean_object* v_fst_4797_; lean_object* v_snd_4798_; uint8_t v_decide_4799_; 
v_fst_4797_ = lean_ctor_get(v_pos_4796_, 0);
v_snd_4798_ = lean_ctor_get(v_pos_4796_, 1);
lean_inc(v_snd_4798_);
v_decide_4799_ = lean_nat_dec_eq(v_snd_4794_, v_snd_4798_);
lean_dec(v_snd_4794_);
if (v_decide_4799_ == 0)
{
lean_dec(v_snd_4798_);
lean_dec_ref(v_pos_4796_);
lean_dec_ref(v___y_4793_);
return v___y_4795_;
}
else
{
lean_object* v___x_4800_; uint8_t v_decide_4801_; 
lean_dec_ref(v___y_4795_);
v___x_4800_ = lean_string_utf8_byte_size(v_fst_4797_);
v_decide_4801_ = lean_nat_dec_eq(v_snd_4798_, v___x_4800_);
if (v_decide_4801_ == 0)
{
if (v_decide_4799_ == 0)
{
lean_dec_ref(v___y_4793_);
v___y_4788_ = v_pos_4796_;
v_snd_4789_ = v_snd_4798_;
goto v___jp_4787_;
}
else
{
uint32_t v___x_4802_; uint32_t v_c_4803_; uint8_t v___x_4804_; 
v___x_4802_ = 115;
v_c_4803_ = lean_string_utf8_get_fast(v_fst_4797_, v_snd_4798_);
v___x_4804_ = lean_uint32_dec_eq(v_c_4803_, v___x_4802_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; 
lean_dec_ref(v___y_4793_);
v___x_4805_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1));
v_snd_4783_ = v_snd_4798_;
v_pos_4784_ = v_pos_4796_;
v_err_4785_ = v___x_4805_;
goto v___jp_4782_;
}
else
{
lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4821_; 
lean_inc(v_fst_4797_);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_pos_4796_);
if (v_isSharedCheck_4821_ == 0)
{
lean_object* v_unused_4822_; lean_object* v_unused_4823_; 
v_unused_4822_ = lean_ctor_get(v_pos_4796_, 1);
lean_dec(v_unused_4822_);
v_unused_4823_ = lean_ctor_get(v_pos_4796_, 0);
lean_dec(v_unused_4823_);
v___x_4807_ = v_pos_4796_;
v_isShared_4808_ = v_isSharedCheck_4821_;
goto v_resetjp_4806_;
}
else
{
lean_dec(v_pos_4796_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4821_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4809_; lean_object* v_it_x27_4811_; 
v___x_4809_ = lean_string_utf8_next_fast(v_fst_4797_, v_snd_4798_);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 1, v___x_4809_);
v_it_x27_4811_ = v___x_4807_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_fst_4797_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v___x_4809_);
v_it_x27_4811_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4812_ = ((lean_object*)(l_Std_Time_parseModifier___closed__22));
v___x_4813_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(v___x_4812_, v_it_x27_4811_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_pos_4814_; lean_object* v_res_4815_; lean_object* v___x_4816_; 
v_pos_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_pos_4814_);
v_res_4815_ = lean_ctor_get(v___x_4813_, 1);
lean_inc(v_res_4815_);
lean_dec_ref_known(v___x_4813_, 2);
v___x_4816_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4791_, v___y_4793_, v_res_4815_, v_pos_4814_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_dec(v_snd_4798_);
return v___x_4816_;
}
else
{
lean_object* v_pos_4817_; 
v_pos_4817_ = lean_ctor_get(v___x_4816_, 0);
lean_inc(v_pos_4817_);
v_snd_4752_ = v_snd_4798_;
v___y_4753_ = v___x_4816_;
v_pos_4754_ = v_pos_4817_;
goto v___jp_4751_;
}
}
else
{
lean_object* v_pos_4818_; lean_object* v_err_4819_; 
lean_dec_ref(v___y_4793_);
v_pos_4818_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_pos_4818_);
v_err_4819_ = lean_ctor_get(v___x_4813_, 1);
lean_inc(v_err_4819_);
lean_dec_ref_known(v___x_4813_, 2);
v_snd_4783_ = v_snd_4798_;
v_pos_4784_ = v_pos_4818_;
v_err_4785_ = v_err_4819_;
goto v___jp_4782_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_4793_);
v___y_4788_ = v_pos_4796_;
v_snd_4789_ = v_snd_4798_;
goto v___jp_4787_;
}
}
}
v___jp_4824_:
{
lean_object* v___x_4829_; 
lean_inc_ref(v_pos_4827_);
v___x_4829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4829_, 0, v_pos_4827_);
lean_ctor_set(v___x_4829_, 1, v_err_4828_);
v___y_4793_ = v___y_4825_;
v_snd_4794_ = v_snd_4826_;
v___y_4795_ = v___x_4829_;
v_pos_4796_ = v_pos_4827_;
goto v___jp_4792_;
}
v___jp_4830_:
{
lean_object* v___x_4834_; 
v___x_4834_ = lean_box(0);
v___y_4825_ = v___y_4831_;
v_snd_4826_ = v_snd_4833_;
v_pos_4827_ = v___y_4832_;
v_err_4828_ = v___x_4834_;
goto v___jp_4824_;
}
v___jp_4836_:
{
lean_object* v_fst_4841_; lean_object* v_snd_4842_; uint8_t v_decide_4843_; 
v_fst_4841_ = lean_ctor_get(v_pos_4840_, 0);
v_snd_4842_ = lean_ctor_get(v_pos_4840_, 1);
lean_inc(v_snd_4842_);
v_decide_4843_ = lean_nat_dec_eq(v_snd_4838_, v_snd_4842_);
lean_dec(v_snd_4838_);
if (v_decide_4843_ == 0)
{
lean_dec(v_snd_4842_);
lean_dec_ref(v_pos_4840_);
lean_dec_ref(v___y_4837_);
return v___y_4839_;
}
else
{
lean_object* v___x_4844_; uint8_t v_decide_4845_; 
lean_dec_ref(v___y_4839_);
v___x_4844_ = lean_string_utf8_byte_size(v_fst_4841_);
v_decide_4845_ = lean_nat_dec_eq(v_snd_4842_, v___x_4844_);
if (v_decide_4845_ == 0)
{
if (v_decide_4843_ == 0)
{
v___y_4831_ = v___y_4837_;
v___y_4832_ = v_pos_4840_;
v_snd_4833_ = v_snd_4842_;
goto v___jp_4830_;
}
else
{
uint32_t v___x_4846_; uint32_t v_c_4847_; uint8_t v___x_4848_; 
v___x_4846_ = 109;
v_c_4847_ = lean_string_utf8_get_fast(v_fst_4841_, v_snd_4842_);
v___x_4848_ = lean_uint32_dec_eq(v_c_4847_, v___x_4846_);
if (v___x_4848_ == 0)
{
lean_object* v___x_4849_; 
v___x_4849_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1));
v___y_4825_ = v___y_4837_;
v_snd_4826_ = v_snd_4842_;
v_pos_4827_ = v_pos_4840_;
v_err_4828_ = v___x_4849_;
goto v___jp_4824_;
}
else
{
lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4865_; 
lean_inc(v_fst_4841_);
v_isSharedCheck_4865_ = !lean_is_exclusive(v_pos_4840_);
if (v_isSharedCheck_4865_ == 0)
{
lean_object* v_unused_4866_; lean_object* v_unused_4867_; 
v_unused_4866_ = lean_ctor_get(v_pos_4840_, 1);
lean_dec(v_unused_4866_);
v_unused_4867_ = lean_ctor_get(v_pos_4840_, 0);
lean_dec(v_unused_4867_);
v___x_4851_ = v_pos_4840_;
v_isShared_4852_ = v_isSharedCheck_4865_;
goto v_resetjp_4850_;
}
else
{
lean_dec(v_pos_4840_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4865_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4853_; lean_object* v_it_x27_4855_; 
v___x_4853_ = lean_string_utf8_next_fast(v_fst_4841_, v_snd_4842_);
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 1, v___x_4853_);
v_it_x27_4855_ = v___x_4851_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_fst_4841_);
lean_ctor_set(v_reuseFailAlloc_4864_, 1, v___x_4853_);
v_it_x27_4855_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4856_ = ((lean_object*)(l_Std_Time_parseModifier___closed__24));
v___x_4857_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(v___x_4856_, v_it_x27_4855_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_pos_4858_; lean_object* v_res_4859_; lean_object* v___x_4860_; 
v_pos_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_pos_4858_);
v_res_4859_ = lean_ctor_get(v___x_4857_, 1);
lean_inc(v_res_4859_);
lean_dec_ref_known(v___x_4857_, 2);
lean_inc_ref(v___y_4837_);
v___x_4860_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4835_, v___y_4837_, v_res_4859_, v_pos_4858_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_dec(v_snd_4842_);
lean_dec_ref(v___y_4837_);
return v___x_4860_;
}
else
{
lean_object* v_pos_4861_; 
v_pos_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_pos_4861_);
v___y_4793_ = v___y_4837_;
v_snd_4794_ = v_snd_4842_;
v___y_4795_ = v___x_4860_;
v_pos_4796_ = v_pos_4861_;
goto v___jp_4792_;
}
}
else
{
lean_object* v_pos_4862_; lean_object* v_err_4863_; 
v_pos_4862_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_pos_4862_);
v_err_4863_ = lean_ctor_get(v___x_4857_, 1);
lean_inc(v_err_4863_);
lean_dec_ref_known(v___x_4857_, 2);
v___y_4825_ = v___y_4837_;
v_snd_4826_ = v_snd_4842_;
v_pos_4827_ = v_pos_4862_;
v_err_4828_ = v_err_4863_;
goto v___jp_4824_;
}
}
}
}
}
}
else
{
v___y_4831_ = v___y_4837_;
v___y_4832_ = v_pos_4840_;
v_snd_4833_ = v_snd_4842_;
goto v___jp_4830_;
}
}
}
v___jp_4868_:
{
lean_object* v___x_4873_; 
lean_inc_ref(v_pos_4871_);
v___x_4873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4873_, 0, v_pos_4871_);
lean_ctor_set(v___x_4873_, 1, v_err_4872_);
v___y_4837_ = v___y_4869_;
v_snd_4838_ = v_snd_4870_;
v___y_4839_ = v___x_4873_;
v_pos_4840_ = v_pos_4871_;
goto v___jp_4836_;
}
v___jp_4874_:
{
lean_object* v___x_4878_; 
v___x_4878_ = lean_box(0);
v___y_4869_ = v___y_4875_;
v_snd_4870_ = v_snd_4877_;
v_pos_4871_ = v___y_4876_;
v_err_4872_ = v___x_4878_;
goto v___jp_4868_;
}
v___jp_4880_:
{
lean_object* v_fst_4885_; lean_object* v_snd_4886_; uint8_t v_decide_4887_; 
v_fst_4885_ = lean_ctor_get(v_pos_4884_, 0);
v_snd_4886_ = lean_ctor_get(v_pos_4884_, 1);
lean_inc(v_snd_4886_);
v_decide_4887_ = lean_nat_dec_eq(v_snd_4881_, v_snd_4886_);
lean_dec(v_snd_4881_);
if (v_decide_4887_ == 0)
{
lean_dec(v_snd_4886_);
lean_dec_ref(v_pos_4884_);
lean_dec_ref(v___y_4882_);
return v___y_4883_;
}
else
{
lean_object* v___x_4888_; uint8_t v_decide_4889_; 
lean_dec_ref(v___y_4883_);
v___x_4888_ = lean_string_utf8_byte_size(v_fst_4885_);
v_decide_4889_ = lean_nat_dec_eq(v_snd_4886_, v___x_4888_);
if (v_decide_4889_ == 0)
{
if (v_decide_4887_ == 0)
{
v___y_4875_ = v___y_4882_;
v___y_4876_ = v_pos_4884_;
v_snd_4877_ = v_snd_4886_;
goto v___jp_4874_;
}
else
{
uint32_t v___x_4890_; uint32_t v_c_4891_; uint8_t v___x_4892_; 
v___x_4890_ = 72;
v_c_4891_ = lean_string_utf8_get_fast(v_fst_4885_, v_snd_4886_);
v___x_4892_ = lean_uint32_dec_eq(v_c_4891_, v___x_4890_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; 
v___x_4893_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1));
v___y_4869_ = v___y_4882_;
v_snd_4870_ = v_snd_4886_;
v_pos_4871_ = v_pos_4884_;
v_err_4872_ = v___x_4893_;
goto v___jp_4868_;
}
else
{
lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4909_; 
lean_inc(v_fst_4885_);
v_isSharedCheck_4909_ = !lean_is_exclusive(v_pos_4884_);
if (v_isSharedCheck_4909_ == 0)
{
lean_object* v_unused_4910_; lean_object* v_unused_4911_; 
v_unused_4910_ = lean_ctor_get(v_pos_4884_, 1);
lean_dec(v_unused_4910_);
v_unused_4911_ = lean_ctor_get(v_pos_4884_, 0);
lean_dec(v_unused_4911_);
v___x_4895_ = v_pos_4884_;
v_isShared_4896_ = v_isSharedCheck_4909_;
goto v_resetjp_4894_;
}
else
{
lean_dec(v_pos_4884_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4909_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4897_; lean_object* v_it_x27_4899_; 
v___x_4897_ = lean_string_utf8_next_fast(v_fst_4885_, v_snd_4886_);
if (v_isShared_4896_ == 0)
{
lean_ctor_set(v___x_4895_, 1, v___x_4897_);
v_it_x27_4899_ = v___x_4895_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_fst_4885_);
lean_ctor_set(v_reuseFailAlloc_4908_, 1, v___x_4897_);
v_it_x27_4899_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4900_ = ((lean_object*)(l_Std_Time_parseModifier___closed__26));
v___x_4901_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(v___x_4900_, v_it_x27_4899_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_pos_4902_; lean_object* v_res_4903_; lean_object* v___x_4904_; 
v_pos_4902_ = lean_ctor_get(v___x_4901_, 0);
lean_inc(v_pos_4902_);
v_res_4903_ = lean_ctor_get(v___x_4901_, 1);
lean_inc(v_res_4903_);
lean_dec_ref_known(v___x_4901_, 2);
lean_inc_ref(v___y_4882_);
v___x_4904_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4879_, v___y_4882_, v_res_4903_, v_pos_4902_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_dec(v_snd_4886_);
lean_dec_ref(v___y_4882_);
return v___x_4904_;
}
else
{
lean_object* v_pos_4905_; 
v_pos_4905_ = lean_ctor_get(v___x_4904_, 0);
lean_inc(v_pos_4905_);
v___y_4837_ = v___y_4882_;
v_snd_4838_ = v_snd_4886_;
v___y_4839_ = v___x_4904_;
v_pos_4840_ = v_pos_4905_;
goto v___jp_4836_;
}
}
else
{
lean_object* v_pos_4906_; lean_object* v_err_4907_; 
v_pos_4906_ = lean_ctor_get(v___x_4901_, 0);
lean_inc(v_pos_4906_);
v_err_4907_ = lean_ctor_get(v___x_4901_, 1);
lean_inc(v_err_4907_);
lean_dec_ref_known(v___x_4901_, 2);
v___y_4869_ = v___y_4882_;
v_snd_4870_ = v_snd_4886_;
v_pos_4871_ = v_pos_4906_;
v_err_4872_ = v_err_4907_;
goto v___jp_4868_;
}
}
}
}
}
}
else
{
v___y_4875_ = v___y_4882_;
v___y_4876_ = v_pos_4884_;
v_snd_4877_ = v_snd_4886_;
goto v___jp_4874_;
}
}
}
v___jp_4912_:
{
lean_object* v___x_4917_; 
lean_inc_ref(v_pos_4915_);
v___x_4917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4917_, 0, v_pos_4915_);
lean_ctor_set(v___x_4917_, 1, v_err_4916_);
v_snd_4881_ = v_snd_4913_;
v___y_4882_ = v___y_4914_;
v___y_4883_ = v___x_4917_;
v_pos_4884_ = v_pos_4915_;
goto v___jp_4880_;
}
v___jp_4918_:
{
lean_object* v___x_4922_; 
v___x_4922_ = lean_box(0);
v_snd_4913_ = v_snd_4920_;
v___y_4914_ = v___y_4921_;
v_pos_4915_ = v___y_4919_;
v_err_4916_ = v___x_4922_;
goto v___jp_4912_;
}
v___jp_4924_:
{
lean_object* v_fst_4929_; lean_object* v_snd_4930_; uint8_t v_decide_4931_; 
v_fst_4929_ = lean_ctor_get(v_pos_4928_, 0);
v_snd_4930_ = lean_ctor_get(v_pos_4928_, 1);
lean_inc(v_snd_4930_);
v_decide_4931_ = lean_nat_dec_eq(v_snd_4926_, v_snd_4930_);
lean_dec(v_snd_4926_);
if (v_decide_4931_ == 0)
{
lean_dec(v_snd_4930_);
lean_dec_ref(v_pos_4928_);
lean_dec_ref(v___y_4925_);
return v___y_4927_;
}
else
{
lean_object* v___x_4932_; uint8_t v_decide_4933_; 
lean_dec_ref(v___y_4927_);
v___x_4932_ = lean_string_utf8_byte_size(v_fst_4929_);
v_decide_4933_ = lean_nat_dec_eq(v_snd_4930_, v___x_4932_);
if (v_decide_4933_ == 0)
{
if (v_decide_4931_ == 0)
{
v___y_4919_ = v_pos_4928_;
v_snd_4920_ = v_snd_4930_;
v___y_4921_ = v___y_4925_;
goto v___jp_4918_;
}
else
{
uint32_t v___x_4934_; uint32_t v_c_4935_; uint8_t v___x_4936_; 
v___x_4934_ = 107;
v_c_4935_ = lean_string_utf8_get_fast(v_fst_4929_, v_snd_4930_);
v___x_4936_ = lean_uint32_dec_eq(v_c_4935_, v___x_4934_);
if (v___x_4936_ == 0)
{
lean_object* v___x_4937_; 
v___x_4937_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1));
v_snd_4913_ = v_snd_4930_;
v___y_4914_ = v___y_4925_;
v_pos_4915_ = v_pos_4928_;
v_err_4916_ = v___x_4937_;
goto v___jp_4912_;
}
else
{
lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4953_; 
lean_inc(v_fst_4929_);
v_isSharedCheck_4953_ = !lean_is_exclusive(v_pos_4928_);
if (v_isSharedCheck_4953_ == 0)
{
lean_object* v_unused_4954_; lean_object* v_unused_4955_; 
v_unused_4954_ = lean_ctor_get(v_pos_4928_, 1);
lean_dec(v_unused_4954_);
v_unused_4955_ = lean_ctor_get(v_pos_4928_, 0);
lean_dec(v_unused_4955_);
v___x_4939_ = v_pos_4928_;
v_isShared_4940_ = v_isSharedCheck_4953_;
goto v_resetjp_4938_;
}
else
{
lean_dec(v_pos_4928_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4953_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4941_; lean_object* v_it_x27_4943_; 
v___x_4941_ = lean_string_utf8_next_fast(v_fst_4929_, v_snd_4930_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___x_4941_);
v_it_x27_4943_ = v___x_4939_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_fst_4929_);
lean_ctor_set(v_reuseFailAlloc_4952_, 1, v___x_4941_);
v_it_x27_4943_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4944_ = ((lean_object*)(l_Std_Time_parseModifier___closed__28));
v___x_4945_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(v___x_4944_, v_it_x27_4943_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v_pos_4946_; lean_object* v_res_4947_; lean_object* v___x_4948_; 
v_pos_4946_ = lean_ctor_get(v___x_4945_, 0);
lean_inc(v_pos_4946_);
v_res_4947_ = lean_ctor_get(v___x_4945_, 1);
lean_inc(v_res_4947_);
lean_dec_ref_known(v___x_4945_, 2);
lean_inc_ref(v___y_4925_);
v___x_4948_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4923_, v___y_4925_, v_res_4947_, v_pos_4946_);
if (lean_obj_tag(v___x_4948_) == 0)
{
lean_dec(v_snd_4930_);
lean_dec_ref(v___y_4925_);
return v___x_4948_;
}
else
{
lean_object* v_pos_4949_; 
v_pos_4949_ = lean_ctor_get(v___x_4948_, 0);
lean_inc(v_pos_4949_);
v_snd_4881_ = v_snd_4930_;
v___y_4882_ = v___y_4925_;
v___y_4883_ = v___x_4948_;
v_pos_4884_ = v_pos_4949_;
goto v___jp_4880_;
}
}
else
{
lean_object* v_pos_4950_; lean_object* v_err_4951_; 
v_pos_4950_ = lean_ctor_get(v___x_4945_, 0);
lean_inc(v_pos_4950_);
v_err_4951_ = lean_ctor_get(v___x_4945_, 1);
lean_inc(v_err_4951_);
lean_dec_ref_known(v___x_4945_, 2);
v_snd_4913_ = v_snd_4930_;
v___y_4914_ = v___y_4925_;
v_pos_4915_ = v_pos_4950_;
v_err_4916_ = v_err_4951_;
goto v___jp_4912_;
}
}
}
}
}
}
else
{
v___y_4919_ = v_pos_4928_;
v_snd_4920_ = v_snd_4930_;
v___y_4921_ = v___y_4925_;
goto v___jp_4918_;
}
}
}
v___jp_4956_:
{
lean_object* v___x_4961_; 
lean_inc_ref(v_pos_4959_);
v___x_4961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4961_, 0, v_pos_4959_);
lean_ctor_set(v___x_4961_, 1, v_err_4960_);
v___y_4925_ = v___y_4957_;
v_snd_4926_ = v_snd_4958_;
v___y_4927_ = v___x_4961_;
v_pos_4928_ = v_pos_4959_;
goto v___jp_4924_;
}
v___jp_4962_:
{
lean_object* v___x_4966_; 
v___x_4966_ = lean_box(0);
v___y_4957_ = v___y_4963_;
v_snd_4958_ = v_snd_4965_;
v_pos_4959_ = v___y_4964_;
v_err_4960_ = v___x_4966_;
goto v___jp_4956_;
}
v___jp_4968_:
{
lean_object* v_fst_4973_; lean_object* v_snd_4974_; uint8_t v_decide_4975_; 
v_fst_4973_ = lean_ctor_get(v_pos_4972_, 0);
v_snd_4974_ = lean_ctor_get(v_pos_4972_, 1);
lean_inc(v_snd_4974_);
v_decide_4975_ = lean_nat_dec_eq(v_snd_4969_, v_snd_4974_);
lean_dec(v_snd_4969_);
if (v_decide_4975_ == 0)
{
lean_dec(v_snd_4974_);
lean_dec_ref(v_pos_4972_);
lean_dec_ref(v___y_4970_);
return v___y_4971_;
}
else
{
lean_object* v___x_4976_; uint8_t v_decide_4977_; 
lean_dec_ref(v___y_4971_);
v___x_4976_ = lean_string_utf8_byte_size(v_fst_4973_);
v_decide_4977_ = lean_nat_dec_eq(v_snd_4974_, v___x_4976_);
if (v_decide_4977_ == 0)
{
if (v_decide_4975_ == 0)
{
v___y_4963_ = v___y_4970_;
v___y_4964_ = v_pos_4972_;
v_snd_4965_ = v_snd_4974_;
goto v___jp_4962_;
}
else
{
uint32_t v___x_4978_; uint32_t v_c_4979_; uint8_t v___x_4980_; 
v___x_4978_ = 75;
v_c_4979_ = lean_string_utf8_get_fast(v_fst_4973_, v_snd_4974_);
v___x_4980_ = lean_uint32_dec_eq(v_c_4979_, v___x_4978_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; 
v___x_4981_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1));
v___y_4957_ = v___y_4970_;
v_snd_4958_ = v_snd_4974_;
v_pos_4959_ = v_pos_4972_;
v_err_4960_ = v___x_4981_;
goto v___jp_4956_;
}
else
{
lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4997_; 
lean_inc(v_fst_4973_);
v_isSharedCheck_4997_ = !lean_is_exclusive(v_pos_4972_);
if (v_isSharedCheck_4997_ == 0)
{
lean_object* v_unused_4998_; lean_object* v_unused_4999_; 
v_unused_4998_ = lean_ctor_get(v_pos_4972_, 1);
lean_dec(v_unused_4998_);
v_unused_4999_ = lean_ctor_get(v_pos_4972_, 0);
lean_dec(v_unused_4999_);
v___x_4983_ = v_pos_4972_;
v_isShared_4984_ = v_isSharedCheck_4997_;
goto v_resetjp_4982_;
}
else
{
lean_dec(v_pos_4972_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4997_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4985_; lean_object* v_it_x27_4987_; 
v___x_4985_ = lean_string_utf8_next_fast(v_fst_4973_, v_snd_4974_);
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 1, v___x_4985_);
v_it_x27_4987_ = v___x_4983_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_fst_4973_);
lean_ctor_set(v_reuseFailAlloc_4996_, 1, v___x_4985_);
v_it_x27_4987_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4988_ = ((lean_object*)(l_Std_Time_parseModifier___closed__30));
v___x_4989_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(v___x_4988_, v_it_x27_4987_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v_pos_4990_; lean_object* v_res_4991_; lean_object* v___x_4992_; 
v_pos_4990_ = lean_ctor_get(v___x_4989_, 0);
lean_inc(v_pos_4990_);
v_res_4991_ = lean_ctor_get(v___x_4989_, 1);
lean_inc(v_res_4991_);
lean_dec_ref_known(v___x_4989_, 2);
lean_inc_ref(v___y_4970_);
v___x_4992_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4967_, v___y_4970_, v_res_4991_, v_pos_4990_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_dec(v_snd_4974_);
lean_dec_ref(v___y_4970_);
return v___x_4992_;
}
else
{
lean_object* v_pos_4993_; 
v_pos_4993_ = lean_ctor_get(v___x_4992_, 0);
lean_inc(v_pos_4993_);
v___y_4925_ = v___y_4970_;
v_snd_4926_ = v_snd_4974_;
v___y_4927_ = v___x_4992_;
v_pos_4928_ = v_pos_4993_;
goto v___jp_4924_;
}
}
else
{
lean_object* v_pos_4994_; lean_object* v_err_4995_; 
v_pos_4994_ = lean_ctor_get(v___x_4989_, 0);
lean_inc(v_pos_4994_);
v_err_4995_ = lean_ctor_get(v___x_4989_, 1);
lean_inc(v_err_4995_);
lean_dec_ref_known(v___x_4989_, 2);
v___y_4957_ = v___y_4970_;
v_snd_4958_ = v_snd_4974_;
v_pos_4959_ = v_pos_4994_;
v_err_4960_ = v_err_4995_;
goto v___jp_4956_;
}
}
}
}
}
}
else
{
v___y_4963_ = v___y_4970_;
v___y_4964_ = v_pos_4972_;
v_snd_4965_ = v_snd_4974_;
goto v___jp_4962_;
}
}
}
v___jp_5000_:
{
lean_object* v___x_5005_; 
lean_inc_ref(v_pos_5003_);
v___x_5005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5005_, 0, v_pos_5003_);
lean_ctor_set(v___x_5005_, 1, v_err_5004_);
v_snd_4969_ = v_snd_5002_;
v___y_4970_ = v___y_5001_;
v___y_4971_ = v___x_5005_;
v_pos_4972_ = v_pos_5003_;
goto v___jp_4968_;
}
v___jp_5006_:
{
lean_object* v___x_5010_; 
v___x_5010_ = lean_box(0);
v___y_5001_ = v___y_5007_;
v_snd_5002_ = v_snd_5009_;
v_pos_5003_ = v___y_5008_;
v_err_5004_ = v___x_5010_;
goto v___jp_5000_;
}
v___jp_5012_:
{
lean_object* v_fst_5017_; lean_object* v_snd_5018_; uint8_t v_decide_5019_; 
v_fst_5017_ = lean_ctor_get(v_pos_5016_, 0);
v_snd_5018_ = lean_ctor_get(v_pos_5016_, 1);
lean_inc(v_snd_5018_);
v_decide_5019_ = lean_nat_dec_eq(v_snd_5013_, v_snd_5018_);
lean_dec(v_snd_5013_);
if (v_decide_5019_ == 0)
{
lean_dec(v_snd_5018_);
lean_dec_ref(v_pos_5016_);
lean_dec_ref(v___y_5014_);
return v___y_5015_;
}
else
{
lean_object* v___x_5020_; uint8_t v_decide_5021_; 
lean_dec_ref(v___y_5015_);
v___x_5020_ = lean_string_utf8_byte_size(v_fst_5017_);
v_decide_5021_ = lean_nat_dec_eq(v_snd_5018_, v___x_5020_);
if (v_decide_5021_ == 0)
{
if (v_decide_5019_ == 0)
{
v___y_5007_ = v___y_5014_;
v___y_5008_ = v_pos_5016_;
v_snd_5009_ = v_snd_5018_;
goto v___jp_5006_;
}
else
{
uint32_t v___x_5022_; uint32_t v_c_5023_; uint8_t v___x_5024_; 
v___x_5022_ = 104;
v_c_5023_ = lean_string_utf8_get_fast(v_fst_5017_, v_snd_5018_);
v___x_5024_ = lean_uint32_dec_eq(v_c_5023_, v___x_5022_);
if (v___x_5024_ == 0)
{
lean_object* v___x_5025_; 
v___x_5025_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1));
v___y_5001_ = v___y_5014_;
v_snd_5002_ = v_snd_5018_;
v_pos_5003_ = v_pos_5016_;
v_err_5004_ = v___x_5025_;
goto v___jp_5000_;
}
else
{
lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5041_; 
lean_inc(v_fst_5017_);
v_isSharedCheck_5041_ = !lean_is_exclusive(v_pos_5016_);
if (v_isSharedCheck_5041_ == 0)
{
lean_object* v_unused_5042_; lean_object* v_unused_5043_; 
v_unused_5042_ = lean_ctor_get(v_pos_5016_, 1);
lean_dec(v_unused_5042_);
v_unused_5043_ = lean_ctor_get(v_pos_5016_, 0);
lean_dec(v_unused_5043_);
v___x_5027_ = v_pos_5016_;
v_isShared_5028_ = v_isSharedCheck_5041_;
goto v_resetjp_5026_;
}
else
{
lean_dec(v_pos_5016_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5041_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5029_; lean_object* v_it_x27_5031_; 
v___x_5029_ = lean_string_utf8_next_fast(v_fst_5017_, v_snd_5018_);
if (v_isShared_5028_ == 0)
{
lean_ctor_set(v___x_5027_, 1, v___x_5029_);
v_it_x27_5031_ = v___x_5027_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_fst_5017_);
lean_ctor_set(v_reuseFailAlloc_5040_, 1, v___x_5029_);
v_it_x27_5031_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5032_ = ((lean_object*)(l_Std_Time_parseModifier___closed__32));
v___x_5033_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(v___x_5032_, v_it_x27_5031_);
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_object* v_pos_5034_; lean_object* v_res_5035_; lean_object* v___x_5036_; 
v_pos_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_pos_5034_);
v_res_5035_ = lean_ctor_get(v___x_5033_, 1);
lean_inc(v_res_5035_);
lean_dec_ref_known(v___x_5033_, 2);
lean_inc_ref(v___y_5014_);
v___x_5036_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5011_, v___y_5014_, v_res_5035_, v_pos_5034_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_dec(v_snd_5018_);
lean_dec_ref(v___y_5014_);
return v___x_5036_;
}
else
{
lean_object* v_pos_5037_; 
v_pos_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_pos_5037_);
v_snd_4969_ = v_snd_5018_;
v___y_4970_ = v___y_5014_;
v___y_4971_ = v___x_5036_;
v_pos_4972_ = v_pos_5037_;
goto v___jp_4968_;
}
}
else
{
lean_object* v_pos_5038_; lean_object* v_err_5039_; 
v_pos_5038_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_pos_5038_);
v_err_5039_ = lean_ctor_get(v___x_5033_, 1);
lean_inc(v_err_5039_);
lean_dec_ref_known(v___x_5033_, 2);
v___y_5001_ = v___y_5014_;
v_snd_5002_ = v_snd_5018_;
v_pos_5003_ = v_pos_5038_;
v_err_5004_ = v_err_5039_;
goto v___jp_5000_;
}
}
}
}
}
}
else
{
v___y_5007_ = v___y_5014_;
v___y_5008_ = v_pos_5016_;
v_snd_5009_ = v_snd_5018_;
goto v___jp_5006_;
}
}
}
v___jp_5044_:
{
lean_object* v___x_5049_; 
lean_inc_ref(v_pos_5047_);
v___x_5049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5049_, 0, v_pos_5047_);
lean_ctor_set(v___x_5049_, 1, v_err_5048_);
v_snd_5013_ = v_snd_5046_;
v___y_5014_ = v___y_5045_;
v___y_5015_ = v___x_5049_;
v_pos_5016_ = v_pos_5047_;
goto v___jp_5012_;
}
v___jp_5050_:
{
lean_object* v___x_5054_; 
v___x_5054_ = lean_box(0);
v___y_5045_ = v___y_5051_;
v_snd_5046_ = v_snd_5053_;
v_pos_5047_ = v___y_5052_;
v_err_5048_ = v___x_5054_;
goto v___jp_5044_;
}
v___jp_5055_:
{
lean_object* v_fst_5060_; lean_object* v_snd_5061_; uint8_t v_decide_5062_; 
v_fst_5060_ = lean_ctor_get(v_pos_5059_, 0);
v_snd_5061_ = lean_ctor_get(v_pos_5059_, 1);
lean_inc(v_snd_5061_);
v_decide_5062_ = lean_nat_dec_eq(v_snd_5057_, v_snd_5061_);
lean_dec(v_snd_5057_);
if (v_decide_5062_ == 0)
{
lean_dec(v_snd_5061_);
lean_dec_ref(v_pos_5059_);
lean_dec_ref(v___y_5056_);
return v___y_5058_;
}
else
{
lean_object* v___x_5063_; uint8_t v_decide_5064_; 
lean_dec_ref(v___y_5058_);
v___x_5063_ = lean_string_utf8_byte_size(v_fst_5060_);
v_decide_5064_ = lean_nat_dec_eq(v_snd_5061_, v___x_5063_);
if (v_decide_5064_ == 0)
{
if (v_decide_5062_ == 0)
{
v___y_5051_ = v___y_5056_;
v___y_5052_ = v_pos_5059_;
v_snd_5053_ = v_snd_5061_;
goto v___jp_5050_;
}
else
{
uint32_t v___x_5065_; uint32_t v_c_5066_; uint8_t v___x_5067_; 
v___x_5065_ = 66;
v_c_5066_ = lean_string_utf8_get_fast(v_fst_5060_, v_snd_5061_);
v___x_5067_ = lean_uint32_dec_eq(v_c_5066_, v___x_5065_);
if (v___x_5067_ == 0)
{
lean_object* v___x_5068_; 
v___x_5068_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1));
v___y_5045_ = v___y_5056_;
v_snd_5046_ = v_snd_5061_;
v_pos_5047_ = v_pos_5059_;
v_err_5048_ = v___x_5068_;
goto v___jp_5044_;
}
else
{
lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5084_; 
lean_inc(v_fst_5060_);
v_isSharedCheck_5084_ = !lean_is_exclusive(v_pos_5059_);
if (v_isSharedCheck_5084_ == 0)
{
lean_object* v_unused_5085_; lean_object* v_unused_5086_; 
v_unused_5085_ = lean_ctor_get(v_pos_5059_, 1);
lean_dec(v_unused_5085_);
v_unused_5086_ = lean_ctor_get(v_pos_5059_, 0);
lean_dec(v_unused_5086_);
v___x_5070_ = v_pos_5059_;
v_isShared_5071_ = v_isSharedCheck_5084_;
goto v_resetjp_5069_;
}
else
{
lean_dec(v_pos_5059_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5084_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5072_; lean_object* v_it_x27_5074_; 
v___x_5072_ = lean_string_utf8_next_fast(v_fst_5060_, v_snd_5061_);
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 1, v___x_5072_);
v_it_x27_5074_ = v___x_5070_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_fst_5060_);
lean_ctor_set(v_reuseFailAlloc_5083_, 1, v___x_5072_);
v_it_x27_5074_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5075_ = ((lean_object*)(l_Std_Time_parseModifier___closed__33));
v___x_5076_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(v___x_5075_, v_it_x27_5074_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_pos_5077_; lean_object* v_res_5078_; lean_object* v___x_5079_; 
v_pos_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_pos_5077_);
v_res_5078_ = lean_ctor_get(v___x_5076_, 1);
lean_inc(v_res_5078_);
lean_dec_ref_known(v___x_5076_, 2);
v___x_5079_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(v_res_5078_, v_pos_5077_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_dec(v_snd_5061_);
lean_dec_ref(v___y_5056_);
return v___x_5079_;
}
else
{
lean_object* v_pos_5080_; 
v_pos_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_pos_5080_);
v_snd_5013_ = v_snd_5061_;
v___y_5014_ = v___y_5056_;
v___y_5015_ = v___x_5079_;
v_pos_5016_ = v_pos_5080_;
goto v___jp_5012_;
}
}
else
{
lean_object* v_pos_5081_; lean_object* v_err_5082_; 
v_pos_5081_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_pos_5081_);
v_err_5082_ = lean_ctor_get(v___x_5076_, 1);
lean_inc(v_err_5082_);
lean_dec_ref_known(v___x_5076_, 2);
v___y_5045_ = v___y_5056_;
v_snd_5046_ = v_snd_5061_;
v_pos_5047_ = v_pos_5081_;
v_err_5048_ = v_err_5082_;
goto v___jp_5044_;
}
}
}
}
}
}
else
{
v___y_5051_ = v___y_5056_;
v___y_5052_ = v_pos_5059_;
v_snd_5053_ = v_snd_5061_;
goto v___jp_5050_;
}
}
}
v___jp_5087_:
{
lean_object* v___x_5092_; 
lean_inc_ref(v_pos_5090_);
v___x_5092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5092_, 0, v_pos_5090_);
lean_ctor_set(v___x_5092_, 1, v_err_5091_);
v___y_5056_ = v___y_5088_;
v_snd_5057_ = v_snd_5089_;
v___y_5058_ = v___x_5092_;
v_pos_5059_ = v_pos_5090_;
goto v___jp_5055_;
}
v___jp_5093_:
{
lean_object* v___x_5097_; 
v___x_5097_ = lean_box(0);
v___y_5088_ = v___y_5094_;
v_snd_5089_ = v_snd_5096_;
v_pos_5090_ = v___y_5095_;
v_err_5091_ = v___x_5097_;
goto v___jp_5087_;
}
v___jp_5098_:
{
lean_object* v_fst_5103_; lean_object* v_snd_5104_; uint8_t v_decide_5105_; 
v_fst_5103_ = lean_ctor_get(v_pos_5102_, 0);
v_snd_5104_ = lean_ctor_get(v_pos_5102_, 1);
lean_inc(v_snd_5104_);
v_decide_5105_ = lean_nat_dec_eq(v_snd_5100_, v_snd_5104_);
lean_dec(v_snd_5100_);
if (v_decide_5105_ == 0)
{
lean_dec(v_snd_5104_);
lean_dec_ref(v_pos_5102_);
lean_dec_ref(v___y_5099_);
return v___y_5101_;
}
else
{
lean_object* v___x_5106_; uint8_t v_decide_5107_; 
lean_dec_ref(v___y_5101_);
v___x_5106_ = lean_string_utf8_byte_size(v_fst_5103_);
v_decide_5107_ = lean_nat_dec_eq(v_snd_5104_, v___x_5106_);
if (v_decide_5107_ == 0)
{
if (v_decide_5105_ == 0)
{
v___y_5094_ = v___y_5099_;
v___y_5095_ = v_pos_5102_;
v_snd_5096_ = v_snd_5104_;
goto v___jp_5093_;
}
else
{
uint32_t v___x_5108_; uint32_t v_c_5109_; uint8_t v___x_5110_; 
v___x_5108_ = 98;
v_c_5109_ = lean_string_utf8_get_fast(v_fst_5103_, v_snd_5104_);
v___x_5110_ = lean_uint32_dec_eq(v_c_5109_, v___x_5108_);
if (v___x_5110_ == 0)
{
lean_object* v___x_5111_; 
v___x_5111_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1));
v___y_5088_ = v___y_5099_;
v_snd_5089_ = v_snd_5104_;
v_pos_5090_ = v_pos_5102_;
v_err_5091_ = v___x_5111_;
goto v___jp_5087_;
}
else
{
lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5127_; 
lean_inc(v_fst_5103_);
v_isSharedCheck_5127_ = !lean_is_exclusive(v_pos_5102_);
if (v_isSharedCheck_5127_ == 0)
{
lean_object* v_unused_5128_; lean_object* v_unused_5129_; 
v_unused_5128_ = lean_ctor_get(v_pos_5102_, 1);
lean_dec(v_unused_5128_);
v_unused_5129_ = lean_ctor_get(v_pos_5102_, 0);
lean_dec(v_unused_5129_);
v___x_5113_ = v_pos_5102_;
v_isShared_5114_ = v_isSharedCheck_5127_;
goto v_resetjp_5112_;
}
else
{
lean_dec(v_pos_5102_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5127_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5115_; lean_object* v_it_x27_5117_; 
v___x_5115_ = lean_string_utf8_next_fast(v_fst_5103_, v_snd_5104_);
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 1, v___x_5115_);
v_it_x27_5117_ = v___x_5113_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_fst_5103_);
lean_ctor_set(v_reuseFailAlloc_5126_, 1, v___x_5115_);
v_it_x27_5117_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
lean_object* v___x_5118_; lean_object* v___x_5119_; 
v___x_5118_ = ((lean_object*)(l_Std_Time_parseModifier___closed__34));
v___x_5119_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(v___x_5118_, v_it_x27_5117_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v_pos_5120_; lean_object* v_res_5121_; lean_object* v___x_5122_; 
v_pos_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_pos_5120_);
v_res_5121_ = lean_ctor_get(v___x_5119_, 1);
lean_inc(v_res_5121_);
lean_dec_ref_known(v___x_5119_, 2);
v___x_5122_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(v_res_5121_, v_pos_5120_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_dec(v_snd_5104_);
lean_dec_ref(v___y_5099_);
return v___x_5122_;
}
else
{
lean_object* v_pos_5123_; 
v_pos_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_pos_5123_);
v___y_5056_ = v___y_5099_;
v_snd_5057_ = v_snd_5104_;
v___y_5058_ = v___x_5122_;
v_pos_5059_ = v_pos_5123_;
goto v___jp_5055_;
}
}
else
{
lean_object* v_pos_5124_; lean_object* v_err_5125_; 
v_pos_5124_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_pos_5124_);
v_err_5125_ = lean_ctor_get(v___x_5119_, 1);
lean_inc(v_err_5125_);
lean_dec_ref_known(v___x_5119_, 2);
v___y_5088_ = v___y_5099_;
v_snd_5089_ = v_snd_5104_;
v_pos_5090_ = v_pos_5124_;
v_err_5091_ = v_err_5125_;
goto v___jp_5087_;
}
}
}
}
}
}
else
{
v___y_5094_ = v___y_5099_;
v___y_5095_ = v_pos_5102_;
v_snd_5096_ = v_snd_5104_;
goto v___jp_5093_;
}
}
}
v___jp_5130_:
{
lean_object* v___x_5135_; 
lean_inc_ref(v_pos_5133_);
v___x_5135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5135_, 0, v_pos_5133_);
lean_ctor_set(v___x_5135_, 1, v_err_5134_);
v___y_5099_ = v___y_5131_;
v_snd_5100_ = v_snd_5132_;
v___y_5101_ = v___x_5135_;
v_pos_5102_ = v_pos_5133_;
goto v___jp_5098_;
}
v___jp_5136_:
{
lean_object* v___x_5140_; 
v___x_5140_ = lean_box(0);
v___y_5131_ = v___y_5137_;
v_snd_5132_ = v_snd_5139_;
v_pos_5133_ = v___y_5138_;
v_err_5134_ = v___x_5140_;
goto v___jp_5130_;
}
v___jp_5141_:
{
lean_object* v_fst_5146_; lean_object* v_snd_5147_; uint8_t v_decide_5148_; 
v_fst_5146_ = lean_ctor_get(v_pos_5145_, 0);
v_snd_5147_ = lean_ctor_get(v_pos_5145_, 1);
lean_inc(v_snd_5147_);
v_decide_5148_ = lean_nat_dec_eq(v_snd_5143_, v_snd_5147_);
lean_dec(v_snd_5143_);
if (v_decide_5148_ == 0)
{
lean_dec(v_snd_5147_);
lean_dec_ref(v_pos_5145_);
lean_dec_ref(v___y_5142_);
return v___y_5144_;
}
else
{
lean_object* v___x_5149_; uint8_t v_decide_5150_; 
lean_dec_ref(v___y_5144_);
v___x_5149_ = lean_string_utf8_byte_size(v_fst_5146_);
v_decide_5150_ = lean_nat_dec_eq(v_snd_5147_, v___x_5149_);
if (v_decide_5150_ == 0)
{
if (v_decide_5148_ == 0)
{
v___y_5137_ = v___y_5142_;
v___y_5138_ = v_pos_5145_;
v_snd_5139_ = v_snd_5147_;
goto v___jp_5136_;
}
else
{
uint32_t v___x_5151_; uint32_t v_c_5152_; uint8_t v___x_5153_; 
v___x_5151_ = 97;
v_c_5152_ = lean_string_utf8_get_fast(v_fst_5146_, v_snd_5147_);
v___x_5153_ = lean_uint32_dec_eq(v_c_5152_, v___x_5151_);
if (v___x_5153_ == 0)
{
lean_object* v___x_5154_; 
v___x_5154_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1));
v___y_5131_ = v___y_5142_;
v_snd_5132_ = v_snd_5147_;
v_pos_5133_ = v_pos_5145_;
v_err_5134_ = v___x_5154_;
goto v___jp_5130_;
}
else
{
lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5170_; 
lean_inc(v_fst_5146_);
v_isSharedCheck_5170_ = !lean_is_exclusive(v_pos_5145_);
if (v_isSharedCheck_5170_ == 0)
{
lean_object* v_unused_5171_; lean_object* v_unused_5172_; 
v_unused_5171_ = lean_ctor_get(v_pos_5145_, 1);
lean_dec(v_unused_5171_);
v_unused_5172_ = lean_ctor_get(v_pos_5145_, 0);
lean_dec(v_unused_5172_);
v___x_5156_ = v_pos_5145_;
v_isShared_5157_ = v_isSharedCheck_5170_;
goto v_resetjp_5155_;
}
else
{
lean_dec(v_pos_5145_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5170_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v___x_5158_; lean_object* v_it_x27_5160_; 
v___x_5158_ = lean_string_utf8_next_fast(v_fst_5146_, v_snd_5147_);
if (v_isShared_5157_ == 0)
{
lean_ctor_set(v___x_5156_, 1, v___x_5158_);
v_it_x27_5160_ = v___x_5156_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_fst_5146_);
lean_ctor_set(v_reuseFailAlloc_5169_, 1, v___x_5158_);
v_it_x27_5160_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5161_ = ((lean_object*)(l_Std_Time_parseModifier___closed__35));
v___x_5162_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(v___x_5161_, v_it_x27_5160_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_pos_5163_; lean_object* v_res_5164_; lean_object* v___x_5165_; 
v_pos_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_pos_5163_);
v_res_5164_ = lean_ctor_get(v___x_5162_, 1);
lean_inc(v_res_5164_);
lean_dec_ref_known(v___x_5162_, 2);
v___x_5165_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(v_res_5164_, v_pos_5163_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_dec(v_snd_5147_);
lean_dec_ref(v___y_5142_);
return v___x_5165_;
}
else
{
lean_object* v_pos_5166_; 
v_pos_5166_ = lean_ctor_get(v___x_5165_, 0);
lean_inc(v_pos_5166_);
v___y_5099_ = v___y_5142_;
v_snd_5100_ = v_snd_5147_;
v___y_5101_ = v___x_5165_;
v_pos_5102_ = v_pos_5166_;
goto v___jp_5098_;
}
}
else
{
lean_object* v_pos_5167_; lean_object* v_err_5168_; 
v_pos_5167_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_pos_5167_);
v_err_5168_ = lean_ctor_get(v___x_5162_, 1);
lean_inc(v_err_5168_);
lean_dec_ref_known(v___x_5162_, 2);
v___y_5131_ = v___y_5142_;
v_snd_5132_ = v_snd_5147_;
v_pos_5133_ = v_pos_5167_;
v_err_5134_ = v_err_5168_;
goto v___jp_5130_;
}
}
}
}
}
}
else
{
v___y_5137_ = v___y_5142_;
v___y_5138_ = v_pos_5145_;
v_snd_5139_ = v_snd_5147_;
goto v___jp_5136_;
}
}
}
v___jp_5173_:
{
lean_object* v___x_5178_; 
lean_inc_ref(v_pos_5176_);
v___x_5178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5178_, 0, v_pos_5176_);
lean_ctor_set(v___x_5178_, 1, v_err_5177_);
v___y_5142_ = v___y_5174_;
v_snd_5143_ = v_snd_5175_;
v___y_5144_ = v___x_5178_;
v_pos_5145_ = v_pos_5176_;
goto v___jp_5141_;
}
v___jp_5179_:
{
lean_object* v___x_5183_; 
v___x_5183_ = lean_box(0);
v___y_5174_ = v___y_5180_;
v_snd_5175_ = v_snd_5182_;
v_pos_5176_ = v___y_5181_;
v_err_5177_ = v___x_5183_;
goto v___jp_5173_;
}
v___jp_5185_:
{
lean_object* v_fst_5191_; lean_object* v_snd_5192_; uint8_t v_decide_5193_; 
v_fst_5191_ = lean_ctor_get(v_pos_5190_, 0);
v_snd_5192_ = lean_ctor_get(v_pos_5190_, 1);
lean_inc(v_snd_5192_);
v_decide_5193_ = lean_nat_dec_eq(v_snd_5186_, v_snd_5192_);
lean_dec(v_snd_5186_);
if (v_decide_5193_ == 0)
{
lean_dec(v_snd_5192_);
lean_dec_ref(v_pos_5190_);
lean_dec_ref(v___y_5188_);
lean_dec_ref(v___y_5187_);
return v___y_5189_;
}
else
{
lean_object* v___x_5194_; uint8_t v_decide_5195_; 
lean_dec_ref(v___y_5189_);
v___x_5194_ = lean_string_utf8_byte_size(v_fst_5191_);
v_decide_5195_ = lean_nat_dec_eq(v_snd_5192_, v___x_5194_);
if (v_decide_5195_ == 0)
{
if (v_decide_5193_ == 0)
{
lean_dec_ref(v___y_5188_);
v___y_5180_ = v___y_5187_;
v___y_5181_ = v_pos_5190_;
v_snd_5182_ = v_snd_5192_;
goto v___jp_5179_;
}
else
{
uint32_t v___x_5196_; uint32_t v_c_5197_; uint8_t v___x_5198_; 
v___x_5196_ = 70;
v_c_5197_ = lean_string_utf8_get_fast(v_fst_5191_, v_snd_5192_);
v___x_5198_ = lean_uint32_dec_eq(v_c_5197_, v___x_5196_);
if (v___x_5198_ == 0)
{
lean_object* v___x_5199_; 
lean_dec_ref(v___y_5188_);
v___x_5199_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1));
v___y_5174_ = v___y_5187_;
v_snd_5175_ = v_snd_5192_;
v_pos_5176_ = v_pos_5190_;
v_err_5177_ = v___x_5199_;
goto v___jp_5173_;
}
else
{
lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5215_; 
lean_inc(v_fst_5191_);
v_isSharedCheck_5215_ = !lean_is_exclusive(v_pos_5190_);
if (v_isSharedCheck_5215_ == 0)
{
lean_object* v_unused_5216_; lean_object* v_unused_5217_; 
v_unused_5216_ = lean_ctor_get(v_pos_5190_, 1);
lean_dec(v_unused_5216_);
v_unused_5217_ = lean_ctor_get(v_pos_5190_, 0);
lean_dec(v_unused_5217_);
v___x_5201_ = v_pos_5190_;
v_isShared_5202_ = v_isSharedCheck_5215_;
goto v_resetjp_5200_;
}
else
{
lean_dec(v_pos_5190_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5215_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5203_; lean_object* v_it_x27_5205_; 
v___x_5203_ = lean_string_utf8_next_fast(v_fst_5191_, v_snd_5192_);
if (v_isShared_5202_ == 0)
{
lean_ctor_set(v___x_5201_, 1, v___x_5203_);
v_it_x27_5205_ = v___x_5201_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_fst_5191_);
lean_ctor_set(v_reuseFailAlloc_5214_, 1, v___x_5203_);
v_it_x27_5205_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
lean_object* v___x_5206_; lean_object* v___x_5207_; 
v___x_5206_ = ((lean_object*)(l_Std_Time_parseModifier___closed__37));
v___x_5207_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(v___x_5206_, v_it_x27_5205_);
if (lean_obj_tag(v___x_5207_) == 0)
{
lean_object* v_pos_5208_; lean_object* v_res_5209_; lean_object* v___x_5210_; 
v_pos_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_pos_5208_);
v_res_5209_ = lean_ctor_get(v___x_5207_, 1);
lean_inc(v_res_5209_);
lean_dec_ref_known(v___x_5207_, 2);
v___x_5210_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5184_, v___y_5188_, v_res_5209_, v_pos_5208_);
if (lean_obj_tag(v___x_5210_) == 0)
{
lean_dec(v_snd_5192_);
lean_dec_ref(v___y_5187_);
return v___x_5210_;
}
else
{
lean_object* v_pos_5211_; 
v_pos_5211_ = lean_ctor_get(v___x_5210_, 0);
lean_inc(v_pos_5211_);
v___y_5142_ = v___y_5187_;
v_snd_5143_ = v_snd_5192_;
v___y_5144_ = v___x_5210_;
v_pos_5145_ = v_pos_5211_;
goto v___jp_5141_;
}
}
else
{
lean_object* v_pos_5212_; lean_object* v_err_5213_; 
lean_dec_ref(v___y_5188_);
v_pos_5212_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_pos_5212_);
v_err_5213_ = lean_ctor_get(v___x_5207_, 1);
lean_inc(v_err_5213_);
lean_dec_ref_known(v___x_5207_, 2);
v___y_5174_ = v___y_5187_;
v_snd_5175_ = v_snd_5192_;
v_pos_5176_ = v_pos_5212_;
v_err_5177_ = v_err_5213_;
goto v___jp_5173_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_5188_);
v___y_5180_ = v___y_5187_;
v___y_5181_ = v_pos_5190_;
v_snd_5182_ = v_snd_5192_;
goto v___jp_5179_;
}
}
}
v___jp_5218_:
{
lean_object* v___x_5224_; 
lean_inc_ref(v_pos_5222_);
v___x_5224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5224_, 0, v_pos_5222_);
lean_ctor_set(v___x_5224_, 1, v_err_5223_);
v_snd_5186_ = v_snd_5219_;
v___y_5187_ = v___y_5220_;
v___y_5188_ = v___y_5221_;
v___y_5189_ = v___x_5224_;
v_pos_5190_ = v_pos_5222_;
goto v___jp_5185_;
}
v___jp_5225_:
{
lean_object* v___x_5230_; 
v___x_5230_ = lean_box(0);
v_snd_5219_ = v_snd_5227_;
v___y_5220_ = v___y_5228_;
v___y_5221_ = v___y_5229_;
v_pos_5222_ = v___y_5226_;
v_err_5223_ = v___x_5230_;
goto v___jp_5218_;
}
v___jp_5232_:
{
lean_object* v_fst_5238_; lean_object* v_snd_5239_; uint8_t v_decide_5240_; 
v_fst_5238_ = lean_ctor_get(v_pos_5237_, 0);
v_snd_5239_ = lean_ctor_get(v_pos_5237_, 1);
lean_inc(v_snd_5239_);
v_decide_5240_ = lean_nat_dec_eq(v_snd_5233_, v_snd_5239_);
lean_dec(v_snd_5233_);
if (v_decide_5240_ == 0)
{
lean_dec(v_snd_5239_);
lean_dec_ref(v_pos_5237_);
lean_dec_ref(v___y_5235_);
lean_dec_ref(v___y_5234_);
return v___y_5236_;
}
else
{
lean_object* v___x_5241_; uint8_t v_decide_5242_; 
lean_dec_ref(v___y_5236_);
v___x_5241_ = lean_string_utf8_byte_size(v_fst_5238_);
v_decide_5242_ = lean_nat_dec_eq(v_snd_5239_, v___x_5241_);
if (v_decide_5242_ == 0)
{
if (v_decide_5240_ == 0)
{
v___y_5226_ = v_pos_5237_;
v_snd_5227_ = v_snd_5239_;
v___y_5228_ = v___y_5234_;
v___y_5229_ = v___y_5235_;
goto v___jp_5225_;
}
else
{
uint32_t v___x_5243_; uint32_t v_c_5244_; uint8_t v___x_5245_; 
v___x_5243_ = 99;
v_c_5244_ = lean_string_utf8_get_fast(v_fst_5238_, v_snd_5239_);
v___x_5245_ = lean_uint32_dec_eq(v_c_5244_, v___x_5243_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; 
v___x_5246_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1));
v_snd_5219_ = v_snd_5239_;
v___y_5220_ = v___y_5234_;
v___y_5221_ = v___y_5235_;
v_pos_5222_ = v_pos_5237_;
v_err_5223_ = v___x_5246_;
goto v___jp_5218_;
}
else
{
lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5262_; 
lean_inc(v_fst_5238_);
v_isSharedCheck_5262_ = !lean_is_exclusive(v_pos_5237_);
if (v_isSharedCheck_5262_ == 0)
{
lean_object* v_unused_5263_; lean_object* v_unused_5264_; 
v_unused_5263_ = lean_ctor_get(v_pos_5237_, 1);
lean_dec(v_unused_5263_);
v_unused_5264_ = lean_ctor_get(v_pos_5237_, 0);
lean_dec(v_unused_5264_);
v___x_5248_ = v_pos_5237_;
v_isShared_5249_ = v_isSharedCheck_5262_;
goto v_resetjp_5247_;
}
else
{
lean_dec(v_pos_5237_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5262_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5250_; lean_object* v_it_x27_5252_; 
v___x_5250_ = lean_string_utf8_next_fast(v_fst_5238_, v_snd_5239_);
if (v_isShared_5249_ == 0)
{
lean_ctor_set(v___x_5248_, 1, v___x_5250_);
v_it_x27_5252_ = v___x_5248_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_fst_5238_);
lean_ctor_set(v_reuseFailAlloc_5261_, 1, v___x_5250_);
v_it_x27_5252_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
lean_object* v___x_5253_; lean_object* v___x_5254_; 
v___x_5253_ = ((lean_object*)(l_Std_Time_parseModifier___closed__39));
v___x_5254_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(v___x_5253_, v_it_x27_5252_);
if (lean_obj_tag(v___x_5254_) == 0)
{
lean_object* v_pos_5255_; lean_object* v_res_5256_; lean_object* v___x_5257_; 
v_pos_5255_ = lean_ctor_get(v___x_5254_, 0);
lean_inc(v_pos_5255_);
v_res_5256_ = lean_ctor_get(v___x_5254_, 1);
lean_inc(v_res_5256_);
lean_dec_ref_known(v___x_5254_, 2);
v___x_5257_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(v___f_5231_, v_res_5256_, v_pos_5255_);
if (lean_obj_tag(v___x_5257_) == 0)
{
lean_dec(v_snd_5239_);
lean_dec_ref(v___y_5235_);
lean_dec_ref(v___y_5234_);
return v___x_5257_;
}
else
{
lean_object* v_pos_5258_; 
v_pos_5258_ = lean_ctor_get(v___x_5257_, 0);
lean_inc(v_pos_5258_);
v_snd_5186_ = v_snd_5239_;
v___y_5187_ = v___y_5234_;
v___y_5188_ = v___y_5235_;
v___y_5189_ = v___x_5257_;
v_pos_5190_ = v_pos_5258_;
goto v___jp_5185_;
}
}
else
{
lean_object* v_pos_5259_; lean_object* v_err_5260_; 
v_pos_5259_ = lean_ctor_get(v___x_5254_, 0);
lean_inc(v_pos_5259_);
v_err_5260_ = lean_ctor_get(v___x_5254_, 1);
lean_inc(v_err_5260_);
lean_dec_ref_known(v___x_5254_, 2);
v_snd_5219_ = v_snd_5239_;
v___y_5220_ = v___y_5234_;
v___y_5221_ = v___y_5235_;
v_pos_5222_ = v_pos_5259_;
v_err_5223_ = v_err_5260_;
goto v___jp_5218_;
}
}
}
}
}
}
else
{
v___y_5226_ = v_pos_5237_;
v_snd_5227_ = v_snd_5239_;
v___y_5228_ = v___y_5234_;
v___y_5229_ = v___y_5235_;
goto v___jp_5225_;
}
}
}
v___jp_5265_:
{
lean_object* v___x_5271_; 
lean_inc_ref(v_pos_5269_);
v___x_5271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5271_, 0, v_pos_5269_);
lean_ctor_set(v___x_5271_, 1, v_err_5270_);
v_snd_5233_ = v_snd_5267_;
v___y_5234_ = v___y_5266_;
v___y_5235_ = v___y_5268_;
v___y_5236_ = v___x_5271_;
v_pos_5237_ = v_pos_5269_;
goto v___jp_5232_;
}
v___jp_5272_:
{
lean_object* v___x_5277_; 
v___x_5277_ = lean_box(0);
v___y_5266_ = v___y_5273_;
v_snd_5267_ = v_snd_5275_;
v___y_5268_ = v___y_5276_;
v_pos_5269_ = v___y_5274_;
v_err_5270_ = v___x_5277_;
goto v___jp_5265_;
}
v___jp_5279_:
{
lean_object* v_fst_5285_; lean_object* v_snd_5286_; uint8_t v_decide_5287_; 
v_fst_5285_ = lean_ctor_get(v_pos_5284_, 0);
v_snd_5286_ = lean_ctor_get(v_pos_5284_, 1);
lean_inc(v_snd_5286_);
v_decide_5287_ = lean_nat_dec_eq(v_snd_5281_, v_snd_5286_);
lean_dec(v_snd_5281_);
if (v_decide_5287_ == 0)
{
lean_dec(v_snd_5286_);
lean_dec_ref(v_pos_5284_);
lean_dec_ref(v___y_5282_);
lean_dec_ref(v___y_5280_);
return v___y_5283_;
}
else
{
lean_object* v___x_5288_; uint8_t v_decide_5289_; 
lean_dec_ref(v___y_5283_);
v___x_5288_ = lean_string_utf8_byte_size(v_fst_5285_);
v_decide_5289_ = lean_nat_dec_eq(v_snd_5286_, v___x_5288_);
if (v_decide_5289_ == 0)
{
if (v_decide_5287_ == 0)
{
v___y_5273_ = v___y_5280_;
v___y_5274_ = v_pos_5284_;
v_snd_5275_ = v_snd_5286_;
v___y_5276_ = v___y_5282_;
goto v___jp_5272_;
}
else
{
uint32_t v___x_5290_; uint32_t v_c_5291_; uint8_t v___x_5292_; 
v___x_5290_ = 101;
v_c_5291_ = lean_string_utf8_get_fast(v_fst_5285_, v_snd_5286_);
v___x_5292_ = lean_uint32_dec_eq(v_c_5291_, v___x_5290_);
if (v___x_5292_ == 0)
{
lean_object* v___x_5293_; 
v___x_5293_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1));
v___y_5266_ = v___y_5280_;
v_snd_5267_ = v_snd_5286_;
v___y_5268_ = v___y_5282_;
v_pos_5269_ = v_pos_5284_;
v_err_5270_ = v___x_5293_;
goto v___jp_5265_;
}
else
{
lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5309_; 
lean_inc(v_fst_5285_);
v_isSharedCheck_5309_ = !lean_is_exclusive(v_pos_5284_);
if (v_isSharedCheck_5309_ == 0)
{
lean_object* v_unused_5310_; lean_object* v_unused_5311_; 
v_unused_5310_ = lean_ctor_get(v_pos_5284_, 1);
lean_dec(v_unused_5310_);
v_unused_5311_ = lean_ctor_get(v_pos_5284_, 0);
lean_dec(v_unused_5311_);
v___x_5295_ = v_pos_5284_;
v_isShared_5296_ = v_isSharedCheck_5309_;
goto v_resetjp_5294_;
}
else
{
lean_dec(v_pos_5284_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5309_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5297_; lean_object* v_it_x27_5299_; 
v___x_5297_ = lean_string_utf8_next_fast(v_fst_5285_, v_snd_5286_);
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 1, v___x_5297_);
v_it_x27_5299_ = v___x_5295_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_fst_5285_);
lean_ctor_set(v_reuseFailAlloc_5308_, 1, v___x_5297_);
v_it_x27_5299_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5300_ = ((lean_object*)(l_Std_Time_parseModifier___closed__41));
v___x_5301_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(v___x_5300_, v_it_x27_5299_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v_pos_5302_; lean_object* v_res_5303_; lean_object* v___x_5304_; 
v_pos_5302_ = lean_ctor_get(v___x_5301_, 0);
lean_inc(v_pos_5302_);
v_res_5303_ = lean_ctor_get(v___x_5301_, 1);
lean_inc(v_res_5303_);
lean_dec_ref_known(v___x_5301_, 2);
v___x_5304_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(v___f_5278_, v_res_5303_, v_pos_5302_);
if (lean_obj_tag(v___x_5304_) == 0)
{
lean_dec(v_snd_5286_);
lean_dec_ref(v___y_5282_);
lean_dec_ref(v___y_5280_);
return v___x_5304_;
}
else
{
lean_object* v_pos_5305_; 
v_pos_5305_ = lean_ctor_get(v___x_5304_, 0);
lean_inc(v_pos_5305_);
v_snd_5233_ = v_snd_5286_;
v___y_5234_ = v___y_5280_;
v___y_5235_ = v___y_5282_;
v___y_5236_ = v___x_5304_;
v_pos_5237_ = v_pos_5305_;
goto v___jp_5232_;
}
}
else
{
lean_object* v_pos_5306_; lean_object* v_err_5307_; 
v_pos_5306_ = lean_ctor_get(v___x_5301_, 0);
lean_inc(v_pos_5306_);
v_err_5307_ = lean_ctor_get(v___x_5301_, 1);
lean_inc(v_err_5307_);
lean_dec_ref_known(v___x_5301_, 2);
v___y_5266_ = v___y_5280_;
v_snd_5267_ = v_snd_5286_;
v___y_5268_ = v___y_5282_;
v_pos_5269_ = v_pos_5306_;
v_err_5270_ = v_err_5307_;
goto v___jp_5265_;
}
}
}
}
}
}
else
{
v___y_5273_ = v___y_5280_;
v___y_5274_ = v_pos_5284_;
v_snd_5275_ = v_snd_5286_;
v___y_5276_ = v___y_5282_;
goto v___jp_5272_;
}
}
}
v___jp_5312_:
{
lean_object* v___x_5318_; 
lean_inc_ref(v_pos_5316_);
v___x_5318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5318_, 0, v_pos_5316_);
lean_ctor_set(v___x_5318_, 1, v_err_5317_);
v___y_5280_ = v___y_5313_;
v_snd_5281_ = v_snd_5314_;
v___y_5282_ = v___y_5315_;
v___y_5283_ = v___x_5318_;
v_pos_5284_ = v_pos_5316_;
goto v___jp_5279_;
}
v___jp_5319_:
{
lean_object* v___x_5324_; 
v___x_5324_ = lean_box(0);
v___y_5313_ = v___y_5320_;
v_snd_5314_ = v_snd_5322_;
v___y_5315_ = v___y_5323_;
v_pos_5316_ = v___y_5321_;
v_err_5317_ = v___x_5324_;
goto v___jp_5312_;
}
v___jp_5326_:
{
lean_object* v_fst_5332_; lean_object* v_snd_5333_; uint8_t v_decide_5334_; 
v_fst_5332_ = lean_ctor_get(v_pos_5331_, 0);
v_snd_5333_ = lean_ctor_get(v_pos_5331_, 1);
lean_inc(v_snd_5333_);
v_decide_5334_ = lean_nat_dec_eq(v___y_5327_, v_snd_5333_);
lean_dec(v___y_5327_);
if (v_decide_5334_ == 0)
{
lean_dec(v_snd_5333_);
lean_dec_ref(v_pos_5331_);
lean_dec_ref(v___y_5329_);
lean_dec_ref(v___y_5328_);
return v___y_5330_;
}
else
{
lean_object* v___x_5335_; uint8_t v_decide_5336_; 
lean_dec_ref(v___y_5330_);
v___x_5335_ = lean_string_utf8_byte_size(v_fst_5332_);
v_decide_5336_ = lean_nat_dec_eq(v_snd_5333_, v___x_5335_);
if (v_decide_5336_ == 0)
{
if (v_decide_5334_ == 0)
{
v___y_5320_ = v___y_5328_;
v___y_5321_ = v_pos_5331_;
v_snd_5322_ = v_snd_5333_;
v___y_5323_ = v___y_5329_;
goto v___jp_5319_;
}
else
{
uint32_t v___x_5337_; uint32_t v_c_5338_; uint8_t v___x_5339_; 
v___x_5337_ = 69;
v_c_5338_ = lean_string_utf8_get_fast(v_fst_5332_, v_snd_5333_);
v___x_5339_ = lean_uint32_dec_eq(v_c_5338_, v___x_5337_);
if (v___x_5339_ == 0)
{
lean_object* v___x_5340_; 
v___x_5340_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1));
v___y_5313_ = v___y_5328_;
v_snd_5314_ = v_snd_5333_;
v___y_5315_ = v___y_5329_;
v_pos_5316_ = v_pos_5331_;
v_err_5317_ = v___x_5340_;
goto v___jp_5312_;
}
else
{
lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5356_; 
lean_inc(v_fst_5332_);
v_isSharedCheck_5356_ = !lean_is_exclusive(v_pos_5331_);
if (v_isSharedCheck_5356_ == 0)
{
lean_object* v_unused_5357_; lean_object* v_unused_5358_; 
v_unused_5357_ = lean_ctor_get(v_pos_5331_, 1);
lean_dec(v_unused_5357_);
v_unused_5358_ = lean_ctor_get(v_pos_5331_, 0);
lean_dec(v_unused_5358_);
v___x_5342_ = v_pos_5331_;
v_isShared_5343_ = v_isSharedCheck_5356_;
goto v_resetjp_5341_;
}
else
{
lean_dec(v_pos_5331_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5356_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5344_; lean_object* v_it_x27_5346_; 
v___x_5344_ = lean_string_utf8_next_fast(v_fst_5332_, v_snd_5333_);
if (v_isShared_5343_ == 0)
{
lean_ctor_set(v___x_5342_, 1, v___x_5344_);
v_it_x27_5346_ = v___x_5342_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_fst_5332_);
lean_ctor_set(v_reuseFailAlloc_5355_, 1, v___x_5344_);
v_it_x27_5346_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5347_ = ((lean_object*)(l_Std_Time_parseModifier___closed__43));
v___x_5348_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(v___x_5347_, v_it_x27_5346_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_pos_5349_; lean_object* v_res_5350_; lean_object* v___x_5351_; 
v_pos_5349_ = lean_ctor_get(v___x_5348_, 0);
lean_inc(v_pos_5349_);
v_res_5350_ = lean_ctor_get(v___x_5348_, 1);
lean_inc(v_res_5350_);
lean_dec_ref_known(v___x_5348_, 2);
v___x_5351_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(v___f_5325_, v_res_5350_, v_pos_5349_);
if (lean_obj_tag(v___x_5351_) == 0)
{
lean_dec(v_snd_5333_);
lean_dec_ref(v___y_5329_);
lean_dec_ref(v___y_5328_);
return v___x_5351_;
}
else
{
lean_object* v_pos_5352_; 
v_pos_5352_ = lean_ctor_get(v___x_5351_, 0);
lean_inc(v_pos_5352_);
v___y_5280_ = v___y_5328_;
v_snd_5281_ = v_snd_5333_;
v___y_5282_ = v___y_5329_;
v___y_5283_ = v___x_5351_;
v_pos_5284_ = v_pos_5352_;
goto v___jp_5279_;
}
}
else
{
lean_object* v_pos_5353_; lean_object* v_err_5354_; 
v_pos_5353_ = lean_ctor_get(v___x_5348_, 0);
lean_inc(v_pos_5353_);
v_err_5354_ = lean_ctor_get(v___x_5348_, 1);
lean_inc(v_err_5354_);
lean_dec_ref_known(v___x_5348_, 2);
v___y_5313_ = v___y_5328_;
v_snd_5314_ = v_snd_5333_;
v___y_5315_ = v___y_5329_;
v_pos_5316_ = v_pos_5353_;
v_err_5317_ = v_err_5354_;
goto v___jp_5312_;
}
}
}
}
}
}
else
{
v___y_5320_ = v___y_5328_;
v___y_5321_ = v_pos_5331_;
v_snd_5322_ = v_snd_5333_;
v___y_5323_ = v___y_5329_;
goto v___jp_5319_;
}
}
}
v___jp_5359_:
{
lean_object* v___x_5365_; 
lean_inc_ref(v_pos_5363_);
v___x_5365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5365_, 0, v_pos_5363_);
lean_ctor_set(v___x_5365_, 1, v_err_5364_);
v___y_5327_ = v___y_5360_;
v___y_5328_ = v___y_5361_;
v___y_5329_ = v___y_5362_;
v___y_5330_ = v___x_5365_;
v_pos_5331_ = v_pos_5363_;
goto v___jp_5326_;
}
v___jp_5366_:
{
lean_object* v___x_5371_; 
v___x_5371_ = lean_box(0);
v___y_5360_ = v___y_5367_;
v___y_5361_ = v___y_5368_;
v___y_5362_ = v___y_5369_;
v_pos_5363_ = v___y_5370_;
v_err_5364_ = v___x_5371_;
goto v___jp_5359_;
}
v___jp_5373_:
{
lean_object* v_fst_5378_; lean_object* v_snd_5379_; uint8_t v_decide_5380_; 
v_fst_5378_ = lean_ctor_get(v_pos_5377_, 0);
v_snd_5379_ = lean_ctor_get(v_pos_5377_, 1);
lean_inc(v_snd_5379_);
v_decide_5380_ = lean_nat_dec_eq(v_snd_5374_, v_snd_5379_);
lean_dec(v_snd_5374_);
if (v_decide_5380_ == 0)
{
lean_dec(v_snd_5379_);
lean_dec_ref(v_pos_5377_);
lean_dec_ref(v___y_5375_);
return v___y_5376_;
}
else
{
lean_object* v___x_5381_; lean_object* v___x_5382_; uint8_t v_decide_5383_; 
lean_dec_ref(v___y_5376_);
v___x_5381_ = ((lean_object*)(l_Std_Time_parseModifier___closed__45));
v___x_5382_ = lean_string_utf8_byte_size(v_fst_5378_);
v_decide_5383_ = lean_nat_dec_eq(v_snd_5379_, v___x_5382_);
if (v_decide_5383_ == 0)
{
if (v_decide_5380_ == 0)
{
v___y_5367_ = v_snd_5379_;
v___y_5368_ = v___y_5375_;
v___y_5369_ = v___x_5381_;
v___y_5370_ = v_pos_5377_;
goto v___jp_5366_;
}
else
{
uint32_t v___x_5384_; uint32_t v_c_5385_; uint8_t v___x_5386_; 
v___x_5384_ = 87;
v_c_5385_ = lean_string_utf8_get_fast(v_fst_5378_, v_snd_5379_);
v___x_5386_ = lean_uint32_dec_eq(v_c_5385_, v___x_5384_);
if (v___x_5386_ == 0)
{
lean_object* v___x_5387_; 
v___x_5387_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1));
v___y_5360_ = v_snd_5379_;
v___y_5361_ = v___y_5375_;
v___y_5362_ = v___x_5381_;
v_pos_5363_ = v_pos_5377_;
v_err_5364_ = v___x_5387_;
goto v___jp_5359_;
}
else
{
lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5403_; 
lean_inc(v_fst_5378_);
v_isSharedCheck_5403_ = !lean_is_exclusive(v_pos_5377_);
if (v_isSharedCheck_5403_ == 0)
{
lean_object* v_unused_5404_; lean_object* v_unused_5405_; 
v_unused_5404_ = lean_ctor_get(v_pos_5377_, 1);
lean_dec(v_unused_5404_);
v_unused_5405_ = lean_ctor_get(v_pos_5377_, 0);
lean_dec(v_unused_5405_);
v___x_5389_ = v_pos_5377_;
v_isShared_5390_ = v_isSharedCheck_5403_;
goto v_resetjp_5388_;
}
else
{
lean_dec(v_pos_5377_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5403_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v___x_5391_; lean_object* v_it_x27_5393_; 
v___x_5391_ = lean_string_utf8_next_fast(v_fst_5378_, v_snd_5379_);
if (v_isShared_5390_ == 0)
{
lean_ctor_set(v___x_5389_, 1, v___x_5391_);
v_it_x27_5393_ = v___x_5389_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_fst_5378_);
lean_ctor_set(v_reuseFailAlloc_5402_, 1, v___x_5391_);
v_it_x27_5393_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___x_5394_ = ((lean_object*)(l_Std_Time_parseModifier___closed__46));
v___x_5395_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(v___x_5394_, v_it_x27_5393_);
if (lean_obj_tag(v___x_5395_) == 0)
{
lean_object* v_pos_5396_; lean_object* v_res_5397_; lean_object* v___x_5398_; 
v_pos_5396_ = lean_ctor_get(v___x_5395_, 0);
lean_inc(v_pos_5396_);
v_res_5397_ = lean_ctor_get(v___x_5395_, 1);
lean_inc(v_res_5397_);
lean_dec_ref_known(v___x_5395_, 2);
v___x_5398_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5372_, v___x_5381_, v_res_5397_, v_pos_5396_);
if (lean_obj_tag(v___x_5398_) == 0)
{
lean_dec(v_snd_5379_);
lean_dec_ref(v___y_5375_);
return v___x_5398_;
}
else
{
lean_object* v_pos_5399_; 
v_pos_5399_ = lean_ctor_get(v___x_5398_, 0);
lean_inc(v_pos_5399_);
v___y_5327_ = v_snd_5379_;
v___y_5328_ = v___y_5375_;
v___y_5329_ = v___x_5381_;
v___y_5330_ = v___x_5398_;
v_pos_5331_ = v_pos_5399_;
goto v___jp_5326_;
}
}
else
{
lean_object* v_pos_5400_; lean_object* v_err_5401_; 
v_pos_5400_ = lean_ctor_get(v___x_5395_, 0);
lean_inc(v_pos_5400_);
v_err_5401_ = lean_ctor_get(v___x_5395_, 1);
lean_inc(v_err_5401_);
lean_dec_ref_known(v___x_5395_, 2);
v___y_5360_ = v_snd_5379_;
v___y_5361_ = v___y_5375_;
v___y_5362_ = v___x_5381_;
v_pos_5363_ = v_pos_5400_;
v_err_5364_ = v_err_5401_;
goto v___jp_5359_;
}
}
}
}
}
}
else
{
v___y_5367_ = v_snd_5379_;
v___y_5368_ = v___y_5375_;
v___y_5369_ = v___x_5381_;
v___y_5370_ = v_pos_5377_;
goto v___jp_5366_;
}
}
}
v___jp_5406_:
{
lean_object* v___x_5411_; 
lean_inc_ref(v_pos_5409_);
v___x_5411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5411_, 0, v_pos_5409_);
lean_ctor_set(v___x_5411_, 1, v_err_5410_);
v_snd_5374_ = v_snd_5407_;
v___y_5375_ = v___y_5408_;
v___y_5376_ = v___x_5411_;
v_pos_5377_ = v_pos_5409_;
goto v___jp_5373_;
}
v___jp_5412_:
{
lean_object* v___x_5416_; 
v___x_5416_ = lean_box(0);
v_snd_5407_ = v_snd_5414_;
v___y_5408_ = v___y_5415_;
v_pos_5409_ = v___y_5413_;
v_err_5410_ = v___x_5416_;
goto v___jp_5406_;
}
v___jp_5418_:
{
lean_object* v_fst_5423_; lean_object* v_snd_5424_; uint8_t v_decide_5425_; 
v_fst_5423_ = lean_ctor_get(v_pos_5422_, 0);
v_snd_5424_ = lean_ctor_get(v_pos_5422_, 1);
lean_inc(v_snd_5424_);
v_decide_5425_ = lean_nat_dec_eq(v_snd_5419_, v_snd_5424_);
lean_dec(v_snd_5419_);
if (v_decide_5425_ == 0)
{
lean_dec(v_snd_5424_);
lean_dec_ref(v_pos_5422_);
lean_dec_ref(v___y_5420_);
return v___y_5421_;
}
else
{
lean_object* v___x_5426_; uint8_t v_decide_5427_; 
lean_dec_ref(v___y_5421_);
v___x_5426_ = lean_string_utf8_byte_size(v_fst_5423_);
v_decide_5427_ = lean_nat_dec_eq(v_snd_5424_, v___x_5426_);
if (v_decide_5427_ == 0)
{
if (v_decide_5425_ == 0)
{
v___y_5413_ = v_pos_5422_;
v_snd_5414_ = v_snd_5424_;
v___y_5415_ = v___y_5420_;
goto v___jp_5412_;
}
else
{
uint32_t v___x_5428_; uint32_t v_c_5429_; uint8_t v___x_5430_; 
v___x_5428_ = 119;
v_c_5429_ = lean_string_utf8_get_fast(v_fst_5423_, v_snd_5424_);
v___x_5430_ = lean_uint32_dec_eq(v_c_5429_, v___x_5428_);
if (v___x_5430_ == 0)
{
lean_object* v___x_5431_; 
v___x_5431_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1));
v_snd_5407_ = v_snd_5424_;
v___y_5408_ = v___y_5420_;
v_pos_5409_ = v_pos_5422_;
v_err_5410_ = v___x_5431_;
goto v___jp_5406_;
}
else
{
lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5447_; 
lean_inc(v_fst_5423_);
v_isSharedCheck_5447_ = !lean_is_exclusive(v_pos_5422_);
if (v_isSharedCheck_5447_ == 0)
{
lean_object* v_unused_5448_; lean_object* v_unused_5449_; 
v_unused_5448_ = lean_ctor_get(v_pos_5422_, 1);
lean_dec(v_unused_5448_);
v_unused_5449_ = lean_ctor_get(v_pos_5422_, 0);
lean_dec(v_unused_5449_);
v___x_5433_ = v_pos_5422_;
v_isShared_5434_ = v_isSharedCheck_5447_;
goto v_resetjp_5432_;
}
else
{
lean_dec(v_pos_5422_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5447_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v___x_5435_; lean_object* v_it_x27_5437_; 
v___x_5435_ = lean_string_utf8_next_fast(v_fst_5423_, v_snd_5424_);
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 1, v___x_5435_);
v_it_x27_5437_ = v___x_5433_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_fst_5423_);
lean_ctor_set(v_reuseFailAlloc_5446_, 1, v___x_5435_);
v_it_x27_5437_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; 
v___x_5438_ = ((lean_object*)(l_Std_Time_parseModifier___closed__48));
v___x_5439_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(v___x_5438_, v_it_x27_5437_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v_pos_5440_; lean_object* v_res_5441_; lean_object* v___x_5442_; 
v_pos_5440_ = lean_ctor_get(v___x_5439_, 0);
lean_inc(v_pos_5440_);
v_res_5441_ = lean_ctor_get(v___x_5439_, 1);
lean_inc(v_res_5441_);
lean_dec_ref_known(v___x_5439_, 2);
lean_inc_ref(v___y_5420_);
v___x_5442_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5417_, v___y_5420_, v_res_5441_, v_pos_5440_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_dec(v_snd_5424_);
lean_dec_ref(v___y_5420_);
return v___x_5442_;
}
else
{
lean_object* v_pos_5443_; 
v_pos_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_pos_5443_);
v_snd_5374_ = v_snd_5424_;
v___y_5375_ = v___y_5420_;
v___y_5376_ = v___x_5442_;
v_pos_5377_ = v_pos_5443_;
goto v___jp_5373_;
}
}
else
{
lean_object* v_pos_5444_; lean_object* v_err_5445_; 
v_pos_5444_ = lean_ctor_get(v___x_5439_, 0);
lean_inc(v_pos_5444_);
v_err_5445_ = lean_ctor_get(v___x_5439_, 1);
lean_inc(v_err_5445_);
lean_dec_ref_known(v___x_5439_, 2);
v_snd_5407_ = v_snd_5424_;
v___y_5408_ = v___y_5420_;
v_pos_5409_ = v_pos_5444_;
v_err_5410_ = v_err_5445_;
goto v___jp_5406_;
}
}
}
}
}
}
else
{
v___y_5413_ = v_pos_5422_;
v_snd_5414_ = v_snd_5424_;
v___y_5415_ = v___y_5420_;
goto v___jp_5412_;
}
}
}
v___jp_5450_:
{
lean_object* v___x_5455_; 
lean_inc_ref(v_pos_5453_);
v___x_5455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5455_, 0, v_pos_5453_);
lean_ctor_set(v___x_5455_, 1, v_err_5454_);
v_snd_5419_ = v_snd_5451_;
v___y_5420_ = v___y_5452_;
v___y_5421_ = v___x_5455_;
v_pos_5422_ = v_pos_5453_;
goto v___jp_5418_;
}
v___jp_5456_:
{
lean_object* v___x_5460_; 
v___x_5460_ = lean_box(0);
v_snd_5451_ = v_snd_5458_;
v___y_5452_ = v___y_5459_;
v_pos_5453_ = v___y_5457_;
v_err_5454_ = v___x_5460_;
goto v___jp_5450_;
}
v___jp_5462_:
{
lean_object* v_fst_5467_; lean_object* v_snd_5468_; uint8_t v_decide_5469_; 
v_fst_5467_ = lean_ctor_get(v_pos_5466_, 0);
v_snd_5468_ = lean_ctor_get(v_pos_5466_, 1);
lean_inc(v_snd_5468_);
v_decide_5469_ = lean_nat_dec_eq(v_snd_5463_, v_snd_5468_);
lean_dec(v_snd_5463_);
if (v_decide_5469_ == 0)
{
lean_dec(v_snd_5468_);
lean_dec_ref(v_pos_5466_);
lean_dec_ref(v___y_5464_);
return v___y_5465_;
}
else
{
lean_object* v___x_5470_; uint8_t v_decide_5471_; 
lean_dec_ref(v___y_5465_);
v___x_5470_ = lean_string_utf8_byte_size(v_fst_5467_);
v_decide_5471_ = lean_nat_dec_eq(v_snd_5468_, v___x_5470_);
if (v_decide_5471_ == 0)
{
if (v_decide_5469_ == 0)
{
v___y_5457_ = v_pos_5466_;
v_snd_5458_ = v_snd_5468_;
v___y_5459_ = v___y_5464_;
goto v___jp_5456_;
}
else
{
uint32_t v___x_5472_; uint32_t v_c_5473_; uint8_t v___x_5474_; 
v___x_5472_ = 113;
v_c_5473_ = lean_string_utf8_get_fast(v_fst_5467_, v_snd_5468_);
v___x_5474_ = lean_uint32_dec_eq(v_c_5473_, v___x_5472_);
if (v___x_5474_ == 0)
{
lean_object* v___x_5475_; 
v___x_5475_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1));
v_snd_5451_ = v_snd_5468_;
v___y_5452_ = v___y_5464_;
v_pos_5453_ = v_pos_5466_;
v_err_5454_ = v___x_5475_;
goto v___jp_5450_;
}
else
{
lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5491_; 
lean_inc(v_fst_5467_);
v_isSharedCheck_5491_ = !lean_is_exclusive(v_pos_5466_);
if (v_isSharedCheck_5491_ == 0)
{
lean_object* v_unused_5492_; lean_object* v_unused_5493_; 
v_unused_5492_ = lean_ctor_get(v_pos_5466_, 1);
lean_dec(v_unused_5492_);
v_unused_5493_ = lean_ctor_get(v_pos_5466_, 0);
lean_dec(v_unused_5493_);
v___x_5477_ = v_pos_5466_;
v_isShared_5478_ = v_isSharedCheck_5491_;
goto v_resetjp_5476_;
}
else
{
lean_dec(v_pos_5466_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5491_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5479_; lean_object* v_it_x27_5481_; 
v___x_5479_ = lean_string_utf8_next_fast(v_fst_5467_, v_snd_5468_);
if (v_isShared_5478_ == 0)
{
lean_ctor_set(v___x_5477_, 1, v___x_5479_);
v_it_x27_5481_ = v___x_5477_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_fst_5467_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v___x_5479_);
v_it_x27_5481_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___x_5482_ = ((lean_object*)(l_Std_Time_parseModifier___closed__50));
v___x_5483_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(v___x_5482_, v_it_x27_5481_);
if (lean_obj_tag(v___x_5483_) == 0)
{
lean_object* v_pos_5484_; lean_object* v_res_5485_; lean_object* v___x_5486_; 
v_pos_5484_ = lean_ctor_get(v___x_5483_, 0);
lean_inc(v_pos_5484_);
v_res_5485_ = lean_ctor_get(v___x_5483_, 1);
lean_inc(v_res_5485_);
lean_dec_ref_known(v___x_5483_, 2);
v___x_5486_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5461_, v_res_5485_, v_pos_5484_);
if (lean_obj_tag(v___x_5486_) == 0)
{
lean_dec(v_snd_5468_);
lean_dec_ref(v___y_5464_);
return v___x_5486_;
}
else
{
lean_object* v_pos_5487_; 
v_pos_5487_ = lean_ctor_get(v___x_5486_, 0);
lean_inc(v_pos_5487_);
v_snd_5419_ = v_snd_5468_;
v___y_5420_ = v___y_5464_;
v___y_5421_ = v___x_5486_;
v_pos_5422_ = v_pos_5487_;
goto v___jp_5418_;
}
}
else
{
lean_object* v_pos_5488_; lean_object* v_err_5489_; 
v_pos_5488_ = lean_ctor_get(v___x_5483_, 0);
lean_inc(v_pos_5488_);
v_err_5489_ = lean_ctor_get(v___x_5483_, 1);
lean_inc(v_err_5489_);
lean_dec_ref_known(v___x_5483_, 2);
v_snd_5451_ = v_snd_5468_;
v___y_5452_ = v___y_5464_;
v_pos_5453_ = v_pos_5488_;
v_err_5454_ = v_err_5489_;
goto v___jp_5450_;
}
}
}
}
}
}
else
{
v___y_5457_ = v_pos_5466_;
v_snd_5458_ = v_snd_5468_;
v___y_5459_ = v___y_5464_;
goto v___jp_5456_;
}
}
}
v___jp_5494_:
{
lean_object* v___x_5499_; 
lean_inc_ref(v_pos_5497_);
v___x_5499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5499_, 0, v_pos_5497_);
lean_ctor_set(v___x_5499_, 1, v_err_5498_);
v_snd_5463_ = v_snd_5495_;
v___y_5464_ = v___y_5496_;
v___y_5465_ = v___x_5499_;
v_pos_5466_ = v_pos_5497_;
goto v___jp_5462_;
}
v___jp_5500_:
{
lean_object* v___x_5504_; 
v___x_5504_ = lean_box(0);
v_snd_5495_ = v_snd_5502_;
v___y_5496_ = v___y_5503_;
v_pos_5497_ = v___y_5501_;
v_err_5498_ = v___x_5504_;
goto v___jp_5494_;
}
v___jp_5506_:
{
lean_object* v_fst_5511_; lean_object* v_snd_5512_; uint8_t v_decide_5513_; 
v_fst_5511_ = lean_ctor_get(v_pos_5510_, 0);
v_snd_5512_ = lean_ctor_get(v_pos_5510_, 1);
lean_inc(v_snd_5512_);
v_decide_5513_ = lean_nat_dec_eq(v___y_5507_, v_snd_5512_);
lean_dec(v___y_5507_);
if (v_decide_5513_ == 0)
{
lean_dec(v_snd_5512_);
lean_dec_ref(v_pos_5510_);
lean_dec_ref(v___y_5508_);
return v___y_5509_;
}
else
{
lean_object* v___x_5514_; uint8_t v_decide_5515_; 
lean_dec_ref(v___y_5509_);
v___x_5514_ = lean_string_utf8_byte_size(v_fst_5511_);
v_decide_5515_ = lean_nat_dec_eq(v_snd_5512_, v___x_5514_);
if (v_decide_5515_ == 0)
{
if (v_decide_5513_ == 0)
{
v___y_5501_ = v_pos_5510_;
v_snd_5502_ = v_snd_5512_;
v___y_5503_ = v___y_5508_;
goto v___jp_5500_;
}
else
{
uint32_t v___x_5516_; uint32_t v_c_5517_; uint8_t v___x_5518_; 
v___x_5516_ = 81;
v_c_5517_ = lean_string_utf8_get_fast(v_fst_5511_, v_snd_5512_);
v___x_5518_ = lean_uint32_dec_eq(v_c_5517_, v___x_5516_);
if (v___x_5518_ == 0)
{
lean_object* v___x_5519_; 
v___x_5519_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1));
v_snd_5495_ = v_snd_5512_;
v___y_5496_ = v___y_5508_;
v_pos_5497_ = v_pos_5510_;
v_err_5498_ = v___x_5519_;
goto v___jp_5494_;
}
else
{
lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5535_; 
lean_inc(v_fst_5511_);
v_isSharedCheck_5535_ = !lean_is_exclusive(v_pos_5510_);
if (v_isSharedCheck_5535_ == 0)
{
lean_object* v_unused_5536_; lean_object* v_unused_5537_; 
v_unused_5536_ = lean_ctor_get(v_pos_5510_, 1);
lean_dec(v_unused_5536_);
v_unused_5537_ = lean_ctor_get(v_pos_5510_, 0);
lean_dec(v_unused_5537_);
v___x_5521_ = v_pos_5510_;
v_isShared_5522_ = v_isSharedCheck_5535_;
goto v_resetjp_5520_;
}
else
{
lean_dec(v_pos_5510_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5535_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5523_; lean_object* v_it_x27_5525_; 
v___x_5523_ = lean_string_utf8_next_fast(v_fst_5511_, v_snd_5512_);
if (v_isShared_5522_ == 0)
{
lean_ctor_set(v___x_5521_, 1, v___x_5523_);
v_it_x27_5525_ = v___x_5521_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_fst_5511_);
lean_ctor_set(v_reuseFailAlloc_5534_, 1, v___x_5523_);
v_it_x27_5525_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
lean_object* v___x_5526_; lean_object* v___x_5527_; 
v___x_5526_ = ((lean_object*)(l_Std_Time_parseModifier___closed__52));
v___x_5527_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(v___x_5526_, v_it_x27_5525_);
if (lean_obj_tag(v___x_5527_) == 0)
{
lean_object* v_pos_5528_; lean_object* v_res_5529_; lean_object* v___x_5530_; 
v_pos_5528_ = lean_ctor_get(v___x_5527_, 0);
lean_inc(v_pos_5528_);
v_res_5529_ = lean_ctor_get(v___x_5527_, 1);
lean_inc(v_res_5529_);
lean_dec_ref_known(v___x_5527_, 2);
v___x_5530_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5505_, v_res_5529_, v_pos_5528_);
if (lean_obj_tag(v___x_5530_) == 0)
{
lean_dec(v_snd_5512_);
lean_dec_ref(v___y_5508_);
return v___x_5530_;
}
else
{
lean_object* v_pos_5531_; 
v_pos_5531_ = lean_ctor_get(v___x_5530_, 0);
lean_inc(v_pos_5531_);
v_snd_5463_ = v_snd_5512_;
v___y_5464_ = v___y_5508_;
v___y_5465_ = v___x_5530_;
v_pos_5466_ = v_pos_5531_;
goto v___jp_5462_;
}
}
else
{
lean_object* v_pos_5532_; lean_object* v_err_5533_; 
v_pos_5532_ = lean_ctor_get(v___x_5527_, 0);
lean_inc(v_pos_5532_);
v_err_5533_ = lean_ctor_get(v___x_5527_, 1);
lean_inc(v_err_5533_);
lean_dec_ref_known(v___x_5527_, 2);
v_snd_5495_ = v_snd_5512_;
v___y_5496_ = v___y_5508_;
v_pos_5497_ = v_pos_5532_;
v_err_5498_ = v_err_5533_;
goto v___jp_5494_;
}
}
}
}
}
}
else
{
v___y_5501_ = v_pos_5510_;
v_snd_5502_ = v_snd_5512_;
v___y_5503_ = v___y_5508_;
goto v___jp_5500_;
}
}
}
v___jp_5538_:
{
lean_object* v___x_5543_; 
lean_inc_ref(v_pos_5541_);
v___x_5543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5543_, 0, v_pos_5541_);
lean_ctor_set(v___x_5543_, 1, v_err_5542_);
v___y_5507_ = v___y_5539_;
v___y_5508_ = v___y_5540_;
v___y_5509_ = v___x_5543_;
v_pos_5510_ = v_pos_5541_;
goto v___jp_5506_;
}
v___jp_5544_:
{
lean_object* v___x_5548_; 
v___x_5548_ = lean_box(0);
v___y_5539_ = v___y_5545_;
v___y_5540_ = v___y_5547_;
v_pos_5541_ = v___y_5546_;
v_err_5542_ = v___x_5548_;
goto v___jp_5538_;
}
v___jp_5550_:
{
lean_object* v_fst_5554_; lean_object* v_snd_5555_; uint8_t v_decide_5556_; 
v_fst_5554_ = lean_ctor_get(v_pos_5553_, 0);
v_snd_5555_ = lean_ctor_get(v_pos_5553_, 1);
lean_inc(v_snd_5555_);
v_decide_5556_ = lean_nat_dec_eq(v_snd_5551_, v_snd_5555_);
lean_dec(v_snd_5551_);
if (v_decide_5556_ == 0)
{
lean_dec(v_snd_5555_);
lean_dec_ref(v_pos_5553_);
return v___y_5552_;
}
else
{
lean_object* v___x_5557_; lean_object* v___x_5558_; uint8_t v_decide_5559_; 
lean_dec_ref(v___y_5552_);
v___x_5557_ = ((lean_object*)(l_Std_Time_parseModifier___closed__54));
v___x_5558_ = lean_string_utf8_byte_size(v_fst_5554_);
v_decide_5559_ = lean_nat_dec_eq(v_snd_5555_, v___x_5558_);
if (v_decide_5559_ == 0)
{
if (v_decide_5556_ == 0)
{
v___y_5545_ = v_snd_5555_;
v___y_5546_ = v_pos_5553_;
v___y_5547_ = v___x_5557_;
goto v___jp_5544_;
}
else
{
uint32_t v___x_5560_; uint32_t v_c_5561_; uint8_t v___x_5562_; 
v___x_5560_ = 100;
v_c_5561_ = lean_string_utf8_get_fast(v_fst_5554_, v_snd_5555_);
v___x_5562_ = lean_uint32_dec_eq(v_c_5561_, v___x_5560_);
if (v___x_5562_ == 0)
{
lean_object* v___x_5563_; 
v___x_5563_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1));
v___y_5539_ = v_snd_5555_;
v___y_5540_ = v___x_5557_;
v_pos_5541_ = v_pos_5553_;
v_err_5542_ = v___x_5563_;
goto v___jp_5538_;
}
else
{
lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5579_; 
lean_inc(v_fst_5554_);
v_isSharedCheck_5579_ = !lean_is_exclusive(v_pos_5553_);
if (v_isSharedCheck_5579_ == 0)
{
lean_object* v_unused_5580_; lean_object* v_unused_5581_; 
v_unused_5580_ = lean_ctor_get(v_pos_5553_, 1);
lean_dec(v_unused_5580_);
v_unused_5581_ = lean_ctor_get(v_pos_5553_, 0);
lean_dec(v_unused_5581_);
v___x_5565_ = v_pos_5553_;
v_isShared_5566_ = v_isSharedCheck_5579_;
goto v_resetjp_5564_;
}
else
{
lean_dec(v_pos_5553_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5579_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v___x_5567_; lean_object* v_it_x27_5569_; 
v___x_5567_ = lean_string_utf8_next_fast(v_fst_5554_, v_snd_5555_);
if (v_isShared_5566_ == 0)
{
lean_ctor_set(v___x_5565_, 1, v___x_5567_);
v_it_x27_5569_ = v___x_5565_;
goto v_reusejp_5568_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_fst_5554_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v___x_5567_);
v_it_x27_5569_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5568_;
}
v_reusejp_5568_:
{
lean_object* v___x_5570_; lean_object* v___x_5571_; 
v___x_5570_ = ((lean_object*)(l_Std_Time_parseModifier___closed__55));
v___x_5571_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(v___x_5570_, v_it_x27_5569_);
if (lean_obj_tag(v___x_5571_) == 0)
{
lean_object* v_pos_5572_; lean_object* v_res_5573_; lean_object* v___x_5574_; 
v_pos_5572_ = lean_ctor_get(v___x_5571_, 0);
lean_inc(v_pos_5572_);
v_res_5573_ = lean_ctor_get(v___x_5571_, 1);
lean_inc(v_res_5573_);
lean_dec_ref_known(v___x_5571_, 2);
v___x_5574_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5549_, v___x_5557_, v_res_5573_, v_pos_5572_);
if (lean_obj_tag(v___x_5574_) == 0)
{
lean_dec(v_snd_5555_);
return v___x_5574_;
}
else
{
lean_object* v_pos_5575_; 
v_pos_5575_ = lean_ctor_get(v___x_5574_, 0);
lean_inc(v_pos_5575_);
v___y_5507_ = v_snd_5555_;
v___y_5508_ = v___x_5557_;
v___y_5509_ = v___x_5574_;
v_pos_5510_ = v_pos_5575_;
goto v___jp_5506_;
}
}
else
{
lean_object* v_pos_5576_; lean_object* v_err_5577_; 
v_pos_5576_ = lean_ctor_get(v___x_5571_, 0);
lean_inc(v_pos_5576_);
v_err_5577_ = lean_ctor_get(v___x_5571_, 1);
lean_inc(v_err_5577_);
lean_dec_ref_known(v___x_5571_, 2);
v___y_5539_ = v_snd_5555_;
v___y_5540_ = v___x_5557_;
v_pos_5541_ = v_pos_5576_;
v_err_5542_ = v_err_5577_;
goto v___jp_5538_;
}
}
}
}
}
}
else
{
v___y_5545_ = v_snd_5555_;
v___y_5546_ = v_pos_5553_;
v___y_5547_ = v___x_5557_;
goto v___jp_5544_;
}
}
}
v___jp_5582_:
{
lean_object* v___x_5586_; 
lean_inc_ref(v_pos_5584_);
v___x_5586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5586_, 0, v_pos_5584_);
lean_ctor_set(v___x_5586_, 1, v_err_5585_);
v_snd_5551_ = v_snd_5583_;
v___y_5552_ = v___x_5586_;
v_pos_5553_ = v_pos_5584_;
goto v___jp_5550_;
}
v___jp_5587_:
{
lean_object* v___x_5590_; 
v___x_5590_ = lean_box(0);
v_snd_5583_ = v_snd_5589_;
v_pos_5584_ = v___y_5588_;
v_err_5585_ = v___x_5590_;
goto v___jp_5582_;
}
v___jp_5592_:
{
lean_object* v_fst_5596_; lean_object* v_snd_5597_; uint8_t v_decide_5598_; 
v_fst_5596_ = lean_ctor_get(v_pos_5595_, 0);
v_snd_5597_ = lean_ctor_get(v_pos_5595_, 1);
lean_inc(v_snd_5597_);
v_decide_5598_ = lean_nat_dec_eq(v_snd_5593_, v_snd_5597_);
lean_dec(v_snd_5593_);
if (v_decide_5598_ == 0)
{
lean_dec(v_snd_5597_);
lean_dec_ref(v_pos_5595_);
return v___y_5594_;
}
else
{
lean_object* v___x_5599_; uint8_t v_decide_5600_; 
lean_dec_ref(v___y_5594_);
v___x_5599_ = lean_string_utf8_byte_size(v_fst_5596_);
v_decide_5600_ = lean_nat_dec_eq(v_snd_5597_, v___x_5599_);
if (v_decide_5600_ == 0)
{
if (v_decide_5598_ == 0)
{
v___y_5588_ = v_pos_5595_;
v_snd_5589_ = v_snd_5597_;
goto v___jp_5587_;
}
else
{
uint32_t v___x_5601_; uint32_t v_c_5602_; uint8_t v___x_5603_; 
v___x_5601_ = 76;
v_c_5602_ = lean_string_utf8_get_fast(v_fst_5596_, v_snd_5597_);
v___x_5603_ = lean_uint32_dec_eq(v_c_5602_, v___x_5601_);
if (v___x_5603_ == 0)
{
lean_object* v___x_5604_; 
v___x_5604_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1));
v_snd_5583_ = v_snd_5597_;
v_pos_5584_ = v_pos_5595_;
v_err_5585_ = v___x_5604_;
goto v___jp_5582_;
}
else
{
lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5620_; 
lean_inc(v_fst_5596_);
v_isSharedCheck_5620_ = !lean_is_exclusive(v_pos_5595_);
if (v_isSharedCheck_5620_ == 0)
{
lean_object* v_unused_5621_; lean_object* v_unused_5622_; 
v_unused_5621_ = lean_ctor_get(v_pos_5595_, 1);
lean_dec(v_unused_5621_);
v_unused_5622_ = lean_ctor_get(v_pos_5595_, 0);
lean_dec(v_unused_5622_);
v___x_5606_ = v_pos_5595_;
v_isShared_5607_ = v_isSharedCheck_5620_;
goto v_resetjp_5605_;
}
else
{
lean_dec(v_pos_5595_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5620_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v___x_5608_; lean_object* v_it_x27_5610_; 
v___x_5608_ = lean_string_utf8_next_fast(v_fst_5596_, v_snd_5597_);
if (v_isShared_5607_ == 0)
{
lean_ctor_set(v___x_5606_, 1, v___x_5608_);
v_it_x27_5610_ = v___x_5606_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_fst_5596_);
lean_ctor_set(v_reuseFailAlloc_5619_, 1, v___x_5608_);
v_it_x27_5610_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
lean_object* v___x_5611_; lean_object* v___x_5612_; 
v___x_5611_ = ((lean_object*)(l_Std_Time_parseModifier___closed__57));
v___x_5612_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(v___x_5611_, v_it_x27_5610_);
if (lean_obj_tag(v___x_5612_) == 0)
{
lean_object* v_pos_5613_; lean_object* v_res_5614_; lean_object* v___x_5615_; 
v_pos_5613_ = lean_ctor_get(v___x_5612_, 0);
lean_inc(v_pos_5613_);
v_res_5614_ = lean_ctor_get(v___x_5612_, 1);
lean_inc(v_res_5614_);
lean_dec_ref_known(v___x_5612_, 2);
v___x_5615_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5591_, v_res_5614_, v_pos_5613_);
if (lean_obj_tag(v___x_5615_) == 0)
{
lean_dec(v_snd_5597_);
return v___x_5615_;
}
else
{
lean_object* v_pos_5616_; 
v_pos_5616_ = lean_ctor_get(v___x_5615_, 0);
lean_inc(v_pos_5616_);
v_snd_5551_ = v_snd_5597_;
v___y_5552_ = v___x_5615_;
v_pos_5553_ = v_pos_5616_;
goto v___jp_5550_;
}
}
else
{
lean_object* v_pos_5617_; lean_object* v_err_5618_; 
v_pos_5617_ = lean_ctor_get(v___x_5612_, 0);
lean_inc(v_pos_5617_);
v_err_5618_ = lean_ctor_get(v___x_5612_, 1);
lean_inc(v_err_5618_);
lean_dec_ref_known(v___x_5612_, 2);
v_snd_5583_ = v_snd_5597_;
v_pos_5584_ = v_pos_5617_;
v_err_5585_ = v_err_5618_;
goto v___jp_5582_;
}
}
}
}
}
}
else
{
v___y_5588_ = v_pos_5595_;
v_snd_5589_ = v_snd_5597_;
goto v___jp_5587_;
}
}
}
v___jp_5623_:
{
lean_object* v___x_5627_; 
lean_inc_ref(v_pos_5625_);
v___x_5627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5627_, 0, v_pos_5625_);
lean_ctor_set(v___x_5627_, 1, v_err_5626_);
v_snd_5593_ = v_snd_5624_;
v___y_5594_ = v___x_5627_;
v_pos_5595_ = v_pos_5625_;
goto v___jp_5592_;
}
v___jp_5628_:
{
lean_object* v___x_5631_; 
v___x_5631_ = lean_box(0);
v_snd_5624_ = v_snd_5630_;
v_pos_5625_ = v___y_5629_;
v_err_5626_ = v___x_5631_;
goto v___jp_5623_;
}
v___jp_5633_:
{
lean_object* v_fst_5637_; lean_object* v_snd_5638_; uint8_t v_decide_5639_; 
v_fst_5637_ = lean_ctor_get(v_pos_5636_, 0);
v_snd_5638_ = lean_ctor_get(v_pos_5636_, 1);
lean_inc(v_snd_5638_);
v_decide_5639_ = lean_nat_dec_eq(v_snd_5634_, v_snd_5638_);
lean_dec(v_snd_5634_);
if (v_decide_5639_ == 0)
{
lean_dec(v_snd_5638_);
lean_dec_ref(v_pos_5636_);
return v___y_5635_;
}
else
{
lean_object* v___x_5640_; uint8_t v_decide_5641_; 
lean_dec_ref(v___y_5635_);
v___x_5640_ = lean_string_utf8_byte_size(v_fst_5637_);
v_decide_5641_ = lean_nat_dec_eq(v_snd_5638_, v___x_5640_);
if (v_decide_5641_ == 0)
{
if (v_decide_5639_ == 0)
{
v___y_5629_ = v_pos_5636_;
v_snd_5630_ = v_snd_5638_;
goto v___jp_5628_;
}
else
{
uint32_t v___x_5642_; uint32_t v_c_5643_; uint8_t v___x_5644_; 
v___x_5642_ = 77;
v_c_5643_ = lean_string_utf8_get_fast(v_fst_5637_, v_snd_5638_);
v___x_5644_ = lean_uint32_dec_eq(v_c_5643_, v___x_5642_);
if (v___x_5644_ == 0)
{
lean_object* v___x_5645_; 
v___x_5645_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1));
v_snd_5624_ = v_snd_5638_;
v_pos_5625_ = v_pos_5636_;
v_err_5626_ = v___x_5645_;
goto v___jp_5623_;
}
else
{
lean_object* v___x_5647_; uint8_t v_isShared_5648_; uint8_t v_isSharedCheck_5661_; 
lean_inc(v_fst_5637_);
v_isSharedCheck_5661_ = !lean_is_exclusive(v_pos_5636_);
if (v_isSharedCheck_5661_ == 0)
{
lean_object* v_unused_5662_; lean_object* v_unused_5663_; 
v_unused_5662_ = lean_ctor_get(v_pos_5636_, 1);
lean_dec(v_unused_5662_);
v_unused_5663_ = lean_ctor_get(v_pos_5636_, 0);
lean_dec(v_unused_5663_);
v___x_5647_ = v_pos_5636_;
v_isShared_5648_ = v_isSharedCheck_5661_;
goto v_resetjp_5646_;
}
else
{
lean_dec(v_pos_5636_);
v___x_5647_ = lean_box(0);
v_isShared_5648_ = v_isSharedCheck_5661_;
goto v_resetjp_5646_;
}
v_resetjp_5646_:
{
lean_object* v___x_5649_; lean_object* v_it_x27_5651_; 
v___x_5649_ = lean_string_utf8_next_fast(v_fst_5637_, v_snd_5638_);
if (v_isShared_5648_ == 0)
{
lean_ctor_set(v___x_5647_, 1, v___x_5649_);
v_it_x27_5651_ = v___x_5647_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_fst_5637_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v___x_5649_);
v_it_x27_5651_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
lean_object* v___x_5652_; lean_object* v___x_5653_; 
v___x_5652_ = ((lean_object*)(l_Std_Time_parseModifier___closed__59));
v___x_5653_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(v___x_5652_, v_it_x27_5651_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v_pos_5654_; lean_object* v_res_5655_; lean_object* v___x_5656_; 
v_pos_5654_ = lean_ctor_get(v___x_5653_, 0);
lean_inc(v_pos_5654_);
v_res_5655_ = lean_ctor_get(v___x_5653_, 1);
lean_inc(v_res_5655_);
lean_dec_ref_known(v___x_5653_, 2);
v___x_5656_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5632_, v_res_5655_, v_pos_5654_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_dec(v_snd_5638_);
return v___x_5656_;
}
else
{
lean_object* v_pos_5657_; 
v_pos_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_pos_5657_);
v_snd_5593_ = v_snd_5638_;
v___y_5594_ = v___x_5656_;
v_pos_5595_ = v_pos_5657_;
goto v___jp_5592_;
}
}
else
{
lean_object* v_pos_5658_; lean_object* v_err_5659_; 
v_pos_5658_ = lean_ctor_get(v___x_5653_, 0);
lean_inc(v_pos_5658_);
v_err_5659_ = lean_ctor_get(v___x_5653_, 1);
lean_inc(v_err_5659_);
lean_dec_ref_known(v___x_5653_, 2);
v_snd_5624_ = v_snd_5638_;
v_pos_5625_ = v_pos_5658_;
v_err_5626_ = v_err_5659_;
goto v___jp_5623_;
}
}
}
}
}
}
else
{
v___y_5629_ = v_pos_5636_;
v_snd_5630_ = v_snd_5638_;
goto v___jp_5628_;
}
}
}
v___jp_5664_:
{
lean_object* v___x_5668_; 
lean_inc_ref(v_pos_5666_);
v___x_5668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5668_, 0, v_pos_5666_);
lean_ctor_set(v___x_5668_, 1, v_err_5667_);
v_snd_5634_ = v_snd_5665_;
v___y_5635_ = v___x_5668_;
v_pos_5636_ = v_pos_5666_;
goto v___jp_5633_;
}
v___jp_5669_:
{
lean_object* v___x_5672_; 
v___x_5672_ = lean_box(0);
v_snd_5665_ = v_snd_5671_;
v_pos_5666_ = v___y_5670_;
v_err_5667_ = v___x_5672_;
goto v___jp_5664_;
}
v___jp_5674_:
{
lean_object* v_fst_5678_; lean_object* v_snd_5679_; uint8_t v_decide_5680_; 
v_fst_5678_ = lean_ctor_get(v_pos_5677_, 0);
v_snd_5679_ = lean_ctor_get(v_pos_5677_, 1);
lean_inc(v_snd_5679_);
v_decide_5680_ = lean_nat_dec_eq(v_snd_5675_, v_snd_5679_);
lean_dec(v_snd_5675_);
if (v_decide_5680_ == 0)
{
lean_dec(v_snd_5679_);
lean_dec_ref(v_pos_5677_);
return v___y_5676_;
}
else
{
lean_object* v___x_5681_; uint8_t v_decide_5682_; 
lean_dec_ref(v___y_5676_);
v___x_5681_ = lean_string_utf8_byte_size(v_fst_5678_);
v_decide_5682_ = lean_nat_dec_eq(v_snd_5679_, v___x_5681_);
if (v_decide_5682_ == 0)
{
if (v_decide_5680_ == 0)
{
v___y_5670_ = v_pos_5677_;
v_snd_5671_ = v_snd_5679_;
goto v___jp_5669_;
}
else
{
uint32_t v___x_5683_; uint32_t v_c_5684_; uint8_t v___x_5685_; 
v___x_5683_ = 68;
v_c_5684_ = lean_string_utf8_get_fast(v_fst_5678_, v_snd_5679_);
v___x_5685_ = lean_uint32_dec_eq(v_c_5684_, v___x_5683_);
if (v___x_5685_ == 0)
{
lean_object* v___x_5686_; 
v___x_5686_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1));
v_snd_5665_ = v_snd_5679_;
v_pos_5666_ = v_pos_5677_;
v_err_5667_ = v___x_5686_;
goto v___jp_5664_;
}
else
{
lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5703_; 
lean_inc(v_fst_5678_);
v_isSharedCheck_5703_ = !lean_is_exclusive(v_pos_5677_);
if (v_isSharedCheck_5703_ == 0)
{
lean_object* v_unused_5704_; lean_object* v_unused_5705_; 
v_unused_5704_ = lean_ctor_get(v_pos_5677_, 1);
lean_dec(v_unused_5704_);
v_unused_5705_ = lean_ctor_get(v_pos_5677_, 0);
lean_dec(v_unused_5705_);
v___x_5688_ = v_pos_5677_;
v_isShared_5689_ = v_isSharedCheck_5703_;
goto v_resetjp_5687_;
}
else
{
lean_dec(v_pos_5677_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5703_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v___x_5690_; lean_object* v_it_x27_5692_; 
v___x_5690_ = lean_string_utf8_next_fast(v_fst_5678_, v_snd_5679_);
if (v_isShared_5689_ == 0)
{
lean_ctor_set(v___x_5688_, 1, v___x_5690_);
v_it_x27_5692_ = v___x_5688_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_fst_5678_);
lean_ctor_set(v_reuseFailAlloc_5702_, 1, v___x_5690_);
v_it_x27_5692_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
lean_object* v___x_5693_; lean_object* v___x_5694_; 
v___x_5693_ = ((lean_object*)(l_Std_Time_parseModifier___closed__61));
v___x_5694_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(v___x_5693_, v_it_x27_5692_);
if (lean_obj_tag(v___x_5694_) == 0)
{
lean_object* v_pos_5695_; lean_object* v_res_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; 
v_pos_5695_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_pos_5695_);
v_res_5696_ = lean_ctor_get(v___x_5694_, 1);
lean_inc(v_res_5696_);
lean_dec_ref_known(v___x_5694_, 2);
v___x_5697_ = ((lean_object*)(l_Std_Time_parseModifier___closed__62));
v___x_5698_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5673_, v___x_5697_, v_res_5696_, v_pos_5695_);
if (lean_obj_tag(v___x_5698_) == 0)
{
lean_dec(v_snd_5679_);
return v___x_5698_;
}
else
{
lean_object* v_pos_5699_; 
v_pos_5699_ = lean_ctor_get(v___x_5698_, 0);
lean_inc(v_pos_5699_);
v_snd_5634_ = v_snd_5679_;
v___y_5635_ = v___x_5698_;
v_pos_5636_ = v_pos_5699_;
goto v___jp_5633_;
}
}
else
{
lean_object* v_pos_5700_; lean_object* v_err_5701_; 
v_pos_5700_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_pos_5700_);
v_err_5701_ = lean_ctor_get(v___x_5694_, 1);
lean_inc(v_err_5701_);
lean_dec_ref_known(v___x_5694_, 2);
v_snd_5665_ = v_snd_5679_;
v_pos_5666_ = v_pos_5700_;
v_err_5667_ = v_err_5701_;
goto v___jp_5664_;
}
}
}
}
}
}
else
{
v___y_5670_ = v_pos_5677_;
v_snd_5671_ = v_snd_5679_;
goto v___jp_5669_;
}
}
}
v___jp_5706_:
{
lean_object* v___x_5710_; 
lean_inc_ref(v_pos_5708_);
v___x_5710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5710_, 0, v_pos_5708_);
lean_ctor_set(v___x_5710_, 1, v_err_5709_);
v_snd_5675_ = v_snd_5707_;
v___y_5676_ = v___x_5710_;
v_pos_5677_ = v_pos_5708_;
goto v___jp_5674_;
}
v___jp_5711_:
{
lean_object* v___x_5714_; 
v___x_5714_ = lean_box(0);
v_snd_5707_ = v_snd_5713_;
v_pos_5708_ = v___y_5712_;
v_err_5709_ = v___x_5714_;
goto v___jp_5706_;
}
v___jp_5716_:
{
lean_object* v_fst_5720_; lean_object* v_snd_5721_; uint8_t v_decide_5722_; 
v_fst_5720_ = lean_ctor_get(v_pos_5719_, 0);
v_snd_5721_ = lean_ctor_get(v_pos_5719_, 1);
lean_inc(v_snd_5721_);
v_decide_5722_ = lean_nat_dec_eq(v_snd_5717_, v_snd_5721_);
lean_dec(v_snd_5717_);
if (v_decide_5722_ == 0)
{
lean_dec(v_snd_5721_);
lean_dec_ref(v_pos_5719_);
return v___y_5718_;
}
else
{
lean_object* v___x_5723_; uint8_t v_decide_5724_; 
lean_dec_ref(v___y_5718_);
v___x_5723_ = lean_string_utf8_byte_size(v_fst_5720_);
v_decide_5724_ = lean_nat_dec_eq(v_snd_5721_, v___x_5723_);
if (v_decide_5724_ == 0)
{
if (v_decide_5722_ == 0)
{
v___y_5712_ = v_pos_5719_;
v_snd_5713_ = v_snd_5721_;
goto v___jp_5711_;
}
else
{
uint32_t v___x_5725_; uint32_t v_c_5726_; uint8_t v___x_5727_; 
v___x_5725_ = 117;
v_c_5726_ = lean_string_utf8_get_fast(v_fst_5720_, v_snd_5721_);
v___x_5727_ = lean_uint32_dec_eq(v_c_5726_, v___x_5725_);
if (v___x_5727_ == 0)
{
lean_object* v___x_5728_; 
v___x_5728_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1));
v_snd_5707_ = v_snd_5721_;
v_pos_5708_ = v_pos_5719_;
v_err_5709_ = v___x_5728_;
goto v___jp_5706_;
}
else
{
lean_object* v___x_5730_; uint8_t v_isShared_5731_; uint8_t v_isSharedCheck_5744_; 
lean_inc(v_fst_5720_);
v_isSharedCheck_5744_ = !lean_is_exclusive(v_pos_5719_);
if (v_isSharedCheck_5744_ == 0)
{
lean_object* v_unused_5745_; lean_object* v_unused_5746_; 
v_unused_5745_ = lean_ctor_get(v_pos_5719_, 1);
lean_dec(v_unused_5745_);
v_unused_5746_ = lean_ctor_get(v_pos_5719_, 0);
lean_dec(v_unused_5746_);
v___x_5730_ = v_pos_5719_;
v_isShared_5731_ = v_isSharedCheck_5744_;
goto v_resetjp_5729_;
}
else
{
lean_dec(v_pos_5719_);
v___x_5730_ = lean_box(0);
v_isShared_5731_ = v_isSharedCheck_5744_;
goto v_resetjp_5729_;
}
v_resetjp_5729_:
{
lean_object* v___x_5732_; lean_object* v_it_x27_5734_; 
v___x_5732_ = lean_string_utf8_next_fast(v_fst_5720_, v_snd_5721_);
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 1, v___x_5732_);
v_it_x27_5734_ = v___x_5730_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_fst_5720_);
lean_ctor_set(v_reuseFailAlloc_5743_, 1, v___x_5732_);
v_it_x27_5734_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
lean_object* v___x_5735_; lean_object* v___x_5736_; 
v___x_5735_ = ((lean_object*)(l_Std_Time_parseModifier___closed__64));
v___x_5736_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(v___x_5735_, v_it_x27_5734_);
if (lean_obj_tag(v___x_5736_) == 0)
{
lean_object* v_pos_5737_; lean_object* v_res_5738_; lean_object* v___x_5739_; 
v_pos_5737_ = lean_ctor_get(v___x_5736_, 0);
lean_inc(v_pos_5737_);
v_res_5738_ = lean_ctor_get(v___x_5736_, 1);
lean_inc(v_res_5738_);
lean_dec_ref_known(v___x_5736_, 2);
v___x_5739_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5715_, v_res_5738_, v_pos_5737_);
if (lean_obj_tag(v___x_5739_) == 0)
{
lean_dec(v_snd_5721_);
return v___x_5739_;
}
else
{
lean_object* v_pos_5740_; 
v_pos_5740_ = lean_ctor_get(v___x_5739_, 0);
lean_inc(v_pos_5740_);
v_snd_5675_ = v_snd_5721_;
v___y_5676_ = v___x_5739_;
v_pos_5677_ = v_pos_5740_;
goto v___jp_5674_;
}
}
else
{
lean_object* v_pos_5741_; lean_object* v_err_5742_; 
v_pos_5741_ = lean_ctor_get(v___x_5736_, 0);
lean_inc(v_pos_5741_);
v_err_5742_ = lean_ctor_get(v___x_5736_, 1);
lean_inc(v_err_5742_);
lean_dec_ref_known(v___x_5736_, 2);
v_snd_5707_ = v_snd_5721_;
v_pos_5708_ = v_pos_5741_;
v_err_5709_ = v_err_5742_;
goto v___jp_5706_;
}
}
}
}
}
}
else
{
v___y_5712_ = v_pos_5719_;
v_snd_5713_ = v_snd_5721_;
goto v___jp_5711_;
}
}
}
v___jp_5747_:
{
lean_object* v___x_5751_; 
lean_inc_ref(v_pos_5749_);
v___x_5751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5751_, 0, v_pos_5749_);
lean_ctor_set(v___x_5751_, 1, v_err_5750_);
v_snd_5717_ = v_snd_5748_;
v___y_5718_ = v___x_5751_;
v_pos_5719_ = v_pos_5749_;
goto v___jp_5716_;
}
v___jp_5752_:
{
lean_object* v___x_5755_; 
v___x_5755_ = lean_box(0);
v_snd_5748_ = v_snd_5754_;
v_pos_5749_ = v___y_5753_;
v_err_5750_ = v___x_5755_;
goto v___jp_5747_;
}
v___jp_5757_:
{
lean_object* v_fst_5761_; lean_object* v_snd_5762_; uint8_t v_decide_5763_; 
v_fst_5761_ = lean_ctor_get(v_pos_5760_, 0);
v_snd_5762_ = lean_ctor_get(v_pos_5760_, 1);
lean_inc(v_snd_5762_);
v_decide_5763_ = lean_nat_dec_eq(v_snd_5758_, v_snd_5762_);
lean_dec(v_snd_5758_);
if (v_decide_5763_ == 0)
{
lean_dec(v_snd_5762_);
lean_dec_ref(v_pos_5760_);
return v___y_5759_;
}
else
{
lean_object* v___x_5764_; uint8_t v_decide_5765_; 
lean_dec_ref(v___y_5759_);
v___x_5764_ = lean_string_utf8_byte_size(v_fst_5761_);
v_decide_5765_ = lean_nat_dec_eq(v_snd_5762_, v___x_5764_);
if (v_decide_5765_ == 0)
{
if (v_decide_5763_ == 0)
{
v___y_5753_ = v_pos_5760_;
v_snd_5754_ = v_snd_5762_;
goto v___jp_5752_;
}
else
{
uint32_t v___x_5766_; uint32_t v_c_5767_; uint8_t v___x_5768_; 
v___x_5766_ = 89;
v_c_5767_ = lean_string_utf8_get_fast(v_fst_5761_, v_snd_5762_);
v___x_5768_ = lean_uint32_dec_eq(v_c_5767_, v___x_5766_);
if (v___x_5768_ == 0)
{
lean_object* v___x_5769_; 
v___x_5769_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1));
v_snd_5748_ = v_snd_5762_;
v_pos_5749_ = v_pos_5760_;
v_err_5750_ = v___x_5769_;
goto v___jp_5747_;
}
else
{
lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5785_; 
lean_inc(v_fst_5761_);
v_isSharedCheck_5785_ = !lean_is_exclusive(v_pos_5760_);
if (v_isSharedCheck_5785_ == 0)
{
lean_object* v_unused_5786_; lean_object* v_unused_5787_; 
v_unused_5786_ = lean_ctor_get(v_pos_5760_, 1);
lean_dec(v_unused_5786_);
v_unused_5787_ = lean_ctor_get(v_pos_5760_, 0);
lean_dec(v_unused_5787_);
v___x_5771_ = v_pos_5760_;
v_isShared_5772_ = v_isSharedCheck_5785_;
goto v_resetjp_5770_;
}
else
{
lean_dec(v_pos_5760_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5785_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
lean_object* v___x_5773_; lean_object* v_it_x27_5775_; 
v___x_5773_ = lean_string_utf8_next_fast(v_fst_5761_, v_snd_5762_);
if (v_isShared_5772_ == 0)
{
lean_ctor_set(v___x_5771_, 1, v___x_5773_);
v_it_x27_5775_ = v___x_5771_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_fst_5761_);
lean_ctor_set(v_reuseFailAlloc_5784_, 1, v___x_5773_);
v_it_x27_5775_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
lean_object* v___x_5776_; lean_object* v___x_5777_; 
v___x_5776_ = ((lean_object*)(l_Std_Time_parseModifier___closed__66));
v___x_5777_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(v___x_5776_, v_it_x27_5775_);
if (lean_obj_tag(v___x_5777_) == 0)
{
lean_object* v_pos_5778_; lean_object* v_res_5779_; lean_object* v___x_5780_; 
v_pos_5778_ = lean_ctor_get(v___x_5777_, 0);
lean_inc(v_pos_5778_);
v_res_5779_ = lean_ctor_get(v___x_5777_, 1);
lean_inc(v_res_5779_);
lean_dec_ref_known(v___x_5777_, 2);
v___x_5780_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5756_, v_res_5779_, v_pos_5778_);
if (lean_obj_tag(v___x_5780_) == 0)
{
lean_dec(v_snd_5762_);
return v___x_5780_;
}
else
{
lean_object* v_pos_5781_; 
v_pos_5781_ = lean_ctor_get(v___x_5780_, 0);
lean_inc(v_pos_5781_);
v_snd_5717_ = v_snd_5762_;
v___y_5718_ = v___x_5780_;
v_pos_5719_ = v_pos_5781_;
goto v___jp_5716_;
}
}
else
{
lean_object* v_pos_5782_; lean_object* v_err_5783_; 
v_pos_5782_ = lean_ctor_get(v___x_5777_, 0);
lean_inc(v_pos_5782_);
v_err_5783_ = lean_ctor_get(v___x_5777_, 1);
lean_inc(v_err_5783_);
lean_dec_ref_known(v___x_5777_, 2);
v_snd_5748_ = v_snd_5762_;
v_pos_5749_ = v_pos_5782_;
v_err_5750_ = v_err_5783_;
goto v___jp_5747_;
}
}
}
}
}
}
else
{
v___y_5753_ = v_pos_5760_;
v_snd_5754_ = v_snd_5762_;
goto v___jp_5752_;
}
}
}
v___jp_5788_:
{
lean_object* v___x_5792_; 
lean_inc_ref(v_pos_5790_);
v___x_5792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5792_, 0, v_pos_5790_);
lean_ctor_set(v___x_5792_, 1, v_err_5791_);
v_snd_5758_ = v_snd_5789_;
v___y_5759_ = v___x_5792_;
v_pos_5760_ = v_pos_5790_;
goto v___jp_5757_;
}
v___jp_5793_:
{
lean_object* v___x_5796_; 
v___x_5796_ = lean_box(0);
v_snd_5789_ = v_snd_5795_;
v_pos_5790_ = v___y_5794_;
v_err_5791_ = v___x_5796_;
goto v___jp_5788_;
}
v___jp_5798_:
{
lean_object* v_fst_5801_; lean_object* v_snd_5802_; uint8_t v_decide_5803_; 
v_fst_5801_ = lean_ctor_get(v_pos_5800_, 0);
v_snd_5802_ = lean_ctor_get(v_pos_5800_, 1);
lean_inc(v_snd_5802_);
v_decide_5803_ = lean_nat_dec_eq(v_snd_4336_, v_snd_5802_);
lean_dec(v_snd_4336_);
if (v_decide_5803_ == 0)
{
lean_dec(v_snd_5802_);
lean_dec_ref(v_pos_5800_);
return v___y_5799_;
}
else
{
lean_object* v___x_5804_; uint8_t v_decide_5805_; 
lean_dec_ref(v___y_5799_);
v___x_5804_ = lean_string_utf8_byte_size(v_fst_5801_);
v_decide_5805_ = lean_nat_dec_eq(v_snd_5802_, v___x_5804_);
if (v_decide_5805_ == 0)
{
if (v_decide_5803_ == 0)
{
v___y_5794_ = v_pos_5800_;
v_snd_5795_ = v_snd_5802_;
goto v___jp_5793_;
}
else
{
uint32_t v___x_5806_; uint32_t v_c_5807_; uint8_t v___x_5808_; 
v___x_5806_ = 121;
v_c_5807_ = lean_string_utf8_get_fast(v_fst_5801_, v_snd_5802_);
v___x_5808_ = lean_uint32_dec_eq(v_c_5807_, v___x_5806_);
if (v___x_5808_ == 0)
{
lean_object* v___x_5809_; 
v___x_5809_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1));
v_snd_5789_ = v_snd_5802_;
v_pos_5790_ = v_pos_5800_;
v_err_5791_ = v___x_5809_;
goto v___jp_5788_;
}
else
{
lean_object* v___x_5811_; uint8_t v_isShared_5812_; uint8_t v_isSharedCheck_5825_; 
lean_inc(v_fst_5801_);
v_isSharedCheck_5825_ = !lean_is_exclusive(v_pos_5800_);
if (v_isSharedCheck_5825_ == 0)
{
lean_object* v_unused_5826_; lean_object* v_unused_5827_; 
v_unused_5826_ = lean_ctor_get(v_pos_5800_, 1);
lean_dec(v_unused_5826_);
v_unused_5827_ = lean_ctor_get(v_pos_5800_, 0);
lean_dec(v_unused_5827_);
v___x_5811_ = v_pos_5800_;
v_isShared_5812_ = v_isSharedCheck_5825_;
goto v_resetjp_5810_;
}
else
{
lean_dec(v_pos_5800_);
v___x_5811_ = lean_box(0);
v_isShared_5812_ = v_isSharedCheck_5825_;
goto v_resetjp_5810_;
}
v_resetjp_5810_:
{
lean_object* v___x_5813_; lean_object* v_it_x27_5815_; 
v___x_5813_ = lean_string_utf8_next_fast(v_fst_5801_, v_snd_5802_);
if (v_isShared_5812_ == 0)
{
lean_ctor_set(v___x_5811_, 1, v___x_5813_);
v_it_x27_5815_ = v___x_5811_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_fst_5801_);
lean_ctor_set(v_reuseFailAlloc_5824_, 1, v___x_5813_);
v_it_x27_5815_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; 
v___x_5816_ = ((lean_object*)(l_Std_Time_parseModifier___closed__68));
v___x_5817_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(v___x_5816_, v_it_x27_5815_);
if (lean_obj_tag(v___x_5817_) == 0)
{
lean_object* v_pos_5818_; lean_object* v_res_5819_; lean_object* v___x_5820_; 
v_pos_5818_ = lean_ctor_get(v___x_5817_, 0);
lean_inc(v_pos_5818_);
v_res_5819_ = lean_ctor_get(v___x_5817_, 1);
lean_inc(v_res_5819_);
lean_dec_ref_known(v___x_5817_, 2);
v___x_5820_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5797_, v_res_5819_, v_pos_5818_);
if (lean_obj_tag(v___x_5820_) == 0)
{
lean_dec(v_snd_5802_);
return v___x_5820_;
}
else
{
lean_object* v_pos_5821_; 
v_pos_5821_ = lean_ctor_get(v___x_5820_, 0);
lean_inc(v_pos_5821_);
v_snd_5758_ = v_snd_5802_;
v___y_5759_ = v___x_5820_;
v_pos_5760_ = v_pos_5821_;
goto v___jp_5757_;
}
}
else
{
lean_object* v_pos_5822_; lean_object* v_err_5823_; 
v_pos_5822_ = lean_ctor_get(v___x_5817_, 0);
lean_inc(v_pos_5822_);
v_err_5823_ = lean_ctor_get(v___x_5817_, 1);
lean_inc(v_err_5823_);
lean_dec_ref_known(v___x_5817_, 2);
v_snd_5789_ = v_snd_5802_;
v_pos_5790_ = v_pos_5822_;
v_err_5791_ = v_err_5823_;
goto v___jp_5788_;
}
}
}
}
}
}
else
{
v___y_5794_ = v_pos_5800_;
v_snd_5795_ = v_snd_5802_;
goto v___jp_5793_;
}
}
}
v___jp_5828_:
{
lean_object* v___x_5831_; 
lean_inc_ref(v_pos_5829_);
v___x_5831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5831_, 0, v_pos_5829_);
lean_ctor_set(v___x_5831_, 1, v_err_5830_);
v___y_5799_ = v___x_5831_;
v_pos_5800_ = v_pos_5829_;
goto v___jp_5798_;
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
