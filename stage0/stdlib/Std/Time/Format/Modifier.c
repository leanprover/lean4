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
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Time_Text_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Time_Text_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Time_Text_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___redArg(lean_object* v_short_22_){
_start:
{
lean_inc(v_short_22_);
return v_short_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___redArg___boxed(lean_object* v_short_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Time_Text_short_elim___redArg(v_short_23_);
lean_dec(v_short_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_short_28_){
_start:
{
lean_inc(v_short_28_);
return v_short_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_short_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_short_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Time_Text_short_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_short_32_);
lean_dec(v_short_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___redArg(lean_object* v_full_35_){
_start:
{
lean_inc(v_full_35_);
return v_full_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___redArg___boxed(lean_object* v_full_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Time_Text_full_elim___redArg(v_full_36_);
lean_dec(v_full_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_full_41_){
_start:
{
lean_inc(v_full_41_);
return v_full_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_full_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_full_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Time_Text_full_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_full_45_);
lean_dec(v_full_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___redArg(lean_object* v_narrow_48_){
_start:
{
lean_inc(v_narrow_48_);
return v_narrow_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___redArg___boxed(lean_object* v_narrow_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Time_Text_narrow_elim___redArg(v_narrow_49_);
lean_dec(v_narrow_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_narrow_54_){
_start:
{
lean_inc(v_narrow_54_);
return v_narrow_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_narrow_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_narrow_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Std_Time_Text_narrow_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_narrow_58_);
lean_dec(v_narrow_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___redArg(lean_object* v_twoLetterShort_61_){
_start:
{
lean_inc(v_twoLetterShort_61_);
return v_twoLetterShort_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___redArg___boxed(lean_object* v_twoLetterShort_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_Time_Text_twoLetterShort_elim___redArg(v_twoLetterShort_62_);
lean_dec(v_twoLetterShort_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_twoLetterShort_67_){
_start:
{
lean_inc(v_twoLetterShort_67_);
return v_twoLetterShort_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_twoLetterShort_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_twoLetterShort_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Std_Time_Text_twoLetterShort_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_twoLetterShort_71_);
lean_dec(v_twoLetterShort_71_);
return v_res_73_;
}
}
static lean_object* _init_l_Std_Time_instReprText_repr___closed__8(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(2u);
v___x_87_ = lean_nat_to_int(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Std_Time_instReprText_repr___closed__9(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_nat_to_int(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprText_repr(uint8_t v_x_90_, lean_object* v_prec_91_){
_start:
{
lean_object* v___y_93_; lean_object* v___y_100_; lean_object* v___y_107_; lean_object* v___y_114_; 
switch(v_x_90_)
{
case 0:
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1024u);
v___x_121_ = lean_nat_dec_le(v___x_120_, v_prec_91_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_93_ = v___x_122_;
goto v___jp_92_;
}
else
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_93_ = v___x_123_;
goto v___jp_92_;
}
}
case 1:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1024u);
v___x_125_ = lean_nat_dec_le(v___x_124_, v_prec_91_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_100_ = v___x_126_;
goto v___jp_99_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_100_ = v___x_127_;
goto v___jp_99_;
}
}
case 2:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(1024u);
v___x_129_ = lean_nat_dec_le(v___x_128_, v_prec_91_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_107_ = v___x_130_;
goto v___jp_106_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_107_ = v___x_131_;
goto v___jp_106_;
}
}
default: 
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1024u);
v___x_133_ = lean_nat_dec_le(v___x_132_, v_prec_91_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_114_ = v___x_134_;
goto v___jp_113_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_114_ = v___x_135_;
goto v___jp_113_;
}
}
}
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_94_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__1));
lean_inc(v___y_93_);
v___x_95_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_95_, 0, v___y_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = 0;
v___x_97_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_96_);
v___x_98_ = l_Repr_addAppParen(v___x_97_, v_prec_91_);
return v___x_98_;
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_101_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__3));
lean_inc(v___y_100_);
v___x_102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_102_, 0, v___y_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = 0;
v___x_104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*1, v___x_103_);
v___x_105_ = l_Repr_addAppParen(v___x_104_, v_prec_91_);
return v___x_105_;
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_108_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__5));
lean_inc(v___y_107_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___y_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
v___x_112_ = l_Repr_addAppParen(v___x_111_, v_prec_91_);
return v___x_112_;
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_115_ = ((lean_object*)(l_Std_Time_instReprText_repr___closed__7));
lean_inc(v___y_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___y_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
v___x_119_ = l_Repr_addAppParen(v___x_118_, v_prec_91_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprText_repr___boxed(lean_object* v_x_136_, lean_object* v_prec_137_){
_start:
{
uint8_t v_x_225__boxed_138_; lean_object* v_res_139_; 
v_x_225__boxed_138_ = lean_unbox(v_x_136_);
v_res_139_ = l_Std_Time_instReprText_repr(v_x_225__boxed_138_, v_prec_137_);
lean_dec(v_prec_137_);
return v_res_139_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedText_default(void){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedText(void){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_classify(lean_object* v_num_153_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(4u);
v___x_155_ = lean_nat_dec_lt(v_num_153_, v___x_154_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_eq(v_num_153_, v___x_154_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(5u);
v___x_158_ = lean_nat_dec_eq(v_num_153_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = ((lean_object*)(l_Std_Time_Text_classify___closed__0));
return v___x_160_;
}
}
else
{
lean_object* v___x_161_; 
v___x_161_ = ((lean_object*)(l_Std_Time_Text_classify___closed__1));
return v___x_161_;
}
}
else
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Std_Time_Text_classify___closed__2));
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Text_classify___boxed(lean_object* v_num_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Time_Text_classify(v_num_163_);
lean_dec(v_num_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprNumber_repr_spec__0(lean_object* v_a_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_nat_to_int(v_a_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Std_Time_instReprNumber_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(11u);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Std_Time_instReprNumber_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__0));
v___x_184_ = lean_string_length(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_Std_Time_instReprNumber_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_obj_once(&l_Std_Time_instReprNumber_repr___redArg___closed__9, &l_Std_Time_instReprNumber_repr___redArg___closed__9_once, _init_l_Std_Time_instReprNumber_repr___redArg___closed__9);
v___x_186_ = lean_nat_to_int(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr___redArg(lean_object* v_x_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_192_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__6));
v___x_193_ = lean_obj_once(&l_Std_Time_instReprNumber_repr___redArg___closed__7, &l_Std_Time_instReprNumber_repr___redArg___closed__7_once, _init_l_Std_Time_instReprNumber_repr___redArg___closed__7);
v___x_194_ = l_Nat_reprFast(v_x_191_);
v___x_195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
v___x_196_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_193_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = 0;
v___x_198_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_197_);
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_192_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_obj_once(&l_Std_Time_instReprNumber_repr___redArg___closed__10, &l_Std_Time_instReprNumber_repr___redArg___closed__10_once, _init_l_Std_Time_instReprNumber_repr___redArg___closed__10);
v___x_201_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__11));
v___x_202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_199_);
v___x_203_ = ((lean_object*)(l_Std_Time_instReprNumber_repr___redArg___closed__12));
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_200_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_197_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr(lean_object* v_x_207_, lean_object* v_prec_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_Time_instReprNumber_repr___redArg(v_x_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprNumber_repr___boxed(lean_object* v_x_210_, lean_object* v_prec_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Std_Time_instReprNumber_repr(v_x_210_, v_prec_211_);
lean_dec(v_prec_211_);
return v_res_212_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedNumber_default(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_unsigned_to_nat(0u);
return v___x_215_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedNumber(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_unsigned_to_nat(0u);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyNumberText(lean_object* v_x_217_){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(3u);
v___x_219_ = lean_nat_dec_lt(v_x_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = l_Std_Time_Text_classify(v_x_217_);
lean_dec(v_x_217_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v_val_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_230_; 
v_val_222_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_230_ == 0)
{
v___x_224_ = v___x_220_;
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_val_222_);
lean_dec(v___x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v_val_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_226_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v_x_217_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx___impl(lean_object* v_x_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_tag_nat(v_x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorIdx___impl___boxed(lean_object* v_x_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Time_Fraction_ctorIdx___impl(v_x_235_);
lean_dec(v_x_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim___redArg(lean_object* v_t_237_, lean_object* v_k_238_){
_start:
{
if (lean_obj_tag(v_t_237_) == 0)
{
return v_k_238_;
}
else
{
lean_object* v_digits_239_; lean_object* v___x_240_; 
v_digits_239_ = lean_ctor_get(v_t_237_, 0);
lean_inc(v_digits_239_);
lean_dec_ref_known(v_t_237_, 1);
v___x_240_ = lean_apply_1(v_k_238_, v_digits_239_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim(lean_object* v_motive_241_, lean_object* v_ctorIdx_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_k_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_243_, v_k_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_ctorElim___boxed(lean_object* v_motive_247_, lean_object* v_ctorIdx_248_, lean_object* v_t_249_, lean_object* v_h_250_, lean_object* v_k_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_Time_Fraction_ctorElim(v_motive_247_, v_ctorIdx_248_, v_t_249_, v_h_250_, v_k_251_);
lean_dec(v_ctorIdx_248_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_nano_elim___redArg(lean_object* v_t_253_, lean_object* v_nano_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_253_, v_nano_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_nano_elim(lean_object* v_motive_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_nano_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_257_, v_nano_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_truncated_elim___redArg(lean_object* v_t_261_, lean_object* v_truncated_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_261_, v_truncated_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_truncated_elim(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_truncated_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_Time_Fraction_ctorElim___redArg(v_t_265_, v_truncated_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFraction_repr(lean_object* v_x_278_, lean_object* v_prec_279_){
_start:
{
lean_object* v___y_281_; 
if (lean_obj_tag(v_x_278_) == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(1024u);
v___x_288_ = lean_nat_dec_le(v___x_287_, v_prec_279_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
v___x_289_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_281_ = v___x_289_;
goto v___jp_280_;
}
else
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_281_ = v___x_290_;
goto v___jp_280_;
}
}
else
{
lean_object* v_digits_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_311_; 
v_digits_291_ = lean_ctor_get(v_x_278_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_278_);
if (v_isSharedCheck_311_ == 0)
{
v___x_293_ = v_x_278_;
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_digits_291_);
lean_dec(v_x_278_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___y_296_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(1024u);
v___x_308_ = lean_nat_dec_le(v___x_307_, v_prec_279_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_296_ = v___x_309_;
goto v___jp_295_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_296_ = v___x_310_;
goto v___jp_295_;
}
v___jp_295_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_297_ = ((lean_object*)(l_Std_Time_instReprFraction_repr___closed__4));
v___x_298_ = l_Nat_reprFast(v_digits_291_);
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 3);
lean_ctor_set(v___x_293_, 0, v___x_298_);
v___x_300_ = v___x_293_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_306_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_297_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
lean_inc(v___y_296_);
v___x_302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_302_, 0, v___y_296_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = 0;
v___x_304_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*1, v___x_303_);
v___x_305_ = l_Repr_addAppParen(v___x_304_, v_prec_279_);
return v___x_305_;
}
}
}
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_282_ = ((lean_object*)(l_Std_Time_instReprFraction_repr___closed__1));
lean_inc(v___y_281_);
v___x_283_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_283_, 0, v___y_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = 0;
v___x_285_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*1, v___x_284_);
v___x_286_ = l_Repr_addAppParen(v___x_285_, v_prec_279_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFraction_repr___boxed(lean_object* v_x_312_, lean_object* v_prec_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Time_instReprFraction_repr(v_x_312_, v_prec_313_);
lean_dec(v_prec_313_);
return v_res_314_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFraction_default(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_box(0);
return v___x_317_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFraction(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Fraction_classify(lean_object* v_nat_321_){
_start:
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(9u);
v___x_323_ = lean_nat_dec_lt(v_nat_321_, v___x_322_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; 
v___x_324_ = lean_nat_dec_eq(v_nat_321_, v___x_322_);
lean_dec(v_nat_321_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(0);
return v___x_325_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = ((lean_object*)(l_Std_Time_Fraction_classify___closed__0));
return v___x_326_;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v_nat_321_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx___impl(lean_object* v_x_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_tag_nat(v_x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorIdx___impl___boxed(lean_object* v_x_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Time_Year_ctorIdx___impl(v_x_331_);
lean_dec(v_x_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim___redArg(lean_object* v_t_333_, lean_object* v_k_334_){
_start:
{
if (lean_obj_tag(v_t_333_) == 3)
{
lean_object* v_num_335_; lean_object* v___x_336_; 
v_num_335_ = lean_ctor_get(v_t_333_, 0);
lean_inc(v_num_335_);
lean_dec_ref_known(v_t_333_, 1);
v___x_336_ = lean_apply_1(v_k_334_, v_num_335_);
return v___x_336_;
}
else
{
lean_dec(v_t_333_);
return v_k_334_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim(lean_object* v_motive_337_, lean_object* v_ctorIdx_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_k_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Std_Time_Year_ctorElim___redArg(v_t_339_, v_k_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_ctorElim___boxed(lean_object* v_motive_343_, lean_object* v_ctorIdx_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_k_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Time_Year_ctorElim(v_motive_343_, v_ctorIdx_344_, v_t_345_, v_h_346_, v_k_347_);
lean_dec(v_ctorIdx_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_any_elim___redArg(lean_object* v_t_349_, lean_object* v_any_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_Time_Year_ctorElim___redArg(v_t_349_, v_any_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_any_elim(lean_object* v_motive_352_, lean_object* v_t_353_, lean_object* v_h_354_, lean_object* v_any_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_Time_Year_ctorElim___redArg(v_t_353_, v_any_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_twoDigit_elim___redArg(lean_object* v_t_357_, lean_object* v_twoDigit_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_Time_Year_ctorElim___redArg(v_t_357_, v_twoDigit_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_twoDigit_elim(lean_object* v_motive_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_twoDigit_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_Time_Year_ctorElim___redArg(v_t_361_, v_twoDigit_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_fourDigit_elim___redArg(lean_object* v_t_365_, lean_object* v_fourDigit_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Std_Time_Year_ctorElim___redArg(v_t_365_, v_fourDigit_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_fourDigit_elim(lean_object* v_motive_368_, lean_object* v_t_369_, lean_object* v_h_370_, lean_object* v_fourDigit_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Std_Time_Year_ctorElim___redArg(v_t_369_, v_fourDigit_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_extended_elim___redArg(lean_object* v_t_373_, lean_object* v_extended_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Std_Time_Year_ctorElim___redArg(v_t_373_, v_extended_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_extended_elim(lean_object* v_motive_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_extended_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_Time_Year_ctorElim___redArg(v_t_377_, v_extended_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprYear_repr(lean_object* v_x_396_, lean_object* v_prec_397_){
_start:
{
lean_object* v___y_399_; lean_object* v___y_406_; lean_object* v___y_413_; 
switch(lean_obj_tag(v_x_396_))
{
case 0:
{
lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_419_ = lean_unsigned_to_nat(1024u);
v___x_420_ = lean_nat_dec_le(v___x_419_, v_prec_397_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
v___x_421_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_413_ = v___x_421_;
goto v___jp_412_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_413_ = v___x_422_;
goto v___jp_412_;
}
}
case 1:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_unsigned_to_nat(1024u);
v___x_424_ = lean_nat_dec_le(v___x_423_, v_prec_397_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_406_ = v___x_425_;
goto v___jp_405_;
}
else
{
lean_object* v___x_426_; 
v___x_426_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_406_ = v___x_426_;
goto v___jp_405_;
}
}
case 2:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(1024u);
v___x_428_ = lean_nat_dec_le(v___x_427_, v_prec_397_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_399_ = v___x_429_;
goto v___jp_398_;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_399_ = v___x_430_;
goto v___jp_398_;
}
}
default: 
{
lean_object* v_num_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_451_; 
v_num_431_ = lean_ctor_get(v_x_396_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v_x_396_);
if (v_isSharedCheck_451_ == 0)
{
v___x_433_ = v_x_396_;
v_isShared_434_ = v_isSharedCheck_451_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_num_431_);
lean_dec(v_x_396_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_451_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___y_436_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_unsigned_to_nat(1024u);
v___x_448_ = lean_nat_dec_le(v___x_447_, v_prec_397_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
v___x_449_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_436_ = v___x_449_;
goto v___jp_435_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_436_ = v___x_450_;
goto v___jp_435_;
}
v___jp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_437_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__8));
v___x_438_ = l_Nat_reprFast(v_num_431_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_438_);
v___x_440_ = v___x_433_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_446_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_437_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
lean_inc(v___y_436_);
v___x_442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_442_, 0, v___y_436_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = 0;
v___x_444_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*1, v___x_443_);
v___x_445_ = l_Repr_addAppParen(v___x_444_, v_prec_397_);
return v___x_445_;
}
}
}
}
}
v___jp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_400_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__1));
lean_inc(v___y_399_);
v___x_401_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_401_, 0, v___y_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = 0;
v___x_403_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v___x_402_);
v___x_404_ = l_Repr_addAppParen(v___x_403_, v_prec_397_);
return v___x_404_;
}
v___jp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_407_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__3));
lean_inc(v___y_406_);
v___x_408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_408_, 0, v___y_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = 0;
v___x_410_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*1, v___x_409_);
v___x_411_ = l_Repr_addAppParen(v___x_410_, v_prec_397_);
return v___x_411_;
}
v___jp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_414_ = ((lean_object*)(l_Std_Time_instReprYear_repr___closed__5));
lean_inc(v___y_413_);
v___x_415_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_415_, 0, v___y_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = 0;
v___x_417_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_416_);
v___x_418_ = l_Repr_addAppParen(v___x_417_, v_prec_397_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprYear_repr___boxed(lean_object* v_x_452_, lean_object* v_prec_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Time_instReprYear_repr(v_x_452_, v_prec_453_);
lean_dec(v_prec_453_);
return v_res_454_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedYear_default(void){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
return v___x_457_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedYear(void){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Year_classify(lean_object* v_num_465_){
_start:
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_dec_eq(v_num_465_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(2u);
v___x_472_ = lean_nat_dec_eq(v_num_465_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(4u);
v___x_474_ = lean_nat_dec_eq(v_num_465_, v___x_473_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; 
v___x_475_ = lean_nat_dec_lt(v___x_473_, v_num_465_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(3u);
v___x_477_ = lean_nat_dec_eq(v_num_465_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec(v_num_465_);
v___x_478_ = lean_box(0);
return v___x_478_;
}
else
{
goto v___jp_466_;
}
}
else
{
goto v___jp_466_;
}
}
else
{
lean_object* v___x_479_; 
lean_dec(v_num_465_);
v___x_479_ = ((lean_object*)(l_Std_Time_Year_classify___closed__0));
return v___x_479_;
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v_num_465_);
v___x_480_ = ((lean_object*)(l_Std_Time_Year_classify___closed__1));
return v___x_480_;
}
}
else
{
lean_object* v___x_481_; 
lean_dec(v_num_465_);
v___x_481_ = ((lean_object*)(l_Std_Time_Year_classify___closed__2));
return v___x_481_;
}
v___jp_466_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_467_, 0, v_num_465_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx___impl(uint8_t v_x_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_box(v_x_482_);
v___x_484_ = lean_obj_tag_nat(v___x_483_);
lean_dec(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorIdx___impl___boxed(lean_object* v_x_485_){
_start:
{
uint8_t v_x_4__boxed_486_; lean_object* v_res_487_; 
v_x_4__boxed_486_ = lean_unbox(v_x_485_);
v_res_487_ = l_Std_Time_ZoneId_ctorIdx___impl(v_x_4__boxed_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___redArg(lean_object* v_k_488_){
_start:
{
lean_inc(v_k_488_);
return v_k_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___redArg___boxed(lean_object* v_k_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_Time_ZoneId_ctorElim___redArg(v_k_489_);
lean_dec(v_k_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim(lean_object* v_motive_491_, lean_object* v_ctorIdx_492_, uint8_t v_t_493_, lean_object* v_h_494_, lean_object* v_k_495_){
_start:
{
lean_inc(v_k_495_);
return v_k_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_ctorElim___boxed(lean_object* v_motive_496_, lean_object* v_ctorIdx_497_, lean_object* v_t_498_, lean_object* v_h_499_, lean_object* v_k_500_){
_start:
{
uint8_t v_t_boxed_501_; lean_object* v_res_502_; 
v_t_boxed_501_ = lean_unbox(v_t_498_);
v_res_502_ = l_Std_Time_ZoneId_ctorElim(v_motive_496_, v_ctorIdx_497_, v_t_boxed_501_, v_h_499_, v_k_500_);
lean_dec(v_k_500_);
lean_dec(v_ctorIdx_497_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg(lean_object* v_unknown_503_){
_start:
{
lean_inc(v_unknown_503_);
return v_unknown_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___redArg___boxed(lean_object* v_unknown_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_Time_ZoneId_unknown_elim___redArg(v_unknown_504_);
lean_dec(v_unknown_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim(lean_object* v_motive_506_, uint8_t v_t_507_, lean_object* v_h_508_, lean_object* v_unknown_509_){
_start:
{
lean_inc(v_unknown_509_);
return v_unknown_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_unknown_elim___boxed(lean_object* v_motive_510_, lean_object* v_t_511_, lean_object* v_h_512_, lean_object* v_unknown_513_){
_start:
{
uint8_t v_t_boxed_514_; lean_object* v_res_515_; 
v_t_boxed_514_ = lean_unbox(v_t_511_);
v_res_515_ = l_Std_Time_ZoneId_unknown_elim(v_motive_510_, v_t_boxed_514_, v_h_512_, v_unknown_513_);
lean_dec(v_unknown_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg(lean_object* v_short_516_){
_start:
{
lean_inc(v_short_516_);
return v_short_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___redArg___boxed(lean_object* v_short_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Time_ZoneId_short_elim___redArg(v_short_517_);
lean_dec(v_short_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim(lean_object* v_motive_519_, uint8_t v_t_520_, lean_object* v_h_521_, lean_object* v_short_522_){
_start:
{
lean_inc(v_short_522_);
return v_short_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_short_elim___boxed(lean_object* v_motive_523_, lean_object* v_t_524_, lean_object* v_h_525_, lean_object* v_short_526_){
_start:
{
uint8_t v_t_boxed_527_; lean_object* v_res_528_; 
v_t_boxed_527_ = lean_unbox(v_t_524_);
v_res_528_ = l_Std_Time_ZoneId_short_elim(v_motive_523_, v_t_boxed_527_, v_h_525_, v_short_526_);
lean_dec(v_short_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg(lean_object* v_full_529_){
_start:
{
lean_inc(v_full_529_);
return v_full_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___redArg___boxed(lean_object* v_full_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Time_ZoneId_full_elim___redArg(v_full_530_);
lean_dec(v_full_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim(lean_object* v_motive_532_, uint8_t v_t_533_, lean_object* v_h_534_, lean_object* v_full_535_){
_start:
{
lean_inc(v_full_535_);
return v_full_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_full_elim___boxed(lean_object* v_motive_536_, lean_object* v_t_537_, lean_object* v_h_538_, lean_object* v_full_539_){
_start:
{
uint8_t v_t_boxed_540_; lean_object* v_res_541_; 
v_t_boxed_540_ = lean_unbox(v_t_537_);
v_res_541_ = l_Std_Time_ZoneId_full_elim(v_motive_536_, v_t_boxed_540_, v_h_538_, v_full_539_);
lean_dec(v_full_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr(uint8_t v_x_551_, lean_object* v_prec_552_){
_start:
{
lean_object* v___y_554_; lean_object* v___y_561_; lean_object* v___y_568_; 
switch(v_x_551_)
{
case 0:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(1024u);
v___x_575_ = lean_nat_dec_le(v___x_574_, v_prec_552_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_554_ = v___x_576_;
goto v___jp_553_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_554_ = v___x_577_;
goto v___jp_553_;
}
}
case 1:
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1024u);
v___x_579_ = lean_nat_dec_le(v___x_578_, v_prec_552_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_561_ = v___x_580_;
goto v___jp_560_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_561_ = v___x_581_;
goto v___jp_560_;
}
}
default: 
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1024u);
v___x_583_ = lean_nat_dec_le(v___x_582_, v_prec_552_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_568_ = v___x_584_;
goto v___jp_567_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_568_ = v___x_585_;
goto v___jp_567_;
}
}
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_555_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__1));
lean_inc(v___y_554_);
v___x_556_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_556_, 0, v___y_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = 0;
v___x_558_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*1, v___x_557_);
v___x_559_ = l_Repr_addAppParen(v___x_558_, v_prec_552_);
return v___x_559_;
}
v___jp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_562_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__3));
lean_inc(v___y_561_);
v___x_563_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_563_, 0, v___y_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = 0;
v___x_565_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*1, v___x_564_);
v___x_566_ = l_Repr_addAppParen(v___x_565_, v_prec_552_);
return v___x_566_;
}
v___jp_567_:
{
lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_569_ = ((lean_object*)(l_Std_Time_instReprZoneId_repr___closed__5));
lean_inc(v___y_568_);
v___x_570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = 0;
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_571_);
v___x_573_ = l_Repr_addAppParen(v___x_572_, v_prec_552_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneId_repr___boxed(lean_object* v_x_586_, lean_object* v_prec_587_){
_start:
{
uint8_t v_x_167__boxed_588_; lean_object* v_res_589_; 
v_x_167__boxed_588_ = lean_unbox(v_x_586_);
v_res_589_ = l_Std_Time_instReprZoneId_repr(v_x_167__boxed_588_, v_prec_587_);
lean_dec(v_prec_587_);
return v_res_589_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneId_default(void){
_start:
{
uint8_t v___x_592_; 
v___x_592_ = 0;
return v___x_592_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneId(void){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = 0;
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify(lean_object* v_num_603_){
_start:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_dec_eq(v_num_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(2u);
v___x_607_ = lean_nat_dec_eq(v_num_603_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(4u);
v___x_609_ = lean_nat_dec_eq(v_num_603_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = lean_box(0);
return v___x_610_;
}
else
{
lean_object* v___x_611_; 
v___x_611_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__0));
return v___x_611_;
}
}
else
{
lean_object* v___x_612_; 
v___x_612_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__1));
return v___x_612_;
}
}
else
{
lean_object* v___x_613_; 
v___x_613_ = ((lean_object*)(l_Std_Time_ZoneId_classify___closed__2));
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneId_classify___boxed(lean_object* v_num_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Std_Time_ZoneId_classify(v_num_614_);
lean_dec(v_num_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx___impl(uint8_t v_x_616_){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_box(v_x_616_);
v___x_618_ = lean_obj_tag_nat(v___x_617_);
lean_dec(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorIdx___impl___boxed(lean_object* v_x_619_){
_start:
{
uint8_t v_x_4__boxed_620_; lean_object* v_res_621_; 
v_x_4__boxed_620_ = lean_unbox(v_x_619_);
v_res_621_ = l_Std_Time_ZoneName_ctorIdx___impl(v_x_4__boxed_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg(lean_object* v_k_622_){
_start:
{
lean_inc(v_k_622_);
return v_k_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___redArg___boxed(lean_object* v_k_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_Time_ZoneName_ctorElim___redArg(v_k_623_);
lean_dec(v_k_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim(lean_object* v_motive_625_, lean_object* v_ctorIdx_626_, uint8_t v_t_627_, lean_object* v_h_628_, lean_object* v_k_629_){
_start:
{
lean_inc(v_k_629_);
return v_k_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_ctorElim___boxed(lean_object* v_motive_630_, lean_object* v_ctorIdx_631_, lean_object* v_t_632_, lean_object* v_h_633_, lean_object* v_k_634_){
_start:
{
uint8_t v_t_boxed_635_; lean_object* v_res_636_; 
v_t_boxed_635_ = lean_unbox(v_t_632_);
v_res_636_ = l_Std_Time_ZoneName_ctorElim(v_motive_630_, v_ctorIdx_631_, v_t_boxed_635_, v_h_633_, v_k_634_);
lean_dec(v_k_634_);
lean_dec(v_ctorIdx_631_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg(lean_object* v_short_637_){
_start:
{
lean_inc(v_short_637_);
return v_short_637_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___redArg___boxed(lean_object* v_short_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_Time_ZoneName_short_elim___redArg(v_short_638_);
lean_dec(v_short_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim(lean_object* v_motive_640_, uint8_t v_t_641_, lean_object* v_h_642_, lean_object* v_short_643_){
_start:
{
lean_inc(v_short_643_);
return v_short_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_short_elim___boxed(lean_object* v_motive_644_, lean_object* v_t_645_, lean_object* v_h_646_, lean_object* v_short_647_){
_start:
{
uint8_t v_t_boxed_648_; lean_object* v_res_649_; 
v_t_boxed_648_ = lean_unbox(v_t_645_);
v_res_649_ = l_Std_Time_ZoneName_short_elim(v_motive_644_, v_t_boxed_648_, v_h_646_, v_short_647_);
lean_dec(v_short_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg(lean_object* v_full_650_){
_start:
{
lean_inc(v_full_650_);
return v_full_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___redArg___boxed(lean_object* v_full_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_Time_ZoneName_full_elim___redArg(v_full_651_);
lean_dec(v_full_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim(lean_object* v_motive_653_, uint8_t v_t_654_, lean_object* v_h_655_, lean_object* v_full_656_){
_start:
{
lean_inc(v_full_656_);
return v_full_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_full_elim___boxed(lean_object* v_motive_657_, lean_object* v_t_658_, lean_object* v_h_659_, lean_object* v_full_660_){
_start:
{
uint8_t v_t_boxed_661_; lean_object* v_res_662_; 
v_t_boxed_661_ = lean_unbox(v_t_658_);
v_res_662_ = l_Std_Time_ZoneName_full_elim(v_motive_657_, v_t_boxed_661_, v_h_659_, v_full_660_);
lean_dec(v_full_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr(uint8_t v_x_669_, lean_object* v_prec_670_){
_start:
{
lean_object* v___y_672_; lean_object* v___y_679_; 
if (v_x_669_ == 0)
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(1024u);
v___x_686_ = lean_nat_dec_le(v___x_685_, v_prec_670_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_672_ = v___x_687_;
goto v___jp_671_;
}
else
{
lean_object* v___x_688_; 
v___x_688_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_672_ = v___x_688_;
goto v___jp_671_;
}
}
else
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(1024u);
v___x_690_ = lean_nat_dec_le(v___x_689_, v_prec_670_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_679_ = v___x_691_;
goto v___jp_678_;
}
else
{
lean_object* v___x_692_; 
v___x_692_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_679_ = v___x_692_;
goto v___jp_678_;
}
}
v___jp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_673_ = ((lean_object*)(l_Std_Time_instReprZoneName_repr___closed__1));
lean_inc(v___y_672_);
v___x_674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = 0;
v___x_676_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*1, v___x_675_);
v___x_677_ = l_Repr_addAppParen(v___x_676_, v_prec_670_);
return v___x_677_;
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_680_ = ((lean_object*)(l_Std_Time_instReprZoneName_repr___closed__3));
lean_inc(v___y_679_);
v___x_681_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_681_, 0, v___y_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = 0;
v___x_683_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*1, v___x_682_);
v___x_684_ = l_Repr_addAppParen(v___x_683_, v_prec_670_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprZoneName_repr___boxed(lean_object* v_x_693_, lean_object* v_prec_694_){
_start:
{
uint8_t v_x_113__boxed_695_; lean_object* v_res_696_; 
v_x_113__boxed_695_ = lean_unbox(v_x_693_);
v_res_696_ = l_Std_Time_instReprZoneName_repr(v_x_113__boxed_695_, v_prec_694_);
lean_dec(v_prec_694_);
return v_res_696_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneName_default(void){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = 0;
return v___x_699_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedZoneName(void){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = 0;
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify(uint32_t v_letter_707_, lean_object* v_num_708_){
_start:
{
uint32_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = 122;
v___x_710_ = lean_uint32_dec_eq(v_letter_707_, v___x_709_);
if (v___x_710_ == 0)
{
uint32_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = 118;
v___x_712_ = lean_uint32_dec_eq(v_letter_707_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_box(0);
return v___x_713_;
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = lean_nat_dec_eq(v_num_708_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(4u);
v___x_717_ = lean_nat_dec_eq(v_num_708_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
v___x_718_ = lean_box(0);
return v___x_718_;
}
else
{
lean_object* v___x_719_; 
v___x_719_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__0));
return v___x_719_;
}
}
else
{
lean_object* v___x_720_; 
v___x_720_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__1));
return v___x_720_;
}
}
}
else
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(4u);
v___x_722_ = lean_nat_dec_lt(v_num_708_, v___x_721_);
if (v___x_722_ == 0)
{
uint8_t v___x_723_; 
v___x_723_ = lean_nat_dec_eq(v_num_708_, v___x_721_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
v___x_724_ = lean_box(0);
return v___x_724_;
}
else
{
lean_object* v___x_725_; 
v___x_725_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__0));
return v___x_725_;
}
}
else
{
lean_object* v___x_726_; 
v___x_726_ = ((lean_object*)(l_Std_Time_ZoneName_classify___closed__1));
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZoneName_classify___boxed(lean_object* v_letter_727_, lean_object* v_num_728_){
_start:
{
uint32_t v_letter_boxed_729_; lean_object* v_res_730_; 
v_letter_boxed_729_ = lean_unbox_uint32(v_letter_727_);
lean_dec(v_letter_727_);
v_res_730_ = l_Std_Time_ZoneName_classify(v_letter_boxed_729_, v_num_728_);
lean_dec(v_num_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx___impl(uint8_t v_x_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_box(v_x_731_);
v___x_733_ = lean_obj_tag_nat(v___x_732_);
lean_dec(v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorIdx___impl___boxed(lean_object* v_x_734_){
_start:
{
uint8_t v_x_4__boxed_735_; lean_object* v_res_736_; 
v_x_4__boxed_735_ = lean_unbox(v_x_734_);
v_res_736_ = l_Std_Time_OffsetX_ctorIdx___impl(v_x_4__boxed_735_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg(lean_object* v_k_737_){
_start:
{
lean_inc(v_k_737_);
return v_k_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___redArg___boxed(lean_object* v_k_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_Time_OffsetX_ctorElim___redArg(v_k_738_);
lean_dec(v_k_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim(lean_object* v_motive_740_, lean_object* v_ctorIdx_741_, uint8_t v_t_742_, lean_object* v_h_743_, lean_object* v_k_744_){
_start:
{
lean_inc(v_k_744_);
return v_k_744_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_ctorElim___boxed(lean_object* v_motive_745_, lean_object* v_ctorIdx_746_, lean_object* v_t_747_, lean_object* v_h_748_, lean_object* v_k_749_){
_start:
{
uint8_t v_t_boxed_750_; lean_object* v_res_751_; 
v_t_boxed_750_ = lean_unbox(v_t_747_);
v_res_751_ = l_Std_Time_OffsetX_ctorElim(v_motive_745_, v_ctorIdx_746_, v_t_boxed_750_, v_h_748_, v_k_749_);
lean_dec(v_k_749_);
lean_dec(v_ctorIdx_746_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg(lean_object* v_hour_752_){
_start:
{
lean_inc(v_hour_752_);
return v_hour_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___redArg___boxed(lean_object* v_hour_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_Time_OffsetX_hour_elim___redArg(v_hour_753_);
lean_dec(v_hour_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim(lean_object* v_motive_755_, uint8_t v_t_756_, lean_object* v_h_757_, lean_object* v_hour_758_){
_start:
{
lean_inc(v_hour_758_);
return v_hour_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hour_elim___boxed(lean_object* v_motive_759_, lean_object* v_t_760_, lean_object* v_h_761_, lean_object* v_hour_762_){
_start:
{
uint8_t v_t_boxed_763_; lean_object* v_res_764_; 
v_t_boxed_763_ = lean_unbox(v_t_760_);
v_res_764_ = l_Std_Time_OffsetX_hour_elim(v_motive_759_, v_t_boxed_763_, v_h_761_, v_hour_762_);
lean_dec(v_hour_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg(lean_object* v_hourMinute_765_){
_start:
{
lean_inc(v_hourMinute_765_);
return v_hourMinute_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___redArg___boxed(lean_object* v_hourMinute_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_Time_OffsetX_hourMinute_elim___redArg(v_hourMinute_766_);
lean_dec(v_hourMinute_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim(lean_object* v_motive_768_, uint8_t v_t_769_, lean_object* v_h_770_, lean_object* v_hourMinute_771_){
_start:
{
lean_inc(v_hourMinute_771_);
return v_hourMinute_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinute_elim___boxed(lean_object* v_motive_772_, lean_object* v_t_773_, lean_object* v_h_774_, lean_object* v_hourMinute_775_){
_start:
{
uint8_t v_t_boxed_776_; lean_object* v_res_777_; 
v_t_boxed_776_ = lean_unbox(v_t_773_);
v_res_777_ = l_Std_Time_OffsetX_hourMinute_elim(v_motive_772_, v_t_boxed_776_, v_h_774_, v_hourMinute_775_);
lean_dec(v_hourMinute_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(lean_object* v_hourMinuteColon_778_){
_start:
{
lean_inc(v_hourMinuteColon_778_);
return v_hourMinuteColon_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___redArg___boxed(lean_object* v_hourMinuteColon_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_Time_OffsetX_hourMinuteColon_elim___redArg(v_hourMinuteColon_779_);
lean_dec(v_hourMinuteColon_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim(lean_object* v_motive_781_, uint8_t v_t_782_, lean_object* v_h_783_, lean_object* v_hourMinuteColon_784_){
_start:
{
lean_inc(v_hourMinuteColon_784_);
return v_hourMinuteColon_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteColon_elim___boxed(lean_object* v_motive_785_, lean_object* v_t_786_, lean_object* v_h_787_, lean_object* v_hourMinuteColon_788_){
_start:
{
uint8_t v_t_boxed_789_; lean_object* v_res_790_; 
v_t_boxed_789_ = lean_unbox(v_t_786_);
v_res_790_ = l_Std_Time_OffsetX_hourMinuteColon_elim(v_motive_785_, v_t_boxed_789_, v_h_787_, v_hourMinuteColon_788_);
lean_dec(v_hourMinuteColon_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(lean_object* v_hourMinuteSecond_791_){
_start:
{
lean_inc(v_hourMinuteSecond_791_);
return v_hourMinuteSecond_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg___boxed(lean_object* v_hourMinuteSecond_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_Time_OffsetX_hourMinuteSecond_elim___redArg(v_hourMinuteSecond_792_);
lean_dec(v_hourMinuteSecond_792_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim(lean_object* v_motive_794_, uint8_t v_t_795_, lean_object* v_h_796_, lean_object* v_hourMinuteSecond_797_){
_start:
{
lean_inc(v_hourMinuteSecond_797_);
return v_hourMinuteSecond_797_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecond_elim___boxed(lean_object* v_motive_798_, lean_object* v_t_799_, lean_object* v_h_800_, lean_object* v_hourMinuteSecond_801_){
_start:
{
uint8_t v_t_boxed_802_; lean_object* v_res_803_; 
v_t_boxed_802_ = lean_unbox(v_t_799_);
v_res_803_ = l_Std_Time_OffsetX_hourMinuteSecond_elim(v_motive_798_, v_t_boxed_802_, v_h_800_, v_hourMinuteSecond_801_);
lean_dec(v_hourMinuteSecond_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(lean_object* v_hourMinuteSecondColon_804_){
_start:
{
lean_inc(v_hourMinuteSecondColon_804_);
return v_hourMinuteSecondColon_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg___boxed(lean_object* v_hourMinuteSecondColon_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim___redArg(v_hourMinuteSecondColon_805_);
lean_dec(v_hourMinuteSecondColon_805_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim(lean_object* v_motive_807_, uint8_t v_t_808_, lean_object* v_h_809_, lean_object* v_hourMinuteSecondColon_810_){
_start:
{
lean_inc(v_hourMinuteSecondColon_810_);
return v_hourMinuteSecondColon_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_hourMinuteSecondColon_elim___boxed(lean_object* v_motive_811_, lean_object* v_t_812_, lean_object* v_h_813_, lean_object* v_hourMinuteSecondColon_814_){
_start:
{
uint8_t v_t_boxed_815_; lean_object* v_res_816_; 
v_t_boxed_815_ = lean_unbox(v_t_812_);
v_res_816_ = l_Std_Time_OffsetX_hourMinuteSecondColon_elim(v_motive_811_, v_t_boxed_815_, v_h_813_, v_hourMinuteSecondColon_814_);
lean_dec(v_hourMinuteSecondColon_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr(uint8_t v_x_832_, lean_object* v_prec_833_){
_start:
{
lean_object* v___y_835_; lean_object* v___y_842_; lean_object* v___y_849_; lean_object* v___y_856_; lean_object* v___y_863_; 
switch(v_x_832_)
{
case 0:
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = lean_unsigned_to_nat(1024u);
v___x_870_ = lean_nat_dec_le(v___x_869_, v_prec_833_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
v___x_871_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_835_ = v___x_871_;
goto v___jp_834_;
}
else
{
lean_object* v___x_872_; 
v___x_872_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_835_ = v___x_872_;
goto v___jp_834_;
}
}
case 1:
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(1024u);
v___x_874_ = lean_nat_dec_le(v___x_873_, v_prec_833_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; 
v___x_875_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_842_ = v___x_875_;
goto v___jp_841_;
}
else
{
lean_object* v___x_876_; 
v___x_876_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_842_ = v___x_876_;
goto v___jp_841_;
}
}
case 2:
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = lean_unsigned_to_nat(1024u);
v___x_878_ = lean_nat_dec_le(v___x_877_, v_prec_833_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
v___x_879_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_849_ = v___x_879_;
goto v___jp_848_;
}
else
{
lean_object* v___x_880_; 
v___x_880_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_849_ = v___x_880_;
goto v___jp_848_;
}
}
case 3:
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = lean_unsigned_to_nat(1024u);
v___x_882_ = lean_nat_dec_le(v___x_881_, v_prec_833_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_856_ = v___x_883_;
goto v___jp_855_;
}
else
{
lean_object* v___x_884_; 
v___x_884_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_856_ = v___x_884_;
goto v___jp_855_;
}
}
default: 
{
lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_885_ = lean_unsigned_to_nat(1024u);
v___x_886_ = lean_nat_dec_le(v___x_885_, v_prec_833_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
v___x_887_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_863_ = v___x_887_;
goto v___jp_862_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_863_ = v___x_888_;
goto v___jp_862_;
}
}
}
v___jp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_836_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__1));
lean_inc(v___y_835_);
v___x_837_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_837_, 0, v___y_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = 0;
v___x_839_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*1, v___x_838_);
v___x_840_ = l_Repr_addAppParen(v___x_839_, v_prec_833_);
return v___x_840_;
}
v___jp_841_:
{
lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_843_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__3));
lean_inc(v___y_842_);
v___x_844_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_844_, 0, v___y_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = 0;
v___x_846_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*1, v___x_845_);
v___x_847_ = l_Repr_addAppParen(v___x_846_, v_prec_833_);
return v___x_847_;
}
v___jp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_850_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__5));
lean_inc(v___y_849_);
v___x_851_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_851_, 0, v___y_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = 0;
v___x_853_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*1, v___x_852_);
v___x_854_ = l_Repr_addAppParen(v___x_853_, v_prec_833_);
return v___x_854_;
}
v___jp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_857_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__7));
lean_inc(v___y_856_);
v___x_858_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_858_, 0, v___y_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = 0;
v___x_860_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*1, v___x_859_);
v___x_861_ = l_Repr_addAppParen(v___x_860_, v_prec_833_);
return v___x_861_;
}
v___jp_862_:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_864_ = ((lean_object*)(l_Std_Time_instReprOffsetX_repr___closed__9));
lean_inc(v___y_863_);
v___x_865_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_865_, 0, v___y_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = 0;
v___x_867_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*1, v___x_866_);
v___x_868_ = l_Repr_addAppParen(v___x_867_, v_prec_833_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetX_repr___boxed(lean_object* v_x_889_, lean_object* v_prec_890_){
_start:
{
uint8_t v_x_275__boxed_891_; lean_object* v_res_892_; 
v_x_275__boxed_891_ = lean_unbox(v_x_889_);
v_res_892_ = l_Std_Time_instReprOffsetX_repr(v_x_275__boxed_891_, v_prec_890_);
lean_dec(v_prec_890_);
return v_res_892_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetX_default(void){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = 0;
return v___x_895_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetX(void){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = 0;
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify(lean_object* v_num_912_){
_start:
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_nat_dec_eq(v_num_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = lean_unsigned_to_nat(2u);
v___x_916_ = lean_nat_dec_eq(v_num_912_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_917_ = lean_unsigned_to_nat(3u);
v___x_918_ = lean_nat_dec_eq(v_num_912_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_919_ = lean_unsigned_to_nat(4u);
v___x_920_ = lean_nat_dec_eq(v_num_912_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = lean_unsigned_to_nat(5u);
v___x_922_ = lean_nat_dec_eq(v_num_912_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
v___x_923_ = lean_box(0);
return v___x_923_;
}
else
{
lean_object* v___x_924_; 
v___x_924_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__0));
return v___x_924_;
}
}
else
{
lean_object* v___x_925_; 
v___x_925_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__1));
return v___x_925_;
}
}
else
{
lean_object* v___x_926_; 
v___x_926_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__2));
return v___x_926_;
}
}
else
{
lean_object* v___x_927_; 
v___x_927_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__3));
return v___x_927_;
}
}
else
{
lean_object* v___x_928_; 
v___x_928_ = ((lean_object*)(l_Std_Time_OffsetX_classify___closed__4));
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetX_classify___boxed(lean_object* v_num_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Std_Time_OffsetX_classify(v_num_929_);
lean_dec(v_num_929_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx___impl(uint8_t v_x_931_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_box(v_x_931_);
v___x_933_ = lean_obj_tag_nat(v___x_932_);
lean_dec(v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorIdx___impl___boxed(lean_object* v_x_934_){
_start:
{
uint8_t v_x_4__boxed_935_; lean_object* v_res_936_; 
v_x_4__boxed_935_ = lean_unbox(v_x_934_);
v_res_936_ = l_Std_Time_OffsetO_ctorIdx___impl(v_x_4__boxed_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg(lean_object* v_k_937_){
_start:
{
lean_inc(v_k_937_);
return v_k_937_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___redArg___boxed(lean_object* v_k_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_Time_OffsetO_ctorElim___redArg(v_k_938_);
lean_dec(v_k_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim(lean_object* v_motive_940_, lean_object* v_ctorIdx_941_, uint8_t v_t_942_, lean_object* v_h_943_, lean_object* v_k_944_){
_start:
{
lean_inc(v_k_944_);
return v_k_944_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_ctorElim___boxed(lean_object* v_motive_945_, lean_object* v_ctorIdx_946_, lean_object* v_t_947_, lean_object* v_h_948_, lean_object* v_k_949_){
_start:
{
uint8_t v_t_boxed_950_; lean_object* v_res_951_; 
v_t_boxed_950_ = lean_unbox(v_t_947_);
v_res_951_ = l_Std_Time_OffsetO_ctorElim(v_motive_945_, v_ctorIdx_946_, v_t_boxed_950_, v_h_948_, v_k_949_);
lean_dec(v_k_949_);
lean_dec(v_ctorIdx_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg(lean_object* v_short_952_){
_start:
{
lean_inc(v_short_952_);
return v_short_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___redArg___boxed(lean_object* v_short_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_Time_OffsetO_short_elim___redArg(v_short_953_);
lean_dec(v_short_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim(lean_object* v_motive_955_, uint8_t v_t_956_, lean_object* v_h_957_, lean_object* v_short_958_){
_start:
{
lean_inc(v_short_958_);
return v_short_958_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_short_elim___boxed(lean_object* v_motive_959_, lean_object* v_t_960_, lean_object* v_h_961_, lean_object* v_short_962_){
_start:
{
uint8_t v_t_boxed_963_; lean_object* v_res_964_; 
v_t_boxed_963_ = lean_unbox(v_t_960_);
v_res_964_ = l_Std_Time_OffsetO_short_elim(v_motive_959_, v_t_boxed_963_, v_h_961_, v_short_962_);
lean_dec(v_short_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg(lean_object* v_full_965_){
_start:
{
lean_inc(v_full_965_);
return v_full_965_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___redArg___boxed(lean_object* v_full_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Std_Time_OffsetO_full_elim___redArg(v_full_966_);
lean_dec(v_full_966_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim(lean_object* v_motive_968_, uint8_t v_t_969_, lean_object* v_h_970_, lean_object* v_full_971_){
_start:
{
lean_inc(v_full_971_);
return v_full_971_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_full_elim___boxed(lean_object* v_motive_972_, lean_object* v_t_973_, lean_object* v_h_974_, lean_object* v_full_975_){
_start:
{
uint8_t v_t_boxed_976_; lean_object* v_res_977_; 
v_t_boxed_976_ = lean_unbox(v_t_973_);
v_res_977_ = l_Std_Time_OffsetO_full_elim(v_motive_972_, v_t_boxed_976_, v_h_974_, v_full_975_);
lean_dec(v_full_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr(uint8_t v_x_984_, lean_object* v_prec_985_){
_start:
{
lean_object* v___y_987_; lean_object* v___y_994_; 
if (v_x_984_ == 0)
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = lean_unsigned_to_nat(1024u);
v___x_1001_ = lean_nat_dec_le(v___x_1000_, v_prec_985_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_987_ = v___x_1002_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_987_ = v___x_1003_;
goto v___jp_986_;
}
}
else
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_unsigned_to_nat(1024u);
v___x_1005_ = lean_nat_dec_le(v___x_1004_, v_prec_985_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_994_ = v___x_1006_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_994_ = v___x_1007_;
goto v___jp_993_;
}
}
v___jp_986_:
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_988_ = ((lean_object*)(l_Std_Time_instReprOffsetO_repr___closed__1));
lean_inc(v___y_987_);
v___x_989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_989_, 0, v___y_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = 0;
v___x_991_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*1, v___x_990_);
v___x_992_ = l_Repr_addAppParen(v___x_991_, v_prec_985_);
return v___x_992_;
}
v___jp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_995_ = ((lean_object*)(l_Std_Time_instReprOffsetO_repr___closed__3));
lean_inc(v___y_994_);
v___x_996_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_996_, 0, v___y_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = 0;
v___x_998_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*1, v___x_997_);
v___x_999_ = l_Repr_addAppParen(v___x_998_, v_prec_985_);
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetO_repr___boxed(lean_object* v_x_1008_, lean_object* v_prec_1009_){
_start:
{
uint8_t v_x_113__boxed_1010_; lean_object* v_res_1011_; 
v_x_113__boxed_1010_ = lean_unbox(v_x_1008_);
v_res_1011_ = l_Std_Time_instReprOffsetO_repr(v_x_113__boxed_1010_, v_prec_1009_);
lean_dec(v_prec_1009_);
return v_res_1011_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetO_default(void){
_start:
{
uint8_t v___x_1014_; 
v___x_1014_ = 0;
return v___x_1014_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetO(void){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = 0;
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify(lean_object* v_num_1022_){
_start:
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_nat_dec_eq(v_num_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = lean_unsigned_to_nat(4u);
v___x_1026_ = lean_nat_dec_eq(v_num_1022_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_box(0);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; 
v___x_1028_ = ((lean_object*)(l_Std_Time_OffsetO_classify___closed__0));
return v___x_1028_;
}
}
else
{
lean_object* v___x_1029_; 
v___x_1029_ = ((lean_object*)(l_Std_Time_OffsetO_classify___closed__1));
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetO_classify___boxed(lean_object* v_num_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Std_Time_OffsetO_classify(v_num_1030_);
lean_dec(v_num_1030_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx___impl(uint8_t v_x_1032_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_box(v_x_1032_);
v___x_1034_ = lean_obj_tag_nat(v___x_1033_);
lean_dec(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorIdx___impl___boxed(lean_object* v_x_1035_){
_start:
{
uint8_t v_x_4__boxed_1036_; lean_object* v_res_1037_; 
v_x_4__boxed_1036_ = lean_unbox(v_x_1035_);
v_res_1037_ = l_Std_Time_OffsetZ_ctorIdx___impl(v_x_4__boxed_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg(lean_object* v_k_1038_){
_start:
{
lean_inc(v_k_1038_);
return v_k_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___redArg___boxed(lean_object* v_k_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Std_Time_OffsetZ_ctorElim___redArg(v_k_1039_);
lean_dec(v_k_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim(lean_object* v_motive_1041_, lean_object* v_ctorIdx_1042_, uint8_t v_t_1043_, lean_object* v_h_1044_, lean_object* v_k_1045_){
_start:
{
lean_inc(v_k_1045_);
return v_k_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_ctorElim___boxed(lean_object* v_motive_1046_, lean_object* v_ctorIdx_1047_, lean_object* v_t_1048_, lean_object* v_h_1049_, lean_object* v_k_1050_){
_start:
{
uint8_t v_t_boxed_1051_; lean_object* v_res_1052_; 
v_t_boxed_1051_ = lean_unbox(v_t_1048_);
v_res_1052_ = l_Std_Time_OffsetZ_ctorElim(v_motive_1046_, v_ctorIdx_1047_, v_t_boxed_1051_, v_h_1049_, v_k_1050_);
lean_dec(v_k_1050_);
lean_dec(v_ctorIdx_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg(lean_object* v_hourMinute_1053_){
_start:
{
lean_inc(v_hourMinute_1053_);
return v_hourMinute_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___redArg___boxed(lean_object* v_hourMinute_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_Time_OffsetZ_hourMinute_elim___redArg(v_hourMinute_1054_);
lean_dec(v_hourMinute_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim(lean_object* v_motive_1056_, uint8_t v_t_1057_, lean_object* v_h_1058_, lean_object* v_hourMinute_1059_){
_start:
{
lean_inc(v_hourMinute_1059_);
return v_hourMinute_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinute_elim___boxed(lean_object* v_motive_1060_, lean_object* v_t_1061_, lean_object* v_h_1062_, lean_object* v_hourMinute_1063_){
_start:
{
uint8_t v_t_boxed_1064_; lean_object* v_res_1065_; 
v_t_boxed_1064_ = lean_unbox(v_t_1061_);
v_res_1065_ = l_Std_Time_OffsetZ_hourMinute_elim(v_motive_1060_, v_t_boxed_1064_, v_h_1062_, v_hourMinute_1063_);
lean_dec(v_hourMinute_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg(lean_object* v_full_1066_){
_start:
{
lean_inc(v_full_1066_);
return v_full_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___redArg___boxed(lean_object* v_full_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_Time_OffsetZ_full_elim___redArg(v_full_1067_);
lean_dec(v_full_1067_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim(lean_object* v_motive_1069_, uint8_t v_t_1070_, lean_object* v_h_1071_, lean_object* v_full_1072_){
_start:
{
lean_inc(v_full_1072_);
return v_full_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_full_elim___boxed(lean_object* v_motive_1073_, lean_object* v_t_1074_, lean_object* v_h_1075_, lean_object* v_full_1076_){
_start:
{
uint8_t v_t_boxed_1077_; lean_object* v_res_1078_; 
v_t_boxed_1077_ = lean_unbox(v_t_1074_);
v_res_1078_ = l_Std_Time_OffsetZ_full_elim(v_motive_1073_, v_t_boxed_1077_, v_h_1075_, v_full_1076_);
lean_dec(v_full_1076_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(lean_object* v_hourMinuteSecondColon_1079_){
_start:
{
lean_inc(v_hourMinuteSecondColon_1079_);
return v_hourMinuteSecondColon_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg___boxed(lean_object* v_hourMinuteSecondColon_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___redArg(v_hourMinuteSecondColon_1080_);
lean_dec(v_hourMinuteSecondColon_1080_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(lean_object* v_motive_1082_, uint8_t v_t_1083_, lean_object* v_h_1084_, lean_object* v_hourMinuteSecondColon_1085_){
_start:
{
lean_inc(v_hourMinuteSecondColon_1085_);
return v_hourMinuteSecondColon_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_hourMinuteSecondColon_elim___boxed(lean_object* v_motive_1086_, lean_object* v_t_1087_, lean_object* v_h_1088_, lean_object* v_hourMinuteSecondColon_1089_){
_start:
{
uint8_t v_t_boxed_1090_; lean_object* v_res_1091_; 
v_t_boxed_1090_ = lean_unbox(v_t_1087_);
v_res_1091_ = l_Std_Time_OffsetZ_hourMinuteSecondColon_elim(v_motive_1086_, v_t_boxed_1090_, v_h_1088_, v_hourMinuteSecondColon_1089_);
lean_dec(v_hourMinuteSecondColon_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr(uint8_t v_x_1101_, lean_object* v_prec_1102_){
_start:
{
lean_object* v___y_1104_; lean_object* v___y_1111_; lean_object* v___y_1118_; 
switch(v_x_1101_)
{
case 0:
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(1024u);
v___x_1125_ = lean_nat_dec_le(v___x_1124_, v_prec_1102_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1104_ = v___x_1126_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1104_ = v___x_1127_;
goto v___jp_1103_;
}
}
case 1:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_unsigned_to_nat(1024u);
v___x_1129_ = lean_nat_dec_le(v___x_1128_, v_prec_1102_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1111_ = v___x_1130_;
goto v___jp_1110_;
}
else
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1111_ = v___x_1131_;
goto v___jp_1110_;
}
}
default: 
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(1024u);
v___x_1133_ = lean_nat_dec_le(v___x_1132_, v_prec_1102_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1118_ = v___x_1134_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1118_ = v___x_1135_;
goto v___jp_1117_;
}
}
}
v___jp_1103_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1105_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__1));
lean_inc(v___y_1104_);
v___x_1106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___y_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = 0;
v___x_1108_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*1, v___x_1107_);
v___x_1109_ = l_Repr_addAppParen(v___x_1108_, v_prec_1102_);
return v___x_1109_;
}
v___jp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1112_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__3));
lean_inc(v___y_1111_);
v___x_1113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___y_1111_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = 0;
v___x_1115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set_uint8(v___x_1115_, sizeof(void*)*1, v___x_1114_);
v___x_1116_ = l_Repr_addAppParen(v___x_1115_, v_prec_1102_);
return v___x_1116_;
}
v___jp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1119_ = ((lean_object*)(l_Std_Time_instReprOffsetZ_repr___closed__5));
lean_inc(v___y_1118_);
v___x_1120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___y_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = 0;
v___x_1122_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*1, v___x_1121_);
v___x_1123_ = l_Repr_addAppParen(v___x_1122_, v_prec_1102_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprOffsetZ_repr___boxed(lean_object* v_x_1136_, lean_object* v_prec_1137_){
_start:
{
uint8_t v_x_167__boxed_1138_; lean_object* v_res_1139_; 
v_x_167__boxed_1138_ = lean_unbox(v_x_1136_);
v_res_1139_ = l_Std_Time_instReprOffsetZ_repr(v_x_167__boxed_1138_, v_prec_1137_);
lean_dec(v_prec_1137_);
return v_res_1139_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetZ_default(void){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = 0;
return v___x_1142_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedOffsetZ(void){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = 0;
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify(lean_object* v_num_1153_){
_start:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_nat_dec_eq(v_num_1153_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_unsigned_to_nat(2u);
v___x_1159_ = lean_nat_dec_eq(v_num_1153_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = lean_unsigned_to_nat(3u);
v___x_1161_ = lean_nat_dec_eq(v_num_1153_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_unsigned_to_nat(4u);
v___x_1163_ = lean_nat_dec_eq(v_num_1153_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(5u);
v___x_1165_ = lean_nat_dec_eq(v_num_1153_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_box(0);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__1));
return v___x_1167_;
}
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__2));
return v___x_1168_;
}
}
else
{
goto v___jp_1154_;
}
}
else
{
goto v___jp_1154_;
}
}
else
{
goto v___jp_1154_;
}
v___jp_1154_:
{
lean_object* v___x_1155_; 
v___x_1155_ = ((lean_object*)(l_Std_Time_OffsetZ_classify___closed__0));
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_OffsetZ_classify___boxed(lean_object* v_num_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Std_Time_OffsetZ_classify(v_num_1169_);
lean_dec(v_num_1169_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx___impl(uint8_t v_x_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_box(v_x_1171_);
v___x_1173_ = lean_obj_tag_nat(v___x_1172_);
lean_dec(v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorIdx___impl___boxed(lean_object* v_x_1174_){
_start:
{
uint8_t v_x_4__boxed_1175_; lean_object* v_res_1176_; 
v_x_4__boxed_1175_ = lean_unbox(v_x_1174_);
v_res_1176_ = l_Std_Time_DayPeriod_ctorIdx___impl(v_x_4__boxed_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg(lean_object* v_k_1177_){
_start:
{
lean_inc(v_k_1177_);
return v_k_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___redArg___boxed(lean_object* v_k_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Std_Time_DayPeriod_ctorElim___redArg(v_k_1178_);
lean_dec(v_k_1178_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim(lean_object* v_motive_1180_, lean_object* v_ctorIdx_1181_, uint8_t v_t_1182_, lean_object* v_h_1183_, lean_object* v_k_1184_){
_start:
{
lean_inc(v_k_1184_);
return v_k_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_ctorElim___boxed(lean_object* v_motive_1185_, lean_object* v_ctorIdx_1186_, lean_object* v_t_1187_, lean_object* v_h_1188_, lean_object* v_k_1189_){
_start:
{
uint8_t v_t_boxed_1190_; lean_object* v_res_1191_; 
v_t_boxed_1190_ = lean_unbox(v_t_1187_);
v_res_1191_ = l_Std_Time_DayPeriod_ctorElim(v_motive_1185_, v_ctorIdx_1186_, v_t_boxed_1190_, v_h_1188_, v_k_1189_);
lean_dec(v_k_1189_);
lean_dec(v_ctorIdx_1186_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg(lean_object* v_am_1192_){
_start:
{
lean_inc(v_am_1192_);
return v_am_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___redArg___boxed(lean_object* v_am_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_Time_DayPeriod_am_elim___redArg(v_am_1193_);
lean_dec(v_am_1193_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim(lean_object* v_motive_1195_, uint8_t v_t_1196_, lean_object* v_h_1197_, lean_object* v_am_1198_){
_start:
{
lean_inc(v_am_1198_);
return v_am_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_am_elim___boxed(lean_object* v_motive_1199_, lean_object* v_t_1200_, lean_object* v_h_1201_, lean_object* v_am_1202_){
_start:
{
uint8_t v_t_boxed_1203_; lean_object* v_res_1204_; 
v_t_boxed_1203_ = lean_unbox(v_t_1200_);
v_res_1204_ = l_Std_Time_DayPeriod_am_elim(v_motive_1199_, v_t_boxed_1203_, v_h_1201_, v_am_1202_);
lean_dec(v_am_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg(lean_object* v_pm_1205_){
_start:
{
lean_inc(v_pm_1205_);
return v_pm_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___redArg___boxed(lean_object* v_pm_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_Time_DayPeriod_pm_elim___redArg(v_pm_1206_);
lean_dec(v_pm_1206_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim(lean_object* v_motive_1208_, uint8_t v_t_1209_, lean_object* v_h_1210_, lean_object* v_pm_1211_){
_start:
{
lean_inc(v_pm_1211_);
return v_pm_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_pm_elim___boxed(lean_object* v_motive_1212_, lean_object* v_t_1213_, lean_object* v_h_1214_, lean_object* v_pm_1215_){
_start:
{
uint8_t v_t_boxed_1216_; lean_object* v_res_1217_; 
v_t_boxed_1216_ = lean_unbox(v_t_1213_);
v_res_1217_ = l_Std_Time_DayPeriod_pm_elim(v_motive_1212_, v_t_boxed_1216_, v_h_1214_, v_pm_1215_);
lean_dec(v_pm_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg(lean_object* v_noon_1218_){
_start:
{
lean_inc(v_noon_1218_);
return v_noon_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___redArg___boxed(lean_object* v_noon_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_Time_DayPeriod_noon_elim___redArg(v_noon_1219_);
lean_dec(v_noon_1219_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim(lean_object* v_motive_1221_, uint8_t v_t_1222_, lean_object* v_h_1223_, lean_object* v_noon_1224_){
_start:
{
lean_inc(v_noon_1224_);
return v_noon_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_noon_elim___boxed(lean_object* v_motive_1225_, lean_object* v_t_1226_, lean_object* v_h_1227_, lean_object* v_noon_1228_){
_start:
{
uint8_t v_t_boxed_1229_; lean_object* v_res_1230_; 
v_t_boxed_1229_ = lean_unbox(v_t_1226_);
v_res_1230_ = l_Std_Time_DayPeriod_noon_elim(v_motive_1225_, v_t_boxed_1229_, v_h_1227_, v_noon_1228_);
lean_dec(v_noon_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg(lean_object* v_midnight_1231_){
_start:
{
lean_inc(v_midnight_1231_);
return v_midnight_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___redArg___boxed(lean_object* v_midnight_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_Time_DayPeriod_midnight_elim___redArg(v_midnight_1232_);
lean_dec(v_midnight_1232_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim(lean_object* v_motive_1234_, uint8_t v_t_1235_, lean_object* v_h_1236_, lean_object* v_midnight_1237_){
_start:
{
lean_inc(v_midnight_1237_);
return v_midnight_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DayPeriod_midnight_elim___boxed(lean_object* v_motive_1238_, lean_object* v_t_1239_, lean_object* v_h_1240_, lean_object* v_midnight_1241_){
_start:
{
uint8_t v_t_boxed_1242_; lean_object* v_res_1243_; 
v_t_boxed_1242_ = lean_unbox(v_t_1239_);
v_res_1243_ = l_Std_Time_DayPeriod_midnight_elim(v_motive_1238_, v_t_boxed_1242_, v_h_1240_, v_midnight_1241_);
lean_dec(v_midnight_1241_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr(uint8_t v_x_1256_, lean_object* v_prec_1257_){
_start:
{
lean_object* v___y_1259_; lean_object* v___y_1266_; lean_object* v___y_1273_; lean_object* v___y_1280_; 
switch(v_x_1256_)
{
case 0:
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = lean_unsigned_to_nat(1024u);
v___x_1287_ = lean_nat_dec_le(v___x_1286_, v_prec_1257_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1259_ = v___x_1288_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1259_ = v___x_1289_;
goto v___jp_1258_;
}
}
case 1:
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = lean_unsigned_to_nat(1024u);
v___x_1291_ = lean_nat_dec_le(v___x_1290_, v_prec_1257_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1266_ = v___x_1292_;
goto v___jp_1265_;
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1266_ = v___x_1293_;
goto v___jp_1265_;
}
}
case 2:
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = lean_unsigned_to_nat(1024u);
v___x_1295_ = lean_nat_dec_le(v___x_1294_, v_prec_1257_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1273_ = v___x_1296_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1273_ = v___x_1297_;
goto v___jp_1272_;
}
}
default: 
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = lean_unsigned_to_nat(1024u);
v___x_1299_ = lean_nat_dec_le(v___x_1298_, v_prec_1257_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1280_ = v___x_1300_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1280_ = v___x_1301_;
goto v___jp_1279_;
}
}
}
v___jp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1260_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__1));
lean_inc(v___y_1259_);
v___x_1261_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___y_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = 0;
v___x_1263_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*1, v___x_1262_);
v___x_1264_ = l_Repr_addAppParen(v___x_1263_, v_prec_1257_);
return v___x_1264_;
}
v___jp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1267_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__3));
lean_inc(v___y_1266_);
v___x_1268_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___y_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = 0;
v___x_1270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*1, v___x_1269_);
v___x_1271_ = l_Repr_addAppParen(v___x_1270_, v_prec_1257_);
return v___x_1271_;
}
v___jp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1274_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__5));
lean_inc(v___y_1273_);
v___x_1275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___y_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = 0;
v___x_1277_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*1, v___x_1276_);
v___x_1278_ = l_Repr_addAppParen(v___x_1277_, v_prec_1257_);
return v___x_1278_;
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1281_ = ((lean_object*)(l_Std_Time_instReprDayPeriod_repr___closed__7));
lean_inc(v___y_1280_);
v___x_1282_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___y_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = 0;
v___x_1284_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*1, v___x_1283_);
v___x_1285_ = l_Repr_addAppParen(v___x_1284_, v_prec_1257_);
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriod_repr___boxed(lean_object* v_x_1302_, lean_object* v_prec_1303_){
_start:
{
uint8_t v_x_221__boxed_1304_; lean_object* v_res_1305_; 
v_x_221__boxed_1304_ = lean_unbox(v_x_1302_);
v_res_1305_ = l_Std_Time_instReprDayPeriod_repr(v_x_221__boxed_1304_, v_prec_1303_);
lean_dec(v_prec_1303_);
return v_res_1305_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedDayPeriod_default(void){
_start:
{
uint8_t v___x_1308_; 
v___x_1308_ = 0;
return v___x_1308_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedDayPeriod(void){
_start:
{
uint8_t v___x_1309_; 
v___x_1309_ = 0;
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx___impl(uint8_t v_x_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_box(v_x_1310_);
v___x_1312_ = lean_obj_tag_nat(v___x_1311_);
lean_dec(v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorIdx___impl___boxed(lean_object* v_x_1313_){
_start:
{
uint8_t v_x_4__boxed_1314_; lean_object* v_res_1315_; 
v_x_4__boxed_1314_ = lean_unbox(v_x_1313_);
v_res_1315_ = l_Std_Time_ExtendedDayPeriod_ctorIdx___impl(v_x_4__boxed_1314_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(lean_object* v_k_1316_){
_start:
{
lean_inc(v_k_1316_);
return v_k_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___redArg___boxed(lean_object* v_k_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_Time_ExtendedDayPeriod_ctorElim___redArg(v_k_1317_);
lean_dec(v_k_1317_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim(lean_object* v_motive_1319_, lean_object* v_ctorIdx_1320_, uint8_t v_t_1321_, lean_object* v_h_1322_, lean_object* v_k_1323_){
_start:
{
lean_inc(v_k_1323_);
return v_k_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_ctorElim___boxed(lean_object* v_motive_1324_, lean_object* v_ctorIdx_1325_, lean_object* v_t_1326_, lean_object* v_h_1327_, lean_object* v_k_1328_){
_start:
{
uint8_t v_t_boxed_1329_; lean_object* v_res_1330_; 
v_t_boxed_1329_ = lean_unbox(v_t_1326_);
v_res_1330_ = l_Std_Time_ExtendedDayPeriod_ctorElim(v_motive_1324_, v_ctorIdx_1325_, v_t_boxed_1329_, v_h_1327_, v_k_1328_);
lean_dec(v_k_1328_);
lean_dec(v_ctorIdx_1325_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(lean_object* v_midnight_1331_){
_start:
{
lean_inc(v_midnight_1331_);
return v_midnight_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg___boxed(lean_object* v_midnight_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_Time_ExtendedDayPeriod_midnight_elim___redArg(v_midnight_1332_);
lean_dec(v_midnight_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim(lean_object* v_motive_1334_, uint8_t v_t_1335_, lean_object* v_h_1336_, lean_object* v_midnight_1337_){
_start:
{
lean_inc(v_midnight_1337_);
return v_midnight_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_midnight_elim___boxed(lean_object* v_motive_1338_, lean_object* v_t_1339_, lean_object* v_h_1340_, lean_object* v_midnight_1341_){
_start:
{
uint8_t v_t_boxed_1342_; lean_object* v_res_1343_; 
v_t_boxed_1342_ = lean_unbox(v_t_1339_);
v_res_1343_ = l_Std_Time_ExtendedDayPeriod_midnight_elim(v_motive_1338_, v_t_boxed_1342_, v_h_1340_, v_midnight_1341_);
lean_dec(v_midnight_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg(lean_object* v_night_1344_){
_start:
{
lean_inc(v_night_1344_);
return v_night_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___redArg___boxed(lean_object* v_night_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_Time_ExtendedDayPeriod_night_elim___redArg(v_night_1345_);
lean_dec(v_night_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim(lean_object* v_motive_1347_, uint8_t v_t_1348_, lean_object* v_h_1349_, lean_object* v_night_1350_){
_start:
{
lean_inc(v_night_1350_);
return v_night_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_night_elim___boxed(lean_object* v_motive_1351_, lean_object* v_t_1352_, lean_object* v_h_1353_, lean_object* v_night_1354_){
_start:
{
uint8_t v_t_boxed_1355_; lean_object* v_res_1356_; 
v_t_boxed_1355_ = lean_unbox(v_t_1352_);
v_res_1356_ = l_Std_Time_ExtendedDayPeriod_night_elim(v_motive_1351_, v_t_boxed_1355_, v_h_1353_, v_night_1354_);
lean_dec(v_night_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(lean_object* v_morning_1357_){
_start:
{
lean_inc(v_morning_1357_);
return v_morning_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___redArg___boxed(lean_object* v_morning_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Std_Time_ExtendedDayPeriod_morning_elim___redArg(v_morning_1358_);
lean_dec(v_morning_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim(lean_object* v_motive_1360_, uint8_t v_t_1361_, lean_object* v_h_1362_, lean_object* v_morning_1363_){
_start:
{
lean_inc(v_morning_1363_);
return v_morning_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_morning_elim___boxed(lean_object* v_motive_1364_, lean_object* v_t_1365_, lean_object* v_h_1366_, lean_object* v_morning_1367_){
_start:
{
uint8_t v_t_boxed_1368_; lean_object* v_res_1369_; 
v_t_boxed_1368_ = lean_unbox(v_t_1365_);
v_res_1369_ = l_Std_Time_ExtendedDayPeriod_morning_elim(v_motive_1364_, v_t_boxed_1368_, v_h_1366_, v_morning_1367_);
lean_dec(v_morning_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(lean_object* v_noon_1370_){
_start:
{
lean_inc(v_noon_1370_);
return v_noon_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___redArg___boxed(lean_object* v_noon_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Std_Time_ExtendedDayPeriod_noon_elim___redArg(v_noon_1371_);
lean_dec(v_noon_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim(lean_object* v_motive_1373_, uint8_t v_t_1374_, lean_object* v_h_1375_, lean_object* v_noon_1376_){
_start:
{
lean_inc(v_noon_1376_);
return v_noon_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_noon_elim___boxed(lean_object* v_motive_1377_, lean_object* v_t_1378_, lean_object* v_h_1379_, lean_object* v_noon_1380_){
_start:
{
uint8_t v_t_boxed_1381_; lean_object* v_res_1382_; 
v_t_boxed_1381_ = lean_unbox(v_t_1378_);
v_res_1382_ = l_Std_Time_ExtendedDayPeriod_noon_elim(v_motive_1377_, v_t_boxed_1381_, v_h_1379_, v_noon_1380_);
lean_dec(v_noon_1380_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(lean_object* v_afternoon_1383_){
_start:
{
lean_inc(v_afternoon_1383_);
return v_afternoon_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg___boxed(lean_object* v_afternoon_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim___redArg(v_afternoon_1384_);
lean_dec(v_afternoon_1384_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim(lean_object* v_motive_1386_, uint8_t v_t_1387_, lean_object* v_h_1388_, lean_object* v_afternoon_1389_){
_start:
{
lean_inc(v_afternoon_1389_);
return v_afternoon_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_afternoon_elim___boxed(lean_object* v_motive_1390_, lean_object* v_t_1391_, lean_object* v_h_1392_, lean_object* v_afternoon_1393_){
_start:
{
uint8_t v_t_boxed_1394_; lean_object* v_res_1395_; 
v_t_boxed_1394_ = lean_unbox(v_t_1391_);
v_res_1395_ = l_Std_Time_ExtendedDayPeriod_afternoon_elim(v_motive_1390_, v_t_boxed_1394_, v_h_1392_, v_afternoon_1393_);
lean_dec(v_afternoon_1393_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(lean_object* v_evening_1396_){
_start:
{
lean_inc(v_evening_1396_);
return v_evening_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___redArg___boxed(lean_object* v_evening_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Std_Time_ExtendedDayPeriod_evening_elim___redArg(v_evening_1397_);
lean_dec(v_evening_1397_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim(lean_object* v_motive_1399_, uint8_t v_t_1400_, lean_object* v_h_1401_, lean_object* v_evening_1402_){
_start:
{
lean_inc(v_evening_1402_);
return v_evening_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ExtendedDayPeriod_evening_elim___boxed(lean_object* v_motive_1403_, lean_object* v_t_1404_, lean_object* v_h_1405_, lean_object* v_evening_1406_){
_start:
{
uint8_t v_t_boxed_1407_; lean_object* v_res_1408_; 
v_t_boxed_1407_ = lean_unbox(v_t_1404_);
v_res_1408_ = l_Std_Time_ExtendedDayPeriod_evening_elim(v_motive_1403_, v_t_boxed_1407_, v_h_1405_, v_evening_1406_);
lean_dec(v_evening_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr(uint8_t v_x_1427_, lean_object* v_prec_1428_){
_start:
{
lean_object* v___y_1430_; lean_object* v___y_1437_; lean_object* v___y_1444_; lean_object* v___y_1451_; lean_object* v___y_1458_; lean_object* v___y_1465_; 
switch(v_x_1427_)
{
case 0:
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = lean_unsigned_to_nat(1024u);
v___x_1472_ = lean_nat_dec_le(v___x_1471_, v_prec_1428_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1430_ = v___x_1473_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1430_ = v___x_1474_;
goto v___jp_1429_;
}
}
case 1:
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = lean_unsigned_to_nat(1024u);
v___x_1476_ = lean_nat_dec_le(v___x_1475_, v_prec_1428_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1437_ = v___x_1477_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1437_ = v___x_1478_;
goto v___jp_1436_;
}
}
case 2:
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = lean_unsigned_to_nat(1024u);
v___x_1480_ = lean_nat_dec_le(v___x_1479_, v_prec_1428_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1444_ = v___x_1481_;
goto v___jp_1443_;
}
else
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1444_ = v___x_1482_;
goto v___jp_1443_;
}
}
case 3:
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = lean_unsigned_to_nat(1024u);
v___x_1484_ = lean_nat_dec_le(v___x_1483_, v_prec_1428_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1451_ = v___x_1485_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1451_ = v___x_1486_;
goto v___jp_1450_;
}
}
case 4:
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = lean_unsigned_to_nat(1024u);
v___x_1488_ = lean_nat_dec_le(v___x_1487_, v_prec_1428_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1458_ = v___x_1489_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1458_ = v___x_1490_;
goto v___jp_1457_;
}
}
default: 
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = lean_unsigned_to_nat(1024u);
v___x_1492_ = lean_nat_dec_le(v___x_1491_, v_prec_1428_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_1465_ = v___x_1493_;
goto v___jp_1464_;
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_1465_ = v___x_1494_;
goto v___jp_1464_;
}
}
}
v___jp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1431_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__1));
lean_inc(v___y_1430_);
v___x_1432_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___y_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = 0;
v___x_1434_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*1, v___x_1433_);
v___x_1435_ = l_Repr_addAppParen(v___x_1434_, v_prec_1428_);
return v___x_1435_;
}
v___jp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1438_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__3));
lean_inc(v___y_1437_);
v___x_1439_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___y_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = 0;
v___x_1441_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*1, v___x_1440_);
v___x_1442_ = l_Repr_addAppParen(v___x_1441_, v_prec_1428_);
return v___x_1442_;
}
v___jp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1445_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__5));
lean_inc(v___y_1444_);
v___x_1446_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___y_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = 0;
v___x_1448_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*1, v___x_1447_);
v___x_1449_ = l_Repr_addAppParen(v___x_1448_, v_prec_1428_);
return v___x_1449_;
}
v___jp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1452_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__7));
lean_inc(v___y_1451_);
v___x_1453_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___y_1451_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = 0;
v___x_1455_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set_uint8(v___x_1455_, sizeof(void*)*1, v___x_1454_);
v___x_1456_ = l_Repr_addAppParen(v___x_1455_, v_prec_1428_);
return v___x_1456_;
}
v___jp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1459_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__9));
lean_inc(v___y_1458_);
v___x_1460_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___y_1458_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = 0;
v___x_1462_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set_uint8(v___x_1462_, sizeof(void*)*1, v___x_1461_);
v___x_1463_ = l_Repr_addAppParen(v___x_1462_, v_prec_1428_);
return v___x_1463_;
}
v___jp_1464_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1466_ = ((lean_object*)(l_Std_Time_instReprExtendedDayPeriod_repr___closed__11));
lean_inc(v___y_1465_);
v___x_1467_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = 0;
v___x_1469_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set_uint8(v___x_1469_, sizeof(void*)*1, v___x_1468_);
v___x_1470_ = l_Repr_addAppParen(v___x_1469_, v_prec_1428_);
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprExtendedDayPeriod_repr___boxed(lean_object* v_x_1495_, lean_object* v_prec_1496_){
_start:
{
uint8_t v_x_329__boxed_1497_; lean_object* v_res_1498_; 
v_x_329__boxed_1497_ = lean_unbox(v_x_1495_);
v_res_1498_ = l_Std_Time_instReprExtendedDayPeriod_repr(v_x_329__boxed_1497_, v_prec_1496_);
lean_dec(v_prec_1496_);
return v_res_1498_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedExtendedDayPeriod_default(void){
_start:
{
uint8_t v___x_1501_; 
v___x_1501_ = 0;
return v___x_1501_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedExtendedDayPeriod(void){
_start:
{
uint8_t v___x_1502_; 
v___x_1502_ = 0;
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx___impl(lean_object* v_x_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_obj_tag_nat(v_x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorIdx___impl___boxed(lean_object* v_x_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_Time_Modifier_ctorIdx___impl(v_x_1505_);
lean_dec_ref(v_x_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___redArg(lean_object* v_t_1507_, lean_object* v_k_1508_){
_start:
{
switch(lean_obj_tag(v_t_1507_))
{
case 0:
{
uint8_t v_presentation_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_presentation_1509_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1510_ = lean_box(v_presentation_1509_);
v___x_1511_ = lean_apply_1(v_k_1508_, v___x_1510_);
return v___x_1511_;
}
case 4:
{
lean_object* v_presentation_1512_; lean_object* v___x_1513_; 
v_presentation_1512_ = lean_ctor_get(v_t_1507_, 0);
lean_inc_ref(v_presentation_1512_);
lean_dec_ref_known(v_t_1507_, 1);
v___x_1513_ = lean_apply_1(v_k_1508_, v_presentation_1512_);
return v___x_1513_;
}
case 5:
{
lean_object* v_presentation_1514_; lean_object* v___x_1515_; 
v_presentation_1514_ = lean_ctor_get(v_t_1507_, 0);
lean_inc_ref(v_presentation_1514_);
lean_dec_ref_known(v_t_1507_, 1);
v___x_1515_ = lean_apply_1(v_k_1508_, v_presentation_1514_);
return v___x_1515_;
}
case 7:
{
lean_object* v_presentation_1516_; lean_object* v___x_1517_; 
v_presentation_1516_ = lean_ctor_get(v_t_1507_, 0);
lean_inc_ref(v_presentation_1516_);
lean_dec_ref_known(v_t_1507_, 1);
v___x_1517_ = lean_apply_1(v_k_1508_, v_presentation_1516_);
return v___x_1517_;
}
case 8:
{
lean_object* v_presentation_1518_; lean_object* v___x_1519_; 
v_presentation_1518_ = lean_ctor_get(v_t_1507_, 0);
lean_inc_ref(v_presentation_1518_);
lean_dec_ref_known(v_t_1507_, 1);
v___x_1519_ = lean_apply_1(v_k_1508_, v_presentation_1518_);
return v___x_1519_;
}
case 12:
{
uint8_t v_presentation_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_presentation_1520_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1521_ = lean_box(v_presentation_1520_);
v___x_1522_ = lean_apply_1(v_k_1508_, v___x_1521_);
return v___x_1522_;
}
case 13:
{
lean_object* v_presentation_1523_; lean_object* v___x_1524_; 
v_presentation_1523_ = lean_ctor_get(v_t_1507_, 0);
lean_inc_ref(v_presentation_1523_);
lean_dec_ref_known(v_t_1507_, 1);
v___x_1524_ = lean_apply_1(v_k_1508_, v_presentation_1523_);
return v___x_1524_;
}
case 14:
{
lean_object* v_presentation_1525_; lean_object* v___x_1526_; 
v_presentation_1525_ = lean_ctor_get(v_t_1507_, 0);
lean_inc_ref(v_presentation_1525_);
lean_dec_ref_known(v_t_1507_, 1);
v___x_1526_ = lean_apply_1(v_k_1508_, v_presentation_1525_);
return v___x_1526_;
}
case 16:
{
uint8_t v_presentation_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_presentation_1527_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1528_ = lean_box(v_presentation_1527_);
v___x_1529_ = lean_apply_1(v_k_1508_, v___x_1528_);
return v___x_1529_;
}
case 17:
{
uint8_t v_presentation_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_presentation_1530_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1531_ = lean_box(v_presentation_1530_);
v___x_1532_ = lean_apply_1(v_k_1508_, v___x_1531_);
return v___x_1532_;
}
case 18:
{
uint8_t v_presentation_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_presentation_1533_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1534_ = lean_box(v_presentation_1533_);
v___x_1535_ = lean_apply_1(v_k_1508_, v___x_1534_);
return v___x_1535_;
}
case 29:
{
uint8_t v_presentation_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_presentation_1536_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1537_ = lean_box(v_presentation_1536_);
v___x_1538_ = lean_apply_1(v_k_1508_, v___x_1537_);
return v___x_1538_;
}
case 30:
{
uint8_t v_presentation_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_presentation_1539_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1540_ = lean_box(v_presentation_1539_);
v___x_1541_ = lean_apply_1(v_k_1508_, v___x_1540_);
return v___x_1541_;
}
case 31:
{
uint8_t v_presentation_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_presentation_1542_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1543_ = lean_box(v_presentation_1542_);
v___x_1544_ = lean_apply_1(v_k_1508_, v___x_1543_);
return v___x_1544_;
}
case 32:
{
uint8_t v_presentation_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_presentation_1545_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1546_ = lean_box(v_presentation_1545_);
v___x_1547_ = lean_apply_1(v_k_1508_, v___x_1546_);
return v___x_1547_;
}
case 33:
{
uint8_t v_presentation_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_presentation_1548_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1549_ = lean_box(v_presentation_1548_);
v___x_1550_ = lean_apply_1(v_k_1508_, v___x_1549_);
return v___x_1550_;
}
case 34:
{
uint8_t v_presentation_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_presentation_1551_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1552_ = lean_box(v_presentation_1551_);
v___x_1553_ = lean_apply_1(v_k_1508_, v___x_1552_);
return v___x_1553_;
}
case 35:
{
uint8_t v_presentation_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_presentation_1554_ = lean_ctor_get_uint8(v_t_1507_, 0);
lean_dec_ref_known(v_t_1507_, 0);
v___x_1555_ = lean_box(v_presentation_1554_);
v___x_1556_ = lean_apply_1(v_k_1508_, v___x_1555_);
return v___x_1556_;
}
default: 
{
lean_object* v_presentation_1557_; lean_object* v___x_1558_; 
v_presentation_1557_ = lean_ctor_get(v_t_1507_, 0);
lean_inc(v_presentation_1557_);
lean_dec_ref(v_t_1507_);
v___x_1558_ = lean_apply_1(v_k_1508_, v_presentation_1557_);
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim(lean_object* v_motive_1559_, lean_object* v_ctorIdx_1560_, lean_object* v_t_1561_, lean_object* v_h_1562_, lean_object* v_k_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1561_, v_k_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_ctorElim___boxed(lean_object* v_motive_1565_, lean_object* v_ctorIdx_1566_, lean_object* v_t_1567_, lean_object* v_h_1568_, lean_object* v_k_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Std_Time_Modifier_ctorElim(v_motive_1565_, v_ctorIdx_1566_, v_t_1567_, v_h_1568_, v_k_1569_);
lean_dec(v_ctorIdx_1566_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim___redArg(lean_object* v_t_1571_, lean_object* v_G_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1571_, v_G_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_G_elim(lean_object* v_motive_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_G_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1575_, v_G_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim___redArg(lean_object* v_t_1579_, lean_object* v_u_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1579_, v_u_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_u_elim(lean_object* v_motive_1582_, lean_object* v_t_1583_, lean_object* v_h_1584_, lean_object* v_u_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1583_, v_u_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim___redArg(lean_object* v_t_1587_, lean_object* v_y_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1587_, v_y_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_y_elim(lean_object* v_motive_1590_, lean_object* v_t_1591_, lean_object* v_h_1592_, lean_object* v_y_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1591_, v_y_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim___redArg(lean_object* v_t_1595_, lean_object* v_D_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1595_, v_D_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_D_elim(lean_object* v_motive_1598_, lean_object* v_t_1599_, lean_object* v_h_1600_, lean_object* v_D_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1599_, v_D_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim___redArg(lean_object* v_t_1603_, lean_object* v_M_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1603_, v_M_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_M_elim(lean_object* v_motive_1606_, lean_object* v_t_1607_, lean_object* v_h_1608_, lean_object* v_M_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1607_, v_M_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim___redArg(lean_object* v_t_1611_, lean_object* v_L_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1611_, v_L_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_L_elim(lean_object* v_motive_1614_, lean_object* v_t_1615_, lean_object* v_h_1616_, lean_object* v_L_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1615_, v_L_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim___redArg(lean_object* v_t_1619_, lean_object* v_d_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1619_, v_d_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_d_elim(lean_object* v_motive_1622_, lean_object* v_t_1623_, lean_object* v_h_1624_, lean_object* v_d_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1623_, v_d_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim___redArg(lean_object* v_t_1627_, lean_object* v_Q_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1627_, v_Q_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Q_elim(lean_object* v_motive_1630_, lean_object* v_t_1631_, lean_object* v_h_1632_, lean_object* v_Q_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1631_, v_Q_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim___redArg(lean_object* v_t_1635_, lean_object* v_q_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1635_, v_q_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_q_elim(lean_object* v_motive_1638_, lean_object* v_t_1639_, lean_object* v_h_1640_, lean_object* v_q_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1639_, v_q_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim___redArg(lean_object* v_t_1643_, lean_object* v_Y_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1643_, v_Y_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Y_elim(lean_object* v_motive_1646_, lean_object* v_t_1647_, lean_object* v_h_1648_, lean_object* v_Y_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1647_, v_Y_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim___redArg(lean_object* v_t_1651_, lean_object* v_w_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1651_, v_w_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_w_elim(lean_object* v_motive_1654_, lean_object* v_t_1655_, lean_object* v_h_1656_, lean_object* v_w_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1655_, v_w_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim___redArg(lean_object* v_t_1659_, lean_object* v_W_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1659_, v_W_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_W_elim(lean_object* v_motive_1662_, lean_object* v_t_1663_, lean_object* v_h_1664_, lean_object* v_W_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1663_, v_W_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim___redArg(lean_object* v_t_1667_, lean_object* v_E_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1667_, v_E_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_E_elim(lean_object* v_motive_1670_, lean_object* v_t_1671_, lean_object* v_h_1672_, lean_object* v_E_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1671_, v_E_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim___redArg(lean_object* v_t_1675_, lean_object* v_e_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1675_, v_e_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_e_elim(lean_object* v_motive_1678_, lean_object* v_t_1679_, lean_object* v_h_1680_, lean_object* v_e_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1679_, v_e_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim___redArg(lean_object* v_t_1683_, lean_object* v_c_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1683_, v_c_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_c_elim(lean_object* v_motive_1686_, lean_object* v_t_1687_, lean_object* v_h_1688_, lean_object* v_c_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1687_, v_c_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim___redArg(lean_object* v_t_1691_, lean_object* v_F_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1691_, v_F_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_F_elim(lean_object* v_motive_1694_, lean_object* v_t_1695_, lean_object* v_h_1696_, lean_object* v_F_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1695_, v_F_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim___redArg(lean_object* v_t_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1699_, v_a_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_a_elim(lean_object* v_motive_1702_, lean_object* v_t_1703_, lean_object* v_h_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1703_, v_a_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim___redArg(lean_object* v_t_1707_, lean_object* v_b_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1707_, v_b_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_b_elim(lean_object* v_motive_1710_, lean_object* v_t_1711_, lean_object* v_h_1712_, lean_object* v_b_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1711_, v_b_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim___redArg(lean_object* v_t_1715_, lean_object* v_B_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1715_, v_B_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_B_elim(lean_object* v_motive_1718_, lean_object* v_t_1719_, lean_object* v_h_1720_, lean_object* v_B_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1719_, v_B_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim___redArg(lean_object* v_t_1723_, lean_object* v_h_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1723_, v_h_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_h_elim(lean_object* v_motive_1726_, lean_object* v_t_1727_, lean_object* v_h_1728_, lean_object* v_h_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1727_, v_h_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim___redArg(lean_object* v_t_1731_, lean_object* v_K_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1731_, v_K_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_K_elim(lean_object* v_motive_1734_, lean_object* v_t_1735_, lean_object* v_h_1736_, lean_object* v_K_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1735_, v_K_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim___redArg(lean_object* v_t_1739_, lean_object* v_k_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1739_, v_k_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_k_elim(lean_object* v_motive_1742_, lean_object* v_t_1743_, lean_object* v_h_1744_, lean_object* v_k_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1743_, v_k_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim___redArg(lean_object* v_t_1747_, lean_object* v_H_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1747_, v_H_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_H_elim(lean_object* v_motive_1750_, lean_object* v_t_1751_, lean_object* v_h_1752_, lean_object* v_H_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1751_, v_H_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim___redArg(lean_object* v_t_1755_, lean_object* v_m_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1755_, v_m_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_m_elim(lean_object* v_motive_1758_, lean_object* v_t_1759_, lean_object* v_h_1760_, lean_object* v_m_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1759_, v_m_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim___redArg(lean_object* v_t_1763_, lean_object* v_s_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1763_, v_s_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_s_elim(lean_object* v_motive_1766_, lean_object* v_t_1767_, lean_object* v_h_1768_, lean_object* v_s_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1767_, v_s_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim___redArg(lean_object* v_t_1771_, lean_object* v_S_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1771_, v_S_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_S_elim(lean_object* v_motive_1774_, lean_object* v_t_1775_, lean_object* v_h_1776_, lean_object* v_S_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1775_, v_S_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim___redArg(lean_object* v_t_1779_, lean_object* v_A_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1779_, v_A_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_A_elim(lean_object* v_motive_1782_, lean_object* v_t_1783_, lean_object* v_h_1784_, lean_object* v_A_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1783_, v_A_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim___redArg(lean_object* v_t_1787_, lean_object* v_n_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1787_, v_n_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_n_elim(lean_object* v_motive_1790_, lean_object* v_t_1791_, lean_object* v_h_1792_, lean_object* v_n_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1791_, v_n_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim___redArg(lean_object* v_t_1795_, lean_object* v_N_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1795_, v_N_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_N_elim(lean_object* v_motive_1798_, lean_object* v_t_1799_, lean_object* v_h_1800_, lean_object* v_N_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1799_, v_N_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim___redArg(lean_object* v_t_1803_, lean_object* v_V_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1803_, v_V_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_V_elim(lean_object* v_motive_1806_, lean_object* v_t_1807_, lean_object* v_h_1808_, lean_object* v_V_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1807_, v_V_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim___redArg(lean_object* v_t_1811_, lean_object* v_z_1812_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1811_, v_z_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_z_elim(lean_object* v_motive_1814_, lean_object* v_t_1815_, lean_object* v_h_1816_, lean_object* v_z_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1815_, v_z_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim___redArg(lean_object* v_t_1819_, lean_object* v_v_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1819_, v_v_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_v_elim(lean_object* v_motive_1822_, lean_object* v_t_1823_, lean_object* v_h_1824_, lean_object* v_v_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1823_, v_v_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim___redArg(lean_object* v_t_1827_, lean_object* v_O_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1827_, v_O_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_O_elim(lean_object* v_motive_1830_, lean_object* v_t_1831_, lean_object* v_h_1832_, lean_object* v_O_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1831_, v_O_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim___redArg(lean_object* v_t_1835_, lean_object* v_X_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1835_, v_X_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_X_elim(lean_object* v_motive_1838_, lean_object* v_t_1839_, lean_object* v_h_1840_, lean_object* v_X_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1839_, v_X_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim___redArg(lean_object* v_t_1843_, lean_object* v_x_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1843_, v_x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_x_elim(lean_object* v_motive_1846_, lean_object* v_t_1847_, lean_object* v_h_1848_, lean_object* v_x_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1847_, v_x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim___redArg(lean_object* v_t_1851_, lean_object* v_Z_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1851_, v_Z_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Modifier_Z_elim(lean_object* v_motive_1854_, lean_object* v_t_1855_, lean_object* v_h_1856_, lean_object* v_Z_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_Time_Modifier_ctorElim___redArg(v_t_1855_, v_Z_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
if (lean_obj_tag(v_x_1865_) == 0)
{
lean_object* v_val_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v_val_1867_ = lean_ctor_get(v_x_1865_, 0);
lean_inc(v_val_1867_);
lean_dec_ref_known(v_x_1865_, 1);
v___x_1868_ = ((lean_object*)(l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__1));
v___x_1869_ = l_Std_Time_instReprNumber_repr___redArg(v_val_1867_);
v___x_1870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Repr_addAppParen(v___x_1870_, v_x_1866_);
return v___x_1871_;
}
else
{
lean_object* v_val_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v_val_1872_ = lean_ctor_get(v_x_1865_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v_x_1865_, 1);
v___x_1873_ = ((lean_object*)(l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___closed__3));
v___x_1874_ = lean_unsigned_to_nat(1024u);
v___x_1875_ = lean_unbox(v_val_1872_);
lean_dec(v_val_1872_);
v___x_1876_ = l_Std_Time_instReprText_repr(v___x_1875_, v___x_1874_);
v___x_1877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1873_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l_Repr_addAppParen(v___x_1877_, v_x_1866_);
return v___x_1878_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0___boxed(lean_object* v_x_1879_, lean_object* v_x_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_x_1879_, v_x_1880_);
lean_dec(v_x_1880_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr(lean_object* v_x_2098_, lean_object* v_prec_2099_){
_start:
{
switch(lean_obj_tag(v_x_2098_))
{
case 0:
{
uint8_t v_presentation_2100_; lean_object* v___y_2102_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v_presentation_2100_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2111_ = lean_unsigned_to_nat(1024u);
v___x_2112_ = lean_nat_dec_le(v___x_2111_, v_prec_2099_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2102_ = v___x_2113_;
goto v___jp_2101_;
}
else
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2102_ = v___x_2114_;
goto v___jp_2101_;
}
v___jp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2103_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__2));
v___x_2104_ = lean_unsigned_to_nat(1024u);
v___x_2105_ = l_Std_Time_instReprText_repr(v_presentation_2100_, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2103_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
lean_inc(v___y_2102_);
v___x_2107_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___y_2102_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = 0;
v___x_2109_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*1, v___x_2108_);
v___x_2110_ = l_Repr_addAppParen(v___x_2109_, v_prec_2099_);
return v___x_2110_;
}
}
case 1:
{
lean_object* v_presentation_2115_; lean_object* v___y_2117_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v_presentation_2115_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2115_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2126_ = lean_unsigned_to_nat(1024u);
v___x_2127_ = lean_nat_dec_le(v___x_2126_, v_prec_2099_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2117_ = v___x_2128_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2117_ = v___x_2129_;
goto v___jp_2116_;
}
v___jp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2118_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__5));
v___x_2119_ = lean_unsigned_to_nat(1024u);
v___x_2120_ = l_Std_Time_instReprYear_repr(v_presentation_2115_, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2118_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
lean_inc(v___y_2117_);
v___x_2122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___y_2117_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = 0;
v___x_2124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*1, v___x_2123_);
v___x_2125_ = l_Repr_addAppParen(v___x_2124_, v_prec_2099_);
return v___x_2125_;
}
}
case 2:
{
lean_object* v_presentation_2130_; lean_object* v___y_2132_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_presentation_2130_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2130_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2141_ = lean_unsigned_to_nat(1024u);
v___x_2142_ = lean_nat_dec_le(v___x_2141_, v_prec_2099_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2132_ = v___x_2143_;
goto v___jp_2131_;
}
else
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2132_ = v___x_2144_;
goto v___jp_2131_;
}
v___jp_2131_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2133_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__8));
v___x_2134_ = lean_unsigned_to_nat(1024u);
v___x_2135_ = l_Std_Time_instReprYear_repr(v_presentation_2130_, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2133_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
lean_inc(v___y_2132_);
v___x_2137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___y_2132_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = 0;
v___x_2139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*1, v___x_2138_);
v___x_2140_ = l_Repr_addAppParen(v___x_2139_, v_prec_2099_);
return v___x_2140_;
}
}
case 3:
{
lean_object* v_presentation_2145_; lean_object* v___y_2147_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v_presentation_2145_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2145_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2155_ = lean_unsigned_to_nat(1024u);
v___x_2156_ = lean_nat_dec_le(v___x_2155_, v_prec_2099_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2147_ = v___x_2157_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2147_ = v___x_2158_;
goto v___jp_2146_;
}
v___jp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2148_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__11));
v___x_2149_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2145_);
v___x_2150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
lean_inc(v___y_2147_);
v___x_2151_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___y_2147_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = 0;
v___x_2153_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*1, v___x_2152_);
v___x_2154_ = l_Repr_addAppParen(v___x_2153_, v_prec_2099_);
return v___x_2154_;
}
}
case 4:
{
lean_object* v_presentation_2159_; lean_object* v___y_2161_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_presentation_2159_ = lean_ctor_get(v_x_2098_, 0);
lean_inc_ref(v_presentation_2159_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2170_ = lean_unsigned_to_nat(1024u);
v___x_2171_ = lean_nat_dec_le(v___x_2170_, v_prec_2099_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; 
v___x_2172_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2161_ = v___x_2172_;
goto v___jp_2160_;
}
else
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2161_ = v___x_2173_;
goto v___jp_2160_;
}
v___jp_2160_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2162_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__14));
v___x_2163_ = lean_unsigned_to_nat(1024u);
v___x_2164_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2159_, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2162_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
lean_inc(v___y_2161_);
v___x_2166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___y_2161_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = 0;
v___x_2168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*1, v___x_2167_);
v___x_2169_ = l_Repr_addAppParen(v___x_2168_, v_prec_2099_);
return v___x_2169_;
}
}
case 5:
{
lean_object* v_presentation_2174_; lean_object* v___y_2176_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_presentation_2174_ = lean_ctor_get(v_x_2098_, 0);
lean_inc_ref(v_presentation_2174_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2185_ = lean_unsigned_to_nat(1024u);
v___x_2186_ = lean_nat_dec_le(v___x_2185_, v_prec_2099_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2176_ = v___x_2187_;
goto v___jp_2175_;
}
else
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2176_ = v___x_2188_;
goto v___jp_2175_;
}
v___jp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2177_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__17));
v___x_2178_ = lean_unsigned_to_nat(1024u);
v___x_2179_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2174_, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2177_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
lean_inc(v___y_2176_);
v___x_2181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___y_2176_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = 0;
v___x_2183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*1, v___x_2182_);
v___x_2184_ = l_Repr_addAppParen(v___x_2183_, v_prec_2099_);
return v___x_2184_;
}
}
case 6:
{
lean_object* v_presentation_2189_; lean_object* v___y_2191_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v_presentation_2189_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2189_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2199_ = lean_unsigned_to_nat(1024u);
v___x_2200_ = lean_nat_dec_le(v___x_2199_, v_prec_2099_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2191_ = v___x_2201_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2191_ = v___x_2202_;
goto v___jp_2190_;
}
v___jp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2192_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__20));
v___x_2193_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2189_);
v___x_2194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
lean_inc(v___y_2191_);
v___x_2195_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___y_2191_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = 0;
v___x_2197_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*1, v___x_2196_);
v___x_2198_ = l_Repr_addAppParen(v___x_2197_, v_prec_2099_);
return v___x_2198_;
}
}
case 7:
{
lean_object* v_presentation_2203_; lean_object* v___y_2205_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v_presentation_2203_ = lean_ctor_get(v_x_2098_, 0);
lean_inc_ref(v_presentation_2203_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2214_ = lean_unsigned_to_nat(1024u);
v___x_2215_ = lean_nat_dec_le(v___x_2214_, v_prec_2099_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; 
v___x_2216_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2205_ = v___x_2216_;
goto v___jp_2204_;
}
else
{
lean_object* v___x_2217_; 
v___x_2217_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2205_ = v___x_2217_;
goto v___jp_2204_;
}
v___jp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2206_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__23));
v___x_2207_ = lean_unsigned_to_nat(1024u);
v___x_2208_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2203_, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2206_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
lean_inc(v___y_2205_);
v___x_2210_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___y_2205_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = 0;
v___x_2212_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set_uint8(v___x_2212_, sizeof(void*)*1, v___x_2211_);
v___x_2213_ = l_Repr_addAppParen(v___x_2212_, v_prec_2099_);
return v___x_2213_;
}
}
case 8:
{
lean_object* v_presentation_2218_; lean_object* v___y_2220_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v_presentation_2218_ = lean_ctor_get(v_x_2098_, 0);
lean_inc_ref(v_presentation_2218_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2229_ = lean_unsigned_to_nat(1024u);
v___x_2230_ = lean_nat_dec_le(v___x_2229_, v_prec_2099_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2220_ = v___x_2231_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2220_ = v___x_2232_;
goto v___jp_2219_;
}
v___jp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2221_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__26));
v___x_2222_ = lean_unsigned_to_nat(1024u);
v___x_2223_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2218_, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2221_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
lean_inc(v___y_2220_);
v___x_2225_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___y_2220_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = 0;
v___x_2227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2227_, 0, v___x_2225_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*1, v___x_2226_);
v___x_2228_ = l_Repr_addAppParen(v___x_2227_, v_prec_2099_);
return v___x_2228_;
}
}
case 9:
{
lean_object* v_presentation_2233_; lean_object* v___y_2235_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v_presentation_2233_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2233_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2244_ = lean_unsigned_to_nat(1024u);
v___x_2245_ = lean_nat_dec_le(v___x_2244_, v_prec_2099_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2235_ = v___x_2246_;
goto v___jp_2234_;
}
else
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2235_ = v___x_2247_;
goto v___jp_2234_;
}
v___jp_2234_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2236_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__29));
v___x_2237_ = lean_unsigned_to_nat(1024u);
v___x_2238_ = l_Std_Time_instReprYear_repr(v_presentation_2233_, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2236_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
lean_inc(v___y_2235_);
v___x_2240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___y_2235_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = 0;
v___x_2242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*1, v___x_2241_);
v___x_2243_ = l_Repr_addAppParen(v___x_2242_, v_prec_2099_);
return v___x_2243_;
}
}
case 10:
{
lean_object* v_presentation_2248_; lean_object* v___y_2250_; lean_object* v___x_2258_; uint8_t v___x_2259_; 
v_presentation_2248_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2248_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2258_ = lean_unsigned_to_nat(1024u);
v___x_2259_ = lean_nat_dec_le(v___x_2258_, v_prec_2099_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2250_ = v___x_2260_;
goto v___jp_2249_;
}
else
{
lean_object* v___x_2261_; 
v___x_2261_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2250_ = v___x_2261_;
goto v___jp_2249_;
}
v___jp_2249_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2251_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__32));
v___x_2252_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2248_);
v___x_2253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
lean_inc(v___y_2250_);
v___x_2254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___y_2250_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = 0;
v___x_2256_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*1, v___x_2255_);
v___x_2257_ = l_Repr_addAppParen(v___x_2256_, v_prec_2099_);
return v___x_2257_;
}
}
case 11:
{
lean_object* v_presentation_2262_; lean_object* v___y_2264_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v_presentation_2262_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2262_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2272_ = lean_unsigned_to_nat(1024u);
v___x_2273_ = lean_nat_dec_le(v___x_2272_, v_prec_2099_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2264_ = v___x_2274_;
goto v___jp_2263_;
}
else
{
lean_object* v___x_2275_; 
v___x_2275_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2264_ = v___x_2275_;
goto v___jp_2263_;
}
v___jp_2263_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2265_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__35));
v___x_2266_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2262_);
v___x_2267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
lean_inc(v___y_2264_);
v___x_2268_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___y_2264_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = 0;
v___x_2270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set_uint8(v___x_2270_, sizeof(void*)*1, v___x_2269_);
v___x_2271_ = l_Repr_addAppParen(v___x_2270_, v_prec_2099_);
return v___x_2271_;
}
}
case 12:
{
uint8_t v_presentation_2276_; lean_object* v___y_2278_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v_presentation_2276_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2287_ = lean_unsigned_to_nat(1024u);
v___x_2288_ = lean_nat_dec_le(v___x_2287_, v_prec_2099_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2278_ = v___x_2289_;
goto v___jp_2277_;
}
else
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2278_ = v___x_2290_;
goto v___jp_2277_;
}
v___jp_2277_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2279_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__38));
v___x_2280_ = lean_unsigned_to_nat(1024u);
v___x_2281_ = l_Std_Time_instReprText_repr(v_presentation_2276_, v___x_2280_);
v___x_2282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2279_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
lean_inc(v___y_2278_);
v___x_2283_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___y_2278_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = 0;
v___x_2285_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*1, v___x_2284_);
v___x_2286_ = l_Repr_addAppParen(v___x_2285_, v_prec_2099_);
return v___x_2286_;
}
}
case 13:
{
lean_object* v_presentation_2291_; lean_object* v___y_2293_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v_presentation_2291_ = lean_ctor_get(v_x_2098_, 0);
lean_inc_ref(v_presentation_2291_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2302_ = lean_unsigned_to_nat(1024u);
v___x_2303_ = lean_nat_dec_le(v___x_2302_, v_prec_2099_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2293_ = v___x_2304_;
goto v___jp_2292_;
}
else
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2293_ = v___x_2305_;
goto v___jp_2292_;
}
v___jp_2292_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2294_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__41));
v___x_2295_ = lean_unsigned_to_nat(1024u);
v___x_2296_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2291_, v___x_2295_);
v___x_2297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2294_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
lean_inc(v___y_2293_);
v___x_2298_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___y_2293_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = 0;
v___x_2300_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1, v___x_2299_);
v___x_2301_ = l_Repr_addAppParen(v___x_2300_, v_prec_2099_);
return v___x_2301_;
}
}
case 14:
{
lean_object* v_presentation_2306_; lean_object* v___y_2308_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_presentation_2306_ = lean_ctor_get(v_x_2098_, 0);
lean_inc_ref(v_presentation_2306_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2317_ = lean_unsigned_to_nat(1024u);
v___x_2318_ = lean_nat_dec_le(v___x_2317_, v_prec_2099_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2308_ = v___x_2319_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2308_ = v___x_2320_;
goto v___jp_2307_;
}
v___jp_2307_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2309_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__44));
v___x_2310_ = lean_unsigned_to_nat(1024u);
v___x_2311_ = l_Sum_repr___at___00Std_Time_instReprModifier_repr_spec__0(v_presentation_2306_, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2309_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
lean_inc(v___y_2308_);
v___x_2313_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___y_2308_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = 0;
v___x_2315_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set_uint8(v___x_2315_, sizeof(void*)*1, v___x_2314_);
v___x_2316_ = l_Repr_addAppParen(v___x_2315_, v_prec_2099_);
return v___x_2316_;
}
}
case 15:
{
lean_object* v_presentation_2321_; lean_object* v___y_2323_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v_presentation_2321_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2321_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2331_ = lean_unsigned_to_nat(1024u);
v___x_2332_ = lean_nat_dec_le(v___x_2331_, v_prec_2099_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2323_ = v___x_2333_;
goto v___jp_2322_;
}
else
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2323_ = v___x_2334_;
goto v___jp_2322_;
}
v___jp_2322_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2324_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__47));
v___x_2325_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2321_);
v___x_2326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
lean_inc(v___y_2323_);
v___x_2327_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___y_2323_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = 0;
v___x_2329_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set_uint8(v___x_2329_, sizeof(void*)*1, v___x_2328_);
v___x_2330_ = l_Repr_addAppParen(v___x_2329_, v_prec_2099_);
return v___x_2330_;
}
}
case 16:
{
uint8_t v_presentation_2335_; lean_object* v___y_2337_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v_presentation_2335_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2346_ = lean_unsigned_to_nat(1024u);
v___x_2347_ = lean_nat_dec_le(v___x_2346_, v_prec_2099_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2337_ = v___x_2348_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2337_ = v___x_2349_;
goto v___jp_2336_;
}
v___jp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2338_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__50));
v___x_2339_ = lean_unsigned_to_nat(1024u);
v___x_2340_ = l_Std_Time_instReprText_repr(v_presentation_2335_, v___x_2339_);
v___x_2341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2338_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
lean_inc(v___y_2337_);
v___x_2342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___y_2337_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = 0;
v___x_2344_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*1, v___x_2343_);
v___x_2345_ = l_Repr_addAppParen(v___x_2344_, v_prec_2099_);
return v___x_2345_;
}
}
case 17:
{
uint8_t v_presentation_2350_; lean_object* v___y_2352_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v_presentation_2350_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2361_ = lean_unsigned_to_nat(1024u);
v___x_2362_ = lean_nat_dec_le(v___x_2361_, v_prec_2099_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2352_ = v___x_2363_;
goto v___jp_2351_;
}
else
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2352_ = v___x_2364_;
goto v___jp_2351_;
}
v___jp_2351_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2353_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__53));
v___x_2354_ = lean_unsigned_to_nat(1024u);
v___x_2355_ = l_Std_Time_instReprText_repr(v_presentation_2350_, v___x_2354_);
v___x_2356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2353_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
lean_inc(v___y_2352_);
v___x_2357_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___y_2352_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = 0;
v___x_2359_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set_uint8(v___x_2359_, sizeof(void*)*1, v___x_2358_);
v___x_2360_ = l_Repr_addAppParen(v___x_2359_, v_prec_2099_);
return v___x_2360_;
}
}
case 18:
{
uint8_t v_presentation_2365_; lean_object* v___y_2367_; lean_object* v___x_2376_; uint8_t v___x_2377_; 
v_presentation_2365_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2376_ = lean_unsigned_to_nat(1024u);
v___x_2377_ = lean_nat_dec_le(v___x_2376_, v_prec_2099_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2367_ = v___x_2378_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2367_ = v___x_2379_;
goto v___jp_2366_;
}
v___jp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2368_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__56));
v___x_2369_ = lean_unsigned_to_nat(1024u);
v___x_2370_ = l_Std_Time_instReprText_repr(v_presentation_2365_, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2368_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
lean_inc(v___y_2367_);
v___x_2372_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___y_2367_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = 0;
v___x_2374_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*1, v___x_2373_);
v___x_2375_ = l_Repr_addAppParen(v___x_2374_, v_prec_2099_);
return v___x_2375_;
}
}
case 19:
{
lean_object* v_presentation_2380_; lean_object* v___y_2382_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v_presentation_2380_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2380_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2390_ = lean_unsigned_to_nat(1024u);
v___x_2391_ = lean_nat_dec_le(v___x_2390_, v_prec_2099_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2382_ = v___x_2392_;
goto v___jp_2381_;
}
else
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2382_ = v___x_2393_;
goto v___jp_2381_;
}
v___jp_2381_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2383_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__59));
v___x_2384_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2380_);
v___x_2385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
lean_inc(v___y_2382_);
v___x_2386_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___y_2382_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = 0;
v___x_2388_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*1, v___x_2387_);
v___x_2389_ = l_Repr_addAppParen(v___x_2388_, v_prec_2099_);
return v___x_2389_;
}
}
case 20:
{
lean_object* v_presentation_2394_; lean_object* v___y_2396_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v_presentation_2394_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2394_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2404_ = lean_unsigned_to_nat(1024u);
v___x_2405_ = lean_nat_dec_le(v___x_2404_, v_prec_2099_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2396_ = v___x_2406_;
goto v___jp_2395_;
}
else
{
lean_object* v___x_2407_; 
v___x_2407_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2396_ = v___x_2407_;
goto v___jp_2395_;
}
v___jp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2397_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__62));
v___x_2398_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2394_);
v___x_2399_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
lean_inc(v___y_2396_);
v___x_2400_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___y_2396_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = 0;
v___x_2402_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*1, v___x_2401_);
v___x_2403_ = l_Repr_addAppParen(v___x_2402_, v_prec_2099_);
return v___x_2403_;
}
}
case 21:
{
lean_object* v_presentation_2408_; lean_object* v___y_2410_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v_presentation_2408_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2408_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2418_ = lean_unsigned_to_nat(1024u);
v___x_2419_ = lean_nat_dec_le(v___x_2418_, v_prec_2099_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2410_ = v___x_2420_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2410_ = v___x_2421_;
goto v___jp_2409_;
}
v___jp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2411_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__65));
v___x_2412_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2408_);
v___x_2413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
lean_inc(v___y_2410_);
v___x_2414_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___y_2410_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = 0;
v___x_2416_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*1, v___x_2415_);
v___x_2417_ = l_Repr_addAppParen(v___x_2416_, v_prec_2099_);
return v___x_2417_;
}
}
case 22:
{
lean_object* v_presentation_2422_; lean_object* v___y_2424_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v_presentation_2422_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2422_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2432_ = lean_unsigned_to_nat(1024u);
v___x_2433_ = lean_nat_dec_le(v___x_2432_, v_prec_2099_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2424_ = v___x_2434_;
goto v___jp_2423_;
}
else
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2424_ = v___x_2435_;
goto v___jp_2423_;
}
v___jp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2425_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__68));
v___x_2426_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2422_);
v___x_2427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
lean_inc(v___y_2424_);
v___x_2428_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___y_2424_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = 0;
v___x_2430_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2430_, 0, v___x_2428_);
lean_ctor_set_uint8(v___x_2430_, sizeof(void*)*1, v___x_2429_);
v___x_2431_ = l_Repr_addAppParen(v___x_2430_, v_prec_2099_);
return v___x_2431_;
}
}
case 23:
{
lean_object* v_presentation_2436_; lean_object* v___y_2438_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v_presentation_2436_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2436_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2446_ = lean_unsigned_to_nat(1024u);
v___x_2447_ = lean_nat_dec_le(v___x_2446_, v_prec_2099_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2438_ = v___x_2448_;
goto v___jp_2437_;
}
else
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2438_ = v___x_2449_;
goto v___jp_2437_;
}
v___jp_2437_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2439_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__71));
v___x_2440_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2436_);
v___x_2441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
lean_inc(v___y_2438_);
v___x_2442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___y_2438_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = 0;
v___x_2444_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2444_, 0, v___x_2442_);
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*1, v___x_2443_);
v___x_2445_ = l_Repr_addAppParen(v___x_2444_, v_prec_2099_);
return v___x_2445_;
}
}
case 24:
{
lean_object* v_presentation_2450_; lean_object* v___y_2452_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v_presentation_2450_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2450_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2460_ = lean_unsigned_to_nat(1024u);
v___x_2461_ = lean_nat_dec_le(v___x_2460_, v_prec_2099_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2452_ = v___x_2462_;
goto v___jp_2451_;
}
else
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2452_ = v___x_2463_;
goto v___jp_2451_;
}
v___jp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2453_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__74));
v___x_2454_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2450_);
v___x_2455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2453_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
lean_inc(v___y_2452_);
v___x_2456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___y_2452_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = 0;
v___x_2458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*1, v___x_2457_);
v___x_2459_ = l_Repr_addAppParen(v___x_2458_, v_prec_2099_);
return v___x_2459_;
}
}
case 25:
{
lean_object* v_presentation_2464_; lean_object* v___y_2466_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v_presentation_2464_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2464_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2475_ = lean_unsigned_to_nat(1024u);
v___x_2476_ = lean_nat_dec_le(v___x_2475_, v_prec_2099_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2466_ = v___x_2477_;
goto v___jp_2465_;
}
else
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2466_ = v___x_2478_;
goto v___jp_2465_;
}
v___jp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2467_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__77));
v___x_2468_ = lean_unsigned_to_nat(1024u);
v___x_2469_ = l_Std_Time_instReprFraction_repr(v_presentation_2464_, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2467_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
lean_inc(v___y_2466_);
v___x_2471_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___y_2466_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = 0;
v___x_2473_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*1, v___x_2472_);
v___x_2474_ = l_Repr_addAppParen(v___x_2473_, v_prec_2099_);
return v___x_2474_;
}
}
case 26:
{
lean_object* v_presentation_2479_; lean_object* v___y_2481_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v_presentation_2479_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2479_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2489_ = lean_unsigned_to_nat(1024u);
v___x_2490_ = lean_nat_dec_le(v___x_2489_, v_prec_2099_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2481_ = v___x_2491_;
goto v___jp_2480_;
}
else
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2481_ = v___x_2492_;
goto v___jp_2480_;
}
v___jp_2480_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2482_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__80));
v___x_2483_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2479_);
v___x_2484_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2482_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
lean_inc(v___y_2481_);
v___x_2485_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___y_2481_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = 0;
v___x_2487_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set_uint8(v___x_2487_, sizeof(void*)*1, v___x_2486_);
v___x_2488_ = l_Repr_addAppParen(v___x_2487_, v_prec_2099_);
return v___x_2488_;
}
}
case 27:
{
lean_object* v_presentation_2493_; lean_object* v___y_2495_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
v_presentation_2493_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2493_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2503_ = lean_unsigned_to_nat(1024u);
v___x_2504_ = lean_nat_dec_le(v___x_2503_, v_prec_2099_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2495_ = v___x_2505_;
goto v___jp_2494_;
}
else
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2495_ = v___x_2506_;
goto v___jp_2494_;
}
v___jp_2494_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2496_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__83));
v___x_2497_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2493_);
v___x_2498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
lean_inc(v___y_2495_);
v___x_2499_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___y_2495_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = 0;
v___x_2501_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set_uint8(v___x_2501_, sizeof(void*)*1, v___x_2500_);
v___x_2502_ = l_Repr_addAppParen(v___x_2501_, v_prec_2099_);
return v___x_2502_;
}
}
case 28:
{
lean_object* v_presentation_2507_; lean_object* v___y_2509_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v_presentation_2507_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_presentation_2507_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2517_ = lean_unsigned_to_nat(1024u);
v___x_2518_ = lean_nat_dec_le(v___x_2517_, v_prec_2099_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2509_ = v___x_2519_;
goto v___jp_2508_;
}
else
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2509_ = v___x_2520_;
goto v___jp_2508_;
}
v___jp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2510_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__86));
v___x_2511_ = l_Std_Time_instReprNumber_repr___redArg(v_presentation_2507_);
v___x_2512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
lean_inc(v___y_2509_);
v___x_2513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2509_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = 0;
v___x_2515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*1, v___x_2514_);
v___x_2516_ = l_Repr_addAppParen(v___x_2515_, v_prec_2099_);
return v___x_2516_;
}
}
case 29:
{
uint8_t v_presentation_2521_; lean_object* v___y_2523_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v_presentation_2521_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2532_ = lean_unsigned_to_nat(1024u);
v___x_2533_ = lean_nat_dec_le(v___x_2532_, v_prec_2099_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2523_ = v___x_2534_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2523_ = v___x_2535_;
goto v___jp_2522_;
}
v___jp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2524_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__89));
v___x_2525_ = lean_unsigned_to_nat(1024u);
v___x_2526_ = l_Std_Time_instReprZoneId_repr(v_presentation_2521_, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2524_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
lean_inc(v___y_2523_);
v___x_2528_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___y_2523_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___x_2529_ = 0;
v___x_2530_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set_uint8(v___x_2530_, sizeof(void*)*1, v___x_2529_);
v___x_2531_ = l_Repr_addAppParen(v___x_2530_, v_prec_2099_);
return v___x_2531_;
}
}
case 30:
{
uint8_t v_presentation_2536_; lean_object* v___y_2538_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v_presentation_2536_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2547_ = lean_unsigned_to_nat(1024u);
v___x_2548_ = lean_nat_dec_le(v___x_2547_, v_prec_2099_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2538_ = v___x_2549_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2538_ = v___x_2550_;
goto v___jp_2537_;
}
v___jp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2539_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__92));
v___x_2540_ = lean_unsigned_to_nat(1024u);
v___x_2541_ = l_Std_Time_instReprZoneName_repr(v_presentation_2536_, v___x_2540_);
v___x_2542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2539_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
lean_inc(v___y_2538_);
v___x_2543_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___y_2538_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = 0;
v___x_2545_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set_uint8(v___x_2545_, sizeof(void*)*1, v___x_2544_);
v___x_2546_ = l_Repr_addAppParen(v___x_2545_, v_prec_2099_);
return v___x_2546_;
}
}
case 31:
{
uint8_t v_presentation_2551_; lean_object* v___y_2553_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v_presentation_2551_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2562_ = lean_unsigned_to_nat(1024u);
v___x_2563_ = lean_nat_dec_le(v___x_2562_, v_prec_2099_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2553_ = v___x_2564_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2553_ = v___x_2565_;
goto v___jp_2552_;
}
v___jp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2554_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__95));
v___x_2555_ = lean_unsigned_to_nat(1024u);
v___x_2556_ = l_Std_Time_instReprZoneName_repr(v_presentation_2551_, v___x_2555_);
v___x_2557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2554_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
lean_inc(v___y_2553_);
v___x_2558_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___y_2553_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = 0;
v___x_2560_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*1, v___x_2559_);
v___x_2561_ = l_Repr_addAppParen(v___x_2560_, v_prec_2099_);
return v___x_2561_;
}
}
case 32:
{
uint8_t v_presentation_2566_; lean_object* v___y_2568_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v_presentation_2566_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2577_ = lean_unsigned_to_nat(1024u);
v___x_2578_ = lean_nat_dec_le(v___x_2577_, v_prec_2099_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2568_ = v___x_2579_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2568_ = v___x_2580_;
goto v___jp_2567_;
}
v___jp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2569_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__98));
v___x_2570_ = lean_unsigned_to_nat(1024u);
v___x_2571_ = l_Std_Time_instReprOffsetO_repr(v_presentation_2566_, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2569_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
lean_inc(v___y_2568_);
v___x_2573_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___y_2568_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = 0;
v___x_2575_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*1, v___x_2574_);
v___x_2576_ = l_Repr_addAppParen(v___x_2575_, v_prec_2099_);
return v___x_2576_;
}
}
case 33:
{
uint8_t v_presentation_2581_; lean_object* v___y_2583_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v_presentation_2581_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2592_ = lean_unsigned_to_nat(1024u);
v___x_2593_ = lean_nat_dec_le(v___x_2592_, v_prec_2099_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2583_ = v___x_2594_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2595_; 
v___x_2595_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2583_ = v___x_2595_;
goto v___jp_2582_;
}
v___jp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2584_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__101));
v___x_2585_ = lean_unsigned_to_nat(1024u);
v___x_2586_ = l_Std_Time_instReprOffsetX_repr(v_presentation_2581_, v___x_2585_);
v___x_2587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2584_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
lean_inc(v___y_2583_);
v___x_2588_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___y_2583_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = 0;
v___x_2590_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*1, v___x_2589_);
v___x_2591_ = l_Repr_addAppParen(v___x_2590_, v_prec_2099_);
return v___x_2591_;
}
}
case 34:
{
uint8_t v_presentation_2596_; lean_object* v___y_2598_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v_presentation_2596_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2607_ = lean_unsigned_to_nat(1024u);
v___x_2608_ = lean_nat_dec_le(v___x_2607_, v_prec_2099_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2598_ = v___x_2609_;
goto v___jp_2597_;
}
else
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2598_ = v___x_2610_;
goto v___jp_2597_;
}
v___jp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2599_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__104));
v___x_2600_ = lean_unsigned_to_nat(1024u);
v___x_2601_ = l_Std_Time_instReprOffsetX_repr(v_presentation_2596_, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2599_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
lean_inc(v___y_2598_);
v___x_2603_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___y_2598_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = 0;
v___x_2605_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2605_, 0, v___x_2603_);
lean_ctor_set_uint8(v___x_2605_, sizeof(void*)*1, v___x_2604_);
v___x_2606_ = l_Repr_addAppParen(v___x_2605_, v_prec_2099_);
return v___x_2606_;
}
}
default: 
{
uint8_t v_presentation_2611_; lean_object* v___y_2613_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_presentation_2611_ = lean_ctor_get_uint8(v_x_2098_, 0);
lean_dec_ref_known(v_x_2098_, 0);
v___x_2622_ = lean_unsigned_to_nat(1024u);
v___x_2623_ = lean_nat_dec_le(v___x_2622_, v_prec_2099_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__8, &l_Std_Time_instReprText_repr___closed__8_once, _init_l_Std_Time_instReprText_repr___closed__8);
v___y_2613_ = v___x_2624_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_obj_once(&l_Std_Time_instReprText_repr___closed__9, &l_Std_Time_instReprText_repr___closed__9_once, _init_l_Std_Time_instReprText_repr___closed__9);
v___y_2613_ = v___x_2625_;
goto v___jp_2612_;
}
v___jp_2612_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2614_ = ((lean_object*)(l_Std_Time_instReprModifier_repr___closed__107));
v___x_2615_ = lean_unsigned_to_nat(1024u);
v___x_2616_ = l_Std_Time_instReprOffsetZ_repr(v_presentation_2611_, v___x_2615_);
v___x_2617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2614_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
lean_inc(v___y_2613_);
v___x_2618_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___y_2613_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = 0;
v___x_2620_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2620_, 0, v___x_2618_);
lean_ctor_set_uint8(v___x_2620_, sizeof(void*)*1, v___x_2619_);
v___x_2621_ = l_Repr_addAppParen(v___x_2620_, v_prec_2099_);
return v___x_2621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprModifier_repr___boxed(lean_object* v_x_2626_, lean_object* v_prec_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Std_Time_instReprModifier_repr(v_x_2626_, v_prec_2627_);
lean_dec(v_prec_2627_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(lean_object* v_constructor_2638_, lean_object* v_classify_2639_, lean_object* v_p_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v_len_2642_; lean_object* v___x_2643_; 
v_len_2642_ = lean_string_length(v_p_2640_);
v___x_2643_ = lean_apply_1(v_classify_2639_, v_len_2642_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v___x_2644_; uint32_t v___y_2646_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec_ref(v_constructor_2638_);
v___x_2644_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_string_utf8_byte_size(v_p_2640_);
v___x_2656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2656_, 0, v_p_2640_);
lean_ctor_set(v___x_2656_, 1, v___x_2654_);
lean_ctor_set(v___x_2656_, 2, v___x_2655_);
v___x_2657_ = l_String_Slice_Pos_get_x3f(v___x_2656_, v___x_2654_);
lean_dec_ref_known(v___x_2656_, 3);
if (lean_obj_tag(v___x_2657_) == 0)
{
uint32_t v___x_2658_; 
v___x_2658_ = 65;
v___y_2646_ = v___x_2658_;
goto v___jp_2645_;
}
else
{
lean_object* v_val_2659_; uint32_t v___x_2660_; 
v_val_2659_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_val_2659_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2660_ = lean_unbox_uint32(v_val_2659_);
lean_dec(v_val_2659_);
v___y_2646_ = v___x_2660_;
goto v___jp_2645_;
}
v___jp_2645_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2647_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2648_ = lean_string_push(v___x_2647_, v___y_2646_);
v___x_2649_ = lean_string_append(v___x_2644_, v___x_2648_);
lean_dec_ref(v___x_2648_);
v___x_2650_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_2651_ = lean_string_append(v___x_2649_, v___x_2650_);
v___x_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
v___x_2653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2653_, 0, v_a_2641_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
return v___x_2653_;
}
}
else
{
lean_object* v_val_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_dec_ref(v_p_2640_);
v_val_2661_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_val_2661_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2662_ = lean_apply_1(v_constructor_2638_, v_val_2661_);
v___x_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2663_, 0, v_a_2641_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod(lean_object* v_00_u03b1_2664_, lean_object* v_constructor_2665_, lean_object* v_classify_2666_, lean_object* v_p_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2665_, v_classify_2666_, v_p_2667_, v_a_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(lean_object* v_constructor_2671_, lean_object* v_p_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseText___closed__0));
v___x_2675_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2671_, v___x_2674_, v_p_2672_, v_a_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(lean_object* v_max_2676_, lean_object* v_x_2677_){
_start:
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_nat_dec_le(v_x_2677_, v_max_2676_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
lean_dec(v_x_2677_);
v___x_2679_ = lean_box(0);
return v___x_2679_;
}
else
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_x_2677_);
return v___x_2680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax___boxed(lean_object* v_max_2681_, lean_object* v_x_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyNumberMax(v_max_2681_, v_x_2682_);
lean_dec(v_max_2681_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(lean_object* v_x_2686_){
_start:
{
lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_nat_dec_eq(v_x_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_box(0);
return v___x_2689_;
}
else
{
lean_object* v___x_2690_; 
v___x_2690_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___closed__0));
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber___boxed(lean_object* v_x_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifySingleNumber(v_x_2691_);
lean_dec(v_x_2691_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(lean_object* v_x_2696_){
_start:
{
lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2697_ = lean_unsigned_to_nat(6u);
v___x_2698_ = lean_nat_dec_eq(v_x_2696_, v___x_2697_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Std_Time_Text_classify(v_x_2696_);
return v___x_2699_;
}
else
{
lean_object* v___x_2700_; 
v___x_2700_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___closed__0));
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText___boxed(lean_object* v_x_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayText(v_x_2701_);
lean_dec(v_x_2701_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(lean_object* v_constructor_2704_, lean_object* v_p_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText___closed__0));
v___x_2708_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2704_, v___x_2707_, v_p_2705_, v_a_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(lean_object* v_constructor_2710_, lean_object* v_p_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction___closed__0));
v___x_2714_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2710_, v___x_2713_, v_p_2711_, v_a_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(lean_object* v_constructor_2715_, lean_object* v_p_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = lean_string_length(v_p_2716_);
v___x_2719_ = lean_apply_1(v_constructor_2715_, v___x_2718_);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v_a_2717_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber___boxed(lean_object* v_constructor_2721_, lean_object* v_p_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v_constructor_2721_, v_p_2722_, v_a_2723_);
lean_dec_ref(v_p_2722_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(lean_object* v_constructor_2726_, lean_object* v_p_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear___closed__0));
v___x_2730_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2726_, v___x_2729_, v_p_2727_, v_a_2728_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(lean_object* v_constructor_2732_, lean_object* v_p_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX___closed__0));
v___x_2736_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2732_, v___x_2735_, v_p_2733_, v_a_2734_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(lean_object* v_constructor_2738_, lean_object* v_p_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ___closed__0));
v___x_2742_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2738_, v___x_2741_, v_p_2739_, v_a_2740_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(lean_object* v_constructor_2744_, lean_object* v_p_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO___closed__0));
v___x_2748_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2744_, v___x_2747_, v_p_2745_, v_a_2746_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(lean_object* v_p_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2756_ = lean_string_length(v_p_2754_);
v___x_2757_ = lean_unsigned_to_nat(1u);
v___x_2758_ = lean_nat_dec_eq(v___x_2756_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = lean_unsigned_to_nat(2u);
v___x_2760_ = lean_nat_dec_eq(v___x_2756_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; uint32_t v___y_2763_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2761_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_string_utf8_byte_size(v_p_2754_);
v___x_2773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2773_, 0, v_p_2754_);
lean_ctor_set(v___x_2773_, 1, v___x_2771_);
lean_ctor_set(v___x_2773_, 2, v___x_2772_);
v___x_2774_ = l_String_Slice_Pos_get_x3f(v___x_2773_, v___x_2771_);
lean_dec_ref_known(v___x_2773_, 3);
if (lean_obj_tag(v___x_2774_) == 0)
{
uint32_t v___x_2775_; 
v___x_2775_ = 65;
v___y_2763_ = v___x_2775_;
goto v___jp_2762_;
}
else
{
lean_object* v_val_2776_; uint32_t v___x_2777_; 
v_val_2776_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_val_2776_);
lean_dec_ref_known(v___x_2774_, 1);
v___x_2777_ = lean_unbox_uint32(v_val_2776_);
lean_dec(v_val_2776_);
v___y_2763_ = v___x_2777_;
goto v___jp_2762_;
}
v___jp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2764_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2765_ = lean_string_push(v___x_2764_, v___y_2763_);
v___x_2766_ = lean_string_append(v___x_2761_, v___x_2765_);
lean_dec_ref(v___x_2765_);
v___x_2767_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__0));
v___x_2768_ = lean_string_append(v___x_2766_, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
v___x_2770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2770_, 0, v_a_2755_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
return v___x_2770_;
}
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_dec_ref(v_p_2754_);
v___x_2778_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__1));
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v_a_2755_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
return v___x_2779_;
}
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
lean_dec_ref(v_p_2754_);
v___x_2780_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId___closed__2));
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v_a_2755_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
return v___x_2781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(lean_object* v_constructor_2783_, lean_object* v_p_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText___closed__0));
v___x_2787_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2783_, v___x_2786_, v_p_2784_, v_a_2785_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText(lean_object* v_x_2793_){
_start:
{
lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2794_ = lean_unsigned_to_nat(3u);
v___x_2795_ = lean_nat_dec_lt(v_x_2793_, v___x_2794_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; uint8_t v___x_2797_; 
v___x_2796_ = lean_unsigned_to_nat(6u);
v___x_2797_ = lean_nat_dec_eq(v_x_2793_, v___x_2796_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Std_Time_Text_classify(v_x_2793_);
lean_dec(v_x_2793_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_box(0);
return v___x_2799_;
}
else
{
lean_object* v_val_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2808_; 
v_val_2800_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2802_ = v___x_2798_;
v_isShared_2803_ = v_isSharedCheck_2808_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_val_2800_);
lean_dec(v___x_2798_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2808_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_val_2800_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2804_);
v___x_2806_ = v___x_2802_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
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
else
{
lean_object* v___x_2809_; 
lean_dec(v_x_2793_);
v___x_2809_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1));
return v___x_2809_;
}
}
else
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_x_2793_);
v___x_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
return v___x_2811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(lean_object* v_constructor_2813_, lean_object* v_p_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText___closed__0));
v___x_2817_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2813_, v___x_2816_, v_p_2814_, v_a_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(lean_object* v_x_2822_){
_start:
{
lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = lean_unsigned_to_nat(1u);
v___x_2824_ = lean_nat_dec_eq(v_x_2822_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = lean_unsigned_to_nat(6u);
v___x_2826_ = lean_nat_dec_eq(v_x_2822_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2827_ = lean_unsigned_to_nat(3u);
v___x_2828_ = lean_nat_dec_le(v___x_2827_, v_x_2822_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_box(0);
return v___x_2829_;
}
else
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Std_Time_Text_classify(v_x_2822_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v___x_2831_; 
v___x_2831_ = lean_box(0);
return v___x_2831_;
}
else
{
lean_object* v_val_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2840_; 
v_val_2832_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2834_ = v___x_2830_;
v_isShared_2835_ = v_isSharedCheck_2840_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_val_2832_);
lean_dec(v___x_2830_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2840_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2836_, 0, v_val_2832_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2836_);
v___x_2838_ = v___x_2834_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
else
{
lean_object* v___x_2841_; 
v___x_2841_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyWeekdayNumberText___closed__1));
return v___x_2841_;
}
}
else
{
lean_object* v___x_2842_; 
v___x_2842_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___closed__1));
return v___x_2842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText___boxed(lean_object* v_x_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l___private_Std_Time_Format_Modifier_0__Std_Time_classifyStandaloneWeekdayNumberText(v_x_2843_);
lean_dec(v_x_2843_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(lean_object* v_constructor_2846_, lean_object* v_p_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText___closed__0));
v___x_2850_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v_constructor_2846_, v___x_2849_, v_p_2847_, v_a_2848_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(uint8_t v_presentation_2851_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = lean_alloc_ctor(16, 0, 1);
lean_ctor_set_uint8(v___x_2852_, 0, v_presentation_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0___boxed(lean_object* v_presentation_2853_){
_start:
{
uint8_t v_presentation_boxed_2854_; lean_object* v_res_2855_; 
v_presentation_boxed_2854_ = lean_unbox(v_presentation_2853_);
v_res_2855_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___lam__0(v_presentation_boxed_2854_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(lean_object* v_p_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v___f_2859_; lean_object* v___x_2860_; 
v___f_2859_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM___closed__0));
v___x_2860_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2859_, v_p_2857_, v_a_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(uint8_t v_presentation_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = lean_alloc_ctor(17, 0, 1);
lean_ctor_set_uint8(v___x_2862_, 0, v_presentation_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0___boxed(lean_object* v_presentation_2863_){
_start:
{
uint8_t v_presentation_boxed_2864_; lean_object* v_res_2865_; 
v_presentation_boxed_2864_ = lean_unbox(v_presentation_2863_);
v_res_2865_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___lam__0(v_presentation_boxed_2864_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(lean_object* v_p_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v___f_2869_; lean_object* v___x_2870_; 
v___f_2869_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod___closed__0));
v___x_2870_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2869_, v_p_2867_, v_a_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(uint8_t v_presentation_2871_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_alloc_ctor(18, 0, 1);
lean_ctor_set_uint8(v___x_2872_, 0, v_presentation_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0___boxed(lean_object* v_presentation_2873_){
_start:
{
uint8_t v_presentation_boxed_2874_; lean_object* v_res_2875_; 
v_presentation_boxed_2874_ = lean_unbox(v_presentation_2873_);
v_res_2875_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___lam__0(v_presentation_boxed_2874_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(lean_object* v_p_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___f_2879_; lean_object* v___x_2880_; 
v___f_2879_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod___closed__0));
v___x_2880_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_2879_, v_p_2877_, v_a_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(lean_object* v_constructor_2881_, lean_object* v_p_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v___y_2885_; uint32_t v___y_2886_; lean_object* v_len_2894_; uint32_t v___y_2896_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_len_2894_ = lean_string_length(v_p_2882_);
v___x_2909_ = lean_unsigned_to_nat(0u);
v___x_2910_ = lean_string_utf8_byte_size(v_p_2882_);
lean_inc_ref(v_p_2882_);
v___x_2911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2911_, 0, v_p_2882_);
lean_ctor_set(v___x_2911_, 1, v___x_2909_);
lean_ctor_set(v___x_2911_, 2, v___x_2910_);
v___x_2912_ = l_String_Slice_Pos_get_x3f(v___x_2911_, v___x_2909_);
lean_dec_ref_known(v___x_2911_, 3);
if (lean_obj_tag(v___x_2912_) == 0)
{
uint32_t v___x_2913_; 
v___x_2913_ = 65;
v___y_2896_ = v___x_2913_;
goto v___jp_2895_;
}
else
{
lean_object* v_val_2914_; uint32_t v___x_2915_; 
v_val_2914_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_val_2914_);
lean_dec_ref_known(v___x_2912_, 1);
v___x_2915_ = lean_unbox_uint32(v_val_2914_);
lean_dec(v_val_2914_);
v___y_2896_ = v___x_2915_;
goto v___jp_2895_;
}
v___jp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2887_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__1));
v___x_2888_ = lean_string_push(v___x_2887_, v___y_2886_);
lean_inc_ref(v___y_2885_);
v___x_2889_ = lean_string_append(v___y_2885_, v___x_2888_);
lean_dec_ref(v___x_2888_);
v___x_2890_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__2));
v___x_2891_ = lean_string_append(v___x_2889_, v___x_2890_);
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
v___x_2893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2893_, 0, v_a_2883_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
return v___x_2893_;
}
v___jp_2895_:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Std_Time_ZoneName_classify(v___y_2896_, v_len_2894_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_dec_ref(v_constructor_2881_);
v___x_2898_ = ((lean_object*)(l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg___closed__0));
v___x_2899_ = lean_unsigned_to_nat(0u);
v___x_2900_ = lean_string_utf8_byte_size(v_p_2882_);
v___x_2901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2901_, 0, v_p_2882_);
lean_ctor_set(v___x_2901_, 1, v___x_2899_);
lean_ctor_set(v___x_2901_, 2, v___x_2900_);
v___x_2902_ = l_String_Slice_Pos_get_x3f(v___x_2901_, v___x_2899_);
lean_dec_ref_known(v___x_2901_, 3);
if (lean_obj_tag(v___x_2902_) == 0)
{
uint32_t v___x_2903_; 
v___x_2903_ = 65;
v___y_2885_ = v___x_2898_;
v___y_2886_ = v___x_2903_;
goto v___jp_2884_;
}
else
{
lean_object* v_val_2904_; uint32_t v___x_2905_; 
v_val_2904_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_val_2904_);
lean_dec_ref_known(v___x_2902_, 1);
v___x_2905_ = lean_unbox_uint32(v_val_2904_);
lean_dec(v_val_2904_);
v___y_2885_ = v___x_2898_;
v___y_2886_ = v___x_2905_;
goto v___jp_2884_;
}
}
else
{
lean_object* v_val_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec_ref(v_p_2882_);
v_val_2906_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_val_2906_);
lean_dec_ref_known(v___x_2897_, 1);
v___x_2907_ = lean_apply_1(v_constructor_2881_, v_val_2906_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_a_2883_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
return v___x_2908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0(uint8_t v_presentation_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_alloc_ctor(35, 0, 1);
lean_ctor_set_uint8(v___x_2917_, 0, v_presentation_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__0___boxed(lean_object* v_presentation_2918_){
_start:
{
uint8_t v_presentation_boxed_2919_; lean_object* v_res_2920_; 
v_presentation_boxed_2919_ = lean_unbox(v_presentation_2918_);
v_res_2920_ = l_Std_Time_parseModifier___lam__0(v_presentation_boxed_2919_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1(uint8_t v_presentation_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = lean_alloc_ctor(34, 0, 1);
lean_ctor_set_uint8(v___x_2922_, 0, v_presentation_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__1___boxed(lean_object* v_presentation_2923_){
_start:
{
uint8_t v_presentation_boxed_2924_; lean_object* v_res_2925_; 
v_presentation_boxed_2924_ = lean_unbox(v_presentation_2923_);
v_res_2925_ = l_Std_Time_parseModifier___lam__1(v_presentation_boxed_2924_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2(uint8_t v_presentation_2926_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_alloc_ctor(33, 0, 1);
lean_ctor_set_uint8(v___x_2927_, 0, v_presentation_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__2___boxed(lean_object* v_presentation_2928_){
_start:
{
uint8_t v_presentation_boxed_2929_; lean_object* v_res_2930_; 
v_presentation_boxed_2929_ = lean_unbox(v_presentation_2928_);
v_res_2930_ = l_Std_Time_parseModifier___lam__2(v_presentation_boxed_2929_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3(uint8_t v_presentation_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = lean_alloc_ctor(32, 0, 1);
lean_ctor_set_uint8(v___x_2932_, 0, v_presentation_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__3___boxed(lean_object* v_presentation_2933_){
_start:
{
uint8_t v_presentation_boxed_2934_; lean_object* v_res_2935_; 
v_presentation_boxed_2934_ = lean_unbox(v_presentation_2933_);
v_res_2935_ = l_Std_Time_parseModifier___lam__3(v_presentation_boxed_2934_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4(uint8_t v_presentation_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_alloc_ctor(31, 0, 1);
lean_ctor_set_uint8(v___x_2937_, 0, v_presentation_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__4___boxed(lean_object* v_presentation_2938_){
_start:
{
uint8_t v_presentation_boxed_2939_; lean_object* v_res_2940_; 
v_presentation_boxed_2939_ = lean_unbox(v_presentation_2938_);
v_res_2940_ = l_Std_Time_parseModifier___lam__4(v_presentation_boxed_2939_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5(uint8_t v_presentation_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_alloc_ctor(30, 0, 1);
lean_ctor_set_uint8(v___x_2942_, 0, v_presentation_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__5___boxed(lean_object* v_presentation_2943_){
_start:
{
uint8_t v_presentation_boxed_2944_; lean_object* v_res_2945_; 
v_presentation_boxed_2944_ = lean_unbox(v_presentation_2943_);
v_res_2945_ = l_Std_Time_parseModifier___lam__5(v_presentation_boxed_2944_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__6(lean_object* v_presentation_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_alloc_ctor(28, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_presentation_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__7(lean_object* v_presentation_2948_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_alloc_ctor(27, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_presentation_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__8(lean_object* v_presentation_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = lean_alloc_ctor(26, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_presentation_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__9(lean_object* v_presentation_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = lean_alloc_ctor(25, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_presentation_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__10(lean_object* v_presentation_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_alloc_ctor(24, 1, 0);
lean_ctor_set(v___x_2955_, 0, v_presentation_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__11(lean_object* v_presentation_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_alloc_ctor(23, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_presentation_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__12(lean_object* v_presentation_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(v___x_2959_, 0, v_presentation_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__13(lean_object* v_presentation_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_alloc_ctor(21, 1, 0);
lean_ctor_set(v___x_2961_, 0, v_presentation_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__14(lean_object* v_presentation_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_presentation_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__15(lean_object* v_presentation_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = lean_alloc_ctor(19, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_presentation_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__16(lean_object* v_presentation_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v___x_2967_, 0, v_presentation_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__17(lean_object* v_presentation_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_2969_, 0, v_presentation_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__18(lean_object* v_presentation_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_2971_, 0, v_presentation_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19(uint8_t v_presentation_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_alloc_ctor(12, 0, 1);
lean_ctor_set_uint8(v___x_2973_, 0, v_presentation_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__19___boxed(lean_object* v_presentation_2974_){
_start:
{
uint8_t v_presentation_boxed_2975_; lean_object* v_res_2976_; 
v_presentation_boxed_2975_ = lean_unbox(v_presentation_2974_);
v_res_2976_ = l_Std_Time_parseModifier___lam__19(v_presentation_boxed_2975_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__20(lean_object* v_presentation_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_presentation_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__21(lean_object* v_presentation_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_presentation_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__22(lean_object* v_presentation_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_presentation_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__23(lean_object* v_presentation_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2984_, 0, v_presentation_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__24(lean_object* v_presentation_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_presentation_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__25(lean_object* v_presentation_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_presentation_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__26(lean_object* v_presentation_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2990_, 0, v_presentation_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__27(lean_object* v_presentation_2991_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_presentation_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__28(lean_object* v_presentation_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v_presentation_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__29(lean_object* v_presentation_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2996_, 0, v_presentation_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__30(lean_object* v_presentation_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_presentation_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31(uint8_t v_presentation_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3000_, 0, v_presentation_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier___lam__31___boxed(lean_object* v_presentation_3001_){
_start:
{
uint8_t v_presentation_boxed_3002_; lean_object* v_res_3003_; 
v_presentation_boxed_3002_ = lean_unbox(v_presentation_3001_);
v_res_3003_ = l_Std_Time_parseModifier___lam__31(v_presentation_boxed_3002_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(lean_object* v_acc_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_fst_3009_; lean_object* v_snd_3010_; lean_object* v_pos_3012_; lean_object* v_snd_3013_; lean_object* v_err_3014_; lean_object* v___x_3018_; uint8_t v_decide_3019_; 
v_fst_3009_ = lean_ctor_get(v_a_3008_, 0);
v_snd_3010_ = lean_ctor_get(v_a_3008_, 1);
lean_inc(v_snd_3010_);
v___x_3018_ = lean_string_utf8_byte_size(v_fst_3009_);
v_decide_3019_ = lean_nat_dec_eq(v_snd_3010_, v___x_3018_);
if (v_decide_3019_ == 0)
{
uint32_t v___x_3020_; uint32_t v_c_3021_; uint8_t v___x_3022_; 
v___x_3020_ = 120;
v_c_3021_ = lean_string_utf8_get_fast(v_fst_3009_, v_snd_3010_);
v___x_3022_ = lean_uint32_dec_eq(v_c_3021_, v___x_3020_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; 
v___x_3023_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1));
lean_inc(v_snd_3010_);
v_pos_3012_ = v_a_3008_;
v_snd_3013_ = v_snd_3010_;
v_err_3014_ = v___x_3023_;
goto v___jp_3011_;
}
else
{
lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3033_; 
lean_inc(v_fst_3009_);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_a_3008_);
if (v_isSharedCheck_3033_ == 0)
{
lean_object* v_unused_3034_; lean_object* v_unused_3035_; 
v_unused_3034_ = lean_ctor_get(v_a_3008_, 1);
lean_dec(v_unused_3034_);
v_unused_3035_ = lean_ctor_get(v_a_3008_, 0);
lean_dec(v_unused_3035_);
v___x_3025_ = v_a_3008_;
v_isShared_3026_ = v_isSharedCheck_3033_;
goto v_resetjp_3024_;
}
else
{
lean_dec(v_a_3008_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3033_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v_it_x27_3029_; 
v___x_3027_ = lean_string_utf8_next_fast(v_fst_3009_, v_snd_3010_);
lean_dec(v_snd_3010_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 1, v___x_3027_);
v_it_x27_3029_ = v___x_3025_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_fst_3009_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v___x_3027_);
v_it_x27_3029_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_string_push(v_acc_3007_, v___x_3020_);
v_acc_3007_ = v___x_3030_;
v_a_3008_ = v_it_x27_3029_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_box(0);
lean_inc(v_snd_3010_);
v_pos_3012_ = v_a_3008_;
v_snd_3013_ = v_snd_3010_;
v_err_3014_ = v___x_3036_;
goto v___jp_3011_;
}
v___jp_3011_:
{
uint8_t v_decide_3015_; 
v_decide_3015_ = lean_nat_dec_eq(v_snd_3010_, v_snd_3013_);
lean_dec(v_snd_3013_);
lean_dec(v_snd_3010_);
if (v_decide_3015_ == 0)
{
lean_object* v___x_3016_; 
lean_dec_ref(v_acc_3007_);
lean_inc(v_err_3014_);
v___x_3016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3016_, 0, v_pos_3012_);
lean_ctor_set(v___x_3016_, 1, v_err_3014_);
return v___x_3016_;
}
else
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v_pos_3012_);
lean_ctor_set(v___x_3017_, 1, v_acc_3007_);
return v___x_3017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(lean_object* v_acc_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_fst_3042_; lean_object* v_snd_3043_; lean_object* v_pos_3045_; lean_object* v_snd_3046_; lean_object* v_err_3047_; lean_object* v___x_3051_; uint8_t v_decide_3052_; 
v_fst_3042_ = lean_ctor_get(v_a_3041_, 0);
v_snd_3043_ = lean_ctor_get(v_a_3041_, 1);
lean_inc(v_snd_3043_);
v___x_3051_ = lean_string_utf8_byte_size(v_fst_3042_);
v_decide_3052_ = lean_nat_dec_eq(v_snd_3043_, v___x_3051_);
if (v_decide_3052_ == 0)
{
uint32_t v___x_3053_; uint32_t v_c_3054_; uint8_t v___x_3055_; 
v___x_3053_ = 89;
v_c_3054_ = lean_string_utf8_get_fast(v_fst_3042_, v_snd_3043_);
v___x_3055_ = lean_uint32_dec_eq(v_c_3054_, v___x_3053_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1));
lean_inc(v_snd_3043_);
v_pos_3045_ = v_a_3041_;
v_snd_3046_ = v_snd_3043_;
v_err_3047_ = v___x_3056_;
goto v___jp_3044_;
}
else
{
lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3066_; 
lean_inc(v_fst_3042_);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_a_3041_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; lean_object* v_unused_3068_; 
v_unused_3067_ = lean_ctor_get(v_a_3041_, 1);
lean_dec(v_unused_3067_);
v_unused_3068_ = lean_ctor_get(v_a_3041_, 0);
lean_dec(v_unused_3068_);
v___x_3058_ = v_a_3041_;
v_isShared_3059_ = v_isSharedCheck_3066_;
goto v_resetjp_3057_;
}
else
{
lean_dec(v_a_3041_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3066_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v_it_x27_3062_; 
v___x_3060_ = lean_string_utf8_next_fast(v_fst_3042_, v_snd_3043_);
lean_dec(v_snd_3043_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 1, v___x_3060_);
v_it_x27_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_fst_3042_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3060_);
v_it_x27_3062_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_string_push(v_acc_3040_, v___x_3053_);
v_acc_3040_ = v___x_3063_;
v_a_3041_ = v_it_x27_3062_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3069_; 
v___x_3069_ = lean_box(0);
lean_inc(v_snd_3043_);
v_pos_3045_ = v_a_3041_;
v_snd_3046_ = v_snd_3043_;
v_err_3047_ = v___x_3069_;
goto v___jp_3044_;
}
v___jp_3044_:
{
uint8_t v_decide_3048_; 
v_decide_3048_ = lean_nat_dec_eq(v_snd_3043_, v_snd_3046_);
lean_dec(v_snd_3046_);
lean_dec(v_snd_3043_);
if (v_decide_3048_ == 0)
{
lean_object* v___x_3049_; 
lean_dec_ref(v_acc_3040_);
lean_inc(v_err_3047_);
v___x_3049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3049_, 0, v_pos_3045_);
lean_ctor_set(v___x_3049_, 1, v_err_3047_);
return v___x_3049_;
}
else
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v_pos_3045_);
lean_ctor_set(v___x_3050_, 1, v_acc_3040_);
return v___x_3050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(lean_object* v_acc_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_fst_3075_; lean_object* v_snd_3076_; lean_object* v_pos_3078_; lean_object* v_snd_3079_; lean_object* v_err_3080_; lean_object* v___x_3084_; uint8_t v_decide_3085_; 
v_fst_3075_ = lean_ctor_get(v_a_3074_, 0);
v_snd_3076_ = lean_ctor_get(v_a_3074_, 1);
lean_inc(v_snd_3076_);
v___x_3084_ = lean_string_utf8_byte_size(v_fst_3075_);
v_decide_3085_ = lean_nat_dec_eq(v_snd_3076_, v___x_3084_);
if (v_decide_3085_ == 0)
{
uint32_t v___x_3086_; uint32_t v_c_3087_; uint8_t v___x_3088_; 
v___x_3086_ = 110;
v_c_3087_ = lean_string_utf8_get_fast(v_fst_3075_, v_snd_3076_);
v___x_3088_ = lean_uint32_dec_eq(v_c_3087_, v___x_3086_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; 
v___x_3089_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1));
lean_inc(v_snd_3076_);
v_pos_3078_ = v_a_3074_;
v_snd_3079_ = v_snd_3076_;
v_err_3080_ = v___x_3089_;
goto v___jp_3077_;
}
else
{
lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3099_; 
lean_inc(v_fst_3075_);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_a_3074_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; lean_object* v_unused_3101_; 
v_unused_3100_ = lean_ctor_get(v_a_3074_, 1);
lean_dec(v_unused_3100_);
v_unused_3101_ = lean_ctor_get(v_a_3074_, 0);
lean_dec(v_unused_3101_);
v___x_3091_ = v_a_3074_;
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
else
{
lean_dec(v_a_3074_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v_it_x27_3095_; 
v___x_3093_ = lean_string_utf8_next_fast(v_fst_3075_, v_snd_3076_);
lean_dec(v_snd_3076_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 1, v___x_3093_);
v_it_x27_3095_ = v___x_3091_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_fst_3075_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3093_);
v_it_x27_3095_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_string_push(v_acc_3073_, v___x_3086_);
v_acc_3073_ = v___x_3096_;
v_a_3074_ = v_it_x27_3095_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3102_; 
v___x_3102_ = lean_box(0);
lean_inc(v_snd_3076_);
v_pos_3078_ = v_a_3074_;
v_snd_3079_ = v_snd_3076_;
v_err_3080_ = v___x_3102_;
goto v___jp_3077_;
}
v___jp_3077_:
{
uint8_t v_decide_3081_; 
v_decide_3081_ = lean_nat_dec_eq(v_snd_3076_, v_snd_3079_);
lean_dec(v_snd_3079_);
lean_dec(v_snd_3076_);
if (v_decide_3081_ == 0)
{
lean_object* v___x_3082_; 
lean_dec_ref(v_acc_3073_);
lean_inc(v_err_3080_);
v___x_3082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3082_, 0, v_pos_3078_);
lean_ctor_set(v___x_3082_, 1, v_err_3080_);
return v___x_3082_;
}
else
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v_pos_3078_);
lean_ctor_set(v___x_3083_, 1, v_acc_3073_);
return v___x_3083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(lean_object* v_acc_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v_fst_3108_; lean_object* v_snd_3109_; lean_object* v_pos_3111_; lean_object* v_snd_3112_; lean_object* v_err_3113_; lean_object* v___x_3117_; uint8_t v_decide_3118_; 
v_fst_3108_ = lean_ctor_get(v_a_3107_, 0);
v_snd_3109_ = lean_ctor_get(v_a_3107_, 1);
lean_inc(v_snd_3109_);
v___x_3117_ = lean_string_utf8_byte_size(v_fst_3108_);
v_decide_3118_ = lean_nat_dec_eq(v_snd_3109_, v___x_3117_);
if (v_decide_3118_ == 0)
{
uint32_t v___x_3119_; uint32_t v_c_3120_; uint8_t v___x_3121_; 
v___x_3119_ = 71;
v_c_3120_ = lean_string_utf8_get_fast(v_fst_3108_, v_snd_3109_);
v___x_3121_ = lean_uint32_dec_eq(v_c_3120_, v___x_3119_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
v___x_3122_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1));
lean_inc(v_snd_3109_);
v_pos_3111_ = v_a_3107_;
v_snd_3112_ = v_snd_3109_;
v_err_3113_ = v___x_3122_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3132_; 
lean_inc(v_fst_3108_);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_a_3107_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; lean_object* v_unused_3134_; 
v_unused_3133_ = lean_ctor_get(v_a_3107_, 1);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_a_3107_, 0);
lean_dec(v_unused_3134_);
v___x_3124_ = v_a_3107_;
v_isShared_3125_ = v_isSharedCheck_3132_;
goto v_resetjp_3123_;
}
else
{
lean_dec(v_a_3107_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3132_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v_it_x27_3128_; 
v___x_3126_ = lean_string_utf8_next_fast(v_fst_3108_, v_snd_3109_);
lean_dec(v_snd_3109_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 1, v___x_3126_);
v_it_x27_3128_ = v___x_3124_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_fst_3108_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v___x_3126_);
v_it_x27_3128_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3129_; 
v___x_3129_ = lean_string_push(v_acc_3106_, v___x_3119_);
v_acc_3106_ = v___x_3129_;
v_a_3107_ = v_it_x27_3128_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_box(0);
lean_inc(v_snd_3109_);
v_pos_3111_ = v_a_3107_;
v_snd_3112_ = v_snd_3109_;
v_err_3113_ = v___x_3135_;
goto v___jp_3110_;
}
v___jp_3110_:
{
uint8_t v_decide_3114_; 
v_decide_3114_ = lean_nat_dec_eq(v_snd_3109_, v_snd_3112_);
lean_dec(v_snd_3112_);
lean_dec(v_snd_3109_);
if (v_decide_3114_ == 0)
{
lean_object* v___x_3115_; 
lean_dec_ref(v_acc_3106_);
lean_inc(v_err_3113_);
v___x_3115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3115_, 0, v_pos_3111_);
lean_ctor_set(v___x_3115_, 1, v_err_3113_);
return v___x_3115_;
}
else
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v_pos_3111_);
lean_ctor_set(v___x_3116_, 1, v_acc_3106_);
return v___x_3116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(lean_object* v_acc_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_fst_3141_; lean_object* v_snd_3142_; lean_object* v_pos_3144_; lean_object* v_snd_3145_; lean_object* v_err_3146_; lean_object* v___x_3150_; uint8_t v_decide_3151_; 
v_fst_3141_ = lean_ctor_get(v_a_3140_, 0);
v_snd_3142_ = lean_ctor_get(v_a_3140_, 1);
lean_inc(v_snd_3142_);
v___x_3150_ = lean_string_utf8_byte_size(v_fst_3141_);
v_decide_3151_ = lean_nat_dec_eq(v_snd_3142_, v___x_3150_);
if (v_decide_3151_ == 0)
{
uint32_t v___x_3152_; uint32_t v_c_3153_; uint8_t v___x_3154_; 
v___x_3152_ = 86;
v_c_3153_ = lean_string_utf8_get_fast(v_fst_3141_, v_snd_3142_);
v___x_3154_ = lean_uint32_dec_eq(v_c_3153_, v___x_3152_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; 
v___x_3155_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1));
lean_inc(v_snd_3142_);
v_pos_3144_ = v_a_3140_;
v_snd_3145_ = v_snd_3142_;
v_err_3146_ = v___x_3155_;
goto v___jp_3143_;
}
else
{
lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3165_; 
lean_inc(v_fst_3141_);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_a_3140_);
if (v_isSharedCheck_3165_ == 0)
{
lean_object* v_unused_3166_; lean_object* v_unused_3167_; 
v_unused_3166_ = lean_ctor_get(v_a_3140_, 1);
lean_dec(v_unused_3166_);
v_unused_3167_ = lean_ctor_get(v_a_3140_, 0);
lean_dec(v_unused_3167_);
v___x_3157_ = v_a_3140_;
v_isShared_3158_ = v_isSharedCheck_3165_;
goto v_resetjp_3156_;
}
else
{
lean_dec(v_a_3140_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3165_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v_it_x27_3161_; 
v___x_3159_ = lean_string_utf8_next_fast(v_fst_3141_, v_snd_3142_);
lean_dec(v_snd_3142_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 1, v___x_3159_);
v_it_x27_3161_ = v___x_3157_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_fst_3141_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v___x_3159_);
v_it_x27_3161_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3162_; 
v___x_3162_ = lean_string_push(v_acc_3139_, v___x_3152_);
v_acc_3139_ = v___x_3162_;
v_a_3140_ = v_it_x27_3161_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_box(0);
lean_inc(v_snd_3142_);
v_pos_3144_ = v_a_3140_;
v_snd_3145_ = v_snd_3142_;
v_err_3146_ = v___x_3168_;
goto v___jp_3143_;
}
v___jp_3143_:
{
uint8_t v_decide_3147_; 
v_decide_3147_ = lean_nat_dec_eq(v_snd_3142_, v_snd_3145_);
lean_dec(v_snd_3145_);
lean_dec(v_snd_3142_);
if (v_decide_3147_ == 0)
{
lean_object* v___x_3148_; 
lean_dec_ref(v_acc_3139_);
lean_inc(v_err_3146_);
v___x_3148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3148_, 0, v_pos_3144_);
lean_ctor_set(v___x_3148_, 1, v_err_3146_);
return v___x_3148_;
}
else
{
lean_object* v___x_3149_; 
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v_pos_3144_);
lean_ctor_set(v___x_3149_, 1, v_acc_3139_);
return v___x_3149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(lean_object* v_acc_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_fst_3174_; lean_object* v_snd_3175_; lean_object* v_pos_3177_; lean_object* v_snd_3178_; lean_object* v_err_3179_; lean_object* v___x_3183_; uint8_t v_decide_3184_; 
v_fst_3174_ = lean_ctor_get(v_a_3173_, 0);
v_snd_3175_ = lean_ctor_get(v_a_3173_, 1);
lean_inc(v_snd_3175_);
v___x_3183_ = lean_string_utf8_byte_size(v_fst_3174_);
v_decide_3184_ = lean_nat_dec_eq(v_snd_3175_, v___x_3183_);
if (v_decide_3184_ == 0)
{
uint32_t v___x_3185_; uint32_t v_c_3186_; uint8_t v___x_3187_; 
v___x_3185_ = 83;
v_c_3186_ = lean_string_utf8_get_fast(v_fst_3174_, v_snd_3175_);
v___x_3187_ = lean_uint32_dec_eq(v_c_3186_, v___x_3185_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1));
lean_inc(v_snd_3175_);
v_pos_3177_ = v_a_3173_;
v_snd_3178_ = v_snd_3175_;
v_err_3179_ = v___x_3188_;
goto v___jp_3176_;
}
else
{
lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3198_; 
lean_inc(v_fst_3174_);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_a_3173_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; lean_object* v_unused_3200_; 
v_unused_3199_ = lean_ctor_get(v_a_3173_, 1);
lean_dec(v_unused_3199_);
v_unused_3200_ = lean_ctor_get(v_a_3173_, 0);
lean_dec(v_unused_3200_);
v___x_3190_ = v_a_3173_;
v_isShared_3191_ = v_isSharedCheck_3198_;
goto v_resetjp_3189_;
}
else
{
lean_dec(v_a_3173_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3198_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3192_; lean_object* v_it_x27_3194_; 
v___x_3192_ = lean_string_utf8_next_fast(v_fst_3174_, v_snd_3175_);
lean_dec(v_snd_3175_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 1, v___x_3192_);
v_it_x27_3194_ = v___x_3190_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_fst_3174_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3192_);
v_it_x27_3194_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3195_; 
v___x_3195_ = lean_string_push(v_acc_3172_, v___x_3185_);
v_acc_3172_ = v___x_3195_;
v_a_3173_ = v_it_x27_3194_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_box(0);
lean_inc(v_snd_3175_);
v_pos_3177_ = v_a_3173_;
v_snd_3178_ = v_snd_3175_;
v_err_3179_ = v___x_3201_;
goto v___jp_3176_;
}
v___jp_3176_:
{
uint8_t v_decide_3180_; 
v_decide_3180_ = lean_nat_dec_eq(v_snd_3175_, v_snd_3178_);
lean_dec(v_snd_3178_);
lean_dec(v_snd_3175_);
if (v_decide_3180_ == 0)
{
lean_object* v___x_3181_; 
lean_dec_ref(v_acc_3172_);
lean_inc(v_err_3179_);
v___x_3181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3181_, 0, v_pos_3177_);
lean_ctor_set(v___x_3181_, 1, v_err_3179_);
return v___x_3181_;
}
else
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v_pos_3177_);
lean_ctor_set(v___x_3182_, 1, v_acc_3172_);
return v___x_3182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(lean_object* v_acc_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v_fst_3207_; lean_object* v_snd_3208_; lean_object* v_pos_3210_; lean_object* v_snd_3211_; lean_object* v_err_3212_; lean_object* v___x_3216_; uint8_t v_decide_3217_; 
v_fst_3207_ = lean_ctor_get(v_a_3206_, 0);
v_snd_3208_ = lean_ctor_get(v_a_3206_, 1);
lean_inc(v_snd_3208_);
v___x_3216_ = lean_string_utf8_byte_size(v_fst_3207_);
v_decide_3217_ = lean_nat_dec_eq(v_snd_3208_, v___x_3216_);
if (v_decide_3217_ == 0)
{
uint32_t v___x_3218_; uint32_t v_c_3219_; uint8_t v___x_3220_; 
v___x_3218_ = 104;
v_c_3219_ = lean_string_utf8_get_fast(v_fst_3207_, v_snd_3208_);
v___x_3220_ = lean_uint32_dec_eq(v_c_3219_, v___x_3218_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
v___x_3221_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1));
lean_inc(v_snd_3208_);
v_pos_3210_ = v_a_3206_;
v_snd_3211_ = v_snd_3208_;
v_err_3212_ = v___x_3221_;
goto v___jp_3209_;
}
else
{
lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3231_; 
lean_inc(v_fst_3207_);
v_isSharedCheck_3231_ = !lean_is_exclusive(v_a_3206_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; lean_object* v_unused_3233_; 
v_unused_3232_ = lean_ctor_get(v_a_3206_, 1);
lean_dec(v_unused_3232_);
v_unused_3233_ = lean_ctor_get(v_a_3206_, 0);
lean_dec(v_unused_3233_);
v___x_3223_ = v_a_3206_;
v_isShared_3224_ = v_isSharedCheck_3231_;
goto v_resetjp_3222_;
}
else
{
lean_dec(v_a_3206_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3231_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v_it_x27_3227_; 
v___x_3225_ = lean_string_utf8_next_fast(v_fst_3207_, v_snd_3208_);
lean_dec(v_snd_3208_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 1, v___x_3225_);
v_it_x27_3227_ = v___x_3223_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_fst_3207_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v___x_3225_);
v_it_x27_3227_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_string_push(v_acc_3205_, v___x_3218_);
v_acc_3205_ = v___x_3228_;
v_a_3206_ = v_it_x27_3227_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_box(0);
lean_inc(v_snd_3208_);
v_pos_3210_ = v_a_3206_;
v_snd_3211_ = v_snd_3208_;
v_err_3212_ = v___x_3234_;
goto v___jp_3209_;
}
v___jp_3209_:
{
uint8_t v_decide_3213_; 
v_decide_3213_ = lean_nat_dec_eq(v_snd_3208_, v_snd_3211_);
lean_dec(v_snd_3211_);
lean_dec(v_snd_3208_);
if (v_decide_3213_ == 0)
{
lean_object* v___x_3214_; 
lean_dec_ref(v_acc_3205_);
lean_inc(v_err_3212_);
v___x_3214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3214_, 0, v_pos_3210_);
lean_ctor_set(v___x_3214_, 1, v_err_3212_);
return v___x_3214_;
}
else
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v_pos_3210_);
lean_ctor_set(v___x_3215_, 1, v_acc_3205_);
return v___x_3215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(lean_object* v_acc_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_fst_3240_; lean_object* v_snd_3241_; lean_object* v_pos_3243_; lean_object* v_snd_3244_; lean_object* v_err_3245_; lean_object* v___x_3249_; uint8_t v_decide_3250_; 
v_fst_3240_ = lean_ctor_get(v_a_3239_, 0);
v_snd_3241_ = lean_ctor_get(v_a_3239_, 1);
lean_inc(v_snd_3241_);
v___x_3249_ = lean_string_utf8_byte_size(v_fst_3240_);
v_decide_3250_ = lean_nat_dec_eq(v_snd_3241_, v___x_3249_);
if (v_decide_3250_ == 0)
{
uint32_t v___x_3251_; uint32_t v_c_3252_; uint8_t v___x_3253_; 
v___x_3251_ = 81;
v_c_3252_ = lean_string_utf8_get_fast(v_fst_3240_, v_snd_3241_);
v___x_3253_ = lean_uint32_dec_eq(v_c_3252_, v___x_3251_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; 
v___x_3254_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1));
lean_inc(v_snd_3241_);
v_pos_3243_ = v_a_3239_;
v_snd_3244_ = v_snd_3241_;
v_err_3245_ = v___x_3254_;
goto v___jp_3242_;
}
else
{
lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3264_; 
lean_inc(v_fst_3240_);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_a_3239_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; lean_object* v_unused_3266_; 
v_unused_3265_ = lean_ctor_get(v_a_3239_, 1);
lean_dec(v_unused_3265_);
v_unused_3266_ = lean_ctor_get(v_a_3239_, 0);
lean_dec(v_unused_3266_);
v___x_3256_ = v_a_3239_;
v_isShared_3257_ = v_isSharedCheck_3264_;
goto v_resetjp_3255_;
}
else
{
lean_dec(v_a_3239_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3264_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v_it_x27_3260_; 
v___x_3258_ = lean_string_utf8_next_fast(v_fst_3240_, v_snd_3241_);
lean_dec(v_snd_3241_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 1, v___x_3258_);
v_it_x27_3260_ = v___x_3256_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_fst_3240_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v___x_3258_);
v_it_x27_3260_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_string_push(v_acc_3238_, v___x_3251_);
v_acc_3238_ = v___x_3261_;
v_a_3239_ = v_it_x27_3260_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_box(0);
lean_inc(v_snd_3241_);
v_pos_3243_ = v_a_3239_;
v_snd_3244_ = v_snd_3241_;
v_err_3245_ = v___x_3267_;
goto v___jp_3242_;
}
v___jp_3242_:
{
uint8_t v_decide_3246_; 
v_decide_3246_ = lean_nat_dec_eq(v_snd_3241_, v_snd_3244_);
lean_dec(v_snd_3244_);
lean_dec(v_snd_3241_);
if (v_decide_3246_ == 0)
{
lean_object* v___x_3247_; 
lean_dec_ref(v_acc_3238_);
lean_inc(v_err_3245_);
v___x_3247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3247_, 0, v_pos_3243_);
lean_ctor_set(v___x_3247_, 1, v_err_3245_);
return v___x_3247_;
}
else
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_pos_3243_);
lean_ctor_set(v___x_3248_, 1, v_acc_3238_);
return v___x_3248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(lean_object* v_acc_3271_, lean_object* v_a_3272_){
_start:
{
lean_object* v_fst_3273_; lean_object* v_snd_3274_; lean_object* v_pos_3276_; lean_object* v_snd_3277_; lean_object* v_err_3278_; lean_object* v___x_3282_; uint8_t v_decide_3283_; 
v_fst_3273_ = lean_ctor_get(v_a_3272_, 0);
v_snd_3274_ = lean_ctor_get(v_a_3272_, 1);
lean_inc(v_snd_3274_);
v___x_3282_ = lean_string_utf8_byte_size(v_fst_3273_);
v_decide_3283_ = lean_nat_dec_eq(v_snd_3274_, v___x_3282_);
if (v_decide_3283_ == 0)
{
uint32_t v___x_3284_; uint32_t v_c_3285_; uint8_t v___x_3286_; 
v___x_3284_ = 68;
v_c_3285_ = lean_string_utf8_get_fast(v_fst_3273_, v_snd_3274_);
v___x_3286_ = lean_uint32_dec_eq(v_c_3285_, v___x_3284_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; 
v___x_3287_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1));
lean_inc(v_snd_3274_);
v_pos_3276_ = v_a_3272_;
v_snd_3277_ = v_snd_3274_;
v_err_3278_ = v___x_3287_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3297_; 
lean_inc(v_fst_3273_);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_a_3272_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; lean_object* v_unused_3299_; 
v_unused_3298_ = lean_ctor_get(v_a_3272_, 1);
lean_dec(v_unused_3298_);
v_unused_3299_ = lean_ctor_get(v_a_3272_, 0);
lean_dec(v_unused_3299_);
v___x_3289_ = v_a_3272_;
v_isShared_3290_ = v_isSharedCheck_3297_;
goto v_resetjp_3288_;
}
else
{
lean_dec(v_a_3272_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3297_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; lean_object* v_it_x27_3293_; 
v___x_3291_ = lean_string_utf8_next_fast(v_fst_3273_, v_snd_3274_);
lean_dec(v_snd_3274_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 1, v___x_3291_);
v_it_x27_3293_ = v___x_3289_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_fst_3273_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v___x_3291_);
v_it_x27_3293_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
lean_object* v___x_3294_; 
v___x_3294_ = lean_string_push(v_acc_3271_, v___x_3284_);
v_acc_3271_ = v___x_3294_;
v_a_3272_ = v_it_x27_3293_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_box(0);
lean_inc(v_snd_3274_);
v_pos_3276_ = v_a_3272_;
v_snd_3277_ = v_snd_3274_;
v_err_3278_ = v___x_3300_;
goto v___jp_3275_;
}
v___jp_3275_:
{
uint8_t v_decide_3279_; 
v_decide_3279_ = lean_nat_dec_eq(v_snd_3274_, v_snd_3277_);
lean_dec(v_snd_3277_);
lean_dec(v_snd_3274_);
if (v_decide_3279_ == 0)
{
lean_object* v___x_3280_; 
lean_dec_ref(v_acc_3271_);
lean_inc(v_err_3278_);
v___x_3280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_pos_3276_);
lean_ctor_set(v___x_3280_, 1, v_err_3278_);
return v___x_3280_;
}
else
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3281_, 0, v_pos_3276_);
lean_ctor_set(v___x_3281_, 1, v_acc_3271_);
return v___x_3281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(lean_object* v_acc_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_fst_3306_; lean_object* v_snd_3307_; lean_object* v_pos_3309_; lean_object* v_snd_3310_; lean_object* v_err_3311_; lean_object* v___x_3315_; uint8_t v_decide_3316_; 
v_fst_3306_ = lean_ctor_get(v_a_3305_, 0);
v_snd_3307_ = lean_ctor_get(v_a_3305_, 1);
lean_inc(v_snd_3307_);
v___x_3315_ = lean_string_utf8_byte_size(v_fst_3306_);
v_decide_3316_ = lean_nat_dec_eq(v_snd_3307_, v___x_3315_);
if (v_decide_3316_ == 0)
{
uint32_t v___x_3317_; uint32_t v_c_3318_; uint8_t v___x_3319_; 
v___x_3317_ = 88;
v_c_3318_ = lean_string_utf8_get_fast(v_fst_3306_, v_snd_3307_);
v___x_3319_ = lean_uint32_dec_eq(v_c_3318_, v___x_3317_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; 
v___x_3320_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1));
lean_inc(v_snd_3307_);
v_pos_3309_ = v_a_3305_;
v_snd_3310_ = v_snd_3307_;
v_err_3311_ = v___x_3320_;
goto v___jp_3308_;
}
else
{
lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3330_; 
lean_inc(v_fst_3306_);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_a_3305_);
if (v_isSharedCheck_3330_ == 0)
{
lean_object* v_unused_3331_; lean_object* v_unused_3332_; 
v_unused_3331_ = lean_ctor_get(v_a_3305_, 1);
lean_dec(v_unused_3331_);
v_unused_3332_ = lean_ctor_get(v_a_3305_, 0);
lean_dec(v_unused_3332_);
v___x_3322_ = v_a_3305_;
v_isShared_3323_ = v_isSharedCheck_3330_;
goto v_resetjp_3321_;
}
else
{
lean_dec(v_a_3305_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3330_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3324_; lean_object* v_it_x27_3326_; 
v___x_3324_ = lean_string_utf8_next_fast(v_fst_3306_, v_snd_3307_);
lean_dec(v_snd_3307_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 1, v___x_3324_);
v_it_x27_3326_ = v___x_3322_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_fst_3306_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v___x_3324_);
v_it_x27_3326_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_string_push(v_acc_3304_, v___x_3317_);
v_acc_3304_ = v___x_3327_;
v_a_3305_ = v_it_x27_3326_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_box(0);
lean_inc(v_snd_3307_);
v_pos_3309_ = v_a_3305_;
v_snd_3310_ = v_snd_3307_;
v_err_3311_ = v___x_3333_;
goto v___jp_3308_;
}
v___jp_3308_:
{
uint8_t v_decide_3312_; 
v_decide_3312_ = lean_nat_dec_eq(v_snd_3307_, v_snd_3310_);
lean_dec(v_snd_3310_);
lean_dec(v_snd_3307_);
if (v_decide_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_dec_ref(v_acc_3304_);
lean_inc(v_err_3311_);
v___x_3313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_pos_3309_);
lean_ctor_set(v___x_3313_, 1, v_err_3311_);
return v___x_3313_;
}
else
{
lean_object* v___x_3314_; 
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v_pos_3309_);
lean_ctor_set(v___x_3314_, 1, v_acc_3304_);
return v___x_3314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(lean_object* v_acc_3337_, lean_object* v_a_3338_){
_start:
{
lean_object* v_fst_3339_; lean_object* v_snd_3340_; lean_object* v_pos_3342_; lean_object* v_snd_3343_; lean_object* v_err_3344_; lean_object* v___x_3348_; uint8_t v_decide_3349_; 
v_fst_3339_ = lean_ctor_get(v_a_3338_, 0);
v_snd_3340_ = lean_ctor_get(v_a_3338_, 1);
lean_inc(v_snd_3340_);
v___x_3348_ = lean_string_utf8_byte_size(v_fst_3339_);
v_decide_3349_ = lean_nat_dec_eq(v_snd_3340_, v___x_3348_);
if (v_decide_3349_ == 0)
{
uint32_t v___x_3350_; uint32_t v_c_3351_; uint8_t v___x_3352_; 
v___x_3350_ = 122;
v_c_3351_ = lean_string_utf8_get_fast(v_fst_3339_, v_snd_3340_);
v___x_3352_ = lean_uint32_dec_eq(v_c_3351_, v___x_3350_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; 
v___x_3353_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1));
lean_inc(v_snd_3340_);
v_pos_3342_ = v_a_3338_;
v_snd_3343_ = v_snd_3340_;
v_err_3344_ = v___x_3353_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3363_; 
lean_inc(v_fst_3339_);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_a_3338_);
if (v_isSharedCheck_3363_ == 0)
{
lean_object* v_unused_3364_; lean_object* v_unused_3365_; 
v_unused_3364_ = lean_ctor_get(v_a_3338_, 1);
lean_dec(v_unused_3364_);
v_unused_3365_ = lean_ctor_get(v_a_3338_, 0);
lean_dec(v_unused_3365_);
v___x_3355_ = v_a_3338_;
v_isShared_3356_ = v_isSharedCheck_3363_;
goto v_resetjp_3354_;
}
else
{
lean_dec(v_a_3338_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3363_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v_it_x27_3359_; 
v___x_3357_ = lean_string_utf8_next_fast(v_fst_3339_, v_snd_3340_);
lean_dec(v_snd_3340_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 1, v___x_3357_);
v_it_x27_3359_ = v___x_3355_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_fst_3339_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v___x_3357_);
v_it_x27_3359_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_string_push(v_acc_3337_, v___x_3350_);
v_acc_3337_ = v___x_3360_;
v_a_3338_ = v_it_x27_3359_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_box(0);
lean_inc(v_snd_3340_);
v_pos_3342_ = v_a_3338_;
v_snd_3343_ = v_snd_3340_;
v_err_3344_ = v___x_3366_;
goto v___jp_3341_;
}
v___jp_3341_:
{
uint8_t v_decide_3345_; 
v_decide_3345_ = lean_nat_dec_eq(v_snd_3340_, v_snd_3343_);
lean_dec(v_snd_3343_);
lean_dec(v_snd_3340_);
if (v_decide_3345_ == 0)
{
lean_object* v___x_3346_; 
lean_dec_ref(v_acc_3337_);
lean_inc(v_err_3344_);
v___x_3346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3346_, 0, v_pos_3342_);
lean_ctor_set(v___x_3346_, 1, v_err_3344_);
return v___x_3346_;
}
else
{
lean_object* v___x_3347_; 
v___x_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3347_, 0, v_pos_3342_);
lean_ctor_set(v___x_3347_, 1, v_acc_3337_);
return v___x_3347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(lean_object* v_acc_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_fst_3372_; lean_object* v_snd_3373_; lean_object* v_pos_3375_; lean_object* v_snd_3376_; lean_object* v_err_3377_; lean_object* v___x_3381_; uint8_t v_decide_3382_; 
v_fst_3372_ = lean_ctor_get(v_a_3371_, 0);
v_snd_3373_ = lean_ctor_get(v_a_3371_, 1);
lean_inc(v_snd_3373_);
v___x_3381_ = lean_string_utf8_byte_size(v_fst_3372_);
v_decide_3382_ = lean_nat_dec_eq(v_snd_3373_, v___x_3381_);
if (v_decide_3382_ == 0)
{
uint32_t v___x_3383_; uint32_t v_c_3384_; uint8_t v___x_3385_; 
v___x_3383_ = 115;
v_c_3384_ = lean_string_utf8_get_fast(v_fst_3372_, v_snd_3373_);
v___x_3385_ = lean_uint32_dec_eq(v_c_3384_, v___x_3383_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; 
v___x_3386_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1));
lean_inc(v_snd_3373_);
v_pos_3375_ = v_a_3371_;
v_snd_3376_ = v_snd_3373_;
v_err_3377_ = v___x_3386_;
goto v___jp_3374_;
}
else
{
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3396_; 
lean_inc(v_fst_3372_);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_a_3371_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; lean_object* v_unused_3398_; 
v_unused_3397_ = lean_ctor_get(v_a_3371_, 1);
lean_dec(v_unused_3397_);
v_unused_3398_ = lean_ctor_get(v_a_3371_, 0);
lean_dec(v_unused_3398_);
v___x_3388_ = v_a_3371_;
v_isShared_3389_ = v_isSharedCheck_3396_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v_a_3371_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3396_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v_it_x27_3392_; 
v___x_3390_ = lean_string_utf8_next_fast(v_fst_3372_, v_snd_3373_);
lean_dec(v_snd_3373_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 1, v___x_3390_);
v_it_x27_3392_ = v___x_3388_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_fst_3372_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v___x_3390_);
v_it_x27_3392_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; 
v___x_3393_ = lean_string_push(v_acc_3370_, v___x_3383_);
v_acc_3370_ = v___x_3393_;
v_a_3371_ = v_it_x27_3392_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_box(0);
lean_inc(v_snd_3373_);
v_pos_3375_ = v_a_3371_;
v_snd_3376_ = v_snd_3373_;
v_err_3377_ = v___x_3399_;
goto v___jp_3374_;
}
v___jp_3374_:
{
uint8_t v_decide_3378_; 
v_decide_3378_ = lean_nat_dec_eq(v_snd_3373_, v_snd_3376_);
lean_dec(v_snd_3376_);
lean_dec(v_snd_3373_);
if (v_decide_3378_ == 0)
{
lean_object* v___x_3379_; 
lean_dec_ref(v_acc_3370_);
lean_inc(v_err_3377_);
v___x_3379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3379_, 0, v_pos_3375_);
lean_ctor_set(v___x_3379_, 1, v_err_3377_);
return v___x_3379_;
}
else
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3380_, 0, v_pos_3375_);
lean_ctor_set(v___x_3380_, 1, v_acc_3370_);
return v___x_3380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(lean_object* v_acc_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v_fst_3405_; lean_object* v_snd_3406_; lean_object* v_pos_3408_; lean_object* v_snd_3409_; lean_object* v_err_3410_; lean_object* v___x_3414_; uint8_t v_decide_3415_; 
v_fst_3405_ = lean_ctor_get(v_a_3404_, 0);
v_snd_3406_ = lean_ctor_get(v_a_3404_, 1);
lean_inc(v_snd_3406_);
v___x_3414_ = lean_string_utf8_byte_size(v_fst_3405_);
v_decide_3415_ = lean_nat_dec_eq(v_snd_3406_, v___x_3414_);
if (v_decide_3415_ == 0)
{
uint32_t v___x_3416_; uint32_t v_c_3417_; uint8_t v___x_3418_; 
v___x_3416_ = 75;
v_c_3417_ = lean_string_utf8_get_fast(v_fst_3405_, v_snd_3406_);
v___x_3418_ = lean_uint32_dec_eq(v_c_3417_, v___x_3416_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; 
v___x_3419_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1));
lean_inc(v_snd_3406_);
v_pos_3408_ = v_a_3404_;
v_snd_3409_ = v_snd_3406_;
v_err_3410_ = v___x_3419_;
goto v___jp_3407_;
}
else
{
lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3429_; 
lean_inc(v_fst_3405_);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_a_3404_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; lean_object* v_unused_3431_; 
v_unused_3430_ = lean_ctor_get(v_a_3404_, 1);
lean_dec(v_unused_3430_);
v_unused_3431_ = lean_ctor_get(v_a_3404_, 0);
lean_dec(v_unused_3431_);
v___x_3421_ = v_a_3404_;
v_isShared_3422_ = v_isSharedCheck_3429_;
goto v_resetjp_3420_;
}
else
{
lean_dec(v_a_3404_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3429_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; lean_object* v_it_x27_3425_; 
v___x_3423_ = lean_string_utf8_next_fast(v_fst_3405_, v_snd_3406_);
lean_dec(v_snd_3406_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 1, v___x_3423_);
v_it_x27_3425_ = v___x_3421_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_fst_3405_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v___x_3423_);
v_it_x27_3425_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_string_push(v_acc_3403_, v___x_3416_);
v_acc_3403_ = v___x_3426_;
v_a_3404_ = v_it_x27_3425_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3432_; 
v___x_3432_ = lean_box(0);
lean_inc(v_snd_3406_);
v_pos_3408_ = v_a_3404_;
v_snd_3409_ = v_snd_3406_;
v_err_3410_ = v___x_3432_;
goto v___jp_3407_;
}
v___jp_3407_:
{
uint8_t v_decide_3411_; 
v_decide_3411_ = lean_nat_dec_eq(v_snd_3406_, v_snd_3409_);
lean_dec(v_snd_3409_);
lean_dec(v_snd_3406_);
if (v_decide_3411_ == 0)
{
lean_object* v___x_3412_; 
lean_dec_ref(v_acc_3403_);
lean_inc(v_err_3410_);
v___x_3412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3412_, 0, v_pos_3408_);
lean_ctor_set(v___x_3412_, 1, v_err_3410_);
return v___x_3412_;
}
else
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v_pos_3408_);
lean_ctor_set(v___x_3413_, 1, v_acc_3403_);
return v___x_3413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(lean_object* v_acc_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v_fst_3438_; lean_object* v_snd_3439_; lean_object* v_pos_3441_; lean_object* v_snd_3442_; lean_object* v_err_3443_; lean_object* v___x_3447_; uint8_t v_decide_3448_; 
v_fst_3438_ = lean_ctor_get(v_a_3437_, 0);
v_snd_3439_ = lean_ctor_get(v_a_3437_, 1);
lean_inc(v_snd_3439_);
v___x_3447_ = lean_string_utf8_byte_size(v_fst_3438_);
v_decide_3448_ = lean_nat_dec_eq(v_snd_3439_, v___x_3447_);
if (v_decide_3448_ == 0)
{
uint32_t v___x_3449_; uint32_t v_c_3450_; uint8_t v___x_3451_; 
v___x_3449_ = 101;
v_c_3450_ = lean_string_utf8_get_fast(v_fst_3438_, v_snd_3439_);
v___x_3451_ = lean_uint32_dec_eq(v_c_3450_, v___x_3449_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1));
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
uint8_t v_decide_3444_; 
v_decide_3444_ = lean_nat_dec_eq(v_snd_3439_, v_snd_3442_);
lean_dec(v_snd_3442_);
lean_dec(v_snd_3439_);
if (v_decide_3444_ == 0)
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(lean_object* v_acc_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v_fst_3471_; lean_object* v_snd_3472_; lean_object* v_pos_3474_; lean_object* v_snd_3475_; lean_object* v_err_3476_; lean_object* v___x_3480_; uint8_t v_decide_3481_; 
v_fst_3471_ = lean_ctor_get(v_a_3470_, 0);
v_snd_3472_ = lean_ctor_get(v_a_3470_, 1);
lean_inc(v_snd_3472_);
v___x_3480_ = lean_string_utf8_byte_size(v_fst_3471_);
v_decide_3481_ = lean_nat_dec_eq(v_snd_3472_, v___x_3480_);
if (v_decide_3481_ == 0)
{
uint32_t v___x_3482_; uint32_t v_c_3483_; uint8_t v___x_3484_; 
v___x_3482_ = 77;
v_c_3483_ = lean_string_utf8_get_fast(v_fst_3471_, v_snd_3472_);
v___x_3484_ = lean_uint32_dec_eq(v_c_3483_, v___x_3482_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1));
lean_inc(v_snd_3472_);
v_pos_3474_ = v_a_3470_;
v_snd_3475_ = v_snd_3472_;
v_err_3476_ = v___x_3485_;
goto v___jp_3473_;
}
else
{
lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3495_; 
lean_inc(v_fst_3471_);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_a_3470_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; lean_object* v_unused_3497_; 
v_unused_3496_ = lean_ctor_get(v_a_3470_, 1);
lean_dec(v_unused_3496_);
v_unused_3497_ = lean_ctor_get(v_a_3470_, 0);
lean_dec(v_unused_3497_);
v___x_3487_ = v_a_3470_;
v_isShared_3488_ = v_isSharedCheck_3495_;
goto v_resetjp_3486_;
}
else
{
lean_dec(v_a_3470_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3495_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; lean_object* v_it_x27_3491_; 
v___x_3489_ = lean_string_utf8_next_fast(v_fst_3471_, v_snd_3472_);
lean_dec(v_snd_3472_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3489_);
v_it_x27_3491_ = v___x_3487_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_fst_3471_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v___x_3489_);
v_it_x27_3491_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; 
v___x_3492_ = lean_string_push(v_acc_3469_, v___x_3482_);
v_acc_3469_ = v___x_3492_;
v_a_3470_ = v_it_x27_3491_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_box(0);
lean_inc(v_snd_3472_);
v_pos_3474_ = v_a_3470_;
v_snd_3475_ = v_snd_3472_;
v_err_3476_ = v___x_3498_;
goto v___jp_3473_;
}
v___jp_3473_:
{
uint8_t v_decide_3477_; 
v_decide_3477_ = lean_nat_dec_eq(v_snd_3472_, v_snd_3475_);
lean_dec(v_snd_3475_);
lean_dec(v_snd_3472_);
if (v_decide_3477_ == 0)
{
lean_object* v___x_3478_; 
lean_dec_ref(v_acc_3469_);
lean_inc(v_err_3476_);
v___x_3478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3478_, 0, v_pos_3474_);
lean_ctor_set(v___x_3478_, 1, v_err_3476_);
return v___x_3478_;
}
else
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3479_, 0, v_pos_3474_);
lean_ctor_set(v___x_3479_, 1, v_acc_3469_);
return v___x_3479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(lean_object* v_acc_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v_fst_3504_; lean_object* v_snd_3505_; lean_object* v_pos_3507_; lean_object* v_snd_3508_; lean_object* v_err_3509_; lean_object* v___x_3513_; uint8_t v_decide_3514_; 
v_fst_3504_ = lean_ctor_get(v_a_3503_, 0);
v_snd_3505_ = lean_ctor_get(v_a_3503_, 1);
lean_inc(v_snd_3505_);
v___x_3513_ = lean_string_utf8_byte_size(v_fst_3504_);
v_decide_3514_ = lean_nat_dec_eq(v_snd_3505_, v___x_3513_);
if (v_decide_3514_ == 0)
{
uint32_t v___x_3515_; uint32_t v_c_3516_; uint8_t v___x_3517_; 
v___x_3515_ = 119;
v_c_3516_ = lean_string_utf8_get_fast(v_fst_3504_, v_snd_3505_);
v___x_3517_ = lean_uint32_dec_eq(v_c_3516_, v___x_3515_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; 
v___x_3518_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1));
lean_inc(v_snd_3505_);
v_pos_3507_ = v_a_3503_;
v_snd_3508_ = v_snd_3505_;
v_err_3509_ = v___x_3518_;
goto v___jp_3506_;
}
else
{
lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3528_; 
lean_inc(v_fst_3504_);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_a_3503_);
if (v_isSharedCheck_3528_ == 0)
{
lean_object* v_unused_3529_; lean_object* v_unused_3530_; 
v_unused_3529_ = lean_ctor_get(v_a_3503_, 1);
lean_dec(v_unused_3529_);
v_unused_3530_ = lean_ctor_get(v_a_3503_, 0);
lean_dec(v_unused_3530_);
v___x_3520_ = v_a_3503_;
v_isShared_3521_ = v_isSharedCheck_3528_;
goto v_resetjp_3519_;
}
else
{
lean_dec(v_a_3503_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3528_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3522_; lean_object* v_it_x27_3524_; 
v___x_3522_ = lean_string_utf8_next_fast(v_fst_3504_, v_snd_3505_);
lean_dec(v_snd_3505_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 1, v___x_3522_);
v_it_x27_3524_ = v___x_3520_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_fst_3504_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3522_);
v_it_x27_3524_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3525_; 
v___x_3525_ = lean_string_push(v_acc_3502_, v___x_3515_);
v_acc_3502_ = v___x_3525_;
v_a_3503_ = v_it_x27_3524_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3531_; 
v___x_3531_ = lean_box(0);
lean_inc(v_snd_3505_);
v_pos_3507_ = v_a_3503_;
v_snd_3508_ = v_snd_3505_;
v_err_3509_ = v___x_3531_;
goto v___jp_3506_;
}
v___jp_3506_:
{
uint8_t v_decide_3510_; 
v_decide_3510_ = lean_nat_dec_eq(v_snd_3505_, v_snd_3508_);
lean_dec(v_snd_3508_);
lean_dec(v_snd_3505_);
if (v_decide_3510_ == 0)
{
lean_object* v___x_3511_; 
lean_dec_ref(v_acc_3502_);
lean_inc(v_err_3509_);
v___x_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3511_, 0, v_pos_3507_);
lean_ctor_set(v___x_3511_, 1, v_err_3509_);
return v___x_3511_;
}
else
{
lean_object* v___x_3512_; 
v___x_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3512_, 0, v_pos_3507_);
lean_ctor_set(v___x_3512_, 1, v_acc_3502_);
return v___x_3512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(lean_object* v_acc_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_fst_3537_; lean_object* v_snd_3538_; lean_object* v_pos_3540_; lean_object* v_snd_3541_; lean_object* v_err_3542_; lean_object* v___x_3546_; uint8_t v_decide_3547_; 
v_fst_3537_ = lean_ctor_get(v_a_3536_, 0);
v_snd_3538_ = lean_ctor_get(v_a_3536_, 1);
lean_inc(v_snd_3538_);
v___x_3546_ = lean_string_utf8_byte_size(v_fst_3537_);
v_decide_3547_ = lean_nat_dec_eq(v_snd_3538_, v___x_3546_);
if (v_decide_3547_ == 0)
{
uint32_t v___x_3548_; uint32_t v_c_3549_; uint8_t v___x_3550_; 
v___x_3548_ = 100;
v_c_3549_ = lean_string_utf8_get_fast(v_fst_3537_, v_snd_3538_);
v___x_3550_ = lean_uint32_dec_eq(v_c_3549_, v___x_3548_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; 
v___x_3551_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1));
lean_inc(v_snd_3538_);
v_pos_3540_ = v_a_3536_;
v_snd_3541_ = v_snd_3538_;
v_err_3542_ = v___x_3551_;
goto v___jp_3539_;
}
else
{
lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3561_; 
lean_inc(v_fst_3537_);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_a_3536_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; lean_object* v_unused_3563_; 
v_unused_3562_ = lean_ctor_get(v_a_3536_, 1);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_a_3536_, 0);
lean_dec(v_unused_3563_);
v___x_3553_ = v_a_3536_;
v_isShared_3554_ = v_isSharedCheck_3561_;
goto v_resetjp_3552_;
}
else
{
lean_dec(v_a_3536_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3561_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; lean_object* v_it_x27_3557_; 
v___x_3555_ = lean_string_utf8_next_fast(v_fst_3537_, v_snd_3538_);
lean_dec(v_snd_3538_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 1, v___x_3555_);
v_it_x27_3557_ = v___x_3553_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_fst_3537_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v___x_3555_);
v_it_x27_3557_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3558_; 
v___x_3558_ = lean_string_push(v_acc_3535_, v___x_3548_);
v_acc_3535_ = v___x_3558_;
v_a_3536_ = v_it_x27_3557_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3564_; 
v___x_3564_ = lean_box(0);
lean_inc(v_snd_3538_);
v_pos_3540_ = v_a_3536_;
v_snd_3541_ = v_snd_3538_;
v_err_3542_ = v___x_3564_;
goto v___jp_3539_;
}
v___jp_3539_:
{
uint8_t v_decide_3543_; 
v_decide_3543_ = lean_nat_dec_eq(v_snd_3538_, v_snd_3541_);
lean_dec(v_snd_3541_);
lean_dec(v_snd_3538_);
if (v_decide_3543_ == 0)
{
lean_object* v___x_3544_; 
lean_dec_ref(v_acc_3535_);
lean_inc(v_err_3542_);
v___x_3544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3544_, 0, v_pos_3540_);
lean_ctor_set(v___x_3544_, 1, v_err_3542_);
return v___x_3544_;
}
else
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3545_, 0, v_pos_3540_);
lean_ctor_set(v___x_3545_, 1, v_acc_3535_);
return v___x_3545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(lean_object* v_acc_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v_fst_3570_; lean_object* v_snd_3571_; lean_object* v_pos_3573_; lean_object* v_snd_3574_; lean_object* v_err_3575_; lean_object* v___x_3579_; uint8_t v_decide_3580_; 
v_fst_3570_ = lean_ctor_get(v_a_3569_, 0);
v_snd_3571_ = lean_ctor_get(v_a_3569_, 1);
lean_inc(v_snd_3571_);
v___x_3579_ = lean_string_utf8_byte_size(v_fst_3570_);
v_decide_3580_ = lean_nat_dec_eq(v_snd_3571_, v___x_3579_);
if (v_decide_3580_ == 0)
{
uint32_t v___x_3581_; uint32_t v_c_3582_; uint8_t v___x_3583_; 
v___x_3581_ = 99;
v_c_3582_ = lean_string_utf8_get_fast(v_fst_3570_, v_snd_3571_);
v___x_3583_ = lean_uint32_dec_eq(v_c_3582_, v___x_3581_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3584_; 
v___x_3584_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1));
lean_inc(v_snd_3571_);
v_pos_3573_ = v_a_3569_;
v_snd_3574_ = v_snd_3571_;
v_err_3575_ = v___x_3584_;
goto v___jp_3572_;
}
else
{
lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3594_; 
lean_inc(v_fst_3570_);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_a_3569_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; lean_object* v_unused_3596_; 
v_unused_3595_ = lean_ctor_get(v_a_3569_, 1);
lean_dec(v_unused_3595_);
v_unused_3596_ = lean_ctor_get(v_a_3569_, 0);
lean_dec(v_unused_3596_);
v___x_3586_ = v_a_3569_;
v_isShared_3587_ = v_isSharedCheck_3594_;
goto v_resetjp_3585_;
}
else
{
lean_dec(v_a_3569_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3594_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v_it_x27_3590_; 
v___x_3588_ = lean_string_utf8_next_fast(v_fst_3570_, v_snd_3571_);
lean_dec(v_snd_3571_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v___x_3588_);
v_it_x27_3590_ = v___x_3586_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_fst_3570_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v___x_3588_);
v_it_x27_3590_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; 
v___x_3591_ = lean_string_push(v_acc_3568_, v___x_3581_);
v_acc_3568_ = v___x_3591_;
v_a_3569_ = v_it_x27_3590_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3597_; 
v___x_3597_ = lean_box(0);
lean_inc(v_snd_3571_);
v_pos_3573_ = v_a_3569_;
v_snd_3574_ = v_snd_3571_;
v_err_3575_ = v___x_3597_;
goto v___jp_3572_;
}
v___jp_3572_:
{
uint8_t v_decide_3576_; 
v_decide_3576_ = lean_nat_dec_eq(v_snd_3571_, v_snd_3574_);
lean_dec(v_snd_3574_);
lean_dec(v_snd_3571_);
if (v_decide_3576_ == 0)
{
lean_object* v___x_3577_; 
lean_dec_ref(v_acc_3568_);
lean_inc(v_err_3575_);
v___x_3577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3577_, 0, v_pos_3573_);
lean_ctor_set(v___x_3577_, 1, v_err_3575_);
return v___x_3577_;
}
else
{
lean_object* v___x_3578_; 
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v_pos_3573_);
lean_ctor_set(v___x_3578_, 1, v_acc_3568_);
return v___x_3578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(lean_object* v_acc_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v_fst_3603_; lean_object* v_snd_3604_; lean_object* v_pos_3606_; lean_object* v_snd_3607_; lean_object* v_err_3608_; lean_object* v___x_3612_; uint8_t v_decide_3613_; 
v_fst_3603_ = lean_ctor_get(v_a_3602_, 0);
v_snd_3604_ = lean_ctor_get(v_a_3602_, 1);
lean_inc(v_snd_3604_);
v___x_3612_ = lean_string_utf8_byte_size(v_fst_3603_);
v_decide_3613_ = lean_nat_dec_eq(v_snd_3604_, v___x_3612_);
if (v_decide_3613_ == 0)
{
uint32_t v___x_3614_; uint32_t v_c_3615_; uint8_t v___x_3616_; 
v___x_3614_ = 69;
v_c_3615_ = lean_string_utf8_get_fast(v_fst_3603_, v_snd_3604_);
v___x_3616_ = lean_uint32_dec_eq(v_c_3615_, v___x_3614_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; 
v___x_3617_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1));
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
uint8_t v_decide_3609_; 
v_decide_3609_ = lean_nat_dec_eq(v_snd_3604_, v_snd_3607_);
lean_dec(v_snd_3607_);
lean_dec(v_snd_3604_);
if (v_decide_3609_ == 0)
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(lean_object* v_acc_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v_fst_3636_; lean_object* v_snd_3637_; lean_object* v_pos_3639_; lean_object* v_snd_3640_; lean_object* v_err_3641_; lean_object* v___x_3645_; uint8_t v_decide_3646_; 
v_fst_3636_ = lean_ctor_get(v_a_3635_, 0);
v_snd_3637_ = lean_ctor_get(v_a_3635_, 1);
lean_inc(v_snd_3637_);
v___x_3645_ = lean_string_utf8_byte_size(v_fst_3636_);
v_decide_3646_ = lean_nat_dec_eq(v_snd_3637_, v___x_3645_);
if (v_decide_3646_ == 0)
{
uint32_t v___x_3647_; uint32_t v_c_3648_; uint8_t v___x_3649_; 
v___x_3647_ = 97;
v_c_3648_ = lean_string_utf8_get_fast(v_fst_3636_, v_snd_3637_);
v___x_3649_ = lean_uint32_dec_eq(v_c_3648_, v___x_3647_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; 
v___x_3650_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1));
lean_inc(v_snd_3637_);
v_pos_3639_ = v_a_3635_;
v_snd_3640_ = v_snd_3637_;
v_err_3641_ = v___x_3650_;
goto v___jp_3638_;
}
else
{
lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3660_; 
lean_inc(v_fst_3636_);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_a_3635_);
if (v_isSharedCheck_3660_ == 0)
{
lean_object* v_unused_3661_; lean_object* v_unused_3662_; 
v_unused_3661_ = lean_ctor_get(v_a_3635_, 1);
lean_dec(v_unused_3661_);
v_unused_3662_ = lean_ctor_get(v_a_3635_, 0);
lean_dec(v_unused_3662_);
v___x_3652_ = v_a_3635_;
v_isShared_3653_ = v_isSharedCheck_3660_;
goto v_resetjp_3651_;
}
else
{
lean_dec(v_a_3635_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3660_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v_it_x27_3656_; 
v___x_3654_ = lean_string_utf8_next_fast(v_fst_3636_, v_snd_3637_);
lean_dec(v_snd_3637_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 1, v___x_3654_);
v_it_x27_3656_ = v___x_3652_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_fst_3636_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v___x_3654_);
v_it_x27_3656_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3657_; 
v___x_3657_ = lean_string_push(v_acc_3634_, v___x_3647_);
v_acc_3634_ = v___x_3657_;
v_a_3635_ = v_it_x27_3656_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_box(0);
lean_inc(v_snd_3637_);
v_pos_3639_ = v_a_3635_;
v_snd_3640_ = v_snd_3637_;
v_err_3641_ = v___x_3663_;
goto v___jp_3638_;
}
v___jp_3638_:
{
uint8_t v_decide_3642_; 
v_decide_3642_ = lean_nat_dec_eq(v_snd_3637_, v_snd_3640_);
lean_dec(v_snd_3640_);
lean_dec(v_snd_3637_);
if (v_decide_3642_ == 0)
{
lean_object* v___x_3643_; 
lean_dec_ref(v_acc_3634_);
lean_inc(v_err_3641_);
v___x_3643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3643_, 0, v_pos_3639_);
lean_ctor_set(v___x_3643_, 1, v_err_3641_);
return v___x_3643_;
}
else
{
lean_object* v___x_3644_; 
v___x_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3644_, 0, v_pos_3639_);
lean_ctor_set(v___x_3644_, 1, v_acc_3634_);
return v___x_3644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(lean_object* v_acc_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_fst_3669_; lean_object* v_snd_3670_; lean_object* v_pos_3672_; lean_object* v_snd_3673_; lean_object* v_err_3674_; lean_object* v___x_3678_; uint8_t v_decide_3679_; 
v_fst_3669_ = lean_ctor_get(v_a_3668_, 0);
v_snd_3670_ = lean_ctor_get(v_a_3668_, 1);
lean_inc(v_snd_3670_);
v___x_3678_ = lean_string_utf8_byte_size(v_fst_3669_);
v_decide_3679_ = lean_nat_dec_eq(v_snd_3670_, v___x_3678_);
if (v_decide_3679_ == 0)
{
uint32_t v___x_3680_; uint32_t v_c_3681_; uint8_t v___x_3682_; 
v___x_3680_ = 79;
v_c_3681_ = lean_string_utf8_get_fast(v_fst_3669_, v_snd_3670_);
v___x_3682_ = lean_uint32_dec_eq(v_c_3681_, v___x_3680_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; 
v___x_3683_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1));
lean_inc(v_snd_3670_);
v_pos_3672_ = v_a_3668_;
v_snd_3673_ = v_snd_3670_;
v_err_3674_ = v___x_3683_;
goto v___jp_3671_;
}
else
{
lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3693_; 
lean_inc(v_fst_3669_);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_a_3668_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; lean_object* v_unused_3695_; 
v_unused_3694_ = lean_ctor_get(v_a_3668_, 1);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_a_3668_, 0);
lean_dec(v_unused_3695_);
v___x_3685_ = v_a_3668_;
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
else
{
lean_dec(v_a_3668_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3687_; lean_object* v_it_x27_3689_; 
v___x_3687_ = lean_string_utf8_next_fast(v_fst_3669_, v_snd_3670_);
lean_dec(v_snd_3670_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 1, v___x_3687_);
v_it_x27_3689_ = v___x_3685_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_fst_3669_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v___x_3687_);
v_it_x27_3689_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_string_push(v_acc_3667_, v___x_3680_);
v_acc_3667_ = v___x_3690_;
v_a_3668_ = v_it_x27_3689_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3696_; 
v___x_3696_ = lean_box(0);
lean_inc(v_snd_3670_);
v_pos_3672_ = v_a_3668_;
v_snd_3673_ = v_snd_3670_;
v_err_3674_ = v___x_3696_;
goto v___jp_3671_;
}
v___jp_3671_:
{
uint8_t v_decide_3675_; 
v_decide_3675_ = lean_nat_dec_eq(v_snd_3670_, v_snd_3673_);
lean_dec(v_snd_3673_);
lean_dec(v_snd_3670_);
if (v_decide_3675_ == 0)
{
lean_object* v___x_3676_; 
lean_dec_ref(v_acc_3667_);
lean_inc(v_err_3674_);
v___x_3676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3676_, 0, v_pos_3672_);
lean_ctor_set(v___x_3676_, 1, v_err_3674_);
return v___x_3676_;
}
else
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3677_, 0, v_pos_3672_);
lean_ctor_set(v___x_3677_, 1, v_acc_3667_);
return v___x_3677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(lean_object* v_acc_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_fst_3702_; lean_object* v_snd_3703_; lean_object* v_pos_3705_; lean_object* v_snd_3706_; lean_object* v_err_3707_; lean_object* v___x_3711_; uint8_t v_decide_3712_; 
v_fst_3702_ = lean_ctor_get(v_a_3701_, 0);
v_snd_3703_ = lean_ctor_get(v_a_3701_, 1);
lean_inc(v_snd_3703_);
v___x_3711_ = lean_string_utf8_byte_size(v_fst_3702_);
v_decide_3712_ = lean_nat_dec_eq(v_snd_3703_, v___x_3711_);
if (v_decide_3712_ == 0)
{
uint32_t v___x_3713_; uint32_t v_c_3714_; uint8_t v___x_3715_; 
v___x_3713_ = 65;
v_c_3714_ = lean_string_utf8_get_fast(v_fst_3702_, v_snd_3703_);
v___x_3715_ = lean_uint32_dec_eq(v_c_3714_, v___x_3713_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; 
v___x_3716_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1));
lean_inc(v_snd_3703_);
v_pos_3705_ = v_a_3701_;
v_snd_3706_ = v_snd_3703_;
v_err_3707_ = v___x_3716_;
goto v___jp_3704_;
}
else
{
lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3726_; 
lean_inc(v_fst_3702_);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_a_3701_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; lean_object* v_unused_3728_; 
v_unused_3727_ = lean_ctor_get(v_a_3701_, 1);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_a_3701_, 0);
lean_dec(v_unused_3728_);
v___x_3718_ = v_a_3701_;
v_isShared_3719_ = v_isSharedCheck_3726_;
goto v_resetjp_3717_;
}
else
{
lean_dec(v_a_3701_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3726_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3720_; lean_object* v_it_x27_3722_; 
v___x_3720_ = lean_string_utf8_next_fast(v_fst_3702_, v_snd_3703_);
lean_dec(v_snd_3703_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 1, v___x_3720_);
v_it_x27_3722_ = v___x_3718_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_fst_3702_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___x_3720_);
v_it_x27_3722_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_string_push(v_acc_3700_, v___x_3713_);
v_acc_3700_ = v___x_3723_;
v_a_3701_ = v_it_x27_3722_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3729_; 
v___x_3729_ = lean_box(0);
lean_inc(v_snd_3703_);
v_pos_3705_ = v_a_3701_;
v_snd_3706_ = v_snd_3703_;
v_err_3707_ = v___x_3729_;
goto v___jp_3704_;
}
v___jp_3704_:
{
uint8_t v_decide_3708_; 
v_decide_3708_ = lean_nat_dec_eq(v_snd_3703_, v_snd_3706_);
lean_dec(v_snd_3706_);
lean_dec(v_snd_3703_);
if (v_decide_3708_ == 0)
{
lean_object* v___x_3709_; 
lean_dec_ref(v_acc_3700_);
lean_inc(v_err_3707_);
v___x_3709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3709_, 0, v_pos_3705_);
lean_ctor_set(v___x_3709_, 1, v_err_3707_);
return v___x_3709_;
}
else
{
lean_object* v___x_3710_; 
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v_pos_3705_);
lean_ctor_set(v___x_3710_, 1, v_acc_3700_);
return v___x_3710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(lean_object* v_acc_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v_fst_3735_; lean_object* v_snd_3736_; lean_object* v_pos_3738_; lean_object* v_snd_3739_; lean_object* v_err_3740_; lean_object* v___x_3744_; uint8_t v_decide_3745_; 
v_fst_3735_ = lean_ctor_get(v_a_3734_, 0);
v_snd_3736_ = lean_ctor_get(v_a_3734_, 1);
lean_inc(v_snd_3736_);
v___x_3744_ = lean_string_utf8_byte_size(v_fst_3735_);
v_decide_3745_ = lean_nat_dec_eq(v_snd_3736_, v___x_3744_);
if (v_decide_3745_ == 0)
{
uint32_t v___x_3746_; uint32_t v_c_3747_; uint8_t v___x_3748_; 
v___x_3746_ = 76;
v_c_3747_ = lean_string_utf8_get_fast(v_fst_3735_, v_snd_3736_);
v___x_3748_ = lean_uint32_dec_eq(v_c_3747_, v___x_3746_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; 
v___x_3749_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1));
lean_inc(v_snd_3736_);
v_pos_3738_ = v_a_3734_;
v_snd_3739_ = v_snd_3736_;
v_err_3740_ = v___x_3749_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3759_; 
lean_inc(v_fst_3735_);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_a_3734_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3760_ = lean_ctor_get(v_a_3734_, 1);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_a_3734_, 0);
lean_dec(v_unused_3761_);
v___x_3751_ = v_a_3734_;
v_isShared_3752_ = v_isSharedCheck_3759_;
goto v_resetjp_3750_;
}
else
{
lean_dec(v_a_3734_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3759_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3753_; lean_object* v_it_x27_3755_; 
v___x_3753_ = lean_string_utf8_next_fast(v_fst_3735_, v_snd_3736_);
lean_dec(v_snd_3736_);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 1, v___x_3753_);
v_it_x27_3755_ = v___x_3751_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_fst_3735_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v___x_3753_);
v_it_x27_3755_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_string_push(v_acc_3733_, v___x_3746_);
v_acc_3733_ = v___x_3756_;
v_a_3734_ = v_it_x27_3755_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_box(0);
lean_inc(v_snd_3736_);
v_pos_3738_ = v_a_3734_;
v_snd_3739_ = v_snd_3736_;
v_err_3740_ = v___x_3762_;
goto v___jp_3737_;
}
v___jp_3737_:
{
uint8_t v_decide_3741_; 
v_decide_3741_ = lean_nat_dec_eq(v_snd_3736_, v_snd_3739_);
lean_dec(v_snd_3739_);
lean_dec(v_snd_3736_);
if (v_decide_3741_ == 0)
{
lean_object* v___x_3742_; 
lean_dec_ref(v_acc_3733_);
lean_inc(v_err_3740_);
v___x_3742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3742_, 0, v_pos_3738_);
lean_ctor_set(v___x_3742_, 1, v_err_3740_);
return v___x_3742_;
}
else
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3743_, 0, v_pos_3738_);
lean_ctor_set(v___x_3743_, 1, v_acc_3733_);
return v___x_3743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(lean_object* v_acc_3766_, lean_object* v_a_3767_){
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
v___x_3779_ = 113;
v_c_3780_ = lean_string_utf8_get_fast(v_fst_3768_, v_snd_3769_);
v___x_3781_ = lean_uint32_dec_eq(v_c_3780_, v___x_3779_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; 
v___x_3782_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1));
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(lean_object* v_acc_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_fst_3801_; lean_object* v_snd_3802_; lean_object* v_pos_3804_; lean_object* v_snd_3805_; lean_object* v_err_3806_; lean_object* v___x_3810_; uint8_t v_decide_3811_; 
v_fst_3801_ = lean_ctor_get(v_a_3800_, 0);
v_snd_3802_ = lean_ctor_get(v_a_3800_, 1);
lean_inc(v_snd_3802_);
v___x_3810_ = lean_string_utf8_byte_size(v_fst_3801_);
v_decide_3811_ = lean_nat_dec_eq(v_snd_3802_, v___x_3810_);
if (v_decide_3811_ == 0)
{
uint32_t v___x_3812_; uint32_t v_c_3813_; uint8_t v___x_3814_; 
v___x_3812_ = 72;
v_c_3813_ = lean_string_utf8_get_fast(v_fst_3801_, v_snd_3802_);
v___x_3814_ = lean_uint32_dec_eq(v_c_3813_, v___x_3812_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
v___x_3815_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1));
lean_inc(v_snd_3802_);
v_pos_3804_ = v_a_3800_;
v_snd_3805_ = v_snd_3802_;
v_err_3806_ = v___x_3815_;
goto v___jp_3803_;
}
else
{
lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3825_; 
lean_inc(v_fst_3801_);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_a_3800_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; lean_object* v_unused_3827_; 
v_unused_3826_ = lean_ctor_get(v_a_3800_, 1);
lean_dec(v_unused_3826_);
v_unused_3827_ = lean_ctor_get(v_a_3800_, 0);
lean_dec(v_unused_3827_);
v___x_3817_ = v_a_3800_;
v_isShared_3818_ = v_isSharedCheck_3825_;
goto v_resetjp_3816_;
}
else
{
lean_dec(v_a_3800_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3825_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3819_; lean_object* v_it_x27_3821_; 
v___x_3819_ = lean_string_utf8_next_fast(v_fst_3801_, v_snd_3802_);
lean_dec(v_snd_3802_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 1, v___x_3819_);
v_it_x27_3821_ = v___x_3817_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_fst_3801_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v___x_3819_);
v_it_x27_3821_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3822_; 
v___x_3822_ = lean_string_push(v_acc_3799_, v___x_3812_);
v_acc_3799_ = v___x_3822_;
v_a_3800_ = v_it_x27_3821_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_box(0);
lean_inc(v_snd_3802_);
v_pos_3804_ = v_a_3800_;
v_snd_3805_ = v_snd_3802_;
v_err_3806_ = v___x_3828_;
goto v___jp_3803_;
}
v___jp_3803_:
{
uint8_t v_decide_3807_; 
v_decide_3807_ = lean_nat_dec_eq(v_snd_3802_, v_snd_3805_);
lean_dec(v_snd_3805_);
lean_dec(v_snd_3802_);
if (v_decide_3807_ == 0)
{
lean_object* v___x_3808_; 
lean_dec_ref(v_acc_3799_);
lean_inc(v_err_3806_);
v___x_3808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3808_, 0, v_pos_3804_);
lean_ctor_set(v___x_3808_, 1, v_err_3806_);
return v___x_3808_;
}
else
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3809_, 0, v_pos_3804_);
lean_ctor_set(v___x_3809_, 1, v_acc_3799_);
return v___x_3809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(lean_object* v_acc_3832_, lean_object* v_a_3833_){
_start:
{
lean_object* v_fst_3834_; lean_object* v_snd_3835_; lean_object* v_pos_3837_; lean_object* v_snd_3838_; lean_object* v_err_3839_; lean_object* v___x_3843_; uint8_t v_decide_3844_; 
v_fst_3834_ = lean_ctor_get(v_a_3833_, 0);
v_snd_3835_ = lean_ctor_get(v_a_3833_, 1);
lean_inc(v_snd_3835_);
v___x_3843_ = lean_string_utf8_byte_size(v_fst_3834_);
v_decide_3844_ = lean_nat_dec_eq(v_snd_3835_, v___x_3843_);
if (v_decide_3844_ == 0)
{
uint32_t v___x_3845_; uint32_t v_c_3846_; uint8_t v___x_3847_; 
v___x_3845_ = 118;
v_c_3846_ = lean_string_utf8_get_fast(v_fst_3834_, v_snd_3835_);
v___x_3847_ = lean_uint32_dec_eq(v_c_3846_, v___x_3845_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; 
v___x_3848_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1));
lean_inc(v_snd_3835_);
v_pos_3837_ = v_a_3833_;
v_snd_3838_ = v_snd_3835_;
v_err_3839_ = v___x_3848_;
goto v___jp_3836_;
}
else
{
lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3858_; 
lean_inc(v_fst_3834_);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_a_3833_);
if (v_isSharedCheck_3858_ == 0)
{
lean_object* v_unused_3859_; lean_object* v_unused_3860_; 
v_unused_3859_ = lean_ctor_get(v_a_3833_, 1);
lean_dec(v_unused_3859_);
v_unused_3860_ = lean_ctor_get(v_a_3833_, 0);
lean_dec(v_unused_3860_);
v___x_3850_ = v_a_3833_;
v_isShared_3851_ = v_isSharedCheck_3858_;
goto v_resetjp_3849_;
}
else
{
lean_dec(v_a_3833_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3858_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3852_; lean_object* v_it_x27_3854_; 
v___x_3852_ = lean_string_utf8_next_fast(v_fst_3834_, v_snd_3835_);
lean_dec(v_snd_3835_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v___x_3852_);
v_it_x27_3854_ = v___x_3850_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_fst_3834_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v___x_3852_);
v_it_x27_3854_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; 
v___x_3855_ = lean_string_push(v_acc_3832_, v___x_3845_);
v_acc_3832_ = v___x_3855_;
v_a_3833_ = v_it_x27_3854_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_box(0);
lean_inc(v_snd_3835_);
v_pos_3837_ = v_a_3833_;
v_snd_3838_ = v_snd_3835_;
v_err_3839_ = v___x_3861_;
goto v___jp_3836_;
}
v___jp_3836_:
{
uint8_t v_decide_3840_; 
v_decide_3840_ = lean_nat_dec_eq(v_snd_3835_, v_snd_3838_);
lean_dec(v_snd_3838_);
lean_dec(v_snd_3835_);
if (v_decide_3840_ == 0)
{
lean_object* v___x_3841_; 
lean_dec_ref(v_acc_3832_);
lean_inc(v_err_3839_);
v___x_3841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3841_, 0, v_pos_3837_);
lean_ctor_set(v___x_3841_, 1, v_err_3839_);
return v___x_3841_;
}
else
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v_pos_3837_);
lean_ctor_set(v___x_3842_, 1, v_acc_3832_);
return v___x_3842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(lean_object* v_acc_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_fst_3867_; lean_object* v_snd_3868_; lean_object* v_pos_3870_; lean_object* v_snd_3871_; lean_object* v_err_3872_; lean_object* v___x_3876_; uint8_t v_decide_3877_; 
v_fst_3867_ = lean_ctor_get(v_a_3866_, 0);
v_snd_3868_ = lean_ctor_get(v_a_3866_, 1);
lean_inc(v_snd_3868_);
v___x_3876_ = lean_string_utf8_byte_size(v_fst_3867_);
v_decide_3877_ = lean_nat_dec_eq(v_snd_3868_, v___x_3876_);
if (v_decide_3877_ == 0)
{
uint32_t v___x_3878_; uint32_t v_c_3879_; uint8_t v___x_3880_; 
v___x_3878_ = 87;
v_c_3879_ = lean_string_utf8_get_fast(v_fst_3867_, v_snd_3868_);
v___x_3880_ = lean_uint32_dec_eq(v_c_3879_, v___x_3878_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; 
v___x_3881_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1));
lean_inc(v_snd_3868_);
v_pos_3870_ = v_a_3866_;
v_snd_3871_ = v_snd_3868_;
v_err_3872_ = v___x_3881_;
goto v___jp_3869_;
}
else
{
lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3891_; 
lean_inc(v_fst_3867_);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_a_3866_);
if (v_isSharedCheck_3891_ == 0)
{
lean_object* v_unused_3892_; lean_object* v_unused_3893_; 
v_unused_3892_ = lean_ctor_get(v_a_3866_, 1);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_a_3866_, 0);
lean_dec(v_unused_3893_);
v___x_3883_ = v_a_3866_;
v_isShared_3884_ = v_isSharedCheck_3891_;
goto v_resetjp_3882_;
}
else
{
lean_dec(v_a_3866_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3891_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; lean_object* v_it_x27_3887_; 
v___x_3885_ = lean_string_utf8_next_fast(v_fst_3867_, v_snd_3868_);
lean_dec(v_snd_3868_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 1, v___x_3885_);
v_it_x27_3887_ = v___x_3883_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_fst_3867_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v___x_3885_);
v_it_x27_3887_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3888_; 
v___x_3888_ = lean_string_push(v_acc_3865_, v___x_3878_);
v_acc_3865_ = v___x_3888_;
v_a_3866_ = v_it_x27_3887_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3894_; 
v___x_3894_ = lean_box(0);
lean_inc(v_snd_3868_);
v_pos_3870_ = v_a_3866_;
v_snd_3871_ = v_snd_3868_;
v_err_3872_ = v___x_3894_;
goto v___jp_3869_;
}
v___jp_3869_:
{
uint8_t v_decide_3873_; 
v_decide_3873_ = lean_nat_dec_eq(v_snd_3868_, v_snd_3871_);
lean_dec(v_snd_3871_);
lean_dec(v_snd_3868_);
if (v_decide_3873_ == 0)
{
lean_object* v___x_3874_; 
lean_dec_ref(v_acc_3865_);
lean_inc(v_err_3872_);
v___x_3874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3874_, 0, v_pos_3870_);
lean_ctor_set(v___x_3874_, 1, v_err_3872_);
return v___x_3874_;
}
else
{
lean_object* v___x_3875_; 
v___x_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3875_, 0, v_pos_3870_);
lean_ctor_set(v___x_3875_, 1, v_acc_3865_);
return v___x_3875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(lean_object* v_acc_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v_fst_3900_; lean_object* v_snd_3901_; lean_object* v_pos_3903_; lean_object* v_snd_3904_; lean_object* v_err_3905_; lean_object* v___x_3909_; uint8_t v_decide_3910_; 
v_fst_3900_ = lean_ctor_get(v_a_3899_, 0);
v_snd_3901_ = lean_ctor_get(v_a_3899_, 1);
lean_inc(v_snd_3901_);
v___x_3909_ = lean_string_utf8_byte_size(v_fst_3900_);
v_decide_3910_ = lean_nat_dec_eq(v_snd_3901_, v___x_3909_);
if (v_decide_3910_ == 0)
{
uint32_t v___x_3911_; uint32_t v_c_3912_; uint8_t v___x_3913_; 
v___x_3911_ = 107;
v_c_3912_ = lean_string_utf8_get_fast(v_fst_3900_, v_snd_3901_);
v___x_3913_ = lean_uint32_dec_eq(v_c_3912_, v___x_3911_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; 
v___x_3914_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1));
lean_inc(v_snd_3901_);
v_pos_3903_ = v_a_3899_;
v_snd_3904_ = v_snd_3901_;
v_err_3905_ = v___x_3914_;
goto v___jp_3902_;
}
else
{
lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3924_; 
lean_inc(v_fst_3900_);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_a_3899_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; lean_object* v_unused_3926_; 
v_unused_3925_ = lean_ctor_get(v_a_3899_, 1);
lean_dec(v_unused_3925_);
v_unused_3926_ = lean_ctor_get(v_a_3899_, 0);
lean_dec(v_unused_3926_);
v___x_3916_ = v_a_3899_;
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
else
{
lean_dec(v_a_3899_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3918_; lean_object* v_it_x27_3920_; 
v___x_3918_ = lean_string_utf8_next_fast(v_fst_3900_, v_snd_3901_);
lean_dec(v_snd_3901_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 1, v___x_3918_);
v_it_x27_3920_ = v___x_3916_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_fst_3900_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v___x_3918_);
v_it_x27_3920_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3921_; 
v___x_3921_ = lean_string_push(v_acc_3898_, v___x_3911_);
v_acc_3898_ = v___x_3921_;
v_a_3899_ = v_it_x27_3920_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3927_; 
v___x_3927_ = lean_box(0);
lean_inc(v_snd_3901_);
v_pos_3903_ = v_a_3899_;
v_snd_3904_ = v_snd_3901_;
v_err_3905_ = v___x_3927_;
goto v___jp_3902_;
}
v___jp_3902_:
{
uint8_t v_decide_3906_; 
v_decide_3906_ = lean_nat_dec_eq(v_snd_3901_, v_snd_3904_);
lean_dec(v_snd_3904_);
lean_dec(v_snd_3901_);
if (v_decide_3906_ == 0)
{
lean_object* v___x_3907_; 
lean_dec_ref(v_acc_3898_);
lean_inc(v_err_3905_);
v___x_3907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3907_, 0, v_pos_3903_);
lean_ctor_set(v___x_3907_, 1, v_err_3905_);
return v___x_3907_;
}
else
{
lean_object* v___x_3908_; 
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v_pos_3903_);
lean_ctor_set(v___x_3908_, 1, v_acc_3898_);
return v___x_3908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(lean_object* v_acc_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v_fst_3933_; lean_object* v_snd_3934_; lean_object* v_pos_3936_; lean_object* v_snd_3937_; lean_object* v_err_3938_; lean_object* v___x_3942_; uint8_t v_decide_3943_; 
v_fst_3933_ = lean_ctor_get(v_a_3932_, 0);
v_snd_3934_ = lean_ctor_get(v_a_3932_, 1);
lean_inc(v_snd_3934_);
v___x_3942_ = lean_string_utf8_byte_size(v_fst_3933_);
v_decide_3943_ = lean_nat_dec_eq(v_snd_3934_, v___x_3942_);
if (v_decide_3943_ == 0)
{
uint32_t v___x_3944_; uint32_t v_c_3945_; uint8_t v___x_3946_; 
v___x_3944_ = 121;
v_c_3945_ = lean_string_utf8_get_fast(v_fst_3933_, v_snd_3934_);
v___x_3946_ = lean_uint32_dec_eq(v_c_3945_, v___x_3944_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
v___x_3947_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1));
lean_inc(v_snd_3934_);
v_pos_3936_ = v_a_3932_;
v_snd_3937_ = v_snd_3934_;
v_err_3938_ = v___x_3947_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3957_; 
lean_inc(v_fst_3933_);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_a_3932_);
if (v_isSharedCheck_3957_ == 0)
{
lean_object* v_unused_3958_; lean_object* v_unused_3959_; 
v_unused_3958_ = lean_ctor_get(v_a_3932_, 1);
lean_dec(v_unused_3958_);
v_unused_3959_ = lean_ctor_get(v_a_3932_, 0);
lean_dec(v_unused_3959_);
v___x_3949_ = v_a_3932_;
v_isShared_3950_ = v_isSharedCheck_3957_;
goto v_resetjp_3948_;
}
else
{
lean_dec(v_a_3932_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3957_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3951_; lean_object* v_it_x27_3953_; 
v___x_3951_ = lean_string_utf8_next_fast(v_fst_3933_, v_snd_3934_);
lean_dec(v_snd_3934_);
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 1, v___x_3951_);
v_it_x27_3953_ = v___x_3949_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_fst_3933_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v___x_3951_);
v_it_x27_3953_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3954_; 
v___x_3954_ = lean_string_push(v_acc_3931_, v___x_3944_);
v_acc_3931_ = v___x_3954_;
v_a_3932_ = v_it_x27_3953_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3960_; 
v___x_3960_ = lean_box(0);
lean_inc(v_snd_3934_);
v_pos_3936_ = v_a_3932_;
v_snd_3937_ = v_snd_3934_;
v_err_3938_ = v___x_3960_;
goto v___jp_3935_;
}
v___jp_3935_:
{
uint8_t v_decide_3939_; 
v_decide_3939_ = lean_nat_dec_eq(v_snd_3934_, v_snd_3937_);
lean_dec(v_snd_3937_);
lean_dec(v_snd_3934_);
if (v_decide_3939_ == 0)
{
lean_object* v___x_3940_; 
lean_dec_ref(v_acc_3931_);
lean_inc(v_err_3938_);
v___x_3940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3940_, 0, v_pos_3936_);
lean_ctor_set(v___x_3940_, 1, v_err_3938_);
return v___x_3940_;
}
else
{
lean_object* v___x_3941_; 
v___x_3941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3941_, 0, v_pos_3936_);
lean_ctor_set(v___x_3941_, 1, v_acc_3931_);
return v___x_3941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(lean_object* v_acc_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v_fst_3966_; lean_object* v_snd_3967_; lean_object* v_pos_3969_; lean_object* v_snd_3970_; lean_object* v_err_3971_; lean_object* v___x_3975_; uint8_t v_decide_3976_; 
v_fst_3966_ = lean_ctor_get(v_a_3965_, 0);
v_snd_3967_ = lean_ctor_get(v_a_3965_, 1);
lean_inc(v_snd_3967_);
v___x_3975_ = lean_string_utf8_byte_size(v_fst_3966_);
v_decide_3976_ = lean_nat_dec_eq(v_snd_3967_, v___x_3975_);
if (v_decide_3976_ == 0)
{
uint32_t v___x_3977_; uint32_t v_c_3978_; uint8_t v___x_3979_; 
v___x_3977_ = 98;
v_c_3978_ = lean_string_utf8_get_fast(v_fst_3966_, v_snd_3967_);
v___x_3979_ = lean_uint32_dec_eq(v_c_3978_, v___x_3977_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; 
v___x_3980_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1));
lean_inc(v_snd_3967_);
v_pos_3969_ = v_a_3965_;
v_snd_3970_ = v_snd_3967_;
v_err_3971_ = v___x_3980_;
goto v___jp_3968_;
}
else
{
lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3990_; 
lean_inc(v_fst_3966_);
v_isSharedCheck_3990_ = !lean_is_exclusive(v_a_3965_);
if (v_isSharedCheck_3990_ == 0)
{
lean_object* v_unused_3991_; lean_object* v_unused_3992_; 
v_unused_3991_ = lean_ctor_get(v_a_3965_, 1);
lean_dec(v_unused_3991_);
v_unused_3992_ = lean_ctor_get(v_a_3965_, 0);
lean_dec(v_unused_3992_);
v___x_3982_ = v_a_3965_;
v_isShared_3983_ = v_isSharedCheck_3990_;
goto v_resetjp_3981_;
}
else
{
lean_dec(v_a_3965_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3990_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; lean_object* v_it_x27_3986_; 
v___x_3984_ = lean_string_utf8_next_fast(v_fst_3966_, v_snd_3967_);
lean_dec(v_snd_3967_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 1, v___x_3984_);
v_it_x27_3986_ = v___x_3982_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_fst_3966_);
lean_ctor_set(v_reuseFailAlloc_3989_, 1, v___x_3984_);
v_it_x27_3986_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3987_; 
v___x_3987_ = lean_string_push(v_acc_3964_, v___x_3977_);
v_acc_3964_ = v___x_3987_;
v_a_3965_ = v_it_x27_3986_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_box(0);
lean_inc(v_snd_3967_);
v_pos_3969_ = v_a_3965_;
v_snd_3970_ = v_snd_3967_;
v_err_3971_ = v___x_3993_;
goto v___jp_3968_;
}
v___jp_3968_:
{
uint8_t v_decide_3972_; 
v_decide_3972_ = lean_nat_dec_eq(v_snd_3967_, v_snd_3970_);
lean_dec(v_snd_3970_);
lean_dec(v_snd_3967_);
if (v_decide_3972_ == 0)
{
lean_object* v___x_3973_; 
lean_dec_ref(v_acc_3964_);
lean_inc(v_err_3971_);
v___x_3973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3973_, 0, v_pos_3969_);
lean_ctor_set(v___x_3973_, 1, v_err_3971_);
return v___x_3973_;
}
else
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3974_, 0, v_pos_3969_);
lean_ctor_set(v___x_3974_, 1, v_acc_3964_);
return v___x_3974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(lean_object* v_acc_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v_fst_3999_; lean_object* v_snd_4000_; lean_object* v_pos_4002_; lean_object* v_snd_4003_; lean_object* v_err_4004_; lean_object* v___x_4008_; uint8_t v_decide_4009_; 
v_fst_3999_ = lean_ctor_get(v_a_3998_, 0);
v_snd_4000_ = lean_ctor_get(v_a_3998_, 1);
lean_inc(v_snd_4000_);
v___x_4008_ = lean_string_utf8_byte_size(v_fst_3999_);
v_decide_4009_ = lean_nat_dec_eq(v_snd_4000_, v___x_4008_);
if (v_decide_4009_ == 0)
{
uint32_t v___x_4010_; uint32_t v_c_4011_; uint8_t v___x_4012_; 
v___x_4010_ = 109;
v_c_4011_ = lean_string_utf8_get_fast(v_fst_3999_, v_snd_4000_);
v___x_4012_ = lean_uint32_dec_eq(v_c_4011_, v___x_4010_);
if (v___x_4012_ == 0)
{
lean_object* v___x_4013_; 
v___x_4013_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1));
lean_inc(v_snd_4000_);
v_pos_4002_ = v_a_3998_;
v_snd_4003_ = v_snd_4000_;
v_err_4004_ = v___x_4013_;
goto v___jp_4001_;
}
else
{
lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4023_; 
lean_inc(v_fst_3999_);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_a_3998_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; lean_object* v_unused_4025_; 
v_unused_4024_ = lean_ctor_get(v_a_3998_, 1);
lean_dec(v_unused_4024_);
v_unused_4025_ = lean_ctor_get(v_a_3998_, 0);
lean_dec(v_unused_4025_);
v___x_4015_ = v_a_3998_;
v_isShared_4016_ = v_isSharedCheck_4023_;
goto v_resetjp_4014_;
}
else
{
lean_dec(v_a_3998_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4023_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; lean_object* v_it_x27_4019_; 
v___x_4017_ = lean_string_utf8_next_fast(v_fst_3999_, v_snd_4000_);
lean_dec(v_snd_4000_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 1, v___x_4017_);
v_it_x27_4019_ = v___x_4015_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_fst_3999_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v___x_4017_);
v_it_x27_4019_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; 
v___x_4020_ = lean_string_push(v_acc_3997_, v___x_4010_);
v_acc_3997_ = v___x_4020_;
v_a_3998_ = v_it_x27_4019_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4026_; 
v___x_4026_ = lean_box(0);
lean_inc(v_snd_4000_);
v_pos_4002_ = v_a_3998_;
v_snd_4003_ = v_snd_4000_;
v_err_4004_ = v___x_4026_;
goto v___jp_4001_;
}
v___jp_4001_:
{
uint8_t v_decide_4005_; 
v_decide_4005_ = lean_nat_dec_eq(v_snd_4000_, v_snd_4003_);
lean_dec(v_snd_4003_);
lean_dec(v_snd_4000_);
if (v_decide_4005_ == 0)
{
lean_object* v___x_4006_; 
lean_dec_ref(v_acc_3997_);
lean_inc(v_err_4004_);
v___x_4006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4006_, 0, v_pos_4002_);
lean_ctor_set(v___x_4006_, 1, v_err_4004_);
return v___x_4006_;
}
else
{
lean_object* v___x_4007_; 
v___x_4007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4007_, 0, v_pos_4002_);
lean_ctor_set(v___x_4007_, 1, v_acc_3997_);
return v___x_4007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(lean_object* v_acc_4030_, lean_object* v_a_4031_){
_start:
{
lean_object* v_fst_4032_; lean_object* v_snd_4033_; lean_object* v_pos_4035_; lean_object* v_snd_4036_; lean_object* v_err_4037_; lean_object* v___x_4041_; uint8_t v_decide_4042_; 
v_fst_4032_ = lean_ctor_get(v_a_4031_, 0);
v_snd_4033_ = lean_ctor_get(v_a_4031_, 1);
lean_inc(v_snd_4033_);
v___x_4041_ = lean_string_utf8_byte_size(v_fst_4032_);
v_decide_4042_ = lean_nat_dec_eq(v_snd_4033_, v___x_4041_);
if (v_decide_4042_ == 0)
{
uint32_t v___x_4043_; uint32_t v_c_4044_; uint8_t v___x_4045_; 
v___x_4043_ = 117;
v_c_4044_ = lean_string_utf8_get_fast(v_fst_4032_, v_snd_4033_);
v___x_4045_ = lean_uint32_dec_eq(v_c_4044_, v___x_4043_);
if (v___x_4045_ == 0)
{
lean_object* v___x_4046_; 
v___x_4046_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1));
lean_inc(v_snd_4033_);
v_pos_4035_ = v_a_4031_;
v_snd_4036_ = v_snd_4033_;
v_err_4037_ = v___x_4046_;
goto v___jp_4034_;
}
else
{
lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4056_; 
lean_inc(v_fst_4032_);
v_isSharedCheck_4056_ = !lean_is_exclusive(v_a_4031_);
if (v_isSharedCheck_4056_ == 0)
{
lean_object* v_unused_4057_; lean_object* v_unused_4058_; 
v_unused_4057_ = lean_ctor_get(v_a_4031_, 1);
lean_dec(v_unused_4057_);
v_unused_4058_ = lean_ctor_get(v_a_4031_, 0);
lean_dec(v_unused_4058_);
v___x_4048_ = v_a_4031_;
v_isShared_4049_ = v_isSharedCheck_4056_;
goto v_resetjp_4047_;
}
else
{
lean_dec(v_a_4031_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4056_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v_it_x27_4052_; 
v___x_4050_ = lean_string_utf8_next_fast(v_fst_4032_, v_snd_4033_);
lean_dec(v_snd_4033_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 1, v___x_4050_);
v_it_x27_4052_ = v___x_4048_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_fst_4032_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v___x_4050_);
v_it_x27_4052_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4053_; 
v___x_4053_ = lean_string_push(v_acc_4030_, v___x_4043_);
v_acc_4030_ = v___x_4053_;
v_a_4031_ = v_it_x27_4052_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4059_; 
v___x_4059_ = lean_box(0);
lean_inc(v_snd_4033_);
v_pos_4035_ = v_a_4031_;
v_snd_4036_ = v_snd_4033_;
v_err_4037_ = v___x_4059_;
goto v___jp_4034_;
}
v___jp_4034_:
{
uint8_t v_decide_4038_; 
v_decide_4038_ = lean_nat_dec_eq(v_snd_4033_, v_snd_4036_);
lean_dec(v_snd_4036_);
lean_dec(v_snd_4033_);
if (v_decide_4038_ == 0)
{
lean_object* v___x_4039_; 
lean_dec_ref(v_acc_4030_);
lean_inc(v_err_4037_);
v___x_4039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4039_, 0, v_pos_4035_);
lean_ctor_set(v___x_4039_, 1, v_err_4037_);
return v___x_4039_;
}
else
{
lean_object* v___x_4040_; 
v___x_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4040_, 0, v_pos_4035_);
lean_ctor_set(v___x_4040_, 1, v_acc_4030_);
return v___x_4040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(lean_object* v_acc_4063_, lean_object* v_a_4064_){
_start:
{
lean_object* v_fst_4065_; lean_object* v_snd_4066_; lean_object* v_pos_4068_; lean_object* v_snd_4069_; lean_object* v_err_4070_; lean_object* v___x_4074_; uint8_t v_decide_4075_; 
v_fst_4065_ = lean_ctor_get(v_a_4064_, 0);
v_snd_4066_ = lean_ctor_get(v_a_4064_, 1);
lean_inc(v_snd_4066_);
v___x_4074_ = lean_string_utf8_byte_size(v_fst_4065_);
v_decide_4075_ = lean_nat_dec_eq(v_snd_4066_, v___x_4074_);
if (v_decide_4075_ == 0)
{
uint32_t v___x_4076_; uint32_t v_c_4077_; uint8_t v___x_4078_; 
v___x_4076_ = 90;
v_c_4077_ = lean_string_utf8_get_fast(v_fst_4065_, v_snd_4066_);
v___x_4078_ = lean_uint32_dec_eq(v_c_4077_, v___x_4076_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; 
v___x_4079_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1));
lean_inc(v_snd_4066_);
v_pos_4068_ = v_a_4064_;
v_snd_4069_ = v_snd_4066_;
v_err_4070_ = v___x_4079_;
goto v___jp_4067_;
}
else
{
lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4089_; 
lean_inc(v_fst_4065_);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_a_4064_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; lean_object* v_unused_4091_; 
v_unused_4090_ = lean_ctor_get(v_a_4064_, 1);
lean_dec(v_unused_4090_);
v_unused_4091_ = lean_ctor_get(v_a_4064_, 0);
lean_dec(v_unused_4091_);
v___x_4081_ = v_a_4064_;
v_isShared_4082_ = v_isSharedCheck_4089_;
goto v_resetjp_4080_;
}
else
{
lean_dec(v_a_4064_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4089_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v_it_x27_4085_; 
v___x_4083_ = lean_string_utf8_next_fast(v_fst_4065_, v_snd_4066_);
lean_dec(v_snd_4066_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 1, v___x_4083_);
v_it_x27_4085_ = v___x_4081_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_fst_4065_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v___x_4083_);
v_it_x27_4085_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_string_push(v_acc_4063_, v___x_4076_);
v_acc_4063_ = v___x_4086_;
v_a_4064_ = v_it_x27_4085_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4092_; 
v___x_4092_ = lean_box(0);
lean_inc(v_snd_4066_);
v_pos_4068_ = v_a_4064_;
v_snd_4069_ = v_snd_4066_;
v_err_4070_ = v___x_4092_;
goto v___jp_4067_;
}
v___jp_4067_:
{
uint8_t v_decide_4071_; 
v_decide_4071_ = lean_nat_dec_eq(v_snd_4066_, v_snd_4069_);
lean_dec(v_snd_4069_);
lean_dec(v_snd_4066_);
if (v_decide_4071_ == 0)
{
lean_object* v___x_4072_; 
lean_dec_ref(v_acc_4063_);
lean_inc(v_err_4070_);
v___x_4072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4072_, 0, v_pos_4068_);
lean_ctor_set(v___x_4072_, 1, v_err_4070_);
return v___x_4072_;
}
else
{
lean_object* v___x_4073_; 
v___x_4073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4073_, 0, v_pos_4068_);
lean_ctor_set(v___x_4073_, 1, v_acc_4063_);
return v___x_4073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(lean_object* v_acc_4096_, lean_object* v_a_4097_){
_start:
{
lean_object* v_fst_4098_; lean_object* v_snd_4099_; lean_object* v_pos_4101_; lean_object* v_snd_4102_; lean_object* v_err_4103_; lean_object* v___x_4107_; uint8_t v_decide_4108_; 
v_fst_4098_ = lean_ctor_get(v_a_4097_, 0);
v_snd_4099_ = lean_ctor_get(v_a_4097_, 1);
lean_inc(v_snd_4099_);
v___x_4107_ = lean_string_utf8_byte_size(v_fst_4098_);
v_decide_4108_ = lean_nat_dec_eq(v_snd_4099_, v___x_4107_);
if (v_decide_4108_ == 0)
{
uint32_t v___x_4109_; uint32_t v_c_4110_; uint8_t v___x_4111_; 
v___x_4109_ = 78;
v_c_4110_ = lean_string_utf8_get_fast(v_fst_4098_, v_snd_4099_);
v___x_4111_ = lean_uint32_dec_eq(v_c_4110_, v___x_4109_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; 
v___x_4112_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1));
lean_inc(v_snd_4099_);
v_pos_4101_ = v_a_4097_;
v_snd_4102_ = v_snd_4099_;
v_err_4103_ = v___x_4112_;
goto v___jp_4100_;
}
else
{
lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4122_; 
lean_inc(v_fst_4098_);
v_isSharedCheck_4122_ = !lean_is_exclusive(v_a_4097_);
if (v_isSharedCheck_4122_ == 0)
{
lean_object* v_unused_4123_; lean_object* v_unused_4124_; 
v_unused_4123_ = lean_ctor_get(v_a_4097_, 1);
lean_dec(v_unused_4123_);
v_unused_4124_ = lean_ctor_get(v_a_4097_, 0);
lean_dec(v_unused_4124_);
v___x_4114_ = v_a_4097_;
v_isShared_4115_ = v_isSharedCheck_4122_;
goto v_resetjp_4113_;
}
else
{
lean_dec(v_a_4097_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4122_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4116_; lean_object* v_it_x27_4118_; 
v___x_4116_ = lean_string_utf8_next_fast(v_fst_4098_, v_snd_4099_);
lean_dec(v_snd_4099_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 1, v___x_4116_);
v_it_x27_4118_ = v___x_4114_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_fst_4098_);
lean_ctor_set(v_reuseFailAlloc_4121_, 1, v___x_4116_);
v_it_x27_4118_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
lean_object* v___x_4119_; 
v___x_4119_ = lean_string_push(v_acc_4096_, v___x_4109_);
v_acc_4096_ = v___x_4119_;
v_a_4097_ = v_it_x27_4118_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_box(0);
lean_inc(v_snd_4099_);
v_pos_4101_ = v_a_4097_;
v_snd_4102_ = v_snd_4099_;
v_err_4103_ = v___x_4125_;
goto v___jp_4100_;
}
v___jp_4100_:
{
uint8_t v_decide_4104_; 
v_decide_4104_ = lean_nat_dec_eq(v_snd_4099_, v_snd_4102_);
lean_dec(v_snd_4102_);
lean_dec(v_snd_4099_);
if (v_decide_4104_ == 0)
{
lean_object* v___x_4105_; 
lean_dec_ref(v_acc_4096_);
lean_inc(v_err_4103_);
v___x_4105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4105_, 0, v_pos_4101_);
lean_ctor_set(v___x_4105_, 1, v_err_4103_);
return v___x_4105_;
}
else
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4106_, 0, v_pos_4101_);
lean_ctor_set(v___x_4106_, 1, v_acc_4096_);
return v___x_4106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(lean_object* v_acc_4129_, lean_object* v_a_4130_){
_start:
{
lean_object* v_fst_4131_; lean_object* v_snd_4132_; lean_object* v_pos_4134_; lean_object* v_snd_4135_; lean_object* v_err_4136_; lean_object* v___x_4140_; uint8_t v_decide_4141_; 
v_fst_4131_ = lean_ctor_get(v_a_4130_, 0);
v_snd_4132_ = lean_ctor_get(v_a_4130_, 1);
lean_inc(v_snd_4132_);
v___x_4140_ = lean_string_utf8_byte_size(v_fst_4131_);
v_decide_4141_ = lean_nat_dec_eq(v_snd_4132_, v___x_4140_);
if (v_decide_4141_ == 0)
{
uint32_t v___x_4142_; uint32_t v_c_4143_; uint8_t v___x_4144_; 
v___x_4142_ = 70;
v_c_4143_ = lean_string_utf8_get_fast(v_fst_4131_, v_snd_4132_);
v___x_4144_ = lean_uint32_dec_eq(v_c_4143_, v___x_4142_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; 
v___x_4145_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1));
lean_inc(v_snd_4132_);
v_pos_4134_ = v_a_4130_;
v_snd_4135_ = v_snd_4132_;
v_err_4136_ = v___x_4145_;
goto v___jp_4133_;
}
else
{
lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4155_; 
lean_inc(v_fst_4131_);
v_isSharedCheck_4155_ = !lean_is_exclusive(v_a_4130_);
if (v_isSharedCheck_4155_ == 0)
{
lean_object* v_unused_4156_; lean_object* v_unused_4157_; 
v_unused_4156_ = lean_ctor_get(v_a_4130_, 1);
lean_dec(v_unused_4156_);
v_unused_4157_ = lean_ctor_get(v_a_4130_, 0);
lean_dec(v_unused_4157_);
v___x_4147_ = v_a_4130_;
v_isShared_4148_ = v_isSharedCheck_4155_;
goto v_resetjp_4146_;
}
else
{
lean_dec(v_a_4130_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4155_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; lean_object* v_it_x27_4151_; 
v___x_4149_ = lean_string_utf8_next_fast(v_fst_4131_, v_snd_4132_);
lean_dec(v_snd_4132_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 1, v___x_4149_);
v_it_x27_4151_ = v___x_4147_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_fst_4131_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v___x_4149_);
v_it_x27_4151_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4152_; 
v___x_4152_ = lean_string_push(v_acc_4129_, v___x_4142_);
v_acc_4129_ = v___x_4152_;
v_a_4130_ = v_it_x27_4151_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4158_; 
v___x_4158_ = lean_box(0);
lean_inc(v_snd_4132_);
v_pos_4134_ = v_a_4130_;
v_snd_4135_ = v_snd_4132_;
v_err_4136_ = v___x_4158_;
goto v___jp_4133_;
}
v___jp_4133_:
{
uint8_t v_decide_4137_; 
v_decide_4137_ = lean_nat_dec_eq(v_snd_4132_, v_snd_4135_);
lean_dec(v_snd_4135_);
lean_dec(v_snd_4132_);
if (v_decide_4137_ == 0)
{
lean_object* v___x_4138_; 
lean_dec_ref(v_acc_4129_);
lean_inc(v_err_4136_);
v___x_4138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4138_, 0, v_pos_4134_);
lean_ctor_set(v___x_4138_, 1, v_err_4136_);
return v___x_4138_;
}
else
{
lean_object* v___x_4139_; 
v___x_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4139_, 0, v_pos_4134_);
lean_ctor_set(v___x_4139_, 1, v_acc_4129_);
return v___x_4139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(lean_object* v_acc_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v_fst_4164_; lean_object* v_snd_4165_; lean_object* v_pos_4167_; lean_object* v_snd_4168_; lean_object* v_err_4169_; lean_object* v___x_4173_; uint8_t v_decide_4174_; 
v_fst_4164_ = lean_ctor_get(v_a_4163_, 0);
v_snd_4165_ = lean_ctor_get(v_a_4163_, 1);
lean_inc(v_snd_4165_);
v___x_4173_ = lean_string_utf8_byte_size(v_fst_4164_);
v_decide_4174_ = lean_nat_dec_eq(v_snd_4165_, v___x_4173_);
if (v_decide_4174_ == 0)
{
uint32_t v___x_4175_; uint32_t v_c_4176_; uint8_t v___x_4177_; 
v___x_4175_ = 66;
v_c_4176_ = lean_string_utf8_get_fast(v_fst_4164_, v_snd_4165_);
v___x_4177_ = lean_uint32_dec_eq(v_c_4176_, v___x_4175_);
if (v___x_4177_ == 0)
{
lean_object* v___x_4178_; 
v___x_4178_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1));
lean_inc(v_snd_4165_);
v_pos_4167_ = v_a_4163_;
v_snd_4168_ = v_snd_4165_;
v_err_4169_ = v___x_4178_;
goto v___jp_4166_;
}
else
{
lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4188_; 
lean_inc(v_fst_4164_);
v_isSharedCheck_4188_ = !lean_is_exclusive(v_a_4163_);
if (v_isSharedCheck_4188_ == 0)
{
lean_object* v_unused_4189_; lean_object* v_unused_4190_; 
v_unused_4189_ = lean_ctor_get(v_a_4163_, 1);
lean_dec(v_unused_4189_);
v_unused_4190_ = lean_ctor_get(v_a_4163_, 0);
lean_dec(v_unused_4190_);
v___x_4180_ = v_a_4163_;
v_isShared_4181_ = v_isSharedCheck_4188_;
goto v_resetjp_4179_;
}
else
{
lean_dec(v_a_4163_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4188_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4182_; lean_object* v_it_x27_4184_; 
v___x_4182_ = lean_string_utf8_next_fast(v_fst_4164_, v_snd_4165_);
lean_dec(v_snd_4165_);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 1, v___x_4182_);
v_it_x27_4184_ = v___x_4180_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_fst_4164_);
lean_ctor_set(v_reuseFailAlloc_4187_, 1, v___x_4182_);
v_it_x27_4184_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
lean_object* v___x_4185_; 
v___x_4185_ = lean_string_push(v_acc_4162_, v___x_4175_);
v_acc_4162_ = v___x_4185_;
v_a_4163_ = v_it_x27_4184_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4191_; 
v___x_4191_ = lean_box(0);
lean_inc(v_snd_4165_);
v_pos_4167_ = v_a_4163_;
v_snd_4168_ = v_snd_4165_;
v_err_4169_ = v___x_4191_;
goto v___jp_4166_;
}
v___jp_4166_:
{
uint8_t v_decide_4170_; 
v_decide_4170_ = lean_nat_dec_eq(v_snd_4165_, v_snd_4168_);
lean_dec(v_snd_4168_);
lean_dec(v_snd_4165_);
if (v_decide_4170_ == 0)
{
lean_object* v___x_4171_; 
lean_dec_ref(v_acc_4162_);
lean_inc(v_err_4169_);
v___x_4171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4171_, 0, v_pos_4167_);
lean_ctor_set(v___x_4171_, 1, v_err_4169_);
return v___x_4171_;
}
else
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4172_, 0, v_pos_4167_);
lean_ctor_set(v___x_4172_, 1, v_acc_4162_);
return v___x_4172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseModifier(lean_object* v_a_4265_){
_start:
{
lean_object* v_fst_4266_; lean_object* v_snd_4267_; lean_object* v___f_4268_; lean_object* v_snd_4270_; lean_object* v___y_4271_; lean_object* v_pos_4272_; lean_object* v_snd_4310_; lean_object* v_pos_4311_; lean_object* v_err_4312_; lean_object* v___f_4314_; lean_object* v_snd_4316_; lean_object* v___y_4317_; lean_object* v_pos_4318_; lean_object* v_snd_4348_; lean_object* v_pos_4349_; lean_object* v_err_4350_; lean_object* v___f_4352_; lean_object* v_snd_4354_; lean_object* v___y_4355_; lean_object* v_pos_4356_; lean_object* v_snd_4386_; lean_object* v_pos_4387_; lean_object* v_err_4388_; lean_object* v___f_4390_; lean_object* v_snd_4392_; lean_object* v___y_4393_; lean_object* v_pos_4394_; lean_object* v_snd_4424_; lean_object* v_pos_4425_; lean_object* v_err_4426_; lean_object* v___f_4428_; lean_object* v_snd_4430_; lean_object* v___y_4431_; lean_object* v_pos_4432_; lean_object* v_snd_4462_; lean_object* v_pos_4463_; lean_object* v_err_4464_; lean_object* v___f_4466_; lean_object* v_snd_4468_; lean_object* v___y_4469_; lean_object* v_pos_4470_; lean_object* v_snd_4500_; lean_object* v_pos_4501_; lean_object* v_err_4502_; lean_object* v_snd_4505_; lean_object* v___y_4506_; lean_object* v_pos_4507_; lean_object* v_snd_4537_; lean_object* v_pos_4538_; lean_object* v_err_4539_; lean_object* v___f_4541_; lean_object* v_snd_4543_; lean_object* v___y_4544_; lean_object* v_pos_4545_; lean_object* v_snd_4574_; lean_object* v_pos_4575_; lean_object* v_err_4576_; lean_object* v___f_4578_; lean_object* v_snd_4580_; lean_object* v___y_4581_; lean_object* v_pos_4582_; lean_object* v_snd_4611_; lean_object* v_pos_4612_; lean_object* v_err_4613_; lean_object* v___f_4615_; lean_object* v_snd_4617_; lean_object* v___y_4618_; lean_object* v_pos_4619_; lean_object* v_snd_4648_; lean_object* v_pos_4649_; lean_object* v_err_4650_; lean_object* v___f_4652_; lean_object* v_snd_4654_; lean_object* v___y_4655_; lean_object* v_pos_4656_; lean_object* v_snd_4686_; lean_object* v_pos_4687_; lean_object* v_err_4688_; lean_object* v___f_4690_; lean_object* v___y_4692_; lean_object* v_snd_4693_; lean_object* v___y_4694_; lean_object* v_pos_4695_; lean_object* v___y_4725_; lean_object* v_snd_4726_; lean_object* v_pos_4727_; lean_object* v_err_4728_; lean_object* v___f_4730_; lean_object* v___y_4732_; lean_object* v_snd_4733_; lean_object* v___y_4734_; lean_object* v_pos_4735_; lean_object* v___y_4765_; lean_object* v_snd_4766_; lean_object* v_pos_4767_; lean_object* v_err_4768_; lean_object* v___f_4770_; lean_object* v_snd_4772_; lean_object* v___y_4773_; lean_object* v___y_4774_; lean_object* v_pos_4775_; lean_object* v_snd_4805_; lean_object* v___y_4806_; lean_object* v_pos_4807_; lean_object* v_err_4808_; lean_object* v___f_4810_; lean_object* v_snd_4812_; lean_object* v___y_4813_; lean_object* v___y_4814_; lean_object* v_pos_4815_; lean_object* v_snd_4845_; lean_object* v___y_4846_; lean_object* v_pos_4847_; lean_object* v_err_4848_; lean_object* v___f_4850_; lean_object* v___y_4852_; lean_object* v_snd_4853_; lean_object* v___y_4854_; lean_object* v_pos_4855_; lean_object* v___y_4885_; lean_object* v_snd_4886_; lean_object* v_pos_4887_; lean_object* v_err_4888_; lean_object* v___f_4890_; lean_object* v_snd_4892_; lean_object* v___y_4893_; lean_object* v___y_4894_; lean_object* v_pos_4895_; lean_object* v_snd_4925_; lean_object* v___y_4926_; lean_object* v_pos_4927_; lean_object* v_err_4928_; lean_object* v___y_4931_; lean_object* v_snd_4932_; lean_object* v___y_4933_; lean_object* v_pos_4934_; lean_object* v___y_4964_; lean_object* v_snd_4965_; lean_object* v_pos_4966_; lean_object* v_err_4967_; lean_object* v___y_4970_; lean_object* v_snd_4971_; lean_object* v___y_4972_; lean_object* v_pos_4973_; lean_object* v___y_5003_; lean_object* v_snd_5004_; lean_object* v_pos_5005_; lean_object* v_err_5006_; lean_object* v_snd_5009_; lean_object* v___y_5010_; lean_object* v___y_5011_; lean_object* v_pos_5012_; lean_object* v_snd_5042_; lean_object* v___y_5043_; lean_object* v_pos_5044_; lean_object* v_err_5045_; lean_object* v___f_5047_; lean_object* v_snd_5049_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v___y_5052_; lean_object* v_pos_5053_; lean_object* v_snd_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v_pos_5086_; lean_object* v_err_5087_; lean_object* v___f_5089_; lean_object* v___y_5091_; lean_object* v___y_5092_; lean_object* v_snd_5093_; lean_object* v___y_5094_; lean_object* v_pos_5095_; lean_object* v___y_5125_; lean_object* v___y_5126_; lean_object* v_snd_5127_; lean_object* v_pos_5128_; lean_object* v_err_5129_; lean_object* v___f_5131_; lean_object* v_snd_5133_; lean_object* v___y_5134_; lean_object* v___y_5135_; lean_object* v___y_5136_; lean_object* v_pos_5137_; lean_object* v_snd_5167_; lean_object* v___y_5168_; lean_object* v___y_5169_; lean_object* v_pos_5170_; lean_object* v_err_5171_; lean_object* v___f_5173_; lean_object* v___y_5175_; lean_object* v___y_5176_; lean_object* v___y_5177_; lean_object* v___y_5178_; lean_object* v_pos_5179_; lean_object* v___y_5209_; lean_object* v___y_5210_; lean_object* v___y_5211_; lean_object* v_pos_5212_; lean_object* v_err_5213_; lean_object* v___f_5215_; lean_object* v___y_5217_; lean_object* v_snd_5218_; lean_object* v___y_5219_; lean_object* v_pos_5220_; lean_object* v___y_5251_; lean_object* v_snd_5252_; lean_object* v_pos_5253_; lean_object* v_err_5254_; lean_object* v___f_5256_; lean_object* v___y_5258_; lean_object* v_snd_5259_; lean_object* v___y_5260_; lean_object* v_pos_5261_; lean_object* v___y_5291_; lean_object* v_snd_5292_; lean_object* v_pos_5293_; lean_object* v_err_5294_; lean_object* v___f_5296_; lean_object* v___y_5298_; lean_object* v_snd_5299_; lean_object* v___y_5300_; lean_object* v_pos_5301_; lean_object* v___y_5331_; lean_object* v_snd_5332_; lean_object* v_pos_5333_; lean_object* v_err_5334_; lean_object* v___f_5336_; lean_object* v___y_5338_; lean_object* v___y_5339_; lean_object* v___y_5340_; lean_object* v_pos_5341_; lean_object* v___y_5371_; lean_object* v___y_5372_; lean_object* v_pos_5373_; lean_object* v_err_5374_; lean_object* v___f_5376_; lean_object* v_snd_5378_; lean_object* v___y_5379_; lean_object* v_pos_5380_; lean_object* v_snd_5411_; lean_object* v_pos_5412_; lean_object* v_err_5413_; lean_object* v___f_5415_; lean_object* v_snd_5417_; lean_object* v___y_5418_; lean_object* v_pos_5419_; lean_object* v_snd_5449_; lean_object* v_pos_5450_; lean_object* v_err_5451_; lean_object* v___f_5453_; lean_object* v_snd_5455_; lean_object* v___y_5456_; lean_object* v_pos_5457_; lean_object* v_snd_5487_; lean_object* v_pos_5488_; lean_object* v_err_5489_; lean_object* v___f_5491_; lean_object* v_snd_5493_; lean_object* v___y_5494_; lean_object* v_pos_5495_; lean_object* v_snd_5526_; lean_object* v_pos_5527_; lean_object* v_err_5528_; lean_object* v___f_5530_; lean_object* v_snd_5532_; lean_object* v___y_5533_; lean_object* v_pos_5534_; lean_object* v_snd_5564_; lean_object* v_pos_5565_; lean_object* v_err_5566_; lean_object* v___f_5568_; lean_object* v_snd_5570_; lean_object* v___y_5571_; lean_object* v_pos_5572_; lean_object* v_snd_5602_; lean_object* v_pos_5603_; lean_object* v_err_5604_; lean_object* v___f_5606_; lean_object* v___y_5608_; lean_object* v_pos_5609_; lean_object* v_pos_5639_; lean_object* v_err_5640_; lean_object* v___x_5642_; uint8_t v_decide_5643_; 
v_fst_4266_ = lean_ctor_get(v_a_4265_, 0);
v_snd_4267_ = lean_ctor_get(v_a_4265_, 1);
lean_inc(v_snd_4267_);
v___f_4268_ = ((lean_object*)(l_Std_Time_parseModifier___closed__0));
v___f_4314_ = ((lean_object*)(l_Std_Time_parseModifier___closed__2));
v___f_4352_ = ((lean_object*)(l_Std_Time_parseModifier___closed__4));
v___f_4390_ = ((lean_object*)(l_Std_Time_parseModifier___closed__6));
v___f_4428_ = ((lean_object*)(l_Std_Time_parseModifier___closed__8));
v___f_4466_ = ((lean_object*)(l_Std_Time_parseModifier___closed__10));
v___f_4541_ = ((lean_object*)(l_Std_Time_parseModifier___closed__13));
v___f_4578_ = ((lean_object*)(l_Std_Time_parseModifier___closed__15));
v___f_4615_ = ((lean_object*)(l_Std_Time_parseModifier___closed__17));
v___f_4652_ = ((lean_object*)(l_Std_Time_parseModifier___closed__19));
v___f_4690_ = ((lean_object*)(l_Std_Time_parseModifier___closed__21));
v___f_4730_ = ((lean_object*)(l_Std_Time_parseModifier___closed__23));
v___f_4770_ = ((lean_object*)(l_Std_Time_parseModifier___closed__25));
v___f_4810_ = ((lean_object*)(l_Std_Time_parseModifier___closed__27));
v___f_4850_ = ((lean_object*)(l_Std_Time_parseModifier___closed__29));
v___f_4890_ = ((lean_object*)(l_Std_Time_parseModifier___closed__31));
v___f_5047_ = ((lean_object*)(l_Std_Time_parseModifier___closed__36));
v___f_5089_ = ((lean_object*)(l_Std_Time_parseModifier___closed__38));
v___f_5131_ = ((lean_object*)(l_Std_Time_parseModifier___closed__40));
v___f_5173_ = ((lean_object*)(l_Std_Time_parseModifier___closed__42));
v___f_5215_ = ((lean_object*)(l_Std_Time_parseModifier___closed__44));
v___f_5256_ = ((lean_object*)(l_Std_Time_parseModifier___closed__47));
v___f_5296_ = ((lean_object*)(l_Std_Time_parseModifier___closed__49));
v___f_5336_ = ((lean_object*)(l_Std_Time_parseModifier___closed__51));
v___f_5376_ = ((lean_object*)(l_Std_Time_parseModifier___closed__53));
v___f_5415_ = ((lean_object*)(l_Std_Time_parseModifier___closed__56));
v___f_5453_ = ((lean_object*)(l_Std_Time_parseModifier___closed__58));
v___f_5491_ = ((lean_object*)(l_Std_Time_parseModifier___closed__60));
v___f_5530_ = ((lean_object*)(l_Std_Time_parseModifier___closed__63));
v___f_5568_ = ((lean_object*)(l_Std_Time_parseModifier___closed__65));
v___f_5606_ = ((lean_object*)(l_Std_Time_parseModifier___closed__67));
v___x_5642_ = lean_string_utf8_byte_size(v_fst_4266_);
v_decide_5643_ = lean_nat_dec_eq(v_snd_4267_, v___x_5642_);
if (v_decide_5643_ == 0)
{
uint32_t v___x_5644_; uint32_t v_c_5645_; uint8_t v___x_5646_; 
v___x_5644_ = 71;
v_c_5645_ = lean_string_utf8_get_fast(v_fst_4266_, v_snd_4267_);
v___x_5646_ = lean_uint32_dec_eq(v_c_5645_, v___x_5644_);
if (v___x_5646_ == 0)
{
lean_object* v___x_5647_; 
v___x_5647_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35___closed__1));
v_pos_5639_ = v_a_4265_;
v_err_5640_ = v___x_5647_;
goto v___jp_5638_;
}
else
{
lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5664_; 
lean_inc(v_fst_4266_);
v_isSharedCheck_5664_ = !lean_is_exclusive(v_a_4265_);
if (v_isSharedCheck_5664_ == 0)
{
lean_object* v_unused_5665_; lean_object* v_unused_5666_; 
v_unused_5665_ = lean_ctor_get(v_a_4265_, 1);
lean_dec(v_unused_5665_);
v_unused_5666_ = lean_ctor_get(v_a_4265_, 0);
lean_dec(v_unused_5666_);
v___x_5649_ = v_a_4265_;
v_isShared_5650_ = v_isSharedCheck_5664_;
goto v_resetjp_5648_;
}
else
{
lean_dec(v_a_4265_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5664_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5651_; lean_object* v_it_x27_5653_; 
v___x_5651_ = lean_string_utf8_next_fast(v_fst_4266_, v_snd_4267_);
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 1, v___x_5651_);
v_it_x27_5653_ = v___x_5649_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_fst_4266_);
lean_ctor_set(v_reuseFailAlloc_5663_, 1, v___x_5651_);
v_it_x27_5653_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
lean_object* v___x_5654_; lean_object* v___x_5655_; 
v___x_5654_ = ((lean_object*)(l_Std_Time_parseModifier___closed__69));
v___x_5655_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__35(v___x_5654_, v_it_x27_5653_);
if (lean_obj_tag(v___x_5655_) == 0)
{
lean_object* v_pos_5656_; lean_object* v_res_5657_; lean_object* v___f_5658_; lean_object* v___x_5659_; 
v_pos_5656_ = lean_ctor_get(v___x_5655_, 0);
lean_inc(v_pos_5656_);
v_res_5657_ = lean_ctor_get(v___x_5655_, 1);
lean_inc(v_res_5657_);
lean_dec_ref_known(v___x_5655_, 2);
v___f_5658_ = ((lean_object*)(l_Std_Time_parseModifier___closed__70));
v___x_5659_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseText(v___f_5658_, v_res_5657_, v_pos_5656_);
if (lean_obj_tag(v___x_5659_) == 0)
{
lean_dec(v_snd_4267_);
return v___x_5659_;
}
else
{
lean_object* v_pos_5660_; 
v_pos_5660_ = lean_ctor_get(v___x_5659_, 0);
lean_inc(v_pos_5660_);
v___y_5608_ = v___x_5659_;
v_pos_5609_ = v_pos_5660_;
goto v___jp_5607_;
}
}
else
{
lean_object* v_pos_5661_; lean_object* v_err_5662_; 
v_pos_5661_ = lean_ctor_get(v___x_5655_, 0);
lean_inc(v_pos_5661_);
v_err_5662_ = lean_ctor_get(v___x_5655_, 1);
lean_inc(v_err_5662_);
lean_dec_ref_known(v___x_5655_, 2);
v_pos_5639_ = v_pos_5661_;
v_err_5640_ = v_err_5662_;
goto v___jp_5638_;
}
}
}
}
}
else
{
lean_object* v___x_5667_; 
v___x_5667_ = lean_box(0);
v_pos_5639_ = v_a_4265_;
v_err_5640_ = v___x_5667_;
goto v___jp_5638_;
}
v___jp_4269_:
{
lean_object* v_fst_4273_; lean_object* v_snd_4274_; uint8_t v_decide_4275_; 
v_fst_4273_ = lean_ctor_get(v_pos_4272_, 0);
v_snd_4274_ = lean_ctor_get(v_pos_4272_, 1);
v_decide_4275_ = lean_nat_dec_eq(v_snd_4270_, v_snd_4274_);
lean_dec(v_snd_4270_);
if (v_decide_4275_ == 0)
{
lean_dec_ref(v_pos_4272_);
return v___y_4271_;
}
else
{
lean_object* v___x_4276_; uint8_t v_decide_4277_; 
lean_dec_ref(v___y_4271_);
v___x_4276_ = lean_string_utf8_byte_size(v_fst_4273_);
v_decide_4277_ = lean_nat_dec_eq(v_snd_4274_, v___x_4276_);
if (v_decide_4277_ == 0)
{
uint32_t v___x_4278_; uint32_t v_c_4279_; uint8_t v___x_4280_; 
v___x_4278_ = 90;
v_c_4279_ = lean_string_utf8_get_fast(v_fst_4273_, v_snd_4274_);
v___x_4280_ = lean_uint32_dec_eq(v_c_4279_, v___x_4278_);
if (v___x_4280_ == 0)
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0___closed__1));
v___x_4282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4282_, 0, v_pos_4272_);
lean_ctor_set(v___x_4282_, 1, v___x_4281_);
return v___x_4282_;
}
else
{
lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4304_; 
lean_inc(v_snd_4274_);
lean_inc(v_fst_4273_);
v_isSharedCheck_4304_ = !lean_is_exclusive(v_pos_4272_);
if (v_isSharedCheck_4304_ == 0)
{
lean_object* v_unused_4305_; lean_object* v_unused_4306_; 
v_unused_4305_ = lean_ctor_get(v_pos_4272_, 1);
lean_dec(v_unused_4305_);
v_unused_4306_ = lean_ctor_get(v_pos_4272_, 0);
lean_dec(v_unused_4306_);
v___x_4284_ = v_pos_4272_;
v_isShared_4285_ = v_isSharedCheck_4304_;
goto v_resetjp_4283_;
}
else
{
lean_dec(v_pos_4272_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4304_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4286_; lean_object* v_it_x27_4288_; 
v___x_4286_ = lean_string_utf8_next_fast(v_fst_4273_, v_snd_4274_);
lean_dec(v_snd_4274_);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 1, v___x_4286_);
v_it_x27_4288_ = v___x_4284_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_fst_4273_);
lean_ctor_set(v_reuseFailAlloc_4303_, 1, v___x_4286_);
v_it_x27_4288_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = ((lean_object*)(l_Std_Time_parseModifier___closed__1));
v___x_4290_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__0(v___x_4289_, v_it_x27_4288_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_pos_4291_; lean_object* v_res_4292_; lean_object* v___x_4293_; 
v_pos_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_pos_4291_);
v_res_4292_ = lean_ctor_get(v___x_4290_, 1);
lean_inc(v_res_4292_);
lean_dec_ref_known(v___x_4290_, 2);
v___x_4293_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetZ(v___f_4268_, v_res_4292_, v_pos_4291_);
return v___x_4293_;
}
else
{
lean_object* v_pos_4294_; lean_object* v_err_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
v_pos_4294_ = lean_ctor_get(v___x_4290_, 0);
v_err_4295_ = lean_ctor_get(v___x_4290_, 1);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4290_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_err_4295_);
lean_inc(v_pos_4294_);
lean_dec(v___x_4290_);
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
}
}
}
else
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4307_ = lean_box(0);
v___x_4308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4308_, 0, v_pos_4272_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
return v___x_4308_;
}
}
}
v___jp_4309_:
{
lean_object* v___x_4313_; 
lean_inc_ref(v_pos_4311_);
v___x_4313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4313_, 0, v_pos_4311_);
lean_ctor_set(v___x_4313_, 1, v_err_4312_);
v_snd_4270_ = v_snd_4310_;
v___y_4271_ = v___x_4313_;
v_pos_4272_ = v_pos_4311_;
goto v___jp_4269_;
}
v___jp_4315_:
{
lean_object* v_fst_4319_; lean_object* v_snd_4320_; uint8_t v_decide_4321_; 
v_fst_4319_ = lean_ctor_get(v_pos_4318_, 0);
v_snd_4320_ = lean_ctor_get(v_pos_4318_, 1);
lean_inc(v_snd_4320_);
v_decide_4321_ = lean_nat_dec_eq(v_snd_4316_, v_snd_4320_);
lean_dec(v_snd_4316_);
if (v_decide_4321_ == 0)
{
lean_dec(v_snd_4320_);
lean_dec_ref(v_pos_4318_);
return v___y_4317_;
}
else
{
lean_object* v___x_4322_; uint8_t v_decide_4323_; 
lean_dec_ref(v___y_4317_);
v___x_4322_ = lean_string_utf8_byte_size(v_fst_4319_);
v_decide_4323_ = lean_nat_dec_eq(v_snd_4320_, v___x_4322_);
if (v_decide_4323_ == 0)
{
uint32_t v___x_4324_; uint32_t v_c_4325_; uint8_t v___x_4326_; 
v___x_4324_ = 120;
v_c_4325_ = lean_string_utf8_get_fast(v_fst_4319_, v_snd_4320_);
v___x_4326_ = lean_uint32_dec_eq(v_c_4325_, v___x_4324_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; 
v___x_4327_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1___closed__1));
v_snd_4310_ = v_snd_4320_;
v_pos_4311_ = v_pos_4318_;
v_err_4312_ = v___x_4327_;
goto v___jp_4309_;
}
else
{
lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4343_; 
lean_inc(v_fst_4319_);
v_isSharedCheck_4343_ = !lean_is_exclusive(v_pos_4318_);
if (v_isSharedCheck_4343_ == 0)
{
lean_object* v_unused_4344_; lean_object* v_unused_4345_; 
v_unused_4344_ = lean_ctor_get(v_pos_4318_, 1);
lean_dec(v_unused_4344_);
v_unused_4345_ = lean_ctor_get(v_pos_4318_, 0);
lean_dec(v_unused_4345_);
v___x_4329_ = v_pos_4318_;
v_isShared_4330_ = v_isSharedCheck_4343_;
goto v_resetjp_4328_;
}
else
{
lean_dec(v_pos_4318_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4343_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4331_; lean_object* v_it_x27_4333_; 
v___x_4331_ = lean_string_utf8_next_fast(v_fst_4319_, v_snd_4320_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 1, v___x_4331_);
v_it_x27_4333_ = v___x_4329_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_fst_4319_);
lean_ctor_set(v_reuseFailAlloc_4342_, 1, v___x_4331_);
v_it_x27_4333_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = ((lean_object*)(l_Std_Time_parseModifier___closed__3));
v___x_4335_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__1(v___x_4334_, v_it_x27_4333_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_pos_4336_; lean_object* v_res_4337_; lean_object* v___x_4338_; 
v_pos_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_pos_4336_);
v_res_4337_ = lean_ctor_get(v___x_4335_, 1);
lean_inc(v_res_4337_);
lean_dec_ref_known(v___x_4335_, 2);
v___x_4338_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4314_, v_res_4337_, v_pos_4336_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_dec(v_snd_4320_);
return v___x_4338_;
}
else
{
lean_object* v_pos_4339_; 
v_pos_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_pos_4339_);
v_snd_4270_ = v_snd_4320_;
v___y_4271_ = v___x_4338_;
v_pos_4272_ = v_pos_4339_;
goto v___jp_4269_;
}
}
else
{
lean_object* v_pos_4340_; lean_object* v_err_4341_; 
v_pos_4340_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_pos_4340_);
v_err_4341_ = lean_ctor_get(v___x_4335_, 1);
lean_inc(v_err_4341_);
lean_dec_ref_known(v___x_4335_, 2);
v_snd_4310_ = v_snd_4320_;
v_pos_4311_ = v_pos_4340_;
v_err_4312_ = v_err_4341_;
goto v___jp_4309_;
}
}
}
}
}
else
{
lean_object* v___x_4346_; 
v___x_4346_ = lean_box(0);
v_snd_4310_ = v_snd_4320_;
v_pos_4311_ = v_pos_4318_;
v_err_4312_ = v___x_4346_;
goto v___jp_4309_;
}
}
}
v___jp_4347_:
{
lean_object* v___x_4351_; 
lean_inc_ref(v_pos_4349_);
v___x_4351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4351_, 0, v_pos_4349_);
lean_ctor_set(v___x_4351_, 1, v_err_4350_);
v_snd_4316_ = v_snd_4348_;
v___y_4317_ = v___x_4351_;
v_pos_4318_ = v_pos_4349_;
goto v___jp_4315_;
}
v___jp_4353_:
{
lean_object* v_fst_4357_; lean_object* v_snd_4358_; uint8_t v_decide_4359_; 
v_fst_4357_ = lean_ctor_get(v_pos_4356_, 0);
v_snd_4358_ = lean_ctor_get(v_pos_4356_, 1);
lean_inc(v_snd_4358_);
v_decide_4359_ = lean_nat_dec_eq(v_snd_4354_, v_snd_4358_);
lean_dec(v_snd_4354_);
if (v_decide_4359_ == 0)
{
lean_dec(v_snd_4358_);
lean_dec_ref(v_pos_4356_);
return v___y_4355_;
}
else
{
lean_object* v___x_4360_; uint8_t v_decide_4361_; 
lean_dec_ref(v___y_4355_);
v___x_4360_ = lean_string_utf8_byte_size(v_fst_4357_);
v_decide_4361_ = lean_nat_dec_eq(v_snd_4358_, v___x_4360_);
if (v_decide_4361_ == 0)
{
uint32_t v___x_4362_; uint32_t v_c_4363_; uint8_t v___x_4364_; 
v___x_4362_ = 88;
v_c_4363_ = lean_string_utf8_get_fast(v_fst_4357_, v_snd_4358_);
v___x_4364_ = lean_uint32_dec_eq(v_c_4363_, v___x_4362_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; 
v___x_4365_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2___closed__1));
v_snd_4348_ = v_snd_4358_;
v_pos_4349_ = v_pos_4356_;
v_err_4350_ = v___x_4365_;
goto v___jp_4347_;
}
else
{
lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4381_; 
lean_inc(v_fst_4357_);
v_isSharedCheck_4381_ = !lean_is_exclusive(v_pos_4356_);
if (v_isSharedCheck_4381_ == 0)
{
lean_object* v_unused_4382_; lean_object* v_unused_4383_; 
v_unused_4382_ = lean_ctor_get(v_pos_4356_, 1);
lean_dec(v_unused_4382_);
v_unused_4383_ = lean_ctor_get(v_pos_4356_, 0);
lean_dec(v_unused_4383_);
v___x_4367_ = v_pos_4356_;
v_isShared_4368_ = v_isSharedCheck_4381_;
goto v_resetjp_4366_;
}
else
{
lean_dec(v_pos_4356_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4381_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4369_; lean_object* v_it_x27_4371_; 
v___x_4369_ = lean_string_utf8_next_fast(v_fst_4357_, v_snd_4358_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 1, v___x_4369_);
v_it_x27_4371_ = v___x_4367_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_fst_4357_);
lean_ctor_set(v_reuseFailAlloc_4380_, 1, v___x_4369_);
v_it_x27_4371_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4372_ = ((lean_object*)(l_Std_Time_parseModifier___closed__5));
v___x_4373_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__2(v___x_4372_, v_it_x27_4371_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_pos_4374_; lean_object* v_res_4375_; lean_object* v___x_4376_; 
v_pos_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_pos_4374_);
v_res_4375_ = lean_ctor_get(v___x_4373_, 1);
lean_inc(v_res_4375_);
lean_dec_ref_known(v___x_4373_, 2);
v___x_4376_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetX(v___f_4352_, v_res_4375_, v_pos_4374_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_dec(v_snd_4358_);
return v___x_4376_;
}
else
{
lean_object* v_pos_4377_; 
v_pos_4377_ = lean_ctor_get(v___x_4376_, 0);
lean_inc(v_pos_4377_);
v_snd_4316_ = v_snd_4358_;
v___y_4317_ = v___x_4376_;
v_pos_4318_ = v_pos_4377_;
goto v___jp_4315_;
}
}
else
{
lean_object* v_pos_4378_; lean_object* v_err_4379_; 
v_pos_4378_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_pos_4378_);
v_err_4379_ = lean_ctor_get(v___x_4373_, 1);
lean_inc(v_err_4379_);
lean_dec_ref_known(v___x_4373_, 2);
v_snd_4348_ = v_snd_4358_;
v_pos_4349_ = v_pos_4378_;
v_err_4350_ = v_err_4379_;
goto v___jp_4347_;
}
}
}
}
}
else
{
lean_object* v___x_4384_; 
v___x_4384_ = lean_box(0);
v_snd_4348_ = v_snd_4358_;
v_pos_4349_ = v_pos_4356_;
v_err_4350_ = v___x_4384_;
goto v___jp_4347_;
}
}
}
v___jp_4385_:
{
lean_object* v___x_4389_; 
lean_inc_ref(v_pos_4387_);
v___x_4389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4389_, 0, v_pos_4387_);
lean_ctor_set(v___x_4389_, 1, v_err_4388_);
v_snd_4354_ = v_snd_4386_;
v___y_4355_ = v___x_4389_;
v_pos_4356_ = v_pos_4387_;
goto v___jp_4353_;
}
v___jp_4391_:
{
lean_object* v_fst_4395_; lean_object* v_snd_4396_; uint8_t v_decide_4397_; 
v_fst_4395_ = lean_ctor_get(v_pos_4394_, 0);
v_snd_4396_ = lean_ctor_get(v_pos_4394_, 1);
lean_inc(v_snd_4396_);
v_decide_4397_ = lean_nat_dec_eq(v_snd_4392_, v_snd_4396_);
lean_dec(v_snd_4392_);
if (v_decide_4397_ == 0)
{
lean_dec(v_snd_4396_);
lean_dec_ref(v_pos_4394_);
return v___y_4393_;
}
else
{
lean_object* v___x_4398_; uint8_t v_decide_4399_; 
lean_dec_ref(v___y_4393_);
v___x_4398_ = lean_string_utf8_byte_size(v_fst_4395_);
v_decide_4399_ = lean_nat_dec_eq(v_snd_4396_, v___x_4398_);
if (v_decide_4399_ == 0)
{
uint32_t v___x_4400_; uint32_t v_c_4401_; uint8_t v___x_4402_; 
v___x_4400_ = 79;
v_c_4401_ = lean_string_utf8_get_fast(v_fst_4395_, v_snd_4396_);
v___x_4402_ = lean_uint32_dec_eq(v_c_4401_, v___x_4400_);
if (v___x_4402_ == 0)
{
lean_object* v___x_4403_; 
v___x_4403_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3___closed__1));
v_snd_4386_ = v_snd_4396_;
v_pos_4387_ = v_pos_4394_;
v_err_4388_ = v___x_4403_;
goto v___jp_4385_;
}
else
{
lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4419_; 
lean_inc(v_fst_4395_);
v_isSharedCheck_4419_ = !lean_is_exclusive(v_pos_4394_);
if (v_isSharedCheck_4419_ == 0)
{
lean_object* v_unused_4420_; lean_object* v_unused_4421_; 
v_unused_4420_ = lean_ctor_get(v_pos_4394_, 1);
lean_dec(v_unused_4420_);
v_unused_4421_ = lean_ctor_get(v_pos_4394_, 0);
lean_dec(v_unused_4421_);
v___x_4405_ = v_pos_4394_;
v_isShared_4406_ = v_isSharedCheck_4419_;
goto v_resetjp_4404_;
}
else
{
lean_dec(v_pos_4394_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4419_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4407_; lean_object* v_it_x27_4409_; 
v___x_4407_ = lean_string_utf8_next_fast(v_fst_4395_, v_snd_4396_);
if (v_isShared_4406_ == 0)
{
lean_ctor_set(v___x_4405_, 1, v___x_4407_);
v_it_x27_4409_ = v___x_4405_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_fst_4395_);
lean_ctor_set(v_reuseFailAlloc_4418_, 1, v___x_4407_);
v_it_x27_4409_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4410_ = ((lean_object*)(l_Std_Time_parseModifier___closed__7));
v___x_4411_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__3(v___x_4410_, v_it_x27_4409_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_pos_4412_; lean_object* v_res_4413_; lean_object* v___x_4414_; 
v_pos_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_pos_4412_);
v_res_4413_ = lean_ctor_get(v___x_4411_, 1);
lean_inc(v_res_4413_);
lean_dec_ref_known(v___x_4411_, 2);
v___x_4414_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseOffsetO(v___f_4390_, v_res_4413_, v_pos_4412_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_dec(v_snd_4396_);
return v___x_4414_;
}
else
{
lean_object* v_pos_4415_; 
v_pos_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_pos_4415_);
v_snd_4354_ = v_snd_4396_;
v___y_4355_ = v___x_4414_;
v_pos_4356_ = v_pos_4415_;
goto v___jp_4353_;
}
}
else
{
lean_object* v_pos_4416_; lean_object* v_err_4417_; 
v_pos_4416_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_pos_4416_);
v_err_4417_ = lean_ctor_get(v___x_4411_, 1);
lean_inc(v_err_4417_);
lean_dec_ref_known(v___x_4411_, 2);
v_snd_4386_ = v_snd_4396_;
v_pos_4387_ = v_pos_4416_;
v_err_4388_ = v_err_4417_;
goto v___jp_4385_;
}
}
}
}
}
else
{
lean_object* v___x_4422_; 
v___x_4422_ = lean_box(0);
v_snd_4386_ = v_snd_4396_;
v_pos_4387_ = v_pos_4394_;
v_err_4388_ = v___x_4422_;
goto v___jp_4385_;
}
}
}
v___jp_4423_:
{
lean_object* v___x_4427_; 
lean_inc_ref(v_pos_4425_);
v___x_4427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4427_, 0, v_pos_4425_);
lean_ctor_set(v___x_4427_, 1, v_err_4426_);
v_snd_4392_ = v_snd_4424_;
v___y_4393_ = v___x_4427_;
v_pos_4394_ = v_pos_4425_;
goto v___jp_4391_;
}
v___jp_4429_:
{
lean_object* v_fst_4433_; lean_object* v_snd_4434_; uint8_t v_decide_4435_; 
v_fst_4433_ = lean_ctor_get(v_pos_4432_, 0);
v_snd_4434_ = lean_ctor_get(v_pos_4432_, 1);
lean_inc(v_snd_4434_);
v_decide_4435_ = lean_nat_dec_eq(v_snd_4430_, v_snd_4434_);
lean_dec(v_snd_4430_);
if (v_decide_4435_ == 0)
{
lean_dec(v_snd_4434_);
lean_dec_ref(v_pos_4432_);
return v___y_4431_;
}
else
{
lean_object* v___x_4436_; uint8_t v_decide_4437_; 
lean_dec_ref(v___y_4431_);
v___x_4436_ = lean_string_utf8_byte_size(v_fst_4433_);
v_decide_4437_ = lean_nat_dec_eq(v_snd_4434_, v___x_4436_);
if (v_decide_4437_ == 0)
{
uint32_t v___x_4438_; uint32_t v_c_4439_; uint8_t v___x_4440_; 
v___x_4438_ = 118;
v_c_4439_ = lean_string_utf8_get_fast(v_fst_4433_, v_snd_4434_);
v___x_4440_ = lean_uint32_dec_eq(v_c_4439_, v___x_4438_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4441_; 
v___x_4441_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4___closed__1));
v_snd_4424_ = v_snd_4434_;
v_pos_4425_ = v_pos_4432_;
v_err_4426_ = v___x_4441_;
goto v___jp_4423_;
}
else
{
lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4457_; 
lean_inc(v_fst_4433_);
v_isSharedCheck_4457_ = !lean_is_exclusive(v_pos_4432_);
if (v_isSharedCheck_4457_ == 0)
{
lean_object* v_unused_4458_; lean_object* v_unused_4459_; 
v_unused_4458_ = lean_ctor_get(v_pos_4432_, 1);
lean_dec(v_unused_4458_);
v_unused_4459_ = lean_ctor_get(v_pos_4432_, 0);
lean_dec(v_unused_4459_);
v___x_4443_ = v_pos_4432_;
v_isShared_4444_ = v_isSharedCheck_4457_;
goto v_resetjp_4442_;
}
else
{
lean_dec(v_pos_4432_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4457_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4445_; lean_object* v_it_x27_4447_; 
v___x_4445_ = lean_string_utf8_next_fast(v_fst_4433_, v_snd_4434_);
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 1, v___x_4445_);
v_it_x27_4447_ = v___x_4443_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_fst_4433_);
lean_ctor_set(v_reuseFailAlloc_4456_, 1, v___x_4445_);
v_it_x27_4447_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4448_ = ((lean_object*)(l_Std_Time_parseModifier___closed__9));
v___x_4449_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__4(v___x_4448_, v_it_x27_4447_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_pos_4450_; lean_object* v_res_4451_; lean_object* v___x_4452_; 
v_pos_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_pos_4450_);
v_res_4451_ = lean_ctor_get(v___x_4449_, 1);
lean_inc(v_res_4451_);
lean_dec_ref_known(v___x_4449_, 2);
v___x_4452_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4428_, v_res_4451_, v_pos_4450_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_dec(v_snd_4434_);
return v___x_4452_;
}
else
{
lean_object* v_pos_4453_; 
v_pos_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_pos_4453_);
v_snd_4392_ = v_snd_4434_;
v___y_4393_ = v___x_4452_;
v_pos_4394_ = v_pos_4453_;
goto v___jp_4391_;
}
}
else
{
lean_object* v_pos_4454_; lean_object* v_err_4455_; 
v_pos_4454_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_pos_4454_);
v_err_4455_ = lean_ctor_get(v___x_4449_, 1);
lean_inc(v_err_4455_);
lean_dec_ref_known(v___x_4449_, 2);
v_snd_4424_ = v_snd_4434_;
v_pos_4425_ = v_pos_4454_;
v_err_4426_ = v_err_4455_;
goto v___jp_4423_;
}
}
}
}
}
else
{
lean_object* v___x_4460_; 
v___x_4460_ = lean_box(0);
v_snd_4424_ = v_snd_4434_;
v_pos_4425_ = v_pos_4432_;
v_err_4426_ = v___x_4460_;
goto v___jp_4423_;
}
}
}
v___jp_4461_:
{
lean_object* v___x_4465_; 
lean_inc_ref(v_pos_4463_);
v___x_4465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4465_, 0, v_pos_4463_);
lean_ctor_set(v___x_4465_, 1, v_err_4464_);
v_snd_4430_ = v_snd_4462_;
v___y_4431_ = v___x_4465_;
v_pos_4432_ = v_pos_4463_;
goto v___jp_4429_;
}
v___jp_4467_:
{
lean_object* v_fst_4471_; lean_object* v_snd_4472_; uint8_t v_decide_4473_; 
v_fst_4471_ = lean_ctor_get(v_pos_4470_, 0);
v_snd_4472_ = lean_ctor_get(v_pos_4470_, 1);
lean_inc(v_snd_4472_);
v_decide_4473_ = lean_nat_dec_eq(v_snd_4468_, v_snd_4472_);
lean_dec(v_snd_4468_);
if (v_decide_4473_ == 0)
{
lean_dec(v_snd_4472_);
lean_dec_ref(v_pos_4470_);
return v___y_4469_;
}
else
{
lean_object* v___x_4474_; uint8_t v_decide_4475_; 
lean_dec_ref(v___y_4469_);
v___x_4474_ = lean_string_utf8_byte_size(v_fst_4471_);
v_decide_4475_ = lean_nat_dec_eq(v_snd_4472_, v___x_4474_);
if (v_decide_4475_ == 0)
{
uint32_t v___x_4476_; uint32_t v_c_4477_; uint8_t v___x_4478_; 
v___x_4476_ = 122;
v_c_4477_ = lean_string_utf8_get_fast(v_fst_4471_, v_snd_4472_);
v___x_4478_ = lean_uint32_dec_eq(v_c_4477_, v___x_4476_);
if (v___x_4478_ == 0)
{
lean_object* v___x_4479_; 
v___x_4479_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5___closed__1));
v_snd_4462_ = v_snd_4472_;
v_pos_4463_ = v_pos_4470_;
v_err_4464_ = v___x_4479_;
goto v___jp_4461_;
}
else
{
lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4495_; 
lean_inc(v_fst_4471_);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_pos_4470_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; lean_object* v_unused_4497_; 
v_unused_4496_ = lean_ctor_get(v_pos_4470_, 1);
lean_dec(v_unused_4496_);
v_unused_4497_ = lean_ctor_get(v_pos_4470_, 0);
lean_dec(v_unused_4497_);
v___x_4481_ = v_pos_4470_;
v_isShared_4482_ = v_isSharedCheck_4495_;
goto v_resetjp_4480_;
}
else
{
lean_dec(v_pos_4470_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4495_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4483_; lean_object* v_it_x27_4485_; 
v___x_4483_ = lean_string_utf8_next_fast(v_fst_4471_, v_snd_4472_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 1, v___x_4483_);
v_it_x27_4485_ = v___x_4481_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_fst_4471_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v___x_4483_);
v_it_x27_4485_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4486_ = ((lean_object*)(l_Std_Time_parseModifier___closed__11));
v___x_4487_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__5(v___x_4486_, v_it_x27_4485_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_pos_4488_; lean_object* v_res_4489_; lean_object* v___x_4490_; 
v_pos_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_pos_4488_);
v_res_4489_ = lean_ctor_get(v___x_4487_, 1);
lean_inc(v_res_4489_);
lean_dec_ref_known(v___x_4487_, 2);
v___x_4490_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneName(v___f_4466_, v_res_4489_, v_pos_4488_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_dec(v_snd_4472_);
return v___x_4490_;
}
else
{
lean_object* v_pos_4491_; 
v_pos_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_pos_4491_);
v_snd_4430_ = v_snd_4472_;
v___y_4431_ = v___x_4490_;
v_pos_4432_ = v_pos_4491_;
goto v___jp_4429_;
}
}
else
{
lean_object* v_pos_4492_; lean_object* v_err_4493_; 
v_pos_4492_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_pos_4492_);
v_err_4493_ = lean_ctor_get(v___x_4487_, 1);
lean_inc(v_err_4493_);
lean_dec_ref_known(v___x_4487_, 2);
v_snd_4462_ = v_snd_4472_;
v_pos_4463_ = v_pos_4492_;
v_err_4464_ = v_err_4493_;
goto v___jp_4461_;
}
}
}
}
}
else
{
lean_object* v___x_4498_; 
v___x_4498_ = lean_box(0);
v_snd_4462_ = v_snd_4472_;
v_pos_4463_ = v_pos_4470_;
v_err_4464_ = v___x_4498_;
goto v___jp_4461_;
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
v_snd_4468_ = v_snd_4500_;
v___y_4469_ = v___x_4503_;
v_pos_4470_ = v_pos_4501_;
goto v___jp_4467_;
}
v___jp_4504_:
{
lean_object* v_fst_4508_; lean_object* v_snd_4509_; uint8_t v_decide_4510_; 
v_fst_4508_ = lean_ctor_get(v_pos_4507_, 0);
v_snd_4509_ = lean_ctor_get(v_pos_4507_, 1);
lean_inc(v_snd_4509_);
v_decide_4510_ = lean_nat_dec_eq(v_snd_4505_, v_snd_4509_);
lean_dec(v_snd_4505_);
if (v_decide_4510_ == 0)
{
lean_dec(v_snd_4509_);
lean_dec_ref(v_pos_4507_);
return v___y_4506_;
}
else
{
lean_object* v___x_4511_; uint8_t v_decide_4512_; 
lean_dec_ref(v___y_4506_);
v___x_4511_ = lean_string_utf8_byte_size(v_fst_4508_);
v_decide_4512_ = lean_nat_dec_eq(v_snd_4509_, v___x_4511_);
if (v_decide_4512_ == 0)
{
uint32_t v___x_4513_; uint32_t v_c_4514_; uint8_t v___x_4515_; 
v___x_4513_ = 86;
v_c_4514_ = lean_string_utf8_get_fast(v_fst_4508_, v_snd_4509_);
v___x_4515_ = lean_uint32_dec_eq(v_c_4514_, v___x_4513_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; 
v___x_4516_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6___closed__1));
v_snd_4500_ = v_snd_4509_;
v_pos_4501_ = v_pos_4507_;
v_err_4502_ = v___x_4516_;
goto v___jp_4499_;
}
else
{
lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4532_; 
lean_inc(v_fst_4508_);
v_isSharedCheck_4532_ = !lean_is_exclusive(v_pos_4507_);
if (v_isSharedCheck_4532_ == 0)
{
lean_object* v_unused_4533_; lean_object* v_unused_4534_; 
v_unused_4533_ = lean_ctor_get(v_pos_4507_, 1);
lean_dec(v_unused_4533_);
v_unused_4534_ = lean_ctor_get(v_pos_4507_, 0);
lean_dec(v_unused_4534_);
v___x_4518_ = v_pos_4507_;
v_isShared_4519_ = v_isSharedCheck_4532_;
goto v_resetjp_4517_;
}
else
{
lean_dec(v_pos_4507_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4532_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4520_; lean_object* v_it_x27_4522_; 
v___x_4520_ = lean_string_utf8_next_fast(v_fst_4508_, v_snd_4509_);
if (v_isShared_4519_ == 0)
{
lean_ctor_set(v___x_4518_, 1, v___x_4520_);
v_it_x27_4522_ = v___x_4518_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_fst_4508_);
lean_ctor_set(v_reuseFailAlloc_4531_, 1, v___x_4520_);
v_it_x27_4522_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = ((lean_object*)(l_Std_Time_parseModifier___closed__12));
v___x_4524_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__6(v___x_4523_, v_it_x27_4522_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_pos_4525_; lean_object* v_res_4526_; lean_object* v___x_4527_; 
v_pos_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_pos_4525_);
v_res_4526_ = lean_ctor_get(v___x_4524_, 1);
lean_inc(v_res_4526_);
lean_dec_ref_known(v___x_4524_, 2);
v___x_4527_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseZoneId(v_res_4526_, v_pos_4525_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_dec(v_snd_4509_);
return v___x_4527_;
}
else
{
lean_object* v_pos_4528_; 
v_pos_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc(v_pos_4528_);
v_snd_4468_ = v_snd_4509_;
v___y_4469_ = v___x_4527_;
v_pos_4470_ = v_pos_4528_;
goto v___jp_4467_;
}
}
else
{
lean_object* v_pos_4529_; lean_object* v_err_4530_; 
v_pos_4529_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_pos_4529_);
v_err_4530_ = lean_ctor_get(v___x_4524_, 1);
lean_inc(v_err_4530_);
lean_dec_ref_known(v___x_4524_, 2);
v_snd_4500_ = v_snd_4509_;
v_pos_4501_ = v_pos_4529_;
v_err_4502_ = v_err_4530_;
goto v___jp_4499_;
}
}
}
}
}
else
{
lean_object* v___x_4535_; 
v___x_4535_ = lean_box(0);
v_snd_4500_ = v_snd_4509_;
v_pos_4501_ = v_pos_4507_;
v_err_4502_ = v___x_4535_;
goto v___jp_4499_;
}
}
}
v___jp_4536_:
{
lean_object* v___x_4540_; 
lean_inc_ref(v_pos_4538_);
v___x_4540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4540_, 0, v_pos_4538_);
lean_ctor_set(v___x_4540_, 1, v_err_4539_);
v_snd_4505_ = v_snd_4537_;
v___y_4506_ = v___x_4540_;
v_pos_4507_ = v_pos_4538_;
goto v___jp_4504_;
}
v___jp_4542_:
{
lean_object* v_fst_4546_; lean_object* v_snd_4547_; uint8_t v_decide_4548_; 
v_fst_4546_ = lean_ctor_get(v_pos_4545_, 0);
v_snd_4547_ = lean_ctor_get(v_pos_4545_, 1);
lean_inc(v_snd_4547_);
v_decide_4548_ = lean_nat_dec_eq(v_snd_4543_, v_snd_4547_);
lean_dec(v_snd_4543_);
if (v_decide_4548_ == 0)
{
lean_dec(v_snd_4547_);
lean_dec_ref(v_pos_4545_);
return v___y_4544_;
}
else
{
lean_object* v___x_4549_; uint8_t v_decide_4550_; 
lean_dec_ref(v___y_4544_);
v___x_4549_ = lean_string_utf8_byte_size(v_fst_4546_);
v_decide_4550_ = lean_nat_dec_eq(v_snd_4547_, v___x_4549_);
if (v_decide_4550_ == 0)
{
uint32_t v___x_4551_; uint32_t v_c_4552_; uint8_t v___x_4553_; 
v___x_4551_ = 78;
v_c_4552_ = lean_string_utf8_get_fast(v_fst_4546_, v_snd_4547_);
v___x_4553_ = lean_uint32_dec_eq(v_c_4552_, v___x_4551_);
if (v___x_4553_ == 0)
{
lean_object* v___x_4554_; 
v___x_4554_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7___closed__1));
v_snd_4537_ = v_snd_4547_;
v_pos_4538_ = v_pos_4545_;
v_err_4539_ = v___x_4554_;
goto v___jp_4536_;
}
else
{
lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4569_; 
lean_inc(v_fst_4546_);
v_isSharedCheck_4569_ = !lean_is_exclusive(v_pos_4545_);
if (v_isSharedCheck_4569_ == 0)
{
lean_object* v_unused_4570_; lean_object* v_unused_4571_; 
v_unused_4570_ = lean_ctor_get(v_pos_4545_, 1);
lean_dec(v_unused_4570_);
v_unused_4571_ = lean_ctor_get(v_pos_4545_, 0);
lean_dec(v_unused_4571_);
v___x_4556_ = v_pos_4545_;
v_isShared_4557_ = v_isSharedCheck_4569_;
goto v_resetjp_4555_;
}
else
{
lean_dec(v_pos_4545_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4569_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4558_; lean_object* v_it_x27_4560_; 
v___x_4558_ = lean_string_utf8_next_fast(v_fst_4546_, v_snd_4547_);
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 1, v___x_4558_);
v_it_x27_4560_ = v___x_4556_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_fst_4546_);
lean_ctor_set(v_reuseFailAlloc_4568_, 1, v___x_4558_);
v_it_x27_4560_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4561_ = ((lean_object*)(l_Std_Time_parseModifier___closed__14));
v___x_4562_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__7(v___x_4561_, v_it_x27_4560_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_pos_4563_; lean_object* v_res_4564_; lean_object* v___x_4565_; 
lean_dec(v_snd_4547_);
v_pos_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_pos_4563_);
v_res_4564_ = lean_ctor_get(v___x_4562_, 1);
lean_inc(v_res_4564_);
lean_dec_ref_known(v___x_4562_, 2);
v___x_4565_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4541_, v_res_4564_, v_pos_4563_);
lean_dec(v_res_4564_);
return v___x_4565_;
}
else
{
lean_object* v_pos_4566_; lean_object* v_err_4567_; 
v_pos_4566_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_pos_4566_);
v_err_4567_ = lean_ctor_get(v___x_4562_, 1);
lean_inc(v_err_4567_);
lean_dec_ref_known(v___x_4562_, 2);
v_snd_4537_ = v_snd_4547_;
v_pos_4538_ = v_pos_4566_;
v_err_4539_ = v_err_4567_;
goto v___jp_4536_;
}
}
}
}
}
else
{
lean_object* v___x_4572_; 
v___x_4572_ = lean_box(0);
v_snd_4537_ = v_snd_4547_;
v_pos_4538_ = v_pos_4545_;
v_err_4539_ = v___x_4572_;
goto v___jp_4536_;
}
}
}
v___jp_4573_:
{
lean_object* v___x_4577_; 
lean_inc_ref(v_pos_4575_);
v___x_4577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4577_, 0, v_pos_4575_);
lean_ctor_set(v___x_4577_, 1, v_err_4576_);
v_snd_4543_ = v_snd_4574_;
v___y_4544_ = v___x_4577_;
v_pos_4545_ = v_pos_4575_;
goto v___jp_4542_;
}
v___jp_4579_:
{
lean_object* v_fst_4583_; lean_object* v_snd_4584_; uint8_t v_decide_4585_; 
v_fst_4583_ = lean_ctor_get(v_pos_4582_, 0);
v_snd_4584_ = lean_ctor_get(v_pos_4582_, 1);
lean_inc(v_snd_4584_);
v_decide_4585_ = lean_nat_dec_eq(v_snd_4580_, v_snd_4584_);
lean_dec(v_snd_4580_);
if (v_decide_4585_ == 0)
{
lean_dec(v_snd_4584_);
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
uint32_t v___x_4588_; uint32_t v_c_4589_; uint8_t v___x_4590_; 
v___x_4588_ = 110;
v_c_4589_ = lean_string_utf8_get_fast(v_fst_4583_, v_snd_4584_);
v___x_4590_ = lean_uint32_dec_eq(v_c_4589_, v___x_4588_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; 
v___x_4591_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8___closed__1));
v_snd_4574_ = v_snd_4584_;
v_pos_4575_ = v_pos_4582_;
v_err_4576_ = v___x_4591_;
goto v___jp_4573_;
}
else
{
lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4606_; 
lean_inc(v_fst_4583_);
v_isSharedCheck_4606_ = !lean_is_exclusive(v_pos_4582_);
if (v_isSharedCheck_4606_ == 0)
{
lean_object* v_unused_4607_; lean_object* v_unused_4608_; 
v_unused_4607_ = lean_ctor_get(v_pos_4582_, 1);
lean_dec(v_unused_4607_);
v_unused_4608_ = lean_ctor_get(v_pos_4582_, 0);
lean_dec(v_unused_4608_);
v___x_4593_ = v_pos_4582_;
v_isShared_4594_ = v_isSharedCheck_4606_;
goto v_resetjp_4592_;
}
else
{
lean_dec(v_pos_4582_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4606_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v_it_x27_4597_; 
v___x_4595_ = lean_string_utf8_next_fast(v_fst_4583_, v_snd_4584_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 1, v___x_4595_);
v_it_x27_4597_ = v___x_4593_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_fst_4583_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v___x_4595_);
v_it_x27_4597_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = ((lean_object*)(l_Std_Time_parseModifier___closed__16));
v___x_4599_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__8(v___x_4598_, v_it_x27_4597_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_pos_4600_; lean_object* v_res_4601_; lean_object* v___x_4602_; 
lean_dec(v_snd_4584_);
v_pos_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_pos_4600_);
v_res_4601_ = lean_ctor_get(v___x_4599_, 1);
lean_inc(v_res_4601_);
lean_dec_ref_known(v___x_4599_, 2);
v___x_4602_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4578_, v_res_4601_, v_pos_4600_);
lean_dec(v_res_4601_);
return v___x_4602_;
}
else
{
lean_object* v_pos_4603_; lean_object* v_err_4604_; 
v_pos_4603_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_pos_4603_);
v_err_4604_ = lean_ctor_get(v___x_4599_, 1);
lean_inc(v_err_4604_);
lean_dec_ref_known(v___x_4599_, 2);
v_snd_4574_ = v_snd_4584_;
v_pos_4575_ = v_pos_4603_;
v_err_4576_ = v_err_4604_;
goto v___jp_4573_;
}
}
}
}
}
else
{
lean_object* v___x_4609_; 
v___x_4609_ = lean_box(0);
v_snd_4574_ = v_snd_4584_;
v_pos_4575_ = v_pos_4582_;
v_err_4576_ = v___x_4609_;
goto v___jp_4573_;
}
}
}
v___jp_4610_:
{
lean_object* v___x_4614_; 
lean_inc_ref(v_pos_4612_);
v___x_4614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4614_, 0, v_pos_4612_);
lean_ctor_set(v___x_4614_, 1, v_err_4613_);
v_snd_4580_ = v_snd_4611_;
v___y_4581_ = v___x_4614_;
v_pos_4582_ = v_pos_4612_;
goto v___jp_4579_;
}
v___jp_4616_:
{
lean_object* v_fst_4620_; lean_object* v_snd_4621_; uint8_t v_decide_4622_; 
v_fst_4620_ = lean_ctor_get(v_pos_4619_, 0);
v_snd_4621_ = lean_ctor_get(v_pos_4619_, 1);
lean_inc(v_snd_4621_);
v_decide_4622_ = lean_nat_dec_eq(v_snd_4617_, v_snd_4621_);
lean_dec(v_snd_4617_);
if (v_decide_4622_ == 0)
{
lean_dec(v_snd_4621_);
lean_dec_ref(v_pos_4619_);
return v___y_4618_;
}
else
{
lean_object* v___x_4623_; uint8_t v_decide_4624_; 
lean_dec_ref(v___y_4618_);
v___x_4623_ = lean_string_utf8_byte_size(v_fst_4620_);
v_decide_4624_ = lean_nat_dec_eq(v_snd_4621_, v___x_4623_);
if (v_decide_4624_ == 0)
{
uint32_t v___x_4625_; uint32_t v_c_4626_; uint8_t v___x_4627_; 
v___x_4625_ = 65;
v_c_4626_ = lean_string_utf8_get_fast(v_fst_4620_, v_snd_4621_);
v___x_4627_ = lean_uint32_dec_eq(v_c_4626_, v___x_4625_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4628_; 
v___x_4628_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9___closed__1));
v_snd_4611_ = v_snd_4621_;
v_pos_4612_ = v_pos_4619_;
v_err_4613_ = v___x_4628_;
goto v___jp_4610_;
}
else
{
lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4643_; 
lean_inc(v_fst_4620_);
v_isSharedCheck_4643_ = !lean_is_exclusive(v_pos_4619_);
if (v_isSharedCheck_4643_ == 0)
{
lean_object* v_unused_4644_; lean_object* v_unused_4645_; 
v_unused_4644_ = lean_ctor_get(v_pos_4619_, 1);
lean_dec(v_unused_4644_);
v_unused_4645_ = lean_ctor_get(v_pos_4619_, 0);
lean_dec(v_unused_4645_);
v___x_4630_ = v_pos_4619_;
v_isShared_4631_ = v_isSharedCheck_4643_;
goto v_resetjp_4629_;
}
else
{
lean_dec(v_pos_4619_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4643_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4632_; lean_object* v_it_x27_4634_; 
v___x_4632_ = lean_string_utf8_next_fast(v_fst_4620_, v_snd_4621_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 1, v___x_4632_);
v_it_x27_4634_ = v___x_4630_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_fst_4620_);
lean_ctor_set(v_reuseFailAlloc_4642_, 1, v___x_4632_);
v_it_x27_4634_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = ((lean_object*)(l_Std_Time_parseModifier___closed__18));
v___x_4636_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__9(v___x_4635_, v_it_x27_4634_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_pos_4637_; lean_object* v_res_4638_; lean_object* v___x_4639_; 
lean_dec(v_snd_4621_);
v_pos_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_pos_4637_);
v_res_4638_ = lean_ctor_get(v___x_4636_, 1);
lean_inc(v_res_4638_);
lean_dec_ref_known(v___x_4636_, 2);
v___x_4639_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumber(v___f_4615_, v_res_4638_, v_pos_4637_);
lean_dec(v_res_4638_);
return v___x_4639_;
}
else
{
lean_object* v_pos_4640_; lean_object* v_err_4641_; 
v_pos_4640_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_pos_4640_);
v_err_4641_ = lean_ctor_get(v___x_4636_, 1);
lean_inc(v_err_4641_);
lean_dec_ref_known(v___x_4636_, 2);
v_snd_4611_ = v_snd_4621_;
v_pos_4612_ = v_pos_4640_;
v_err_4613_ = v_err_4641_;
goto v___jp_4610_;
}
}
}
}
}
else
{
lean_object* v___x_4646_; 
v___x_4646_ = lean_box(0);
v_snd_4611_ = v_snd_4621_;
v_pos_4612_ = v_pos_4619_;
v_err_4613_ = v___x_4646_;
goto v___jp_4610_;
}
}
}
v___jp_4647_:
{
lean_object* v___x_4651_; 
lean_inc_ref(v_pos_4649_);
v___x_4651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4651_, 0, v_pos_4649_);
lean_ctor_set(v___x_4651_, 1, v_err_4650_);
v_snd_4617_ = v_snd_4648_;
v___y_4618_ = v___x_4651_;
v_pos_4619_ = v_pos_4649_;
goto v___jp_4616_;
}
v___jp_4653_:
{
lean_object* v_fst_4657_; lean_object* v_snd_4658_; uint8_t v_decide_4659_; 
v_fst_4657_ = lean_ctor_get(v_pos_4656_, 0);
v_snd_4658_ = lean_ctor_get(v_pos_4656_, 1);
lean_inc(v_snd_4658_);
v_decide_4659_ = lean_nat_dec_eq(v_snd_4654_, v_snd_4658_);
lean_dec(v_snd_4654_);
if (v_decide_4659_ == 0)
{
lean_dec(v_snd_4658_);
lean_dec_ref(v_pos_4656_);
return v___y_4655_;
}
else
{
lean_object* v___x_4660_; uint8_t v_decide_4661_; 
lean_dec_ref(v___y_4655_);
v___x_4660_ = lean_string_utf8_byte_size(v_fst_4657_);
v_decide_4661_ = lean_nat_dec_eq(v_snd_4658_, v___x_4660_);
if (v_decide_4661_ == 0)
{
uint32_t v___x_4662_; uint32_t v_c_4663_; uint8_t v___x_4664_; 
v___x_4662_ = 83;
v_c_4663_ = lean_string_utf8_get_fast(v_fst_4657_, v_snd_4658_);
v___x_4664_ = lean_uint32_dec_eq(v_c_4663_, v___x_4662_);
if (v___x_4664_ == 0)
{
lean_object* v___x_4665_; 
v___x_4665_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10___closed__1));
v_snd_4648_ = v_snd_4658_;
v_pos_4649_ = v_pos_4656_;
v_err_4650_ = v___x_4665_;
goto v___jp_4647_;
}
else
{
lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4681_; 
lean_inc(v_fst_4657_);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_pos_4656_);
if (v_isSharedCheck_4681_ == 0)
{
lean_object* v_unused_4682_; lean_object* v_unused_4683_; 
v_unused_4682_ = lean_ctor_get(v_pos_4656_, 1);
lean_dec(v_unused_4682_);
v_unused_4683_ = lean_ctor_get(v_pos_4656_, 0);
lean_dec(v_unused_4683_);
v___x_4667_ = v_pos_4656_;
v_isShared_4668_ = v_isSharedCheck_4681_;
goto v_resetjp_4666_;
}
else
{
lean_dec(v_pos_4656_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4681_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4669_; lean_object* v_it_x27_4671_; 
v___x_4669_ = lean_string_utf8_next_fast(v_fst_4657_, v_snd_4658_);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 1, v___x_4669_);
v_it_x27_4671_ = v___x_4667_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_fst_4657_);
lean_ctor_set(v_reuseFailAlloc_4680_, 1, v___x_4669_);
v_it_x27_4671_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4672_ = ((lean_object*)(l_Std_Time_parseModifier___closed__20));
v___x_4673_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__10(v___x_4672_, v_it_x27_4671_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_pos_4674_; lean_object* v_res_4675_; lean_object* v___x_4676_; 
v_pos_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_pos_4674_);
v_res_4675_ = lean_ctor_get(v___x_4673_, 1);
lean_inc(v_res_4675_);
lean_dec_ref_known(v___x_4673_, 2);
v___x_4676_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseFraction(v___f_4652_, v_res_4675_, v_pos_4674_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_dec(v_snd_4658_);
return v___x_4676_;
}
else
{
lean_object* v_pos_4677_; 
v_pos_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_pos_4677_);
v_snd_4617_ = v_snd_4658_;
v___y_4618_ = v___x_4676_;
v_pos_4619_ = v_pos_4677_;
goto v___jp_4616_;
}
}
else
{
lean_object* v_pos_4678_; lean_object* v_err_4679_; 
v_pos_4678_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_pos_4678_);
v_err_4679_ = lean_ctor_get(v___x_4673_, 1);
lean_inc(v_err_4679_);
lean_dec_ref_known(v___x_4673_, 2);
v_snd_4648_ = v_snd_4658_;
v_pos_4649_ = v_pos_4678_;
v_err_4650_ = v_err_4679_;
goto v___jp_4647_;
}
}
}
}
}
else
{
lean_object* v___x_4684_; 
v___x_4684_ = lean_box(0);
v_snd_4648_ = v_snd_4658_;
v_pos_4649_ = v_pos_4656_;
v_err_4650_ = v___x_4684_;
goto v___jp_4647_;
}
}
}
v___jp_4685_:
{
lean_object* v___x_4689_; 
lean_inc_ref(v_pos_4687_);
v___x_4689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4689_, 0, v_pos_4687_);
lean_ctor_set(v___x_4689_, 1, v_err_4688_);
v_snd_4654_ = v_snd_4686_;
v___y_4655_ = v___x_4689_;
v_pos_4656_ = v_pos_4687_;
goto v___jp_4653_;
}
v___jp_4691_:
{
lean_object* v_fst_4696_; lean_object* v_snd_4697_; uint8_t v_decide_4698_; 
v_fst_4696_ = lean_ctor_get(v_pos_4695_, 0);
v_snd_4697_ = lean_ctor_get(v_pos_4695_, 1);
lean_inc(v_snd_4697_);
v_decide_4698_ = lean_nat_dec_eq(v_snd_4693_, v_snd_4697_);
lean_dec(v_snd_4693_);
if (v_decide_4698_ == 0)
{
lean_dec(v_snd_4697_);
lean_dec_ref(v_pos_4695_);
lean_dec_ref(v___y_4692_);
return v___y_4694_;
}
else
{
lean_object* v___x_4699_; uint8_t v_decide_4700_; 
lean_dec_ref(v___y_4694_);
v___x_4699_ = lean_string_utf8_byte_size(v_fst_4696_);
v_decide_4700_ = lean_nat_dec_eq(v_snd_4697_, v___x_4699_);
if (v_decide_4700_ == 0)
{
uint32_t v___x_4701_; uint32_t v_c_4702_; uint8_t v___x_4703_; 
v___x_4701_ = 115;
v_c_4702_ = lean_string_utf8_get_fast(v_fst_4696_, v_snd_4697_);
v___x_4703_ = lean_uint32_dec_eq(v_c_4702_, v___x_4701_);
if (v___x_4703_ == 0)
{
lean_object* v___x_4704_; 
lean_dec_ref(v___y_4692_);
v___x_4704_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11___closed__1));
v_snd_4686_ = v_snd_4697_;
v_pos_4687_ = v_pos_4695_;
v_err_4688_ = v___x_4704_;
goto v___jp_4685_;
}
else
{
lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4720_; 
lean_inc(v_fst_4696_);
v_isSharedCheck_4720_ = !lean_is_exclusive(v_pos_4695_);
if (v_isSharedCheck_4720_ == 0)
{
lean_object* v_unused_4721_; lean_object* v_unused_4722_; 
v_unused_4721_ = lean_ctor_get(v_pos_4695_, 1);
lean_dec(v_unused_4721_);
v_unused_4722_ = lean_ctor_get(v_pos_4695_, 0);
lean_dec(v_unused_4722_);
v___x_4706_ = v_pos_4695_;
v_isShared_4707_ = v_isSharedCheck_4720_;
goto v_resetjp_4705_;
}
else
{
lean_dec(v_pos_4695_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4720_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v_it_x27_4710_; 
v___x_4708_ = lean_string_utf8_next_fast(v_fst_4696_, v_snd_4697_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 1, v___x_4708_);
v_it_x27_4710_ = v___x_4706_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_fst_4696_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v___x_4708_);
v_it_x27_4710_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4711_ = ((lean_object*)(l_Std_Time_parseModifier___closed__22));
v___x_4712_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__11(v___x_4711_, v_it_x27_4710_);
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_pos_4713_; lean_object* v_res_4714_; lean_object* v___x_4715_; 
v_pos_4713_ = lean_ctor_get(v___x_4712_, 0);
lean_inc(v_pos_4713_);
v_res_4714_ = lean_ctor_get(v___x_4712_, 1);
lean_inc(v_res_4714_);
lean_dec_ref_known(v___x_4712_, 2);
v___x_4715_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4690_, v___y_4692_, v_res_4714_, v_pos_4713_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_dec(v_snd_4697_);
return v___x_4715_;
}
else
{
lean_object* v_pos_4716_; 
v_pos_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_pos_4716_);
v_snd_4654_ = v_snd_4697_;
v___y_4655_ = v___x_4715_;
v_pos_4656_ = v_pos_4716_;
goto v___jp_4653_;
}
}
else
{
lean_object* v_pos_4717_; lean_object* v_err_4718_; 
lean_dec_ref(v___y_4692_);
v_pos_4717_ = lean_ctor_get(v___x_4712_, 0);
lean_inc(v_pos_4717_);
v_err_4718_ = lean_ctor_get(v___x_4712_, 1);
lean_inc(v_err_4718_);
lean_dec_ref_known(v___x_4712_, 2);
v_snd_4686_ = v_snd_4697_;
v_pos_4687_ = v_pos_4717_;
v_err_4688_ = v_err_4718_;
goto v___jp_4685_;
}
}
}
}
}
else
{
lean_object* v___x_4723_; 
lean_dec_ref(v___y_4692_);
v___x_4723_ = lean_box(0);
v_snd_4686_ = v_snd_4697_;
v_pos_4687_ = v_pos_4695_;
v_err_4688_ = v___x_4723_;
goto v___jp_4685_;
}
}
}
v___jp_4724_:
{
lean_object* v___x_4729_; 
lean_inc_ref(v_pos_4727_);
v___x_4729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4729_, 0, v_pos_4727_);
lean_ctor_set(v___x_4729_, 1, v_err_4728_);
v___y_4692_ = v___y_4725_;
v_snd_4693_ = v_snd_4726_;
v___y_4694_ = v___x_4729_;
v_pos_4695_ = v_pos_4727_;
goto v___jp_4691_;
}
v___jp_4731_:
{
lean_object* v_fst_4736_; lean_object* v_snd_4737_; uint8_t v_decide_4738_; 
v_fst_4736_ = lean_ctor_get(v_pos_4735_, 0);
v_snd_4737_ = lean_ctor_get(v_pos_4735_, 1);
lean_inc(v_snd_4737_);
v_decide_4738_ = lean_nat_dec_eq(v_snd_4733_, v_snd_4737_);
lean_dec(v_snd_4733_);
if (v_decide_4738_ == 0)
{
lean_dec(v_snd_4737_);
lean_dec_ref(v_pos_4735_);
lean_dec_ref(v___y_4732_);
return v___y_4734_;
}
else
{
lean_object* v___x_4739_; uint8_t v_decide_4740_; 
lean_dec_ref(v___y_4734_);
v___x_4739_ = lean_string_utf8_byte_size(v_fst_4736_);
v_decide_4740_ = lean_nat_dec_eq(v_snd_4737_, v___x_4739_);
if (v_decide_4740_ == 0)
{
uint32_t v___x_4741_; uint32_t v_c_4742_; uint8_t v___x_4743_; 
v___x_4741_ = 109;
v_c_4742_ = lean_string_utf8_get_fast(v_fst_4736_, v_snd_4737_);
v___x_4743_ = lean_uint32_dec_eq(v_c_4742_, v___x_4741_);
if (v___x_4743_ == 0)
{
lean_object* v___x_4744_; 
v___x_4744_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12___closed__1));
v___y_4725_ = v___y_4732_;
v_snd_4726_ = v_snd_4737_;
v_pos_4727_ = v_pos_4735_;
v_err_4728_ = v___x_4744_;
goto v___jp_4724_;
}
else
{
lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4760_; 
lean_inc(v_fst_4736_);
v_isSharedCheck_4760_ = !lean_is_exclusive(v_pos_4735_);
if (v_isSharedCheck_4760_ == 0)
{
lean_object* v_unused_4761_; lean_object* v_unused_4762_; 
v_unused_4761_ = lean_ctor_get(v_pos_4735_, 1);
lean_dec(v_unused_4761_);
v_unused_4762_ = lean_ctor_get(v_pos_4735_, 0);
lean_dec(v_unused_4762_);
v___x_4746_ = v_pos_4735_;
v_isShared_4747_ = v_isSharedCheck_4760_;
goto v_resetjp_4745_;
}
else
{
lean_dec(v_pos_4735_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4760_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4748_; lean_object* v_it_x27_4750_; 
v___x_4748_ = lean_string_utf8_next_fast(v_fst_4736_, v_snd_4737_);
if (v_isShared_4747_ == 0)
{
lean_ctor_set(v___x_4746_, 1, v___x_4748_);
v_it_x27_4750_ = v___x_4746_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_fst_4736_);
lean_ctor_set(v_reuseFailAlloc_4759_, 1, v___x_4748_);
v_it_x27_4750_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4751_ = ((lean_object*)(l_Std_Time_parseModifier___closed__24));
v___x_4752_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__12(v___x_4751_, v_it_x27_4750_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_object* v_pos_4753_; lean_object* v_res_4754_; lean_object* v___x_4755_; 
v_pos_4753_ = lean_ctor_get(v___x_4752_, 0);
lean_inc(v_pos_4753_);
v_res_4754_ = lean_ctor_get(v___x_4752_, 1);
lean_inc(v_res_4754_);
lean_dec_ref_known(v___x_4752_, 2);
lean_inc_ref(v___y_4732_);
v___x_4755_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4730_, v___y_4732_, v_res_4754_, v_pos_4753_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_dec(v_snd_4737_);
lean_dec_ref(v___y_4732_);
return v___x_4755_;
}
else
{
lean_object* v_pos_4756_; 
v_pos_4756_ = lean_ctor_get(v___x_4755_, 0);
lean_inc(v_pos_4756_);
v___y_4692_ = v___y_4732_;
v_snd_4693_ = v_snd_4737_;
v___y_4694_ = v___x_4755_;
v_pos_4695_ = v_pos_4756_;
goto v___jp_4691_;
}
}
else
{
lean_object* v_pos_4757_; lean_object* v_err_4758_; 
v_pos_4757_ = lean_ctor_get(v___x_4752_, 0);
lean_inc(v_pos_4757_);
v_err_4758_ = lean_ctor_get(v___x_4752_, 1);
lean_inc(v_err_4758_);
lean_dec_ref_known(v___x_4752_, 2);
v___y_4725_ = v___y_4732_;
v_snd_4726_ = v_snd_4737_;
v_pos_4727_ = v_pos_4757_;
v_err_4728_ = v_err_4758_;
goto v___jp_4724_;
}
}
}
}
}
else
{
lean_object* v___x_4763_; 
v___x_4763_ = lean_box(0);
v___y_4725_ = v___y_4732_;
v_snd_4726_ = v_snd_4737_;
v_pos_4727_ = v_pos_4735_;
v_err_4728_ = v___x_4763_;
goto v___jp_4724_;
}
}
}
v___jp_4764_:
{
lean_object* v___x_4769_; 
lean_inc_ref(v_pos_4767_);
v___x_4769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4769_, 0, v_pos_4767_);
lean_ctor_set(v___x_4769_, 1, v_err_4768_);
v___y_4732_ = v___y_4765_;
v_snd_4733_ = v_snd_4766_;
v___y_4734_ = v___x_4769_;
v_pos_4735_ = v_pos_4767_;
goto v___jp_4731_;
}
v___jp_4771_:
{
lean_object* v_fst_4776_; lean_object* v_snd_4777_; uint8_t v_decide_4778_; 
v_fst_4776_ = lean_ctor_get(v_pos_4775_, 0);
v_snd_4777_ = lean_ctor_get(v_pos_4775_, 1);
lean_inc(v_snd_4777_);
v_decide_4778_ = lean_nat_dec_eq(v_snd_4772_, v_snd_4777_);
lean_dec(v_snd_4772_);
if (v_decide_4778_ == 0)
{
lean_dec(v_snd_4777_);
lean_dec_ref(v_pos_4775_);
lean_dec_ref(v___y_4773_);
return v___y_4774_;
}
else
{
lean_object* v___x_4779_; uint8_t v_decide_4780_; 
lean_dec_ref(v___y_4774_);
v___x_4779_ = lean_string_utf8_byte_size(v_fst_4776_);
v_decide_4780_ = lean_nat_dec_eq(v_snd_4777_, v___x_4779_);
if (v_decide_4780_ == 0)
{
uint32_t v___x_4781_; uint32_t v_c_4782_; uint8_t v___x_4783_; 
v___x_4781_ = 72;
v_c_4782_ = lean_string_utf8_get_fast(v_fst_4776_, v_snd_4777_);
v___x_4783_ = lean_uint32_dec_eq(v_c_4782_, v___x_4781_);
if (v___x_4783_ == 0)
{
lean_object* v___x_4784_; 
v___x_4784_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13___closed__1));
v___y_4765_ = v___y_4773_;
v_snd_4766_ = v_snd_4777_;
v_pos_4767_ = v_pos_4775_;
v_err_4768_ = v___x_4784_;
goto v___jp_4764_;
}
else
{
lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4800_; 
lean_inc(v_fst_4776_);
v_isSharedCheck_4800_ = !lean_is_exclusive(v_pos_4775_);
if (v_isSharedCheck_4800_ == 0)
{
lean_object* v_unused_4801_; lean_object* v_unused_4802_; 
v_unused_4801_ = lean_ctor_get(v_pos_4775_, 1);
lean_dec(v_unused_4801_);
v_unused_4802_ = lean_ctor_get(v_pos_4775_, 0);
lean_dec(v_unused_4802_);
v___x_4786_ = v_pos_4775_;
v_isShared_4787_ = v_isSharedCheck_4800_;
goto v_resetjp_4785_;
}
else
{
lean_dec(v_pos_4775_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4800_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4788_; lean_object* v_it_x27_4790_; 
v___x_4788_ = lean_string_utf8_next_fast(v_fst_4776_, v_snd_4777_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 1, v___x_4788_);
v_it_x27_4790_ = v___x_4786_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_fst_4776_);
lean_ctor_set(v_reuseFailAlloc_4799_, 1, v___x_4788_);
v_it_x27_4790_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = ((lean_object*)(l_Std_Time_parseModifier___closed__26));
v___x_4792_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__13(v___x_4791_, v_it_x27_4790_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v_pos_4793_; lean_object* v_res_4794_; lean_object* v___x_4795_; 
v_pos_4793_ = lean_ctor_get(v___x_4792_, 0);
lean_inc(v_pos_4793_);
v_res_4794_ = lean_ctor_get(v___x_4792_, 1);
lean_inc(v_res_4794_);
lean_dec_ref_known(v___x_4792_, 2);
lean_inc_ref(v___y_4773_);
v___x_4795_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4770_, v___y_4773_, v_res_4794_, v_pos_4793_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_dec(v_snd_4777_);
lean_dec_ref(v___y_4773_);
return v___x_4795_;
}
else
{
lean_object* v_pos_4796_; 
v_pos_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_pos_4796_);
v___y_4732_ = v___y_4773_;
v_snd_4733_ = v_snd_4777_;
v___y_4734_ = v___x_4795_;
v_pos_4735_ = v_pos_4796_;
goto v___jp_4731_;
}
}
else
{
lean_object* v_pos_4797_; lean_object* v_err_4798_; 
v_pos_4797_ = lean_ctor_get(v___x_4792_, 0);
lean_inc(v_pos_4797_);
v_err_4798_ = lean_ctor_get(v___x_4792_, 1);
lean_inc(v_err_4798_);
lean_dec_ref_known(v___x_4792_, 2);
v___y_4765_ = v___y_4773_;
v_snd_4766_ = v_snd_4777_;
v_pos_4767_ = v_pos_4797_;
v_err_4768_ = v_err_4798_;
goto v___jp_4764_;
}
}
}
}
}
else
{
lean_object* v___x_4803_; 
v___x_4803_ = lean_box(0);
v___y_4765_ = v___y_4773_;
v_snd_4766_ = v_snd_4777_;
v_pos_4767_ = v_pos_4775_;
v_err_4768_ = v___x_4803_;
goto v___jp_4764_;
}
}
}
v___jp_4804_:
{
lean_object* v___x_4809_; 
lean_inc_ref(v_pos_4807_);
v___x_4809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4809_, 0, v_pos_4807_);
lean_ctor_set(v___x_4809_, 1, v_err_4808_);
v_snd_4772_ = v_snd_4805_;
v___y_4773_ = v___y_4806_;
v___y_4774_ = v___x_4809_;
v_pos_4775_ = v_pos_4807_;
goto v___jp_4771_;
}
v___jp_4811_:
{
lean_object* v_fst_4816_; lean_object* v_snd_4817_; uint8_t v_decide_4818_; 
v_fst_4816_ = lean_ctor_get(v_pos_4815_, 0);
v_snd_4817_ = lean_ctor_get(v_pos_4815_, 1);
lean_inc(v_snd_4817_);
v_decide_4818_ = lean_nat_dec_eq(v_snd_4812_, v_snd_4817_);
lean_dec(v_snd_4812_);
if (v_decide_4818_ == 0)
{
lean_dec(v_snd_4817_);
lean_dec_ref(v_pos_4815_);
lean_dec_ref(v___y_4813_);
return v___y_4814_;
}
else
{
lean_object* v___x_4819_; uint8_t v_decide_4820_; 
lean_dec_ref(v___y_4814_);
v___x_4819_ = lean_string_utf8_byte_size(v_fst_4816_);
v_decide_4820_ = lean_nat_dec_eq(v_snd_4817_, v___x_4819_);
if (v_decide_4820_ == 0)
{
uint32_t v___x_4821_; uint32_t v_c_4822_; uint8_t v___x_4823_; 
v___x_4821_ = 107;
v_c_4822_ = lean_string_utf8_get_fast(v_fst_4816_, v_snd_4817_);
v___x_4823_ = lean_uint32_dec_eq(v_c_4822_, v___x_4821_);
if (v___x_4823_ == 0)
{
lean_object* v___x_4824_; 
v___x_4824_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14___closed__1));
v_snd_4805_ = v_snd_4817_;
v___y_4806_ = v___y_4813_;
v_pos_4807_ = v_pos_4815_;
v_err_4808_ = v___x_4824_;
goto v___jp_4804_;
}
else
{
lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4840_; 
lean_inc(v_fst_4816_);
v_isSharedCheck_4840_ = !lean_is_exclusive(v_pos_4815_);
if (v_isSharedCheck_4840_ == 0)
{
lean_object* v_unused_4841_; lean_object* v_unused_4842_; 
v_unused_4841_ = lean_ctor_get(v_pos_4815_, 1);
lean_dec(v_unused_4841_);
v_unused_4842_ = lean_ctor_get(v_pos_4815_, 0);
lean_dec(v_unused_4842_);
v___x_4826_ = v_pos_4815_;
v_isShared_4827_ = v_isSharedCheck_4840_;
goto v_resetjp_4825_;
}
else
{
lean_dec(v_pos_4815_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4840_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4828_; lean_object* v_it_x27_4830_; 
v___x_4828_ = lean_string_utf8_next_fast(v_fst_4816_, v_snd_4817_);
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 1, v___x_4828_);
v_it_x27_4830_ = v___x_4826_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_fst_4816_);
lean_ctor_set(v_reuseFailAlloc_4839_, 1, v___x_4828_);
v_it_x27_4830_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4831_ = ((lean_object*)(l_Std_Time_parseModifier___closed__28));
v___x_4832_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__14(v___x_4831_, v_it_x27_4830_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_pos_4833_; lean_object* v_res_4834_; lean_object* v___x_4835_; 
v_pos_4833_ = lean_ctor_get(v___x_4832_, 0);
lean_inc(v_pos_4833_);
v_res_4834_ = lean_ctor_get(v___x_4832_, 1);
lean_inc(v_res_4834_);
lean_dec_ref_known(v___x_4832_, 2);
lean_inc_ref(v___y_4813_);
v___x_4835_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4810_, v___y_4813_, v_res_4834_, v_pos_4833_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_dec(v_snd_4817_);
lean_dec_ref(v___y_4813_);
return v___x_4835_;
}
else
{
lean_object* v_pos_4836_; 
v_pos_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_pos_4836_);
v_snd_4772_ = v_snd_4817_;
v___y_4773_ = v___y_4813_;
v___y_4774_ = v___x_4835_;
v_pos_4775_ = v_pos_4836_;
goto v___jp_4771_;
}
}
else
{
lean_object* v_pos_4837_; lean_object* v_err_4838_; 
v_pos_4837_ = lean_ctor_get(v___x_4832_, 0);
lean_inc(v_pos_4837_);
v_err_4838_ = lean_ctor_get(v___x_4832_, 1);
lean_inc(v_err_4838_);
lean_dec_ref_known(v___x_4832_, 2);
v_snd_4805_ = v_snd_4817_;
v___y_4806_ = v___y_4813_;
v_pos_4807_ = v_pos_4837_;
v_err_4808_ = v_err_4838_;
goto v___jp_4804_;
}
}
}
}
}
else
{
lean_object* v___x_4843_; 
v___x_4843_ = lean_box(0);
v_snd_4805_ = v_snd_4817_;
v___y_4806_ = v___y_4813_;
v_pos_4807_ = v_pos_4815_;
v_err_4808_ = v___x_4843_;
goto v___jp_4804_;
}
}
}
v___jp_4844_:
{
lean_object* v___x_4849_; 
lean_inc_ref(v_pos_4847_);
v___x_4849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4849_, 0, v_pos_4847_);
lean_ctor_set(v___x_4849_, 1, v_err_4848_);
v_snd_4812_ = v_snd_4845_;
v___y_4813_ = v___y_4846_;
v___y_4814_ = v___x_4849_;
v_pos_4815_ = v_pos_4847_;
goto v___jp_4811_;
}
v___jp_4851_:
{
lean_object* v_fst_4856_; lean_object* v_snd_4857_; uint8_t v_decide_4858_; 
v_fst_4856_ = lean_ctor_get(v_pos_4855_, 0);
v_snd_4857_ = lean_ctor_get(v_pos_4855_, 1);
lean_inc(v_snd_4857_);
v_decide_4858_ = lean_nat_dec_eq(v_snd_4853_, v_snd_4857_);
lean_dec(v_snd_4853_);
if (v_decide_4858_ == 0)
{
lean_dec(v_snd_4857_);
lean_dec_ref(v_pos_4855_);
lean_dec_ref(v___y_4852_);
return v___y_4854_;
}
else
{
lean_object* v___x_4859_; uint8_t v_decide_4860_; 
lean_dec_ref(v___y_4854_);
v___x_4859_ = lean_string_utf8_byte_size(v_fst_4856_);
v_decide_4860_ = lean_nat_dec_eq(v_snd_4857_, v___x_4859_);
if (v_decide_4860_ == 0)
{
uint32_t v___x_4861_; uint32_t v_c_4862_; uint8_t v___x_4863_; 
v___x_4861_ = 75;
v_c_4862_ = lean_string_utf8_get_fast(v_fst_4856_, v_snd_4857_);
v___x_4863_ = lean_uint32_dec_eq(v_c_4862_, v___x_4861_);
if (v___x_4863_ == 0)
{
lean_object* v___x_4864_; 
v___x_4864_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15___closed__1));
v_snd_4845_ = v_snd_4857_;
v___y_4846_ = v___y_4852_;
v_pos_4847_ = v_pos_4855_;
v_err_4848_ = v___x_4864_;
goto v___jp_4844_;
}
else
{
lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4880_; 
lean_inc(v_fst_4856_);
v_isSharedCheck_4880_ = !lean_is_exclusive(v_pos_4855_);
if (v_isSharedCheck_4880_ == 0)
{
lean_object* v_unused_4881_; lean_object* v_unused_4882_; 
v_unused_4881_ = lean_ctor_get(v_pos_4855_, 1);
lean_dec(v_unused_4881_);
v_unused_4882_ = lean_ctor_get(v_pos_4855_, 0);
lean_dec(v_unused_4882_);
v___x_4866_ = v_pos_4855_;
v_isShared_4867_ = v_isSharedCheck_4880_;
goto v_resetjp_4865_;
}
else
{
lean_dec(v_pos_4855_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4880_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4868_; lean_object* v_it_x27_4870_; 
v___x_4868_ = lean_string_utf8_next_fast(v_fst_4856_, v_snd_4857_);
if (v_isShared_4867_ == 0)
{
lean_ctor_set(v___x_4866_, 1, v___x_4868_);
v_it_x27_4870_ = v___x_4866_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_fst_4856_);
lean_ctor_set(v_reuseFailAlloc_4879_, 1, v___x_4868_);
v_it_x27_4870_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = ((lean_object*)(l_Std_Time_parseModifier___closed__30));
v___x_4872_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__15(v___x_4871_, v_it_x27_4870_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_pos_4873_; lean_object* v_res_4874_; lean_object* v___x_4875_; 
v_pos_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_pos_4873_);
v_res_4874_ = lean_ctor_get(v___x_4872_, 1);
lean_inc(v_res_4874_);
lean_dec_ref_known(v___x_4872_, 2);
lean_inc_ref(v___y_4852_);
v___x_4875_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4850_, v___y_4852_, v_res_4874_, v_pos_4873_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_dec(v_snd_4857_);
lean_dec_ref(v___y_4852_);
return v___x_4875_;
}
else
{
lean_object* v_pos_4876_; 
v_pos_4876_ = lean_ctor_get(v___x_4875_, 0);
lean_inc(v_pos_4876_);
v_snd_4812_ = v_snd_4857_;
v___y_4813_ = v___y_4852_;
v___y_4814_ = v___x_4875_;
v_pos_4815_ = v_pos_4876_;
goto v___jp_4811_;
}
}
else
{
lean_object* v_pos_4877_; lean_object* v_err_4878_; 
v_pos_4877_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_pos_4877_);
v_err_4878_ = lean_ctor_get(v___x_4872_, 1);
lean_inc(v_err_4878_);
lean_dec_ref_known(v___x_4872_, 2);
v_snd_4845_ = v_snd_4857_;
v___y_4846_ = v___y_4852_;
v_pos_4847_ = v_pos_4877_;
v_err_4848_ = v_err_4878_;
goto v___jp_4844_;
}
}
}
}
}
else
{
lean_object* v___x_4883_; 
v___x_4883_ = lean_box(0);
v_snd_4845_ = v_snd_4857_;
v___y_4846_ = v___y_4852_;
v_pos_4847_ = v_pos_4855_;
v_err_4848_ = v___x_4883_;
goto v___jp_4844_;
}
}
}
v___jp_4884_:
{
lean_object* v___x_4889_; 
lean_inc_ref(v_pos_4887_);
v___x_4889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4889_, 0, v_pos_4887_);
lean_ctor_set(v___x_4889_, 1, v_err_4888_);
v___y_4852_ = v___y_4885_;
v_snd_4853_ = v_snd_4886_;
v___y_4854_ = v___x_4889_;
v_pos_4855_ = v_pos_4887_;
goto v___jp_4851_;
}
v___jp_4891_:
{
lean_object* v_fst_4896_; lean_object* v_snd_4897_; uint8_t v_decide_4898_; 
v_fst_4896_ = lean_ctor_get(v_pos_4895_, 0);
v_snd_4897_ = lean_ctor_get(v_pos_4895_, 1);
lean_inc(v_snd_4897_);
v_decide_4898_ = lean_nat_dec_eq(v_snd_4892_, v_snd_4897_);
lean_dec(v_snd_4892_);
if (v_decide_4898_ == 0)
{
lean_dec(v_snd_4897_);
lean_dec_ref(v_pos_4895_);
lean_dec_ref(v___y_4893_);
return v___y_4894_;
}
else
{
lean_object* v___x_4899_; uint8_t v_decide_4900_; 
lean_dec_ref(v___y_4894_);
v___x_4899_ = lean_string_utf8_byte_size(v_fst_4896_);
v_decide_4900_ = lean_nat_dec_eq(v_snd_4897_, v___x_4899_);
if (v_decide_4900_ == 0)
{
uint32_t v___x_4901_; uint32_t v_c_4902_; uint8_t v___x_4903_; 
v___x_4901_ = 104;
v_c_4902_ = lean_string_utf8_get_fast(v_fst_4896_, v_snd_4897_);
v___x_4903_ = lean_uint32_dec_eq(v_c_4902_, v___x_4901_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; 
v___x_4904_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16___closed__1));
v___y_4885_ = v___y_4893_;
v_snd_4886_ = v_snd_4897_;
v_pos_4887_ = v_pos_4895_;
v_err_4888_ = v___x_4904_;
goto v___jp_4884_;
}
else
{
lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4920_; 
lean_inc(v_fst_4896_);
v_isSharedCheck_4920_ = !lean_is_exclusive(v_pos_4895_);
if (v_isSharedCheck_4920_ == 0)
{
lean_object* v_unused_4921_; lean_object* v_unused_4922_; 
v_unused_4921_ = lean_ctor_get(v_pos_4895_, 1);
lean_dec(v_unused_4921_);
v_unused_4922_ = lean_ctor_get(v_pos_4895_, 0);
lean_dec(v_unused_4922_);
v___x_4906_ = v_pos_4895_;
v_isShared_4907_ = v_isSharedCheck_4920_;
goto v_resetjp_4905_;
}
else
{
lean_dec(v_pos_4895_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4920_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v___x_4908_; lean_object* v_it_x27_4910_; 
v___x_4908_ = lean_string_utf8_next_fast(v_fst_4896_, v_snd_4897_);
if (v_isShared_4907_ == 0)
{
lean_ctor_set(v___x_4906_, 1, v___x_4908_);
v_it_x27_4910_ = v___x_4906_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_fst_4896_);
lean_ctor_set(v_reuseFailAlloc_4919_, 1, v___x_4908_);
v_it_x27_4910_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4911_ = ((lean_object*)(l_Std_Time_parseModifier___closed__32));
v___x_4912_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__16(v___x_4911_, v_it_x27_4910_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_pos_4913_; lean_object* v_res_4914_; lean_object* v___x_4915_; 
v_pos_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_pos_4913_);
v_res_4914_ = lean_ctor_get(v___x_4912_, 1);
lean_inc(v_res_4914_);
lean_dec_ref_known(v___x_4912_, 2);
lean_inc_ref(v___y_4893_);
v___x_4915_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_4890_, v___y_4893_, v_res_4914_, v_pos_4913_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_dec(v_snd_4897_);
lean_dec_ref(v___y_4893_);
return v___x_4915_;
}
else
{
lean_object* v_pos_4916_; 
v_pos_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_pos_4916_);
v___y_4852_ = v___y_4893_;
v_snd_4853_ = v_snd_4897_;
v___y_4854_ = v___x_4915_;
v_pos_4855_ = v_pos_4916_;
goto v___jp_4851_;
}
}
else
{
lean_object* v_pos_4917_; lean_object* v_err_4918_; 
v_pos_4917_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_pos_4917_);
v_err_4918_ = lean_ctor_get(v___x_4912_, 1);
lean_inc(v_err_4918_);
lean_dec_ref_known(v___x_4912_, 2);
v___y_4885_ = v___y_4893_;
v_snd_4886_ = v_snd_4897_;
v_pos_4887_ = v_pos_4917_;
v_err_4888_ = v_err_4918_;
goto v___jp_4884_;
}
}
}
}
}
else
{
lean_object* v___x_4923_; 
v___x_4923_ = lean_box(0);
v___y_4885_ = v___y_4893_;
v_snd_4886_ = v_snd_4897_;
v_pos_4887_ = v_pos_4895_;
v_err_4888_ = v___x_4923_;
goto v___jp_4884_;
}
}
}
v___jp_4924_:
{
lean_object* v___x_4929_; 
lean_inc_ref(v_pos_4927_);
v___x_4929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4929_, 0, v_pos_4927_);
lean_ctor_set(v___x_4929_, 1, v_err_4928_);
v_snd_4892_ = v_snd_4925_;
v___y_4893_ = v___y_4926_;
v___y_4894_ = v___x_4929_;
v_pos_4895_ = v_pos_4927_;
goto v___jp_4891_;
}
v___jp_4930_:
{
lean_object* v_fst_4935_; lean_object* v_snd_4936_; uint8_t v_decide_4937_; 
v_fst_4935_ = lean_ctor_get(v_pos_4934_, 0);
v_snd_4936_ = lean_ctor_get(v_pos_4934_, 1);
lean_inc(v_snd_4936_);
v_decide_4937_ = lean_nat_dec_eq(v_snd_4932_, v_snd_4936_);
lean_dec(v_snd_4932_);
if (v_decide_4937_ == 0)
{
lean_dec(v_snd_4936_);
lean_dec_ref(v_pos_4934_);
lean_dec_ref(v___y_4931_);
return v___y_4933_;
}
else
{
lean_object* v___x_4938_; uint8_t v_decide_4939_; 
lean_dec_ref(v___y_4933_);
v___x_4938_ = lean_string_utf8_byte_size(v_fst_4935_);
v_decide_4939_ = lean_nat_dec_eq(v_snd_4936_, v___x_4938_);
if (v_decide_4939_ == 0)
{
uint32_t v___x_4940_; uint32_t v_c_4941_; uint8_t v___x_4942_; 
v___x_4940_ = 66;
v_c_4941_ = lean_string_utf8_get_fast(v_fst_4935_, v_snd_4936_);
v___x_4942_ = lean_uint32_dec_eq(v_c_4941_, v___x_4940_);
if (v___x_4942_ == 0)
{
lean_object* v___x_4943_; 
v___x_4943_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17___closed__1));
v_snd_4925_ = v_snd_4936_;
v___y_4926_ = v___y_4931_;
v_pos_4927_ = v_pos_4934_;
v_err_4928_ = v___x_4943_;
goto v___jp_4924_;
}
else
{
lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4959_; 
lean_inc(v_fst_4935_);
v_isSharedCheck_4959_ = !lean_is_exclusive(v_pos_4934_);
if (v_isSharedCheck_4959_ == 0)
{
lean_object* v_unused_4960_; lean_object* v_unused_4961_; 
v_unused_4960_ = lean_ctor_get(v_pos_4934_, 1);
lean_dec(v_unused_4960_);
v_unused_4961_ = lean_ctor_get(v_pos_4934_, 0);
lean_dec(v_unused_4961_);
v___x_4945_ = v_pos_4934_;
v_isShared_4946_ = v_isSharedCheck_4959_;
goto v_resetjp_4944_;
}
else
{
lean_dec(v_pos_4934_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4959_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4947_; lean_object* v_it_x27_4949_; 
v___x_4947_ = lean_string_utf8_next_fast(v_fst_4935_, v_snd_4936_);
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 1, v___x_4947_);
v_it_x27_4949_ = v___x_4945_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_fst_4935_);
lean_ctor_set(v_reuseFailAlloc_4958_, 1, v___x_4947_);
v_it_x27_4949_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; 
v___x_4950_ = ((lean_object*)(l_Std_Time_parseModifier___closed__33));
v___x_4951_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__17(v___x_4950_, v_it_x27_4949_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_object* v_pos_4952_; lean_object* v_res_4953_; lean_object* v___x_4954_; 
v_pos_4952_ = lean_ctor_get(v___x_4951_, 0);
lean_inc(v_pos_4952_);
v_res_4953_ = lean_ctor_get(v___x_4951_, 1);
lean_inc(v_res_4953_);
lean_dec_ref_known(v___x_4951_, 2);
v___x_4954_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseBPeriod(v_res_4953_, v_pos_4952_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_dec(v_snd_4936_);
lean_dec_ref(v___y_4931_);
return v___x_4954_;
}
else
{
lean_object* v_pos_4955_; 
v_pos_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_pos_4955_);
v_snd_4892_ = v_snd_4936_;
v___y_4893_ = v___y_4931_;
v___y_4894_ = v___x_4954_;
v_pos_4895_ = v_pos_4955_;
goto v___jp_4891_;
}
}
else
{
lean_object* v_pos_4956_; lean_object* v_err_4957_; 
v_pos_4956_ = lean_ctor_get(v___x_4951_, 0);
lean_inc(v_pos_4956_);
v_err_4957_ = lean_ctor_get(v___x_4951_, 1);
lean_inc(v_err_4957_);
lean_dec_ref_known(v___x_4951_, 2);
v_snd_4925_ = v_snd_4936_;
v___y_4926_ = v___y_4931_;
v_pos_4927_ = v_pos_4956_;
v_err_4928_ = v_err_4957_;
goto v___jp_4924_;
}
}
}
}
}
else
{
lean_object* v___x_4962_; 
v___x_4962_ = lean_box(0);
v_snd_4925_ = v_snd_4936_;
v___y_4926_ = v___y_4931_;
v_pos_4927_ = v_pos_4934_;
v_err_4928_ = v___x_4962_;
goto v___jp_4924_;
}
}
}
v___jp_4963_:
{
lean_object* v___x_4968_; 
lean_inc_ref(v_pos_4966_);
v___x_4968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4968_, 0, v_pos_4966_);
lean_ctor_set(v___x_4968_, 1, v_err_4967_);
v___y_4931_ = v___y_4964_;
v_snd_4932_ = v_snd_4965_;
v___y_4933_ = v___x_4968_;
v_pos_4934_ = v_pos_4966_;
goto v___jp_4930_;
}
v___jp_4969_:
{
lean_object* v_fst_4974_; lean_object* v_snd_4975_; uint8_t v_decide_4976_; 
v_fst_4974_ = lean_ctor_get(v_pos_4973_, 0);
v_snd_4975_ = lean_ctor_get(v_pos_4973_, 1);
lean_inc(v_snd_4975_);
v_decide_4976_ = lean_nat_dec_eq(v_snd_4971_, v_snd_4975_);
lean_dec(v_snd_4971_);
if (v_decide_4976_ == 0)
{
lean_dec(v_snd_4975_);
lean_dec_ref(v_pos_4973_);
lean_dec_ref(v___y_4970_);
return v___y_4972_;
}
else
{
lean_object* v___x_4977_; uint8_t v_decide_4978_; 
lean_dec_ref(v___y_4972_);
v___x_4977_ = lean_string_utf8_byte_size(v_fst_4974_);
v_decide_4978_ = lean_nat_dec_eq(v_snd_4975_, v___x_4977_);
if (v_decide_4978_ == 0)
{
uint32_t v___x_4979_; uint32_t v_c_4980_; uint8_t v___x_4981_; 
v___x_4979_ = 98;
v_c_4980_ = lean_string_utf8_get_fast(v_fst_4974_, v_snd_4975_);
v___x_4981_ = lean_uint32_dec_eq(v_c_4980_, v___x_4979_);
if (v___x_4981_ == 0)
{
lean_object* v___x_4982_; 
v___x_4982_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18___closed__1));
v___y_4964_ = v___y_4970_;
v_snd_4965_ = v_snd_4975_;
v_pos_4966_ = v_pos_4973_;
v_err_4967_ = v___x_4982_;
goto v___jp_4963_;
}
else
{
lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_4998_; 
lean_inc(v_fst_4974_);
v_isSharedCheck_4998_ = !lean_is_exclusive(v_pos_4973_);
if (v_isSharedCheck_4998_ == 0)
{
lean_object* v_unused_4999_; lean_object* v_unused_5000_; 
v_unused_4999_ = lean_ctor_get(v_pos_4973_, 1);
lean_dec(v_unused_4999_);
v_unused_5000_ = lean_ctor_get(v_pos_4973_, 0);
lean_dec(v_unused_5000_);
v___x_4984_ = v_pos_4973_;
v_isShared_4985_ = v_isSharedCheck_4998_;
goto v_resetjp_4983_;
}
else
{
lean_dec(v_pos_4973_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_4998_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4986_; lean_object* v_it_x27_4988_; 
v___x_4986_ = lean_string_utf8_next_fast(v_fst_4974_, v_snd_4975_);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 1, v___x_4986_);
v_it_x27_4988_ = v___x_4984_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_fst_4974_);
lean_ctor_set(v_reuseFailAlloc_4997_, 1, v___x_4986_);
v_it_x27_4988_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4989_ = ((lean_object*)(l_Std_Time_parseModifier___closed__34));
v___x_4990_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__18(v___x_4989_, v_it_x27_4988_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_pos_4991_; lean_object* v_res_4992_; lean_object* v___x_4993_; 
v_pos_4991_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_pos_4991_);
v_res_4992_ = lean_ctor_get(v___x_4990_, 1);
lean_inc(v_res_4992_);
lean_dec_ref_known(v___x_4990_, 2);
v___x_4993_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseDayPeriod(v_res_4992_, v_pos_4991_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_dec(v_snd_4975_);
lean_dec_ref(v___y_4970_);
return v___x_4993_;
}
else
{
lean_object* v_pos_4994_; 
v_pos_4994_ = lean_ctor_get(v___x_4993_, 0);
lean_inc(v_pos_4994_);
v___y_4931_ = v___y_4970_;
v_snd_4932_ = v_snd_4975_;
v___y_4933_ = v___x_4993_;
v_pos_4934_ = v_pos_4994_;
goto v___jp_4930_;
}
}
else
{
lean_object* v_pos_4995_; lean_object* v_err_4996_; 
v_pos_4995_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_pos_4995_);
v_err_4996_ = lean_ctor_get(v___x_4990_, 1);
lean_inc(v_err_4996_);
lean_dec_ref_known(v___x_4990_, 2);
v___y_4964_ = v___y_4970_;
v_snd_4965_ = v_snd_4975_;
v_pos_4966_ = v_pos_4995_;
v_err_4967_ = v_err_4996_;
goto v___jp_4963_;
}
}
}
}
}
else
{
lean_object* v___x_5001_; 
v___x_5001_ = lean_box(0);
v___y_4964_ = v___y_4970_;
v_snd_4965_ = v_snd_4975_;
v_pos_4966_ = v_pos_4973_;
v_err_4967_ = v___x_5001_;
goto v___jp_4963_;
}
}
}
v___jp_5002_:
{
lean_object* v___x_5007_; 
lean_inc_ref(v_pos_5005_);
v___x_5007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5007_, 0, v_pos_5005_);
lean_ctor_set(v___x_5007_, 1, v_err_5006_);
v___y_4970_ = v___y_5003_;
v_snd_4971_ = v_snd_5004_;
v___y_4972_ = v___x_5007_;
v_pos_4973_ = v_pos_5005_;
goto v___jp_4969_;
}
v___jp_5008_:
{
lean_object* v_fst_5013_; lean_object* v_snd_5014_; uint8_t v_decide_5015_; 
v_fst_5013_ = lean_ctor_get(v_pos_5012_, 0);
v_snd_5014_ = lean_ctor_get(v_pos_5012_, 1);
lean_inc(v_snd_5014_);
v_decide_5015_ = lean_nat_dec_eq(v_snd_5009_, v_snd_5014_);
lean_dec(v_snd_5009_);
if (v_decide_5015_ == 0)
{
lean_dec(v_snd_5014_);
lean_dec_ref(v_pos_5012_);
lean_dec_ref(v___y_5010_);
return v___y_5011_;
}
else
{
lean_object* v___x_5016_; uint8_t v_decide_5017_; 
lean_dec_ref(v___y_5011_);
v___x_5016_ = lean_string_utf8_byte_size(v_fst_5013_);
v_decide_5017_ = lean_nat_dec_eq(v_snd_5014_, v___x_5016_);
if (v_decide_5017_ == 0)
{
uint32_t v___x_5018_; uint32_t v_c_5019_; uint8_t v___x_5020_; 
v___x_5018_ = 97;
v_c_5019_ = lean_string_utf8_get_fast(v_fst_5013_, v_snd_5014_);
v___x_5020_ = lean_uint32_dec_eq(v_c_5019_, v___x_5018_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; 
v___x_5021_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19___closed__1));
v___y_5003_ = v___y_5010_;
v_snd_5004_ = v_snd_5014_;
v_pos_5005_ = v_pos_5012_;
v_err_5006_ = v___x_5021_;
goto v___jp_5002_;
}
else
{
lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5037_; 
lean_inc(v_fst_5013_);
v_isSharedCheck_5037_ = !lean_is_exclusive(v_pos_5012_);
if (v_isSharedCheck_5037_ == 0)
{
lean_object* v_unused_5038_; lean_object* v_unused_5039_; 
v_unused_5038_ = lean_ctor_get(v_pos_5012_, 1);
lean_dec(v_unused_5038_);
v_unused_5039_ = lean_ctor_get(v_pos_5012_, 0);
lean_dec(v_unused_5039_);
v___x_5023_ = v_pos_5012_;
v_isShared_5024_ = v_isSharedCheck_5037_;
goto v_resetjp_5022_;
}
else
{
lean_dec(v_pos_5012_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5037_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5025_; lean_object* v_it_x27_5027_; 
v___x_5025_ = lean_string_utf8_next_fast(v_fst_5013_, v_snd_5014_);
if (v_isShared_5024_ == 0)
{
lean_ctor_set(v___x_5023_, 1, v___x_5025_);
v_it_x27_5027_ = v___x_5023_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_fst_5013_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v___x_5025_);
v_it_x27_5027_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5028_ = ((lean_object*)(l_Std_Time_parseModifier___closed__35));
v___x_5029_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__19(v___x_5028_, v_it_x27_5027_);
if (lean_obj_tag(v___x_5029_) == 0)
{
lean_object* v_pos_5030_; lean_object* v_res_5031_; lean_object* v___x_5032_; 
v_pos_5030_ = lean_ctor_get(v___x_5029_, 0);
lean_inc(v_pos_5030_);
v_res_5031_ = lean_ctor_get(v___x_5029_, 1);
lean_inc(v_res_5031_);
lean_dec_ref_known(v___x_5029_, 2);
v___x_5032_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseAMPM(v_res_5031_, v_pos_5030_);
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_dec(v_snd_5014_);
lean_dec_ref(v___y_5010_);
return v___x_5032_;
}
else
{
lean_object* v_pos_5033_; 
v_pos_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_pos_5033_);
v___y_4970_ = v___y_5010_;
v_snd_4971_ = v_snd_5014_;
v___y_4972_ = v___x_5032_;
v_pos_4973_ = v_pos_5033_;
goto v___jp_4969_;
}
}
else
{
lean_object* v_pos_5034_; lean_object* v_err_5035_; 
v_pos_5034_ = lean_ctor_get(v___x_5029_, 0);
lean_inc(v_pos_5034_);
v_err_5035_ = lean_ctor_get(v___x_5029_, 1);
lean_inc(v_err_5035_);
lean_dec_ref_known(v___x_5029_, 2);
v___y_5003_ = v___y_5010_;
v_snd_5004_ = v_snd_5014_;
v_pos_5005_ = v_pos_5034_;
v_err_5006_ = v_err_5035_;
goto v___jp_5002_;
}
}
}
}
}
else
{
lean_object* v___x_5040_; 
v___x_5040_ = lean_box(0);
v___y_5003_ = v___y_5010_;
v_snd_5004_ = v_snd_5014_;
v_pos_5005_ = v_pos_5012_;
v_err_5006_ = v___x_5040_;
goto v___jp_5002_;
}
}
}
v___jp_5041_:
{
lean_object* v___x_5046_; 
lean_inc_ref(v_pos_5044_);
v___x_5046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5046_, 0, v_pos_5044_);
lean_ctor_set(v___x_5046_, 1, v_err_5045_);
v_snd_5009_ = v_snd_5042_;
v___y_5010_ = v___y_5043_;
v___y_5011_ = v___x_5046_;
v_pos_5012_ = v_pos_5044_;
goto v___jp_5008_;
}
v___jp_5048_:
{
lean_object* v_fst_5054_; lean_object* v_snd_5055_; uint8_t v_decide_5056_; 
v_fst_5054_ = lean_ctor_get(v_pos_5053_, 0);
v_snd_5055_ = lean_ctor_get(v_pos_5053_, 1);
lean_inc(v_snd_5055_);
v_decide_5056_ = lean_nat_dec_eq(v_snd_5049_, v_snd_5055_);
lean_dec(v_snd_5049_);
if (v_decide_5056_ == 0)
{
lean_dec(v_snd_5055_);
lean_dec_ref(v_pos_5053_);
lean_dec_ref(v___y_5051_);
lean_dec_ref(v___y_5050_);
return v___y_5052_;
}
else
{
lean_object* v___x_5057_; uint8_t v_decide_5058_; 
lean_dec_ref(v___y_5052_);
v___x_5057_ = lean_string_utf8_byte_size(v_fst_5054_);
v_decide_5058_ = lean_nat_dec_eq(v_snd_5055_, v___x_5057_);
if (v_decide_5058_ == 0)
{
uint32_t v___x_5059_; uint32_t v_c_5060_; uint8_t v___x_5061_; 
v___x_5059_ = 70;
v_c_5060_ = lean_string_utf8_get_fast(v_fst_5054_, v_snd_5055_);
v___x_5061_ = lean_uint32_dec_eq(v_c_5060_, v___x_5059_);
if (v___x_5061_ == 0)
{
lean_object* v___x_5062_; 
lean_dec_ref(v___y_5050_);
v___x_5062_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20___closed__1));
v_snd_5042_ = v_snd_5055_;
v___y_5043_ = v___y_5051_;
v_pos_5044_ = v_pos_5053_;
v_err_5045_ = v___x_5062_;
goto v___jp_5041_;
}
else
{
lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5078_; 
lean_inc(v_fst_5054_);
v_isSharedCheck_5078_ = !lean_is_exclusive(v_pos_5053_);
if (v_isSharedCheck_5078_ == 0)
{
lean_object* v_unused_5079_; lean_object* v_unused_5080_; 
v_unused_5079_ = lean_ctor_get(v_pos_5053_, 1);
lean_dec(v_unused_5079_);
v_unused_5080_ = lean_ctor_get(v_pos_5053_, 0);
lean_dec(v_unused_5080_);
v___x_5064_ = v_pos_5053_;
v_isShared_5065_ = v_isSharedCheck_5078_;
goto v_resetjp_5063_;
}
else
{
lean_dec(v_pos_5053_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5078_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5066_; lean_object* v_it_x27_5068_; 
v___x_5066_ = lean_string_utf8_next_fast(v_fst_5054_, v_snd_5055_);
if (v_isShared_5065_ == 0)
{
lean_ctor_set(v___x_5064_, 1, v___x_5066_);
v_it_x27_5068_ = v___x_5064_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_fst_5054_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v___x_5066_);
v_it_x27_5068_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5069_ = ((lean_object*)(l_Std_Time_parseModifier___closed__37));
v___x_5070_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__20(v___x_5069_, v_it_x27_5068_);
if (lean_obj_tag(v___x_5070_) == 0)
{
lean_object* v_pos_5071_; lean_object* v_res_5072_; lean_object* v___x_5073_; 
v_pos_5071_ = lean_ctor_get(v___x_5070_, 0);
lean_inc(v_pos_5071_);
v_res_5072_ = lean_ctor_get(v___x_5070_, 1);
lean_inc(v_res_5072_);
lean_dec_ref_known(v___x_5070_, 2);
v___x_5073_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5047_, v___y_5050_, v_res_5072_, v_pos_5071_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_dec(v_snd_5055_);
lean_dec_ref(v___y_5051_);
return v___x_5073_;
}
else
{
lean_object* v_pos_5074_; 
v_pos_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_pos_5074_);
v_snd_5009_ = v_snd_5055_;
v___y_5010_ = v___y_5051_;
v___y_5011_ = v___x_5073_;
v_pos_5012_ = v_pos_5074_;
goto v___jp_5008_;
}
}
else
{
lean_object* v_pos_5075_; lean_object* v_err_5076_; 
lean_dec_ref(v___y_5050_);
v_pos_5075_ = lean_ctor_get(v___x_5070_, 0);
lean_inc(v_pos_5075_);
v_err_5076_ = lean_ctor_get(v___x_5070_, 1);
lean_inc(v_err_5076_);
lean_dec_ref_known(v___x_5070_, 2);
v_snd_5042_ = v_snd_5055_;
v___y_5043_ = v___y_5051_;
v_pos_5044_ = v_pos_5075_;
v_err_5045_ = v_err_5076_;
goto v___jp_5041_;
}
}
}
}
}
else
{
lean_object* v___x_5081_; 
lean_dec_ref(v___y_5050_);
v___x_5081_ = lean_box(0);
v_snd_5042_ = v_snd_5055_;
v___y_5043_ = v___y_5051_;
v_pos_5044_ = v_pos_5053_;
v_err_5045_ = v___x_5081_;
goto v___jp_5041_;
}
}
}
v___jp_5082_:
{
lean_object* v___x_5088_; 
lean_inc_ref(v_pos_5086_);
v___x_5088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5088_, 0, v_pos_5086_);
lean_ctor_set(v___x_5088_, 1, v_err_5087_);
v_snd_5049_ = v_snd_5083_;
v___y_5050_ = v___y_5084_;
v___y_5051_ = v___y_5085_;
v___y_5052_ = v___x_5088_;
v_pos_5053_ = v_pos_5086_;
goto v___jp_5048_;
}
v___jp_5090_:
{
lean_object* v_fst_5096_; lean_object* v_snd_5097_; uint8_t v_decide_5098_; 
v_fst_5096_ = lean_ctor_get(v_pos_5095_, 0);
v_snd_5097_ = lean_ctor_get(v_pos_5095_, 1);
lean_inc(v_snd_5097_);
v_decide_5098_ = lean_nat_dec_eq(v_snd_5093_, v_snd_5097_);
lean_dec(v_snd_5093_);
if (v_decide_5098_ == 0)
{
lean_dec(v_snd_5097_);
lean_dec_ref(v_pos_5095_);
lean_dec_ref(v___y_5092_);
lean_dec_ref(v___y_5091_);
return v___y_5094_;
}
else
{
lean_object* v___x_5099_; uint8_t v_decide_5100_; 
lean_dec_ref(v___y_5094_);
v___x_5099_ = lean_string_utf8_byte_size(v_fst_5096_);
v_decide_5100_ = lean_nat_dec_eq(v_snd_5097_, v___x_5099_);
if (v_decide_5100_ == 0)
{
uint32_t v___x_5101_; uint32_t v_c_5102_; uint8_t v___x_5103_; 
v___x_5101_ = 99;
v_c_5102_ = lean_string_utf8_get_fast(v_fst_5096_, v_snd_5097_);
v___x_5103_ = lean_uint32_dec_eq(v_c_5102_, v___x_5101_);
if (v___x_5103_ == 0)
{
lean_object* v___x_5104_; 
v___x_5104_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21___closed__1));
v_snd_5083_ = v_snd_5097_;
v___y_5084_ = v___y_5091_;
v___y_5085_ = v___y_5092_;
v_pos_5086_ = v_pos_5095_;
v_err_5087_ = v___x_5104_;
goto v___jp_5082_;
}
else
{
lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5120_; 
lean_inc(v_fst_5096_);
v_isSharedCheck_5120_ = !lean_is_exclusive(v_pos_5095_);
if (v_isSharedCheck_5120_ == 0)
{
lean_object* v_unused_5121_; lean_object* v_unused_5122_; 
v_unused_5121_ = lean_ctor_get(v_pos_5095_, 1);
lean_dec(v_unused_5121_);
v_unused_5122_ = lean_ctor_get(v_pos_5095_, 0);
lean_dec(v_unused_5122_);
v___x_5106_ = v_pos_5095_;
v_isShared_5107_ = v_isSharedCheck_5120_;
goto v_resetjp_5105_;
}
else
{
lean_dec(v_pos_5095_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5120_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5108_; lean_object* v_it_x27_5110_; 
v___x_5108_ = lean_string_utf8_next_fast(v_fst_5096_, v_snd_5097_);
if (v_isShared_5107_ == 0)
{
lean_ctor_set(v___x_5106_, 1, v___x_5108_);
v_it_x27_5110_ = v___x_5106_;
goto v_reusejp_5109_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_fst_5096_);
lean_ctor_set(v_reuseFailAlloc_5119_, 1, v___x_5108_);
v_it_x27_5110_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5109_;
}
v_reusejp_5109_:
{
lean_object* v___x_5111_; lean_object* v___x_5112_; 
v___x_5111_ = ((lean_object*)(l_Std_Time_parseModifier___closed__39));
v___x_5112_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__21(v___x_5111_, v_it_x27_5110_);
if (lean_obj_tag(v___x_5112_) == 0)
{
lean_object* v_pos_5113_; lean_object* v_res_5114_; lean_object* v___x_5115_; 
v_pos_5113_ = lean_ctor_get(v___x_5112_, 0);
lean_inc(v_pos_5113_);
v_res_5114_ = lean_ctor_get(v___x_5112_, 1);
lean_inc(v_res_5114_);
lean_dec_ref_known(v___x_5112_, 2);
v___x_5115_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseStandaloneWeekdayNumberText(v___f_5089_, v_res_5114_, v_pos_5113_);
if (lean_obj_tag(v___x_5115_) == 0)
{
lean_dec(v_snd_5097_);
lean_dec_ref(v___y_5092_);
lean_dec_ref(v___y_5091_);
return v___x_5115_;
}
else
{
lean_object* v_pos_5116_; 
v_pos_5116_ = lean_ctor_get(v___x_5115_, 0);
lean_inc(v_pos_5116_);
v_snd_5049_ = v_snd_5097_;
v___y_5050_ = v___y_5091_;
v___y_5051_ = v___y_5092_;
v___y_5052_ = v___x_5115_;
v_pos_5053_ = v_pos_5116_;
goto v___jp_5048_;
}
}
else
{
lean_object* v_pos_5117_; lean_object* v_err_5118_; 
v_pos_5117_ = lean_ctor_get(v___x_5112_, 0);
lean_inc(v_pos_5117_);
v_err_5118_ = lean_ctor_get(v___x_5112_, 1);
lean_inc(v_err_5118_);
lean_dec_ref_known(v___x_5112_, 2);
v_snd_5083_ = v_snd_5097_;
v___y_5084_ = v___y_5091_;
v___y_5085_ = v___y_5092_;
v_pos_5086_ = v_pos_5117_;
v_err_5087_ = v_err_5118_;
goto v___jp_5082_;
}
}
}
}
}
else
{
lean_object* v___x_5123_; 
v___x_5123_ = lean_box(0);
v_snd_5083_ = v_snd_5097_;
v___y_5084_ = v___y_5091_;
v___y_5085_ = v___y_5092_;
v_pos_5086_ = v_pos_5095_;
v_err_5087_ = v___x_5123_;
goto v___jp_5082_;
}
}
}
v___jp_5124_:
{
lean_object* v___x_5130_; 
lean_inc_ref(v_pos_5128_);
v___x_5130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5130_, 0, v_pos_5128_);
lean_ctor_set(v___x_5130_, 1, v_err_5129_);
v___y_5091_ = v___y_5125_;
v___y_5092_ = v___y_5126_;
v_snd_5093_ = v_snd_5127_;
v___y_5094_ = v___x_5130_;
v_pos_5095_ = v_pos_5128_;
goto v___jp_5090_;
}
v___jp_5132_:
{
lean_object* v_fst_5138_; lean_object* v_snd_5139_; uint8_t v_decide_5140_; 
v_fst_5138_ = lean_ctor_get(v_pos_5137_, 0);
v_snd_5139_ = lean_ctor_get(v_pos_5137_, 1);
lean_inc(v_snd_5139_);
v_decide_5140_ = lean_nat_dec_eq(v_snd_5133_, v_snd_5139_);
lean_dec(v_snd_5133_);
if (v_decide_5140_ == 0)
{
lean_dec(v_snd_5139_);
lean_dec_ref(v_pos_5137_);
lean_dec_ref(v___y_5135_);
lean_dec_ref(v___y_5134_);
return v___y_5136_;
}
else
{
lean_object* v___x_5141_; uint8_t v_decide_5142_; 
lean_dec_ref(v___y_5136_);
v___x_5141_ = lean_string_utf8_byte_size(v_fst_5138_);
v_decide_5142_ = lean_nat_dec_eq(v_snd_5139_, v___x_5141_);
if (v_decide_5142_ == 0)
{
uint32_t v___x_5143_; uint32_t v_c_5144_; uint8_t v___x_5145_; 
v___x_5143_ = 101;
v_c_5144_ = lean_string_utf8_get_fast(v_fst_5138_, v_snd_5139_);
v___x_5145_ = lean_uint32_dec_eq(v_c_5144_, v___x_5143_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; 
v___x_5146_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22___closed__1));
v___y_5125_ = v___y_5134_;
v___y_5126_ = v___y_5135_;
v_snd_5127_ = v_snd_5139_;
v_pos_5128_ = v_pos_5137_;
v_err_5129_ = v___x_5146_;
goto v___jp_5124_;
}
else
{
lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5162_; 
lean_inc(v_fst_5138_);
v_isSharedCheck_5162_ = !lean_is_exclusive(v_pos_5137_);
if (v_isSharedCheck_5162_ == 0)
{
lean_object* v_unused_5163_; lean_object* v_unused_5164_; 
v_unused_5163_ = lean_ctor_get(v_pos_5137_, 1);
lean_dec(v_unused_5163_);
v_unused_5164_ = lean_ctor_get(v_pos_5137_, 0);
lean_dec(v_unused_5164_);
v___x_5148_ = v_pos_5137_;
v_isShared_5149_ = v_isSharedCheck_5162_;
goto v_resetjp_5147_;
}
else
{
lean_dec(v_pos_5137_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5162_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5150_; lean_object* v_it_x27_5152_; 
v___x_5150_ = lean_string_utf8_next_fast(v_fst_5138_, v_snd_5139_);
if (v_isShared_5149_ == 0)
{
lean_ctor_set(v___x_5148_, 1, v___x_5150_);
v_it_x27_5152_ = v___x_5148_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_fst_5138_);
lean_ctor_set(v_reuseFailAlloc_5161_, 1, v___x_5150_);
v_it_x27_5152_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; 
v___x_5153_ = ((lean_object*)(l_Std_Time_parseModifier___closed__41));
v___x_5154_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__22(v___x_5153_, v_it_x27_5152_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_pos_5155_; lean_object* v_res_5156_; lean_object* v___x_5157_; 
v_pos_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_pos_5155_);
v_res_5156_ = lean_ctor_get(v___x_5154_, 1);
lean_inc(v_res_5156_);
lean_dec_ref_known(v___x_5154_, 2);
v___x_5157_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayNumberText(v___f_5131_, v_res_5156_, v_pos_5155_);
if (lean_obj_tag(v___x_5157_) == 0)
{
lean_dec(v_snd_5139_);
lean_dec_ref(v___y_5135_);
lean_dec_ref(v___y_5134_);
return v___x_5157_;
}
else
{
lean_object* v_pos_5158_; 
v_pos_5158_ = lean_ctor_get(v___x_5157_, 0);
lean_inc(v_pos_5158_);
v___y_5091_ = v___y_5134_;
v___y_5092_ = v___y_5135_;
v_snd_5093_ = v_snd_5139_;
v___y_5094_ = v___x_5157_;
v_pos_5095_ = v_pos_5158_;
goto v___jp_5090_;
}
}
else
{
lean_object* v_pos_5159_; lean_object* v_err_5160_; 
v_pos_5159_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_pos_5159_);
v_err_5160_ = lean_ctor_get(v___x_5154_, 1);
lean_inc(v_err_5160_);
lean_dec_ref_known(v___x_5154_, 2);
v___y_5125_ = v___y_5134_;
v___y_5126_ = v___y_5135_;
v_snd_5127_ = v_snd_5139_;
v_pos_5128_ = v_pos_5159_;
v_err_5129_ = v_err_5160_;
goto v___jp_5124_;
}
}
}
}
}
else
{
lean_object* v___x_5165_; 
v___x_5165_ = lean_box(0);
v___y_5125_ = v___y_5134_;
v___y_5126_ = v___y_5135_;
v_snd_5127_ = v_snd_5139_;
v_pos_5128_ = v_pos_5137_;
v_err_5129_ = v___x_5165_;
goto v___jp_5124_;
}
}
}
v___jp_5166_:
{
lean_object* v___x_5172_; 
lean_inc_ref(v_pos_5170_);
v___x_5172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5172_, 0, v_pos_5170_);
lean_ctor_set(v___x_5172_, 1, v_err_5171_);
v_snd_5133_ = v_snd_5167_;
v___y_5134_ = v___y_5168_;
v___y_5135_ = v___y_5169_;
v___y_5136_ = v___x_5172_;
v_pos_5137_ = v_pos_5170_;
goto v___jp_5132_;
}
v___jp_5174_:
{
lean_object* v_fst_5180_; lean_object* v_snd_5181_; uint8_t v_decide_5182_; 
v_fst_5180_ = lean_ctor_get(v_pos_5179_, 0);
v_snd_5181_ = lean_ctor_get(v_pos_5179_, 1);
lean_inc(v_snd_5181_);
v_decide_5182_ = lean_nat_dec_eq(v___y_5177_, v_snd_5181_);
lean_dec(v___y_5177_);
if (v_decide_5182_ == 0)
{
lean_dec(v_snd_5181_);
lean_dec_ref(v_pos_5179_);
lean_dec_ref(v___y_5176_);
lean_dec_ref(v___y_5175_);
return v___y_5178_;
}
else
{
lean_object* v___x_5183_; uint8_t v_decide_5184_; 
lean_dec_ref(v___y_5178_);
v___x_5183_ = lean_string_utf8_byte_size(v_fst_5180_);
v_decide_5184_ = lean_nat_dec_eq(v_snd_5181_, v___x_5183_);
if (v_decide_5184_ == 0)
{
uint32_t v___x_5185_; uint32_t v_c_5186_; uint8_t v___x_5187_; 
v___x_5185_ = 69;
v_c_5186_ = lean_string_utf8_get_fast(v_fst_5180_, v_snd_5181_);
v___x_5187_ = lean_uint32_dec_eq(v_c_5186_, v___x_5185_);
if (v___x_5187_ == 0)
{
lean_object* v___x_5188_; 
v___x_5188_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23___closed__1));
v_snd_5167_ = v_snd_5181_;
v___y_5168_ = v___y_5175_;
v___y_5169_ = v___y_5176_;
v_pos_5170_ = v_pos_5179_;
v_err_5171_ = v___x_5188_;
goto v___jp_5166_;
}
else
{
lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5204_; 
lean_inc(v_fst_5180_);
v_isSharedCheck_5204_ = !lean_is_exclusive(v_pos_5179_);
if (v_isSharedCheck_5204_ == 0)
{
lean_object* v_unused_5205_; lean_object* v_unused_5206_; 
v_unused_5205_ = lean_ctor_get(v_pos_5179_, 1);
lean_dec(v_unused_5205_);
v_unused_5206_ = lean_ctor_get(v_pos_5179_, 0);
lean_dec(v_unused_5206_);
v___x_5190_ = v_pos_5179_;
v_isShared_5191_ = v_isSharedCheck_5204_;
goto v_resetjp_5189_;
}
else
{
lean_dec(v_pos_5179_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5204_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5192_; lean_object* v_it_x27_5194_; 
v___x_5192_ = lean_string_utf8_next_fast(v_fst_5180_, v_snd_5181_);
if (v_isShared_5191_ == 0)
{
lean_ctor_set(v___x_5190_, 1, v___x_5192_);
v_it_x27_5194_ = v___x_5190_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_fst_5180_);
lean_ctor_set(v_reuseFailAlloc_5203_, 1, v___x_5192_);
v_it_x27_5194_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
lean_object* v___x_5195_; lean_object* v___x_5196_; 
v___x_5195_ = ((lean_object*)(l_Std_Time_parseModifier___closed__43));
v___x_5196_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__23(v___x_5195_, v_it_x27_5194_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v_pos_5197_; lean_object* v_res_5198_; lean_object* v___x_5199_; 
v_pos_5197_ = lean_ctor_get(v___x_5196_, 0);
lean_inc(v_pos_5197_);
v_res_5198_ = lean_ctor_get(v___x_5196_, 1);
lean_inc(v_res_5198_);
lean_dec_ref_known(v___x_5196_, 2);
v___x_5199_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseWeekdayText(v___f_5173_, v_res_5198_, v_pos_5197_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_dec(v_snd_5181_);
lean_dec_ref(v___y_5176_);
lean_dec_ref(v___y_5175_);
return v___x_5199_;
}
else
{
lean_object* v_pos_5200_; 
v_pos_5200_ = lean_ctor_get(v___x_5199_, 0);
lean_inc(v_pos_5200_);
v_snd_5133_ = v_snd_5181_;
v___y_5134_ = v___y_5175_;
v___y_5135_ = v___y_5176_;
v___y_5136_ = v___x_5199_;
v_pos_5137_ = v_pos_5200_;
goto v___jp_5132_;
}
}
else
{
lean_object* v_pos_5201_; lean_object* v_err_5202_; 
v_pos_5201_ = lean_ctor_get(v___x_5196_, 0);
lean_inc(v_pos_5201_);
v_err_5202_ = lean_ctor_get(v___x_5196_, 1);
lean_inc(v_err_5202_);
lean_dec_ref_known(v___x_5196_, 2);
v_snd_5167_ = v_snd_5181_;
v___y_5168_ = v___y_5175_;
v___y_5169_ = v___y_5176_;
v_pos_5170_ = v_pos_5201_;
v_err_5171_ = v_err_5202_;
goto v___jp_5166_;
}
}
}
}
}
else
{
lean_object* v___x_5207_; 
v___x_5207_ = lean_box(0);
v_snd_5167_ = v_snd_5181_;
v___y_5168_ = v___y_5175_;
v___y_5169_ = v___y_5176_;
v_pos_5170_ = v_pos_5179_;
v_err_5171_ = v___x_5207_;
goto v___jp_5166_;
}
}
}
v___jp_5208_:
{
lean_object* v___x_5214_; 
lean_inc_ref(v_pos_5212_);
v___x_5214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5214_, 0, v_pos_5212_);
lean_ctor_set(v___x_5214_, 1, v_err_5213_);
v___y_5175_ = v___y_5209_;
v___y_5176_ = v___y_5210_;
v___y_5177_ = v___y_5211_;
v___y_5178_ = v___x_5214_;
v_pos_5179_ = v_pos_5212_;
goto v___jp_5174_;
}
v___jp_5216_:
{
lean_object* v_fst_5221_; lean_object* v_snd_5222_; uint8_t v_decide_5223_; 
v_fst_5221_ = lean_ctor_get(v_pos_5220_, 0);
v_snd_5222_ = lean_ctor_get(v_pos_5220_, 1);
lean_inc(v_snd_5222_);
v_decide_5223_ = lean_nat_dec_eq(v_snd_5218_, v_snd_5222_);
lean_dec(v_snd_5218_);
if (v_decide_5223_ == 0)
{
lean_dec(v_snd_5222_);
lean_dec_ref(v_pos_5220_);
lean_dec_ref(v___y_5217_);
return v___y_5219_;
}
else
{
lean_object* v___x_5224_; lean_object* v___x_5225_; uint8_t v_decide_5226_; 
lean_dec_ref(v___y_5219_);
v___x_5224_ = ((lean_object*)(l_Std_Time_parseModifier___closed__45));
v___x_5225_ = lean_string_utf8_byte_size(v_fst_5221_);
v_decide_5226_ = lean_nat_dec_eq(v_snd_5222_, v___x_5225_);
if (v_decide_5226_ == 0)
{
uint32_t v___x_5227_; uint32_t v_c_5228_; uint8_t v___x_5229_; 
v___x_5227_ = 87;
v_c_5228_ = lean_string_utf8_get_fast(v_fst_5221_, v_snd_5222_);
v___x_5229_ = lean_uint32_dec_eq(v_c_5228_, v___x_5227_);
if (v___x_5229_ == 0)
{
lean_object* v___x_5230_; 
v___x_5230_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24___closed__1));
v___y_5209_ = v___x_5224_;
v___y_5210_ = v___y_5217_;
v___y_5211_ = v_snd_5222_;
v_pos_5212_ = v_pos_5220_;
v_err_5213_ = v___x_5230_;
goto v___jp_5208_;
}
else
{
lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5246_; 
lean_inc(v_fst_5221_);
v_isSharedCheck_5246_ = !lean_is_exclusive(v_pos_5220_);
if (v_isSharedCheck_5246_ == 0)
{
lean_object* v_unused_5247_; lean_object* v_unused_5248_; 
v_unused_5247_ = lean_ctor_get(v_pos_5220_, 1);
lean_dec(v_unused_5247_);
v_unused_5248_ = lean_ctor_get(v_pos_5220_, 0);
lean_dec(v_unused_5248_);
v___x_5232_ = v_pos_5220_;
v_isShared_5233_ = v_isSharedCheck_5246_;
goto v_resetjp_5231_;
}
else
{
lean_dec(v_pos_5220_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5246_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5234_; lean_object* v_it_x27_5236_; 
v___x_5234_ = lean_string_utf8_next_fast(v_fst_5221_, v_snd_5222_);
if (v_isShared_5233_ == 0)
{
lean_ctor_set(v___x_5232_, 1, v___x_5234_);
v_it_x27_5236_ = v___x_5232_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_fst_5221_);
lean_ctor_set(v_reuseFailAlloc_5245_, 1, v___x_5234_);
v_it_x27_5236_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
lean_object* v___x_5237_; lean_object* v___x_5238_; 
v___x_5237_ = ((lean_object*)(l_Std_Time_parseModifier___closed__46));
v___x_5238_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__24(v___x_5237_, v_it_x27_5236_);
if (lean_obj_tag(v___x_5238_) == 0)
{
lean_object* v_pos_5239_; lean_object* v_res_5240_; lean_object* v___x_5241_; 
v_pos_5239_ = lean_ctor_get(v___x_5238_, 0);
lean_inc(v_pos_5239_);
v_res_5240_ = lean_ctor_get(v___x_5238_, 1);
lean_inc(v_res_5240_);
lean_dec_ref_known(v___x_5238_, 2);
v___x_5241_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5215_, v___x_5224_, v_res_5240_, v_pos_5239_);
if (lean_obj_tag(v___x_5241_) == 0)
{
lean_dec(v_snd_5222_);
lean_dec_ref(v___y_5217_);
return v___x_5241_;
}
else
{
lean_object* v_pos_5242_; 
v_pos_5242_ = lean_ctor_get(v___x_5241_, 0);
lean_inc(v_pos_5242_);
v___y_5175_ = v___x_5224_;
v___y_5176_ = v___y_5217_;
v___y_5177_ = v_snd_5222_;
v___y_5178_ = v___x_5241_;
v_pos_5179_ = v_pos_5242_;
goto v___jp_5174_;
}
}
else
{
lean_object* v_pos_5243_; lean_object* v_err_5244_; 
v_pos_5243_ = lean_ctor_get(v___x_5238_, 0);
lean_inc(v_pos_5243_);
v_err_5244_ = lean_ctor_get(v___x_5238_, 1);
lean_inc(v_err_5244_);
lean_dec_ref_known(v___x_5238_, 2);
v___y_5209_ = v___x_5224_;
v___y_5210_ = v___y_5217_;
v___y_5211_ = v_snd_5222_;
v_pos_5212_ = v_pos_5243_;
v_err_5213_ = v_err_5244_;
goto v___jp_5208_;
}
}
}
}
}
else
{
lean_object* v___x_5249_; 
v___x_5249_ = lean_box(0);
v___y_5209_ = v___x_5224_;
v___y_5210_ = v___y_5217_;
v___y_5211_ = v_snd_5222_;
v_pos_5212_ = v_pos_5220_;
v_err_5213_ = v___x_5249_;
goto v___jp_5208_;
}
}
}
v___jp_5250_:
{
lean_object* v___x_5255_; 
lean_inc_ref(v_pos_5253_);
v___x_5255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5255_, 0, v_pos_5253_);
lean_ctor_set(v___x_5255_, 1, v_err_5254_);
v___y_5217_ = v___y_5251_;
v_snd_5218_ = v_snd_5252_;
v___y_5219_ = v___x_5255_;
v_pos_5220_ = v_pos_5253_;
goto v___jp_5216_;
}
v___jp_5257_:
{
lean_object* v_fst_5262_; lean_object* v_snd_5263_; uint8_t v_decide_5264_; 
v_fst_5262_ = lean_ctor_get(v_pos_5261_, 0);
v_snd_5263_ = lean_ctor_get(v_pos_5261_, 1);
lean_inc(v_snd_5263_);
v_decide_5264_ = lean_nat_dec_eq(v_snd_5259_, v_snd_5263_);
lean_dec(v_snd_5259_);
if (v_decide_5264_ == 0)
{
lean_dec(v_snd_5263_);
lean_dec_ref(v_pos_5261_);
lean_dec_ref(v___y_5258_);
return v___y_5260_;
}
else
{
lean_object* v___x_5265_; uint8_t v_decide_5266_; 
lean_dec_ref(v___y_5260_);
v___x_5265_ = lean_string_utf8_byte_size(v_fst_5262_);
v_decide_5266_ = lean_nat_dec_eq(v_snd_5263_, v___x_5265_);
if (v_decide_5266_ == 0)
{
uint32_t v___x_5267_; uint32_t v_c_5268_; uint8_t v___x_5269_; 
v___x_5267_ = 119;
v_c_5268_ = lean_string_utf8_get_fast(v_fst_5262_, v_snd_5263_);
v___x_5269_ = lean_uint32_dec_eq(v_c_5268_, v___x_5267_);
if (v___x_5269_ == 0)
{
lean_object* v___x_5270_; 
v___x_5270_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25___closed__1));
v___y_5251_ = v___y_5258_;
v_snd_5252_ = v_snd_5263_;
v_pos_5253_ = v_pos_5261_;
v_err_5254_ = v___x_5270_;
goto v___jp_5250_;
}
else
{
lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5286_; 
lean_inc(v_fst_5262_);
v_isSharedCheck_5286_ = !lean_is_exclusive(v_pos_5261_);
if (v_isSharedCheck_5286_ == 0)
{
lean_object* v_unused_5287_; lean_object* v_unused_5288_; 
v_unused_5287_ = lean_ctor_get(v_pos_5261_, 1);
lean_dec(v_unused_5287_);
v_unused_5288_ = lean_ctor_get(v_pos_5261_, 0);
lean_dec(v_unused_5288_);
v___x_5272_ = v_pos_5261_;
v_isShared_5273_ = v_isSharedCheck_5286_;
goto v_resetjp_5271_;
}
else
{
lean_dec(v_pos_5261_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5286_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5274_; lean_object* v_it_x27_5276_; 
v___x_5274_ = lean_string_utf8_next_fast(v_fst_5262_, v_snd_5263_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 1, v___x_5274_);
v_it_x27_5276_ = v___x_5272_;
goto v_reusejp_5275_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_fst_5262_);
lean_ctor_set(v_reuseFailAlloc_5285_, 1, v___x_5274_);
v_it_x27_5276_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5275_;
}
v_reusejp_5275_:
{
lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___x_5277_ = ((lean_object*)(l_Std_Time_parseModifier___closed__48));
v___x_5278_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__25(v___x_5277_, v_it_x27_5276_);
if (lean_obj_tag(v___x_5278_) == 0)
{
lean_object* v_pos_5279_; lean_object* v_res_5280_; lean_object* v___x_5281_; 
v_pos_5279_ = lean_ctor_get(v___x_5278_, 0);
lean_inc(v_pos_5279_);
v_res_5280_ = lean_ctor_get(v___x_5278_, 1);
lean_inc(v_res_5280_);
lean_dec_ref_known(v___x_5278_, 2);
lean_inc_ref(v___y_5258_);
v___x_5281_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5256_, v___y_5258_, v_res_5280_, v_pos_5279_);
if (lean_obj_tag(v___x_5281_) == 0)
{
lean_dec(v_snd_5263_);
lean_dec_ref(v___y_5258_);
return v___x_5281_;
}
else
{
lean_object* v_pos_5282_; 
v_pos_5282_ = lean_ctor_get(v___x_5281_, 0);
lean_inc(v_pos_5282_);
v___y_5217_ = v___y_5258_;
v_snd_5218_ = v_snd_5263_;
v___y_5219_ = v___x_5281_;
v_pos_5220_ = v_pos_5282_;
goto v___jp_5216_;
}
}
else
{
lean_object* v_pos_5283_; lean_object* v_err_5284_; 
v_pos_5283_ = lean_ctor_get(v___x_5278_, 0);
lean_inc(v_pos_5283_);
v_err_5284_ = lean_ctor_get(v___x_5278_, 1);
lean_inc(v_err_5284_);
lean_dec_ref_known(v___x_5278_, 2);
v___y_5251_ = v___y_5258_;
v_snd_5252_ = v_snd_5263_;
v_pos_5253_ = v_pos_5283_;
v_err_5254_ = v_err_5284_;
goto v___jp_5250_;
}
}
}
}
}
else
{
lean_object* v___x_5289_; 
v___x_5289_ = lean_box(0);
v___y_5251_ = v___y_5258_;
v_snd_5252_ = v_snd_5263_;
v_pos_5253_ = v_pos_5261_;
v_err_5254_ = v___x_5289_;
goto v___jp_5250_;
}
}
}
v___jp_5290_:
{
lean_object* v___x_5295_; 
lean_inc_ref(v_pos_5293_);
v___x_5295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5295_, 0, v_pos_5293_);
lean_ctor_set(v___x_5295_, 1, v_err_5294_);
v___y_5258_ = v___y_5291_;
v_snd_5259_ = v_snd_5292_;
v___y_5260_ = v___x_5295_;
v_pos_5261_ = v_pos_5293_;
goto v___jp_5257_;
}
v___jp_5297_:
{
lean_object* v_fst_5302_; lean_object* v_snd_5303_; uint8_t v_decide_5304_; 
v_fst_5302_ = lean_ctor_get(v_pos_5301_, 0);
v_snd_5303_ = lean_ctor_get(v_pos_5301_, 1);
lean_inc(v_snd_5303_);
v_decide_5304_ = lean_nat_dec_eq(v_snd_5299_, v_snd_5303_);
lean_dec(v_snd_5299_);
if (v_decide_5304_ == 0)
{
lean_dec(v_snd_5303_);
lean_dec_ref(v_pos_5301_);
lean_dec_ref(v___y_5298_);
return v___y_5300_;
}
else
{
lean_object* v___x_5305_; uint8_t v_decide_5306_; 
lean_dec_ref(v___y_5300_);
v___x_5305_ = lean_string_utf8_byte_size(v_fst_5302_);
v_decide_5306_ = lean_nat_dec_eq(v_snd_5303_, v___x_5305_);
if (v_decide_5306_ == 0)
{
uint32_t v___x_5307_; uint32_t v_c_5308_; uint8_t v___x_5309_; 
v___x_5307_ = 113;
v_c_5308_ = lean_string_utf8_get_fast(v_fst_5302_, v_snd_5303_);
v___x_5309_ = lean_uint32_dec_eq(v_c_5308_, v___x_5307_);
if (v___x_5309_ == 0)
{
lean_object* v___x_5310_; 
v___x_5310_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26___closed__1));
v___y_5291_ = v___y_5298_;
v_snd_5292_ = v_snd_5303_;
v_pos_5293_ = v_pos_5301_;
v_err_5294_ = v___x_5310_;
goto v___jp_5290_;
}
else
{
lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5326_; 
lean_inc(v_fst_5302_);
v_isSharedCheck_5326_ = !lean_is_exclusive(v_pos_5301_);
if (v_isSharedCheck_5326_ == 0)
{
lean_object* v_unused_5327_; lean_object* v_unused_5328_; 
v_unused_5327_ = lean_ctor_get(v_pos_5301_, 1);
lean_dec(v_unused_5327_);
v_unused_5328_ = lean_ctor_get(v_pos_5301_, 0);
lean_dec(v_unused_5328_);
v___x_5312_ = v_pos_5301_;
v_isShared_5313_ = v_isSharedCheck_5326_;
goto v_resetjp_5311_;
}
else
{
lean_dec(v_pos_5301_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5326_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5314_; lean_object* v_it_x27_5316_; 
v___x_5314_ = lean_string_utf8_next_fast(v_fst_5302_, v_snd_5303_);
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 1, v___x_5314_);
v_it_x27_5316_ = v___x_5312_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_fst_5302_);
lean_ctor_set(v_reuseFailAlloc_5325_, 1, v___x_5314_);
v_it_x27_5316_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5317_ = ((lean_object*)(l_Std_Time_parseModifier___closed__50));
v___x_5318_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__26(v___x_5317_, v_it_x27_5316_);
if (lean_obj_tag(v___x_5318_) == 0)
{
lean_object* v_pos_5319_; lean_object* v_res_5320_; lean_object* v___x_5321_; 
v_pos_5319_ = lean_ctor_get(v___x_5318_, 0);
lean_inc(v_pos_5319_);
v_res_5320_ = lean_ctor_get(v___x_5318_, 1);
lean_inc(v_res_5320_);
lean_dec_ref_known(v___x_5318_, 2);
v___x_5321_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5296_, v_res_5320_, v_pos_5319_);
if (lean_obj_tag(v___x_5321_) == 0)
{
lean_dec(v_snd_5303_);
lean_dec_ref(v___y_5298_);
return v___x_5321_;
}
else
{
lean_object* v_pos_5322_; 
v_pos_5322_ = lean_ctor_get(v___x_5321_, 0);
lean_inc(v_pos_5322_);
v___y_5258_ = v___y_5298_;
v_snd_5259_ = v_snd_5303_;
v___y_5260_ = v___x_5321_;
v_pos_5261_ = v_pos_5322_;
goto v___jp_5257_;
}
}
else
{
lean_object* v_pos_5323_; lean_object* v_err_5324_; 
v_pos_5323_ = lean_ctor_get(v___x_5318_, 0);
lean_inc(v_pos_5323_);
v_err_5324_ = lean_ctor_get(v___x_5318_, 1);
lean_inc(v_err_5324_);
lean_dec_ref_known(v___x_5318_, 2);
v___y_5291_ = v___y_5298_;
v_snd_5292_ = v_snd_5303_;
v_pos_5293_ = v_pos_5323_;
v_err_5294_ = v_err_5324_;
goto v___jp_5290_;
}
}
}
}
}
else
{
lean_object* v___x_5329_; 
v___x_5329_ = lean_box(0);
v___y_5291_ = v___y_5298_;
v_snd_5292_ = v_snd_5303_;
v_pos_5293_ = v_pos_5301_;
v_err_5294_ = v___x_5329_;
goto v___jp_5290_;
}
}
}
v___jp_5330_:
{
lean_object* v___x_5335_; 
lean_inc_ref(v_pos_5333_);
v___x_5335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5335_, 0, v_pos_5333_);
lean_ctor_set(v___x_5335_, 1, v_err_5334_);
v___y_5298_ = v___y_5331_;
v_snd_5299_ = v_snd_5332_;
v___y_5300_ = v___x_5335_;
v_pos_5301_ = v_pos_5333_;
goto v___jp_5297_;
}
v___jp_5337_:
{
lean_object* v_fst_5342_; lean_object* v_snd_5343_; uint8_t v_decide_5344_; 
v_fst_5342_ = lean_ctor_get(v_pos_5341_, 0);
v_snd_5343_ = lean_ctor_get(v_pos_5341_, 1);
lean_inc(v_snd_5343_);
v_decide_5344_ = lean_nat_dec_eq(v___y_5338_, v_snd_5343_);
lean_dec(v___y_5338_);
if (v_decide_5344_ == 0)
{
lean_dec(v_snd_5343_);
lean_dec_ref(v_pos_5341_);
lean_dec_ref(v___y_5339_);
return v___y_5340_;
}
else
{
lean_object* v___x_5345_; uint8_t v_decide_5346_; 
lean_dec_ref(v___y_5340_);
v___x_5345_ = lean_string_utf8_byte_size(v_fst_5342_);
v_decide_5346_ = lean_nat_dec_eq(v_snd_5343_, v___x_5345_);
if (v_decide_5346_ == 0)
{
uint32_t v___x_5347_; uint32_t v_c_5348_; uint8_t v___x_5349_; 
v___x_5347_ = 81;
v_c_5348_ = lean_string_utf8_get_fast(v_fst_5342_, v_snd_5343_);
v___x_5349_ = lean_uint32_dec_eq(v_c_5348_, v___x_5347_);
if (v___x_5349_ == 0)
{
lean_object* v___x_5350_; 
v___x_5350_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27___closed__1));
v___y_5331_ = v___y_5339_;
v_snd_5332_ = v_snd_5343_;
v_pos_5333_ = v_pos_5341_;
v_err_5334_ = v___x_5350_;
goto v___jp_5330_;
}
else
{
lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5366_; 
lean_inc(v_fst_5342_);
v_isSharedCheck_5366_ = !lean_is_exclusive(v_pos_5341_);
if (v_isSharedCheck_5366_ == 0)
{
lean_object* v_unused_5367_; lean_object* v_unused_5368_; 
v_unused_5367_ = lean_ctor_get(v_pos_5341_, 1);
lean_dec(v_unused_5367_);
v_unused_5368_ = lean_ctor_get(v_pos_5341_, 0);
lean_dec(v_unused_5368_);
v___x_5352_ = v_pos_5341_;
v_isShared_5353_ = v_isSharedCheck_5366_;
goto v_resetjp_5351_;
}
else
{
lean_dec(v_pos_5341_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5366_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5354_; lean_object* v_it_x27_5356_; 
v___x_5354_ = lean_string_utf8_next_fast(v_fst_5342_, v_snd_5343_);
if (v_isShared_5353_ == 0)
{
lean_ctor_set(v___x_5352_, 1, v___x_5354_);
v_it_x27_5356_ = v___x_5352_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_fst_5342_);
lean_ctor_set(v_reuseFailAlloc_5365_, 1, v___x_5354_);
v_it_x27_5356_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
lean_object* v___x_5357_; lean_object* v___x_5358_; 
v___x_5357_ = ((lean_object*)(l_Std_Time_parseModifier___closed__52));
v___x_5358_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__27(v___x_5357_, v_it_x27_5356_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_pos_5359_; lean_object* v_res_5360_; lean_object* v___x_5361_; 
v_pos_5359_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_pos_5359_);
v_res_5360_ = lean_ctor_get(v___x_5358_, 1);
lean_inc(v_res_5360_);
lean_dec_ref_known(v___x_5358_, 2);
v___x_5361_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5336_, v_res_5360_, v_pos_5359_);
if (lean_obj_tag(v___x_5361_) == 0)
{
lean_dec(v_snd_5343_);
lean_dec_ref(v___y_5339_);
return v___x_5361_;
}
else
{
lean_object* v_pos_5362_; 
v_pos_5362_ = lean_ctor_get(v___x_5361_, 0);
lean_inc(v_pos_5362_);
v___y_5298_ = v___y_5339_;
v_snd_5299_ = v_snd_5343_;
v___y_5300_ = v___x_5361_;
v_pos_5301_ = v_pos_5362_;
goto v___jp_5297_;
}
}
else
{
lean_object* v_pos_5363_; lean_object* v_err_5364_; 
v_pos_5363_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_pos_5363_);
v_err_5364_ = lean_ctor_get(v___x_5358_, 1);
lean_inc(v_err_5364_);
lean_dec_ref_known(v___x_5358_, 2);
v___y_5331_ = v___y_5339_;
v_snd_5332_ = v_snd_5343_;
v_pos_5333_ = v_pos_5363_;
v_err_5334_ = v_err_5364_;
goto v___jp_5330_;
}
}
}
}
}
else
{
lean_object* v___x_5369_; 
v___x_5369_ = lean_box(0);
v___y_5331_ = v___y_5339_;
v_snd_5332_ = v_snd_5343_;
v_pos_5333_ = v_pos_5341_;
v_err_5334_ = v___x_5369_;
goto v___jp_5330_;
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
v___y_5338_ = v___y_5371_;
v___y_5339_ = v___y_5372_;
v___y_5340_ = v___x_5375_;
v_pos_5341_ = v_pos_5373_;
goto v___jp_5337_;
}
v___jp_5377_:
{
lean_object* v_fst_5381_; lean_object* v_snd_5382_; uint8_t v_decide_5383_; 
v_fst_5381_ = lean_ctor_get(v_pos_5380_, 0);
v_snd_5382_ = lean_ctor_get(v_pos_5380_, 1);
lean_inc(v_snd_5382_);
v_decide_5383_ = lean_nat_dec_eq(v_snd_5378_, v_snd_5382_);
lean_dec(v_snd_5378_);
if (v_decide_5383_ == 0)
{
lean_dec(v_snd_5382_);
lean_dec_ref(v_pos_5380_);
return v___y_5379_;
}
else
{
lean_object* v___x_5384_; lean_object* v___x_5385_; uint8_t v_decide_5386_; 
lean_dec_ref(v___y_5379_);
v___x_5384_ = ((lean_object*)(l_Std_Time_parseModifier___closed__54));
v___x_5385_ = lean_string_utf8_byte_size(v_fst_5381_);
v_decide_5386_ = lean_nat_dec_eq(v_snd_5382_, v___x_5385_);
if (v_decide_5386_ == 0)
{
uint32_t v___x_5387_; uint32_t v_c_5388_; uint8_t v___x_5389_; 
v___x_5387_ = 100;
v_c_5388_ = lean_string_utf8_get_fast(v_fst_5381_, v_snd_5382_);
v___x_5389_ = lean_uint32_dec_eq(v_c_5388_, v___x_5387_);
if (v___x_5389_ == 0)
{
lean_object* v___x_5390_; 
v___x_5390_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28___closed__1));
v___y_5371_ = v_snd_5382_;
v___y_5372_ = v___x_5384_;
v_pos_5373_ = v_pos_5380_;
v_err_5374_ = v___x_5390_;
goto v___jp_5370_;
}
else
{
lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5406_; 
lean_inc(v_fst_5381_);
v_isSharedCheck_5406_ = !lean_is_exclusive(v_pos_5380_);
if (v_isSharedCheck_5406_ == 0)
{
lean_object* v_unused_5407_; lean_object* v_unused_5408_; 
v_unused_5407_ = lean_ctor_get(v_pos_5380_, 1);
lean_dec(v_unused_5407_);
v_unused_5408_ = lean_ctor_get(v_pos_5380_, 0);
lean_dec(v_unused_5408_);
v___x_5392_ = v_pos_5380_;
v_isShared_5393_ = v_isSharedCheck_5406_;
goto v_resetjp_5391_;
}
else
{
lean_dec(v_pos_5380_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5406_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v___x_5394_; lean_object* v_it_x27_5396_; 
v___x_5394_ = lean_string_utf8_next_fast(v_fst_5381_, v_snd_5382_);
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 1, v___x_5394_);
v_it_x27_5396_ = v___x_5392_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_fst_5381_);
lean_ctor_set(v_reuseFailAlloc_5405_, 1, v___x_5394_);
v_it_x27_5396_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5397_ = ((lean_object*)(l_Std_Time_parseModifier___closed__55));
v___x_5398_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__28(v___x_5397_, v_it_x27_5396_);
if (lean_obj_tag(v___x_5398_) == 0)
{
lean_object* v_pos_5399_; lean_object* v_res_5400_; lean_object* v___x_5401_; 
v_pos_5399_ = lean_ctor_get(v___x_5398_, 0);
lean_inc(v_pos_5399_);
v_res_5400_ = lean_ctor_get(v___x_5398_, 1);
lean_inc(v_res_5400_);
lean_dec_ref_known(v___x_5398_, 2);
v___x_5401_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5376_, v___x_5384_, v_res_5400_, v_pos_5399_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_dec(v_snd_5382_);
return v___x_5401_;
}
else
{
lean_object* v_pos_5402_; 
v_pos_5402_ = lean_ctor_get(v___x_5401_, 0);
lean_inc(v_pos_5402_);
v___y_5338_ = v_snd_5382_;
v___y_5339_ = v___x_5384_;
v___y_5340_ = v___x_5401_;
v_pos_5341_ = v_pos_5402_;
goto v___jp_5337_;
}
}
else
{
lean_object* v_pos_5403_; lean_object* v_err_5404_; 
v_pos_5403_ = lean_ctor_get(v___x_5398_, 0);
lean_inc(v_pos_5403_);
v_err_5404_ = lean_ctor_get(v___x_5398_, 1);
lean_inc(v_err_5404_);
lean_dec_ref_known(v___x_5398_, 2);
v___y_5371_ = v_snd_5382_;
v___y_5372_ = v___x_5384_;
v_pos_5373_ = v_pos_5403_;
v_err_5374_ = v_err_5404_;
goto v___jp_5370_;
}
}
}
}
}
else
{
lean_object* v___x_5409_; 
v___x_5409_ = lean_box(0);
v___y_5371_ = v_snd_5382_;
v___y_5372_ = v___x_5384_;
v_pos_5373_ = v_pos_5380_;
v_err_5374_ = v___x_5409_;
goto v___jp_5370_;
}
}
}
v___jp_5410_:
{
lean_object* v___x_5414_; 
lean_inc_ref(v_pos_5412_);
v___x_5414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5414_, 0, v_pos_5412_);
lean_ctor_set(v___x_5414_, 1, v_err_5413_);
v_snd_5378_ = v_snd_5411_;
v___y_5379_ = v___x_5414_;
v_pos_5380_ = v_pos_5412_;
goto v___jp_5377_;
}
v___jp_5416_:
{
lean_object* v_fst_5420_; lean_object* v_snd_5421_; uint8_t v_decide_5422_; 
v_fst_5420_ = lean_ctor_get(v_pos_5419_, 0);
v_snd_5421_ = lean_ctor_get(v_pos_5419_, 1);
lean_inc(v_snd_5421_);
v_decide_5422_ = lean_nat_dec_eq(v_snd_5417_, v_snd_5421_);
lean_dec(v_snd_5417_);
if (v_decide_5422_ == 0)
{
lean_dec(v_snd_5421_);
lean_dec_ref(v_pos_5419_);
return v___y_5418_;
}
else
{
lean_object* v___x_5423_; uint8_t v_decide_5424_; 
lean_dec_ref(v___y_5418_);
v___x_5423_ = lean_string_utf8_byte_size(v_fst_5420_);
v_decide_5424_ = lean_nat_dec_eq(v_snd_5421_, v___x_5423_);
if (v_decide_5424_ == 0)
{
uint32_t v___x_5425_; uint32_t v_c_5426_; uint8_t v___x_5427_; 
v___x_5425_ = 76;
v_c_5426_ = lean_string_utf8_get_fast(v_fst_5420_, v_snd_5421_);
v___x_5427_ = lean_uint32_dec_eq(v_c_5426_, v___x_5425_);
if (v___x_5427_ == 0)
{
lean_object* v___x_5428_; 
v___x_5428_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29___closed__1));
v_snd_5411_ = v_snd_5421_;
v_pos_5412_ = v_pos_5419_;
v_err_5413_ = v___x_5428_;
goto v___jp_5410_;
}
else
{
lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5444_; 
lean_inc(v_fst_5420_);
v_isSharedCheck_5444_ = !lean_is_exclusive(v_pos_5419_);
if (v_isSharedCheck_5444_ == 0)
{
lean_object* v_unused_5445_; lean_object* v_unused_5446_; 
v_unused_5445_ = lean_ctor_get(v_pos_5419_, 1);
lean_dec(v_unused_5445_);
v_unused_5446_ = lean_ctor_get(v_pos_5419_, 0);
lean_dec(v_unused_5446_);
v___x_5430_ = v_pos_5419_;
v_isShared_5431_ = v_isSharedCheck_5444_;
goto v_resetjp_5429_;
}
else
{
lean_dec(v_pos_5419_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5444_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5432_; lean_object* v_it_x27_5434_; 
v___x_5432_ = lean_string_utf8_next_fast(v_fst_5420_, v_snd_5421_);
if (v_isShared_5431_ == 0)
{
lean_ctor_set(v___x_5430_, 1, v___x_5432_);
v_it_x27_5434_ = v___x_5430_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_fst_5420_);
lean_ctor_set(v_reuseFailAlloc_5443_, 1, v___x_5432_);
v_it_x27_5434_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
lean_object* v___x_5435_; lean_object* v___x_5436_; 
v___x_5435_ = ((lean_object*)(l_Std_Time_parseModifier___closed__57));
v___x_5436_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__29(v___x_5435_, v_it_x27_5434_);
if (lean_obj_tag(v___x_5436_) == 0)
{
lean_object* v_pos_5437_; lean_object* v_res_5438_; lean_object* v___x_5439_; 
v_pos_5437_ = lean_ctor_get(v___x_5436_, 0);
lean_inc(v_pos_5437_);
v_res_5438_ = lean_ctor_get(v___x_5436_, 1);
lean_inc(v_res_5438_);
lean_dec_ref_known(v___x_5436_, 2);
v___x_5439_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5415_, v_res_5438_, v_pos_5437_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_dec(v_snd_5421_);
return v___x_5439_;
}
else
{
lean_object* v_pos_5440_; 
v_pos_5440_ = lean_ctor_get(v___x_5439_, 0);
lean_inc(v_pos_5440_);
v_snd_5378_ = v_snd_5421_;
v___y_5379_ = v___x_5439_;
v_pos_5380_ = v_pos_5440_;
goto v___jp_5377_;
}
}
else
{
lean_object* v_pos_5441_; lean_object* v_err_5442_; 
v_pos_5441_ = lean_ctor_get(v___x_5436_, 0);
lean_inc(v_pos_5441_);
v_err_5442_ = lean_ctor_get(v___x_5436_, 1);
lean_inc(v_err_5442_);
lean_dec_ref_known(v___x_5436_, 2);
v_snd_5411_ = v_snd_5421_;
v_pos_5412_ = v_pos_5441_;
v_err_5413_ = v_err_5442_;
goto v___jp_5410_;
}
}
}
}
}
else
{
lean_object* v___x_5447_; 
v___x_5447_ = lean_box(0);
v_snd_5411_ = v_snd_5421_;
v_pos_5412_ = v_pos_5419_;
v_err_5413_ = v___x_5447_;
goto v___jp_5410_;
}
}
}
v___jp_5448_:
{
lean_object* v___x_5452_; 
lean_inc_ref(v_pos_5450_);
v___x_5452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5452_, 0, v_pos_5450_);
lean_ctor_set(v___x_5452_, 1, v_err_5451_);
v_snd_5417_ = v_snd_5449_;
v___y_5418_ = v___x_5452_;
v_pos_5419_ = v_pos_5450_;
goto v___jp_5416_;
}
v___jp_5454_:
{
lean_object* v_fst_5458_; lean_object* v_snd_5459_; uint8_t v_decide_5460_; 
v_fst_5458_ = lean_ctor_get(v_pos_5457_, 0);
v_snd_5459_ = lean_ctor_get(v_pos_5457_, 1);
lean_inc(v_snd_5459_);
v_decide_5460_ = lean_nat_dec_eq(v_snd_5455_, v_snd_5459_);
lean_dec(v_snd_5455_);
if (v_decide_5460_ == 0)
{
lean_dec(v_snd_5459_);
lean_dec_ref(v_pos_5457_);
return v___y_5456_;
}
else
{
lean_object* v___x_5461_; uint8_t v_decide_5462_; 
lean_dec_ref(v___y_5456_);
v___x_5461_ = lean_string_utf8_byte_size(v_fst_5458_);
v_decide_5462_ = lean_nat_dec_eq(v_snd_5459_, v___x_5461_);
if (v_decide_5462_ == 0)
{
uint32_t v___x_5463_; uint32_t v_c_5464_; uint8_t v___x_5465_; 
v___x_5463_ = 77;
v_c_5464_ = lean_string_utf8_get_fast(v_fst_5458_, v_snd_5459_);
v___x_5465_ = lean_uint32_dec_eq(v_c_5464_, v___x_5463_);
if (v___x_5465_ == 0)
{
lean_object* v___x_5466_; 
v___x_5466_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30___closed__1));
v_snd_5449_ = v_snd_5459_;
v_pos_5450_ = v_pos_5457_;
v_err_5451_ = v___x_5466_;
goto v___jp_5448_;
}
else
{
lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5482_; 
lean_inc(v_fst_5458_);
v_isSharedCheck_5482_ = !lean_is_exclusive(v_pos_5457_);
if (v_isSharedCheck_5482_ == 0)
{
lean_object* v_unused_5483_; lean_object* v_unused_5484_; 
v_unused_5483_ = lean_ctor_get(v_pos_5457_, 1);
lean_dec(v_unused_5483_);
v_unused_5484_ = lean_ctor_get(v_pos_5457_, 0);
lean_dec(v_unused_5484_);
v___x_5468_ = v_pos_5457_;
v_isShared_5469_ = v_isSharedCheck_5482_;
goto v_resetjp_5467_;
}
else
{
lean_dec(v_pos_5457_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5482_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5470_; lean_object* v_it_x27_5472_; 
v___x_5470_ = lean_string_utf8_next_fast(v_fst_5458_, v_snd_5459_);
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 1, v___x_5470_);
v_it_x27_5472_ = v___x_5468_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_fst_5458_);
lean_ctor_set(v_reuseFailAlloc_5481_, 1, v___x_5470_);
v_it_x27_5472_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
lean_object* v___x_5473_; lean_object* v___x_5474_; 
v___x_5473_ = ((lean_object*)(l_Std_Time_parseModifier___closed__59));
v___x_5474_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__30(v___x_5473_, v_it_x27_5472_);
if (lean_obj_tag(v___x_5474_) == 0)
{
lean_object* v_pos_5475_; lean_object* v_res_5476_; lean_object* v___x_5477_; 
v_pos_5475_ = lean_ctor_get(v___x_5474_, 0);
lean_inc(v_pos_5475_);
v_res_5476_ = lean_ctor_get(v___x_5474_, 1);
lean_inc(v_res_5476_);
lean_dec_ref_known(v___x_5474_, 2);
v___x_5477_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseNumberText(v___f_5453_, v_res_5476_, v_pos_5475_);
if (lean_obj_tag(v___x_5477_) == 0)
{
lean_dec(v_snd_5459_);
return v___x_5477_;
}
else
{
lean_object* v_pos_5478_; 
v_pos_5478_ = lean_ctor_get(v___x_5477_, 0);
lean_inc(v_pos_5478_);
v_snd_5417_ = v_snd_5459_;
v___y_5418_ = v___x_5477_;
v_pos_5419_ = v_pos_5478_;
goto v___jp_5416_;
}
}
else
{
lean_object* v_pos_5479_; lean_object* v_err_5480_; 
v_pos_5479_ = lean_ctor_get(v___x_5474_, 0);
lean_inc(v_pos_5479_);
v_err_5480_ = lean_ctor_get(v___x_5474_, 1);
lean_inc(v_err_5480_);
lean_dec_ref_known(v___x_5474_, 2);
v_snd_5449_ = v_snd_5459_;
v_pos_5450_ = v_pos_5479_;
v_err_5451_ = v_err_5480_;
goto v___jp_5448_;
}
}
}
}
}
else
{
lean_object* v___x_5485_; 
v___x_5485_ = lean_box(0);
v_snd_5449_ = v_snd_5459_;
v_pos_5450_ = v_pos_5457_;
v_err_5451_ = v___x_5485_;
goto v___jp_5448_;
}
}
}
v___jp_5486_:
{
lean_object* v___x_5490_; 
lean_inc_ref(v_pos_5488_);
v___x_5490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5490_, 0, v_pos_5488_);
lean_ctor_set(v___x_5490_, 1, v_err_5489_);
v_snd_5455_ = v_snd_5487_;
v___y_5456_ = v___x_5490_;
v_pos_5457_ = v_pos_5488_;
goto v___jp_5454_;
}
v___jp_5492_:
{
lean_object* v_fst_5496_; lean_object* v_snd_5497_; uint8_t v_decide_5498_; 
v_fst_5496_ = lean_ctor_get(v_pos_5495_, 0);
v_snd_5497_ = lean_ctor_get(v_pos_5495_, 1);
lean_inc(v_snd_5497_);
v_decide_5498_ = lean_nat_dec_eq(v_snd_5493_, v_snd_5497_);
lean_dec(v_snd_5493_);
if (v_decide_5498_ == 0)
{
lean_dec(v_snd_5497_);
lean_dec_ref(v_pos_5495_);
return v___y_5494_;
}
else
{
lean_object* v___x_5499_; uint8_t v_decide_5500_; 
lean_dec_ref(v___y_5494_);
v___x_5499_ = lean_string_utf8_byte_size(v_fst_5496_);
v_decide_5500_ = lean_nat_dec_eq(v_snd_5497_, v___x_5499_);
if (v_decide_5500_ == 0)
{
uint32_t v___x_5501_; uint32_t v_c_5502_; uint8_t v___x_5503_; 
v___x_5501_ = 68;
v_c_5502_ = lean_string_utf8_get_fast(v_fst_5496_, v_snd_5497_);
v___x_5503_ = lean_uint32_dec_eq(v_c_5502_, v___x_5501_);
if (v___x_5503_ == 0)
{
lean_object* v___x_5504_; 
v___x_5504_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31___closed__1));
v_snd_5487_ = v_snd_5497_;
v_pos_5488_ = v_pos_5495_;
v_err_5489_ = v___x_5504_;
goto v___jp_5486_;
}
else
{
lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5521_; 
lean_inc(v_fst_5496_);
v_isSharedCheck_5521_ = !lean_is_exclusive(v_pos_5495_);
if (v_isSharedCheck_5521_ == 0)
{
lean_object* v_unused_5522_; lean_object* v_unused_5523_; 
v_unused_5522_ = lean_ctor_get(v_pos_5495_, 1);
lean_dec(v_unused_5522_);
v_unused_5523_ = lean_ctor_get(v_pos_5495_, 0);
lean_dec(v_unused_5523_);
v___x_5506_ = v_pos_5495_;
v_isShared_5507_ = v_isSharedCheck_5521_;
goto v_resetjp_5505_;
}
else
{
lean_dec(v_pos_5495_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5521_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5508_; lean_object* v_it_x27_5510_; 
v___x_5508_ = lean_string_utf8_next_fast(v_fst_5496_, v_snd_5497_);
if (v_isShared_5507_ == 0)
{
lean_ctor_set(v___x_5506_, 1, v___x_5508_);
v_it_x27_5510_ = v___x_5506_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_fst_5496_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v___x_5508_);
v_it_x27_5510_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5511_; lean_object* v___x_5512_; 
v___x_5511_ = ((lean_object*)(l_Std_Time_parseModifier___closed__61));
v___x_5512_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__31(v___x_5511_, v_it_x27_5510_);
if (lean_obj_tag(v___x_5512_) == 0)
{
lean_object* v_pos_5513_; lean_object* v_res_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; 
v_pos_5513_ = lean_ctor_get(v___x_5512_, 0);
lean_inc(v_pos_5513_);
v_res_5514_ = lean_ctor_get(v___x_5512_, 1);
lean_inc(v_res_5514_);
lean_dec_ref_known(v___x_5512_, 2);
v___x_5515_ = ((lean_object*)(l_Std_Time_parseModifier___closed__62));
v___x_5516_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseMod___redArg(v___f_5491_, v___x_5515_, v_res_5514_, v_pos_5513_);
if (lean_obj_tag(v___x_5516_) == 0)
{
lean_dec(v_snd_5497_);
return v___x_5516_;
}
else
{
lean_object* v_pos_5517_; 
v_pos_5517_ = lean_ctor_get(v___x_5516_, 0);
lean_inc(v_pos_5517_);
v_snd_5455_ = v_snd_5497_;
v___y_5456_ = v___x_5516_;
v_pos_5457_ = v_pos_5517_;
goto v___jp_5454_;
}
}
else
{
lean_object* v_pos_5518_; lean_object* v_err_5519_; 
v_pos_5518_ = lean_ctor_get(v___x_5512_, 0);
lean_inc(v_pos_5518_);
v_err_5519_ = lean_ctor_get(v___x_5512_, 1);
lean_inc(v_err_5519_);
lean_dec_ref_known(v___x_5512_, 2);
v_snd_5487_ = v_snd_5497_;
v_pos_5488_ = v_pos_5518_;
v_err_5489_ = v_err_5519_;
goto v___jp_5486_;
}
}
}
}
}
else
{
lean_object* v___x_5524_; 
v___x_5524_ = lean_box(0);
v_snd_5487_ = v_snd_5497_;
v_pos_5488_ = v_pos_5495_;
v_err_5489_ = v___x_5524_;
goto v___jp_5486_;
}
}
}
v___jp_5525_:
{
lean_object* v___x_5529_; 
lean_inc_ref(v_pos_5527_);
v___x_5529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5529_, 0, v_pos_5527_);
lean_ctor_set(v___x_5529_, 1, v_err_5528_);
v_snd_5493_ = v_snd_5526_;
v___y_5494_ = v___x_5529_;
v_pos_5495_ = v_pos_5527_;
goto v___jp_5492_;
}
v___jp_5531_:
{
lean_object* v_fst_5535_; lean_object* v_snd_5536_; uint8_t v_decide_5537_; 
v_fst_5535_ = lean_ctor_get(v_pos_5534_, 0);
v_snd_5536_ = lean_ctor_get(v_pos_5534_, 1);
lean_inc(v_snd_5536_);
v_decide_5537_ = lean_nat_dec_eq(v_snd_5532_, v_snd_5536_);
lean_dec(v_snd_5532_);
if (v_decide_5537_ == 0)
{
lean_dec(v_snd_5536_);
lean_dec_ref(v_pos_5534_);
return v___y_5533_;
}
else
{
lean_object* v___x_5538_; uint8_t v_decide_5539_; 
lean_dec_ref(v___y_5533_);
v___x_5538_ = lean_string_utf8_byte_size(v_fst_5535_);
v_decide_5539_ = lean_nat_dec_eq(v_snd_5536_, v___x_5538_);
if (v_decide_5539_ == 0)
{
uint32_t v___x_5540_; uint32_t v_c_5541_; uint8_t v___x_5542_; 
v___x_5540_ = 117;
v_c_5541_ = lean_string_utf8_get_fast(v_fst_5535_, v_snd_5536_);
v___x_5542_ = lean_uint32_dec_eq(v_c_5541_, v___x_5540_);
if (v___x_5542_ == 0)
{
lean_object* v___x_5543_; 
v___x_5543_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32___closed__1));
v_snd_5526_ = v_snd_5536_;
v_pos_5527_ = v_pos_5534_;
v_err_5528_ = v___x_5543_;
goto v___jp_5525_;
}
else
{
lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5559_; 
lean_inc(v_fst_5535_);
v_isSharedCheck_5559_ = !lean_is_exclusive(v_pos_5534_);
if (v_isSharedCheck_5559_ == 0)
{
lean_object* v_unused_5560_; lean_object* v_unused_5561_; 
v_unused_5560_ = lean_ctor_get(v_pos_5534_, 1);
lean_dec(v_unused_5560_);
v_unused_5561_ = lean_ctor_get(v_pos_5534_, 0);
lean_dec(v_unused_5561_);
v___x_5545_ = v_pos_5534_;
v_isShared_5546_ = v_isSharedCheck_5559_;
goto v_resetjp_5544_;
}
else
{
lean_dec(v_pos_5534_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5559_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v___x_5547_; lean_object* v_it_x27_5549_; 
v___x_5547_ = lean_string_utf8_next_fast(v_fst_5535_, v_snd_5536_);
if (v_isShared_5546_ == 0)
{
lean_ctor_set(v___x_5545_, 1, v___x_5547_);
v_it_x27_5549_ = v___x_5545_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_fst_5535_);
lean_ctor_set(v_reuseFailAlloc_5558_, 1, v___x_5547_);
v_it_x27_5549_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; 
v___x_5550_ = ((lean_object*)(l_Std_Time_parseModifier___closed__64));
v___x_5551_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__32(v___x_5550_, v_it_x27_5549_);
if (lean_obj_tag(v___x_5551_) == 0)
{
lean_object* v_pos_5552_; lean_object* v_res_5553_; lean_object* v___x_5554_; 
v_pos_5552_ = lean_ctor_get(v___x_5551_, 0);
lean_inc(v_pos_5552_);
v_res_5553_ = lean_ctor_get(v___x_5551_, 1);
lean_inc(v_res_5553_);
lean_dec_ref_known(v___x_5551_, 2);
v___x_5554_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5530_, v_res_5553_, v_pos_5552_);
if (lean_obj_tag(v___x_5554_) == 0)
{
lean_dec(v_snd_5536_);
return v___x_5554_;
}
else
{
lean_object* v_pos_5555_; 
v_pos_5555_ = lean_ctor_get(v___x_5554_, 0);
lean_inc(v_pos_5555_);
v_snd_5493_ = v_snd_5536_;
v___y_5494_ = v___x_5554_;
v_pos_5495_ = v_pos_5555_;
goto v___jp_5492_;
}
}
else
{
lean_object* v_pos_5556_; lean_object* v_err_5557_; 
v_pos_5556_ = lean_ctor_get(v___x_5551_, 0);
lean_inc(v_pos_5556_);
v_err_5557_ = lean_ctor_get(v___x_5551_, 1);
lean_inc(v_err_5557_);
lean_dec_ref_known(v___x_5551_, 2);
v_snd_5526_ = v_snd_5536_;
v_pos_5527_ = v_pos_5556_;
v_err_5528_ = v_err_5557_;
goto v___jp_5525_;
}
}
}
}
}
else
{
lean_object* v___x_5562_; 
v___x_5562_ = lean_box(0);
v_snd_5526_ = v_snd_5536_;
v_pos_5527_ = v_pos_5534_;
v_err_5528_ = v___x_5562_;
goto v___jp_5525_;
}
}
}
v___jp_5563_:
{
lean_object* v___x_5567_; 
lean_inc_ref(v_pos_5565_);
v___x_5567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5567_, 0, v_pos_5565_);
lean_ctor_set(v___x_5567_, 1, v_err_5566_);
v_snd_5532_ = v_snd_5564_;
v___y_5533_ = v___x_5567_;
v_pos_5534_ = v_pos_5565_;
goto v___jp_5531_;
}
v___jp_5569_:
{
lean_object* v_fst_5573_; lean_object* v_snd_5574_; uint8_t v_decide_5575_; 
v_fst_5573_ = lean_ctor_get(v_pos_5572_, 0);
v_snd_5574_ = lean_ctor_get(v_pos_5572_, 1);
lean_inc(v_snd_5574_);
v_decide_5575_ = lean_nat_dec_eq(v_snd_5570_, v_snd_5574_);
lean_dec(v_snd_5570_);
if (v_decide_5575_ == 0)
{
lean_dec(v_snd_5574_);
lean_dec_ref(v_pos_5572_);
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
uint32_t v___x_5578_; uint32_t v_c_5579_; uint8_t v___x_5580_; 
v___x_5578_ = 89;
v_c_5579_ = lean_string_utf8_get_fast(v_fst_5573_, v_snd_5574_);
v___x_5580_ = lean_uint32_dec_eq(v_c_5579_, v___x_5578_);
if (v___x_5580_ == 0)
{
lean_object* v___x_5581_; 
v___x_5581_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33___closed__1));
v_snd_5564_ = v_snd_5574_;
v_pos_5565_ = v_pos_5572_;
v_err_5566_ = v___x_5581_;
goto v___jp_5563_;
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
v___x_5588_ = ((lean_object*)(l_Std_Time_parseModifier___closed__66));
v___x_5589_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__33(v___x_5588_, v_it_x27_5587_);
if (lean_obj_tag(v___x_5589_) == 0)
{
lean_object* v_pos_5590_; lean_object* v_res_5591_; lean_object* v___x_5592_; 
v_pos_5590_ = lean_ctor_get(v___x_5589_, 0);
lean_inc(v_pos_5590_);
v_res_5591_ = lean_ctor_get(v___x_5589_, 1);
lean_inc(v_res_5591_);
lean_dec_ref_known(v___x_5589_, 2);
v___x_5592_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5568_, v_res_5591_, v_pos_5590_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_dec(v_snd_5574_);
return v___x_5592_;
}
else
{
lean_object* v_pos_5593_; 
v_pos_5593_ = lean_ctor_get(v___x_5592_, 0);
lean_inc(v_pos_5593_);
v_snd_5532_ = v_snd_5574_;
v___y_5533_ = v___x_5592_;
v_pos_5534_ = v_pos_5593_;
goto v___jp_5531_;
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
v_snd_5564_ = v_snd_5574_;
v_pos_5565_ = v_pos_5594_;
v_err_5566_ = v_err_5595_;
goto v___jp_5563_;
}
}
}
}
}
else
{
lean_object* v___x_5600_; 
v___x_5600_ = lean_box(0);
v_snd_5564_ = v_snd_5574_;
v_pos_5565_ = v_pos_5572_;
v_err_5566_ = v___x_5600_;
goto v___jp_5563_;
}
}
}
v___jp_5601_:
{
lean_object* v___x_5605_; 
lean_inc_ref(v_pos_5603_);
v___x_5605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5605_, 0, v_pos_5603_);
lean_ctor_set(v___x_5605_, 1, v_err_5604_);
v_snd_5570_ = v_snd_5602_;
v___y_5571_ = v___x_5605_;
v_pos_5572_ = v_pos_5603_;
goto v___jp_5569_;
}
v___jp_5607_:
{
lean_object* v_fst_5610_; lean_object* v_snd_5611_; uint8_t v_decide_5612_; 
v_fst_5610_ = lean_ctor_get(v_pos_5609_, 0);
v_snd_5611_ = lean_ctor_get(v_pos_5609_, 1);
lean_inc(v_snd_5611_);
v_decide_5612_ = lean_nat_dec_eq(v_snd_4267_, v_snd_5611_);
lean_dec(v_snd_4267_);
if (v_decide_5612_ == 0)
{
lean_dec(v_snd_5611_);
lean_dec_ref(v_pos_5609_);
return v___y_5608_;
}
else
{
lean_object* v___x_5613_; uint8_t v_decide_5614_; 
lean_dec_ref(v___y_5608_);
v___x_5613_ = lean_string_utf8_byte_size(v_fst_5610_);
v_decide_5614_ = lean_nat_dec_eq(v_snd_5611_, v___x_5613_);
if (v_decide_5614_ == 0)
{
uint32_t v___x_5615_; uint32_t v_c_5616_; uint8_t v___x_5617_; 
v___x_5615_ = 121;
v_c_5616_ = lean_string_utf8_get_fast(v_fst_5610_, v_snd_5611_);
v___x_5617_ = lean_uint32_dec_eq(v_c_5616_, v___x_5615_);
if (v___x_5617_ == 0)
{
lean_object* v___x_5618_; 
v___x_5618_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34___closed__1));
v_snd_5602_ = v_snd_5611_;
v_pos_5603_ = v_pos_5609_;
v_err_5604_ = v___x_5618_;
goto v___jp_5601_;
}
else
{
lean_object* v___x_5620_; uint8_t v_isShared_5621_; uint8_t v_isSharedCheck_5634_; 
lean_inc(v_fst_5610_);
v_isSharedCheck_5634_ = !lean_is_exclusive(v_pos_5609_);
if (v_isSharedCheck_5634_ == 0)
{
lean_object* v_unused_5635_; lean_object* v_unused_5636_; 
v_unused_5635_ = lean_ctor_get(v_pos_5609_, 1);
lean_dec(v_unused_5635_);
v_unused_5636_ = lean_ctor_get(v_pos_5609_, 0);
lean_dec(v_unused_5636_);
v___x_5620_ = v_pos_5609_;
v_isShared_5621_ = v_isSharedCheck_5634_;
goto v_resetjp_5619_;
}
else
{
lean_dec(v_pos_5609_);
v___x_5620_ = lean_box(0);
v_isShared_5621_ = v_isSharedCheck_5634_;
goto v_resetjp_5619_;
}
v_resetjp_5619_:
{
lean_object* v___x_5622_; lean_object* v_it_x27_5624_; 
v___x_5622_ = lean_string_utf8_next_fast(v_fst_5610_, v_snd_5611_);
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 1, v___x_5622_);
v_it_x27_5624_ = v___x_5620_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_fst_5610_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v___x_5622_);
v_it_x27_5624_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
lean_object* v___x_5625_; lean_object* v___x_5626_; 
v___x_5625_ = ((lean_object*)(l_Std_Time_parseModifier___closed__68));
v___x_5626_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Time_parseModifier_spec__34(v___x_5625_, v_it_x27_5624_);
if (lean_obj_tag(v___x_5626_) == 0)
{
lean_object* v_pos_5627_; lean_object* v_res_5628_; lean_object* v___x_5629_; 
v_pos_5627_ = lean_ctor_get(v___x_5626_, 0);
lean_inc(v_pos_5627_);
v_res_5628_ = lean_ctor_get(v___x_5626_, 1);
lean_inc(v_res_5628_);
lean_dec_ref_known(v___x_5626_, 2);
v___x_5629_ = l___private_Std_Time_Format_Modifier_0__Std_Time_parseYear(v___f_5606_, v_res_5628_, v_pos_5627_);
if (lean_obj_tag(v___x_5629_) == 0)
{
lean_dec(v_snd_5611_);
return v___x_5629_;
}
else
{
lean_object* v_pos_5630_; 
v_pos_5630_ = lean_ctor_get(v___x_5629_, 0);
lean_inc(v_pos_5630_);
v_snd_5570_ = v_snd_5611_;
v___y_5571_ = v___x_5629_;
v_pos_5572_ = v_pos_5630_;
goto v___jp_5569_;
}
}
else
{
lean_object* v_pos_5631_; lean_object* v_err_5632_; 
v_pos_5631_ = lean_ctor_get(v___x_5626_, 0);
lean_inc(v_pos_5631_);
v_err_5632_ = lean_ctor_get(v___x_5626_, 1);
lean_inc(v_err_5632_);
lean_dec_ref_known(v___x_5626_, 2);
v_snd_5602_ = v_snd_5611_;
v_pos_5603_ = v_pos_5631_;
v_err_5604_ = v_err_5632_;
goto v___jp_5601_;
}
}
}
}
}
else
{
lean_object* v___x_5637_; 
v___x_5637_ = lean_box(0);
v_snd_5602_ = v_snd_5611_;
v_pos_5603_ = v_pos_5609_;
v_err_5604_ = v___x_5637_;
goto v___jp_5601_;
}
}
}
v___jp_5638_:
{
lean_object* v___x_5641_; 
lean_inc_ref(v_pos_5639_);
v___x_5641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5641_, 0, v_pos_5639_);
lean_ctor_set(v___x_5641_, 1, v_err_5640_);
v___y_5608_ = v___x_5641_;
v_pos_5609_ = v_pos_5639_;
goto v___jp_5607_;
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
