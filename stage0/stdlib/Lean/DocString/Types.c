// Lean compiler output
// Module: Lean.DocString.Types
// Imports: public import Init.Data.Ord import Init.Data.Nat.Compare public import Init.Data.Array.GetLit
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
uint8_t l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_Option_repr___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_instReprMathMode_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Doc.MathMode.inline"};
static const lean_object* l_Lean_Doc_instReprMathMode_repr___closed__0 = (const lean_object*)&l_Lean_Doc_instReprMathMode_repr___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprMathMode_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprMathMode_repr___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprMathMode_repr___closed__1 = (const lean_object*)&l_Lean_Doc_instReprMathMode_repr___closed__1_value;
static const lean_string_object l_Lean_Doc_instReprMathMode_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Doc.MathMode.display"};
static const lean_object* l_Lean_Doc_instReprMathMode_repr___closed__2 = (const lean_object*)&l_Lean_Doc_instReprMathMode_repr___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprMathMode_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprMathMode_repr___closed__2_value)}};
static const lean_object* l_Lean_Doc_instReprMathMode_repr___closed__3 = (const lean_object*)&l_Lean_Doc_instReprMathMode_repr___closed__3_value;
static lean_once_cell_t l_Lean_Doc_instReprMathMode_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprMathMode_repr___closed__4;
static lean_once_cell_t l_Lean_Doc_instReprMathMode_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprMathMode_repr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprMathMode_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprMathMode_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instReprMathMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instReprMathMode_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instReprMathMode___closed__0 = (const lean_object*)&l_Lean_Doc_instReprMathMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instReprMathMode = (const lean_object*)&l_Lean_Doc_instReprMathMode___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqMathMode_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqMathMode_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instBEqMathMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instBEqMathMode_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instBEqMathMode___closed__0 = (const lean_object*)&l_Lean_Doc_instBEqMathMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instBEqMathMode = (const lean_object*)&l_Lean_Doc_instBEqMathMode___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Doc_instHashableMathMode_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_instHashableMathMode_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_instHashableMathMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instHashableMathMode_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instHashableMathMode___closed__0 = (const lean_object*)&l_Lean_Doc_instHashableMathMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instHashableMathMode = (const lean_object*)&l_Lean_Doc_instHashableMathMode___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdMathMode_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdMathMode_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instOrdMathMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instOrdMathMode_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instOrdMathMode___closed__0 = (const lean_object*)&l_Lean_Doc_instOrdMathMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instOrdMathMode = (const lean_object*)&l_Lean_Doc_instOrdMathMode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_text_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_text_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_emph_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_emph_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_bold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_bold_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_code_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_code_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_math_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_math_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_linebreak_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_linebreak_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_link_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_link_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_footnote_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_footnote_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_image_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_image_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_concat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_concat_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_other_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqInline_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqInline_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.text"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__2_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.emph"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__3_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__5_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.bold"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__6_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.code"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.math"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__14_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Doc.Inline.linebreak"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__17_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.link"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__20_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Doc.Inline.footnote"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__21_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__21_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__22 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__22_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__23_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Doc.Inline.image"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__24 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__24_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__24_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__25 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__25_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__25_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__26_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Doc.Inline.concat"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__27 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__27_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__27_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__28 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__28_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__29 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__29_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Doc.Inline.other"};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__30 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__30_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__30_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__31 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__31_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__31_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___redArg___closed__32 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___redArg___closed__32_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_instInhabitedInline_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Doc_instInhabitedInline_default___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedInline_default___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instInhabitedInline_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedInline_default___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedInline_default___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instInhabitedInline_default___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_instInhabitedInline_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instInhabitedInline_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instAppendInline___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instAppendInline___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instAppendInline___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instAppendInline___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline(lean_object*);
static const lean_array_object l_Lean_Doc_Inline_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_Inline_empty___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_Inline_empty___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Inline_empty___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Doc_Inline_empty___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_Inline_empty___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_Inline_empty___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Inline_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Inline_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty(lean_object*);
static const lean_string_object l_Lean_Doc_instReprListItem_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Doc_instReprListItem_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "contents"};
static const lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Doc_instReprListItem_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__7;
static const lean_string_object l_Lean_Doc_instReprListItem_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem(lean_object*, lean_object*);
static const lean_array_object l_Lean_Doc_instInhabitedListItem_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedListItem_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_instInhabitedListItem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instInhabitedListItem_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem(lean_object*);
static const lean_string_object l_Lean_Doc_instReprDescItem_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Doc_instReprDescItem_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprDescItem_repr___redArg___closed__4;
static const lean_string_object l_Lean_Doc_instReprDescItem_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_Doc_instReprDescItem_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "desc"};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Doc_instInhabitedDescItem_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedListItem_default___redArg___closed__0_value),((lean_object*)&l_Lean_Doc_instInhabitedListItem_default___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedDescItem_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_instInhabitedDescItem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instInhabitedDescItem_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_instReprBlock_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Doc.Block.para"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__2_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Doc.Block.code"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__3_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__5_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Doc.Block.ul"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__6_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Doc.Block.ol"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__12;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Doc.Block.dl"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Doc.Block.blockquote"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__18_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Doc.Block.concat"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__19_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__20_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__21_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Block.other"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__22 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__22_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__23_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___redArg___closed__24 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___redArg___closed__24_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Doc_instInhabitedBlock_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedBlock_default___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instInhabitedBlock_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedBlock_default___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instInhabitedBlock_default___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_instInhabitedBlock_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instInhabitedBlock_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock(lean_object*, lean_object*);
static const lean_array_object l_Lean_Doc_Block_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_Block_empty___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_Block_empty___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Block_empty___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Doc_Block_empty___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_Block_empty___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_Block_empty___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Block_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Block_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_instReprPart_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "title"};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Doc_instReprPart_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__4;
static const lean_string_object l_Lean_Doc_instReprPart_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "titleString"};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Doc_instReprPart_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__7;
static const lean_string_object l_Lean_Doc_instReprPart_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "metadata"};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Doc_instReprPart_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "content"};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Doc_instReprPart_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__12;
static const lean_string_object l_Lean_Doc_instReprPart_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "subParts"};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Doc_instInhabitedPart_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedBlock_default___redArg___closed__0_value),((lean_object*)&l_Lean_Doc_instInhabitedInline_default___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instInhabitedBlock_default___redArg___closed__0_value),((lean_object*)&l_Lean_Doc_instInhabitedBlock_default___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedPart_default___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedPart_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_instInhabitedPart_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instInhabitedPart_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_MathMode_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Doc_MathMode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Doc_MathMode_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Doc_MathMode_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Doc_MathMode_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Doc_MathMode_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Doc_MathMode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Doc_MathMode_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Doc_MathMode_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___redArg(lean_object* v_inline_24_){
_start:
{
lean_inc(v_inline_24_);
return v_inline_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___redArg___boxed(lean_object* v_inline_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Doc_MathMode_inline_elim___redArg(v_inline_25_);
lean_dec(v_inline_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Doc_MathMode_inline_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_inline_30_){
_start:
{
lean_inc(v_inline_30_);
return v_inline_30_;
}
}
LEAN_EXPORT void l_Lean_Doc_MathMode_inline_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_inline_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Doc_MathMode_inline_elim(lean_box(0), v_t_28_, lean_box(0), v_inline_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_inline_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Doc_MathMode_inline_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_inline_35_);
lean_dec(v_inline_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___redArg(lean_object* v_display_38_){
_start:
{
lean_inc(v_display_38_);
return v_display_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___redArg___boxed(lean_object* v_display_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Doc_MathMode_display_elim___redArg(v_display_39_);
lean_dec(v_display_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Doc_MathMode_display_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_display_44_){
_start:
{
lean_inc(v_display_44_);
return v_display_44_;
}
}
LEAN_EXPORT void l_Lean_Doc_MathMode_display_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_display_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Doc_MathMode_display_elim(lean_box(0), v_t_42_, lean_box(0), v_display_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_display_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Doc_MathMode_display_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_display_49_);
lean_dec(v_display_49_);
return v_res_51_;
}
}
static lean_object* _init_l_Lean_Doc_instReprMathMode_repr___closed__4(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(2u);
v___x_59_ = lean_nat_to_int(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Doc_instReprMathMode_repr___closed__5(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_to_int(v___x_60_);
return v___x_61_;
}
}
lean_object* l_Lean_Doc_instReprMathMode_repr(uint8_t v_x_62_, lean_object* v_prec_63_){
_start:
{
lean_object* v___y_65_; lean_object* v___y_72_; 
if (v_x_62_ == 0)
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1024u);
v___x_79_ = lean_nat_dec_le(v___x_78_, v_prec_63_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_65_ = v___x_80_;
goto v___jp_64_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_65_ = v___x_81_;
goto v___jp_64_;
}
}
else
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(1024u);
v___x_83_ = lean_nat_dec_le(v___x_82_, v_prec_63_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_72_ = v___x_84_;
goto v___jp_71_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_72_ = v___x_85_;
goto v___jp_71_;
}
}
v___jp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_66_ = ((lean_object*)(l_Lean_Doc_instReprMathMode_repr___closed__1));
lean_inc(v___y_65_);
v___x_67_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_67_, 0, v___y_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = 0;
v___x_69_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set_uint8(v___x_69_, sizeof(void*)*1, v___x_68_);
v___x_70_ = l_Repr_addAppParen(v___x_69_, v_prec_63_);
return v___x_70_;
}
v___jp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = ((lean_object*)(l_Lean_Doc_instReprMathMode_repr___closed__3));
lean_inc(v___y_72_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___y_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = 0;
v___x_76_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_75_);
v___x_77_ = l_Repr_addAppParen(v___x_76_, v_prec_63_);
return v___x_77_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_instReprMathMode_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_62_ = stack[0].m_num;
lean_object* v_prec_63_ = stack[1].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Lean_Doc_instReprMathMode_repr(v_x_62_, v_prec_63_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprMathMode_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
uint8_t v_x_117__boxed_89_; lean_object* v_res_90_; 
v_x_117__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Lean_Doc_instReprMathMode_repr(v_x_117__boxed_89_, v_prec_88_);
lean_dec(v_prec_88_);
return v_res_90_;
}
}
uint8_t l_Lean_Doc_instBEqMathMode_beq(uint8_t v_x_93_, uint8_t v_y_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_95_ = lean_box(v_x_93_);
v___x_96_ = lean_obj_tag_nat(v___x_95_);
lean_dec(v___x_95_);
v___x_97_ = lean_box(v_y_94_);
v___x_98_ = lean_obj_tag_nat(v___x_97_);
lean_dec(v___x_97_);
v___x_99_ = lean_nat_dec_eq(v___x_96_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqMathMode_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_93_ = stack[0].m_num;
uint8_t v_y_94_ = stack[1].m_num;
uint8_t v_res_100_;
v_res_100_ = l_Lean_Doc_instBEqMathMode_beq(v_x_93_, v_y_94_);
stack->m_num = v_res_100_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqMathMode_beq___boxed(lean_object* v_x_101_, lean_object* v_y_102_){
_start:
{
uint8_t v_x_24__boxed_103_; uint8_t v_y_25__boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_x_24__boxed_103_ = lean_unbox(v_x_101_);
v_y_25__boxed_104_ = lean_unbox(v_y_102_);
v_res_105_ = l_Lean_Doc_instBEqMathMode_beq(v_x_24__boxed_103_, v_y_25__boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
uint64_t l_Lean_Doc_instHashableMathMode_hash(uint8_t v_x_109_){
_start:
{
if (v_x_109_ == 0)
{
uint64_t v___x_110_; 
v___x_110_ = 0ULL;
return v___x_110_;
}
else
{
uint64_t v___x_111_; 
v___x_111_ = 1ULL;
return v___x_111_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_instHashableMathMode_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_109_ = stack[0].m_num;
uint64_t v_res_112_;
v_res_112_ = l_Lean_Doc_instHashableMathMode_hash(v_x_109_);
stack->m_num = v_res_112_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instHashableMathMode_hash___boxed(lean_object* v_x_113_){
_start:
{
uint8_t v_x_28__boxed_114_; uint64_t v_res_115_; lean_object* v_r_116_; 
v_x_28__boxed_114_ = lean_unbox(v_x_113_);
v_res_115_ = l_Lean_Doc_instHashableMathMode_hash(v_x_28__boxed_114_);
v_r_116_ = lean_box_uint64(v_res_115_);
return v_r_116_;
}
}
uint8_t l_Lean_Doc_instOrdMathMode_ord(uint8_t v_x_119_, uint8_t v_y_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_121_ = lean_box(v_x_119_);
v___x_122_ = lean_obj_tag_nat(v___x_121_);
lean_dec(v___x_121_);
v___x_123_ = lean_box(v_y_120_);
v___x_124_ = lean_obj_tag_nat(v___x_123_);
lean_dec(v___x_123_);
v___x_125_ = lean_nat_dec_lt(v___x_122_, v___x_124_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_eq(v___x_122_, v___x_124_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = 2;
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 1;
return v___x_128_;
}
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdMathMode_ord_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_119_ = stack[0].m_num;
uint8_t v_y_120_ = stack[1].m_num;
uint8_t v_res_130_;
v_res_130_ = l_Lean_Doc_instOrdMathMode_ord(v_x_119_, v_y_120_);
stack->m_num = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdMathMode_ord___boxed(lean_object* v_x_131_, lean_object* v_y_132_){
_start:
{
uint8_t v_x_33__boxed_133_; uint8_t v_y_34__boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v_x_33__boxed_133_ = lean_unbox(v_x_131_);
v_y_34__boxed_134_ = lean_unbox(v_y_132_);
v_res_135_ = l_Lean_Doc_instOrdMathMode_ord(v_x_33__boxed_133_, v_y_34__boxed_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl___redArg(lean_object* v_x_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_tag_nat(v_x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl___redArg___boxed(lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Doc_Inline_ctorIdx___impl___redArg(v_x_141_);
lean_dec_ref(v_x_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl(lean_object* v_i_143_, lean_object* v_x_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_tag_nat(v_x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl___boxed(lean_object* v_i_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Doc_Inline_ctorIdx___impl(v_i_146_, v_x_147_);
lean_dec_ref(v_x_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim___redArg(lean_object* v_t_149_, lean_object* v_k_150_){
_start:
{
switch(lean_obj_tag(v_t_149_))
{
case 4:
{
uint8_t v_mode_151_; lean_object* v_string_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_mode_151_ = lean_ctor_get_uint8(v_t_149_, sizeof(void*)*1);
v_string_152_ = lean_ctor_get(v_t_149_, 0);
lean_inc_ref(v_string_152_);
lean_dec_ref_known(v_t_149_, 1);
v___x_153_ = lean_box(v_mode_151_);
v___x_154_ = lean_apply_2(v_k_150_, v___x_153_, v_string_152_);
return v___x_154_;
}
case 6:
{
lean_object* v_content_155_; lean_object* v_url_156_; lean_object* v___x_157_; 
v_content_155_ = lean_ctor_get(v_t_149_, 0);
lean_inc_ref(v_content_155_);
v_url_156_ = lean_ctor_get(v_t_149_, 1);
lean_inc_ref(v_url_156_);
lean_dec_ref_known(v_t_149_, 2);
v___x_157_ = lean_apply_2(v_k_150_, v_content_155_, v_url_156_);
return v___x_157_;
}
case 7:
{
lean_object* v_name_158_; lean_object* v_content_159_; lean_object* v___x_160_; 
v_name_158_ = lean_ctor_get(v_t_149_, 0);
lean_inc_ref(v_name_158_);
v_content_159_ = lean_ctor_get(v_t_149_, 1);
lean_inc_ref(v_content_159_);
lean_dec_ref_known(v_t_149_, 2);
v___x_160_ = lean_apply_2(v_k_150_, v_name_158_, v_content_159_);
return v___x_160_;
}
case 8:
{
lean_object* v_alt_161_; lean_object* v_url_162_; lean_object* v___x_163_; 
v_alt_161_ = lean_ctor_get(v_t_149_, 0);
lean_inc_ref(v_alt_161_);
v_url_162_ = lean_ctor_get(v_t_149_, 1);
lean_inc_ref(v_url_162_);
lean_dec_ref_known(v_t_149_, 2);
v___x_163_ = lean_apply_2(v_k_150_, v_alt_161_, v_url_162_);
return v___x_163_;
}
case 10:
{
lean_object* v_container_164_; lean_object* v_content_165_; lean_object* v___x_166_; 
v_container_164_ = lean_ctor_get(v_t_149_, 0);
lean_inc(v_container_164_);
v_content_165_ = lean_ctor_get(v_t_149_, 1);
lean_inc_ref(v_content_165_);
lean_dec_ref_known(v_t_149_, 2);
v___x_166_ = lean_apply_2(v_k_150_, v_container_164_, v_content_165_);
return v___x_166_;
}
default: 
{
lean_object* v_string_167_; lean_object* v___x_168_; 
v_string_167_ = lean_ctor_get(v_t_149_, 0);
lean_inc_ref(v_string_167_);
lean_dec_ref(v_t_149_);
v___x_168_ = lean_apply_1(v_k_150_, v_string_167_);
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim(lean_object* v_i_169_, lean_object* v_motive__1_170_, lean_object* v_ctorIdx_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_k_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_172_, v_k_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim___boxed(lean_object* v_i_176_, lean_object* v_motive__1_177_, lean_object* v_ctorIdx_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_k_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Doc_Inline_ctorElim(v_i_176_, v_motive__1_177_, v_ctorIdx_178_, v_t_179_, v_h_180_, v_k_181_);
lean_dec(v_ctorIdx_178_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_text_elim___redArg(lean_object* v_t_183_, lean_object* v_text_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_183_, v_text_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_text_elim(lean_object* v_i_186_, lean_object* v_motive__1_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_text_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_188_, v_text_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_emph_elim___redArg(lean_object* v_t_192_, lean_object* v_emph_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_192_, v_emph_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_emph_elim(lean_object* v_i_195_, lean_object* v_motive__1_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_emph_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_197_, v_emph_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_bold_elim___redArg(lean_object* v_t_201_, lean_object* v_bold_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_201_, v_bold_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_bold_elim(lean_object* v_i_204_, lean_object* v_motive__1_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_bold_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_206_, v_bold_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_code_elim___redArg(lean_object* v_t_210_, lean_object* v_code_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_210_, v_code_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_code_elim(lean_object* v_i_213_, lean_object* v_motive__1_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_code_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_215_, v_code_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_math_elim___redArg(lean_object* v_t_219_, lean_object* v_math_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_219_, v_math_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_math_elim(lean_object* v_i_222_, lean_object* v_motive__1_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_math_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_224_, v_math_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_linebreak_elim___redArg(lean_object* v_t_228_, lean_object* v_linebreak_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_228_, v_linebreak_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_linebreak_elim(lean_object* v_i_231_, lean_object* v_motive__1_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_linebreak_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_233_, v_linebreak_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_link_elim___redArg(lean_object* v_t_237_, lean_object* v_link_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_237_, v_link_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_link_elim(lean_object* v_i_240_, lean_object* v_motive__1_241_, lean_object* v_t_242_, lean_object* v_h_243_, lean_object* v_link_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_242_, v_link_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_footnote_elim___redArg(lean_object* v_t_246_, lean_object* v_footnote_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_246_, v_footnote_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_footnote_elim(lean_object* v_i_249_, lean_object* v_motive__1_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_footnote_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_251_, v_footnote_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_image_elim___redArg(lean_object* v_t_255_, lean_object* v_image_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_255_, v_image_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_image_elim(lean_object* v_i_258_, lean_object* v_motive__1_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_image_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_260_, v_image_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_concat_elim___redArg(lean_object* v_t_264_, lean_object* v_concat_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_264_, v_concat_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_concat_elim(lean_object* v_i_267_, lean_object* v_motive__1_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_concat_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_269_, v_concat_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_other_elim___redArg(lean_object* v_t_273_, lean_object* v_other_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_273_, v_other_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_other_elim(lean_object* v_i_276_, lean_object* v_motive__1_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_other_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_278_, v_other_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline_beq___redArg___boxed(lean_object* v_inst_282_, lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_282_, v_x_283_, v_x_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
uint8_t l_Lean_Doc_instBEqInline_beq___redArg(lean_object* v_inst_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v_decide_292_; 
v___x_290_ = lean_obj_tag_nat(v_x_288_);
v___x_291_ = lean_obj_tag_nat(v_x_289_);
v_decide_292_ = lean_nat_dec_eq(v___x_290_, v___x_291_);
if (v_decide_292_ == 0)
{
lean_dec_ref(v_x_289_);
lean_dec_ref(v_x_288_);
lean_dec_ref(v_inst_287_);
return v_decide_292_;
}
else
{
lean_object* v___x_293_; lean_object* v_content_295_; lean_object* v_content_x27_296_; 
lean_inc_ref(v_inst_287_);
v___x_293_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___redArg___boxed), 3, 1);
lean_closure_set(v___x_293_, 0, v_inst_287_);
switch(lean_obj_tag(v_x_288_))
{
case 1:
{
lean_object* v_content_301_; lean_object* v_content_302_; 
lean_dec_ref(v_inst_287_);
v_content_301_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_content_301_);
lean_dec_ref_known(v_x_288_, 1);
v_content_302_ = lean_ctor_get(v_x_289_, 0);
lean_inc_ref(v_content_302_);
lean_dec_ref(v_x_289_);
v_content_295_ = v_content_301_;
v_content_x27_296_ = v_content_302_;
goto v___jp_294_;
}
case 2:
{
lean_object* v_content_303_; lean_object* v_content_304_; 
lean_dec_ref(v_inst_287_);
v_content_303_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_content_303_);
lean_dec_ref_known(v_x_288_, 1);
v_content_304_ = lean_ctor_get(v_x_289_, 0);
lean_inc_ref(v_content_304_);
lean_dec_ref(v_x_289_);
v_content_295_ = v_content_303_;
v_content_x27_296_ = v_content_304_;
goto v___jp_294_;
}
case 4:
{
uint8_t v_mode_305_; lean_object* v_string_306_; uint8_t v_mode_307_; lean_object* v_string_308_; uint8_t v___x_309_; 
lean_dec_ref(v___x_293_);
lean_dec_ref(v_inst_287_);
v_mode_305_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*1);
v_string_306_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_string_306_);
lean_dec_ref_known(v_x_288_, 1);
v_mode_307_ = lean_ctor_get_uint8(v_x_289_, sizeof(void*)*1);
v_string_308_ = lean_ctor_get(v_x_289_, 0);
lean_inc_ref(v_string_308_);
lean_dec_ref(v_x_289_);
v___x_309_ = l_Lean_Doc_instBEqMathMode_beq(v_mode_305_, v_mode_307_);
if (v___x_309_ == 0)
{
lean_dec_ref(v_string_308_);
lean_dec_ref(v_string_306_);
return v___x_309_;
}
else
{
uint8_t v___x_310_; 
v___x_310_ = lean_string_dec_eq(v_string_306_, v_string_308_);
lean_dec_ref(v_string_308_);
lean_dec_ref(v_string_306_);
return v___x_310_;
}
}
case 6:
{
lean_object* v_content_311_; lean_object* v_url_312_; lean_object* v_content_313_; lean_object* v_url_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
lean_dec_ref(v_inst_287_);
v_content_311_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_content_311_);
v_url_312_ = lean_ctor_get(v_x_288_, 1);
lean_inc_ref(v_url_312_);
lean_dec_ref_known(v_x_288_, 2);
v_content_313_ = lean_ctor_get(v_x_289_, 0);
lean_inc_ref(v_content_313_);
v_url_314_ = lean_ctor_get(v_x_289_, 1);
lean_inc_ref(v_url_314_);
lean_dec_ref(v_x_289_);
v___x_315_ = lean_array_get_size(v_content_311_);
v___x_316_ = lean_array_get_size(v_content_313_);
v___x_317_ = lean_nat_dec_eq(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
lean_dec_ref(v_url_314_);
lean_dec_ref(v_content_313_);
lean_dec_ref(v_url_312_);
lean_dec_ref(v_content_311_);
lean_dec_ref(v___x_293_);
return v___x_317_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = l_Array_isEqvAux___redArg(v_content_311_, v_content_313_, v___x_293_, v___x_315_);
lean_dec_ref(v_content_313_);
lean_dec_ref(v_content_311_);
if (v___x_318_ == 0)
{
lean_dec_ref(v_url_314_);
lean_dec_ref(v_url_312_);
return v___x_318_;
}
else
{
uint8_t v___x_319_; 
v___x_319_ = lean_string_dec_eq(v_url_312_, v_url_314_);
lean_dec_ref(v_url_314_);
lean_dec_ref(v_url_312_);
return v___x_319_;
}
}
}
case 7:
{
lean_object* v_name_320_; lean_object* v_content_321_; lean_object* v_name_322_; lean_object* v_content_323_; uint8_t v___x_324_; 
lean_dec_ref(v_inst_287_);
v_name_320_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_name_320_);
v_content_321_ = lean_ctor_get(v_x_288_, 1);
lean_inc_ref(v_content_321_);
lean_dec_ref_known(v_x_288_, 2);
v_name_322_ = lean_ctor_get(v_x_289_, 0);
lean_inc_ref(v_name_322_);
v_content_323_ = lean_ctor_get(v_x_289_, 1);
lean_inc_ref(v_content_323_);
lean_dec_ref(v_x_289_);
v___x_324_ = lean_string_dec_eq(v_name_320_, v_name_322_);
lean_dec_ref(v_name_322_);
lean_dec_ref(v_name_320_);
if (v___x_324_ == 0)
{
lean_dec_ref(v_content_323_);
lean_dec_ref(v_content_321_);
lean_dec_ref(v___x_293_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_325_ = lean_array_get_size(v_content_321_);
v___x_326_ = lean_array_get_size(v_content_323_);
v___x_327_ = lean_nat_dec_eq(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_dec_ref(v_content_323_);
lean_dec_ref(v_content_321_);
lean_dec_ref(v___x_293_);
return v___x_327_;
}
else
{
uint8_t v___x_328_; 
v___x_328_ = l_Array_isEqvAux___redArg(v_content_321_, v_content_323_, v___x_293_, v___x_325_);
lean_dec_ref(v_content_323_);
lean_dec_ref(v_content_321_);
return v___x_328_;
}
}
}
case 8:
{
lean_object* v_alt_329_; lean_object* v_url_330_; lean_object* v_alt_331_; lean_object* v_url_332_; uint8_t v___x_333_; 
lean_dec_ref(v___x_293_);
lean_dec_ref(v_inst_287_);
v_alt_329_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_alt_329_);
v_url_330_ = lean_ctor_get(v_x_288_, 1);
lean_inc_ref(v_url_330_);
lean_dec_ref_known(v_x_288_, 2);
v_alt_331_ = lean_ctor_get(v_x_289_, 0);
lean_inc_ref(v_alt_331_);
v_url_332_ = lean_ctor_get(v_x_289_, 1);
lean_inc_ref(v_url_332_);
lean_dec_ref(v_x_289_);
v___x_333_ = lean_string_dec_eq(v_alt_329_, v_alt_331_);
lean_dec_ref(v_alt_331_);
lean_dec_ref(v_alt_329_);
if (v___x_333_ == 0)
{
lean_dec_ref(v_url_332_);
lean_dec_ref(v_url_330_);
return v___x_333_;
}
else
{
uint8_t v___x_334_; 
v___x_334_ = lean_string_dec_eq(v_url_330_, v_url_332_);
lean_dec_ref(v_url_332_);
lean_dec_ref(v_url_330_);
return v___x_334_;
}
}
case 9:
{
lean_object* v_content_335_; lean_object* v_content_336_; 
lean_dec_ref(v_inst_287_);
v_content_335_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_content_335_);
lean_dec_ref_known(v_x_288_, 1);
v_content_336_ = lean_ctor_get(v_x_289_, 0);
lean_inc_ref(v_content_336_);
lean_dec_ref(v_x_289_);
v_content_295_ = v_content_335_;
v_content_x27_296_ = v_content_336_;
goto v___jp_294_;
}
case 10:
{
lean_object* v_container_337_; lean_object* v_content_338_; lean_object* v_container_339_; lean_object* v_content_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_container_337_ = lean_ctor_get(v_x_288_, 0);
lean_inc(v_container_337_);
v_content_338_ = lean_ctor_get(v_x_288_, 1);
lean_inc_ref(v_content_338_);
lean_dec_ref_known(v_x_288_, 2);
v_container_339_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_container_339_);
v_content_340_ = lean_ctor_get(v_x_289_, 1);
lean_inc_ref(v_content_340_);
lean_dec_ref(v_x_289_);
v___x_341_ = lean_apply_2(v_inst_287_, v_container_337_, v_container_339_);
v___x_342_ = lean_unbox(v___x_341_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
lean_dec_ref(v_content_340_);
lean_dec_ref(v_content_338_);
lean_dec_ref(v___x_293_);
v___x_343_ = lean_unbox(v___x_341_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = lean_array_get_size(v_content_338_);
v___x_345_ = lean_array_get_size(v_content_340_);
v___x_346_ = lean_nat_dec_eq(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_dec_ref(v_content_340_);
lean_dec_ref(v_content_338_);
lean_dec_ref(v___x_293_);
return v___x_346_;
}
else
{
uint8_t v___x_347_; 
v___x_347_ = l_Array_isEqvAux___redArg(v_content_338_, v_content_340_, v___x_293_, v___x_344_);
lean_dec_ref(v_content_340_);
lean_dec_ref(v_content_338_);
return v___x_347_;
}
}
}
default: 
{
lean_object* v_string_348_; lean_object* v_string_349_; uint8_t v___x_350_; 
lean_dec_ref(v___x_293_);
lean_dec_ref(v_inst_287_);
v_string_348_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_string_348_);
lean_dec_ref(v_x_288_);
v_string_349_ = lean_ctor_get(v_x_289_, 0);
lean_inc_ref(v_string_349_);
lean_dec_ref(v_x_289_);
v___x_350_ = lean_string_dec_eq(v_string_348_, v_string_349_);
lean_dec_ref(v_string_349_);
lean_dec_ref(v_string_348_);
return v___x_350_;
}
}
v___jp_294_:
{
lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_297_ = lean_array_get_size(v_content_295_);
v___x_298_ = lean_array_get_size(v_content_x27_296_);
v___x_299_ = lean_nat_dec_eq(v___x_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_dec_ref(v_content_x27_296_);
lean_dec_ref(v_content_295_);
lean_dec_ref(v___x_293_);
return v___x_299_;
}
else
{
uint8_t v___x_300_; 
v___x_300_ = l_Array_isEqvAux___redArg(v_content_295_, v_content_x27_296_, v___x_293_, v___x_297_);
lean_dec_ref(v_content_x27_296_);
lean_dec_ref(v_content_295_);
return v___x_300_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqInline_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_287_ = stack[0].m_obj;
lean_object* v_x_288_ = stack[1].m_obj;
lean_object* v_x_289_ = stack[2].m_obj;
uint8_t v_res_351_;
v_res_351_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_287_, v_x_288_, v_x_289_);
stack->m_num = v_res_351_;
}
uint8_t l_Lean_Doc_instBEqInline_beq(lean_object* v_i_352_, lean_object* v_inst_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_353_, v_x_354_, v_x_355_);
return v___x_356_;
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqInline_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_353_ = stack[1].m_obj;
lean_object* v_x_354_ = stack[2].m_obj;
lean_object* v_x_355_ = stack[3].m_obj;
uint8_t v_res_357_;
v_res_357_ = l_Lean_Doc_instBEqInline_beq(lean_box(0), v_inst_353_, v_x_354_, v_x_355_);
stack->m_num = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline_beq___boxed(lean_object* v_i_358_, lean_object* v_inst_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Lean_Doc_instBEqInline_beq(v_i_358_, v_inst_359_, v_x_360_, v_x_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline___redArg(lean_object* v_inst_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_365_, 0, lean_box(0));
lean_closure_set(v___x_365_, 1, v_inst_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline(lean_object* v_i_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_368_, 0, lean_box(0));
lean_closure_set(v___x_368_, 1, v_inst_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___redArg___boxed(lean_object* v_inst_369_, lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_369_, v_x_370_, v_x_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
uint8_t l_Lean_Doc_instOrdInline_ord___redArg(lean_object* v_inst_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_377_ = lean_obj_tag_nat(v_x_375_);
v___x_378_ = lean_obj_tag_nat(v_x_376_);
v___x_379_ = lean_nat_dec_lt(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = lean_nat_dec_eq(v___x_377_, v___x_378_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; 
lean_dec_ref(v_x_376_);
lean_dec_ref(v_x_375_);
lean_dec_ref(v_inst_374_);
v___x_381_ = 2;
return v___x_381_;
}
else
{
lean_object* v___x_382_; lean_object* v_content_384_; lean_object* v_content_x27_385_; 
lean_inc_ref(v_inst_374_);
v___x_382_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___redArg___boxed), 3, 1);
lean_closure_set(v___x_382_, 0, v_inst_374_);
switch(lean_obj_tag(v_x_375_))
{
case 1:
{
lean_object* v_content_388_; lean_object* v_content_389_; 
lean_dec_ref(v_inst_374_);
v_content_388_ = lean_ctor_get(v_x_375_, 0);
lean_inc_ref(v_content_388_);
lean_dec_ref_known(v_x_375_, 1);
v_content_389_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_389_);
lean_dec_ref(v_x_376_);
v_content_384_ = v_content_388_;
v_content_x27_385_ = v_content_389_;
goto v___jp_383_;
}
case 2:
{
lean_object* v_content_390_; lean_object* v_content_391_; 
lean_dec_ref(v_inst_374_);
v_content_390_ = lean_ctor_get(v_x_375_, 0);
lean_inc_ref(v_content_390_);
lean_dec_ref_known(v_x_375_, 1);
v_content_391_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_391_);
lean_dec_ref(v_x_376_);
v_content_384_ = v_content_390_;
v_content_x27_385_ = v_content_391_;
goto v___jp_383_;
}
case 4:
{
uint8_t v_mode_392_; lean_object* v_string_393_; uint8_t v_mode_394_; lean_object* v_string_395_; uint8_t v___x_396_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_inst_374_);
v_mode_392_ = lean_ctor_get_uint8(v_x_375_, sizeof(void*)*1);
v_string_393_ = lean_ctor_get(v_x_375_, 0);
lean_inc_ref(v_string_393_);
lean_dec_ref_known(v_x_375_, 1);
v_mode_394_ = lean_ctor_get_uint8(v_x_376_, sizeof(void*)*1);
v_string_395_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_string_395_);
lean_dec_ref(v_x_376_);
v___x_396_ = l_Lean_Doc_instOrdMathMode_ord(v_mode_392_, v_mode_394_);
if (v___x_396_ == 1)
{
uint8_t v___x_397_; 
v___x_397_ = lean_string_compare(v_string_393_, v_string_395_);
lean_dec_ref(v_string_395_);
lean_dec_ref(v_string_393_);
return v___x_397_;
}
else
{
lean_dec_ref(v_string_395_);
lean_dec_ref(v_string_393_);
return v___x_396_;
}
}
case 6:
{
lean_object* v_content_398_; lean_object* v_url_399_; lean_object* v_content_400_; lean_object* v_url_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
lean_dec_ref(v_inst_374_);
v_content_398_ = lean_ctor_get(v_x_375_, 0);
lean_inc_ref(v_content_398_);
v_url_399_ = lean_ctor_get(v_x_375_, 1);
lean_inc_ref(v_url_399_);
lean_dec_ref_known(v_x_375_, 2);
v_content_400_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_400_);
v_url_401_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_url_401_);
lean_dec_ref(v_x_376_);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_382_, v_content_398_, v_content_400_, v___x_402_);
lean_dec_ref(v_content_400_);
lean_dec_ref(v_content_398_);
if (v___x_403_ == 1)
{
uint8_t v___x_404_; 
v___x_404_ = lean_string_compare(v_url_399_, v_url_401_);
lean_dec_ref(v_url_401_);
lean_dec_ref(v_url_399_);
return v___x_404_;
}
else
{
lean_dec_ref(v_url_401_);
lean_dec_ref(v_url_399_);
return v___x_403_;
}
}
case 7:
{
lean_object* v_name_405_; lean_object* v_content_406_; lean_object* v_name_407_; lean_object* v_content_408_; uint8_t v___x_409_; 
lean_dec_ref(v_inst_374_);
v_name_405_ = lean_ctor_get(v_x_375_, 0);
lean_inc_ref(v_name_405_);
v_content_406_ = lean_ctor_get(v_x_375_, 1);
lean_inc_ref(v_content_406_);
lean_dec_ref_known(v_x_375_, 2);
v_name_407_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_name_407_);
v_content_408_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_content_408_);
lean_dec_ref(v_x_376_);
v___x_409_ = lean_string_compare(v_name_405_, v_name_407_);
lean_dec_ref(v_name_407_);
lean_dec_ref(v_name_405_);
if (v___x_409_ == 1)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_382_, v_content_406_, v_content_408_, v___x_410_);
lean_dec_ref(v_content_408_);
lean_dec_ref(v_content_406_);
return v___x_411_;
}
else
{
lean_dec_ref(v_content_408_);
lean_dec_ref(v_content_406_);
lean_dec_ref(v___x_382_);
return v___x_409_;
}
}
case 8:
{
lean_object* v_alt_412_; lean_object* v_url_413_; lean_object* v_alt_414_; lean_object* v_url_415_; uint8_t v___x_416_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_inst_374_);
v_alt_412_ = lean_ctor_get(v_x_375_, 0);
lean_inc_ref(v_alt_412_);
v_url_413_ = lean_ctor_get(v_x_375_, 1);
lean_inc_ref(v_url_413_);
lean_dec_ref_known(v_x_375_, 2);
v_alt_414_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_alt_414_);
v_url_415_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_url_415_);
lean_dec_ref(v_x_376_);
v___x_416_ = lean_string_compare(v_alt_412_, v_alt_414_);
lean_dec_ref(v_alt_414_);
lean_dec_ref(v_alt_412_);
if (v___x_416_ == 1)
{
uint8_t v___x_417_; 
v___x_417_ = lean_string_compare(v_url_413_, v_url_415_);
lean_dec_ref(v_url_415_);
lean_dec_ref(v_url_413_);
return v___x_417_;
}
else
{
lean_dec_ref(v_url_415_);
lean_dec_ref(v_url_413_);
return v___x_416_;
}
}
case 9:
{
lean_object* v_content_418_; lean_object* v_content_419_; 
lean_dec_ref(v_inst_374_);
v_content_418_ = lean_ctor_get(v_x_375_, 0);
lean_inc_ref(v_content_418_);
lean_dec_ref_known(v_x_375_, 1);
v_content_419_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_419_);
lean_dec_ref(v_x_376_);
v_content_384_ = v_content_418_;
v_content_x27_385_ = v_content_419_;
goto v___jp_383_;
}
case 10:
{
lean_object* v_container_420_; lean_object* v_content_421_; lean_object* v_container_422_; lean_object* v_content_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_container_420_ = lean_ctor_get(v_x_375_, 0);
lean_inc(v_container_420_);
v_content_421_ = lean_ctor_get(v_x_375_, 1);
lean_inc_ref(v_content_421_);
lean_dec_ref_known(v_x_375_, 2);
v_container_422_ = lean_ctor_get(v_x_376_, 0);
lean_inc(v_container_422_);
v_content_423_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_content_423_);
lean_dec_ref(v_x_376_);
v___x_424_ = lean_apply_2(v_inst_374_, v_container_420_, v_container_422_);
v___x_425_ = lean_unbox(v___x_424_);
if (v___x_425_ == 1)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_382_, v_content_421_, v_content_423_, v___x_426_);
lean_dec_ref(v_content_423_);
lean_dec_ref(v_content_421_);
return v___x_427_;
}
else
{
uint8_t v___x_428_; 
lean_dec_ref(v_content_423_);
lean_dec_ref(v_content_421_);
lean_dec_ref(v___x_382_);
v___x_428_ = lean_unbox(v___x_424_);
return v___x_428_;
}
}
default: 
{
lean_object* v_string_429_; lean_object* v_string_430_; uint8_t v___x_431_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_inst_374_);
v_string_429_ = lean_ctor_get(v_x_375_, 0);
lean_inc_ref(v_string_429_);
lean_dec_ref(v_x_375_);
v_string_430_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_string_430_);
lean_dec_ref(v_x_376_);
v___x_431_ = lean_string_compare(v_string_429_, v_string_430_);
lean_dec_ref(v_string_430_);
lean_dec_ref(v_string_429_);
return v___x_431_;
}
}
v___jp_383_:
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_382_, v_content_384_, v_content_x27_385_, v___x_386_);
lean_dec_ref(v_content_x27_385_);
lean_dec_ref(v_content_384_);
return v___x_387_;
}
}
}
else
{
uint8_t v___x_432_; 
lean_dec_ref(v_x_376_);
lean_dec_ref(v_x_375_);
lean_dec_ref(v_inst_374_);
v___x_432_ = 0;
return v___x_432_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdInline_ord___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_374_ = stack[0].m_obj;
lean_object* v_x_375_ = stack[1].m_obj;
lean_object* v_x_376_ = stack[2].m_obj;
uint8_t v_res_433_;
v_res_433_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_374_, v_x_375_, v_x_376_);
stack->m_num = v_res_433_;
}
uint8_t l_Lean_Doc_instOrdInline_ord(lean_object* v_i_434_, lean_object* v_inst_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_435_, v_x_436_, v_x_437_);
return v___x_438_;
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdInline_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_435_ = stack[1].m_obj;
lean_object* v_x_436_ = stack[2].m_obj;
lean_object* v_x_437_ = stack[3].m_obj;
uint8_t v_res_439_;
v_res_439_ = l_Lean_Doc_instOrdInline_ord(lean_box(0), v_inst_435_, v_x_436_, v_x_437_);
stack->m_num = v_res_439_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___boxed(lean_object* v_i_440_, lean_object* v_inst_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Lean_Doc_instOrdInline_ord(v_i_440_, v_inst_441_, v_x_442_, v_x_443_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline___redArg(lean_object* v_inst_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_447_, 0, lean_box(0));
lean_closure_set(v___x_447_, 1, v_inst_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline(lean_object* v_i_448_, lean_object* v_inst_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_450_, 0, lean_box(0));
lean_closure_set(v___x_450_, 1, v_inst_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg___boxed(lean_object* v_inst_517_, lean_object* v_x_518_, lean_object* v_prec_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_517_, v_x_518_, v_prec_519_);
lean_dec(v_prec_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg(lean_object* v_inst_521_, lean_object* v_x_522_, lean_object* v_prec_523_){
_start:
{
lean_object* v_localinst_524_; 
lean_inc_ref(v_inst_521_);
v_localinst_524_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_524_, 0, v_inst_521_);
switch(lean_obj_tag(v_x_522_))
{
case 0:
{
lean_object* v_string_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_localinst_524_);
lean_dec_ref(v_inst_521_);
v_string_525_ = lean_ctor_get(v_x_522_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_545_ == 0)
{
v___x_527_ = v_x_522_;
v_isShared_528_ = v_isSharedCheck_545_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_string_525_);
lean_dec(v_x_522_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_545_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___y_530_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(1024u);
v___x_542_ = lean_nat_dec_le(v___x_541_, v_prec_523_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_530_ = v___x_543_;
goto v___jp_529_;
}
else
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_530_ = v___x_544_;
goto v___jp_529_;
}
v___jp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_531_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__2));
v___x_532_ = l_String_quote(v_string_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 3);
lean_ctor_set(v___x_527_, 0, v___x_532_);
v___x_534_ = v___x_527_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_540_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_531_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_inc(v___y_530_);
v___x_536_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_530_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = 0;
v___x_538_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*1, v___x_537_);
v___x_539_ = l_Repr_addAppParen(v___x_538_, v_prec_523_);
return v___x_539_;
}
}
}
}
case 1:
{
lean_object* v_content_546_; lean_object* v___y_548_; lean_object* v___x_556_; uint8_t v___x_557_; 
lean_dec_ref(v_inst_521_);
v_content_546_ = lean_ctor_get(v_x_522_, 0);
lean_inc_ref(v_content_546_);
lean_dec_ref_known(v_x_522_, 1);
v___x_556_ = lean_unsigned_to_nat(1024u);
v___x_557_ = lean_nat_dec_le(v___x_556_, v_prec_523_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_548_ = v___x_558_;
goto v___jp_547_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_548_ = v___x_559_;
goto v___jp_547_;
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_549_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__5));
v___x_550_ = l_Array_repr___redArg(v_localinst_524_, v_content_546_);
v___x_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
lean_inc(v___y_548_);
v___x_552_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_552_, 0, v___y_548_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = 0;
v___x_554_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*1, v___x_553_);
v___x_555_ = l_Repr_addAppParen(v___x_554_, v_prec_523_);
return v___x_555_;
}
}
case 2:
{
lean_object* v_content_560_; lean_object* v___y_562_; lean_object* v___x_570_; uint8_t v___x_571_; 
lean_dec_ref(v_inst_521_);
v_content_560_ = lean_ctor_get(v_x_522_, 0);
lean_inc_ref(v_content_560_);
lean_dec_ref_known(v_x_522_, 1);
v___x_570_ = lean_unsigned_to_nat(1024u);
v___x_571_ = lean_nat_dec_le(v___x_570_, v_prec_523_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
v___x_572_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_562_ = v___x_572_;
goto v___jp_561_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_562_ = v___x_573_;
goto v___jp_561_;
}
v___jp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_563_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__8));
v___x_564_ = l_Array_repr___redArg(v_localinst_524_, v_content_560_);
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
lean_inc(v___y_562_);
v___x_566_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_566_, 0, v___y_562_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = 0;
v___x_568_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*1, v___x_567_);
v___x_569_ = l_Repr_addAppParen(v___x_568_, v_prec_523_);
return v___x_569_;
}
}
case 3:
{
lean_object* v_string_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v_localinst_524_);
lean_dec_ref(v_inst_521_);
v_string_574_ = lean_ctor_get(v_x_522_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_594_ == 0)
{
v___x_576_ = v_x_522_;
v_isShared_577_ = v_isSharedCheck_594_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_string_574_);
lean_dec(v_x_522_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_594_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___y_579_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(1024u);
v___x_591_ = lean_nat_dec_le(v___x_590_, v_prec_523_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_579_ = v___x_592_;
goto v___jp_578_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_579_ = v___x_593_;
goto v___jp_578_;
}
v___jp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_580_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__11));
v___x_581_ = l_String_quote(v_string_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_581_);
v___x_583_ = v___x_576_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_589_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_580_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
lean_inc(v___y_579_);
v___x_585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_585_, 0, v___y_579_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = 0;
v___x_587_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*1, v___x_586_);
v___x_588_ = l_Repr_addAppParen(v___x_587_, v_prec_523_);
return v___x_588_;
}
}
}
}
case 4:
{
uint8_t v_mode_595_; lean_object* v_string_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_localinst_524_);
lean_dec_ref(v_inst_521_);
v_mode_595_ = lean_ctor_get_uint8(v_x_522_, sizeof(void*)*1);
v_string_596_ = lean_ctor_get(v_x_522_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_621_ == 0)
{
v___x_598_ = v_x_522_;
v_isShared_599_ = v_isSharedCheck_621_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_string_596_);
lean_dec(v_x_522_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_621_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___y_601_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(1024u);
v___x_618_ = lean_nat_dec_le(v___x_617_, v_prec_523_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
v___x_619_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_601_ = v___x_619_;
goto v___jp_600_;
}
else
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_601_ = v___x_620_;
goto v___jp_600_;
}
v___jp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; lean_object* v___x_614_; 
v___x_602_ = lean_box(1);
v___x_603_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__14));
v___x_604_ = lean_unsigned_to_nat(1024u);
v___x_605_ = l_Lean_Doc_instReprMathMode_repr(v_mode_595_, v___x_604_);
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_603_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_602_);
v___x_608_ = l_String_quote(v_string_596_);
v___x_609_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_607_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
lean_inc(v___y_601_);
v___x_611_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_611_, 0, v___y_601_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = 0;
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 6);
lean_ctor_set(v___x_598_, 0, v___x_611_);
v___x_614_ = v___x_598_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_611_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*1, v___x_612_);
v___x_615_ = l_Repr_addAppParen(v___x_614_, v_prec_523_);
return v___x_615_;
}
}
}
}
case 5:
{
lean_object* v_string_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_localinst_524_);
lean_dec_ref(v_inst_521_);
v_string_622_ = lean_ctor_get(v_x_522_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_642_ == 0)
{
v___x_624_ = v_x_522_;
v_isShared_625_ = v_isSharedCheck_642_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_string_622_);
lean_dec(v_x_522_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_642_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___y_627_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1024u);
v___x_639_ = lean_nat_dec_le(v___x_638_, v_prec_523_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_627_ = v___x_640_;
goto v___jp_626_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_627_ = v___x_641_;
goto v___jp_626_;
}
v___jp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__17));
v___x_629_ = l_String_quote(v_string_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 3);
lean_ctor_set(v___x_624_, 0, v___x_629_);
v___x_631_ = v___x_624_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_637_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_628_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
lean_inc(v___y_627_);
v___x_633_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_633_, 0, v___y_627_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = 0;
v___x_635_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_634_);
v___x_636_ = l_Repr_addAppParen(v___x_635_, v_prec_523_);
return v___x_636_;
}
}
}
}
case 6:
{
lean_object* v_content_643_; lean_object* v_url_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v_inst_521_);
v_content_643_ = lean_ctor_get(v_x_522_, 0);
v_url_644_ = lean_ctor_get(v_x_522_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_668_ == 0)
{
v___x_646_ = v_x_522_;
v_isShared_647_ = v_isSharedCheck_668_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_url_644_);
lean_inc(v_content_643_);
lean_dec(v_x_522_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_668_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___y_649_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(1024u);
v___x_665_ = lean_nat_dec_le(v___x_664_, v_prec_523_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_649_ = v___x_666_;
goto v___jp_648_;
}
else
{
lean_object* v___x_667_; 
v___x_667_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_649_ = v___x_667_;
goto v___jp_648_;
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_650_ = lean_box(1);
v___x_651_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__20));
v___x_652_ = l_Array_repr___redArg(v_localinst_524_, v_content_643_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 5);
lean_ctor_set(v___x_646_, 1, v___x_652_);
lean_ctor_set(v___x_646_, 0, v___x_651_);
v___x_654_ = v___x_646_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_652_);
v___x_654_ = v_reuseFailAlloc_663_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_650_);
v___x_656_ = l_String_quote(v_url_644_);
v___x_657_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
v___x_658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_655_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
lean_inc(v___y_649_);
v___x_659_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_659_, 0, v___y_649_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = 0;
v___x_661_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set_uint8(v___x_661_, sizeof(void*)*1, v___x_660_);
v___x_662_ = l_Repr_addAppParen(v___x_661_, v_prec_523_);
return v___x_662_;
}
}
}
}
case 7:
{
lean_object* v_name_669_; lean_object* v_content_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v_inst_521_);
v_name_669_ = lean_ctor_get(v_x_522_, 0);
v_content_670_ = lean_ctor_get(v_x_522_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_694_ == 0)
{
v___x_672_ = v_x_522_;
v_isShared_673_ = v_isSharedCheck_694_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_content_670_);
lean_inc(v_name_669_);
lean_dec(v_x_522_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_694_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___y_675_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_unsigned_to_nat(1024u);
v___x_691_ = lean_nat_dec_le(v___x_690_, v_prec_523_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; 
v___x_692_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_675_ = v___x_692_;
goto v___jp_674_;
}
else
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_675_ = v___x_693_;
goto v___jp_674_;
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_676_ = lean_box(1);
v___x_677_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__23));
v___x_678_ = l_String_quote(v_name_669_);
v___x_679_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 5);
lean_ctor_set(v___x_672_, 1, v___x_679_);
lean_ctor_set(v___x_672_, 0, v___x_677_);
v___x_681_ = v___x_672_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_689_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___x_676_);
v___x_683_ = l_Array_repr___redArg(v_localinst_524_, v_content_670_);
v___x_684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
lean_inc(v___y_675_);
v___x_685_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_685_, 0, v___y_675_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = 0;
v___x_687_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*1, v___x_686_);
v___x_688_ = l_Repr_addAppParen(v___x_687_, v_prec_523_);
return v___x_688_;
}
}
}
}
case 8:
{
lean_object* v_alt_695_; lean_object* v_url_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_localinst_524_);
lean_dec_ref(v_inst_521_);
v_alt_695_ = lean_ctor_get(v_x_522_, 0);
v_url_696_ = lean_ctor_get(v_x_522_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_721_ == 0)
{
v___x_698_ = v_x_522_;
v_isShared_699_ = v_isSharedCheck_721_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_url_696_);
lean_inc(v_alt_695_);
lean_dec(v_x_522_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_721_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___y_701_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = lean_unsigned_to_nat(1024u);
v___x_718_ = lean_nat_dec_le(v___x_717_, v_prec_523_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_701_ = v___x_719_;
goto v___jp_700_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_701_ = v___x_720_;
goto v___jp_700_;
}
v___jp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_702_ = lean_box(1);
v___x_703_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__26));
v___x_704_ = l_String_quote(v_alt_695_);
v___x_705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 5);
lean_ctor_set(v___x_698_, 1, v___x_705_);
lean_ctor_set(v___x_698_, 0, v___x_703_);
v___x_707_ = v___x_698_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_705_);
v___x_707_ = v_reuseFailAlloc_716_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v___x_702_);
v___x_709_ = l_String_quote(v_url_696_);
v___x_710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
v___x_711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_708_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
lean_inc(v___y_701_);
v___x_712_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_712_, 0, v___y_701_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = 0;
v___x_714_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*1, v___x_713_);
v___x_715_ = l_Repr_addAppParen(v___x_714_, v_prec_523_);
return v___x_715_;
}
}
}
}
case 9:
{
lean_object* v_content_722_; lean_object* v___y_724_; lean_object* v___x_732_; uint8_t v___x_733_; 
lean_dec_ref(v_inst_521_);
v_content_722_ = lean_ctor_get(v_x_522_, 0);
lean_inc_ref(v_content_722_);
lean_dec_ref_known(v_x_522_, 1);
v___x_732_ = lean_unsigned_to_nat(1024u);
v___x_733_ = lean_nat_dec_le(v___x_732_, v_prec_523_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
v___x_734_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_724_ = v___x_734_;
goto v___jp_723_;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_724_ = v___x_735_;
goto v___jp_723_;
}
v___jp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_725_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__29));
v___x_726_ = l_Array_repr___redArg(v_localinst_524_, v_content_722_);
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
lean_inc(v___y_724_);
v___x_728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_728_, 0, v___y_724_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = 0;
v___x_730_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*1, v___x_729_);
v___x_731_ = l_Repr_addAppParen(v___x_730_, v_prec_523_);
return v___x_731_;
}
}
default: 
{
lean_object* v_container_736_; lean_object* v_content_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_761_; 
v_container_736_ = lean_ctor_get(v_x_522_, 0);
v_content_737_ = lean_ctor_get(v_x_522_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_761_ == 0)
{
v___x_739_ = v_x_522_;
v_isShared_740_ = v_isSharedCheck_761_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_content_737_);
lean_inc(v_container_736_);
lean_dec(v_x_522_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_761_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___y_742_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(1024u);
v___x_758_ = lean_nat_dec_le(v___x_757_, v_prec_523_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
v___x_759_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_742_ = v___x_759_;
goto v___jp_741_;
}
else
{
lean_object* v___x_760_; 
v___x_760_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_742_ = v___x_760_;
goto v___jp_741_;
}
v___jp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_743_ = lean_box(1);
v___x_744_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__32));
v___x_745_ = lean_unsigned_to_nat(1024u);
v___x_746_ = lean_apply_2(v_inst_521_, v_container_736_, v___x_745_);
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 5);
lean_ctor_set(v___x_739_, 1, v___x_746_);
lean_ctor_set(v___x_739_, 0, v___x_744_);
v___x_748_ = v___x_739_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_746_);
v___x_748_ = v_reuseFailAlloc_756_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___x_743_);
v___x_750_ = l_Array_repr___redArg(v_localinst_524_, v_content_737_);
v___x_751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
lean_inc(v___y_742_);
v___x_752_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_752_, 0, v___y_742_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = 0;
v___x_754_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*1, v___x_753_);
v___x_755_ = l_Repr_addAppParen(v___x_754_, v_prec_523_);
return v___x_755_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr(lean_object* v_i_762_, lean_object* v_inst_763_, lean_object* v_x_764_, lean_object* v_prec_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_763_, v_x_764_, v_prec_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___boxed(lean_object* v_i_767_, lean_object* v_inst_768_, lean_object* v_x_769_, lean_object* v_prec_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Doc_instReprInline_repr(v_i_767_, v_inst_768_, v_x_769_, v_prec_770_);
lean_dec(v_prec_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline___redArg(lean_object* v_inst_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_773_, 0, lean_box(0));
lean_closure_set(v___x_773_, 1, v_inst_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline(lean_object* v_i_774_, lean_object* v_inst_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_776_, 0, lean_box(0));
lean_closure_set(v___x_776_, 1, v_inst_775_);
return v___x_776_;
}
}
lean_object* l_Lean_Doc_instInhabitedInline_default___redArg(){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = ((lean_object*)(l_Lean_Doc_instInhabitedInline_default___redArg___closed__1));
return v___x_781_;
}
}
LEAN_EXPORT void l_Lean_Doc_instInhabitedInline_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_782_;
v_res_782_ = l_Lean_Doc_instInhabitedInline_default___redArg();
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg___boxed(lean_object* v___dummy_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Doc_instInhabitedInline_default___redArg();
return v_res_784_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedInline_default___closed__0(void){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Doc_instInhabitedInline_default___redArg();
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default(lean_object* v_i_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_787_;
}
}
lean_object* l_Lean_Doc_instInhabitedInline___redArg(){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_789_;
}
}
LEAN_EXPORT void l_Lean_Doc_instInhabitedInline___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_790_;
v_res_790_ = l_Lean_Doc_instInhabitedInline___redArg();
stack->m_obj
 = v_res_790_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg___boxed(lean_object* v___dummy_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Doc_instInhabitedInline___redArg();
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline(lean_object* v_a_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg(lean_object* v_x_795_){
_start:
{
lean_inc_ref(v_x_795_);
return v_x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg___boxed(lean_object* v_x_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_Doc_Inline_cast___redArg(v_x_796_);
lean_dec_ref(v_x_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast(lean_object* v_i_798_, lean_object* v_i_x27_799_, lean_object* v_inlines__eq_800_, lean_object* v_x_801_){
_start:
{
lean_inc_ref(v_x_801_);
return v_x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___boxed(lean_object* v_i_802_, lean_object* v_i_x27_803_, lean_object* v_inlines__eq_804_, lean_object* v_x_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Doc_Inline_cast(v_i_802_, v_i_x27_803_, v_inlines__eq_804_, v_x_805_);
lean_dec_ref(v_x_805_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___lam__0(lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
if (lean_obj_tag(v_x_807_) == 9)
{
lean_object* v_content_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_content_809_ = lean_ctor_get(v_x_807_, 0);
v___x_810_ = lean_array_get_size(v_content_809_);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_nat_dec_eq(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
if (lean_obj_tag(v_x_808_) == 9)
{
lean_object* v_content_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_823_; 
v_content_813_ = lean_ctor_get(v_x_808_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_823_ == 0)
{
v___x_815_ = v_x_808_;
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_content_813_);
lean_dec(v_x_808_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = lean_array_get_size(v_content_813_);
v___x_818_ = lean_nat_dec_eq(v___x_817_, v___x_811_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_821_; 
lean_inc_ref(v_content_809_);
lean_dec_ref_known(v_x_807_, 1);
v___x_819_ = l_Array_append___redArg(v_content_809_, v_content_813_);
lean_dec_ref(v_content_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_819_);
v___x_821_ = v___x_815_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_del_object(v___x_815_);
lean_dec_ref(v_content_813_);
return v_x_807_;
}
}
}
else
{
lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_831_; 
lean_inc_ref(v_content_809_);
v_isSharedCheck_831_ = !lean_is_exclusive(v_x_807_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v_x_807_, 0);
lean_dec(v_unused_832_);
v___x_825_ = v_x_807_;
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
else
{
lean_dec(v_x_807_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_array_push(v_content_809_, v_x_808_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_dec_ref_known(v_x_807_, 1);
return v_x_808_;
}
}
else
{
if (lean_obj_tag(v_x_808_) == 9)
{
lean_object* v_content_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_847_; 
v_content_833_ = lean_ctor_get(v_x_808_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_847_ == 0)
{
v___x_835_ = v_x_808_;
v_isShared_836_ = v_isSharedCheck_847_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_content_833_);
lean_dec(v_x_808_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_847_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_837_ = lean_array_get_size(v_content_833_);
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_nat_dec_eq(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_mk_empty_array_with_capacity(v___x_840_);
v___x_842_ = lean_array_push(v___x_841_, v_x_807_);
v___x_843_ = l_Array_append___redArg(v___x_842_, v_content_833_);
lean_dec_ref(v_content_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_843_);
v___x_845_ = v___x_835_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_del_object(v___x_835_);
lean_dec_ref(v_content_833_);
return v_x_807_;
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_848_ = lean_unsigned_to_nat(2u);
v___x_849_ = lean_mk_empty_array_with_capacity(v___x_848_);
v___x_850_ = lean_array_push(v___x_849_, v_x_807_);
v___x_851_ = lean_array_push(v___x_850_, v_x_808_);
v___x_852_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
}
lean_object* l_Lean_Doc_instAppendInline___redArg(){
_start:
{
lean_object* v___f_855_; 
v___f_855_ = ((lean_object*)(l_Lean_Doc_instAppendInline___redArg___closed__0));
return v___f_855_;
}
}
LEAN_EXPORT void l_Lean_Doc_instAppendInline___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_856_;
v_res_856_ = l_Lean_Doc_instAppendInline___redArg();
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___boxed(lean_object* v___dummy_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Doc_instAppendInline___redArg();
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline(lean_object* v_i_859_){
_start:
{
lean_object* v___f_860_; 
v___f_860_ = ((lean_object*)(l_Lean_Doc_instAppendInline___redArg___closed__0));
return v___f_860_;
}
}
lean_object* l_Lean_Doc_Inline_empty___redArg(){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = ((lean_object*)(l_Lean_Doc_Inline_empty___redArg___closed__1));
return v___x_866_;
}
}
LEAN_EXPORT void l_Lean_Doc_Inline_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_867_;
v_res_867_ = l_Lean_Doc_Inline_empty___redArg();
stack->m_obj
 = v_res_867_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg___boxed(lean_object* v___dummy_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Doc_Inline_empty___redArg();
return v_res_869_;
}
}
static lean_object* _init_l_Lean_Doc_Inline_empty___closed__0(void){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Doc_Inline_empty___redArg();
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty(lean_object* v_i_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = lean_obj_once(&l_Lean_Doc_Inline_empty___closed__0, &l_Lean_Doc_Inline_empty___closed__0_once, _init_l_Lean_Doc_Inline_empty___closed__0);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_unsigned_to_nat(12u);
v___x_887_ = lean_nat_to_int(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__0));
v___x_890_ = lean_string_length(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9);
v___x_892_ = lean_nat_to_int(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___redArg(lean_object* v_inst_897_, lean_object* v_x_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_899_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__6));
v___x_900_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_901_ = l_Array_repr___redArg(v_inst_897_, v_x_898_);
v___x_902_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = 0;
v___x_904_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*1, v___x_903_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_899_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_907_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_905_);
v___x_909_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_906_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1, v___x_903_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr(lean_object* v_00_u03b1_913_, lean_object* v_inst_914_, lean_object* v_x_915_, lean_object* v_prec_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Doc_instReprListItem_repr___redArg(v_inst_914_, v_x_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___boxed(lean_object* v_00_u03b1_918_, lean_object* v_inst_919_, lean_object* v_x_920_, lean_object* v_prec_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Doc_instReprListItem_repr(v_00_u03b1_918_, v_inst_919_, v_x_920_, v_prec_921_);
lean_dec(v_prec_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem___redArg(lean_object* v_inst_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_924_, 0, lean_box(0));
lean_closure_set(v___x_924_, 1, v_inst_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem(lean_object* v_00_u03b1_925_, lean_object* v_inst_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_927_, 0, lean_box(0));
lean_closure_set(v___x_927_, 1, v_inst_926_);
return v___x_927_;
}
}
uint8_t l_Lean_Doc_instBEqListItem_beq___redArg(lean_object* v_inst_928_, lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_931_ = lean_array_get_size(v_x_929_);
v___x_932_ = lean_array_get_size(v_x_930_);
v___x_933_ = lean_nat_dec_eq(v___x_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_dec_ref(v_inst_928_);
return v___x_933_;
}
else
{
uint8_t v___x_934_; 
v___x_934_ = l_Array_isEqvAux___redArg(v_x_929_, v_x_930_, v_inst_928_, v___x_931_);
return v___x_934_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqListItem_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_928_ = stack[0].m_obj;
lean_object* v_x_929_ = stack[1].m_obj;
lean_object* v_x_930_ = stack[2].m_obj;
uint8_t v_res_935_;
v_res_935_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_928_, v_x_929_, v_x_930_);
stack->m_num = v_res_935_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___redArg___boxed(lean_object* v_inst_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
uint8_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_936_, v_x_937_, v_x_938_);
lean_dec_ref(v_x_938_);
lean_dec_ref(v_x_937_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
uint8_t l_Lean_Doc_instBEqListItem_beq(lean_object* v_00_u03b1_941_, lean_object* v_inst_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_942_, v_x_943_, v_x_944_);
return v___x_945_;
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqListItem_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_942_ = stack[1].m_obj;
lean_object* v_x_943_ = stack[2].m_obj;
lean_object* v_x_944_ = stack[3].m_obj;
uint8_t v_res_946_;
v_res_946_ = l_Lean_Doc_instBEqListItem_beq(lean_box(0), v_inst_942_, v_x_943_, v_x_944_);
stack->m_num = v_res_946_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___boxed(lean_object* v_00_u03b1_947_, lean_object* v_inst_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Lean_Doc_instBEqListItem_beq(v_00_u03b1_947_, v_inst_948_, v_x_949_, v_x_950_);
lean_dec_ref(v_x_950_);
lean_dec_ref(v_x_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem___redArg(lean_object* v_inst_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_954_, 0, lean_box(0));
lean_closure_set(v___x_954_, 1, v_inst_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem(lean_object* v_00_u03b1_955_, lean_object* v_inst_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_957_, 0, lean_box(0));
lean_closure_set(v___x_957_, 1, v_inst_956_);
return v___x_957_;
}
}
uint8_t l_Lean_Doc_instOrdListItem_ord___redArg(lean_object* v_inst_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_inst_958_, v_x_959_, v_x_960_, v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdListItem_ord___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_958_ = stack[0].m_obj;
lean_object* v_x_959_ = stack[1].m_obj;
lean_object* v_x_960_ = stack[2].m_obj;
uint8_t v_res_963_;
v_res_963_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_958_, v_x_959_, v_x_960_);
stack->m_num = v_res_963_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___redArg___boxed(lean_object* v_inst_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
uint8_t v_res_967_; lean_object* v_r_968_; 
v_res_967_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_964_, v_x_965_, v_x_966_);
lean_dec_ref(v_x_966_);
lean_dec_ref(v_x_965_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
uint8_t l_Lean_Doc_instOrdListItem_ord(lean_object* v_00_u03b1_969_, lean_object* v_inst_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_970_, v_x_971_, v_x_972_);
return v___x_973_;
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdListItem_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_970_ = stack[1].m_obj;
lean_object* v_x_971_ = stack[2].m_obj;
lean_object* v_x_972_ = stack[3].m_obj;
uint8_t v_res_974_;
v_res_974_ = l_Lean_Doc_instOrdListItem_ord(lean_box(0), v_inst_970_, v_x_971_, v_x_972_);
stack->m_num = v_res_974_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___boxed(lean_object* v_00_u03b1_975_, lean_object* v_inst_976_, lean_object* v_x_977_, lean_object* v_x_978_){
_start:
{
uint8_t v_res_979_; lean_object* v_r_980_; 
v_res_979_ = l_Lean_Doc_instOrdListItem_ord(v_00_u03b1_975_, v_inst_976_, v_x_977_, v_x_978_);
lean_dec_ref(v_x_978_);
lean_dec_ref(v_x_977_);
v_r_980_ = lean_box(v_res_979_);
return v_r_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem___redArg(lean_object* v_inst_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_982_, 0, lean_box(0));
lean_closure_set(v___x_982_, 1, v_inst_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem(lean_object* v_00_u03b1_983_, lean_object* v_inst_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_985_, 0, lean_box(0));
lean_closure_set(v___x_985_, 1, v_inst_984_);
return v___x_985_;
}
}
lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg(){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l_Lean_Doc_instInhabitedListItem_default___redArg___closed__0));
return v___x_989_;
}
}
LEAN_EXPORT void l_Lean_Doc_instInhabitedListItem_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_990_;
v_res_990_ = l_Lean_Doc_instInhabitedListItem_default___redArg();
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg___boxed(lean_object* v___dummy_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Doc_instInhabitedListItem_default___redArg();
return v_res_992_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedListItem_default___closed__0(void){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Doc_instInhabitedListItem_default___redArg();
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default(lean_object* v_00_u03b1_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_995_;
}
}
lean_object* l_Lean_Doc_instInhabitedListItem___redArg(){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_997_;
}
}
LEAN_EXPORT void l_Lean_Doc_instInhabitedListItem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_998_;
v_res_998_ = l_Lean_Doc_instInhabitedListItem___redArg();
stack->m_obj
 = v_res_998_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem___redArg___boxed(lean_object* v___dummy_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Doc_instInhabitedListItem___redArg();
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem(lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_unsigned_to_nat(8u);
v___x_1013_ = lean_nat_to_int(v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___redArg(lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v_term_1023_; lean_object* v_desc_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1056_; 
v_term_1023_ = lean_ctor_get(v_x_1022_, 0);
v_desc_1024_ = lean_ctor_get(v_x_1022_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1026_ = v_x_1022_;
v_isShared_1027_ = v_isSharedCheck_1056_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_desc_1024_);
lean_inc(v_term_1023_);
lean_dec(v_x_1022_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1056_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1028_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1029_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__3));
v___x_1030_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4);
v___x_1031_ = l_Array_repr___redArg(v_inst_1020_, v_term_1023_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set_tag(v___x_1026_, 4);
lean_ctor_set(v___x_1026_, 1, v___x_1031_);
lean_ctor_set(v___x_1026_, 0, v___x_1030_);
v___x_1033_ = v___x_1026_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1034_ = 0;
v___x_1035_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*1, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1029_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_box(1);
v___x_1040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__8));
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_1028_);
v___x_1044_ = l_Array_repr___redArg(v_inst_1021_, v_desc_1024_);
v___x_1045_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1030_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*1, v___x_1034_);
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1043_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_1049_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_1047_);
v___x_1051_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1048_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*1, v___x_1034_);
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr(lean_object* v_00_u03b1_1057_, lean_object* v_00_u03b2_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_x_1061_, lean_object* v_prec_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Doc_instReprDescItem_repr___redArg(v_inst_1059_, v_inst_1060_, v_x_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_x_1068_, lean_object* v_prec_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_Doc_instReprDescItem_repr(v_00_u03b1_1064_, v_00_u03b2_1065_, v_inst_1066_, v_inst_1067_, v_x_1068_, v_prec_1069_);
lean_dec(v_prec_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem___redArg(lean_object* v_inst_1071_, lean_object* v_inst_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1073_, 0, lean_box(0));
lean_closure_set(v___x_1073_, 1, lean_box(0));
lean_closure_set(v___x_1073_, 2, v_inst_1071_);
lean_closure_set(v___x_1073_, 3, v_inst_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem(lean_object* v_00_u03b1_1074_, lean_object* v_00_u03b2_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1078_, 0, lean_box(0));
lean_closure_set(v___x_1078_, 1, lean_box(0));
lean_closure_set(v___x_1078_, 2, v_inst_1076_);
lean_closure_set(v___x_1078_, 3, v_inst_1077_);
return v___x_1078_;
}
}
uint8_t l_Lean_Doc_instBEqDescItem_beq___redArg(lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v_term_1083_; lean_object* v_desc_1084_; lean_object* v_term_1085_; lean_object* v_desc_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_term_1083_ = lean_ctor_get(v_x_1081_, 0);
v_desc_1084_ = lean_ctor_get(v_x_1081_, 1);
v_term_1085_ = lean_ctor_get(v_x_1082_, 0);
v_desc_1086_ = lean_ctor_get(v_x_1082_, 1);
v___x_1087_ = lean_array_get_size(v_term_1083_);
v___x_1088_ = lean_array_get_size(v_term_1085_);
v___x_1089_ = lean_nat_dec_eq(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_dec_ref(v_inst_1080_);
lean_dec_ref(v_inst_1079_);
return v___x_1089_;
}
else
{
uint8_t v___x_1090_; 
v___x_1090_ = l_Array_isEqvAux___redArg(v_term_1083_, v_term_1085_, v_inst_1079_, v___x_1087_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v_inst_1080_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1091_ = lean_array_get_size(v_desc_1084_);
v___x_1092_ = lean_array_get_size(v_desc_1086_);
v___x_1093_ = lean_nat_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_dec_ref(v_inst_1080_);
return v___x_1093_;
}
else
{
uint8_t v___x_1094_; 
v___x_1094_ = l_Array_isEqvAux___redArg(v_desc_1084_, v_desc_1086_, v_inst_1080_, v___x_1091_);
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqDescItem_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1079_ = stack[0].m_obj;
lean_object* v_inst_1080_ = stack[1].m_obj;
lean_object* v_x_1081_ = stack[2].m_obj;
lean_object* v_x_1082_ = stack[3].m_obj;
uint8_t v_res_1095_;
v_res_1095_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1079_, v_inst_1080_, v_x_1081_, v_x_1082_);
stack->m_num = v_res_1095_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___redArg___boxed(lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_res_1100_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1096_, v_inst_1097_, v_x_1098_, v_x_1099_);
lean_dec_ref(v_x_1099_);
lean_dec_ref(v_x_1098_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
uint8_t l_Lean_Doc_instBEqDescItem_beq(lean_object* v_00_u03b1_1102_, lean_object* v_00_u03b2_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
uint8_t v___x_1108_; 
v___x_1108_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1104_, v_inst_1105_, v_x_1106_, v_x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqDescItem_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1104_ = stack[2].m_obj;
lean_object* v_inst_1105_ = stack[3].m_obj;
lean_object* v_x_1106_ = stack[4].m_obj;
lean_object* v_x_1107_ = stack[5].m_obj;
uint8_t v_res_1109_;
v_res_1109_ = l_Lean_Doc_instBEqDescItem_beq(lean_box(0), lean_box(0), v_inst_1104_, v_inst_1105_, v_x_1106_, v_x_1107_);
stack->m_num = v_res_1109_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___boxed(lean_object* v_00_u03b1_1110_, lean_object* v_00_u03b2_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
uint8_t v_res_1116_; lean_object* v_r_1117_; 
v_res_1116_ = l_Lean_Doc_instBEqDescItem_beq(v_00_u03b1_1110_, v_00_u03b2_1111_, v_inst_1112_, v_inst_1113_, v_x_1114_, v_x_1115_);
lean_dec_ref(v_x_1115_);
lean_dec_ref(v_x_1114_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem___redArg(lean_object* v_inst_1118_, lean_object* v_inst_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1120_, 0, lean_box(0));
lean_closure_set(v___x_1120_, 1, lean_box(0));
lean_closure_set(v___x_1120_, 2, v_inst_1118_);
lean_closure_set(v___x_1120_, 3, v_inst_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem(lean_object* v_00_u03b1_1121_, lean_object* v_00_u03b2_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1125_, 0, lean_box(0));
lean_closure_set(v___x_1125_, 1, lean_box(0));
lean_closure_set(v___x_1125_, 2, v_inst_1123_);
lean_closure_set(v___x_1125_, 3, v_inst_1124_);
return v___x_1125_;
}
}
uint8_t l_Lean_Doc_instOrdDescItem_ord___redArg(lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v_term_1130_; lean_object* v_desc_1131_; lean_object* v_term_1132_; lean_object* v_desc_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_term_1130_ = lean_ctor_get(v_x_1128_, 0);
v_desc_1131_ = lean_ctor_get(v_x_1128_, 1);
v_term_1132_ = lean_ctor_get(v_x_1129_, 0);
v_desc_1133_ = lean_ctor_get(v_x_1129_, 1);
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_inst_1126_, v_term_1130_, v_term_1132_, v___x_1134_);
if (v___x_1135_ == 1)
{
uint8_t v___x_1136_; 
v___x_1136_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_inst_1127_, v_desc_1131_, v_desc_1133_, v___x_1134_);
return v___x_1136_;
}
else
{
lean_dec_ref(v_inst_1127_);
return v___x_1135_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdDescItem_ord___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1126_ = stack[0].m_obj;
lean_object* v_inst_1127_ = stack[1].m_obj;
lean_object* v_x_1128_ = stack[2].m_obj;
lean_object* v_x_1129_ = stack[3].m_obj;
uint8_t v_res_1137_;
v_res_1137_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1126_, v_inst_1127_, v_x_1128_, v_x_1129_);
stack->m_num = v_res_1137_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___redArg___boxed(lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1138_, v_inst_1139_, v_x_1140_, v_x_1141_);
lean_dec_ref(v_x_1141_);
lean_dec_ref(v_x_1140_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
uint8_t l_Lean_Doc_instOrdDescItem_ord(lean_object* v_00_u03b1_1144_, lean_object* v_00_u03b2_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1146_, v_inst_1147_, v_x_1148_, v_x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdDescItem_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1146_ = stack[2].m_obj;
lean_object* v_inst_1147_ = stack[3].m_obj;
lean_object* v_x_1148_ = stack[4].m_obj;
lean_object* v_x_1149_ = stack[5].m_obj;
uint8_t v_res_1151_;
v_res_1151_ = l_Lean_Doc_instOrdDescItem_ord(lean_box(0), lean_box(0), v_inst_1146_, v_inst_1147_, v_x_1148_, v_x_1149_);
stack->m_num = v_res_1151_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___boxed(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Lean_Doc_instOrdDescItem_ord(v_00_u03b1_1152_, v_00_u03b2_1153_, v_inst_1154_, v_inst_1155_, v_x_1156_, v_x_1157_);
lean_dec_ref(v_x_1157_);
lean_dec_ref(v_x_1156_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem___redArg(lean_object* v_inst_1160_, lean_object* v_inst_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1162_, 0, lean_box(0));
lean_closure_set(v___x_1162_, 1, lean_box(0));
lean_closure_set(v___x_1162_, 2, v_inst_1160_);
lean_closure_set(v___x_1162_, 3, v_inst_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem(lean_object* v_00_u03b1_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1167_, 0, lean_box(0));
lean_closure_set(v___x_1167_, 1, lean_box(0));
lean_closure_set(v___x_1167_, 2, v_inst_1165_);
lean_closure_set(v___x_1167_, 3, v_inst_1166_);
return v___x_1167_;
}
}
lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg(){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = ((lean_object*)(l_Lean_Doc_instInhabitedDescItem_default___redArg___closed__0));
return v___x_1171_;
}
}
LEAN_EXPORT void l_Lean_Doc_instInhabitedDescItem_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1172_;
v_res_1172_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
stack->m_obj
 = v_res_1172_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg___boxed(lean_object* v___dummy_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
return v_res_1174_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0(void){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default(lean_object* v_00_u03b1_1176_, lean_object* v_00_u03b2_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1178_;
}
}
lean_object* l_Lean_Doc_instInhabitedDescItem___redArg(){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1180_;
}
}
LEAN_EXPORT void l_Lean_Doc_instInhabitedDescItem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1181_;
v_res_1181_ = l_Lean_Doc_instInhabitedDescItem___redArg();
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg___boxed(lean_object* v___dummy_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Doc_instInhabitedDescItem___redArg();
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem(lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl___redArg(lean_object* v_x_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_obj_tag_nat(v_x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl___redArg___boxed(lean_object* v_x_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Doc_Block_ctorIdx___impl___redArg(v_x_1189_);
lean_dec_ref(v_x_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl(lean_object* v_i_1191_, lean_object* v_b_1192_, lean_object* v_x_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_obj_tag_nat(v_x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl___boxed(lean_object* v_i_1195_, lean_object* v_b_1196_, lean_object* v_x_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Doc_Block_ctorIdx___impl(v_i_1195_, v_b_1196_, v_x_1197_);
lean_dec_ref(v_x_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___redArg(lean_object* v_t_1199_, lean_object* v_k_1200_){
_start:
{
switch(lean_obj_tag(v_t_1199_))
{
case 3:
{
lean_object* v_start_1201_; lean_object* v_items_1202_; lean_object* v___x_1203_; 
v_start_1201_ = lean_ctor_get(v_t_1199_, 0);
lean_inc(v_start_1201_);
v_items_1202_ = lean_ctor_get(v_t_1199_, 1);
lean_inc_ref(v_items_1202_);
lean_dec_ref_known(v_t_1199_, 2);
v___x_1203_ = lean_apply_2(v_k_1200_, v_start_1201_, v_items_1202_);
return v___x_1203_;
}
case 7:
{
lean_object* v_container_1204_; lean_object* v_content_1205_; lean_object* v___x_1206_; 
v_container_1204_ = lean_ctor_get(v_t_1199_, 0);
lean_inc(v_container_1204_);
v_content_1205_ = lean_ctor_get(v_t_1199_, 1);
lean_inc_ref(v_content_1205_);
lean_dec_ref_known(v_t_1199_, 2);
v___x_1206_ = lean_apply_2(v_k_1200_, v_container_1204_, v_content_1205_);
return v___x_1206_;
}
default: 
{
lean_object* v_contents_1207_; lean_object* v___x_1208_; 
v_contents_1207_ = lean_ctor_get(v_t_1199_, 0);
lean_inc_ref(v_contents_1207_);
lean_dec_ref(v_t_1199_);
v___x_1208_ = lean_apply_1(v_k_1200_, v_contents_1207_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim(lean_object* v_i_1209_, lean_object* v_b_1210_, lean_object* v_motive__1_1211_, lean_object* v_ctorIdx_1212_, lean_object* v_t_1213_, lean_object* v_h_1214_, lean_object* v_k_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1213_, v_k_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___boxed(lean_object* v_i_1217_, lean_object* v_b_1218_, lean_object* v_motive__1_1219_, lean_object* v_ctorIdx_1220_, lean_object* v_t_1221_, lean_object* v_h_1222_, lean_object* v_k_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Doc_Block_ctorElim(v_i_1217_, v_b_1218_, v_motive__1_1219_, v_ctorIdx_1220_, v_t_1221_, v_h_1222_, v_k_1223_);
lean_dec(v_ctorIdx_1220_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim___redArg(lean_object* v_t_1225_, lean_object* v_para_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1225_, v_para_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim(lean_object* v_i_1228_, lean_object* v_b_1229_, lean_object* v_motive__1_1230_, lean_object* v_t_1231_, lean_object* v_h_1232_, lean_object* v_para_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1231_, v_para_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim___redArg(lean_object* v_t_1235_, lean_object* v_code_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1235_, v_code_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim(lean_object* v_i_1238_, lean_object* v_b_1239_, lean_object* v_motive__1_1240_, lean_object* v_t_1241_, lean_object* v_h_1242_, lean_object* v_code_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1241_, v_code_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim___redArg(lean_object* v_t_1245_, lean_object* v_ul_1246_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1245_, v_ul_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim(lean_object* v_i_1248_, lean_object* v_b_1249_, lean_object* v_motive__1_1250_, lean_object* v_t_1251_, lean_object* v_h_1252_, lean_object* v_ul_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1251_, v_ul_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim___redArg(lean_object* v_t_1255_, lean_object* v_ol_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1255_, v_ol_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim(lean_object* v_i_1258_, lean_object* v_b_1259_, lean_object* v_motive__1_1260_, lean_object* v_t_1261_, lean_object* v_h_1262_, lean_object* v_ol_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1261_, v_ol_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim___redArg(lean_object* v_t_1265_, lean_object* v_dl_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1265_, v_dl_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim(lean_object* v_i_1268_, lean_object* v_b_1269_, lean_object* v_motive__1_1270_, lean_object* v_t_1271_, lean_object* v_h_1272_, lean_object* v_dl_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1271_, v_dl_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim___redArg(lean_object* v_t_1275_, lean_object* v_blockquote_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1275_, v_blockquote_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim(lean_object* v_i_1278_, lean_object* v_b_1279_, lean_object* v_motive__1_1280_, lean_object* v_t_1281_, lean_object* v_h_1282_, lean_object* v_blockquote_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1281_, v_blockquote_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim___redArg(lean_object* v_t_1285_, lean_object* v_concat_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1285_, v_concat_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim(lean_object* v_i_1288_, lean_object* v_b_1289_, lean_object* v_motive__1_1290_, lean_object* v_t_1291_, lean_object* v_h_1292_, lean_object* v_concat_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1291_, v_concat_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim___redArg(lean_object* v_t_1295_, lean_object* v_other_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1295_, v_other_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim(lean_object* v_i_1298_, lean_object* v_b_1299_, lean_object* v_motive__1_1300_, lean_object* v_t_1301_, lean_object* v_h_1302_, lean_object* v_other_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1301_, v_other_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___redArg___boxed(lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
uint8_t v_res_1309_; lean_object* v_r_1310_; 
v_res_1309_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1305_, v_inst_1306_, v_x_1307_, v_x_1308_);
v_r_1310_ = lean_box(v_res_1309_);
return v_r_1310_;
}
}
uint8_t l_Lean_Doc_instBEqBlock_beq___redArg(lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_){
_start:
{
lean_object* v_localinst_1315_; lean_object* v_a_1317_; lean_object* v_b_1318_; 
lean_inc_ref(v_inst_1312_);
lean_inc_ref(v_inst_1311_);
v_localinst_1315_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1315_, 0, v_inst_1311_);
lean_closure_set(v_localinst_1315_, 1, v_inst_1312_);
switch(lean_obj_tag(v_x_1313_))
{
case 0:
{
lean_dec_ref(v_localinst_1315_);
lean_dec_ref(v_inst_1312_);
if (lean_obj_tag(v_x_1314_) == 0)
{
lean_object* v_contents_1323_; lean_object* v_contents_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_contents_1323_ = lean_ctor_get(v_x_1313_, 0);
lean_inc_ref(v_contents_1323_);
lean_dec_ref_known(v_x_1313_, 1);
v_contents_1324_ = lean_ctor_get(v_x_1314_, 0);
lean_inc_ref(v_contents_1324_);
lean_dec_ref_known(v_x_1314_, 1);
v___x_1325_ = lean_array_get_size(v_contents_1323_);
v___x_1326_ = lean_array_get_size(v_contents_1324_);
v___x_1327_ = lean_nat_dec_eq(v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_dec_ref(v_contents_1324_);
lean_dec_ref(v_contents_1323_);
lean_dec_ref(v_inst_1311_);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1328_, 0, lean_box(0));
lean_closure_set(v___x_1328_, 1, v_inst_1311_);
v___x_1329_ = l_Array_isEqvAux___redArg(v_contents_1323_, v_contents_1324_, v___x_1328_, v___x_1325_);
lean_dec_ref(v_contents_1324_);
lean_dec_ref(v_contents_1323_);
return v___x_1329_;
}
}
else
{
uint8_t v___x_1330_; 
lean_dec_ref_known(v_x_1313_, 1);
lean_dec_ref(v_x_1314_);
lean_dec_ref(v_inst_1311_);
v___x_1330_ = 0;
return v___x_1330_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1315_);
lean_dec_ref(v_inst_1312_);
lean_dec_ref(v_inst_1311_);
if (lean_obj_tag(v_x_1314_) == 1)
{
lean_object* v_content_1331_; lean_object* v_content_1332_; uint8_t v___x_1333_; 
v_content_1331_ = lean_ctor_get(v_x_1313_, 0);
lean_inc_ref(v_content_1331_);
lean_dec_ref_known(v_x_1313_, 1);
v_content_1332_ = lean_ctor_get(v_x_1314_, 0);
lean_inc_ref(v_content_1332_);
lean_dec_ref_known(v_x_1314_, 1);
v___x_1333_ = lean_string_dec_eq(v_content_1331_, v_content_1332_);
lean_dec_ref(v_content_1332_);
lean_dec_ref(v_content_1331_);
return v___x_1333_;
}
else
{
uint8_t v___x_1334_; 
lean_dec_ref_known(v_x_1313_, 1);
lean_dec_ref(v_x_1314_);
v___x_1334_ = 0;
return v___x_1334_;
}
}
case 2:
{
lean_dec_ref(v_inst_1312_);
lean_dec_ref(v_inst_1311_);
if (lean_obj_tag(v_x_1314_) == 2)
{
lean_object* v_items_1335_; lean_object* v_items_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_items_1335_ = lean_ctor_get(v_x_1313_, 0);
lean_inc_ref(v_items_1335_);
lean_dec_ref_known(v_x_1313_, 1);
v_items_1336_ = lean_ctor_get(v_x_1314_, 0);
lean_inc_ref(v_items_1336_);
lean_dec_ref_known(v_x_1314_, 1);
v___x_1337_ = lean_array_get_size(v_items_1335_);
v___x_1338_ = lean_array_get_size(v_items_1336_);
v___x_1339_ = lean_nat_dec_eq(v___x_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_dec_ref(v_items_1336_);
lean_dec_ref(v_items_1335_);
lean_dec_ref(v_localinst_1315_);
return v___x_1339_;
}
else
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1340_, 0, lean_box(0));
lean_closure_set(v___x_1340_, 1, v_localinst_1315_);
v___x_1341_ = l_Array_isEqvAux___redArg(v_items_1335_, v_items_1336_, v___x_1340_, v___x_1337_);
lean_dec_ref(v_items_1336_);
lean_dec_ref(v_items_1335_);
return v___x_1341_;
}
}
else
{
uint8_t v___x_1342_; 
lean_dec_ref_known(v_x_1313_, 1);
lean_dec_ref(v_localinst_1315_);
lean_dec_ref(v_x_1314_);
v___x_1342_ = 0;
return v___x_1342_;
}
}
case 3:
{
lean_dec_ref(v_inst_1312_);
lean_dec_ref(v_inst_1311_);
if (lean_obj_tag(v_x_1314_) == 3)
{
lean_object* v_start_1343_; lean_object* v_items_1344_; lean_object* v_start_1345_; lean_object* v_items_1346_; uint8_t v___x_1347_; 
v_start_1343_ = lean_ctor_get(v_x_1313_, 0);
lean_inc(v_start_1343_);
v_items_1344_ = lean_ctor_get(v_x_1313_, 1);
lean_inc_ref(v_items_1344_);
lean_dec_ref_known(v_x_1313_, 2);
v_start_1345_ = lean_ctor_get(v_x_1314_, 0);
lean_inc(v_start_1345_);
v_items_1346_ = lean_ctor_get(v_x_1314_, 1);
lean_inc_ref(v_items_1346_);
lean_dec_ref_known(v_x_1314_, 2);
v___x_1347_ = lean_int_dec_eq(v_start_1343_, v_start_1345_);
lean_dec(v_start_1345_);
lean_dec(v_start_1343_);
if (v___x_1347_ == 0)
{
lean_dec_ref(v_items_1346_);
lean_dec_ref(v_items_1344_);
lean_dec_ref(v_localinst_1315_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = lean_array_get_size(v_items_1344_);
v___x_1349_ = lean_array_get_size(v_items_1346_);
v___x_1350_ = lean_nat_dec_eq(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_dec_ref(v_items_1346_);
lean_dec_ref(v_items_1344_);
lean_dec_ref(v_localinst_1315_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1351_, 0, lean_box(0));
lean_closure_set(v___x_1351_, 1, v_localinst_1315_);
v___x_1352_ = l_Array_isEqvAux___redArg(v_items_1344_, v_items_1346_, v___x_1351_, v___x_1348_);
lean_dec_ref(v_items_1346_);
lean_dec_ref(v_items_1344_);
return v___x_1352_;
}
}
}
else
{
uint8_t v___x_1353_; 
lean_dec_ref_known(v_x_1313_, 2);
lean_dec_ref(v_localinst_1315_);
lean_dec_ref(v_x_1314_);
v___x_1353_ = 0;
return v___x_1353_;
}
}
case 4:
{
lean_dec_ref(v_inst_1312_);
if (lean_obj_tag(v_x_1314_) == 4)
{
lean_object* v_items_1354_; lean_object* v_items_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_items_1354_ = lean_ctor_get(v_x_1313_, 0);
lean_inc_ref(v_items_1354_);
lean_dec_ref_known(v_x_1313_, 1);
v_items_1355_ = lean_ctor_get(v_x_1314_, 0);
lean_inc_ref(v_items_1355_);
lean_dec_ref_known(v_x_1314_, 1);
v___x_1356_ = lean_array_get_size(v_items_1354_);
v___x_1357_ = lean_array_get_size(v_items_1355_);
v___x_1358_ = lean_nat_dec_eq(v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_dec_ref(v_items_1355_);
lean_dec_ref(v_items_1354_);
lean_dec_ref(v_localinst_1315_);
lean_dec_ref(v_inst_1311_);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1359_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1359_, 0, lean_box(0));
lean_closure_set(v___x_1359_, 1, v_inst_1311_);
v___x_1360_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1360_, 0, lean_box(0));
lean_closure_set(v___x_1360_, 1, lean_box(0));
lean_closure_set(v___x_1360_, 2, v___x_1359_);
lean_closure_set(v___x_1360_, 3, v_localinst_1315_);
v___x_1361_ = l_Array_isEqvAux___redArg(v_items_1354_, v_items_1355_, v___x_1360_, v___x_1356_);
lean_dec_ref(v_items_1355_);
lean_dec_ref(v_items_1354_);
return v___x_1361_;
}
}
else
{
uint8_t v___x_1362_; 
lean_dec_ref_known(v_x_1313_, 1);
lean_dec_ref(v_localinst_1315_);
lean_dec_ref(v_x_1314_);
lean_dec_ref(v_inst_1311_);
v___x_1362_ = 0;
return v___x_1362_;
}
}
case 5:
{
lean_dec_ref(v_inst_1312_);
lean_dec_ref(v_inst_1311_);
if (lean_obj_tag(v_x_1314_) == 5)
{
lean_object* v_items_1363_; lean_object* v_items_1364_; 
v_items_1363_ = lean_ctor_get(v_x_1313_, 0);
lean_inc_ref(v_items_1363_);
lean_dec_ref_known(v_x_1313_, 1);
v_items_1364_ = lean_ctor_get(v_x_1314_, 0);
lean_inc_ref(v_items_1364_);
lean_dec_ref_known(v_x_1314_, 1);
v_a_1317_ = v_items_1363_;
v_b_1318_ = v_items_1364_;
goto v___jp_1316_;
}
else
{
uint8_t v___x_1365_; 
lean_dec_ref_known(v_x_1313_, 1);
lean_dec_ref(v_localinst_1315_);
lean_dec_ref(v_x_1314_);
v___x_1365_ = 0;
return v___x_1365_;
}
}
case 6:
{
lean_dec_ref(v_inst_1312_);
lean_dec_ref(v_inst_1311_);
if (lean_obj_tag(v_x_1314_) == 6)
{
lean_object* v_content_1366_; lean_object* v_content_1367_; 
v_content_1366_ = lean_ctor_get(v_x_1313_, 0);
lean_inc_ref(v_content_1366_);
lean_dec_ref_known(v_x_1313_, 1);
v_content_1367_ = lean_ctor_get(v_x_1314_, 0);
lean_inc_ref(v_content_1367_);
lean_dec_ref_known(v_x_1314_, 1);
v_a_1317_ = v_content_1366_;
v_b_1318_ = v_content_1367_;
goto v___jp_1316_;
}
else
{
uint8_t v___x_1368_; 
lean_dec_ref_known(v_x_1313_, 1);
lean_dec_ref(v_localinst_1315_);
lean_dec_ref(v_x_1314_);
v___x_1368_ = 0;
return v___x_1368_;
}
}
default: 
{
lean_dec_ref(v_inst_1311_);
if (lean_obj_tag(v_x_1314_) == 7)
{
lean_object* v_container_1369_; lean_object* v_content_1370_; lean_object* v_container_1371_; lean_object* v_content_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_container_1369_ = lean_ctor_get(v_x_1313_, 0);
lean_inc(v_container_1369_);
v_content_1370_ = lean_ctor_get(v_x_1313_, 1);
lean_inc_ref(v_content_1370_);
lean_dec_ref_known(v_x_1313_, 2);
v_container_1371_ = lean_ctor_get(v_x_1314_, 0);
lean_inc(v_container_1371_);
v_content_1372_ = lean_ctor_get(v_x_1314_, 1);
lean_inc_ref(v_content_1372_);
lean_dec_ref_known(v_x_1314_, 2);
v___x_1373_ = lean_apply_2(v_inst_1312_, v_container_1369_, v_container_1371_);
v___x_1374_ = lean_unbox(v___x_1373_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; 
lean_dec_ref(v_content_1372_);
lean_dec_ref(v_content_1370_);
lean_dec_ref(v_localinst_1315_);
v___x_1375_ = lean_unbox(v___x_1373_);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = lean_array_get_size(v_content_1370_);
v___x_1377_ = lean_array_get_size(v_content_1372_);
v___x_1378_ = lean_nat_dec_eq(v___x_1376_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_dec_ref(v_content_1372_);
lean_dec_ref(v_content_1370_);
lean_dec_ref(v_localinst_1315_);
return v___x_1378_;
}
else
{
uint8_t v___x_1379_; 
v___x_1379_ = l_Array_isEqvAux___redArg(v_content_1370_, v_content_1372_, v_localinst_1315_, v___x_1376_);
lean_dec_ref(v_content_1372_);
lean_dec_ref(v_content_1370_);
return v___x_1379_;
}
}
}
else
{
uint8_t v___x_1380_; 
lean_dec_ref_known(v_x_1313_, 2);
lean_dec_ref(v_localinst_1315_);
lean_dec_ref(v_x_1314_);
lean_dec_ref(v_inst_1312_);
v___x_1380_ = 0;
return v___x_1380_;
}
}
}
v___jp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_array_get_size(v_a_1317_);
v___x_1320_ = lean_array_get_size(v_b_1318_);
v___x_1321_ = lean_nat_dec_eq(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_dec_ref(v_b_1318_);
lean_dec_ref(v_a_1317_);
lean_dec_ref(v_localinst_1315_);
return v___x_1321_;
}
else
{
uint8_t v___x_1322_; 
v___x_1322_ = l_Array_isEqvAux___redArg(v_a_1317_, v_b_1318_, v_localinst_1315_, v___x_1319_);
lean_dec_ref(v_b_1318_);
lean_dec_ref(v_a_1317_);
return v___x_1322_;
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqBlock_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1311_ = stack[0].m_obj;
lean_object* v_inst_1312_ = stack[1].m_obj;
lean_object* v_x_1313_ = stack[2].m_obj;
lean_object* v_x_1314_ = stack[3].m_obj;
uint8_t v_res_1381_;
v_res_1381_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1311_, v_inst_1312_, v_x_1313_, v_x_1314_);
stack->m_num = v_res_1381_;
}
uint8_t l_Lean_Doc_instBEqBlock_beq(lean_object* v_i_1382_, lean_object* v_b_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1384_, v_inst_1385_, v_x_1386_, v_x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqBlock_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1384_ = stack[2].m_obj;
lean_object* v_inst_1385_ = stack[3].m_obj;
lean_object* v_x_1386_ = stack[4].m_obj;
lean_object* v_x_1387_ = stack[5].m_obj;
uint8_t v_res_1389_;
v_res_1389_ = l_Lean_Doc_instBEqBlock_beq(lean_box(0), lean_box(0), v_inst_1384_, v_inst_1385_, v_x_1386_, v_x_1387_);
stack->m_num = v_res_1389_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___boxed(lean_object* v_i_1390_, lean_object* v_b_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
uint8_t v_res_1396_; lean_object* v_r_1397_; 
v_res_1396_ = l_Lean_Doc_instBEqBlock_beq(v_i_1390_, v_b_1391_, v_inst_1392_, v_inst_1393_, v_x_1394_, v_x_1395_);
v_r_1397_ = lean_box(v_res_1396_);
return v_r_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock___redArg(lean_object* v_inst_1398_, lean_object* v_inst_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1400_, 0, lean_box(0));
lean_closure_set(v___x_1400_, 1, lean_box(0));
lean_closure_set(v___x_1400_, 2, v_inst_1398_);
lean_closure_set(v___x_1400_, 3, v_inst_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock(lean_object* v_i_1401_, lean_object* v_b_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1405_, 0, lean_box(0));
lean_closure_set(v___x_1405_, 1, lean_box(0));
lean_closure_set(v___x_1405_, 2, v_inst_1403_);
lean_closure_set(v___x_1405_, 3, v_inst_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___redArg___boxed(lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
uint8_t v_res_1410_; lean_object* v_r_1411_; 
v_res_1410_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1406_, v_inst_1407_, v_x_1408_, v_x_1409_);
v_r_1411_ = lean_box(v_res_1410_);
return v_r_1411_;
}
}
uint8_t l_Lean_Doc_instOrdBlock_ord___redArg(lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v_localinst_1416_; lean_object* v_a_1418_; lean_object* v_b_1419_; 
lean_inc_ref(v_inst_1413_);
lean_inc_ref(v_inst_1412_);
v_localinst_1416_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1416_, 0, v_inst_1412_);
lean_closure_set(v_localinst_1416_, 1, v_inst_1413_);
switch(lean_obj_tag(v_x_1414_))
{
case 0:
{
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_inst_1413_);
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v_contents_1422_; lean_object* v_contents_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v_contents_1422_ = lean_ctor_get(v_x_1414_, 0);
lean_inc_ref(v_contents_1422_);
lean_dec_ref_known(v_x_1414_, 1);
v_contents_1423_ = lean_ctor_get(v_x_1415_, 0);
lean_inc_ref(v_contents_1423_);
lean_dec_ref_known(v_x_1415_, 1);
v___x_1424_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1424_, 0, lean_box(0));
lean_closure_set(v___x_1424_, 1, v_inst_1412_);
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1424_, v_contents_1422_, v_contents_1423_, v___x_1425_);
lean_dec_ref(v_contents_1423_);
lean_dec_ref(v_contents_1422_);
return v___x_1426_;
}
else
{
uint8_t v___x_1427_; 
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_x_1415_);
lean_dec_ref(v_inst_1412_);
v___x_1427_ = 0;
return v___x_1427_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_inst_1413_);
lean_dec_ref(v_inst_1412_);
switch(lean_obj_tag(v_x_1415_))
{
case 0:
{
uint8_t v___x_1428_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
v___x_1428_ = 2;
return v___x_1428_;
}
case 1:
{
lean_object* v_content_1429_; lean_object* v_content_1430_; uint8_t v___x_1431_; 
v_content_1429_ = lean_ctor_get(v_x_1414_, 0);
lean_inc_ref(v_content_1429_);
lean_dec_ref_known(v_x_1414_, 1);
v_content_1430_ = lean_ctor_get(v_x_1415_, 0);
lean_inc_ref(v_content_1430_);
lean_dec_ref_known(v_x_1415_, 1);
v___x_1431_ = lean_string_compare(v_content_1429_, v_content_1430_);
lean_dec_ref(v_content_1430_);
lean_dec_ref(v_content_1429_);
return v___x_1431_;
}
default: 
{
uint8_t v___x_1432_; 
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_x_1415_);
v___x_1432_ = 0;
return v___x_1432_;
}
}
}
case 2:
{
lean_dec_ref(v_inst_1413_);
lean_dec_ref(v_inst_1412_);
switch(lean_obj_tag(v_x_1415_))
{
case 0:
{
uint8_t v___x_1433_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1433_ = 2;
return v___x_1433_;
}
case 1:
{
uint8_t v___x_1434_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1434_ = 2;
return v___x_1434_;
}
case 2:
{
lean_object* v_items_1435_; lean_object* v_items_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_items_1435_ = lean_ctor_get(v_x_1414_, 0);
lean_inc_ref(v_items_1435_);
lean_dec_ref_known(v_x_1414_, 1);
v_items_1436_ = lean_ctor_get(v_x_1415_, 0);
lean_inc_ref(v_items_1436_);
lean_dec_ref_known(v_x_1415_, 1);
v___x_1437_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1437_, 0, lean_box(0));
lean_closure_set(v___x_1437_, 1, v_localinst_1416_);
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1437_, v_items_1435_, v_items_1436_, v___x_1438_);
lean_dec_ref(v_items_1436_);
lean_dec_ref(v_items_1435_);
return v___x_1439_;
}
default: 
{
uint8_t v___x_1440_; 
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_x_1415_);
v___x_1440_ = 0;
return v___x_1440_;
}
}
}
case 3:
{
lean_dec_ref(v_inst_1413_);
lean_dec_ref(v_inst_1412_);
switch(lean_obj_tag(v_x_1415_))
{
case 0:
{
uint8_t v___x_1441_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 2);
lean_dec_ref(v_localinst_1416_);
v___x_1441_ = 2;
return v___x_1441_;
}
case 1:
{
uint8_t v___x_1442_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 2);
lean_dec_ref(v_localinst_1416_);
v___x_1442_ = 2;
return v___x_1442_;
}
case 2:
{
uint8_t v___x_1443_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 2);
lean_dec_ref(v_localinst_1416_);
v___x_1443_ = 2;
return v___x_1443_;
}
case 3:
{
lean_object* v_start_1444_; lean_object* v_items_1445_; lean_object* v_start_1446_; lean_object* v_items_1447_; uint8_t v___x_1448_; 
v_start_1444_ = lean_ctor_get(v_x_1414_, 0);
lean_inc(v_start_1444_);
v_items_1445_ = lean_ctor_get(v_x_1414_, 1);
lean_inc_ref(v_items_1445_);
lean_dec_ref_known(v_x_1414_, 2);
v_start_1446_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_start_1446_);
v_items_1447_ = lean_ctor_get(v_x_1415_, 1);
lean_inc_ref(v_items_1447_);
lean_dec_ref_known(v_x_1415_, 2);
v___x_1448_ = lean_int_dec_lt(v_start_1444_, v_start_1446_);
if (v___x_1448_ == 0)
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_int_dec_eq(v_start_1444_, v_start_1446_);
lean_dec(v_start_1446_);
lean_dec(v_start_1444_);
if (v___x_1449_ == 0)
{
uint8_t v___x_1450_; 
lean_dec_ref(v_items_1447_);
lean_dec_ref(v_items_1445_);
lean_dec_ref(v_localinst_1416_);
v___x_1450_ = 2;
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1451_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1451_, 0, lean_box(0));
lean_closure_set(v___x_1451_, 1, v_localinst_1416_);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1451_, v_items_1445_, v_items_1447_, v___x_1452_);
lean_dec_ref(v_items_1447_);
lean_dec_ref(v_items_1445_);
return v___x_1453_;
}
}
else
{
uint8_t v___x_1454_; 
lean_dec_ref(v_items_1447_);
lean_dec(v_start_1446_);
lean_dec_ref(v_items_1445_);
lean_dec(v_start_1444_);
lean_dec_ref(v_localinst_1416_);
v___x_1454_ = 0;
return v___x_1454_;
}
}
default: 
{
uint8_t v___x_1455_; 
lean_dec_ref_known(v_x_1414_, 2);
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_x_1415_);
v___x_1455_ = 0;
return v___x_1455_;
}
}
}
case 4:
{
lean_dec_ref(v_inst_1413_);
switch(lean_obj_tag(v_x_1415_))
{
case 0:
{
uint8_t v___x_1456_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_inst_1412_);
v___x_1456_ = 2;
return v___x_1456_;
}
case 1:
{
uint8_t v___x_1457_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_inst_1412_);
v___x_1457_ = 2;
return v___x_1457_;
}
case 2:
{
uint8_t v___x_1458_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_inst_1412_);
v___x_1458_ = 2;
return v___x_1458_;
}
case 3:
{
uint8_t v___x_1459_; 
lean_dec_ref_known(v_x_1415_, 2);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_inst_1412_);
v___x_1459_ = 2;
return v___x_1459_;
}
case 4:
{
lean_object* v_items_1460_; lean_object* v_items_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v_items_1460_ = lean_ctor_get(v_x_1414_, 0);
lean_inc_ref(v_items_1460_);
lean_dec_ref_known(v_x_1414_, 1);
v_items_1461_ = lean_ctor_get(v_x_1415_, 0);
lean_inc_ref(v_items_1461_);
lean_dec_ref_known(v_x_1415_, 1);
v___x_1462_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1462_, 0, lean_box(0));
lean_closure_set(v___x_1462_, 1, v_inst_1412_);
v___x_1463_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1463_, 0, lean_box(0));
lean_closure_set(v___x_1463_, 1, lean_box(0));
lean_closure_set(v___x_1463_, 2, v___x_1462_);
lean_closure_set(v___x_1463_, 3, v_localinst_1416_);
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1463_, v_items_1460_, v_items_1461_, v___x_1464_);
lean_dec_ref(v_items_1461_);
lean_dec_ref(v_items_1460_);
return v___x_1465_;
}
default: 
{
uint8_t v___x_1466_; 
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_x_1415_);
lean_dec_ref(v_inst_1412_);
v___x_1466_ = 0;
return v___x_1466_;
}
}
}
case 5:
{
lean_dec_ref(v_inst_1413_);
lean_dec_ref(v_inst_1412_);
switch(lean_obj_tag(v_x_1415_))
{
case 0:
{
uint8_t v___x_1467_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1467_ = 2;
return v___x_1467_;
}
case 1:
{
uint8_t v___x_1468_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1468_ = 2;
return v___x_1468_;
}
case 2:
{
uint8_t v___x_1469_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1469_ = 2;
return v___x_1469_;
}
case 3:
{
uint8_t v___x_1470_; 
lean_dec_ref_known(v_x_1415_, 2);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1470_ = 2;
return v___x_1470_;
}
case 4:
{
uint8_t v___x_1471_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1471_ = 2;
return v___x_1471_;
}
case 5:
{
lean_object* v_items_1472_; lean_object* v_items_1473_; 
v_items_1472_ = lean_ctor_get(v_x_1414_, 0);
lean_inc_ref(v_items_1472_);
lean_dec_ref_known(v_x_1414_, 1);
v_items_1473_ = lean_ctor_get(v_x_1415_, 0);
lean_inc_ref(v_items_1473_);
lean_dec_ref_known(v_x_1415_, 1);
v_a_1418_ = v_items_1472_;
v_b_1419_ = v_items_1473_;
goto v___jp_1417_;
}
default: 
{
uint8_t v___x_1474_; 
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_x_1415_);
v___x_1474_ = 0;
return v___x_1474_;
}
}
}
case 6:
{
lean_dec_ref(v_inst_1413_);
lean_dec_ref(v_inst_1412_);
switch(lean_obj_tag(v_x_1415_))
{
case 0:
{
uint8_t v___x_1475_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1475_ = 2;
return v___x_1475_;
}
case 1:
{
uint8_t v___x_1476_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1476_ = 2;
return v___x_1476_;
}
case 2:
{
uint8_t v___x_1477_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1477_ = 2;
return v___x_1477_;
}
case 3:
{
uint8_t v___x_1478_; 
lean_dec_ref_known(v_x_1415_, 2);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1478_ = 2;
return v___x_1478_;
}
case 4:
{
uint8_t v___x_1479_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1479_ = 2;
return v___x_1479_;
}
case 5:
{
uint8_t v___x_1480_; 
lean_dec_ref_known(v_x_1415_, 1);
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
v___x_1480_ = 2;
return v___x_1480_;
}
case 6:
{
lean_object* v_content_1481_; lean_object* v_content_1482_; 
v_content_1481_ = lean_ctor_get(v_x_1414_, 0);
lean_inc_ref(v_content_1481_);
lean_dec_ref_known(v_x_1414_, 1);
v_content_1482_ = lean_ctor_get(v_x_1415_, 0);
lean_inc_ref(v_content_1482_);
lean_dec_ref_known(v_x_1415_, 1);
v_a_1418_ = v_content_1481_;
v_b_1419_ = v_content_1482_;
goto v___jp_1417_;
}
default: 
{
uint8_t v___x_1483_; 
lean_dec_ref_known(v_x_1414_, 1);
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_x_1415_);
v___x_1483_ = 0;
return v___x_1483_;
}
}
}
default: 
{
lean_dec_ref(v_inst_1412_);
if (lean_obj_tag(v_x_1415_) == 7)
{
lean_object* v_container_1484_; lean_object* v_content_1485_; lean_object* v_container_1486_; lean_object* v_content_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_container_1484_ = lean_ctor_get(v_x_1414_, 0);
lean_inc(v_container_1484_);
v_content_1485_ = lean_ctor_get(v_x_1414_, 1);
lean_inc_ref(v_content_1485_);
lean_dec_ref_known(v_x_1414_, 2);
v_container_1486_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_container_1486_);
v_content_1487_ = lean_ctor_get(v_x_1415_, 1);
lean_inc_ref(v_content_1487_);
lean_dec_ref_known(v_x_1415_, 2);
v___x_1488_ = lean_apply_2(v_inst_1413_, v_container_1484_, v_container_1486_);
v___x_1489_ = lean_unbox(v___x_1488_);
if (v___x_1489_ == 1)
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_localinst_1416_, v_content_1485_, v_content_1487_, v___x_1490_);
lean_dec_ref(v_content_1487_);
lean_dec_ref(v_content_1485_);
return v___x_1491_;
}
else
{
uint8_t v___x_1492_; 
lean_dec_ref(v_content_1487_);
lean_dec_ref(v_content_1485_);
lean_dec_ref(v_localinst_1416_);
v___x_1492_ = lean_unbox(v___x_1488_);
return v___x_1492_;
}
}
else
{
uint8_t v___x_1493_; 
lean_dec_ref_known(v_x_1414_, 2);
lean_dec_ref(v_localinst_1416_);
lean_dec_ref(v_x_1415_);
lean_dec_ref(v_inst_1413_);
v___x_1493_ = 2;
return v___x_1493_;
}
}
}
v___jp_1417_:
{
lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_localinst_1416_, v_a_1418_, v_b_1419_, v___x_1420_);
lean_dec_ref(v_b_1419_);
lean_dec_ref(v_a_1418_);
return v___x_1421_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdBlock_ord___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1412_ = stack[0].m_obj;
lean_object* v_inst_1413_ = stack[1].m_obj;
lean_object* v_x_1414_ = stack[2].m_obj;
lean_object* v_x_1415_ = stack[3].m_obj;
uint8_t v_res_1494_;
v_res_1494_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1412_, v_inst_1413_, v_x_1414_, v_x_1415_);
stack->m_num = v_res_1494_;
}
uint8_t l_Lean_Doc_instOrdBlock_ord(lean_object* v_i_1495_, lean_object* v_b_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
uint8_t v___x_1501_; 
v___x_1501_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1497_, v_inst_1498_, v_x_1499_, v_x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdBlock_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1497_ = stack[2].m_obj;
lean_object* v_inst_1498_ = stack[3].m_obj;
lean_object* v_x_1499_ = stack[4].m_obj;
lean_object* v_x_1500_ = stack[5].m_obj;
uint8_t v_res_1502_;
v_res_1502_ = l_Lean_Doc_instOrdBlock_ord(lean_box(0), lean_box(0), v_inst_1497_, v_inst_1498_, v_x_1499_, v_x_1500_);
stack->m_num = v_res_1502_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___boxed(lean_object* v_i_1503_, lean_object* v_b_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l_Lean_Doc_instOrdBlock_ord(v_i_1503_, v_b_1504_, v_inst_1505_, v_inst_1506_, v_x_1507_, v_x_1508_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock___redArg(lean_object* v_inst_1511_, lean_object* v_inst_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1513_, 0, lean_box(0));
lean_closure_set(v___x_1513_, 1, lean_box(0));
lean_closure_set(v___x_1513_, 2, v_inst_1511_);
lean_closure_set(v___x_1513_, 3, v_inst_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock(lean_object* v_i_1514_, lean_object* v_b_1515_, lean_object* v_inst_1516_, lean_object* v_inst_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1518_, 0, lean_box(0));
lean_closure_set(v___x_1518_, 1, lean_box(0));
lean_closure_set(v___x_1518_, 2, v_inst_1516_);
lean_closure_set(v___x_1518_, 3, v_inst_1517_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = lean_nat_to_int(v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg___boxed(lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_x_1571_, lean_object* v_prec_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1569_, v_inst_1570_, v_x_1571_, v_prec_1572_);
lean_dec(v_prec_1572_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg(lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_x_1576_, lean_object* v_prec_1577_){
_start:
{
lean_object* v_localinst_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_inc_ref(v_inst_1575_);
lean_inc_ref(v_inst_1574_);
v_localinst_1578_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1578_, 0, v_inst_1574_);
lean_closure_set(v_localinst_1578_, 1, v_inst_1575_);
v___x_1579_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1579_, 0, lean_box(0));
lean_closure_set(v___x_1579_, 1, v_inst_1574_);
lean_inc_ref(v_localinst_1578_);
v___x_1580_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_1580_, 0, lean_box(0));
lean_closure_set(v___x_1580_, 1, v_localinst_1578_);
switch(lean_obj_tag(v_x_1576_))
{
case 0:
{
lean_object* v_contents_1581_; lean_object* v___y_1583_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
lean_dec_ref(v___x_1580_);
lean_dec_ref(v_localinst_1578_);
lean_dec_ref(v_inst_1575_);
v_contents_1581_ = lean_ctor_get(v_x_1576_, 0);
lean_inc_ref(v_contents_1581_);
lean_dec_ref_known(v_x_1576_, 1);
v___x_1591_ = lean_unsigned_to_nat(1024u);
v___x_1592_ = lean_nat_dec_le(v___x_1591_, v_prec_1577_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1583_ = v___x_1593_;
goto v___jp_1582_;
}
else
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1583_ = v___x_1594_;
goto v___jp_1582_;
}
v___jp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1584_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__2));
v___x_1585_ = l_Array_repr___redArg(v___x_1579_, v_contents_1581_);
v___x_1586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
lean_inc(v___y_1583_);
v___x_1587_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___y_1583_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = 0;
v___x_1589_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*1, v___x_1588_);
v___x_1590_ = l_Repr_addAppParen(v___x_1589_, v_prec_1577_);
return v___x_1590_;
}
}
case 1:
{
lean_object* v_content_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1615_; 
lean_dec_ref(v___x_1580_);
lean_dec_ref(v___x_1579_);
lean_dec_ref(v_localinst_1578_);
lean_dec_ref(v_inst_1575_);
v_content_1595_ = lean_ctor_get(v_x_1576_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_x_1576_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1597_ = v_x_1576_;
v_isShared_1598_ = v_isSharedCheck_1615_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_content_1595_);
lean_dec(v_x_1576_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1615_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___y_1600_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = lean_unsigned_to_nat(1024u);
v___x_1612_ = lean_nat_dec_le(v___x_1611_, v_prec_1577_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1600_ = v___x_1613_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1600_ = v___x_1614_;
goto v___jp_1599_;
}
v___jp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1601_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__5));
v___x_1602_ = l_String_quote(v_content_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set_tag(v___x_1597_, 3);
lean_ctor_set(v___x_1597_, 0, v___x_1602_);
v___x_1604_ = v___x_1597_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1601_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
lean_inc(v___y_1600_);
v___x_1606_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___y_1600_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = 0;
v___x_1608_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set_uint8(v___x_1608_, sizeof(void*)*1, v___x_1607_);
v___x_1609_ = l_Repr_addAppParen(v___x_1608_, v_prec_1577_);
return v___x_1609_;
}
}
}
}
case 2:
{
lean_object* v_items_1616_; lean_object* v___y_1618_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
lean_dec_ref(v___x_1579_);
lean_dec_ref(v_localinst_1578_);
lean_dec_ref(v_inst_1575_);
v_items_1616_ = lean_ctor_get(v_x_1576_, 0);
lean_inc_ref(v_items_1616_);
lean_dec_ref_known(v_x_1576_, 1);
v___x_1626_ = lean_unsigned_to_nat(1024u);
v___x_1627_ = lean_nat_dec_le(v___x_1626_, v_prec_1577_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1618_ = v___x_1628_;
goto v___jp_1617_;
}
else
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1618_ = v___x_1629_;
goto v___jp_1617_;
}
v___jp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1619_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__8));
v___x_1620_ = l_Array_repr___redArg(v___x_1580_, v_items_1616_);
v___x_1621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
lean_inc(v___y_1618_);
v___x_1622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___y_1618_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = 0;
v___x_1624_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set_uint8(v___x_1624_, sizeof(void*)*1, v___x_1623_);
v___x_1625_ = l_Repr_addAppParen(v___x_1624_, v_prec_1577_);
return v___x_1625_;
}
}
case 3:
{
lean_object* v_start_1630_; lean_object* v_items_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v___x_1579_);
lean_dec_ref(v_localinst_1578_);
lean_dec_ref(v_inst_1575_);
v_start_1630_ = lean_ctor_get(v_x_1576_, 0);
v_items_1631_ = lean_ctor_get(v_x_1576_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_x_1576_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1633_ = v_x_1576_;
v_isShared_1634_ = v_isSharedCheck_1666_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_items_1631_);
lean_inc(v_start_1630_);
lean_dec(v_x_1576_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1666_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1651_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = lean_unsigned_to_nat(1024u);
v___x_1663_ = lean_nat_dec_le(v___x_1662_, v_prec_1577_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1651_ = v___x_1664_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1651_ = v___x_1665_;
goto v___jp_1650_;
}
v___jp_1635_:
{
lean_object* v___x_1641_; 
lean_inc(v___y_1637_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set_tag(v___x_1633_, 5);
lean_ctor_set(v___x_1633_, 1, v___y_1639_);
lean_ctor_set(v___x_1633_, 0, v___y_1637_);
v___x_1641_ = v___x_1633_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___y_1637_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v___y_1639_);
v___x_1641_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_inc(v___y_1636_);
v___x_1642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v___y_1636_);
v___x_1643_ = l_Array_repr___redArg(v___x_1580_, v_items_1631_);
v___x_1644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
lean_inc(v___y_1638_);
v___x_1645_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___y_1638_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = 0;
v___x_1647_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*1, v___x_1646_);
v___x_1648_ = l_Repr_addAppParen(v___x_1647_, v_prec_1577_);
return v___x_1648_;
}
}
v___jp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1652_ = lean_box(1);
v___x_1653_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__11));
v___x_1654_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___redArg___closed__12, &l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12);
v___x_1655_ = lean_int_dec_lt(v_start_1630_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = l_Int_repr(v_start_1630_);
lean_dec(v_start_1630_);
v___x_1657_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
v___y_1636_ = v___x_1652_;
v___y_1637_ = v___x_1653_;
v___y_1638_ = v___y_1651_;
v___y_1639_ = v___x_1657_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1658_ = lean_unsigned_to_nat(1024u);
v___x_1659_ = l_Int_repr(v_start_1630_);
lean_dec(v_start_1630_);
v___x_1660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
v___x_1661_ = l_Repr_addAppParen(v___x_1660_, v___x_1658_);
v___y_1636_ = v___x_1652_;
v___y_1637_ = v___x_1653_;
v___y_1638_ = v___y_1651_;
v___y_1639_ = v___x_1661_;
goto v___jp_1635_;
}
}
}
}
case 4:
{
lean_object* v_items_1667_; lean_object* v___x_1668_; lean_object* v___y_1670_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
lean_dec_ref(v___x_1580_);
lean_dec_ref(v_inst_1575_);
v_items_1667_ = lean_ctor_get(v_x_1576_, 0);
lean_inc_ref(v_items_1667_);
lean_dec_ref_known(v_x_1576_, 1);
v___x_1668_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1668_, 0, lean_box(0));
lean_closure_set(v___x_1668_, 1, lean_box(0));
lean_closure_set(v___x_1668_, 2, v___x_1579_);
lean_closure_set(v___x_1668_, 3, v_localinst_1578_);
v___x_1678_ = lean_unsigned_to_nat(1024u);
v___x_1679_ = lean_nat_dec_le(v___x_1678_, v_prec_1577_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1670_ = v___x_1680_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1670_ = v___x_1681_;
goto v___jp_1669_;
}
v___jp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1671_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__15));
v___x_1672_ = l_Array_repr___redArg(v___x_1668_, v_items_1667_);
v___x_1673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
lean_inc(v___y_1670_);
v___x_1674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___y_1670_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = 0;
v___x_1676_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set_uint8(v___x_1676_, sizeof(void*)*1, v___x_1675_);
v___x_1677_ = l_Repr_addAppParen(v___x_1676_, v_prec_1577_);
return v___x_1677_;
}
}
case 5:
{
lean_object* v_items_1682_; lean_object* v___y_1684_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
lean_dec_ref(v___x_1580_);
lean_dec_ref(v___x_1579_);
lean_dec_ref(v_inst_1575_);
v_items_1682_ = lean_ctor_get(v_x_1576_, 0);
lean_inc_ref(v_items_1682_);
lean_dec_ref_known(v_x_1576_, 1);
v___x_1692_ = lean_unsigned_to_nat(1024u);
v___x_1693_ = lean_nat_dec_le(v___x_1692_, v_prec_1577_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1684_ = v___x_1694_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1684_ = v___x_1695_;
goto v___jp_1683_;
}
v___jp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1685_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__18));
v___x_1686_ = l_Array_repr___redArg(v_localinst_1578_, v_items_1682_);
v___x_1687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
lean_inc(v___y_1684_);
v___x_1688_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___y_1684_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = 0;
v___x_1690_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set_uint8(v___x_1690_, sizeof(void*)*1, v___x_1689_);
v___x_1691_ = l_Repr_addAppParen(v___x_1690_, v_prec_1577_);
return v___x_1691_;
}
}
case 6:
{
lean_object* v_content_1696_; lean_object* v___y_1698_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
lean_dec_ref(v___x_1580_);
lean_dec_ref(v___x_1579_);
lean_dec_ref(v_inst_1575_);
v_content_1696_ = lean_ctor_get(v_x_1576_, 0);
lean_inc_ref(v_content_1696_);
lean_dec_ref_known(v_x_1576_, 1);
v___x_1706_ = lean_unsigned_to_nat(1024u);
v___x_1707_ = lean_nat_dec_le(v___x_1706_, v_prec_1577_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1698_ = v___x_1708_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1698_ = v___x_1709_;
goto v___jp_1697_;
}
v___jp_1697_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1699_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__21));
v___x_1700_ = l_Array_repr___redArg(v_localinst_1578_, v_content_1696_);
v___x_1701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
lean_inc(v___y_1698_);
v___x_1702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___y_1698_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = 0;
v___x_1704_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*1, v___x_1703_);
v___x_1705_ = l_Repr_addAppParen(v___x_1704_, v_prec_1577_);
return v___x_1705_;
}
}
default: 
{
lean_object* v_container_1710_; lean_object* v_content_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref(v___x_1580_);
lean_dec_ref(v___x_1579_);
v_container_1710_ = lean_ctor_get(v_x_1576_, 0);
v_content_1711_ = lean_ctor_get(v_x_1576_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_x_1576_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1713_ = v_x_1576_;
v_isShared_1714_ = v_isSharedCheck_1735_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_content_1711_);
lean_inc(v_container_1710_);
lean_dec(v_x_1576_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1735_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___y_1716_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = lean_unsigned_to_nat(1024u);
v___x_1732_ = lean_nat_dec_le(v___x_1731_, v_prec_1577_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1716_ = v___x_1733_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1716_ = v___x_1734_;
goto v___jp_1715_;
}
v___jp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1717_ = lean_box(1);
v___x_1718_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__24));
v___x_1719_ = lean_unsigned_to_nat(1024u);
v___x_1720_ = lean_apply_2(v_inst_1575_, v_container_1710_, v___x_1719_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 5);
lean_ctor_set(v___x_1713_, 1, v___x_1720_);
lean_ctor_set(v___x_1713_, 0, v___x_1718_);
v___x_1722_ = v___x_1713_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v___x_1717_);
v___x_1724_ = l_Array_repr___redArg(v_localinst_1578_, v_content_1711_);
v___x_1725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
lean_inc(v___y_1716_);
v___x_1726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1716_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = 0;
v___x_1728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set_uint8(v___x_1728_, sizeof(void*)*1, v___x_1727_);
v___x_1729_ = l_Repr_addAppParen(v___x_1728_, v_prec_1577_);
return v___x_1729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr(lean_object* v_i_1736_, lean_object* v_b_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_x_1740_, lean_object* v_prec_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1738_, v_inst_1739_, v_x_1740_, v_prec_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___boxed(lean_object* v_i_1743_, lean_object* v_b_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_x_1747_, lean_object* v_prec_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Doc_instReprBlock_repr(v_i_1743_, v_b_1744_, v_inst_1745_, v_inst_1746_, v_x_1747_, v_prec_1748_);
lean_dec(v_prec_1748_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock___redArg(lean_object* v_inst_1750_, lean_object* v_inst_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1752_, 0, lean_box(0));
lean_closure_set(v___x_1752_, 1, lean_box(0));
lean_closure_set(v___x_1752_, 2, v_inst_1750_);
lean_closure_set(v___x_1752_, 3, v_inst_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock(lean_object* v_i_1753_, lean_object* v_b_1754_, lean_object* v_inst_1755_, lean_object* v_inst_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1757_, 0, lean_box(0));
lean_closure_set(v___x_1757_, 1, lean_box(0));
lean_closure_set(v___x_1757_, 2, v_inst_1755_);
lean_closure_set(v___x_1757_, 3, v_inst_1756_);
return v___x_1757_;
}
}
lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg(){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlock_default___redArg___closed__1));
return v___x_1763_;
}
}
LEAN_EXPORT void l_Lean_Doc_instInhabitedBlock_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1764_;
v_res_1764_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
stack->m_obj
 = v_res_1764_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg___boxed(lean_object* v___dummy_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
return v_res_1766_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedBlock_default___closed__0(void){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default(lean_object* v_i_1768_, lean_object* v_b_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1770_;
}
}
lean_object* l_Lean_Doc_instInhabitedBlock___redArg(){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1772_;
}
}
LEAN_EXPORT void l_Lean_Doc_instInhabitedBlock___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1773_;
v_res_1773_ = l_Lean_Doc_instInhabitedBlock___redArg();
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg___boxed(lean_object* v___dummy_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Doc_instInhabitedBlock___redArg();
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock(lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1778_;
}
}
lean_object* l_Lean_Doc_Block_empty___redArg(){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = ((lean_object*)(l_Lean_Doc_Block_empty___redArg___closed__1));
return v___x_1784_;
}
}
LEAN_EXPORT void l_Lean_Doc_Block_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1785_;
v_res_1785_ = l_Lean_Doc_Block_empty___redArg();
stack->m_obj
 = v_res_1785_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg___boxed(lean_object* v___dummy_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Doc_Block_empty___redArg();
return v_res_1787_;
}
}
static lean_object* _init_l_Lean_Doc_Block_empty___closed__0(void){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Doc_Block_empty___redArg();
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty(lean_object* v_i_1789_, lean_object* v_b_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = lean_obj_once(&l_Lean_Doc_Block_empty___closed__0, &l_Lean_Doc_Block_empty___closed__0_once, _init_l_Lean_Doc_Block_empty___closed__0);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg(lean_object* v_x_1792_){
_start:
{
lean_inc_ref(v_x_1792_);
return v_x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg___boxed(lean_object* v_x_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_Doc_Block_cast___redArg(v_x_1793_);
lean_dec_ref(v_x_1793_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast(lean_object* v_i_1795_, lean_object* v_i_x27_1796_, lean_object* v_b_1797_, lean_object* v_b_x27_1798_, lean_object* v_inlines__eq_1799_, lean_object* v_blocks__eq_1800_, lean_object* v_x_1801_){
_start:
{
lean_inc_ref(v_x_1801_);
return v_x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___boxed(lean_object* v_i_1802_, lean_object* v_i_x27_1803_, lean_object* v_b_1804_, lean_object* v_b_x27_1805_, lean_object* v_inlines__eq_1806_, lean_object* v_blocks__eq_1807_, lean_object* v_x_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Doc_Block_cast(v_i_1802_, v_i_x27_1803_, v_b_1804_, v_b_x27_1805_, v_inlines__eq_1806_, v_blocks__eq_1807_, v_x_1808_);
lean_dec_ref(v_x_1808_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___redArg___boxed(lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_x_1813_, lean_object* v_x_1814_){
_start:
{
uint8_t v_res_1815_; lean_object* v_r_1816_; 
v_res_1815_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1810_, v_inst_1811_, v_inst_1812_, v_x_1813_, v_x_1814_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
uint8_t l_Lean_Doc_instBEqPart_beq___redArg(lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v_title_1822_; lean_object* v_titleString_1823_; lean_object* v_metadata_1824_; lean_object* v_content_1825_; lean_object* v_subParts_1826_; lean_object* v_title_1827_; lean_object* v_titleString_1828_; lean_object* v_metadata_1829_; lean_object* v_content_1830_; lean_object* v_subParts_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_title_1822_ = lean_ctor_get(v_x_1820_, 0);
lean_inc_ref(v_title_1822_);
v_titleString_1823_ = lean_ctor_get(v_x_1820_, 1);
lean_inc_ref(v_titleString_1823_);
v_metadata_1824_ = lean_ctor_get(v_x_1820_, 2);
lean_inc(v_metadata_1824_);
v_content_1825_ = lean_ctor_get(v_x_1820_, 3);
lean_inc_ref(v_content_1825_);
v_subParts_1826_ = lean_ctor_get(v_x_1820_, 4);
lean_inc_ref(v_subParts_1826_);
lean_dec_ref(v_x_1820_);
v_title_1827_ = lean_ctor_get(v_x_1821_, 0);
lean_inc_ref(v_title_1827_);
v_titleString_1828_ = lean_ctor_get(v_x_1821_, 1);
lean_inc_ref(v_titleString_1828_);
v_metadata_1829_ = lean_ctor_get(v_x_1821_, 2);
lean_inc(v_metadata_1829_);
v_content_1830_ = lean_ctor_get(v_x_1821_, 3);
lean_inc_ref(v_content_1830_);
v_subParts_1831_ = lean_ctor_get(v_x_1821_, 4);
lean_inc_ref(v_subParts_1831_);
lean_dec_ref(v_x_1821_);
v___x_1832_ = lean_array_get_size(v_title_1822_);
v___x_1833_ = lean_array_get_size(v_title_1827_);
v___x_1834_ = lean_nat_dec_eq(v___x_1832_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_dec_ref(v_subParts_1831_);
lean_dec_ref(v_content_1830_);
lean_dec(v_metadata_1829_);
lean_dec_ref(v_titleString_1828_);
lean_dec_ref(v_title_1827_);
lean_dec_ref(v_subParts_1826_);
lean_dec_ref(v_content_1825_);
lean_dec(v_metadata_1824_);
lean_dec_ref(v_titleString_1823_);
lean_dec_ref(v_title_1822_);
lean_dec_ref(v_inst_1819_);
lean_dec_ref(v_inst_1818_);
lean_dec_ref(v_inst_1817_);
return v___x_1834_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
lean_inc_ref(v_inst_1819_);
lean_inc_ref(v_inst_1818_);
lean_inc_ref_n(v_inst_1817_, 2);
v___x_1835_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___redArg___boxed), 5, 3);
lean_closure_set(v___x_1835_, 0, v_inst_1817_);
lean_closure_set(v___x_1835_, 1, v_inst_1818_);
lean_closure_set(v___x_1835_, 2, v_inst_1819_);
v___x_1836_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1836_, 0, lean_box(0));
lean_closure_set(v___x_1836_, 1, v_inst_1817_);
v___x_1837_ = l_Array_isEqvAux___redArg(v_title_1822_, v_title_1827_, v___x_1836_, v___x_1832_);
lean_dec_ref(v_title_1827_);
lean_dec_ref(v_title_1822_);
if (v___x_1837_ == 0)
{
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_subParts_1831_);
lean_dec_ref(v_content_1830_);
lean_dec(v_metadata_1829_);
lean_dec_ref(v_titleString_1828_);
lean_dec_ref(v_subParts_1826_);
lean_dec_ref(v_content_1825_);
lean_dec(v_metadata_1824_);
lean_dec_ref(v_titleString_1823_);
lean_dec_ref(v_inst_1819_);
lean_dec_ref(v_inst_1818_);
lean_dec_ref(v_inst_1817_);
return v___x_1837_;
}
else
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_string_dec_eq(v_titleString_1823_, v_titleString_1828_);
lean_dec_ref(v_titleString_1828_);
lean_dec_ref(v_titleString_1823_);
if (v___x_1838_ == 0)
{
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_subParts_1831_);
lean_dec_ref(v_content_1830_);
lean_dec(v_metadata_1829_);
lean_dec_ref(v_subParts_1826_);
lean_dec_ref(v_content_1825_);
lean_dec(v_metadata_1824_);
lean_dec_ref(v_inst_1819_);
lean_dec_ref(v_inst_1818_);
lean_dec_ref(v_inst_1817_);
return v___x_1838_;
}
else
{
uint8_t v___x_1839_; 
v___x_1839_ = l_instBEqOption_beq___redArg(v_inst_1819_, v_metadata_1824_, v_metadata_1829_);
if (v___x_1839_ == 0)
{
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_subParts_1831_);
lean_dec_ref(v_content_1830_);
lean_dec_ref(v_subParts_1826_);
lean_dec_ref(v_content_1825_);
lean_dec_ref(v_inst_1818_);
lean_dec_ref(v_inst_1817_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = lean_array_get_size(v_content_1825_);
v___x_1841_ = lean_array_get_size(v_content_1830_);
v___x_1842_ = lean_nat_dec_eq(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_subParts_1831_);
lean_dec_ref(v_content_1830_);
lean_dec_ref(v_subParts_1826_);
lean_dec_ref(v_content_1825_);
lean_dec_ref(v_inst_1818_);
lean_dec_ref(v_inst_1817_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1843_, 0, lean_box(0));
lean_closure_set(v___x_1843_, 1, lean_box(0));
lean_closure_set(v___x_1843_, 2, v_inst_1817_);
lean_closure_set(v___x_1843_, 3, v_inst_1818_);
v___x_1844_ = l_Array_isEqvAux___redArg(v_content_1825_, v_content_1830_, v___x_1843_, v___x_1840_);
lean_dec_ref(v_content_1830_);
lean_dec_ref(v_content_1825_);
if (v___x_1844_ == 0)
{
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_subParts_1831_);
lean_dec_ref(v_subParts_1826_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = lean_array_get_size(v_subParts_1826_);
v___x_1846_ = lean_array_get_size(v_subParts_1831_);
v___x_1847_ = lean_nat_dec_eq(v___x_1845_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_subParts_1831_);
lean_dec_ref(v_subParts_1826_);
return v___x_1847_;
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = l_Array_isEqvAux___redArg(v_subParts_1826_, v_subParts_1831_, v___x_1835_, v___x_1845_);
lean_dec_ref(v_subParts_1831_);
lean_dec_ref(v_subParts_1826_);
return v___x_1848_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqPart_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1817_ = stack[0].m_obj;
lean_object* v_inst_1818_ = stack[1].m_obj;
lean_object* v_inst_1819_ = stack[2].m_obj;
lean_object* v_x_1820_ = stack[3].m_obj;
lean_object* v_x_1821_ = stack[4].m_obj;
uint8_t v_res_1849_;
v_res_1849_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1817_, v_inst_1818_, v_inst_1819_, v_x_1820_, v_x_1821_);
stack->m_num = v_res_1849_;
}
uint8_t l_Lean_Doc_instBEqPart_beq(lean_object* v_i_1850_, lean_object* v_b_1851_, lean_object* v_p_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1853_, v_inst_1854_, v_inst_1855_, v_x_1856_, v_x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT void l_Lean_Doc_instBEqPart_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1853_ = stack[3].m_obj;
lean_object* v_inst_1854_ = stack[4].m_obj;
lean_object* v_inst_1855_ = stack[5].m_obj;
lean_object* v_x_1856_ = stack[6].m_obj;
lean_object* v_x_1857_ = stack[7].m_obj;
uint8_t v_res_1859_;
v_res_1859_ = l_Lean_Doc_instBEqPart_beq(lean_box(0), lean_box(0), lean_box(0), v_inst_1853_, v_inst_1854_, v_inst_1855_, v_x_1856_, v_x_1857_);
stack->m_num = v_res_1859_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___boxed(lean_object* v_i_1860_, lean_object* v_b_1861_, lean_object* v_p_1862_, lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
uint8_t v_res_1868_; lean_object* v_r_1869_; 
v_res_1868_ = l_Lean_Doc_instBEqPart_beq(v_i_1860_, v_b_1861_, v_p_1862_, v_inst_1863_, v_inst_1864_, v_inst_1865_, v_x_1866_, v_x_1867_);
v_r_1869_ = lean_box(v_res_1868_);
return v_r_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart___redArg(lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1873_, 0, lean_box(0));
lean_closure_set(v___x_1873_, 1, lean_box(0));
lean_closure_set(v___x_1873_, 2, lean_box(0));
lean_closure_set(v___x_1873_, 3, v_inst_1870_);
lean_closure_set(v___x_1873_, 4, v_inst_1871_);
lean_closure_set(v___x_1873_, 5, v_inst_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart(lean_object* v_i_1874_, lean_object* v_b_1875_, lean_object* v_p_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_inst_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1880_, 0, lean_box(0));
lean_closure_set(v___x_1880_, 1, lean_box(0));
lean_closure_set(v___x_1880_, 2, lean_box(0));
lean_closure_set(v___x_1880_, 3, v_inst_1877_);
lean_closure_set(v___x_1880_, 4, v_inst_1878_);
lean_closure_set(v___x_1880_, 5, v_inst_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___redArg___boxed(lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_inst_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
uint8_t v_res_1886_; lean_object* v_r_1887_; 
v_res_1886_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1881_, v_inst_1882_, v_inst_1883_, v_x_1884_, v_x_1885_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
uint8_t l_Lean_Doc_instOrdPart_ord___redArg(lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
lean_object* v_title_1893_; lean_object* v_titleString_1894_; lean_object* v_metadata_1895_; lean_object* v_content_1896_; lean_object* v_subParts_1897_; lean_object* v_title_1898_; lean_object* v_titleString_1899_; lean_object* v_metadata_1900_; lean_object* v_content_1901_; lean_object* v_subParts_1902_; lean_object* v___x_1903_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v_title_1893_ = lean_ctor_get(v_x_1891_, 0);
lean_inc_ref(v_title_1893_);
v_titleString_1894_ = lean_ctor_get(v_x_1891_, 1);
lean_inc_ref(v_titleString_1894_);
v_metadata_1895_ = lean_ctor_get(v_x_1891_, 2);
lean_inc(v_metadata_1895_);
v_content_1896_ = lean_ctor_get(v_x_1891_, 3);
lean_inc_ref(v_content_1896_);
v_subParts_1897_ = lean_ctor_get(v_x_1891_, 4);
lean_inc_ref(v_subParts_1897_);
lean_dec_ref(v_x_1891_);
v_title_1898_ = lean_ctor_get(v_x_1892_, 0);
lean_inc_ref(v_title_1898_);
v_titleString_1899_ = lean_ctor_get(v_x_1892_, 1);
lean_inc_ref(v_titleString_1899_);
v_metadata_1900_ = lean_ctor_get(v_x_1892_, 2);
lean_inc(v_metadata_1900_);
v_content_1901_ = lean_ctor_get(v_x_1892_, 3);
lean_inc_ref(v_content_1901_);
v_subParts_1902_ = lean_ctor_get(v_x_1892_, 4);
lean_inc_ref(v_subParts_1902_);
lean_dec_ref(v_x_1892_);
lean_inc_ref(v_inst_1890_);
lean_inc_ref(v_inst_1889_);
lean_inc_ref_n(v_inst_1888_, 2);
v___x_1903_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___redArg___boxed), 5, 3);
lean_closure_set(v___x_1903_, 0, v_inst_1888_);
lean_closure_set(v___x_1903_, 1, v_inst_1889_);
lean_closure_set(v___x_1903_, 2, v_inst_1890_);
v___x_1909_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1909_, 0, lean_box(0));
lean_closure_set(v___x_1909_, 1, v_inst_1888_);
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1909_, v_title_1893_, v_title_1898_, v___x_1910_);
lean_dec_ref(v_title_1898_);
lean_dec_ref(v_title_1893_);
if (v___x_1911_ == 1)
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_string_compare(v_titleString_1894_, v_titleString_1899_);
lean_dec_ref(v_titleString_1899_);
lean_dec_ref(v_titleString_1894_);
if (v___x_1912_ == 1)
{
if (lean_obj_tag(v_metadata_1895_) == 0)
{
lean_dec_ref(v_inst_1890_);
if (lean_obj_tag(v_metadata_1900_) == 0)
{
goto v___jp_1904_;
}
else
{
uint8_t v___x_1913_; 
lean_dec_ref_known(v_metadata_1900_, 1);
lean_dec_ref(v___x_1903_);
lean_dec_ref(v_subParts_1902_);
lean_dec_ref(v_content_1901_);
lean_dec_ref(v_subParts_1897_);
lean_dec_ref(v_content_1896_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
v___x_1913_ = 0;
return v___x_1913_;
}
}
else
{
if (lean_obj_tag(v_metadata_1900_) == 0)
{
uint8_t v___x_1914_; 
lean_dec_ref_known(v_metadata_1895_, 1);
lean_dec_ref(v___x_1903_);
lean_dec_ref(v_subParts_1902_);
lean_dec_ref(v_content_1901_);
lean_dec_ref(v_subParts_1897_);
lean_dec_ref(v_content_1896_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
v___x_1914_ = 2;
return v___x_1914_;
}
else
{
lean_object* v_val_1915_; lean_object* v_val_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v_val_1915_ = lean_ctor_get(v_metadata_1895_, 0);
lean_inc(v_val_1915_);
lean_dec_ref_known(v_metadata_1895_, 1);
v_val_1916_ = lean_ctor_get(v_metadata_1900_, 0);
lean_inc(v_val_1916_);
lean_dec_ref_known(v_metadata_1900_, 1);
v___x_1917_ = lean_apply_2(v_inst_1890_, v_val_1915_, v_val_1916_);
v___x_1918_ = lean_unbox(v___x_1917_);
if (v___x_1918_ == 1)
{
goto v___jp_1904_;
}
else
{
uint8_t v___x_1919_; 
lean_dec_ref(v___x_1903_);
lean_dec_ref(v_subParts_1902_);
lean_dec_ref(v_content_1901_);
lean_dec_ref(v_subParts_1897_);
lean_dec_ref(v_content_1896_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
v___x_1919_ = lean_unbox(v___x_1917_);
return v___x_1919_;
}
}
}
}
else
{
lean_dec_ref(v___x_1903_);
lean_dec_ref(v_subParts_1902_);
lean_dec_ref(v_content_1901_);
lean_dec(v_metadata_1900_);
lean_dec_ref(v_subParts_1897_);
lean_dec_ref(v_content_1896_);
lean_dec(v_metadata_1895_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
return v___x_1912_;
}
}
else
{
lean_dec_ref(v___x_1903_);
lean_dec_ref(v_subParts_1902_);
lean_dec_ref(v_content_1901_);
lean_dec(v_metadata_1900_);
lean_dec_ref(v_titleString_1899_);
lean_dec_ref(v_subParts_1897_);
lean_dec_ref(v_content_1896_);
lean_dec(v_metadata_1895_);
lean_dec_ref(v_titleString_1894_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
return v___x_1911_;
}
v___jp_1904_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1905_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1905_, 0, lean_box(0));
lean_closure_set(v___x_1905_, 1, lean_box(0));
lean_closure_set(v___x_1905_, 2, v_inst_1888_);
lean_closure_set(v___x_1905_, 3, v_inst_1889_);
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1905_, v_content_1896_, v_content_1901_, v___x_1906_);
lean_dec_ref(v_content_1901_);
lean_dec_ref(v_content_1896_);
if (v___x_1907_ == 1)
{
uint8_t v___x_1908_; 
v___x_1908_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1903_, v_subParts_1897_, v_subParts_1902_, v___x_1906_);
lean_dec_ref(v_subParts_1902_);
lean_dec_ref(v_subParts_1897_);
return v___x_1908_;
}
else
{
lean_dec_ref(v___x_1903_);
lean_dec_ref(v_subParts_1902_);
lean_dec_ref(v_subParts_1897_);
return v___x_1907_;
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdPart_ord___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1888_ = stack[0].m_obj;
lean_object* v_inst_1889_ = stack[1].m_obj;
lean_object* v_inst_1890_ = stack[2].m_obj;
lean_object* v_x_1891_ = stack[3].m_obj;
lean_object* v_x_1892_ = stack[4].m_obj;
uint8_t v_res_1920_;
v_res_1920_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1888_, v_inst_1889_, v_inst_1890_, v_x_1891_, v_x_1892_);
stack->m_num = v_res_1920_;
}
uint8_t l_Lean_Doc_instOrdPart_ord(lean_object* v_i_1921_, lean_object* v_b_1922_, lean_object* v_p_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_){
_start:
{
uint8_t v___x_1929_; 
v___x_1929_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1924_, v_inst_1925_, v_inst_1926_, v_x_1927_, v_x_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT void l_Lean_Doc_instOrdPart_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1924_ = stack[3].m_obj;
lean_object* v_inst_1925_ = stack[4].m_obj;
lean_object* v_inst_1926_ = stack[5].m_obj;
lean_object* v_x_1927_ = stack[6].m_obj;
lean_object* v_x_1928_ = stack[7].m_obj;
uint8_t v_res_1930_;
v_res_1930_ = l_Lean_Doc_instOrdPart_ord(lean_box(0), lean_box(0), lean_box(0), v_inst_1924_, v_inst_1925_, v_inst_1926_, v_x_1927_, v_x_1928_);
stack->m_num = v_res_1930_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___boxed(lean_object* v_i_1931_, lean_object* v_b_1932_, lean_object* v_p_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_inst_1936_, lean_object* v_x_1937_, lean_object* v_x_1938_){
_start:
{
uint8_t v_res_1939_; lean_object* v_r_1940_; 
v_res_1939_ = l_Lean_Doc_instOrdPart_ord(v_i_1931_, v_b_1932_, v_p_1933_, v_inst_1934_, v_inst_1935_, v_inst_1936_, v_x_1937_, v_x_1938_);
v_r_1940_ = lean_box(v_res_1939_);
return v_r_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart___redArg(lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1944_, 0, lean_box(0));
lean_closure_set(v___x_1944_, 1, lean_box(0));
lean_closure_set(v___x_1944_, 2, lean_box(0));
lean_closure_set(v___x_1944_, 3, v_inst_1941_);
lean_closure_set(v___x_1944_, 4, v_inst_1942_);
lean_closure_set(v___x_1944_, 5, v_inst_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart(lean_object* v_i_1945_, lean_object* v_b_1946_, lean_object* v_p_1947_, lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1951_, 0, lean_box(0));
lean_closure_set(v___x_1951_, 1, lean_box(0));
lean_closure_set(v___x_1951_, 2, lean_box(0));
lean_closure_set(v___x_1951_, 3, v_inst_1948_);
lean_closure_set(v___x_1951_, 4, v_inst_1949_);
lean_closure_set(v___x_1951_, 5, v_inst_1950_);
return v___x_1951_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_unsigned_to_nat(9u);
v___x_1962_ = lean_nat_to_int(v___x_1961_);
return v___x_1962_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_unsigned_to_nat(15u);
v___x_1967_ = lean_nat_to_int(v___x_1966_);
return v___x_1967_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = lean_unsigned_to_nat(11u);
v___x_1975_ = lean_nat_to_int(v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg___boxed(lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_inst_1981_, lean_object* v_x_1982_, lean_object* v_prec_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_1979_, v_inst_1980_, v_inst_1981_, v_x_1982_, v_prec_1983_);
lean_dec(v_prec_1983_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg(lean_object* v_inst_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_, lean_object* v_x_1988_, lean_object* v_prec_1989_){
_start:
{
lean_object* v_title_1990_; lean_object* v_titleString_1991_; lean_object* v_metadata_1992_; lean_object* v_content_1993_; lean_object* v_subParts_1994_; lean_object* v_localinst_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_title_1990_ = lean_ctor_get(v_x_1988_, 0);
lean_inc_ref(v_title_1990_);
v_titleString_1991_ = lean_ctor_get(v_x_1988_, 1);
lean_inc_ref(v_titleString_1991_);
v_metadata_1992_ = lean_ctor_get(v_x_1988_, 2);
lean_inc(v_metadata_1992_);
v_content_1993_ = lean_ctor_get(v_x_1988_, 3);
lean_inc_ref(v_content_1993_);
v_subParts_1994_ = lean_ctor_get(v_x_1988_, 4);
lean_inc_ref(v_subParts_1994_);
lean_dec_ref(v_x_1988_);
lean_inc_ref(v_inst_1987_);
lean_inc_ref(v_inst_1986_);
lean_inc_ref_n(v_inst_1985_, 2);
v_localinst_1995_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___redArg___boxed), 5, 3);
lean_closure_set(v_localinst_1995_, 0, v_inst_1985_);
lean_closure_set(v_localinst_1995_, 1, v_inst_1986_);
lean_closure_set(v_localinst_1995_, 2, v_inst_1987_);
v___x_1996_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1997_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__3));
v___x_1998_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4);
v___x_1999_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1999_, 0, lean_box(0));
lean_closure_set(v___x_1999_, 1, v_inst_1985_);
v___x_2000_ = l_Array_repr___redArg(v___x_1999_, v_title_1990_);
v___x_2001_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1998_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = 0;
v___x_2003_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2003_, 0, v___x_2001_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*1, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_1997_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_2006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2004_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = lean_box(1);
v___x_2008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__6));
v___x_2010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2008_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___x_1996_);
v___x_2012_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7);
v___x_2013_ = l_String_quote(v_titleString_1991_);
v___x_2014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
v___x_2015_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2012_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*1, v___x_2002_);
v___x_2017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2011_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
lean_ctor_set(v___x_2018_, 1, v___x_2005_);
v___x_2019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v___x_2007_);
v___x_2020_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__9));
v___x_2021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2019_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_ctor_set(v___x_2022_, 1, v___x_1996_);
v___x_2023_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = l_Option_repr___redArg(v_inst_1987_, v_metadata_1992_, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2023_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*1, v___x_2002_);
v___x_2028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2022_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
lean_ctor_set(v___x_2029_, 1, v___x_2005_);
v___x_2030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v___x_2007_);
v___x_2031_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__11));
v___x_2032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v___x_1996_);
v___x_2034_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12);
v___x_2035_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_2035_, 0, lean_box(0));
lean_closure_set(v___x_2035_, 1, lean_box(0));
lean_closure_set(v___x_2035_, 2, v_inst_1985_);
lean_closure_set(v___x_2035_, 3, v_inst_1986_);
v___x_2036_ = l_Array_repr___redArg(v___x_2035_, v_content_1993_);
v___x_2037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2034_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*1, v___x_2002_);
v___x_2039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2033_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v___x_2005_);
v___x_2041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
lean_ctor_set(v___x_2041_, 1, v___x_2007_);
v___x_2042_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__14));
v___x_2043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_1996_);
v___x_2045_ = l_Array_repr___redArg(v_localinst_1995_, v_subParts_1994_);
v___x_2046_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2023_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*1, v___x_2002_);
v___x_2048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2044_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_2050_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_2051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v___x_2048_);
v___x_2052_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_2053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2049_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*1, v___x_2002_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr(lean_object* v_i_2056_, lean_object* v_b_2057_, lean_object* v_p_2058_, lean_object* v_inst_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_x_2062_, lean_object* v_prec_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_2059_, v_inst_2060_, v_inst_2061_, v_x_2062_, v_prec_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___boxed(lean_object* v_i_2065_, lean_object* v_b_2066_, lean_object* v_p_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_x_2071_, lean_object* v_prec_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Doc_instReprPart_repr(v_i_2065_, v_b_2066_, v_p_2067_, v_inst_2068_, v_inst_2069_, v_inst_2070_, v_x_2071_, v_prec_2072_);
lean_dec(v_prec_2072_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart___redArg(lean_object* v_inst_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2077_, 0, lean_box(0));
lean_closure_set(v___x_2077_, 1, lean_box(0));
lean_closure_set(v___x_2077_, 2, lean_box(0));
lean_closure_set(v___x_2077_, 3, v_inst_2074_);
lean_closure_set(v___x_2077_, 4, v_inst_2075_);
lean_closure_set(v___x_2077_, 5, v_inst_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart(lean_object* v_i_2078_, lean_object* v_b_2079_, lean_object* v_p_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2084_, 0, lean_box(0));
lean_closure_set(v___x_2084_, 1, lean_box(0));
lean_closure_set(v___x_2084_, 2, lean_box(0));
lean_closure_set(v___x_2084_, 3, v_inst_2081_);
lean_closure_set(v___x_2084_, 4, v_inst_2082_);
lean_closure_set(v___x_2084_, 5, v_inst_2083_);
return v___x_2084_;
}
}
lean_object* l_Lean_Doc_instInhabitedPart_default___redArg(){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = ((lean_object*)(l_Lean_Doc_instInhabitedPart_default___redArg___closed__0));
return v___x_2090_;
}
}
LEAN_EXPORT void l_Lean_Doc_instInhabitedPart_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2091_;
v_res_2091_ = l_Lean_Doc_instInhabitedPart_default___redArg();
stack->m_obj
 = v_res_2091_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg___boxed(lean_object* v___dummy_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Doc_instInhabitedPart_default___redArg();
return v_res_2093_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedPart_default___closed__0(void){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Doc_instInhabitedPart_default___redArg();
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default(lean_object* v_i_2095_, lean_object* v_b_2096_, lean_object* v_p_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2098_;
}
}
lean_object* l_Lean_Doc_instInhabitedPart___redArg(){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2100_;
}
}
LEAN_EXPORT void l_Lean_Doc_instInhabitedPart___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2101_;
v_res_2101_ = l_Lean_Doc_instInhabitedPart___redArg();
stack->m_obj
 = v_res_2101_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg___boxed(lean_object* v___dummy_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Doc_instInhabitedPart___redArg();
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart(lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg(lean_object* v_x_2108_){
_start:
{
lean_inc_ref(v_x_2108_);
return v_x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg___boxed(lean_object* v_x_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Doc_Part_cast___redArg(v_x_2109_);
lean_dec_ref(v_x_2109_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast(lean_object* v_i_2111_, lean_object* v_i_x27_2112_, lean_object* v_b_2113_, lean_object* v_b_x27_2114_, lean_object* v_p_2115_, lean_object* v_p_x27_2116_, lean_object* v_inlines__eq_2117_, lean_object* v_blocks__eq_2118_, lean_object* v_metadata__eq_2119_, lean_object* v_x_2120_){
_start:
{
lean_inc_ref(v_x_2120_);
return v_x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___boxed(lean_object* v_i_2121_, lean_object* v_i_x27_2122_, lean_object* v_b_2123_, lean_object* v_b_x27_2124_, lean_object* v_p_2125_, lean_object* v_p_x27_2126_, lean_object* v_inlines__eq_2127_, lean_object* v_blocks__eq_2128_, lean_object* v_metadata__eq_2129_, lean_object* v_x_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Doc_Part_cast(v_i_2121_, v_i_x27_2122_, v_b_2123_, v_b_x27_2124_, v_p_2125_, v_p_x27_2126_, v_inlines__eq_2127_, v_blocks__eq_2128_, v_metadata__eq_2129_, v_x_2130_);
lean_dec_ref(v_x_2130_);
return v_res_2131_;
}
}
lean_object* runtime_initialize_Init_Data_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Compare(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Compare(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Types(builtin);
}
#ifdef __cplusplus
}
#endif
