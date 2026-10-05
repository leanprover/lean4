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
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Doc_MathMode_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Doc_MathMode_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Doc_MathMode_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___redArg(lean_object* v_inline_22_){
_start:
{
lean_inc(v_inline_22_);
return v_inline_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___redArg___boxed(lean_object* v_inline_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Doc_MathMode_inline_elim___redArg(v_inline_23_);
lean_dec(v_inline_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_inline_28_){
_start:
{
lean_inc(v_inline_28_);
return v_inline_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_inline_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Doc_MathMode_inline_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_inline_32_);
lean_dec(v_inline_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___redArg(lean_object* v_display_35_){
_start:
{
lean_inc(v_display_35_);
return v_display_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___redArg___boxed(lean_object* v_display_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Doc_MathMode_display_elim___redArg(v_display_36_);
lean_dec(v_display_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_display_41_){
_start:
{
lean_inc(v_display_41_);
return v_display_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_display_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Doc_MathMode_display_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_display_45_);
lean_dec(v_display_45_);
return v_res_47_;
}
}
static lean_object* _init_l_Lean_Doc_instReprMathMode_repr___closed__4(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(2u);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Doc_instReprMathMode_repr___closed__5(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_nat_to_int(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprMathMode_repr(uint8_t v_x_58_, lean_object* v_prec_59_){
_start:
{
lean_object* v___y_61_; lean_object* v___y_68_; 
if (v_x_58_ == 0)
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1024u);
v___x_75_ = lean_nat_dec_le(v___x_74_, v_prec_59_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_61_ = v___x_76_;
goto v___jp_60_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_61_ = v___x_77_;
goto v___jp_60_;
}
}
else
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1024u);
v___x_79_ = lean_nat_dec_le(v___x_78_, v_prec_59_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_68_ = v___x_80_;
goto v___jp_67_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_68_ = v___x_81_;
goto v___jp_67_;
}
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_62_ = ((lean_object*)(l_Lean_Doc_instReprMathMode_repr___closed__1));
lean_inc(v___y_61_);
v___x_63_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_63_, 0, v___y_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = 0;
v___x_65_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*1, v___x_64_);
v___x_66_ = l_Repr_addAppParen(v___x_65_, v_prec_59_);
return v___x_66_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_69_ = ((lean_object*)(l_Lean_Doc_instReprMathMode_repr___closed__3));
lean_inc(v___y_68_);
v___x_70_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_70_, 0, v___y_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = 0;
v___x_72_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*1, v___x_71_);
v___x_73_ = l_Repr_addAppParen(v___x_72_, v_prec_59_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprMathMode_repr___boxed(lean_object* v_x_82_, lean_object* v_prec_83_){
_start:
{
uint8_t v_x_117__boxed_84_; lean_object* v_res_85_; 
v_x_117__boxed_84_ = lean_unbox(v_x_82_);
v_res_85_ = l_Lean_Doc_instReprMathMode_repr(v_x_117__boxed_84_, v_prec_83_);
lean_dec(v_prec_83_);
return v_res_85_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqMathMode_beq(uint8_t v_x_88_, uint8_t v_y_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_90_ = lean_box(v_x_88_);
v___x_91_ = lean_obj_tag_nat(v___x_90_);
lean_dec(v___x_90_);
v___x_92_ = lean_box(v_y_89_);
v___x_93_ = lean_obj_tag_nat(v___x_92_);
lean_dec(v___x_92_);
v___x_94_ = lean_nat_dec_eq(v___x_91_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqMathMode_beq___boxed(lean_object* v_x_95_, lean_object* v_y_96_){
_start:
{
uint8_t v_x_24__boxed_97_; uint8_t v_y_25__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_x_24__boxed_97_ = lean_unbox(v_x_95_);
v_y_25__boxed_98_ = lean_unbox(v_y_96_);
v_res_99_ = l_Lean_Doc_instBEqMathMode_beq(v_x_24__boxed_97_, v_y_25__boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint64_t l_Lean_Doc_instHashableMathMode_hash(uint8_t v_x_103_){
_start:
{
if (v_x_103_ == 0)
{
uint64_t v___x_104_; 
v___x_104_ = 0ULL;
return v___x_104_;
}
else
{
uint64_t v___x_105_; 
v___x_105_ = 1ULL;
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instHashableMathMode_hash___boxed(lean_object* v_x_106_){
_start:
{
uint8_t v_x_28__boxed_107_; uint64_t v_res_108_; lean_object* v_r_109_; 
v_x_28__boxed_107_ = lean_unbox(v_x_106_);
v_res_108_ = l_Lean_Doc_instHashableMathMode_hash(v_x_28__boxed_107_);
v_r_109_ = lean_box_uint64(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdMathMode_ord(uint8_t v_x_112_, uint8_t v_y_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_114_ = lean_box(v_x_112_);
v___x_115_ = lean_obj_tag_nat(v___x_114_);
lean_dec(v___x_114_);
v___x_116_ = lean_box(v_y_113_);
v___x_117_ = lean_obj_tag_nat(v___x_116_);
lean_dec(v___x_116_);
v___x_118_ = lean_nat_dec_lt(v___x_115_, v___x_117_);
if (v___x_118_ == 0)
{
uint8_t v___x_119_; 
v___x_119_ = lean_nat_dec_eq(v___x_115_, v___x_117_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 2;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 1;
return v___x_121_;
}
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdMathMode_ord___boxed(lean_object* v_x_123_, lean_object* v_y_124_){
_start:
{
uint8_t v_x_33__boxed_125_; uint8_t v_y_34__boxed_126_; uint8_t v_res_127_; lean_object* v_r_128_; 
v_x_33__boxed_125_ = lean_unbox(v_x_123_);
v_y_34__boxed_126_ = lean_unbox(v_y_124_);
v_res_127_ = l_Lean_Doc_instOrdMathMode_ord(v_x_33__boxed_125_, v_y_34__boxed_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl___redArg(lean_object* v_x_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_tag_nat(v_x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl___redArg___boxed(lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_Doc_Inline_ctorIdx___impl___redArg(v_x_133_);
lean_dec_ref(v_x_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl(lean_object* v_i_135_, lean_object* v_x_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_tag_nat(v_x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___impl___boxed(lean_object* v_i_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Doc_Inline_ctorIdx___impl(v_i_138_, v_x_139_);
lean_dec_ref(v_x_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim___redArg(lean_object* v_t_141_, lean_object* v_k_142_){
_start:
{
switch(lean_obj_tag(v_t_141_))
{
case 4:
{
uint8_t v_mode_143_; lean_object* v_string_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_mode_143_ = lean_ctor_get_uint8(v_t_141_, sizeof(void*)*1);
v_string_144_ = lean_ctor_get(v_t_141_, 0);
lean_inc_ref(v_string_144_);
lean_dec_ref_known(v_t_141_, 1);
v___x_145_ = lean_box(v_mode_143_);
v___x_146_ = lean_apply_2(v_k_142_, v___x_145_, v_string_144_);
return v___x_146_;
}
case 6:
{
lean_object* v_content_147_; lean_object* v_url_148_; lean_object* v___x_149_; 
v_content_147_ = lean_ctor_get(v_t_141_, 0);
lean_inc_ref(v_content_147_);
v_url_148_ = lean_ctor_get(v_t_141_, 1);
lean_inc_ref(v_url_148_);
lean_dec_ref_known(v_t_141_, 2);
v___x_149_ = lean_apply_2(v_k_142_, v_content_147_, v_url_148_);
return v___x_149_;
}
case 7:
{
lean_object* v_name_150_; lean_object* v_content_151_; lean_object* v___x_152_; 
v_name_150_ = lean_ctor_get(v_t_141_, 0);
lean_inc_ref(v_name_150_);
v_content_151_ = lean_ctor_get(v_t_141_, 1);
lean_inc_ref(v_content_151_);
lean_dec_ref_known(v_t_141_, 2);
v___x_152_ = lean_apply_2(v_k_142_, v_name_150_, v_content_151_);
return v___x_152_;
}
case 8:
{
lean_object* v_alt_153_; lean_object* v_url_154_; lean_object* v___x_155_; 
v_alt_153_ = lean_ctor_get(v_t_141_, 0);
lean_inc_ref(v_alt_153_);
v_url_154_ = lean_ctor_get(v_t_141_, 1);
lean_inc_ref(v_url_154_);
lean_dec_ref_known(v_t_141_, 2);
v___x_155_ = lean_apply_2(v_k_142_, v_alt_153_, v_url_154_);
return v___x_155_;
}
case 10:
{
lean_object* v_container_156_; lean_object* v_content_157_; lean_object* v___x_158_; 
v_container_156_ = lean_ctor_get(v_t_141_, 0);
lean_inc(v_container_156_);
v_content_157_ = lean_ctor_get(v_t_141_, 1);
lean_inc_ref(v_content_157_);
lean_dec_ref_known(v_t_141_, 2);
v___x_158_ = lean_apply_2(v_k_142_, v_container_156_, v_content_157_);
return v___x_158_;
}
default: 
{
lean_object* v_string_159_; lean_object* v___x_160_; 
v_string_159_ = lean_ctor_get(v_t_141_, 0);
lean_inc_ref(v_string_159_);
lean_dec_ref(v_t_141_);
v___x_160_ = lean_apply_1(v_k_142_, v_string_159_);
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim(lean_object* v_i_161_, lean_object* v_motive__1_162_, lean_object* v_ctorIdx_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_k_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_164_, v_k_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim___boxed(lean_object* v_i_168_, lean_object* v_motive__1_169_, lean_object* v_ctorIdx_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_k_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Doc_Inline_ctorElim(v_i_168_, v_motive__1_169_, v_ctorIdx_170_, v_t_171_, v_h_172_, v_k_173_);
lean_dec(v_ctorIdx_170_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_text_elim___redArg(lean_object* v_t_175_, lean_object* v_text_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_175_, v_text_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_text_elim(lean_object* v_i_178_, lean_object* v_motive__1_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_text_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_180_, v_text_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_emph_elim___redArg(lean_object* v_t_184_, lean_object* v_emph_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_184_, v_emph_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_emph_elim(lean_object* v_i_187_, lean_object* v_motive__1_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_emph_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_189_, v_emph_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_bold_elim___redArg(lean_object* v_t_193_, lean_object* v_bold_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_193_, v_bold_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_bold_elim(lean_object* v_i_196_, lean_object* v_motive__1_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_bold_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_198_, v_bold_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_code_elim___redArg(lean_object* v_t_202_, lean_object* v_code_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_202_, v_code_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_code_elim(lean_object* v_i_205_, lean_object* v_motive__1_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_code_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_207_, v_code_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_math_elim___redArg(lean_object* v_t_211_, lean_object* v_math_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_211_, v_math_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_math_elim(lean_object* v_i_214_, lean_object* v_motive__1_215_, lean_object* v_t_216_, lean_object* v_h_217_, lean_object* v_math_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_216_, v_math_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_linebreak_elim___redArg(lean_object* v_t_220_, lean_object* v_linebreak_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_220_, v_linebreak_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_linebreak_elim(lean_object* v_i_223_, lean_object* v_motive__1_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_linebreak_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_225_, v_linebreak_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_link_elim___redArg(lean_object* v_t_229_, lean_object* v_link_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_229_, v_link_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_link_elim(lean_object* v_i_232_, lean_object* v_motive__1_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_link_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_234_, v_link_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_footnote_elim___redArg(lean_object* v_t_238_, lean_object* v_footnote_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_238_, v_footnote_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_footnote_elim(lean_object* v_i_241_, lean_object* v_motive__1_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_footnote_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_243_, v_footnote_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_image_elim___redArg(lean_object* v_t_247_, lean_object* v_image_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_247_, v_image_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_image_elim(lean_object* v_i_250_, lean_object* v_motive__1_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_image_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_252_, v_image_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_concat_elim___redArg(lean_object* v_t_256_, lean_object* v_concat_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_256_, v_concat_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_concat_elim(lean_object* v_i_259_, lean_object* v_motive__1_260_, lean_object* v_t_261_, lean_object* v_h_262_, lean_object* v_concat_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_261_, v_concat_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_other_elim___redArg(lean_object* v_t_265_, lean_object* v_other_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_265_, v_other_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_other_elim(lean_object* v_i_268_, lean_object* v_motive__1_269_, lean_object* v_t_270_, lean_object* v_h_271_, lean_object* v_other_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_270_, v_other_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline_beq___redArg___boxed(lean_object* v_inst_274_, lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_274_, v_x_275_, v_x_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqInline_beq___redArg(lean_object* v_inst_279_, lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v_decide_284_; 
v___x_282_ = lean_obj_tag_nat(v_x_280_);
v___x_283_ = lean_obj_tag_nat(v_x_281_);
v_decide_284_ = lean_nat_dec_eq(v___x_282_, v___x_283_);
if (v_decide_284_ == 0)
{
lean_dec_ref(v_x_281_);
lean_dec_ref(v_x_280_);
lean_dec_ref(v_inst_279_);
return v_decide_284_;
}
else
{
lean_object* v___x_285_; lean_object* v_content_287_; lean_object* v_content_x27_288_; 
lean_inc_ref(v_inst_279_);
v___x_285_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___redArg___boxed), 3, 1);
lean_closure_set(v___x_285_, 0, v_inst_279_);
switch(lean_obj_tag(v_x_280_))
{
case 1:
{
lean_object* v_content_293_; lean_object* v_content_294_; 
lean_dec_ref(v_inst_279_);
v_content_293_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_content_293_);
lean_dec_ref_known(v_x_280_, 1);
v_content_294_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_content_294_);
lean_dec_ref(v_x_281_);
v_content_287_ = v_content_293_;
v_content_x27_288_ = v_content_294_;
goto v___jp_286_;
}
case 2:
{
lean_object* v_content_295_; lean_object* v_content_296_; 
lean_dec_ref(v_inst_279_);
v_content_295_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_content_295_);
lean_dec_ref_known(v_x_280_, 1);
v_content_296_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_content_296_);
lean_dec_ref(v_x_281_);
v_content_287_ = v_content_295_;
v_content_x27_288_ = v_content_296_;
goto v___jp_286_;
}
case 4:
{
uint8_t v_mode_297_; lean_object* v_string_298_; uint8_t v_mode_299_; lean_object* v_string_300_; uint8_t v___x_301_; 
lean_dec_ref(v___x_285_);
lean_dec_ref(v_inst_279_);
v_mode_297_ = lean_ctor_get_uint8(v_x_280_, sizeof(void*)*1);
v_string_298_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_string_298_);
lean_dec_ref_known(v_x_280_, 1);
v_mode_299_ = lean_ctor_get_uint8(v_x_281_, sizeof(void*)*1);
v_string_300_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_string_300_);
lean_dec_ref(v_x_281_);
v___x_301_ = l_Lean_Doc_instBEqMathMode_beq(v_mode_297_, v_mode_299_);
if (v___x_301_ == 0)
{
lean_dec_ref(v_string_300_);
lean_dec_ref(v_string_298_);
return v___x_301_;
}
else
{
uint8_t v___x_302_; 
v___x_302_ = lean_string_dec_eq(v_string_298_, v_string_300_);
lean_dec_ref(v_string_300_);
lean_dec_ref(v_string_298_);
return v___x_302_;
}
}
case 6:
{
lean_object* v_content_303_; lean_object* v_url_304_; lean_object* v_content_305_; lean_object* v_url_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
lean_dec_ref(v_inst_279_);
v_content_303_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_content_303_);
v_url_304_ = lean_ctor_get(v_x_280_, 1);
lean_inc_ref(v_url_304_);
lean_dec_ref_known(v_x_280_, 2);
v_content_305_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_content_305_);
v_url_306_ = lean_ctor_get(v_x_281_, 1);
lean_inc_ref(v_url_306_);
lean_dec_ref(v_x_281_);
v___x_307_ = lean_array_get_size(v_content_303_);
v___x_308_ = lean_array_get_size(v_content_305_);
v___x_309_ = lean_nat_dec_eq(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec_ref(v_url_306_);
lean_dec_ref(v_content_305_);
lean_dec_ref(v_url_304_);
lean_dec_ref(v_content_303_);
lean_dec_ref(v___x_285_);
return v___x_309_;
}
else
{
uint8_t v___x_310_; 
v___x_310_ = l_Array_isEqvAux___redArg(v_content_303_, v_content_305_, v___x_285_, v___x_307_);
lean_dec_ref(v_content_305_);
lean_dec_ref(v_content_303_);
if (v___x_310_ == 0)
{
lean_dec_ref(v_url_306_);
lean_dec_ref(v_url_304_);
return v___x_310_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = lean_string_dec_eq(v_url_304_, v_url_306_);
lean_dec_ref(v_url_306_);
lean_dec_ref(v_url_304_);
return v___x_311_;
}
}
}
case 7:
{
lean_object* v_name_312_; lean_object* v_content_313_; lean_object* v_name_314_; lean_object* v_content_315_; uint8_t v___x_316_; 
lean_dec_ref(v_inst_279_);
v_name_312_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_name_312_);
v_content_313_ = lean_ctor_get(v_x_280_, 1);
lean_inc_ref(v_content_313_);
lean_dec_ref_known(v_x_280_, 2);
v_name_314_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_name_314_);
v_content_315_ = lean_ctor_get(v_x_281_, 1);
lean_inc_ref(v_content_315_);
lean_dec_ref(v_x_281_);
v___x_316_ = lean_string_dec_eq(v_name_312_, v_name_314_);
lean_dec_ref(v_name_314_);
lean_dec_ref(v_name_312_);
if (v___x_316_ == 0)
{
lean_dec_ref(v_content_315_);
lean_dec_ref(v_content_313_);
lean_dec_ref(v___x_285_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_array_get_size(v_content_313_);
v___x_318_ = lean_array_get_size(v_content_315_);
v___x_319_ = lean_nat_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_dec_ref(v_content_315_);
lean_dec_ref(v_content_313_);
lean_dec_ref(v___x_285_);
return v___x_319_;
}
else
{
uint8_t v___x_320_; 
v___x_320_ = l_Array_isEqvAux___redArg(v_content_313_, v_content_315_, v___x_285_, v___x_317_);
lean_dec_ref(v_content_315_);
lean_dec_ref(v_content_313_);
return v___x_320_;
}
}
}
case 8:
{
lean_object* v_alt_321_; lean_object* v_url_322_; lean_object* v_alt_323_; lean_object* v_url_324_; uint8_t v___x_325_; 
lean_dec_ref(v___x_285_);
lean_dec_ref(v_inst_279_);
v_alt_321_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_alt_321_);
v_url_322_ = lean_ctor_get(v_x_280_, 1);
lean_inc_ref(v_url_322_);
lean_dec_ref_known(v_x_280_, 2);
v_alt_323_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_alt_323_);
v_url_324_ = lean_ctor_get(v_x_281_, 1);
lean_inc_ref(v_url_324_);
lean_dec_ref(v_x_281_);
v___x_325_ = lean_string_dec_eq(v_alt_321_, v_alt_323_);
lean_dec_ref(v_alt_323_);
lean_dec_ref(v_alt_321_);
if (v___x_325_ == 0)
{
lean_dec_ref(v_url_324_);
lean_dec_ref(v_url_322_);
return v___x_325_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = lean_string_dec_eq(v_url_322_, v_url_324_);
lean_dec_ref(v_url_324_);
lean_dec_ref(v_url_322_);
return v___x_326_;
}
}
case 9:
{
lean_object* v_content_327_; lean_object* v_content_328_; 
lean_dec_ref(v_inst_279_);
v_content_327_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_content_327_);
lean_dec_ref_known(v_x_280_, 1);
v_content_328_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_content_328_);
lean_dec_ref(v_x_281_);
v_content_287_ = v_content_327_;
v_content_x27_288_ = v_content_328_;
goto v___jp_286_;
}
case 10:
{
lean_object* v_container_329_; lean_object* v_content_330_; lean_object* v_container_331_; lean_object* v_content_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_container_329_ = lean_ctor_get(v_x_280_, 0);
lean_inc(v_container_329_);
v_content_330_ = lean_ctor_get(v_x_280_, 1);
lean_inc_ref(v_content_330_);
lean_dec_ref_known(v_x_280_, 2);
v_container_331_ = lean_ctor_get(v_x_281_, 0);
lean_inc(v_container_331_);
v_content_332_ = lean_ctor_get(v_x_281_, 1);
lean_inc_ref(v_content_332_);
lean_dec_ref(v_x_281_);
v___x_333_ = lean_apply_2(v_inst_279_, v_container_329_, v_container_331_);
v___x_334_ = lean_unbox(v___x_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
lean_dec_ref(v_content_332_);
lean_dec_ref(v_content_330_);
lean_dec_ref(v___x_285_);
v___x_335_ = lean_unbox(v___x_333_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = lean_array_get_size(v_content_330_);
v___x_337_ = lean_array_get_size(v_content_332_);
v___x_338_ = lean_nat_dec_eq(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec_ref(v_content_332_);
lean_dec_ref(v_content_330_);
lean_dec_ref(v___x_285_);
return v___x_338_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = l_Array_isEqvAux___redArg(v_content_330_, v_content_332_, v___x_285_, v___x_336_);
lean_dec_ref(v_content_332_);
lean_dec_ref(v_content_330_);
return v___x_339_;
}
}
}
default: 
{
lean_object* v_string_340_; lean_object* v_string_341_; uint8_t v___x_342_; 
lean_dec_ref(v___x_285_);
lean_dec_ref(v_inst_279_);
v_string_340_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_string_340_);
lean_dec_ref(v_x_280_);
v_string_341_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_string_341_);
lean_dec_ref(v_x_281_);
v___x_342_ = lean_string_dec_eq(v_string_340_, v_string_341_);
lean_dec_ref(v_string_341_);
lean_dec_ref(v_string_340_);
return v___x_342_;
}
}
v___jp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_array_get_size(v_content_287_);
v___x_290_ = lean_array_get_size(v_content_x27_288_);
v___x_291_ = lean_nat_dec_eq(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec_ref(v_content_x27_288_);
lean_dec_ref(v_content_287_);
lean_dec_ref(v___x_285_);
return v___x_291_;
}
else
{
uint8_t v___x_292_; 
v___x_292_ = l_Array_isEqvAux___redArg(v_content_287_, v_content_x27_288_, v___x_285_, v___x_289_);
lean_dec_ref(v_content_x27_288_);
lean_dec_ref(v_content_287_);
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqInline_beq(lean_object* v_i_343_, lean_object* v_inst_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_344_, v_x_345_, v_x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline_beq___boxed(lean_object* v_i_348_, lean_object* v_inst_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Lean_Doc_instBEqInline_beq(v_i_348_, v_inst_349_, v_x_350_, v_x_351_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline___redArg(lean_object* v_inst_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_355_, 0, lean_box(0));
lean_closure_set(v___x_355_, 1, v_inst_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline(lean_object* v_i_356_, lean_object* v_inst_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_358_, 0, lean_box(0));
lean_closure_set(v___x_358_, 1, v_inst_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___redArg___boxed(lean_object* v_inst_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_359_, v_x_360_, v_x_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord___redArg(lean_object* v_inst_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = lean_obj_tag_nat(v_x_365_);
v___x_368_ = lean_obj_tag_nat(v_x_366_);
v___x_369_ = lean_nat_dec_lt(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
uint8_t v___x_370_; 
v___x_370_ = lean_nat_dec_eq(v___x_367_, v___x_368_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
lean_dec_ref(v_x_366_);
lean_dec_ref(v_x_365_);
lean_dec_ref(v_inst_364_);
v___x_371_ = 2;
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v_content_374_; lean_object* v_content_x27_375_; 
lean_inc_ref(v_inst_364_);
v___x_372_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___redArg___boxed), 3, 1);
lean_closure_set(v___x_372_, 0, v_inst_364_);
switch(lean_obj_tag(v_x_365_))
{
case 1:
{
lean_object* v_content_378_; lean_object* v_content_379_; 
lean_dec_ref(v_inst_364_);
v_content_378_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_content_378_);
lean_dec_ref_known(v_x_365_, 1);
v_content_379_ = lean_ctor_get(v_x_366_, 0);
lean_inc_ref(v_content_379_);
lean_dec_ref(v_x_366_);
v_content_374_ = v_content_378_;
v_content_x27_375_ = v_content_379_;
goto v___jp_373_;
}
case 2:
{
lean_object* v_content_380_; lean_object* v_content_381_; 
lean_dec_ref(v_inst_364_);
v_content_380_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_content_380_);
lean_dec_ref_known(v_x_365_, 1);
v_content_381_ = lean_ctor_get(v_x_366_, 0);
lean_inc_ref(v_content_381_);
lean_dec_ref(v_x_366_);
v_content_374_ = v_content_380_;
v_content_x27_375_ = v_content_381_;
goto v___jp_373_;
}
case 4:
{
uint8_t v_mode_382_; lean_object* v_string_383_; uint8_t v_mode_384_; lean_object* v_string_385_; uint8_t v___x_386_; 
lean_dec_ref(v___x_372_);
lean_dec_ref(v_inst_364_);
v_mode_382_ = lean_ctor_get_uint8(v_x_365_, sizeof(void*)*1);
v_string_383_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_string_383_);
lean_dec_ref_known(v_x_365_, 1);
v_mode_384_ = lean_ctor_get_uint8(v_x_366_, sizeof(void*)*1);
v_string_385_ = lean_ctor_get(v_x_366_, 0);
lean_inc_ref(v_string_385_);
lean_dec_ref(v_x_366_);
v___x_386_ = l_Lean_Doc_instOrdMathMode_ord(v_mode_382_, v_mode_384_);
if (v___x_386_ == 1)
{
uint8_t v___x_387_; 
v___x_387_ = lean_string_compare(v_string_383_, v_string_385_);
lean_dec_ref(v_string_385_);
lean_dec_ref(v_string_383_);
return v___x_387_;
}
else
{
lean_dec_ref(v_string_385_);
lean_dec_ref(v_string_383_);
return v___x_386_;
}
}
case 6:
{
lean_object* v_content_388_; lean_object* v_url_389_; lean_object* v_content_390_; lean_object* v_url_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
lean_dec_ref(v_inst_364_);
v_content_388_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_content_388_);
v_url_389_ = lean_ctor_get(v_x_365_, 1);
lean_inc_ref(v_url_389_);
lean_dec_ref_known(v_x_365_, 2);
v_content_390_ = lean_ctor_get(v_x_366_, 0);
lean_inc_ref(v_content_390_);
v_url_391_ = lean_ctor_get(v_x_366_, 1);
lean_inc_ref(v_url_391_);
lean_dec_ref(v_x_366_);
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_372_, v_content_388_, v_content_390_, v___x_392_);
lean_dec_ref(v_content_390_);
lean_dec_ref(v_content_388_);
if (v___x_393_ == 1)
{
uint8_t v___x_394_; 
v___x_394_ = lean_string_compare(v_url_389_, v_url_391_);
lean_dec_ref(v_url_391_);
lean_dec_ref(v_url_389_);
return v___x_394_;
}
else
{
lean_dec_ref(v_url_391_);
lean_dec_ref(v_url_389_);
return v___x_393_;
}
}
case 7:
{
lean_object* v_name_395_; lean_object* v_content_396_; lean_object* v_name_397_; lean_object* v_content_398_; uint8_t v___x_399_; 
lean_dec_ref(v_inst_364_);
v_name_395_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_name_395_);
v_content_396_ = lean_ctor_get(v_x_365_, 1);
lean_inc_ref(v_content_396_);
lean_dec_ref_known(v_x_365_, 2);
v_name_397_ = lean_ctor_get(v_x_366_, 0);
lean_inc_ref(v_name_397_);
v_content_398_ = lean_ctor_get(v_x_366_, 1);
lean_inc_ref(v_content_398_);
lean_dec_ref(v_x_366_);
v___x_399_ = lean_string_compare(v_name_395_, v_name_397_);
lean_dec_ref(v_name_397_);
lean_dec_ref(v_name_395_);
if (v___x_399_ == 1)
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_372_, v_content_396_, v_content_398_, v___x_400_);
lean_dec_ref(v_content_398_);
lean_dec_ref(v_content_396_);
return v___x_401_;
}
else
{
lean_dec_ref(v_content_398_);
lean_dec_ref(v_content_396_);
lean_dec_ref(v___x_372_);
return v___x_399_;
}
}
case 8:
{
lean_object* v_alt_402_; lean_object* v_url_403_; lean_object* v_alt_404_; lean_object* v_url_405_; uint8_t v___x_406_; 
lean_dec_ref(v___x_372_);
lean_dec_ref(v_inst_364_);
v_alt_402_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_alt_402_);
v_url_403_ = lean_ctor_get(v_x_365_, 1);
lean_inc_ref(v_url_403_);
lean_dec_ref_known(v_x_365_, 2);
v_alt_404_ = lean_ctor_get(v_x_366_, 0);
lean_inc_ref(v_alt_404_);
v_url_405_ = lean_ctor_get(v_x_366_, 1);
lean_inc_ref(v_url_405_);
lean_dec_ref(v_x_366_);
v___x_406_ = lean_string_compare(v_alt_402_, v_alt_404_);
lean_dec_ref(v_alt_404_);
lean_dec_ref(v_alt_402_);
if (v___x_406_ == 1)
{
uint8_t v___x_407_; 
v___x_407_ = lean_string_compare(v_url_403_, v_url_405_);
lean_dec_ref(v_url_405_);
lean_dec_ref(v_url_403_);
return v___x_407_;
}
else
{
lean_dec_ref(v_url_405_);
lean_dec_ref(v_url_403_);
return v___x_406_;
}
}
case 9:
{
lean_object* v_content_408_; lean_object* v_content_409_; 
lean_dec_ref(v_inst_364_);
v_content_408_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_content_408_);
lean_dec_ref_known(v_x_365_, 1);
v_content_409_ = lean_ctor_get(v_x_366_, 0);
lean_inc_ref(v_content_409_);
lean_dec_ref(v_x_366_);
v_content_374_ = v_content_408_;
v_content_x27_375_ = v_content_409_;
goto v___jp_373_;
}
case 10:
{
lean_object* v_container_410_; lean_object* v_content_411_; lean_object* v_container_412_; lean_object* v_content_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_container_410_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_container_410_);
v_content_411_ = lean_ctor_get(v_x_365_, 1);
lean_inc_ref(v_content_411_);
lean_dec_ref_known(v_x_365_, 2);
v_container_412_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_container_412_);
v_content_413_ = lean_ctor_get(v_x_366_, 1);
lean_inc_ref(v_content_413_);
lean_dec_ref(v_x_366_);
v___x_414_ = lean_apply_2(v_inst_364_, v_container_410_, v_container_412_);
v___x_415_ = lean_unbox(v___x_414_);
if (v___x_415_ == 1)
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_372_, v_content_411_, v_content_413_, v___x_416_);
lean_dec_ref(v_content_413_);
lean_dec_ref(v_content_411_);
return v___x_417_;
}
else
{
uint8_t v___x_418_; 
lean_dec_ref(v_content_413_);
lean_dec_ref(v_content_411_);
lean_dec_ref(v___x_372_);
v___x_418_ = lean_unbox(v___x_414_);
return v___x_418_;
}
}
default: 
{
lean_object* v_string_419_; lean_object* v_string_420_; uint8_t v___x_421_; 
lean_dec_ref(v___x_372_);
lean_dec_ref(v_inst_364_);
v_string_419_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_string_419_);
lean_dec_ref(v_x_365_);
v_string_420_ = lean_ctor_get(v_x_366_, 0);
lean_inc_ref(v_string_420_);
lean_dec_ref(v_x_366_);
v___x_421_ = lean_string_compare(v_string_419_, v_string_420_);
lean_dec_ref(v_string_420_);
lean_dec_ref(v_string_419_);
return v___x_421_;
}
}
v___jp_373_:
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_372_, v_content_374_, v_content_x27_375_, v___x_376_);
lean_dec_ref(v_content_x27_375_);
lean_dec_ref(v_content_374_);
return v___x_377_;
}
}
}
else
{
uint8_t v___x_422_; 
lean_dec_ref(v_x_366_);
lean_dec_ref(v_x_365_);
lean_dec_ref(v_inst_364_);
v___x_422_ = 0;
return v___x_422_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord(lean_object* v_i_423_, lean_object* v_inst_424_, lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_424_, v_x_425_, v_x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___boxed(lean_object* v_i_428_, lean_object* v_inst_429_, lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Lean_Doc_instOrdInline_ord(v_i_428_, v_inst_429_, v_x_430_, v_x_431_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline___redArg(lean_object* v_inst_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_435_, 0, lean_box(0));
lean_closure_set(v___x_435_, 1, v_inst_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline(lean_object* v_i_436_, lean_object* v_inst_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_438_, 0, lean_box(0));
lean_closure_set(v___x_438_, 1, v_inst_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg___boxed(lean_object* v_inst_505_, lean_object* v_x_506_, lean_object* v_prec_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_505_, v_x_506_, v_prec_507_);
lean_dec(v_prec_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg(lean_object* v_inst_509_, lean_object* v_x_510_, lean_object* v_prec_511_){
_start:
{
lean_object* v_localinst_512_; 
lean_inc_ref(v_inst_509_);
v_localinst_512_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_512_, 0, v_inst_509_);
switch(lean_obj_tag(v_x_510_))
{
case 0:
{
lean_object* v_string_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v_localinst_512_);
lean_dec_ref(v_inst_509_);
v_string_513_ = lean_ctor_get(v_x_510_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_533_ == 0)
{
v___x_515_ = v_x_510_;
v_isShared_516_ = v_isSharedCheck_533_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_string_513_);
lean_dec(v_x_510_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_533_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___y_518_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(1024u);
v___x_530_ = lean_nat_dec_le(v___x_529_, v_prec_511_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_518_ = v___x_531_;
goto v___jp_517_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_518_ = v___x_532_;
goto v___jp_517_;
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__2));
v___x_520_ = l_String_quote(v_string_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 3);
lean_ctor_set(v___x_515_, 0, v___x_520_);
v___x_522_ = v___x_515_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_528_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_519_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
lean_inc(v___y_518_);
v___x_524_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_524_, 0, v___y_518_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = 0;
v___x_526_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*1, v___x_525_);
v___x_527_ = l_Repr_addAppParen(v___x_526_, v_prec_511_);
return v___x_527_;
}
}
}
}
case 1:
{
lean_object* v_content_534_; lean_object* v___y_536_; lean_object* v___x_544_; uint8_t v___x_545_; 
lean_dec_ref(v_inst_509_);
v_content_534_ = lean_ctor_get(v_x_510_, 0);
lean_inc_ref(v_content_534_);
lean_dec_ref_known(v_x_510_, 1);
v___x_544_ = lean_unsigned_to_nat(1024u);
v___x_545_ = lean_nat_dec_le(v___x_544_, v_prec_511_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_536_ = v___x_546_;
goto v___jp_535_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_536_ = v___x_547_;
goto v___jp_535_;
}
v___jp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_537_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__5));
v___x_538_ = l_Array_repr___redArg(v_localinst_512_, v_content_534_);
v___x_539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
lean_inc(v___y_536_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___y_536_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = 0;
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_541_);
v___x_543_ = l_Repr_addAppParen(v___x_542_, v_prec_511_);
return v___x_543_;
}
}
case 2:
{
lean_object* v_content_548_; lean_object* v___y_550_; lean_object* v___x_558_; uint8_t v___x_559_; 
lean_dec_ref(v_inst_509_);
v_content_548_ = lean_ctor_get(v_x_510_, 0);
lean_inc_ref(v_content_548_);
lean_dec_ref_known(v_x_510_, 1);
v___x_558_ = lean_unsigned_to_nat(1024u);
v___x_559_ = lean_nat_dec_le(v___x_558_, v_prec_511_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_550_ = v___x_560_;
goto v___jp_549_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_550_ = v___x_561_;
goto v___jp_549_;
}
v___jp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_551_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__8));
v___x_552_ = l_Array_repr___redArg(v_localinst_512_, v_content_548_);
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
lean_inc(v___y_550_);
v___x_554_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_554_, 0, v___y_550_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = 0;
v___x_556_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*1, v___x_555_);
v___x_557_ = l_Repr_addAppParen(v___x_556_, v_prec_511_);
return v___x_557_;
}
}
case 3:
{
lean_object* v_string_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_582_; 
lean_dec_ref(v_localinst_512_);
lean_dec_ref(v_inst_509_);
v_string_562_ = lean_ctor_get(v_x_510_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_582_ == 0)
{
v___x_564_ = v_x_510_;
v_isShared_565_ = v_isSharedCheck_582_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_string_562_);
lean_dec(v_x_510_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_582_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___y_567_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1024u);
v___x_579_ = lean_nat_dec_le(v___x_578_, v_prec_511_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_567_ = v___x_580_;
goto v___jp_566_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_567_ = v___x_581_;
goto v___jp_566_;
}
v___jp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_568_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__11));
v___x_569_ = l_String_quote(v_string_562_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_569_);
v___x_571_ = v___x_564_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_577_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_568_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
lean_inc(v___y_567_);
v___x_573_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_573_, 0, v___y_567_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = 0;
v___x_575_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set_uint8(v___x_575_, sizeof(void*)*1, v___x_574_);
v___x_576_ = l_Repr_addAppParen(v___x_575_, v_prec_511_);
return v___x_576_;
}
}
}
}
case 4:
{
uint8_t v_mode_583_; lean_object* v_string_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v_localinst_512_);
lean_dec_ref(v_inst_509_);
v_mode_583_ = lean_ctor_get_uint8(v_x_510_, sizeof(void*)*1);
v_string_584_ = lean_ctor_get(v_x_510_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_609_ == 0)
{
v___x_586_ = v_x_510_;
v_isShared_587_ = v_isSharedCheck_609_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_string_584_);
lean_dec(v_x_510_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_609_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___y_589_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(1024u);
v___x_606_ = lean_nat_dec_le(v___x_605_, v_prec_511_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
v___x_607_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_589_ = v___x_607_;
goto v___jp_588_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_589_ = v___x_608_;
goto v___jp_588_;
}
v___jp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; lean_object* v___x_602_; 
v___x_590_ = lean_box(1);
v___x_591_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__14));
v___x_592_ = lean_unsigned_to_nat(1024u);
v___x_593_ = l_Lean_Doc_instReprMathMode_repr(v_mode_583_, v___x_592_);
v___x_594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_591_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_590_);
v___x_596_ = l_String_quote(v_string_584_);
v___x_597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_inc(v___y_589_);
v___x_599_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_599_, 0, v___y_589_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = 0;
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 6);
lean_ctor_set(v___x_586_, 0, v___x_599_);
v___x_602_ = v___x_586_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_599_);
v___x_602_ = v_reuseFailAlloc_604_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; 
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*1, v___x_600_);
v___x_603_ = l_Repr_addAppParen(v___x_602_, v_prec_511_);
return v___x_603_;
}
}
}
}
case 5:
{
lean_object* v_string_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_localinst_512_);
lean_dec_ref(v_inst_509_);
v_string_610_ = lean_ctor_get(v_x_510_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_630_ == 0)
{
v___x_612_ = v_x_510_;
v_isShared_613_ = v_isSharedCheck_630_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_string_610_);
lean_dec(v_x_510_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_630_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___y_615_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(1024u);
v___x_627_ = lean_nat_dec_le(v___x_626_, v_prec_511_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_615_ = v___x_628_;
goto v___jp_614_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_615_ = v___x_629_;
goto v___jp_614_;
}
v___jp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_616_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__17));
v___x_617_ = l_String_quote(v_string_610_);
if (v_isShared_613_ == 0)
{
lean_ctor_set_tag(v___x_612_, 3);
lean_ctor_set(v___x_612_, 0, v___x_617_);
v___x_619_ = v___x_612_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_625_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_616_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
lean_inc(v___y_615_);
v___x_621_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_621_, 0, v___y_615_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = 0;
v___x_623_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*1, v___x_622_);
v___x_624_ = l_Repr_addAppParen(v___x_623_, v_prec_511_);
return v___x_624_;
}
}
}
}
case 6:
{
lean_object* v_content_631_; lean_object* v_url_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v_inst_509_);
v_content_631_ = lean_ctor_get(v_x_510_, 0);
v_url_632_ = lean_ctor_get(v_x_510_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_656_ == 0)
{
v___x_634_ = v_x_510_;
v_isShared_635_ = v_isSharedCheck_656_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_url_632_);
lean_inc(v_content_631_);
lean_dec(v_x_510_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_656_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___y_637_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = lean_unsigned_to_nat(1024u);
v___x_653_ = lean_nat_dec_le(v___x_652_, v_prec_511_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
v___x_654_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_637_ = v___x_654_;
goto v___jp_636_;
}
else
{
lean_object* v___x_655_; 
v___x_655_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_637_ = v___x_655_;
goto v___jp_636_;
}
v___jp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_638_ = lean_box(1);
v___x_639_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__20));
v___x_640_ = l_Array_repr___redArg(v_localinst_512_, v_content_631_);
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 5);
lean_ctor_set(v___x_634_, 1, v___x_640_);
lean_ctor_set(v___x_634_, 0, v___x_639_);
v___x_642_ = v___x_634_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_651_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_638_);
v___x_644_ = l_String_quote(v_url_632_);
v___x_645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
v___x_646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_643_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_inc(v___y_637_);
v___x_647_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_647_, 0, v___y_637_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = 0;
v___x_649_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*1, v___x_648_);
v___x_650_ = l_Repr_addAppParen(v___x_649_, v_prec_511_);
return v___x_650_;
}
}
}
}
case 7:
{
lean_object* v_name_657_; lean_object* v_content_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_inst_509_);
v_name_657_ = lean_ctor_get(v_x_510_, 0);
v_content_658_ = lean_ctor_get(v_x_510_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_682_ == 0)
{
v___x_660_ = v_x_510_;
v_isShared_661_ = v_isSharedCheck_682_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_content_658_);
lean_inc(v_name_657_);
lean_dec(v_x_510_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_682_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___y_663_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_unsigned_to_nat(1024u);
v___x_679_ = lean_nat_dec_le(v___x_678_, v_prec_511_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
v___x_680_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_663_ = v___x_680_;
goto v___jp_662_;
}
else
{
lean_object* v___x_681_; 
v___x_681_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_663_ = v___x_681_;
goto v___jp_662_;
}
v___jp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_664_ = lean_box(1);
v___x_665_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__23));
v___x_666_ = l_String_quote(v_name_657_);
v___x_667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 5);
lean_ctor_set(v___x_660_, 1, v___x_667_);
lean_ctor_set(v___x_660_, 0, v___x_665_);
v___x_669_ = v___x_660_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_667_);
v___x_669_ = v_reuseFailAlloc_677_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_664_);
v___x_671_ = l_Array_repr___redArg(v_localinst_512_, v_content_658_);
v___x_672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
lean_inc(v___y_663_);
v___x_673_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_673_, 0, v___y_663_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = 0;
v___x_675_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*1, v___x_674_);
v___x_676_ = l_Repr_addAppParen(v___x_675_, v_prec_511_);
return v___x_676_;
}
}
}
}
case 8:
{
lean_object* v_alt_683_; lean_object* v_url_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v_localinst_512_);
lean_dec_ref(v_inst_509_);
v_alt_683_ = lean_ctor_get(v_x_510_, 0);
v_url_684_ = lean_ctor_get(v_x_510_, 1);
v_isSharedCheck_709_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_709_ == 0)
{
v___x_686_ = v_x_510_;
v_isShared_687_ = v_isSharedCheck_709_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_url_684_);
lean_inc(v_alt_683_);
lean_dec(v_x_510_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_709_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___y_689_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1024u);
v___x_706_ = lean_nat_dec_le(v___x_705_, v_prec_511_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_689_ = v___x_707_;
goto v___jp_688_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_689_ = v___x_708_;
goto v___jp_688_;
}
v___jp_688_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_690_ = lean_box(1);
v___x_691_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__26));
v___x_692_ = l_String_quote(v_alt_683_);
v___x_693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 5);
lean_ctor_set(v___x_686_, 1, v___x_693_);
lean_ctor_set(v___x_686_, 0, v___x_691_);
v___x_695_ = v___x_686_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_704_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_690_);
v___x_697_ = l_String_quote(v_url_684_);
v___x_698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_696_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
lean_inc(v___y_689_);
v___x_700_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_700_, 0, v___y_689_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = 0;
v___x_702_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*1, v___x_701_);
v___x_703_ = l_Repr_addAppParen(v___x_702_, v_prec_511_);
return v___x_703_;
}
}
}
}
case 9:
{
lean_object* v_content_710_; lean_object* v___y_712_; lean_object* v___x_720_; uint8_t v___x_721_; 
lean_dec_ref(v_inst_509_);
v_content_710_ = lean_ctor_get(v_x_510_, 0);
lean_inc_ref(v_content_710_);
lean_dec_ref_known(v_x_510_, 1);
v___x_720_ = lean_unsigned_to_nat(1024u);
v___x_721_ = lean_nat_dec_le(v___x_720_, v_prec_511_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_712_ = v___x_722_;
goto v___jp_711_;
}
else
{
lean_object* v___x_723_; 
v___x_723_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_712_ = v___x_723_;
goto v___jp_711_;
}
v___jp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_713_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__29));
v___x_714_ = l_Array_repr___redArg(v_localinst_512_, v_content_710_);
v___x_715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
lean_inc(v___y_712_);
v___x_716_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_716_, 0, v___y_712_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = 0;
v___x_718_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*1, v___x_717_);
v___x_719_ = l_Repr_addAppParen(v___x_718_, v_prec_511_);
return v___x_719_;
}
}
default: 
{
lean_object* v_container_724_; lean_object* v_content_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_749_; 
v_container_724_ = lean_ctor_get(v_x_510_, 0);
v_content_725_ = lean_ctor_get(v_x_510_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_749_ == 0)
{
v___x_727_ = v_x_510_;
v_isShared_728_ = v_isSharedCheck_749_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_content_725_);
lean_inc(v_container_724_);
lean_dec(v_x_510_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_749_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___y_730_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(1024u);
v___x_746_ = lean_nat_dec_le(v___x_745_, v_prec_511_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
v___x_747_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_730_ = v___x_747_;
goto v___jp_729_;
}
else
{
lean_object* v___x_748_; 
v___x_748_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_730_ = v___x_748_;
goto v___jp_729_;
}
v___jp_729_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_731_ = lean_box(1);
v___x_732_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__32));
v___x_733_ = lean_unsigned_to_nat(1024u);
v___x_734_ = lean_apply_2(v_inst_509_, v_container_724_, v___x_733_);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 5);
lean_ctor_set(v___x_727_, 1, v___x_734_);
lean_ctor_set(v___x_727_, 0, v___x_732_);
v___x_736_ = v___x_727_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_734_);
v___x_736_ = v_reuseFailAlloc_744_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_731_);
v___x_738_ = l_Array_repr___redArg(v_localinst_512_, v_content_725_);
v___x_739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
lean_inc(v___y_730_);
v___x_740_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_740_, 0, v___y_730_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = 0;
v___x_742_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set_uint8(v___x_742_, sizeof(void*)*1, v___x_741_);
v___x_743_ = l_Repr_addAppParen(v___x_742_, v_prec_511_);
return v___x_743_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr(lean_object* v_i_750_, lean_object* v_inst_751_, lean_object* v_x_752_, lean_object* v_prec_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_751_, v_x_752_, v_prec_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___boxed(lean_object* v_i_755_, lean_object* v_inst_756_, lean_object* v_x_757_, lean_object* v_prec_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Doc_instReprInline_repr(v_i_755_, v_inst_756_, v_x_757_, v_prec_758_);
lean_dec(v_prec_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline___redArg(lean_object* v_inst_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_761_, 0, lean_box(0));
lean_closure_set(v___x_761_, 1, v_inst_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline(lean_object* v_i_762_, lean_object* v_inst_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_764_, 0, lean_box(0));
lean_closure_set(v___x_764_, 1, v_inst_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg(){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = ((lean_object*)(l_Lean_Doc_instInhabitedInline_default___redArg___closed__1));
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg___boxed(lean_object* v___dummy_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Doc_instInhabitedInline_default___redArg();
return v_res_771_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedInline_default___closed__0(void){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Doc_instInhabitedInline_default___redArg();
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default(lean_object* v_i_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg(){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg___boxed(lean_object* v___dummy_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Doc_instInhabitedInline___redArg();
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline(lean_object* v_a_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg(lean_object* v_x_781_){
_start:
{
lean_inc_ref(v_x_781_);
return v_x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg___boxed(lean_object* v_x_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Doc_Inline_cast___redArg(v_x_782_);
lean_dec_ref(v_x_782_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast(lean_object* v_i_784_, lean_object* v_i_x27_785_, lean_object* v_inlines__eq_786_, lean_object* v_x_787_){
_start:
{
lean_inc_ref(v_x_787_);
return v_x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___boxed(lean_object* v_i_788_, lean_object* v_i_x27_789_, lean_object* v_inlines__eq_790_, lean_object* v_x_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Doc_Inline_cast(v_i_788_, v_i_x27_789_, v_inlines__eq_790_, v_x_791_);
lean_dec_ref(v_x_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___lam__0(lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
if (lean_obj_tag(v_x_793_) == 9)
{
lean_object* v_content_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v_content_795_ = lean_ctor_get(v_x_793_, 0);
v___x_796_ = lean_array_get_size(v_content_795_);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_nat_dec_eq(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
if (lean_obj_tag(v_x_794_) == 9)
{
lean_object* v_content_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_809_; 
v_content_799_ = lean_ctor_get(v_x_794_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_809_ == 0)
{
v___x_801_ = v_x_794_;
v_isShared_802_ = v_isSharedCheck_809_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_content_799_);
lean_dec(v_x_794_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_809_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_array_get_size(v_content_799_);
v___x_804_ = lean_nat_dec_eq(v___x_803_, v___x_797_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_807_; 
lean_inc_ref(v_content_795_);
lean_dec_ref_known(v_x_793_, 1);
v___x_805_ = l_Array_append___redArg(v_content_795_, v_content_799_);
lean_dec_ref(v_content_799_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_805_);
v___x_807_ = v___x_801_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
else
{
lean_del_object(v___x_801_);
lean_dec_ref(v_content_799_);
return v_x_793_;
}
}
}
else
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_817_; 
lean_inc_ref(v_content_795_);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_793_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_x_793_, 0);
lean_dec(v_unused_818_);
v___x_811_ = v_x_793_;
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
else
{
lean_dec(v_x_793_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_array_push(v_content_795_, v_x_794_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_dec_ref_known(v_x_793_, 1);
return v_x_794_;
}
}
else
{
if (lean_obj_tag(v_x_794_) == 9)
{
lean_object* v_content_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_833_; 
v_content_819_ = lean_ctor_get(v_x_794_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_833_ == 0)
{
v___x_821_ = v_x_794_;
v_isShared_822_ = v_isSharedCheck_833_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_content_819_);
lean_dec(v_x_794_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_833_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_823_ = lean_array_get_size(v_content_819_);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_nat_dec_eq(v___x_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_827_ = lean_mk_empty_array_with_capacity(v___x_826_);
v___x_828_ = lean_array_push(v___x_827_, v_x_793_);
v___x_829_ = l_Array_append___redArg(v___x_828_, v_content_819_);
lean_dec_ref(v_content_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_829_);
v___x_831_ = v___x_821_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
else
{
lean_del_object(v___x_821_);
lean_dec_ref(v_content_819_);
return v_x_793_;
}
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_834_ = lean_unsigned_to_nat(2u);
v___x_835_ = lean_mk_empty_array_with_capacity(v___x_834_);
v___x_836_ = lean_array_push(v___x_835_, v_x_793_);
v___x_837_ = lean_array_push(v___x_836_, v_x_794_);
v___x_838_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg(){
_start:
{
lean_object* v___f_841_; 
v___f_841_ = ((lean_object*)(l_Lean_Doc_instAppendInline___redArg___closed__0));
return v___f_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___boxed(lean_object* v___dummy_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Doc_instAppendInline___redArg();
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline(lean_object* v_i_844_){
_start:
{
lean_object* v___f_845_; 
v___f_845_ = ((lean_object*)(l_Lean_Doc_instAppendInline___redArg___closed__0));
return v___f_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg(){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = ((lean_object*)(l_Lean_Doc_Inline_empty___redArg___closed__1));
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg___boxed(lean_object* v___dummy_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Doc_Inline_empty___redArg();
return v_res_853_;
}
}
static lean_object* _init_l_Lean_Doc_Inline_empty___closed__0(void){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Doc_Inline_empty___redArg();
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty(lean_object* v_i_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lean_obj_once(&l_Lean_Doc_Inline_empty___closed__0, &l_Lean_Doc_Inline_empty___closed__0_once, _init_l_Lean_Doc_Inline_empty___closed__0);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(12u);
v___x_871_ = lean_nat_to_int(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__0));
v___x_874_ = lean_string_length(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9);
v___x_876_ = lean_nat_to_int(v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___redArg(lean_object* v_inst_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_883_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__6));
v___x_884_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_885_ = l_Array_repr___redArg(v_inst_881_, v_x_882_);
v___x_886_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = 0;
v___x_888_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set_uint8(v___x_888_, sizeof(void*)*1, v___x_887_);
v___x_889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_883_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_891_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v___x_889_);
v___x_893_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_890_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set_uint8(v___x_896_, sizeof(void*)*1, v___x_887_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr(lean_object* v_00_u03b1_897_, lean_object* v_inst_898_, lean_object* v_x_899_, lean_object* v_prec_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Doc_instReprListItem_repr___redArg(v_inst_898_, v_x_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___boxed(lean_object* v_00_u03b1_902_, lean_object* v_inst_903_, lean_object* v_x_904_, lean_object* v_prec_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Doc_instReprListItem_repr(v_00_u03b1_902_, v_inst_903_, v_x_904_, v_prec_905_);
lean_dec(v_prec_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem___redArg(lean_object* v_inst_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_908_, 0, lean_box(0));
lean_closure_set(v___x_908_, 1, v_inst_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem(lean_object* v_00_u03b1_909_, lean_object* v_inst_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_911_, 0, lean_box(0));
lean_closure_set(v___x_911_, 1, v_inst_910_);
return v___x_911_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq___redArg(lean_object* v_inst_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_array_get_size(v_x_913_);
v___x_916_ = lean_array_get_size(v_x_914_);
v___x_917_ = lean_nat_dec_eq(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_dec_ref(v_inst_912_);
return v___x_917_;
}
else
{
uint8_t v___x_918_; 
v___x_918_ = l_Array_isEqvAux___redArg(v_x_913_, v_x_914_, v_inst_912_, v___x_915_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___redArg___boxed(lean_object* v_inst_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_919_, v_x_920_, v_x_921_);
lean_dec_ref(v_x_921_);
lean_dec_ref(v_x_920_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq(lean_object* v_00_u03b1_924_, lean_object* v_inst_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
uint8_t v___x_928_; 
v___x_928_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_925_, v_x_926_, v_x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___boxed(lean_object* v_00_u03b1_929_, lean_object* v_inst_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Lean_Doc_instBEqListItem_beq(v_00_u03b1_929_, v_inst_930_, v_x_931_, v_x_932_);
lean_dec_ref(v_x_932_);
lean_dec_ref(v_x_931_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem___redArg(lean_object* v_inst_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_936_, 0, lean_box(0));
lean_closure_set(v___x_936_, 1, v_inst_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem(lean_object* v_00_u03b1_937_, lean_object* v_inst_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_939_, 0, lean_box(0));
lean_closure_set(v___x_939_, 1, v_inst_938_);
return v___x_939_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord___redArg(lean_object* v_inst_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_inst_940_, v_x_941_, v_x_942_, v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___redArg___boxed(lean_object* v_inst_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
uint8_t v_res_948_; lean_object* v_r_949_; 
v_res_948_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_945_, v_x_946_, v_x_947_);
lean_dec_ref(v_x_947_);
lean_dec_ref(v_x_946_);
v_r_949_ = lean_box(v_res_948_);
return v_r_949_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord(lean_object* v_00_u03b1_950_, lean_object* v_inst_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_951_, v_x_952_, v_x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___boxed(lean_object* v_00_u03b1_955_, lean_object* v_inst_956_, lean_object* v_x_957_, lean_object* v_x_958_){
_start:
{
uint8_t v_res_959_; lean_object* v_r_960_; 
v_res_959_ = l_Lean_Doc_instOrdListItem_ord(v_00_u03b1_955_, v_inst_956_, v_x_957_, v_x_958_);
lean_dec_ref(v_x_958_);
lean_dec_ref(v_x_957_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem___redArg(lean_object* v_inst_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_962_, 0, lean_box(0));
lean_closure_set(v___x_962_, 1, v_inst_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem(lean_object* v_00_u03b1_963_, lean_object* v_inst_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_965_, 0, lean_box(0));
lean_closure_set(v___x_965_, 1, v_inst_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg(){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l_Lean_Doc_instInhabitedListItem_default___redArg___closed__0));
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg___boxed(lean_object* v___dummy_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Doc_instInhabitedListItem_default___redArg();
return v_res_971_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedListItem_default___closed__0(void){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Doc_instInhabitedListItem_default___redArg();
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default(lean_object* v_00_u03b1_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem___redArg(){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem___redArg___boxed(lean_object* v___dummy_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Doc_instInhabitedListItem___redArg();
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem(lean_object* v_a_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(8u);
v___x_991_ = lean_nat_to_int(v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___redArg(lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v_term_1001_; lean_object* v_desc_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1034_; 
v_term_1001_ = lean_ctor_get(v_x_1000_, 0);
v_desc_1002_ = lean_ctor_get(v_x_1000_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1004_ = v_x_1000_;
v_isShared_1005_ = v_isSharedCheck_1034_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_desc_1002_);
lean_inc(v_term_1001_);
lean_dec(v_x_1000_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1034_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1006_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1007_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__3));
v___x_1008_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4);
v___x_1009_ = l_Array_repr___redArg(v_inst_998_, v_term_1001_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set_tag(v___x_1004_, 4);
lean_ctor_set(v___x_1004_, 1, v___x_1009_);
lean_ctor_set(v___x_1004_, 0, v___x_1008_);
v___x_1011_ = v___x_1004_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1012_ = 0;
v___x_1013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*1, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1007_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_box(1);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__8));
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_1006_);
v___x_1022_ = l_Array_repr___redArg(v_inst_999_, v_desc_1002_);
v___x_1023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1008_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*1, v___x_1012_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1021_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_1027_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_1025_);
v___x_1029_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1026_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*1, v___x_1012_);
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr(lean_object* v_00_u03b1_1035_, lean_object* v_00_u03b2_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_x_1039_, lean_object* v_prec_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Doc_instReprDescItem_repr___redArg(v_inst_1037_, v_inst_1038_, v_x_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_x_1046_, lean_object* v_prec_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Doc_instReprDescItem_repr(v_00_u03b1_1042_, v_00_u03b2_1043_, v_inst_1044_, v_inst_1045_, v_x_1046_, v_prec_1047_);
lean_dec(v_prec_1047_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem___redArg(lean_object* v_inst_1049_, lean_object* v_inst_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1051_, 0, lean_box(0));
lean_closure_set(v___x_1051_, 1, lean_box(0));
lean_closure_set(v___x_1051_, 2, v_inst_1049_);
lean_closure_set(v___x_1051_, 3, v_inst_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem(lean_object* v_00_u03b1_1052_, lean_object* v_00_u03b2_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1056_, 0, lean_box(0));
lean_closure_set(v___x_1056_, 1, lean_box(0));
lean_closure_set(v___x_1056_, 2, v_inst_1054_);
lean_closure_set(v___x_1056_, 3, v_inst_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq___redArg(lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v_term_1061_; lean_object* v_desc_1062_; lean_object* v_term_1063_; lean_object* v_desc_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_term_1061_ = lean_ctor_get(v_x_1059_, 0);
v_desc_1062_ = lean_ctor_get(v_x_1059_, 1);
v_term_1063_ = lean_ctor_get(v_x_1060_, 0);
v_desc_1064_ = lean_ctor_get(v_x_1060_, 1);
v___x_1065_ = lean_array_get_size(v_term_1061_);
v___x_1066_ = lean_array_get_size(v_term_1063_);
v___x_1067_ = lean_nat_dec_eq(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec_ref(v_inst_1058_);
lean_dec_ref(v_inst_1057_);
return v___x_1067_;
}
else
{
uint8_t v___x_1068_; 
v___x_1068_ = l_Array_isEqvAux___redArg(v_term_1061_, v_term_1063_, v_inst_1057_, v___x_1065_);
if (v___x_1068_ == 0)
{
lean_dec_ref(v_inst_1058_);
return v___x_1068_;
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = lean_array_get_size(v_desc_1062_);
v___x_1070_ = lean_array_get_size(v_desc_1064_);
v___x_1071_ = lean_nat_dec_eq(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v_inst_1058_);
return v___x_1071_;
}
else
{
uint8_t v___x_1072_; 
v___x_1072_ = l_Array_isEqvAux___redArg(v_desc_1062_, v_desc_1064_, v_inst_1058_, v___x_1069_);
return v___x_1072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___redArg___boxed(lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
uint8_t v_res_1077_; lean_object* v_r_1078_; 
v_res_1077_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1073_, v_inst_1074_, v_x_1075_, v_x_1076_);
lean_dec_ref(v_x_1076_);
lean_dec_ref(v_x_1075_);
v_r_1078_ = lean_box(v_res_1077_);
return v_r_1078_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq(lean_object* v_00_u03b1_1079_, lean_object* v_00_u03b2_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1081_, v_inst_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___boxed(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_res_1092_ = l_Lean_Doc_instBEqDescItem_beq(v_00_u03b1_1086_, v_00_u03b2_1087_, v_inst_1088_, v_inst_1089_, v_x_1090_, v_x_1091_);
lean_dec_ref(v_x_1091_);
lean_dec_ref(v_x_1090_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem___redArg(lean_object* v_inst_1094_, lean_object* v_inst_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1096_, 0, lean_box(0));
lean_closure_set(v___x_1096_, 1, lean_box(0));
lean_closure_set(v___x_1096_, 2, v_inst_1094_);
lean_closure_set(v___x_1096_, 3, v_inst_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem(lean_object* v_00_u03b1_1097_, lean_object* v_00_u03b2_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1101_, 0, lean_box(0));
lean_closure_set(v___x_1101_, 1, lean_box(0));
lean_closure_set(v___x_1101_, 2, v_inst_1099_);
lean_closure_set(v___x_1101_, 3, v_inst_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord___redArg(lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v_term_1106_; lean_object* v_desc_1107_; lean_object* v_term_1108_; lean_object* v_desc_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_term_1106_ = lean_ctor_get(v_x_1104_, 0);
v_desc_1107_ = lean_ctor_get(v_x_1104_, 1);
v_term_1108_ = lean_ctor_get(v_x_1105_, 0);
v_desc_1109_ = lean_ctor_get(v_x_1105_, 1);
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_inst_1102_, v_term_1106_, v_term_1108_, v___x_1110_);
if (v___x_1111_ == 1)
{
uint8_t v___x_1112_; 
v___x_1112_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_inst_1103_, v_desc_1107_, v_desc_1109_, v___x_1110_);
return v___x_1112_;
}
else
{
lean_dec_ref(v_inst_1103_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___redArg___boxed(lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_res_1117_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1113_, v_inst_1114_, v_x_1115_, v_x_1116_);
lean_dec_ref(v_x_1116_);
lean_dec_ref(v_x_1115_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord(lean_object* v_00_u03b1_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1121_, v_inst_1122_, v_x_1123_, v_x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___boxed(lean_object* v_00_u03b1_1126_, lean_object* v_00_u03b2_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
uint8_t v_res_1132_; lean_object* v_r_1133_; 
v_res_1132_ = l_Lean_Doc_instOrdDescItem_ord(v_00_u03b1_1126_, v_00_u03b2_1127_, v_inst_1128_, v_inst_1129_, v_x_1130_, v_x_1131_);
lean_dec_ref(v_x_1131_);
lean_dec_ref(v_x_1130_);
v_r_1133_ = lean_box(v_res_1132_);
return v_r_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem___redArg(lean_object* v_inst_1134_, lean_object* v_inst_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1136_, 0, lean_box(0));
lean_closure_set(v___x_1136_, 1, lean_box(0));
lean_closure_set(v___x_1136_, 2, v_inst_1134_);
lean_closure_set(v___x_1136_, 3, v_inst_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem(lean_object* v_00_u03b1_1137_, lean_object* v_00_u03b2_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1141_, 0, lean_box(0));
lean_closure_set(v___x_1141_, 1, lean_box(0));
lean_closure_set(v___x_1141_, 2, v_inst_1139_);
lean_closure_set(v___x_1141_, 3, v_inst_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg(){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = ((lean_object*)(l_Lean_Doc_instInhabitedDescItem_default___redArg___closed__0));
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg___boxed(lean_object* v___dummy_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
return v_res_1147_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0(void){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default(lean_object* v_00_u03b1_1149_, lean_object* v_00_u03b2_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg(){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg___boxed(lean_object* v___dummy_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Doc_instInhabitedDescItem___redArg();
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem(lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl___redArg(lean_object* v_x_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_obj_tag_nat(v_x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl___redArg___boxed(lean_object* v_x_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Doc_Block_ctorIdx___impl___redArg(v_x_1161_);
lean_dec_ref(v_x_1161_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl(lean_object* v_i_1163_, lean_object* v_b_1164_, lean_object* v_x_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_obj_tag_nat(v_x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___impl___boxed(lean_object* v_i_1167_, lean_object* v_b_1168_, lean_object* v_x_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Doc_Block_ctorIdx___impl(v_i_1167_, v_b_1168_, v_x_1169_);
lean_dec_ref(v_x_1169_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___redArg(lean_object* v_t_1171_, lean_object* v_k_1172_){
_start:
{
switch(lean_obj_tag(v_t_1171_))
{
case 3:
{
lean_object* v_start_1173_; lean_object* v_items_1174_; lean_object* v___x_1175_; 
v_start_1173_ = lean_ctor_get(v_t_1171_, 0);
lean_inc(v_start_1173_);
v_items_1174_ = lean_ctor_get(v_t_1171_, 1);
lean_inc_ref(v_items_1174_);
lean_dec_ref_known(v_t_1171_, 2);
v___x_1175_ = lean_apply_2(v_k_1172_, v_start_1173_, v_items_1174_);
return v___x_1175_;
}
case 7:
{
lean_object* v_container_1176_; lean_object* v_content_1177_; lean_object* v___x_1178_; 
v_container_1176_ = lean_ctor_get(v_t_1171_, 0);
lean_inc(v_container_1176_);
v_content_1177_ = lean_ctor_get(v_t_1171_, 1);
lean_inc_ref(v_content_1177_);
lean_dec_ref_known(v_t_1171_, 2);
v___x_1178_ = lean_apply_2(v_k_1172_, v_container_1176_, v_content_1177_);
return v___x_1178_;
}
default: 
{
lean_object* v_contents_1179_; lean_object* v___x_1180_; 
v_contents_1179_ = lean_ctor_get(v_t_1171_, 0);
lean_inc_ref(v_contents_1179_);
lean_dec_ref(v_t_1171_);
v___x_1180_ = lean_apply_1(v_k_1172_, v_contents_1179_);
return v___x_1180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim(lean_object* v_i_1181_, lean_object* v_b_1182_, lean_object* v_motive__1_1183_, lean_object* v_ctorIdx_1184_, lean_object* v_t_1185_, lean_object* v_h_1186_, lean_object* v_k_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1185_, v_k_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___boxed(lean_object* v_i_1189_, lean_object* v_b_1190_, lean_object* v_motive__1_1191_, lean_object* v_ctorIdx_1192_, lean_object* v_t_1193_, lean_object* v_h_1194_, lean_object* v_k_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Doc_Block_ctorElim(v_i_1189_, v_b_1190_, v_motive__1_1191_, v_ctorIdx_1192_, v_t_1193_, v_h_1194_, v_k_1195_);
lean_dec(v_ctorIdx_1192_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim___redArg(lean_object* v_t_1197_, lean_object* v_para_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1197_, v_para_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim(lean_object* v_i_1200_, lean_object* v_b_1201_, lean_object* v_motive__1_1202_, lean_object* v_t_1203_, lean_object* v_h_1204_, lean_object* v_para_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1203_, v_para_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim___redArg(lean_object* v_t_1207_, lean_object* v_code_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1207_, v_code_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim(lean_object* v_i_1210_, lean_object* v_b_1211_, lean_object* v_motive__1_1212_, lean_object* v_t_1213_, lean_object* v_h_1214_, lean_object* v_code_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1213_, v_code_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim___redArg(lean_object* v_t_1217_, lean_object* v_ul_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1217_, v_ul_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim(lean_object* v_i_1220_, lean_object* v_b_1221_, lean_object* v_motive__1_1222_, lean_object* v_t_1223_, lean_object* v_h_1224_, lean_object* v_ul_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1223_, v_ul_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim___redArg(lean_object* v_t_1227_, lean_object* v_ol_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1227_, v_ol_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim(lean_object* v_i_1230_, lean_object* v_b_1231_, lean_object* v_motive__1_1232_, lean_object* v_t_1233_, lean_object* v_h_1234_, lean_object* v_ol_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1233_, v_ol_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim___redArg(lean_object* v_t_1237_, lean_object* v_dl_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1237_, v_dl_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim(lean_object* v_i_1240_, lean_object* v_b_1241_, lean_object* v_motive__1_1242_, lean_object* v_t_1243_, lean_object* v_h_1244_, lean_object* v_dl_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1243_, v_dl_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim___redArg(lean_object* v_t_1247_, lean_object* v_blockquote_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1247_, v_blockquote_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim(lean_object* v_i_1250_, lean_object* v_b_1251_, lean_object* v_motive__1_1252_, lean_object* v_t_1253_, lean_object* v_h_1254_, lean_object* v_blockquote_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1253_, v_blockquote_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim___redArg(lean_object* v_t_1257_, lean_object* v_concat_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1257_, v_concat_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim(lean_object* v_i_1260_, lean_object* v_b_1261_, lean_object* v_motive__1_1262_, lean_object* v_t_1263_, lean_object* v_h_1264_, lean_object* v_concat_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1263_, v_concat_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim___redArg(lean_object* v_t_1267_, lean_object* v_other_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1267_, v_other_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim(lean_object* v_i_1270_, lean_object* v_b_1271_, lean_object* v_motive__1_1272_, lean_object* v_t_1273_, lean_object* v_h_1274_, lean_object* v_other_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1273_, v_other_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___redArg___boxed(lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
uint8_t v_res_1281_; lean_object* v_r_1282_; 
v_res_1281_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1277_, v_inst_1278_, v_x_1279_, v_x_1280_);
v_r_1282_ = lean_box(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq___redArg(lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
lean_object* v_localinst_1287_; lean_object* v_a_1289_; lean_object* v_b_1290_; 
lean_inc_ref(v_inst_1284_);
lean_inc_ref(v_inst_1283_);
v_localinst_1287_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1287_, 0, v_inst_1283_);
lean_closure_set(v_localinst_1287_, 1, v_inst_1284_);
switch(lean_obj_tag(v_x_1285_))
{
case 0:
{
lean_dec_ref(v_localinst_1287_);
lean_dec_ref(v_inst_1284_);
if (lean_obj_tag(v_x_1286_) == 0)
{
lean_object* v_contents_1295_; lean_object* v_contents_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_contents_1295_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_contents_1295_);
lean_dec_ref_known(v_x_1285_, 1);
v_contents_1296_ = lean_ctor_get(v_x_1286_, 0);
lean_inc_ref(v_contents_1296_);
lean_dec_ref_known(v_x_1286_, 1);
v___x_1297_ = lean_array_get_size(v_contents_1295_);
v___x_1298_ = lean_array_get_size(v_contents_1296_);
v___x_1299_ = lean_nat_dec_eq(v___x_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_dec_ref(v_contents_1296_);
lean_dec_ref(v_contents_1295_);
lean_dec_ref(v_inst_1283_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1300_, 0, lean_box(0));
lean_closure_set(v___x_1300_, 1, v_inst_1283_);
v___x_1301_ = l_Array_isEqvAux___redArg(v_contents_1295_, v_contents_1296_, v___x_1300_, v___x_1297_);
lean_dec_ref(v_contents_1296_);
lean_dec_ref(v_contents_1295_);
return v___x_1301_;
}
}
else
{
uint8_t v___x_1302_; 
lean_dec_ref_known(v_x_1285_, 1);
lean_dec_ref(v_x_1286_);
lean_dec_ref(v_inst_1283_);
v___x_1302_ = 0;
return v___x_1302_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1287_);
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
if (lean_obj_tag(v_x_1286_) == 1)
{
lean_object* v_content_1303_; lean_object* v_content_1304_; uint8_t v___x_1305_; 
v_content_1303_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_content_1303_);
lean_dec_ref_known(v_x_1285_, 1);
v_content_1304_ = lean_ctor_get(v_x_1286_, 0);
lean_inc_ref(v_content_1304_);
lean_dec_ref_known(v_x_1286_, 1);
v___x_1305_ = lean_string_dec_eq(v_content_1303_, v_content_1304_);
lean_dec_ref(v_content_1304_);
lean_dec_ref(v_content_1303_);
return v___x_1305_;
}
else
{
uint8_t v___x_1306_; 
lean_dec_ref_known(v_x_1285_, 1);
lean_dec_ref(v_x_1286_);
v___x_1306_ = 0;
return v___x_1306_;
}
}
case 2:
{
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
if (lean_obj_tag(v_x_1286_) == 2)
{
lean_object* v_items_1307_; lean_object* v_items_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_items_1307_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_items_1307_);
lean_dec_ref_known(v_x_1285_, 1);
v_items_1308_ = lean_ctor_get(v_x_1286_, 0);
lean_inc_ref(v_items_1308_);
lean_dec_ref_known(v_x_1286_, 1);
v___x_1309_ = lean_array_get_size(v_items_1307_);
v___x_1310_ = lean_array_get_size(v_items_1308_);
v___x_1311_ = lean_nat_dec_eq(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_dec_ref(v_items_1308_);
lean_dec_ref(v_items_1307_);
lean_dec_ref(v_localinst_1287_);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1312_, 0, lean_box(0));
lean_closure_set(v___x_1312_, 1, v_localinst_1287_);
v___x_1313_ = l_Array_isEqvAux___redArg(v_items_1307_, v_items_1308_, v___x_1312_, v___x_1309_);
lean_dec_ref(v_items_1308_);
lean_dec_ref(v_items_1307_);
return v___x_1313_;
}
}
else
{
uint8_t v___x_1314_; 
lean_dec_ref_known(v_x_1285_, 1);
lean_dec_ref(v_localinst_1287_);
lean_dec_ref(v_x_1286_);
v___x_1314_ = 0;
return v___x_1314_;
}
}
case 3:
{
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
if (lean_obj_tag(v_x_1286_) == 3)
{
lean_object* v_start_1315_; lean_object* v_items_1316_; lean_object* v_start_1317_; lean_object* v_items_1318_; uint8_t v___x_1319_; 
v_start_1315_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_start_1315_);
v_items_1316_ = lean_ctor_get(v_x_1285_, 1);
lean_inc_ref(v_items_1316_);
lean_dec_ref_known(v_x_1285_, 2);
v_start_1317_ = lean_ctor_get(v_x_1286_, 0);
lean_inc(v_start_1317_);
v_items_1318_ = lean_ctor_get(v_x_1286_, 1);
lean_inc_ref(v_items_1318_);
lean_dec_ref_known(v_x_1286_, 2);
v___x_1319_ = lean_int_dec_eq(v_start_1315_, v_start_1317_);
lean_dec(v_start_1317_);
lean_dec(v_start_1315_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v_items_1318_);
lean_dec_ref(v_items_1316_);
lean_dec_ref(v_localinst_1287_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1320_ = lean_array_get_size(v_items_1316_);
v___x_1321_ = lean_array_get_size(v_items_1318_);
v___x_1322_ = lean_nat_dec_eq(v___x_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v_items_1318_);
lean_dec_ref(v_items_1316_);
lean_dec_ref(v_localinst_1287_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1323_, 0, lean_box(0));
lean_closure_set(v___x_1323_, 1, v_localinst_1287_);
v___x_1324_ = l_Array_isEqvAux___redArg(v_items_1316_, v_items_1318_, v___x_1323_, v___x_1320_);
lean_dec_ref(v_items_1318_);
lean_dec_ref(v_items_1316_);
return v___x_1324_;
}
}
}
else
{
uint8_t v___x_1325_; 
lean_dec_ref_known(v_x_1285_, 2);
lean_dec_ref(v_localinst_1287_);
lean_dec_ref(v_x_1286_);
v___x_1325_ = 0;
return v___x_1325_;
}
}
case 4:
{
lean_dec_ref(v_inst_1284_);
if (lean_obj_tag(v_x_1286_) == 4)
{
lean_object* v_items_1326_; lean_object* v_items_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_items_1326_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_items_1326_);
lean_dec_ref_known(v_x_1285_, 1);
v_items_1327_ = lean_ctor_get(v_x_1286_, 0);
lean_inc_ref(v_items_1327_);
lean_dec_ref_known(v_x_1286_, 1);
v___x_1328_ = lean_array_get_size(v_items_1326_);
v___x_1329_ = lean_array_get_size(v_items_1327_);
v___x_1330_ = lean_nat_dec_eq(v___x_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_dec_ref(v_items_1327_);
lean_dec_ref(v_items_1326_);
lean_dec_ref(v_localinst_1287_);
lean_dec_ref(v_inst_1283_);
return v___x_1330_;
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1331_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1331_, 0, lean_box(0));
lean_closure_set(v___x_1331_, 1, v_inst_1283_);
v___x_1332_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1332_, 0, lean_box(0));
lean_closure_set(v___x_1332_, 1, lean_box(0));
lean_closure_set(v___x_1332_, 2, v___x_1331_);
lean_closure_set(v___x_1332_, 3, v_localinst_1287_);
v___x_1333_ = l_Array_isEqvAux___redArg(v_items_1326_, v_items_1327_, v___x_1332_, v___x_1328_);
lean_dec_ref(v_items_1327_);
lean_dec_ref(v_items_1326_);
return v___x_1333_;
}
}
else
{
uint8_t v___x_1334_; 
lean_dec_ref_known(v_x_1285_, 1);
lean_dec_ref(v_localinst_1287_);
lean_dec_ref(v_x_1286_);
lean_dec_ref(v_inst_1283_);
v___x_1334_ = 0;
return v___x_1334_;
}
}
case 5:
{
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
if (lean_obj_tag(v_x_1286_) == 5)
{
lean_object* v_items_1335_; lean_object* v_items_1336_; 
v_items_1335_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_items_1335_);
lean_dec_ref_known(v_x_1285_, 1);
v_items_1336_ = lean_ctor_get(v_x_1286_, 0);
lean_inc_ref(v_items_1336_);
lean_dec_ref_known(v_x_1286_, 1);
v_a_1289_ = v_items_1335_;
v_b_1290_ = v_items_1336_;
goto v___jp_1288_;
}
else
{
uint8_t v___x_1337_; 
lean_dec_ref_known(v_x_1285_, 1);
lean_dec_ref(v_localinst_1287_);
lean_dec_ref(v_x_1286_);
v___x_1337_ = 0;
return v___x_1337_;
}
}
case 6:
{
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
if (lean_obj_tag(v_x_1286_) == 6)
{
lean_object* v_content_1338_; lean_object* v_content_1339_; 
v_content_1338_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_content_1338_);
lean_dec_ref_known(v_x_1285_, 1);
v_content_1339_ = lean_ctor_get(v_x_1286_, 0);
lean_inc_ref(v_content_1339_);
lean_dec_ref_known(v_x_1286_, 1);
v_a_1289_ = v_content_1338_;
v_b_1290_ = v_content_1339_;
goto v___jp_1288_;
}
else
{
uint8_t v___x_1340_; 
lean_dec_ref_known(v_x_1285_, 1);
lean_dec_ref(v_localinst_1287_);
lean_dec_ref(v_x_1286_);
v___x_1340_ = 0;
return v___x_1340_;
}
}
default: 
{
lean_dec_ref(v_inst_1283_);
if (lean_obj_tag(v_x_1286_) == 7)
{
lean_object* v_container_1341_; lean_object* v_content_1342_; lean_object* v_container_1343_; lean_object* v_content_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_container_1341_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_container_1341_);
v_content_1342_ = lean_ctor_get(v_x_1285_, 1);
lean_inc_ref(v_content_1342_);
lean_dec_ref_known(v_x_1285_, 2);
v_container_1343_ = lean_ctor_get(v_x_1286_, 0);
lean_inc(v_container_1343_);
v_content_1344_ = lean_ctor_get(v_x_1286_, 1);
lean_inc_ref(v_content_1344_);
lean_dec_ref_known(v_x_1286_, 2);
v___x_1345_ = lean_apply_2(v_inst_1284_, v_container_1341_, v_container_1343_);
v___x_1346_ = lean_unbox(v___x_1345_);
if (v___x_1346_ == 0)
{
uint8_t v___x_1347_; 
lean_dec_ref(v_content_1344_);
lean_dec_ref(v_content_1342_);
lean_dec_ref(v_localinst_1287_);
v___x_1347_ = lean_unbox(v___x_1345_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = lean_array_get_size(v_content_1342_);
v___x_1349_ = lean_array_get_size(v_content_1344_);
v___x_1350_ = lean_nat_dec_eq(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_dec_ref(v_content_1344_);
lean_dec_ref(v_content_1342_);
lean_dec_ref(v_localinst_1287_);
return v___x_1350_;
}
else
{
uint8_t v___x_1351_; 
v___x_1351_ = l_Array_isEqvAux___redArg(v_content_1342_, v_content_1344_, v_localinst_1287_, v___x_1348_);
lean_dec_ref(v_content_1344_);
lean_dec_ref(v_content_1342_);
return v___x_1351_;
}
}
}
else
{
uint8_t v___x_1352_; 
lean_dec_ref_known(v_x_1285_, 2);
lean_dec_ref(v_localinst_1287_);
lean_dec_ref(v_x_1286_);
lean_dec_ref(v_inst_1284_);
v___x_1352_ = 0;
return v___x_1352_;
}
}
}
v___jp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1291_ = lean_array_get_size(v_a_1289_);
v___x_1292_ = lean_array_get_size(v_b_1290_);
v___x_1293_ = lean_nat_dec_eq(v___x_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v_b_1290_);
lean_dec_ref(v_a_1289_);
lean_dec_ref(v_localinst_1287_);
return v___x_1293_;
}
else
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Array_isEqvAux___redArg(v_a_1289_, v_b_1290_, v_localinst_1287_, v___x_1291_);
lean_dec_ref(v_b_1290_);
lean_dec_ref(v_a_1289_);
return v___x_1294_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq(lean_object* v_i_1353_, lean_object* v_b_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1355_, v_inst_1356_, v_x_1357_, v_x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___boxed(lean_object* v_i_1360_, lean_object* v_b_1361_, lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
uint8_t v_res_1366_; lean_object* v_r_1367_; 
v_res_1366_ = l_Lean_Doc_instBEqBlock_beq(v_i_1360_, v_b_1361_, v_inst_1362_, v_inst_1363_, v_x_1364_, v_x_1365_);
v_r_1367_ = lean_box(v_res_1366_);
return v_r_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock___redArg(lean_object* v_inst_1368_, lean_object* v_inst_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1370_, 0, lean_box(0));
lean_closure_set(v___x_1370_, 1, lean_box(0));
lean_closure_set(v___x_1370_, 2, v_inst_1368_);
lean_closure_set(v___x_1370_, 3, v_inst_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock(lean_object* v_i_1371_, lean_object* v_b_1372_, lean_object* v_inst_1373_, lean_object* v_inst_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1375_, 0, lean_box(0));
lean_closure_set(v___x_1375_, 1, lean_box(0));
lean_closure_set(v___x_1375_, 2, v_inst_1373_);
lean_closure_set(v___x_1375_, 3, v_inst_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___redArg___boxed(lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_){
_start:
{
uint8_t v_res_1380_; lean_object* v_r_1381_; 
v_res_1380_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1376_, v_inst_1377_, v_x_1378_, v_x_1379_);
v_r_1381_ = lean_box(v_res_1380_);
return v_r_1381_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord___redArg(lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
lean_object* v_localinst_1386_; lean_object* v_a_1388_; lean_object* v_b_1389_; 
lean_inc_ref(v_inst_1383_);
lean_inc_ref(v_inst_1382_);
v_localinst_1386_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1386_, 0, v_inst_1382_);
lean_closure_set(v_localinst_1386_, 1, v_inst_1383_);
switch(lean_obj_tag(v_x_1384_))
{
case 0:
{
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_inst_1383_);
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_object* v_contents_1392_; lean_object* v_contents_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_contents_1392_ = lean_ctor_get(v_x_1384_, 0);
lean_inc_ref(v_contents_1392_);
lean_dec_ref_known(v_x_1384_, 1);
v_contents_1393_ = lean_ctor_get(v_x_1385_, 0);
lean_inc_ref(v_contents_1393_);
lean_dec_ref_known(v_x_1385_, 1);
v___x_1394_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1394_, 0, lean_box(0));
lean_closure_set(v___x_1394_, 1, v_inst_1382_);
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1394_, v_contents_1392_, v_contents_1393_, v___x_1395_);
lean_dec_ref(v_contents_1393_);
lean_dec_ref(v_contents_1392_);
return v___x_1396_;
}
else
{
uint8_t v___x_1397_; 
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_x_1385_);
lean_dec_ref(v_inst_1382_);
v___x_1397_ = 0;
return v___x_1397_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_inst_1383_);
lean_dec_ref(v_inst_1382_);
switch(lean_obj_tag(v_x_1385_))
{
case 0:
{
uint8_t v___x_1398_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1398_ = 2;
return v___x_1398_;
}
case 1:
{
lean_object* v_content_1399_; lean_object* v_content_1400_; uint8_t v___x_1401_; 
v_content_1399_ = lean_ctor_get(v_x_1384_, 0);
lean_inc_ref(v_content_1399_);
lean_dec_ref_known(v_x_1384_, 1);
v_content_1400_ = lean_ctor_get(v_x_1385_, 0);
lean_inc_ref(v_content_1400_);
lean_dec_ref_known(v_x_1385_, 1);
v___x_1401_ = lean_string_compare(v_content_1399_, v_content_1400_);
lean_dec_ref(v_content_1400_);
lean_dec_ref(v_content_1399_);
return v___x_1401_;
}
default: 
{
uint8_t v___x_1402_; 
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_x_1385_);
v___x_1402_ = 0;
return v___x_1402_;
}
}
}
case 2:
{
lean_dec_ref(v_inst_1383_);
lean_dec_ref(v_inst_1382_);
switch(lean_obj_tag(v_x_1385_))
{
case 0:
{
uint8_t v___x_1403_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1403_ = 2;
return v___x_1403_;
}
case 1:
{
uint8_t v___x_1404_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1404_ = 2;
return v___x_1404_;
}
case 2:
{
lean_object* v_items_1405_; lean_object* v_items_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v_items_1405_ = lean_ctor_get(v_x_1384_, 0);
lean_inc_ref(v_items_1405_);
lean_dec_ref_known(v_x_1384_, 1);
v_items_1406_ = lean_ctor_get(v_x_1385_, 0);
lean_inc_ref(v_items_1406_);
lean_dec_ref_known(v_x_1385_, 1);
v___x_1407_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1407_, 0, lean_box(0));
lean_closure_set(v___x_1407_, 1, v_localinst_1386_);
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1407_, v_items_1405_, v_items_1406_, v___x_1408_);
lean_dec_ref(v_items_1406_);
lean_dec_ref(v_items_1405_);
return v___x_1409_;
}
default: 
{
uint8_t v___x_1410_; 
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_x_1385_);
v___x_1410_ = 0;
return v___x_1410_;
}
}
}
case 3:
{
lean_dec_ref(v_inst_1383_);
lean_dec_ref(v_inst_1382_);
switch(lean_obj_tag(v_x_1385_))
{
case 0:
{
uint8_t v___x_1411_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 2);
lean_dec_ref(v_localinst_1386_);
v___x_1411_ = 2;
return v___x_1411_;
}
case 1:
{
uint8_t v___x_1412_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 2);
lean_dec_ref(v_localinst_1386_);
v___x_1412_ = 2;
return v___x_1412_;
}
case 2:
{
uint8_t v___x_1413_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 2);
lean_dec_ref(v_localinst_1386_);
v___x_1413_ = 2;
return v___x_1413_;
}
case 3:
{
lean_object* v_start_1414_; lean_object* v_items_1415_; lean_object* v_start_1416_; lean_object* v_items_1417_; uint8_t v___x_1418_; 
v_start_1414_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_start_1414_);
v_items_1415_ = lean_ctor_get(v_x_1384_, 1);
lean_inc_ref(v_items_1415_);
lean_dec_ref_known(v_x_1384_, 2);
v_start_1416_ = lean_ctor_get(v_x_1385_, 0);
lean_inc(v_start_1416_);
v_items_1417_ = lean_ctor_get(v_x_1385_, 1);
lean_inc_ref(v_items_1417_);
lean_dec_ref_known(v_x_1385_, 2);
v___x_1418_ = lean_int_dec_lt(v_start_1414_, v_start_1416_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_int_dec_eq(v_start_1414_, v_start_1416_);
lean_dec(v_start_1416_);
lean_dec(v_start_1414_);
if (v___x_1419_ == 0)
{
uint8_t v___x_1420_; 
lean_dec_ref(v_items_1417_);
lean_dec_ref(v_items_1415_);
lean_dec_ref(v_localinst_1386_);
v___x_1420_ = 2;
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1421_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1421_, 0, lean_box(0));
lean_closure_set(v___x_1421_, 1, v_localinst_1386_);
v___x_1422_ = lean_unsigned_to_nat(0u);
v___x_1423_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1421_, v_items_1415_, v_items_1417_, v___x_1422_);
lean_dec_ref(v_items_1417_);
lean_dec_ref(v_items_1415_);
return v___x_1423_;
}
}
else
{
uint8_t v___x_1424_; 
lean_dec_ref(v_items_1417_);
lean_dec(v_start_1416_);
lean_dec_ref(v_items_1415_);
lean_dec(v_start_1414_);
lean_dec_ref(v_localinst_1386_);
v___x_1424_ = 0;
return v___x_1424_;
}
}
default: 
{
uint8_t v___x_1425_; 
lean_dec_ref_known(v_x_1384_, 2);
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_x_1385_);
v___x_1425_ = 0;
return v___x_1425_;
}
}
}
case 4:
{
lean_dec_ref(v_inst_1383_);
switch(lean_obj_tag(v_x_1385_))
{
case 0:
{
uint8_t v___x_1426_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_inst_1382_);
v___x_1426_ = 2;
return v___x_1426_;
}
case 1:
{
uint8_t v___x_1427_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_inst_1382_);
v___x_1427_ = 2;
return v___x_1427_;
}
case 2:
{
uint8_t v___x_1428_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_inst_1382_);
v___x_1428_ = 2;
return v___x_1428_;
}
case 3:
{
uint8_t v___x_1429_; 
lean_dec_ref_known(v_x_1385_, 2);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_inst_1382_);
v___x_1429_ = 2;
return v___x_1429_;
}
case 4:
{
lean_object* v_items_1430_; lean_object* v_items_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_items_1430_ = lean_ctor_get(v_x_1384_, 0);
lean_inc_ref(v_items_1430_);
lean_dec_ref_known(v_x_1384_, 1);
v_items_1431_ = lean_ctor_get(v_x_1385_, 0);
lean_inc_ref(v_items_1431_);
lean_dec_ref_known(v_x_1385_, 1);
v___x_1432_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1432_, 0, lean_box(0));
lean_closure_set(v___x_1432_, 1, v_inst_1382_);
v___x_1433_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1433_, 0, lean_box(0));
lean_closure_set(v___x_1433_, 1, lean_box(0));
lean_closure_set(v___x_1433_, 2, v___x_1432_);
lean_closure_set(v___x_1433_, 3, v_localinst_1386_);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1433_, v_items_1430_, v_items_1431_, v___x_1434_);
lean_dec_ref(v_items_1431_);
lean_dec_ref(v_items_1430_);
return v___x_1435_;
}
default: 
{
uint8_t v___x_1436_; 
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_x_1385_);
lean_dec_ref(v_inst_1382_);
v___x_1436_ = 0;
return v___x_1436_;
}
}
}
case 5:
{
lean_dec_ref(v_inst_1383_);
lean_dec_ref(v_inst_1382_);
switch(lean_obj_tag(v_x_1385_))
{
case 0:
{
uint8_t v___x_1437_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1437_ = 2;
return v___x_1437_;
}
case 1:
{
uint8_t v___x_1438_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1438_ = 2;
return v___x_1438_;
}
case 2:
{
uint8_t v___x_1439_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1439_ = 2;
return v___x_1439_;
}
case 3:
{
uint8_t v___x_1440_; 
lean_dec_ref_known(v_x_1385_, 2);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1440_ = 2;
return v___x_1440_;
}
case 4:
{
uint8_t v___x_1441_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1441_ = 2;
return v___x_1441_;
}
case 5:
{
lean_object* v_items_1442_; lean_object* v_items_1443_; 
v_items_1442_ = lean_ctor_get(v_x_1384_, 0);
lean_inc_ref(v_items_1442_);
lean_dec_ref_known(v_x_1384_, 1);
v_items_1443_ = lean_ctor_get(v_x_1385_, 0);
lean_inc_ref(v_items_1443_);
lean_dec_ref_known(v_x_1385_, 1);
v_a_1388_ = v_items_1442_;
v_b_1389_ = v_items_1443_;
goto v___jp_1387_;
}
default: 
{
uint8_t v___x_1444_; 
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_x_1385_);
v___x_1444_ = 0;
return v___x_1444_;
}
}
}
case 6:
{
lean_dec_ref(v_inst_1383_);
lean_dec_ref(v_inst_1382_);
switch(lean_obj_tag(v_x_1385_))
{
case 0:
{
uint8_t v___x_1445_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1445_ = 2;
return v___x_1445_;
}
case 1:
{
uint8_t v___x_1446_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1446_ = 2;
return v___x_1446_;
}
case 2:
{
uint8_t v___x_1447_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1447_ = 2;
return v___x_1447_;
}
case 3:
{
uint8_t v___x_1448_; 
lean_dec_ref_known(v_x_1385_, 2);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1448_ = 2;
return v___x_1448_;
}
case 4:
{
uint8_t v___x_1449_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1449_ = 2;
return v___x_1449_;
}
case 5:
{
uint8_t v___x_1450_; 
lean_dec_ref_known(v_x_1385_, 1);
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
v___x_1450_ = 2;
return v___x_1450_;
}
case 6:
{
lean_object* v_content_1451_; lean_object* v_content_1452_; 
v_content_1451_ = lean_ctor_get(v_x_1384_, 0);
lean_inc_ref(v_content_1451_);
lean_dec_ref_known(v_x_1384_, 1);
v_content_1452_ = lean_ctor_get(v_x_1385_, 0);
lean_inc_ref(v_content_1452_);
lean_dec_ref_known(v_x_1385_, 1);
v_a_1388_ = v_content_1451_;
v_b_1389_ = v_content_1452_;
goto v___jp_1387_;
}
default: 
{
uint8_t v___x_1453_; 
lean_dec_ref_known(v_x_1384_, 1);
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_x_1385_);
v___x_1453_ = 0;
return v___x_1453_;
}
}
}
default: 
{
lean_dec_ref(v_inst_1382_);
if (lean_obj_tag(v_x_1385_) == 7)
{
lean_object* v_container_1454_; lean_object* v_content_1455_; lean_object* v_container_1456_; lean_object* v_content_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_container_1454_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_container_1454_);
v_content_1455_ = lean_ctor_get(v_x_1384_, 1);
lean_inc_ref(v_content_1455_);
lean_dec_ref_known(v_x_1384_, 2);
v_container_1456_ = lean_ctor_get(v_x_1385_, 0);
lean_inc(v_container_1456_);
v_content_1457_ = lean_ctor_get(v_x_1385_, 1);
lean_inc_ref(v_content_1457_);
lean_dec_ref_known(v_x_1385_, 2);
v___x_1458_ = lean_apply_2(v_inst_1383_, v_container_1454_, v_container_1456_);
v___x_1459_ = lean_unbox(v___x_1458_);
if (v___x_1459_ == 1)
{
lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_localinst_1386_, v_content_1455_, v_content_1457_, v___x_1460_);
lean_dec_ref(v_content_1457_);
lean_dec_ref(v_content_1455_);
return v___x_1461_;
}
else
{
uint8_t v___x_1462_; 
lean_dec_ref(v_content_1457_);
lean_dec_ref(v_content_1455_);
lean_dec_ref(v_localinst_1386_);
v___x_1462_ = lean_unbox(v___x_1458_);
return v___x_1462_;
}
}
else
{
uint8_t v___x_1463_; 
lean_dec_ref_known(v_x_1384_, 2);
lean_dec_ref(v_localinst_1386_);
lean_dec_ref(v_x_1385_);
lean_dec_ref(v_inst_1383_);
v___x_1463_ = 2;
return v___x_1463_;
}
}
}
v___jp_1387_:
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_localinst_1386_, v_a_1388_, v_b_1389_, v___x_1390_);
lean_dec_ref(v_b_1389_);
lean_dec_ref(v_a_1388_);
return v___x_1391_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord(lean_object* v_i_1464_, lean_object* v_b_1465_, lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_){
_start:
{
uint8_t v___x_1470_; 
v___x_1470_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1466_, v_inst_1467_, v_x_1468_, v_x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___boxed(lean_object* v_i_1471_, lean_object* v_b_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_){
_start:
{
uint8_t v_res_1477_; lean_object* v_r_1478_; 
v_res_1477_ = l_Lean_Doc_instOrdBlock_ord(v_i_1471_, v_b_1472_, v_inst_1473_, v_inst_1474_, v_x_1475_, v_x_1476_);
v_r_1478_ = lean_box(v_res_1477_);
return v_r_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock___redArg(lean_object* v_inst_1479_, lean_object* v_inst_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1481_, 0, lean_box(0));
lean_closure_set(v___x_1481_, 1, lean_box(0));
lean_closure_set(v___x_1481_, 2, v_inst_1479_);
lean_closure_set(v___x_1481_, 3, v_inst_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock(lean_object* v_i_1482_, lean_object* v_b_1483_, lean_object* v_inst_1484_, lean_object* v_inst_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1486_, 0, lean_box(0));
lean_closure_set(v___x_1486_, 1, lean_box(0));
lean_closure_set(v___x_1486_, 2, v_inst_1484_);
lean_closure_set(v___x_1486_, 3, v_inst_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_unsigned_to_nat(0u);
v___x_1512_ = lean_nat_to_int(v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg___boxed(lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_x_1539_, lean_object* v_prec_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1537_, v_inst_1538_, v_x_1539_, v_prec_1540_);
lean_dec(v_prec_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg(lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_x_1544_, lean_object* v_prec_1545_){
_start:
{
lean_object* v_localinst_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_inc_ref(v_inst_1543_);
lean_inc_ref(v_inst_1542_);
v_localinst_1546_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1546_, 0, v_inst_1542_);
lean_closure_set(v_localinst_1546_, 1, v_inst_1543_);
v___x_1547_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1547_, 0, lean_box(0));
lean_closure_set(v___x_1547_, 1, v_inst_1542_);
lean_inc_ref(v_localinst_1546_);
v___x_1548_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_1548_, 0, lean_box(0));
lean_closure_set(v___x_1548_, 1, v_localinst_1546_);
switch(lean_obj_tag(v_x_1544_))
{
case 0:
{
lean_object* v_contents_1549_; lean_object* v___y_1551_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v_localinst_1546_);
lean_dec_ref(v_inst_1543_);
v_contents_1549_ = lean_ctor_get(v_x_1544_, 0);
lean_inc_ref(v_contents_1549_);
lean_dec_ref_known(v_x_1544_, 1);
v___x_1559_ = lean_unsigned_to_nat(1024u);
v___x_1560_ = lean_nat_dec_le(v___x_1559_, v_prec_1545_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1551_ = v___x_1561_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1551_ = v___x_1562_;
goto v___jp_1550_;
}
v___jp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1552_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__2));
v___x_1553_ = l_Array_repr___redArg(v___x_1547_, v_contents_1549_);
v___x_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
lean_inc(v___y_1551_);
v___x_1555_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___y_1551_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = 0;
v___x_1557_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*1, v___x_1556_);
v___x_1558_ = l_Repr_addAppParen(v___x_1557_, v_prec_1545_);
return v___x_1558_;
}
}
case 1:
{
lean_object* v_content_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v___x_1547_);
lean_dec_ref(v_localinst_1546_);
lean_dec_ref(v_inst_1543_);
v_content_1563_ = lean_ctor_get(v_x_1544_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_x_1544_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1565_ = v_x_1544_;
v_isShared_1566_ = v_isSharedCheck_1583_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_content_1563_);
lean_dec(v_x_1544_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1583_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___y_1568_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = lean_unsigned_to_nat(1024u);
v___x_1580_ = lean_nat_dec_le(v___x_1579_, v_prec_1545_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1568_ = v___x_1581_;
goto v___jp_1567_;
}
else
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1568_ = v___x_1582_;
goto v___jp_1567_;
}
v___jp_1567_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1569_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__5));
v___x_1570_ = l_String_quote(v_content_1563_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set_tag(v___x_1565_, 3);
lean_ctor_set(v___x_1565_, 0, v___x_1570_);
v___x_1572_ = v___x_1565_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1569_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
lean_inc(v___y_1568_);
v___x_1574_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___y_1568_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = 0;
v___x_1576_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*1, v___x_1575_);
v___x_1577_ = l_Repr_addAppParen(v___x_1576_, v_prec_1545_);
return v___x_1577_;
}
}
}
}
case 2:
{
lean_object* v_items_1584_; lean_object* v___y_1586_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
lean_dec_ref(v___x_1547_);
lean_dec_ref(v_localinst_1546_);
lean_dec_ref(v_inst_1543_);
v_items_1584_ = lean_ctor_get(v_x_1544_, 0);
lean_inc_ref(v_items_1584_);
lean_dec_ref_known(v_x_1544_, 1);
v___x_1594_ = lean_unsigned_to_nat(1024u);
v___x_1595_ = lean_nat_dec_le(v___x_1594_, v_prec_1545_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1586_ = v___x_1596_;
goto v___jp_1585_;
}
else
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1586_ = v___x_1597_;
goto v___jp_1585_;
}
v___jp_1585_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1587_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__8));
v___x_1588_ = l_Array_repr___redArg(v___x_1548_, v_items_1584_);
v___x_1589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
lean_inc(v___y_1586_);
v___x_1590_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___y_1586_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = 0;
v___x_1592_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set_uint8(v___x_1592_, sizeof(void*)*1, v___x_1591_);
v___x_1593_ = l_Repr_addAppParen(v___x_1592_, v_prec_1545_);
return v___x_1593_;
}
}
case 3:
{
lean_object* v_start_1598_; lean_object* v_items_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v___x_1547_);
lean_dec_ref(v_localinst_1546_);
lean_dec_ref(v_inst_1543_);
v_start_1598_ = lean_ctor_get(v_x_1544_, 0);
v_items_1599_ = lean_ctor_get(v_x_1544_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_x_1544_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1601_ = v_x_1544_;
v_isShared_1602_ = v_isSharedCheck_1634_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_items_1599_);
lean_inc(v_start_1598_);
lean_dec(v_x_1544_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1634_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1619_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = lean_unsigned_to_nat(1024u);
v___x_1631_ = lean_nat_dec_le(v___x_1630_, v_prec_1545_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1619_ = v___x_1632_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1619_ = v___x_1633_;
goto v___jp_1618_;
}
v___jp_1603_:
{
lean_object* v___x_1609_; 
lean_inc(v___y_1604_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set_tag(v___x_1601_, 5);
lean_ctor_set(v___x_1601_, 1, v___y_1607_);
lean_ctor_set(v___x_1601_, 0, v___y_1604_);
v___x_1609_ = v___x_1601_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___y_1604_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___y_1607_);
v___x_1609_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_inc(v___y_1606_);
v___x_1610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___y_1606_);
v___x_1611_ = l_Array_repr___redArg(v___x_1548_, v_items_1599_);
v___x_1612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
lean_inc(v___y_1605_);
v___x_1613_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___y_1605_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = 0;
v___x_1615_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set_uint8(v___x_1615_, sizeof(void*)*1, v___x_1614_);
v___x_1616_ = l_Repr_addAppParen(v___x_1615_, v_prec_1545_);
return v___x_1616_;
}
}
v___jp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1620_ = lean_box(1);
v___x_1621_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__11));
v___x_1622_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___redArg___closed__12, &l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12);
v___x_1623_ = lean_int_dec_lt(v_start_1598_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = l_Int_repr(v_start_1598_);
lean_dec(v_start_1598_);
v___x_1625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
v___y_1604_ = v___x_1621_;
v___y_1605_ = v___y_1619_;
v___y_1606_ = v___x_1620_;
v___y_1607_ = v___x_1625_;
goto v___jp_1603_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1626_ = lean_unsigned_to_nat(1024u);
v___x_1627_ = l_Int_repr(v_start_1598_);
lean_dec(v_start_1598_);
v___x_1628_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
v___x_1629_ = l_Repr_addAppParen(v___x_1628_, v___x_1626_);
v___y_1604_ = v___x_1621_;
v___y_1605_ = v___y_1619_;
v___y_1606_ = v___x_1620_;
v___y_1607_ = v___x_1629_;
goto v___jp_1603_;
}
}
}
}
case 4:
{
lean_object* v_items_1635_; lean_object* v___x_1636_; lean_object* v___y_1638_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v_inst_1543_);
v_items_1635_ = lean_ctor_get(v_x_1544_, 0);
lean_inc_ref(v_items_1635_);
lean_dec_ref_known(v_x_1544_, 1);
v___x_1636_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1636_, 0, lean_box(0));
lean_closure_set(v___x_1636_, 1, lean_box(0));
lean_closure_set(v___x_1636_, 2, v___x_1547_);
lean_closure_set(v___x_1636_, 3, v_localinst_1546_);
v___x_1646_ = lean_unsigned_to_nat(1024u);
v___x_1647_ = lean_nat_dec_le(v___x_1646_, v_prec_1545_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1638_ = v___x_1648_;
goto v___jp_1637_;
}
else
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1638_ = v___x_1649_;
goto v___jp_1637_;
}
v___jp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1639_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__15));
v___x_1640_ = l_Array_repr___redArg(v___x_1636_, v_items_1635_);
v___x_1641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
lean_inc(v___y_1638_);
v___x_1642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___y_1638_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = 0;
v___x_1644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set_uint8(v___x_1644_, sizeof(void*)*1, v___x_1643_);
v___x_1645_ = l_Repr_addAppParen(v___x_1644_, v_prec_1545_);
return v___x_1645_;
}
}
case 5:
{
lean_object* v_items_1650_; lean_object* v___y_1652_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v___x_1547_);
lean_dec_ref(v_inst_1543_);
v_items_1650_ = lean_ctor_get(v_x_1544_, 0);
lean_inc_ref(v_items_1650_);
lean_dec_ref_known(v_x_1544_, 1);
v___x_1660_ = lean_unsigned_to_nat(1024u);
v___x_1661_ = lean_nat_dec_le(v___x_1660_, v_prec_1545_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1652_ = v___x_1662_;
goto v___jp_1651_;
}
else
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1652_ = v___x_1663_;
goto v___jp_1651_;
}
v___jp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1653_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__18));
v___x_1654_ = l_Array_repr___redArg(v_localinst_1546_, v_items_1650_);
v___x_1655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
lean_inc(v___y_1652_);
v___x_1656_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___y_1652_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = 0;
v___x_1658_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*1, v___x_1657_);
v___x_1659_ = l_Repr_addAppParen(v___x_1658_, v_prec_1545_);
return v___x_1659_;
}
}
case 6:
{
lean_object* v_content_1664_; lean_object* v___y_1666_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v___x_1547_);
lean_dec_ref(v_inst_1543_);
v_content_1664_ = lean_ctor_get(v_x_1544_, 0);
lean_inc_ref(v_content_1664_);
lean_dec_ref_known(v_x_1544_, 1);
v___x_1674_ = lean_unsigned_to_nat(1024u);
v___x_1675_ = lean_nat_dec_le(v___x_1674_, v_prec_1545_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1666_ = v___x_1676_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1666_ = v___x_1677_;
goto v___jp_1665_;
}
v___jp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1667_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__21));
v___x_1668_ = l_Array_repr___redArg(v_localinst_1546_, v_content_1664_);
v___x_1669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
lean_inc(v___y_1666_);
v___x_1670_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___y_1666_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = 0;
v___x_1672_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*1, v___x_1671_);
v___x_1673_ = l_Repr_addAppParen(v___x_1672_, v_prec_1545_);
return v___x_1673_;
}
}
default: 
{
lean_object* v_container_1678_; lean_object* v_content_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v___x_1547_);
v_container_1678_ = lean_ctor_get(v_x_1544_, 0);
v_content_1679_ = lean_ctor_get(v_x_1544_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_x_1544_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1681_ = v_x_1544_;
v_isShared_1682_ = v_isSharedCheck_1703_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_content_1679_);
lean_inc(v_container_1678_);
lean_dec(v_x_1544_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1703_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___y_1684_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1699_ = lean_unsigned_to_nat(1024u);
v___x_1700_ = lean_nat_dec_le(v___x_1699_, v_prec_1545_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1684_ = v___x_1701_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1684_ = v___x_1702_;
goto v___jp_1683_;
}
v___jp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1685_ = lean_box(1);
v___x_1686_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__24));
v___x_1687_ = lean_unsigned_to_nat(1024u);
v___x_1688_ = lean_apply_2(v_inst_1543_, v_container_1678_, v___x_1687_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 5);
lean_ctor_set(v___x_1681_, 1, v___x_1688_);
lean_ctor_set(v___x_1681_, 0, v___x_1686_);
v___x_1690_ = v___x_1681_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v___x_1685_);
v___x_1692_ = l_Array_repr___redArg(v_localinst_1546_, v_content_1679_);
v___x_1693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
lean_inc(v___y_1684_);
v___x_1694_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___y_1684_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = 0;
v___x_1696_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set_uint8(v___x_1696_, sizeof(void*)*1, v___x_1695_);
v___x_1697_ = l_Repr_addAppParen(v___x_1696_, v_prec_1545_);
return v___x_1697_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr(lean_object* v_i_1704_, lean_object* v_b_1705_, lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_x_1708_, lean_object* v_prec_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1706_, v_inst_1707_, v_x_1708_, v_prec_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___boxed(lean_object* v_i_1711_, lean_object* v_b_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_x_1715_, lean_object* v_prec_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Doc_instReprBlock_repr(v_i_1711_, v_b_1712_, v_inst_1713_, v_inst_1714_, v_x_1715_, v_prec_1716_);
lean_dec(v_prec_1716_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock___redArg(lean_object* v_inst_1718_, lean_object* v_inst_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1720_, 0, lean_box(0));
lean_closure_set(v___x_1720_, 1, lean_box(0));
lean_closure_set(v___x_1720_, 2, v_inst_1718_);
lean_closure_set(v___x_1720_, 3, v_inst_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock(lean_object* v_i_1721_, lean_object* v_b_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1725_, 0, lean_box(0));
lean_closure_set(v___x_1725_, 1, lean_box(0));
lean_closure_set(v___x_1725_, 2, v_inst_1723_);
lean_closure_set(v___x_1725_, 3, v_inst_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg(){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlock_default___redArg___closed__1));
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg___boxed(lean_object* v___dummy_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
return v_res_1733_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedBlock_default___closed__0(void){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default(lean_object* v_i_1735_, lean_object* v_b_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg(){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg___boxed(lean_object* v___dummy_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Doc_instInhabitedBlock___redArg();
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock(lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg(){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = ((lean_object*)(l_Lean_Doc_Block_empty___redArg___closed__1));
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg___boxed(lean_object* v___dummy_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Doc_Block_empty___redArg();
return v_res_1752_;
}
}
static lean_object* _init_l_Lean_Doc_Block_empty___closed__0(void){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Doc_Block_empty___redArg();
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty(lean_object* v_i_1754_, lean_object* v_b_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_obj_once(&l_Lean_Doc_Block_empty___closed__0, &l_Lean_Doc_Block_empty___closed__0_once, _init_l_Lean_Doc_Block_empty___closed__0);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg(lean_object* v_x_1757_){
_start:
{
lean_inc_ref(v_x_1757_);
return v_x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg___boxed(lean_object* v_x_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Doc_Block_cast___redArg(v_x_1758_);
lean_dec_ref(v_x_1758_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast(lean_object* v_i_1760_, lean_object* v_i_x27_1761_, lean_object* v_b_1762_, lean_object* v_b_x27_1763_, lean_object* v_inlines__eq_1764_, lean_object* v_blocks__eq_1765_, lean_object* v_x_1766_){
_start:
{
lean_inc_ref(v_x_1766_);
return v_x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___boxed(lean_object* v_i_1767_, lean_object* v_i_x27_1768_, lean_object* v_b_1769_, lean_object* v_b_x27_1770_, lean_object* v_inlines__eq_1771_, lean_object* v_blocks__eq_1772_, lean_object* v_x_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Doc_Block_cast(v_i_1767_, v_i_x27_1768_, v_b_1769_, v_b_x27_1770_, v_inlines__eq_1771_, v_blocks__eq_1772_, v_x_1773_);
lean_dec_ref(v_x_1773_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___redArg___boxed(lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_){
_start:
{
uint8_t v_res_1780_; lean_object* v_r_1781_; 
v_res_1780_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1775_, v_inst_1776_, v_inst_1777_, v_x_1778_, v_x_1779_);
v_r_1781_ = lean_box(v_res_1780_);
return v_r_1781_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq___redArg(lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_x_1785_, lean_object* v_x_1786_){
_start:
{
lean_object* v_title_1787_; lean_object* v_titleString_1788_; lean_object* v_metadata_1789_; lean_object* v_content_1790_; lean_object* v_subParts_1791_; lean_object* v_title_1792_; lean_object* v_titleString_1793_; lean_object* v_metadata_1794_; lean_object* v_content_1795_; lean_object* v_subParts_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_title_1787_ = lean_ctor_get(v_x_1785_, 0);
lean_inc_ref(v_title_1787_);
v_titleString_1788_ = lean_ctor_get(v_x_1785_, 1);
lean_inc_ref(v_titleString_1788_);
v_metadata_1789_ = lean_ctor_get(v_x_1785_, 2);
lean_inc(v_metadata_1789_);
v_content_1790_ = lean_ctor_get(v_x_1785_, 3);
lean_inc_ref(v_content_1790_);
v_subParts_1791_ = lean_ctor_get(v_x_1785_, 4);
lean_inc_ref(v_subParts_1791_);
lean_dec_ref(v_x_1785_);
v_title_1792_ = lean_ctor_get(v_x_1786_, 0);
lean_inc_ref(v_title_1792_);
v_titleString_1793_ = lean_ctor_get(v_x_1786_, 1);
lean_inc_ref(v_titleString_1793_);
v_metadata_1794_ = lean_ctor_get(v_x_1786_, 2);
lean_inc(v_metadata_1794_);
v_content_1795_ = lean_ctor_get(v_x_1786_, 3);
lean_inc_ref(v_content_1795_);
v_subParts_1796_ = lean_ctor_get(v_x_1786_, 4);
lean_inc_ref(v_subParts_1796_);
lean_dec_ref(v_x_1786_);
v___x_1797_ = lean_array_get_size(v_title_1787_);
v___x_1798_ = lean_array_get_size(v_title_1792_);
v___x_1799_ = lean_nat_dec_eq(v___x_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_dec_ref(v_subParts_1796_);
lean_dec_ref(v_content_1795_);
lean_dec(v_metadata_1794_);
lean_dec_ref(v_titleString_1793_);
lean_dec_ref(v_title_1792_);
lean_dec_ref(v_subParts_1791_);
lean_dec_ref(v_content_1790_);
lean_dec(v_metadata_1789_);
lean_dec_ref(v_titleString_1788_);
lean_dec_ref(v_title_1787_);
lean_dec_ref(v_inst_1784_);
lean_dec_ref(v_inst_1783_);
lean_dec_ref(v_inst_1782_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
lean_inc_ref(v_inst_1784_);
lean_inc_ref(v_inst_1783_);
lean_inc_ref_n(v_inst_1782_, 2);
v___x_1800_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___redArg___boxed), 5, 3);
lean_closure_set(v___x_1800_, 0, v_inst_1782_);
lean_closure_set(v___x_1800_, 1, v_inst_1783_);
lean_closure_set(v___x_1800_, 2, v_inst_1784_);
v___x_1801_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1801_, 0, lean_box(0));
lean_closure_set(v___x_1801_, 1, v_inst_1782_);
v___x_1802_ = l_Array_isEqvAux___redArg(v_title_1787_, v_title_1792_, v___x_1801_, v___x_1797_);
lean_dec_ref(v_title_1792_);
lean_dec_ref(v_title_1787_);
if (v___x_1802_ == 0)
{
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_subParts_1796_);
lean_dec_ref(v_content_1795_);
lean_dec(v_metadata_1794_);
lean_dec_ref(v_titleString_1793_);
lean_dec_ref(v_subParts_1791_);
lean_dec_ref(v_content_1790_);
lean_dec(v_metadata_1789_);
lean_dec_ref(v_titleString_1788_);
lean_dec_ref(v_inst_1784_);
lean_dec_ref(v_inst_1783_);
lean_dec_ref(v_inst_1782_);
return v___x_1802_;
}
else
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_string_dec_eq(v_titleString_1788_, v_titleString_1793_);
lean_dec_ref(v_titleString_1793_);
lean_dec_ref(v_titleString_1788_);
if (v___x_1803_ == 0)
{
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_subParts_1796_);
lean_dec_ref(v_content_1795_);
lean_dec(v_metadata_1794_);
lean_dec_ref(v_subParts_1791_);
lean_dec_ref(v_content_1790_);
lean_dec(v_metadata_1789_);
lean_dec_ref(v_inst_1784_);
lean_dec_ref(v_inst_1783_);
lean_dec_ref(v_inst_1782_);
return v___x_1803_;
}
else
{
uint8_t v___x_1804_; 
v___x_1804_ = l_instBEqOption_beq___redArg(v_inst_1784_, v_metadata_1789_, v_metadata_1794_);
if (v___x_1804_ == 0)
{
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_subParts_1796_);
lean_dec_ref(v_content_1795_);
lean_dec_ref(v_subParts_1791_);
lean_dec_ref(v_content_1790_);
lean_dec_ref(v_inst_1783_);
lean_dec_ref(v_inst_1782_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1805_ = lean_array_get_size(v_content_1790_);
v___x_1806_ = lean_array_get_size(v_content_1795_);
v___x_1807_ = lean_nat_dec_eq(v___x_1805_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_subParts_1796_);
lean_dec_ref(v_content_1795_);
lean_dec_ref(v_subParts_1791_);
lean_dec_ref(v_content_1790_);
lean_dec_ref(v_inst_1783_);
lean_dec_ref(v_inst_1782_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1808_, 0, lean_box(0));
lean_closure_set(v___x_1808_, 1, lean_box(0));
lean_closure_set(v___x_1808_, 2, v_inst_1782_);
lean_closure_set(v___x_1808_, 3, v_inst_1783_);
v___x_1809_ = l_Array_isEqvAux___redArg(v_content_1790_, v_content_1795_, v___x_1808_, v___x_1805_);
lean_dec_ref(v_content_1795_);
lean_dec_ref(v_content_1790_);
if (v___x_1809_ == 0)
{
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_subParts_1796_);
lean_dec_ref(v_subParts_1791_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = lean_array_get_size(v_subParts_1791_);
v___x_1811_ = lean_array_get_size(v_subParts_1796_);
v___x_1812_ = lean_nat_dec_eq(v___x_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_subParts_1796_);
lean_dec_ref(v_subParts_1791_);
return v___x_1812_;
}
else
{
uint8_t v___x_1813_; 
v___x_1813_ = l_Array_isEqvAux___redArg(v_subParts_1791_, v_subParts_1796_, v___x_1800_, v___x_1810_);
lean_dec_ref(v_subParts_1796_);
lean_dec_ref(v_subParts_1791_);
return v___x_1813_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq(lean_object* v_i_1814_, lean_object* v_b_1815_, lean_object* v_p_1816_, lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
uint8_t v___x_1822_; 
v___x_1822_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1817_, v_inst_1818_, v_inst_1819_, v_x_1820_, v_x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___boxed(lean_object* v_i_1823_, lean_object* v_b_1824_, lean_object* v_p_1825_, lean_object* v_inst_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
uint8_t v_res_1831_; lean_object* v_r_1832_; 
v_res_1831_ = l_Lean_Doc_instBEqPart_beq(v_i_1823_, v_b_1824_, v_p_1825_, v_inst_1826_, v_inst_1827_, v_inst_1828_, v_x_1829_, v_x_1830_);
v_r_1832_ = lean_box(v_res_1831_);
return v_r_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart___redArg(lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1836_, 0, lean_box(0));
lean_closure_set(v___x_1836_, 1, lean_box(0));
lean_closure_set(v___x_1836_, 2, lean_box(0));
lean_closure_set(v___x_1836_, 3, v_inst_1833_);
lean_closure_set(v___x_1836_, 4, v_inst_1834_);
lean_closure_set(v___x_1836_, 5, v_inst_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart(lean_object* v_i_1837_, lean_object* v_b_1838_, lean_object* v_p_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1843_, 0, lean_box(0));
lean_closure_set(v___x_1843_, 1, lean_box(0));
lean_closure_set(v___x_1843_, 2, lean_box(0));
lean_closure_set(v___x_1843_, 3, v_inst_1840_);
lean_closure_set(v___x_1843_, 4, v_inst_1841_);
lean_closure_set(v___x_1843_, 5, v_inst_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___redArg___boxed(lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_){
_start:
{
uint8_t v_res_1849_; lean_object* v_r_1850_; 
v_res_1849_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1844_, v_inst_1845_, v_inst_1846_, v_x_1847_, v_x_1848_);
v_r_1850_ = lean_box(v_res_1849_);
return v_r_1850_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord___redArg(lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v_title_1856_; lean_object* v_titleString_1857_; lean_object* v_metadata_1858_; lean_object* v_content_1859_; lean_object* v_subParts_1860_; lean_object* v_title_1861_; lean_object* v_titleString_1862_; lean_object* v_metadata_1863_; lean_object* v_content_1864_; lean_object* v_subParts_1865_; lean_object* v___x_1866_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v_title_1856_ = lean_ctor_get(v_x_1854_, 0);
lean_inc_ref(v_title_1856_);
v_titleString_1857_ = lean_ctor_get(v_x_1854_, 1);
lean_inc_ref(v_titleString_1857_);
v_metadata_1858_ = lean_ctor_get(v_x_1854_, 2);
lean_inc(v_metadata_1858_);
v_content_1859_ = lean_ctor_get(v_x_1854_, 3);
lean_inc_ref(v_content_1859_);
v_subParts_1860_ = lean_ctor_get(v_x_1854_, 4);
lean_inc_ref(v_subParts_1860_);
lean_dec_ref(v_x_1854_);
v_title_1861_ = lean_ctor_get(v_x_1855_, 0);
lean_inc_ref(v_title_1861_);
v_titleString_1862_ = lean_ctor_get(v_x_1855_, 1);
lean_inc_ref(v_titleString_1862_);
v_metadata_1863_ = lean_ctor_get(v_x_1855_, 2);
lean_inc(v_metadata_1863_);
v_content_1864_ = lean_ctor_get(v_x_1855_, 3);
lean_inc_ref(v_content_1864_);
v_subParts_1865_ = lean_ctor_get(v_x_1855_, 4);
lean_inc_ref(v_subParts_1865_);
lean_dec_ref(v_x_1855_);
lean_inc_ref(v_inst_1853_);
lean_inc_ref(v_inst_1852_);
lean_inc_ref_n(v_inst_1851_, 2);
v___x_1866_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___redArg___boxed), 5, 3);
lean_closure_set(v___x_1866_, 0, v_inst_1851_);
lean_closure_set(v___x_1866_, 1, v_inst_1852_);
lean_closure_set(v___x_1866_, 2, v_inst_1853_);
v___x_1872_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1872_, 0, lean_box(0));
lean_closure_set(v___x_1872_, 1, v_inst_1851_);
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1872_, v_title_1856_, v_title_1861_, v___x_1873_);
lean_dec_ref(v_title_1861_);
lean_dec_ref(v_title_1856_);
if (v___x_1874_ == 1)
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_string_compare(v_titleString_1857_, v_titleString_1862_);
lean_dec_ref(v_titleString_1862_);
lean_dec_ref(v_titleString_1857_);
if (v___x_1875_ == 1)
{
if (lean_obj_tag(v_metadata_1858_) == 0)
{
lean_dec_ref(v_inst_1853_);
if (lean_obj_tag(v_metadata_1863_) == 0)
{
goto v___jp_1867_;
}
else
{
uint8_t v___x_1876_; 
lean_dec_ref_known(v_metadata_1863_, 1);
lean_dec_ref(v___x_1866_);
lean_dec_ref(v_subParts_1865_);
lean_dec_ref(v_content_1864_);
lean_dec_ref(v_subParts_1860_);
lean_dec_ref(v_content_1859_);
lean_dec_ref(v_inst_1852_);
lean_dec_ref(v_inst_1851_);
v___x_1876_ = 0;
return v___x_1876_;
}
}
else
{
if (lean_obj_tag(v_metadata_1863_) == 0)
{
uint8_t v___x_1877_; 
lean_dec_ref_known(v_metadata_1858_, 1);
lean_dec_ref(v___x_1866_);
lean_dec_ref(v_subParts_1865_);
lean_dec_ref(v_content_1864_);
lean_dec_ref(v_subParts_1860_);
lean_dec_ref(v_content_1859_);
lean_dec_ref(v_inst_1853_);
lean_dec_ref(v_inst_1852_);
lean_dec_ref(v_inst_1851_);
v___x_1877_ = 2;
return v___x_1877_;
}
else
{
lean_object* v_val_1878_; lean_object* v_val_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v_val_1878_ = lean_ctor_get(v_metadata_1858_, 0);
lean_inc(v_val_1878_);
lean_dec_ref_known(v_metadata_1858_, 1);
v_val_1879_ = lean_ctor_get(v_metadata_1863_, 0);
lean_inc(v_val_1879_);
lean_dec_ref_known(v_metadata_1863_, 1);
v___x_1880_ = lean_apply_2(v_inst_1853_, v_val_1878_, v_val_1879_);
v___x_1881_ = lean_unbox(v___x_1880_);
if (v___x_1881_ == 1)
{
goto v___jp_1867_;
}
else
{
uint8_t v___x_1882_; 
lean_dec_ref(v___x_1866_);
lean_dec_ref(v_subParts_1865_);
lean_dec_ref(v_content_1864_);
lean_dec_ref(v_subParts_1860_);
lean_dec_ref(v_content_1859_);
lean_dec_ref(v_inst_1852_);
lean_dec_ref(v_inst_1851_);
v___x_1882_ = lean_unbox(v___x_1880_);
return v___x_1882_;
}
}
}
}
else
{
lean_dec_ref(v___x_1866_);
lean_dec_ref(v_subParts_1865_);
lean_dec_ref(v_content_1864_);
lean_dec(v_metadata_1863_);
lean_dec_ref(v_subParts_1860_);
lean_dec_ref(v_content_1859_);
lean_dec(v_metadata_1858_);
lean_dec_ref(v_inst_1853_);
lean_dec_ref(v_inst_1852_);
lean_dec_ref(v_inst_1851_);
return v___x_1875_;
}
}
else
{
lean_dec_ref(v___x_1866_);
lean_dec_ref(v_subParts_1865_);
lean_dec_ref(v_content_1864_);
lean_dec(v_metadata_1863_);
lean_dec_ref(v_titleString_1862_);
lean_dec_ref(v_subParts_1860_);
lean_dec_ref(v_content_1859_);
lean_dec(v_metadata_1858_);
lean_dec_ref(v_titleString_1857_);
lean_dec_ref(v_inst_1853_);
lean_dec_ref(v_inst_1852_);
lean_dec_ref(v_inst_1851_);
return v___x_1874_;
}
v___jp_1867_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1868_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1868_, 0, lean_box(0));
lean_closure_set(v___x_1868_, 1, lean_box(0));
lean_closure_set(v___x_1868_, 2, v_inst_1851_);
lean_closure_set(v___x_1868_, 3, v_inst_1852_);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1868_, v_content_1859_, v_content_1864_, v___x_1869_);
lean_dec_ref(v_content_1864_);
lean_dec_ref(v_content_1859_);
if (v___x_1870_ == 1)
{
uint8_t v___x_1871_; 
v___x_1871_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1866_, v_subParts_1860_, v_subParts_1865_, v___x_1869_);
lean_dec_ref(v_subParts_1865_);
lean_dec_ref(v_subParts_1860_);
return v___x_1871_;
}
else
{
lean_dec_ref(v___x_1866_);
lean_dec_ref(v_subParts_1865_);
lean_dec_ref(v_subParts_1860_);
return v___x_1870_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord(lean_object* v_i_1883_, lean_object* v_b_1884_, lean_object* v_p_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
uint8_t v___x_1891_; 
v___x_1891_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1886_, v_inst_1887_, v_inst_1888_, v_x_1889_, v_x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___boxed(lean_object* v_i_1892_, lean_object* v_b_1893_, lean_object* v_p_1894_, lean_object* v_inst_1895_, lean_object* v_inst_1896_, lean_object* v_inst_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
uint8_t v_res_1900_; lean_object* v_r_1901_; 
v_res_1900_ = l_Lean_Doc_instOrdPart_ord(v_i_1892_, v_b_1893_, v_p_1894_, v_inst_1895_, v_inst_1896_, v_inst_1897_, v_x_1898_, v_x_1899_);
v_r_1901_ = lean_box(v_res_1900_);
return v_r_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart___redArg(lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1905_, 0, lean_box(0));
lean_closure_set(v___x_1905_, 1, lean_box(0));
lean_closure_set(v___x_1905_, 2, lean_box(0));
lean_closure_set(v___x_1905_, 3, v_inst_1902_);
lean_closure_set(v___x_1905_, 4, v_inst_1903_);
lean_closure_set(v___x_1905_, 5, v_inst_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart(lean_object* v_i_1906_, lean_object* v_b_1907_, lean_object* v_p_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_inst_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1912_, 0, lean_box(0));
lean_closure_set(v___x_1912_, 1, lean_box(0));
lean_closure_set(v___x_1912_, 2, lean_box(0));
lean_closure_set(v___x_1912_, 3, v_inst_1909_);
lean_closure_set(v___x_1912_, 4, v_inst_1910_);
lean_closure_set(v___x_1912_, 5, v_inst_1911_);
return v___x_1912_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_unsigned_to_nat(9u);
v___x_1923_ = lean_nat_to_int(v___x_1922_);
return v___x_1923_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_unsigned_to_nat(15u);
v___x_1928_ = lean_nat_to_int(v___x_1927_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_unsigned_to_nat(11u);
v___x_1936_ = lean_nat_to_int(v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg___boxed(lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_x_1943_, lean_object* v_prec_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_1940_, v_inst_1941_, v_inst_1942_, v_x_1943_, v_prec_1944_);
lean_dec(v_prec_1944_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg(lean_object* v_inst_1946_, lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_x_1949_, lean_object* v_prec_1950_){
_start:
{
lean_object* v_title_1951_; lean_object* v_titleString_1952_; lean_object* v_metadata_1953_; lean_object* v_content_1954_; lean_object* v_subParts_1955_; lean_object* v_localinst_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_title_1951_ = lean_ctor_get(v_x_1949_, 0);
lean_inc_ref(v_title_1951_);
v_titleString_1952_ = lean_ctor_get(v_x_1949_, 1);
lean_inc_ref(v_titleString_1952_);
v_metadata_1953_ = lean_ctor_get(v_x_1949_, 2);
lean_inc(v_metadata_1953_);
v_content_1954_ = lean_ctor_get(v_x_1949_, 3);
lean_inc_ref(v_content_1954_);
v_subParts_1955_ = lean_ctor_get(v_x_1949_, 4);
lean_inc_ref(v_subParts_1955_);
lean_dec_ref(v_x_1949_);
lean_inc_ref(v_inst_1948_);
lean_inc_ref(v_inst_1947_);
lean_inc_ref_n(v_inst_1946_, 2);
v_localinst_1956_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___redArg___boxed), 5, 3);
lean_closure_set(v_localinst_1956_, 0, v_inst_1946_);
lean_closure_set(v_localinst_1956_, 1, v_inst_1947_);
lean_closure_set(v_localinst_1956_, 2, v_inst_1948_);
v___x_1957_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1958_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__3));
v___x_1959_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4);
v___x_1960_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1960_, 0, lean_box(0));
lean_closure_set(v___x_1960_, 1, v_inst_1946_);
v___x_1961_ = l_Array_repr___redArg(v___x_1960_, v_title_1951_);
v___x_1962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1959_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = 0;
v___x_1964_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1958_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = lean_box(1);
v___x_1969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__6));
v___x_1971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
lean_ctor_set(v___x_1972_, 1, v___x_1957_);
v___x_1973_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7);
v___x_1974_ = l_String_quote(v_titleString_1952_);
v___x_1975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1973_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*1, v___x_1963_);
v___x_1978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1972_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v___x_1966_);
v___x_1980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
lean_ctor_set(v___x_1980_, 1, v___x_1968_);
v___x_1981_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__9));
v___x_1982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v___x_1957_);
v___x_1984_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = l_Option_repr___redArg(v_inst_1948_, v_metadata_1953_, v___x_1985_);
v___x_1987_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1984_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*1, v___x_1963_);
v___x_1989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1983_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v___x_1966_);
v___x_1991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v___x_1968_);
v___x_1992_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__11));
v___x_1993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v___x_1957_);
v___x_1995_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12);
v___x_1996_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1996_, 0, lean_box(0));
lean_closure_set(v___x_1996_, 1, lean_box(0));
lean_closure_set(v___x_1996_, 2, v_inst_1946_);
lean_closure_set(v___x_1996_, 3, v_inst_1947_);
v___x_1997_ = l_Array_repr___redArg(v___x_1996_, v_content_1954_);
v___x_1998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1995_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
lean_ctor_set_uint8(v___x_1999_, sizeof(void*)*1, v___x_1963_);
v___x_2000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1994_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v___x_1966_);
v___x_2002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v___x_1968_);
v___x_2003_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__14));
v___x_2004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_ctor_set(v___x_2005_, 1, v___x_1957_);
v___x_2006_ = l_Array_repr___redArg(v_localinst_1956_, v_subParts_1955_);
v___x_2007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_1984_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*1, v___x_1963_);
v___x_2009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2005_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_2011_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_2012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
lean_ctor_set(v___x_2012_, 1, v___x_2009_);
v___x_2013_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_2014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2012_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2010_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*1, v___x_1963_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr(lean_object* v_i_2017_, lean_object* v_b_2018_, lean_object* v_p_2019_, lean_object* v_inst_2020_, lean_object* v_inst_2021_, lean_object* v_inst_2022_, lean_object* v_x_2023_, lean_object* v_prec_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_2020_, v_inst_2021_, v_inst_2022_, v_x_2023_, v_prec_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___boxed(lean_object* v_i_2026_, lean_object* v_b_2027_, lean_object* v_p_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_inst_2031_, lean_object* v_x_2032_, lean_object* v_prec_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Doc_instReprPart_repr(v_i_2026_, v_b_2027_, v_p_2028_, v_inst_2029_, v_inst_2030_, v_inst_2031_, v_x_2032_, v_prec_2033_);
lean_dec(v_prec_2033_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart___redArg(lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2038_, 0, lean_box(0));
lean_closure_set(v___x_2038_, 1, lean_box(0));
lean_closure_set(v___x_2038_, 2, lean_box(0));
lean_closure_set(v___x_2038_, 3, v_inst_2035_);
lean_closure_set(v___x_2038_, 4, v_inst_2036_);
lean_closure_set(v___x_2038_, 5, v_inst_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart(lean_object* v_i_2039_, lean_object* v_b_2040_, lean_object* v_p_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_inst_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2045_, 0, lean_box(0));
lean_closure_set(v___x_2045_, 1, lean_box(0));
lean_closure_set(v___x_2045_, 2, lean_box(0));
lean_closure_set(v___x_2045_, 3, v_inst_2042_);
lean_closure_set(v___x_2045_, 4, v_inst_2043_);
lean_closure_set(v___x_2045_, 5, v_inst_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg(){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = ((lean_object*)(l_Lean_Doc_instInhabitedPart_default___redArg___closed__0));
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg___boxed(lean_object* v___dummy_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Doc_instInhabitedPart_default___redArg();
return v_res_2053_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedPart_default___closed__0(void){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_Doc_instInhabitedPart_default___redArg();
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default(lean_object* v_i_2055_, lean_object* v_b_2056_, lean_object* v_p_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg(){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg___boxed(lean_object* v___dummy_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_Doc_instInhabitedPart___redArg();
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart(lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg(lean_object* v_x_2067_){
_start:
{
lean_inc_ref(v_x_2067_);
return v_x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg___boxed(lean_object* v_x_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Doc_Part_cast___redArg(v_x_2068_);
lean_dec_ref(v_x_2068_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast(lean_object* v_i_2070_, lean_object* v_i_x27_2071_, lean_object* v_b_2072_, lean_object* v_b_x27_2073_, lean_object* v_p_2074_, lean_object* v_p_x27_2075_, lean_object* v_inlines__eq_2076_, lean_object* v_blocks__eq_2077_, lean_object* v_metadata__eq_2078_, lean_object* v_x_2079_){
_start:
{
lean_inc_ref(v_x_2079_);
return v_x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___boxed(lean_object* v_i_2080_, lean_object* v_i_x27_2081_, lean_object* v_b_2082_, lean_object* v_b_x27_2083_, lean_object* v_p_2084_, lean_object* v_p_x27_2085_, lean_object* v_inlines__eq_2086_, lean_object* v_blocks__eq_2087_, lean_object* v_metadata__eq_2088_, lean_object* v_x_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Doc_Part_cast(v_i_2080_, v_i_x27_2081_, v_b_2082_, v_b_x27_2083_, v_p_2084_, v_p_x27_2085_, v_inlines__eq_2086_, v_blocks__eq_2087_, v_metadata__eq_2088_, v_x_2089_);
lean_dec_ref(v_x_2089_);
return v_res_2090_;
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
