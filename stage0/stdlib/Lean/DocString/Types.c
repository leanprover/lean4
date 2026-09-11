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
uint8_t l_Array_compareLex___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Option_repr___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
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
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Doc_MathMode_ctorIdx(v_x_boxed_5_);
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
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_90_ = l_Lean_Doc_MathMode_ctorIdx(v_x_88_);
v___x_91_ = l_Lean_Doc_MathMode_ctorIdx(v_y_89_);
v___x_92_ = lean_nat_dec_eq(v___x_90_, v___x_91_);
lean_dec(v___x_91_);
lean_dec(v___x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqMathMode_beq___boxed(lean_object* v_x_93_, lean_object* v_y_94_){
_start:
{
uint8_t v_x_21__boxed_95_; uint8_t v_y_22__boxed_96_; uint8_t v_res_97_; lean_object* v_r_98_; 
v_x_21__boxed_95_ = lean_unbox(v_x_93_);
v_y_22__boxed_96_ = lean_unbox(v_y_94_);
v_res_97_ = l_Lean_Doc_instBEqMathMode_beq(v_x_21__boxed_95_, v_y_22__boxed_96_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint64_t l_Lean_Doc_instHashableMathMode_hash(uint8_t v_x_101_){
_start:
{
if (v_x_101_ == 0)
{
uint64_t v___x_102_; 
v___x_102_ = 0ULL;
return v___x_102_;
}
else
{
uint64_t v___x_103_; 
v___x_103_ = 1ULL;
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instHashableMathMode_hash___boxed(lean_object* v_x_104_){
_start:
{
uint8_t v_x_28__boxed_105_; uint64_t v_res_106_; lean_object* v_r_107_; 
v_x_28__boxed_105_ = lean_unbox(v_x_104_);
v_res_106_ = l_Lean_Doc_instHashableMathMode_hash(v_x_28__boxed_105_);
v_r_107_ = lean_box_uint64(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdMathMode_ord(uint8_t v_x_110_, uint8_t v_y_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = l_Lean_Doc_MathMode_ctorIdx(v_x_110_);
v___x_113_ = l_Lean_Doc_MathMode_ctorIdx(v_y_111_);
v___x_114_ = lean_nat_dec_lt(v___x_112_, v___x_113_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = lean_nat_dec_eq(v___x_112_, v___x_113_);
lean_dec(v___x_113_);
lean_dec(v___x_112_);
if (v___x_115_ == 0)
{
uint8_t v___x_116_; 
v___x_116_ = 2;
return v___x_116_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 1;
return v___x_117_;
}
}
else
{
uint8_t v___x_118_; 
lean_dec(v___x_113_);
lean_dec(v___x_112_);
v___x_118_ = 0;
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdMathMode_ord___boxed(lean_object* v_x_119_, lean_object* v_y_120_){
_start:
{
uint8_t v_x_30__boxed_121_; uint8_t v_y_31__boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_x_30__boxed_121_ = lean_unbox(v_x_119_);
v_y_31__boxed_122_ = lean_unbox(v_y_120_);
v_res_123_ = l_Lean_Doc_instOrdMathMode_ord(v_x_30__boxed_121_, v_y_31__boxed_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___redArg(lean_object* v_x_127_){
_start:
{
switch(lean_obj_tag(v_x_127_))
{
case 0:
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(0u);
return v___x_128_;
}
case 1:
{
lean_object* v___x_129_; 
v___x_129_ = lean_unsigned_to_nat(1u);
return v___x_129_;
}
case 2:
{
lean_object* v___x_130_; 
v___x_130_ = lean_unsigned_to_nat(2u);
return v___x_130_;
}
case 3:
{
lean_object* v___x_131_; 
v___x_131_ = lean_unsigned_to_nat(3u);
return v___x_131_;
}
case 4:
{
lean_object* v___x_132_; 
v___x_132_ = lean_unsigned_to_nat(4u);
return v___x_132_;
}
case 5:
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(5u);
return v___x_133_;
}
case 6:
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(6u);
return v___x_134_;
}
case 7:
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(7u);
return v___x_135_;
}
case 8:
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(8u);
return v___x_136_;
}
case 9:
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(9u);
return v___x_137_;
}
default: 
{
lean_object* v___x_138_; 
v___x_138_ = lean_unsigned_to_nat(10u);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___redArg___boxed(lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_139_);
lean_dec_ref(v_x_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx(lean_object* v_i_141_, lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___boxed(lean_object* v_i_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Doc_Inline_ctorIdx(v_i_144_, v_x_145_);
lean_dec_ref(v_x_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim___redArg(lean_object* v_t_147_, lean_object* v_k_148_){
_start:
{
switch(lean_obj_tag(v_t_147_))
{
case 4:
{
uint8_t v_mode_149_; lean_object* v_string_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_mode_149_ = lean_ctor_get_uint8(v_t_147_, sizeof(void*)*1);
v_string_150_ = lean_ctor_get(v_t_147_, 0);
lean_inc_ref(v_string_150_);
lean_dec_ref_known(v_t_147_, 1);
v___x_151_ = lean_box(v_mode_149_);
v___x_152_ = lean_apply_2(v_k_148_, v___x_151_, v_string_150_);
return v___x_152_;
}
case 6:
{
lean_object* v_content_153_; lean_object* v_url_154_; lean_object* v___x_155_; 
v_content_153_ = lean_ctor_get(v_t_147_, 0);
lean_inc_ref(v_content_153_);
v_url_154_ = lean_ctor_get(v_t_147_, 1);
lean_inc_ref(v_url_154_);
lean_dec_ref_known(v_t_147_, 2);
v___x_155_ = lean_apply_2(v_k_148_, v_content_153_, v_url_154_);
return v___x_155_;
}
case 7:
{
lean_object* v_name_156_; lean_object* v_content_157_; lean_object* v___x_158_; 
v_name_156_ = lean_ctor_get(v_t_147_, 0);
lean_inc_ref(v_name_156_);
v_content_157_ = lean_ctor_get(v_t_147_, 1);
lean_inc_ref(v_content_157_);
lean_dec_ref_known(v_t_147_, 2);
v___x_158_ = lean_apply_2(v_k_148_, v_name_156_, v_content_157_);
return v___x_158_;
}
case 8:
{
lean_object* v_alt_159_; lean_object* v_url_160_; lean_object* v___x_161_; 
v_alt_159_ = lean_ctor_get(v_t_147_, 0);
lean_inc_ref(v_alt_159_);
v_url_160_ = lean_ctor_get(v_t_147_, 1);
lean_inc_ref(v_url_160_);
lean_dec_ref_known(v_t_147_, 2);
v___x_161_ = lean_apply_2(v_k_148_, v_alt_159_, v_url_160_);
return v___x_161_;
}
case 10:
{
lean_object* v_container_162_; lean_object* v_content_163_; lean_object* v___x_164_; 
v_container_162_ = lean_ctor_get(v_t_147_, 0);
lean_inc(v_container_162_);
v_content_163_ = lean_ctor_get(v_t_147_, 1);
lean_inc_ref(v_content_163_);
lean_dec_ref_known(v_t_147_, 2);
v___x_164_ = lean_apply_2(v_k_148_, v_container_162_, v_content_163_);
return v___x_164_;
}
default: 
{
lean_object* v_string_165_; lean_object* v___x_166_; 
v_string_165_ = lean_ctor_get(v_t_147_, 0);
lean_inc_ref(v_string_165_);
lean_dec_ref(v_t_147_);
v___x_166_ = lean_apply_1(v_k_148_, v_string_165_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim(lean_object* v_i_167_, lean_object* v_motive__1_168_, lean_object* v_ctorIdx_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_k_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_170_, v_k_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim___boxed(lean_object* v_i_174_, lean_object* v_motive__1_175_, lean_object* v_ctorIdx_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_k_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Doc_Inline_ctorElim(v_i_174_, v_motive__1_175_, v_ctorIdx_176_, v_t_177_, v_h_178_, v_k_179_);
lean_dec(v_ctorIdx_176_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_text_elim___redArg(lean_object* v_t_181_, lean_object* v_text_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_181_, v_text_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_text_elim(lean_object* v_i_184_, lean_object* v_motive__1_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_text_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_186_, v_text_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_emph_elim___redArg(lean_object* v_t_190_, lean_object* v_emph_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_190_, v_emph_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_emph_elim(lean_object* v_i_193_, lean_object* v_motive__1_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_emph_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_195_, v_emph_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_bold_elim___redArg(lean_object* v_t_199_, lean_object* v_bold_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_199_, v_bold_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_bold_elim(lean_object* v_i_202_, lean_object* v_motive__1_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_bold_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_204_, v_bold_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_code_elim___redArg(lean_object* v_t_208_, lean_object* v_code_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_208_, v_code_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_code_elim(lean_object* v_i_211_, lean_object* v_motive__1_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_code_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_213_, v_code_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_math_elim___redArg(lean_object* v_t_217_, lean_object* v_math_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_217_, v_math_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_math_elim(lean_object* v_i_220_, lean_object* v_motive__1_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_math_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_222_, v_math_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_linebreak_elim___redArg(lean_object* v_t_226_, lean_object* v_linebreak_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_226_, v_linebreak_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_linebreak_elim(lean_object* v_i_229_, lean_object* v_motive__1_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_linebreak_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_231_, v_linebreak_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_link_elim___redArg(lean_object* v_t_235_, lean_object* v_link_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_235_, v_link_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_link_elim(lean_object* v_i_238_, lean_object* v_motive__1_239_, lean_object* v_t_240_, lean_object* v_h_241_, lean_object* v_link_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_240_, v_link_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_footnote_elim___redArg(lean_object* v_t_244_, lean_object* v_footnote_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_244_, v_footnote_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_footnote_elim(lean_object* v_i_247_, lean_object* v_motive__1_248_, lean_object* v_t_249_, lean_object* v_h_250_, lean_object* v_footnote_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_249_, v_footnote_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_image_elim___redArg(lean_object* v_t_253_, lean_object* v_image_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_253_, v_image_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_image_elim(lean_object* v_i_256_, lean_object* v_motive__1_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_image_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_258_, v_image_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_concat_elim___redArg(lean_object* v_t_262_, lean_object* v_concat_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_262_, v_concat_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_concat_elim(lean_object* v_i_265_, lean_object* v_motive__1_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_concat_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_267_, v_concat_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_other_elim___redArg(lean_object* v_t_271_, lean_object* v_other_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_271_, v_other_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_other_elim(lean_object* v_i_274_, lean_object* v_motive__1_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_other_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_276_, v_other_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline_beq___redArg___boxed(lean_object* v_inst_280_, lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_280_, v_x_281_, v_x_282_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqInline_beq___redArg(lean_object* v_inst_285_, lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v_decide_290_; 
v___x_288_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_286_);
v___x_289_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_287_);
v_decide_290_ = lean_nat_dec_eq(v___x_288_, v___x_289_);
lean_dec(v___x_289_);
lean_dec(v___x_288_);
if (v_decide_290_ == 0)
{
lean_dec_ref(v_x_287_);
lean_dec_ref(v_x_286_);
lean_dec_ref(v_inst_285_);
return v_decide_290_;
}
else
{
lean_object* v___x_291_; lean_object* v_content_293_; lean_object* v_content_x27_294_; 
lean_inc_ref(v_inst_285_);
v___x_291_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___redArg___boxed), 3, 1);
lean_closure_set(v___x_291_, 0, v_inst_285_);
switch(lean_obj_tag(v_x_286_))
{
case 1:
{
lean_object* v_content_299_; lean_object* v_content_300_; 
lean_dec_ref(v_inst_285_);
v_content_299_ = lean_ctor_get(v_x_286_, 0);
lean_inc_ref(v_content_299_);
lean_dec_ref_known(v_x_286_, 1);
v_content_300_ = lean_ctor_get(v_x_287_, 0);
lean_inc_ref(v_content_300_);
lean_dec_ref(v_x_287_);
v_content_293_ = v_content_299_;
v_content_x27_294_ = v_content_300_;
goto v___jp_292_;
}
case 2:
{
lean_object* v_content_301_; lean_object* v_content_302_; 
lean_dec_ref(v_inst_285_);
v_content_301_ = lean_ctor_get(v_x_286_, 0);
lean_inc_ref(v_content_301_);
lean_dec_ref_known(v_x_286_, 1);
v_content_302_ = lean_ctor_get(v_x_287_, 0);
lean_inc_ref(v_content_302_);
lean_dec_ref(v_x_287_);
v_content_293_ = v_content_301_;
v_content_x27_294_ = v_content_302_;
goto v___jp_292_;
}
case 4:
{
uint8_t v_mode_303_; lean_object* v_string_304_; uint8_t v_mode_305_; lean_object* v_string_306_; uint8_t v___x_307_; 
lean_dec_ref(v___x_291_);
lean_dec_ref(v_inst_285_);
v_mode_303_ = lean_ctor_get_uint8(v_x_286_, sizeof(void*)*1);
v_string_304_ = lean_ctor_get(v_x_286_, 0);
lean_inc_ref(v_string_304_);
lean_dec_ref_known(v_x_286_, 1);
v_mode_305_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*1);
v_string_306_ = lean_ctor_get(v_x_287_, 0);
lean_inc_ref(v_string_306_);
lean_dec_ref(v_x_287_);
v___x_307_ = l_Lean_Doc_instBEqMathMode_beq(v_mode_303_, v_mode_305_);
if (v___x_307_ == 0)
{
lean_dec_ref(v_string_306_);
lean_dec_ref(v_string_304_);
return v___x_307_;
}
else
{
uint8_t v___x_308_; 
v___x_308_ = lean_string_dec_eq(v_string_304_, v_string_306_);
lean_dec_ref(v_string_306_);
lean_dec_ref(v_string_304_);
return v___x_308_;
}
}
case 6:
{
lean_object* v_content_309_; lean_object* v_url_310_; lean_object* v_content_311_; lean_object* v_url_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
lean_dec_ref(v_inst_285_);
v_content_309_ = lean_ctor_get(v_x_286_, 0);
lean_inc_ref(v_content_309_);
v_url_310_ = lean_ctor_get(v_x_286_, 1);
lean_inc_ref(v_url_310_);
lean_dec_ref_known(v_x_286_, 2);
v_content_311_ = lean_ctor_get(v_x_287_, 0);
lean_inc_ref(v_content_311_);
v_url_312_ = lean_ctor_get(v_x_287_, 1);
lean_inc_ref(v_url_312_);
lean_dec_ref(v_x_287_);
v___x_313_ = lean_array_get_size(v_content_309_);
v___x_314_ = lean_array_get_size(v_content_311_);
v___x_315_ = lean_nat_dec_eq(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_dec_ref(v_url_312_);
lean_dec_ref(v_content_311_);
lean_dec_ref(v_url_310_);
lean_dec_ref(v_content_309_);
lean_dec_ref(v___x_291_);
return v___x_315_;
}
else
{
uint8_t v___x_316_; 
v___x_316_ = l_Array_isEqvAux___redArg(v_content_309_, v_content_311_, v___x_291_, v___x_313_);
lean_dec_ref(v_content_311_);
lean_dec_ref(v_content_309_);
if (v___x_316_ == 0)
{
lean_dec_ref(v_url_312_);
lean_dec_ref(v_url_310_);
return v___x_316_;
}
else
{
uint8_t v___x_317_; 
v___x_317_ = lean_string_dec_eq(v_url_310_, v_url_312_);
lean_dec_ref(v_url_312_);
lean_dec_ref(v_url_310_);
return v___x_317_;
}
}
}
case 7:
{
lean_object* v_name_318_; lean_object* v_content_319_; lean_object* v_name_320_; lean_object* v_content_321_; uint8_t v___x_322_; 
lean_dec_ref(v_inst_285_);
v_name_318_ = lean_ctor_get(v_x_286_, 0);
lean_inc_ref(v_name_318_);
v_content_319_ = lean_ctor_get(v_x_286_, 1);
lean_inc_ref(v_content_319_);
lean_dec_ref_known(v_x_286_, 2);
v_name_320_ = lean_ctor_get(v_x_287_, 0);
lean_inc_ref(v_name_320_);
v_content_321_ = lean_ctor_get(v_x_287_, 1);
lean_inc_ref(v_content_321_);
lean_dec_ref(v_x_287_);
v___x_322_ = lean_string_dec_eq(v_name_318_, v_name_320_);
lean_dec_ref(v_name_320_);
lean_dec_ref(v_name_318_);
if (v___x_322_ == 0)
{
lean_dec_ref(v_content_321_);
lean_dec_ref(v_content_319_);
lean_dec_ref(v___x_291_);
return v___x_322_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_323_ = lean_array_get_size(v_content_319_);
v___x_324_ = lean_array_get_size(v_content_321_);
v___x_325_ = lean_nat_dec_eq(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_dec_ref(v_content_321_);
lean_dec_ref(v_content_319_);
lean_dec_ref(v___x_291_);
return v___x_325_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = l_Array_isEqvAux___redArg(v_content_319_, v_content_321_, v___x_291_, v___x_323_);
lean_dec_ref(v_content_321_);
lean_dec_ref(v_content_319_);
return v___x_326_;
}
}
}
case 8:
{
lean_object* v_alt_327_; lean_object* v_url_328_; lean_object* v_alt_329_; lean_object* v_url_330_; uint8_t v___x_331_; 
lean_dec_ref(v___x_291_);
lean_dec_ref(v_inst_285_);
v_alt_327_ = lean_ctor_get(v_x_286_, 0);
lean_inc_ref(v_alt_327_);
v_url_328_ = lean_ctor_get(v_x_286_, 1);
lean_inc_ref(v_url_328_);
lean_dec_ref_known(v_x_286_, 2);
v_alt_329_ = lean_ctor_get(v_x_287_, 0);
lean_inc_ref(v_alt_329_);
v_url_330_ = lean_ctor_get(v_x_287_, 1);
lean_inc_ref(v_url_330_);
lean_dec_ref(v_x_287_);
v___x_331_ = lean_string_dec_eq(v_alt_327_, v_alt_329_);
lean_dec_ref(v_alt_329_);
lean_dec_ref(v_alt_327_);
if (v___x_331_ == 0)
{
lean_dec_ref(v_url_330_);
lean_dec_ref(v_url_328_);
return v___x_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = lean_string_dec_eq(v_url_328_, v_url_330_);
lean_dec_ref(v_url_330_);
lean_dec_ref(v_url_328_);
return v___x_332_;
}
}
case 9:
{
lean_object* v_content_333_; lean_object* v_content_334_; 
lean_dec_ref(v_inst_285_);
v_content_333_ = lean_ctor_get(v_x_286_, 0);
lean_inc_ref(v_content_333_);
lean_dec_ref_known(v_x_286_, 1);
v_content_334_ = lean_ctor_get(v_x_287_, 0);
lean_inc_ref(v_content_334_);
lean_dec_ref(v_x_287_);
v_content_293_ = v_content_333_;
v_content_x27_294_ = v_content_334_;
goto v___jp_292_;
}
case 10:
{
lean_object* v_container_335_; lean_object* v_content_336_; lean_object* v_container_337_; lean_object* v_content_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_container_335_ = lean_ctor_get(v_x_286_, 0);
lean_inc(v_container_335_);
v_content_336_ = lean_ctor_get(v_x_286_, 1);
lean_inc_ref(v_content_336_);
lean_dec_ref_known(v_x_286_, 2);
v_container_337_ = lean_ctor_get(v_x_287_, 0);
lean_inc(v_container_337_);
v_content_338_ = lean_ctor_get(v_x_287_, 1);
lean_inc_ref(v_content_338_);
lean_dec_ref(v_x_287_);
v___x_339_ = lean_apply_2(v_inst_285_, v_container_335_, v_container_337_);
v___x_340_ = lean_unbox(v___x_339_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
lean_dec_ref(v_content_338_);
lean_dec_ref(v_content_336_);
lean_dec_ref(v___x_291_);
v___x_341_ = lean_unbox(v___x_339_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = lean_array_get_size(v_content_336_);
v___x_343_ = lean_array_get_size(v_content_338_);
v___x_344_ = lean_nat_dec_eq(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_dec_ref(v_content_338_);
lean_dec_ref(v_content_336_);
lean_dec_ref(v___x_291_);
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = l_Array_isEqvAux___redArg(v_content_336_, v_content_338_, v___x_291_, v___x_342_);
lean_dec_ref(v_content_338_);
lean_dec_ref(v_content_336_);
return v___x_345_;
}
}
}
default: 
{
lean_object* v_string_346_; lean_object* v_string_347_; uint8_t v___x_348_; 
lean_dec_ref(v___x_291_);
lean_dec_ref(v_inst_285_);
v_string_346_ = lean_ctor_get(v_x_286_, 0);
lean_inc_ref(v_string_346_);
lean_dec_ref(v_x_286_);
v_string_347_ = lean_ctor_get(v_x_287_, 0);
lean_inc_ref(v_string_347_);
lean_dec_ref(v_x_287_);
v___x_348_ = lean_string_dec_eq(v_string_346_, v_string_347_);
lean_dec_ref(v_string_347_);
lean_dec_ref(v_string_346_);
return v___x_348_;
}
}
v___jp_292_:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_array_get_size(v_content_293_);
v___x_296_ = lean_array_get_size(v_content_x27_294_);
v___x_297_ = lean_nat_dec_eq(v___x_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_dec_ref(v_content_x27_294_);
lean_dec_ref(v_content_293_);
lean_dec_ref(v___x_291_);
return v___x_297_;
}
else
{
uint8_t v___x_298_; 
v___x_298_ = l_Array_isEqvAux___redArg(v_content_293_, v_content_x27_294_, v___x_291_, v___x_295_);
lean_dec_ref(v_content_x27_294_);
lean_dec_ref(v_content_293_);
return v___x_298_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqInline_beq(lean_object* v_i_349_, lean_object* v_inst_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
uint8_t v___x_353_; 
v___x_353_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_350_, v_x_351_, v_x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline_beq___boxed(lean_object* v_i_354_, lean_object* v_inst_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Lean_Doc_instBEqInline_beq(v_i_354_, v_inst_355_, v_x_356_, v_x_357_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline___redArg(lean_object* v_inst_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_361_, 0, lean_box(0));
lean_closure_set(v___x_361_, 1, v_inst_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline(lean_object* v_i_362_, lean_object* v_inst_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_364_, 0, lean_box(0));
lean_closure_set(v___x_364_, 1, v_inst_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___redArg___boxed(lean_object* v_inst_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_365_, v_x_366_, v_x_367_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord___redArg(lean_object* v_inst_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
lean_object* v_string_374_; lean_object* v_string_x27_375_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_377_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_371_);
v___x_378_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_372_);
v___x_379_ = lean_nat_dec_lt(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = lean_nat_dec_eq(v___x_377_, v___x_378_);
lean_dec(v___x_378_);
lean_dec(v___x_377_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; 
lean_dec_ref(v_x_372_);
lean_dec_ref(v_x_371_);
lean_dec_ref(v_inst_370_);
v___x_381_ = 2;
return v___x_381_;
}
else
{
lean_object* v___x_382_; lean_object* v_content_384_; lean_object* v_content_x27_385_; 
lean_inc_ref(v_inst_370_);
v___x_382_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___redArg___boxed), 3, 1);
lean_closure_set(v___x_382_, 0, v_inst_370_);
switch(lean_obj_tag(v_x_371_))
{
case 1:
{
lean_object* v_content_387_; lean_object* v_content_388_; 
lean_dec_ref(v_inst_370_);
v_content_387_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_387_);
lean_dec_ref_known(v_x_371_, 1);
v_content_388_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_388_);
lean_dec_ref(v_x_372_);
v_content_384_ = v_content_387_;
v_content_x27_385_ = v_content_388_;
goto v___jp_383_;
}
case 2:
{
lean_object* v_content_389_; lean_object* v_content_390_; 
lean_dec_ref(v_inst_370_);
v_content_389_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_389_);
lean_dec_ref_known(v_x_371_, 1);
v_content_390_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_390_);
lean_dec_ref(v_x_372_);
v_content_384_ = v_content_389_;
v_content_x27_385_ = v_content_390_;
goto v___jp_383_;
}
case 4:
{
uint8_t v_mode_391_; lean_object* v_string_392_; uint8_t v_mode_393_; lean_object* v_string_394_; uint8_t v___x_395_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_inst_370_);
v_mode_391_ = lean_ctor_get_uint8(v_x_371_, sizeof(void*)*1);
v_string_392_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_string_392_);
lean_dec_ref_known(v_x_371_, 1);
v_mode_393_ = lean_ctor_get_uint8(v_x_372_, sizeof(void*)*1);
v_string_394_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_string_394_);
lean_dec_ref(v_x_372_);
v___x_395_ = l_Lean_Doc_instOrdMathMode_ord(v_mode_391_, v_mode_393_);
if (v___x_395_ == 1)
{
uint8_t v___x_396_; 
v___x_396_ = lean_string_compare(v_string_392_, v_string_394_);
lean_dec_ref(v_string_394_);
lean_dec_ref(v_string_392_);
if (v___x_396_ == 1)
{
return v___x_396_;
}
else
{
return v___x_396_;
}
}
else
{
lean_dec_ref(v_string_394_);
lean_dec_ref(v_string_392_);
return v___x_395_;
}
}
case 6:
{
lean_object* v_content_397_; lean_object* v_url_398_; lean_object* v_content_399_; lean_object* v_url_400_; uint8_t v___x_401_; 
lean_dec_ref(v_inst_370_);
v_content_397_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_397_);
v_url_398_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_url_398_);
lean_dec_ref_known(v_x_371_, 2);
v_content_399_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_399_);
v_url_400_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_url_400_);
lean_dec_ref(v_x_372_);
v___x_401_ = l_Array_compareLex___redArg(v___x_382_, v_content_397_, v_content_399_);
lean_dec_ref(v_content_399_);
lean_dec_ref(v_content_397_);
if (v___x_401_ == 1)
{
uint8_t v___x_402_; 
v___x_402_ = lean_string_compare(v_url_398_, v_url_400_);
lean_dec_ref(v_url_400_);
lean_dec_ref(v_url_398_);
if (v___x_402_ == 1)
{
return v___x_402_;
}
else
{
return v___x_402_;
}
}
else
{
lean_dec_ref(v_url_400_);
lean_dec_ref(v_url_398_);
return v___x_401_;
}
}
case 7:
{
lean_object* v_name_403_; lean_object* v_content_404_; lean_object* v_name_405_; lean_object* v_content_406_; uint8_t v___x_407_; 
lean_dec_ref(v_inst_370_);
v_name_403_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_name_403_);
v_content_404_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_content_404_);
lean_dec_ref_known(v_x_371_, 2);
v_name_405_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_name_405_);
v_content_406_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_content_406_);
lean_dec_ref(v_x_372_);
v___x_407_ = lean_string_compare(v_name_403_, v_name_405_);
lean_dec_ref(v_name_405_);
lean_dec_ref(v_name_403_);
if (v___x_407_ == 1)
{
uint8_t v___x_408_; 
v___x_408_ = l_Array_compareLex___redArg(v___x_382_, v_content_404_, v_content_406_);
lean_dec_ref(v_content_406_);
lean_dec_ref(v_content_404_);
if (v___x_408_ == 1)
{
return v___x_408_;
}
else
{
return v___x_408_;
}
}
else
{
lean_dec_ref(v_content_406_);
lean_dec_ref(v_content_404_);
lean_dec_ref(v___x_382_);
return v___x_407_;
}
}
case 8:
{
lean_object* v_alt_409_; lean_object* v_url_410_; lean_object* v_alt_411_; lean_object* v_url_412_; uint8_t v___x_413_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_inst_370_);
v_alt_409_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_alt_409_);
v_url_410_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_url_410_);
lean_dec_ref_known(v_x_371_, 2);
v_alt_411_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_alt_411_);
v_url_412_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_url_412_);
lean_dec_ref(v_x_372_);
v___x_413_ = lean_string_compare(v_alt_409_, v_alt_411_);
lean_dec_ref(v_alt_411_);
lean_dec_ref(v_alt_409_);
if (v___x_413_ == 1)
{
uint8_t v___x_414_; 
v___x_414_ = lean_string_compare(v_url_410_, v_url_412_);
lean_dec_ref(v_url_412_);
lean_dec_ref(v_url_410_);
if (v___x_414_ == 1)
{
return v___x_414_;
}
else
{
return v___x_414_;
}
}
else
{
lean_dec_ref(v_url_412_);
lean_dec_ref(v_url_410_);
return v___x_413_;
}
}
case 9:
{
lean_object* v_content_415_; lean_object* v_content_416_; 
lean_dec_ref(v_inst_370_);
v_content_415_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_415_);
lean_dec_ref_known(v_x_371_, 1);
v_content_416_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_416_);
lean_dec_ref(v_x_372_);
v_content_384_ = v_content_415_;
v_content_x27_385_ = v_content_416_;
goto v___jp_383_;
}
case 10:
{
lean_object* v_container_417_; lean_object* v_content_418_; lean_object* v_container_419_; lean_object* v_content_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_container_417_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_container_417_);
v_content_418_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_content_418_);
lean_dec_ref_known(v_x_371_, 2);
v_container_419_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_container_419_);
v_content_420_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_content_420_);
lean_dec_ref(v_x_372_);
v___x_421_ = lean_apply_2(v_inst_370_, v_container_417_, v_container_419_);
v___x_422_ = lean_unbox(v___x_421_);
if (v___x_422_ == 1)
{
uint8_t v___x_423_; 
v___x_423_ = l_Array_compareLex___redArg(v___x_382_, v_content_418_, v_content_420_);
lean_dec_ref(v_content_420_);
lean_dec_ref(v_content_418_);
if (v___x_423_ == 1)
{
return v___x_423_;
}
else
{
return v___x_423_;
}
}
else
{
uint8_t v___x_424_; 
lean_dec_ref(v_content_420_);
lean_dec_ref(v_content_418_);
lean_dec_ref(v___x_382_);
v___x_424_ = lean_unbox(v___x_421_);
return v___x_424_;
}
}
default: 
{
lean_object* v_string_425_; lean_object* v_string_426_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_inst_370_);
v_string_425_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_string_425_);
lean_dec_ref(v_x_371_);
v_string_426_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_string_426_);
lean_dec_ref(v_x_372_);
v_string_374_ = v_string_425_;
v_string_x27_375_ = v_string_426_;
goto v___jp_373_;
}
}
v___jp_383_:
{
uint8_t v___x_386_; 
v___x_386_ = l_Array_compareLex___redArg(v___x_382_, v_content_384_, v_content_x27_385_);
lean_dec_ref(v_content_x27_385_);
lean_dec_ref(v_content_384_);
if (v___x_386_ == 1)
{
return v___x_386_;
}
else
{
return v___x_386_;
}
}
}
}
else
{
uint8_t v___x_427_; 
lean_dec(v___x_378_);
lean_dec(v___x_377_);
lean_dec_ref(v_x_372_);
lean_dec_ref(v_x_371_);
lean_dec_ref(v_inst_370_);
v___x_427_ = 0;
return v___x_427_;
}
v___jp_373_:
{
uint8_t v___x_376_; 
v___x_376_ = lean_string_compare(v_string_374_, v_string_x27_375_);
lean_dec_ref(v_string_x27_375_);
lean_dec_ref(v_string_374_);
if (v___x_376_ == 1)
{
return v___x_376_;
}
else
{
return v___x_376_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord(lean_object* v_i_428_, lean_object* v_inst_429_, lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_429_, v_x_430_, v_x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___boxed(lean_object* v_i_433_, lean_object* v_inst_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Lean_Doc_instOrdInline_ord(v_i_433_, v_inst_434_, v_x_435_, v_x_436_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline___redArg(lean_object* v_inst_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_440_, 0, lean_box(0));
lean_closure_set(v___x_440_, 1, v_inst_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline(lean_object* v_i_441_, lean_object* v_inst_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_443_, 0, lean_box(0));
lean_closure_set(v___x_443_, 1, v_inst_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg___boxed(lean_object* v_inst_510_, lean_object* v_x_511_, lean_object* v_prec_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_510_, v_x_511_, v_prec_512_);
lean_dec(v_prec_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg(lean_object* v_inst_514_, lean_object* v_x_515_, lean_object* v_prec_516_){
_start:
{
lean_object* v_localinst_517_; 
lean_inc_ref(v_inst_514_);
v_localinst_517_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_517_, 0, v_inst_514_);
switch(lean_obj_tag(v_x_515_))
{
case 0:
{
lean_object* v_string_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v_localinst_517_);
lean_dec_ref(v_inst_514_);
v_string_518_ = lean_ctor_get(v_x_515_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_538_ == 0)
{
v___x_520_ = v_x_515_;
v_isShared_521_ = v_isSharedCheck_538_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_string_518_);
lean_dec(v_x_515_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_538_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___y_523_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1024u);
v___x_535_ = lean_nat_dec_le(v___x_534_, v_prec_516_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_523_ = v___x_536_;
goto v___jp_522_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_523_ = v___x_537_;
goto v___jp_522_;
}
v___jp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_524_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__2));
v___x_525_ = l_String_quote(v_string_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 3);
lean_ctor_set(v___x_520_, 0, v___x_525_);
v___x_527_ = v___x_520_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_533_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_524_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
lean_inc(v___y_523_);
v___x_529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_529_, 0, v___y_523_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = 0;
v___x_531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*1, v___x_530_);
v___x_532_ = l_Repr_addAppParen(v___x_531_, v_prec_516_);
return v___x_532_;
}
}
}
}
case 1:
{
lean_object* v_content_539_; lean_object* v___y_541_; lean_object* v___x_549_; uint8_t v___x_550_; 
lean_dec_ref(v_inst_514_);
v_content_539_ = lean_ctor_get(v_x_515_, 0);
lean_inc_ref(v_content_539_);
lean_dec_ref_known(v_x_515_, 1);
v___x_549_ = lean_unsigned_to_nat(1024u);
v___x_550_ = lean_nat_dec_le(v___x_549_, v_prec_516_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_541_ = v___x_551_;
goto v___jp_540_;
}
else
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_541_ = v___x_552_;
goto v___jp_540_;
}
v___jp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_542_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__5));
v___x_543_ = l_Array_repr___redArg(v_localinst_517_, v_content_539_);
v___x_544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
lean_inc(v___y_541_);
v___x_545_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_545_, 0, v___y_541_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = 0;
v___x_547_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*1, v___x_546_);
v___x_548_ = l_Repr_addAppParen(v___x_547_, v_prec_516_);
return v___x_548_;
}
}
case 2:
{
lean_object* v_content_553_; lean_object* v___y_555_; lean_object* v___x_563_; uint8_t v___x_564_; 
lean_dec_ref(v_inst_514_);
v_content_553_ = lean_ctor_get(v_x_515_, 0);
lean_inc_ref(v_content_553_);
lean_dec_ref_known(v_x_515_, 1);
v___x_563_ = lean_unsigned_to_nat(1024u);
v___x_564_ = lean_nat_dec_le(v___x_563_, v_prec_516_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_555_ = v___x_565_;
goto v___jp_554_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_555_ = v___x_566_;
goto v___jp_554_;
}
v___jp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_556_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__8));
v___x_557_ = l_Array_repr___redArg(v_localinst_517_, v_content_553_);
v___x_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
lean_inc(v___y_555_);
v___x_559_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_559_, 0, v___y_555_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = 0;
v___x_561_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*1, v___x_560_);
v___x_562_ = l_Repr_addAppParen(v___x_561_, v_prec_516_);
return v___x_562_;
}
}
case 3:
{
lean_object* v_string_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v_localinst_517_);
lean_dec_ref(v_inst_514_);
v_string_567_ = lean_ctor_get(v_x_515_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_587_ == 0)
{
v___x_569_ = v_x_515_;
v_isShared_570_ = v_isSharedCheck_587_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_string_567_);
lean_dec(v_x_515_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_587_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___y_572_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(1024u);
v___x_584_ = lean_nat_dec_le(v___x_583_, v_prec_516_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_572_ = v___x_585_;
goto v___jp_571_;
}
else
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_572_ = v___x_586_;
goto v___jp_571_;
}
v___jp_571_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__11));
v___x_574_ = l_String_quote(v_string_567_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_574_);
v___x_576_ = v___x_569_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_582_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_573_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
lean_inc(v___y_572_);
v___x_578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_578_, 0, v___y_572_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = 0;
v___x_580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*1, v___x_579_);
v___x_581_ = l_Repr_addAppParen(v___x_580_, v_prec_516_);
return v___x_581_;
}
}
}
}
case 4:
{
uint8_t v_mode_588_; lean_object* v_string_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_localinst_517_);
lean_dec_ref(v_inst_514_);
v_mode_588_ = lean_ctor_get_uint8(v_x_515_, sizeof(void*)*1);
v_string_589_ = lean_ctor_get(v_x_515_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_614_ == 0)
{
v___x_591_ = v_x_515_;
v_isShared_592_ = v_isSharedCheck_614_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_string_589_);
lean_dec(v_x_515_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_614_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___y_594_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(1024u);
v___x_611_ = lean_nat_dec_le(v___x_610_, v_prec_516_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
v___x_612_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_594_ = v___x_612_;
goto v___jp_593_;
}
else
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_594_ = v___x_613_;
goto v___jp_593_;
}
v___jp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_607_; 
v___x_595_ = lean_box(1);
v___x_596_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__14));
v___x_597_ = lean_unsigned_to_nat(1024u);
v___x_598_ = l_Lean_Doc_instReprMathMode_repr(v_mode_588_, v___x_597_);
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_596_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_595_);
v___x_601_ = l_String_quote(v_string_589_);
v___x_602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_600_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
lean_inc(v___y_594_);
v___x_604_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_604_, 0, v___y_594_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = 0;
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 6);
lean_ctor_set(v___x_591_, 0, v___x_604_);
v___x_607_ = v___x_591_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_604_);
v___x_607_ = v_reuseFailAlloc_609_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; 
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*1, v___x_605_);
v___x_608_ = l_Repr_addAppParen(v___x_607_, v_prec_516_);
return v___x_608_;
}
}
}
}
case 5:
{
lean_object* v_string_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_localinst_517_);
lean_dec_ref(v_inst_514_);
v_string_615_ = lean_ctor_get(v_x_515_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_635_ == 0)
{
v___x_617_ = v_x_515_;
v_isShared_618_ = v_isSharedCheck_635_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_string_615_);
lean_dec(v_x_515_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_635_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___y_620_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(1024u);
v___x_632_ = lean_nat_dec_le(v___x_631_, v_prec_516_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_620_ = v___x_633_;
goto v___jp_619_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_620_ = v___x_634_;
goto v___jp_619_;
}
v___jp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_621_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__17));
v___x_622_ = l_String_quote(v_string_615_);
if (v_isShared_618_ == 0)
{
lean_ctor_set_tag(v___x_617_, 3);
lean_ctor_set(v___x_617_, 0, v___x_622_);
v___x_624_ = v___x_617_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_630_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_621_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
lean_inc(v___y_620_);
v___x_626_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_626_, 0, v___y_620_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = 0;
v___x_628_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*1, v___x_627_);
v___x_629_ = l_Repr_addAppParen(v___x_628_, v_prec_516_);
return v___x_629_;
}
}
}
}
case 6:
{
lean_object* v_content_636_; lean_object* v_url_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_inst_514_);
v_content_636_ = lean_ctor_get(v_x_515_, 0);
v_url_637_ = lean_ctor_get(v_x_515_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_661_ == 0)
{
v___x_639_ = v_x_515_;
v_isShared_640_ = v_isSharedCheck_661_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_url_637_);
lean_inc(v_content_636_);
lean_dec(v_x_515_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_661_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___y_642_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(1024u);
v___x_658_ = lean_nat_dec_le(v___x_657_, v_prec_516_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_642_ = v___x_659_;
goto v___jp_641_;
}
else
{
lean_object* v___x_660_; 
v___x_660_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_642_ = v___x_660_;
goto v___jp_641_;
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_643_ = lean_box(1);
v___x_644_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__20));
v___x_645_ = l_Array_repr___redArg(v_localinst_517_, v_content_636_);
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 5);
lean_ctor_set(v___x_639_, 1, v___x_645_);
lean_ctor_set(v___x_639_, 0, v___x_644_);
v___x_647_ = v___x_639_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_645_);
v___x_647_ = v_reuseFailAlloc_656_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_643_);
v___x_649_ = l_String_quote(v_url_637_);
v___x_650_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_648_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
lean_inc(v___y_642_);
v___x_652_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_652_, 0, v___y_642_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = 0;
v___x_654_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*1, v___x_653_);
v___x_655_ = l_Repr_addAppParen(v___x_654_, v_prec_516_);
return v___x_655_;
}
}
}
}
case 7:
{
lean_object* v_name_662_; lean_object* v_content_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v_inst_514_);
v_name_662_ = lean_ctor_get(v_x_515_, 0);
v_content_663_ = lean_ctor_get(v_x_515_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_687_ == 0)
{
v___x_665_ = v_x_515_;
v_isShared_666_ = v_isSharedCheck_687_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_content_663_);
lean_inc(v_name_662_);
lean_dec(v_x_515_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_687_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___y_668_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(1024u);
v___x_684_ = lean_nat_dec_le(v___x_683_, v_prec_516_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_668_ = v___x_685_;
goto v___jp_667_;
}
else
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_668_ = v___x_686_;
goto v___jp_667_;
}
v___jp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_669_ = lean_box(1);
v___x_670_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__23));
v___x_671_ = l_String_quote(v_name_662_);
v___x_672_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
if (v_isShared_666_ == 0)
{
lean_ctor_set_tag(v___x_665_, 5);
lean_ctor_set(v___x_665_, 1, v___x_672_);
lean_ctor_set(v___x_665_, 0, v___x_670_);
v___x_674_ = v___x_665_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_682_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_669_);
v___x_676_ = l_Array_repr___redArg(v_localinst_517_, v_content_663_);
v___x_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
lean_inc(v___y_668_);
v___x_678_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_678_, 0, v___y_668_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = 0;
v___x_680_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*1, v___x_679_);
v___x_681_ = l_Repr_addAppParen(v___x_680_, v_prec_516_);
return v___x_681_;
}
}
}
}
case 8:
{
lean_object* v_alt_688_; lean_object* v_url_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v_localinst_517_);
lean_dec_ref(v_inst_514_);
v_alt_688_ = lean_ctor_get(v_x_515_, 0);
v_url_689_ = lean_ctor_get(v_x_515_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_714_ == 0)
{
v___x_691_ = v_x_515_;
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_url_689_);
lean_inc(v_alt_688_);
lean_dec(v_x_515_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___y_694_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(1024u);
v___x_711_ = lean_nat_dec_le(v___x_710_, v_prec_516_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
v___x_712_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_694_ = v___x_712_;
goto v___jp_693_;
}
else
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_694_ = v___x_713_;
goto v___jp_693_;
}
v___jp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_695_ = lean_box(1);
v___x_696_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__26));
v___x_697_ = l_String_quote(v_alt_688_);
v___x_698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 5);
lean_ctor_set(v___x_691_, 1, v___x_698_);
lean_ctor_set(v___x_691_, 0, v___x_696_);
v___x_700_ = v___x_691_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_709_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_695_);
v___x_702_ = l_String_quote(v_url_689_);
v___x_703_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_701_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
lean_inc(v___y_694_);
v___x_705_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_705_, 0, v___y_694_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = 0;
v___x_707_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*1, v___x_706_);
v___x_708_ = l_Repr_addAppParen(v___x_707_, v_prec_516_);
return v___x_708_;
}
}
}
}
case 9:
{
lean_object* v_content_715_; lean_object* v___y_717_; lean_object* v___x_725_; uint8_t v___x_726_; 
lean_dec_ref(v_inst_514_);
v_content_715_ = lean_ctor_get(v_x_515_, 0);
lean_inc_ref(v_content_715_);
lean_dec_ref_known(v_x_515_, 1);
v___x_725_ = lean_unsigned_to_nat(1024u);
v___x_726_ = lean_nat_dec_le(v___x_725_, v_prec_516_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
v___x_727_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_717_ = v___x_727_;
goto v___jp_716_;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_717_ = v___x_728_;
goto v___jp_716_;
}
v___jp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_718_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__29));
v___x_719_ = l_Array_repr___redArg(v_localinst_517_, v_content_715_);
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
lean_inc(v___y_717_);
v___x_721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_721_, 0, v___y_717_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = 0;
v___x_723_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*1, v___x_722_);
v___x_724_ = l_Repr_addAppParen(v___x_723_, v_prec_516_);
return v___x_724_;
}
}
default: 
{
lean_object* v_container_729_; lean_object* v_content_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_754_; 
v_container_729_ = lean_ctor_get(v_x_515_, 0);
v_content_730_ = lean_ctor_get(v_x_515_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_754_ == 0)
{
v___x_732_ = v_x_515_;
v_isShared_733_ = v_isSharedCheck_754_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_content_730_);
lean_inc(v_container_729_);
lean_dec(v_x_515_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_754_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___y_735_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_unsigned_to_nat(1024u);
v___x_751_ = lean_nat_dec_le(v___x_750_, v_prec_516_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_735_ = v___x_752_;
goto v___jp_734_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_735_ = v___x_753_;
goto v___jp_734_;
}
v___jp_734_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_736_ = lean_box(1);
v___x_737_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__32));
v___x_738_ = lean_unsigned_to_nat(1024u);
v___x_739_ = lean_apply_2(v_inst_514_, v_container_729_, v___x_738_);
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 5);
lean_ctor_set(v___x_732_, 1, v___x_739_);
lean_ctor_set(v___x_732_, 0, v___x_737_);
v___x_741_ = v___x_732_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_739_);
v___x_741_ = v_reuseFailAlloc_749_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___x_736_);
v___x_743_ = l_Array_repr___redArg(v_localinst_517_, v_content_730_);
v___x_744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
lean_inc(v___y_735_);
v___x_745_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_745_, 0, v___y_735_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = 0;
v___x_747_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*1, v___x_746_);
v___x_748_ = l_Repr_addAppParen(v___x_747_, v_prec_516_);
return v___x_748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr(lean_object* v_i_755_, lean_object* v_inst_756_, lean_object* v_x_757_, lean_object* v_prec_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_756_, v_x_757_, v_prec_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___boxed(lean_object* v_i_760_, lean_object* v_inst_761_, lean_object* v_x_762_, lean_object* v_prec_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Doc_instReprInline_repr(v_i_760_, v_inst_761_, v_x_762_, v_prec_763_);
lean_dec(v_prec_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline___redArg(lean_object* v_inst_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_766_, 0, lean_box(0));
lean_closure_set(v___x_766_, 1, v_inst_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline(lean_object* v_i_767_, lean_object* v_inst_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_769_, 0, lean_box(0));
lean_closure_set(v___x_769_, 1, v_inst_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg(){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = ((lean_object*)(l_Lean_Doc_instInhabitedInline_default___redArg___closed__1));
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg___boxed(lean_object* v___dummy_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Doc_instInhabitedInline_default___redArg();
return v_res_776_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedInline_default___closed__0(void){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Doc_instInhabitedInline_default___redArg();
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default(lean_object* v_i_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg(){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg___boxed(lean_object* v___dummy_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Doc_instInhabitedInline___redArg();
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline(lean_object* v_a_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg(lean_object* v_x_786_){
_start:
{
lean_inc_ref(v_x_786_);
return v_x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg___boxed(lean_object* v_x_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Doc_Inline_cast___redArg(v_x_787_);
lean_dec_ref(v_x_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast(lean_object* v_i_789_, lean_object* v_i_x27_790_, lean_object* v_inlines__eq_791_, lean_object* v_x_792_){
_start:
{
lean_inc_ref(v_x_792_);
return v_x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___boxed(lean_object* v_i_793_, lean_object* v_i_x27_794_, lean_object* v_inlines__eq_795_, lean_object* v_x_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_Doc_Inline_cast(v_i_793_, v_i_x27_794_, v_inlines__eq_795_, v_x_796_);
lean_dec_ref(v_x_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___lam__0(lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_798_) == 9)
{
lean_object* v_content_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_content_800_ = lean_ctor_get(v_x_798_, 0);
v___x_801_ = lean_array_get_size(v_content_800_);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_nat_dec_eq(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
if (lean_obj_tag(v_x_799_) == 9)
{
lean_object* v_content_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_814_; 
v_content_804_ = lean_ctor_get(v_x_799_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_814_ == 0)
{
v___x_806_ = v_x_799_;
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_content_804_);
lean_dec(v_x_799_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = lean_array_get_size(v_content_804_);
v___x_809_ = lean_nat_dec_eq(v___x_808_, v___x_802_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_812_; 
lean_inc_ref(v_content_800_);
lean_dec_ref_known(v_x_798_, 1);
v___x_810_ = l_Array_append___redArg(v_content_800_, v_content_804_);
lean_dec_ref(v_content_804_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_810_);
v___x_812_ = v___x_806_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
lean_del_object(v___x_806_);
lean_dec_ref(v_content_804_);
return v_x_798_;
}
}
}
else
{
lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_822_; 
lean_inc_ref(v_content_800_);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_x_798_, 0);
lean_dec(v_unused_823_);
v___x_816_ = v_x_798_;
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
else
{
lean_dec(v_x_798_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_array_push(v_content_800_, v_x_799_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_dec_ref_known(v_x_798_, 1);
return v_x_799_;
}
}
else
{
if (lean_obj_tag(v_x_799_) == 9)
{
lean_object* v_content_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_838_; 
v_content_824_ = lean_ctor_get(v_x_799_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_838_ == 0)
{
v___x_826_ = v_x_799_;
v_isShared_827_ = v_isSharedCheck_838_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_content_824_);
lean_dec(v_x_799_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_838_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_828_ = lean_array_get_size(v_content_824_);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_nat_dec_eq(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_mk_empty_array_with_capacity(v___x_831_);
v___x_833_ = lean_array_push(v___x_832_, v_x_798_);
v___x_834_ = l_Array_append___redArg(v___x_833_, v_content_824_);
lean_dec_ref(v_content_824_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_834_);
v___x_836_ = v___x_826_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_del_object(v___x_826_);
lean_dec_ref(v_content_824_);
return v_x_798_;
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_839_ = lean_unsigned_to_nat(2u);
v___x_840_ = lean_mk_empty_array_with_capacity(v___x_839_);
v___x_841_ = lean_array_push(v___x_840_, v_x_798_);
v___x_842_ = lean_array_push(v___x_841_, v_x_799_);
v___x_843_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg(){
_start:
{
lean_object* v___f_846_; 
v___f_846_ = ((lean_object*)(l_Lean_Doc_instAppendInline___redArg___closed__0));
return v___f_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___boxed(lean_object* v___dummy_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Doc_instAppendInline___redArg();
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline(lean_object* v_i_849_){
_start:
{
lean_object* v___f_850_; 
v___f_850_ = ((lean_object*)(l_Lean_Doc_instAppendInline___redArg___closed__0));
return v___f_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg(){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = ((lean_object*)(l_Lean_Doc_Inline_empty___redArg___closed__1));
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg___boxed(lean_object* v___dummy_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Doc_Inline_empty___redArg();
return v_res_858_;
}
}
static lean_object* _init_l_Lean_Doc_Inline_empty___closed__0(void){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Doc_Inline_empty___redArg();
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty(lean_object* v_i_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = lean_obj_once(&l_Lean_Doc_Inline_empty___closed__0, &l_Lean_Doc_Inline_empty___closed__0_once, _init_l_Lean_Doc_Inline_empty___closed__0);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(12u);
v___x_876_ = lean_nat_to_int(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__0));
v___x_879_ = lean_string_length(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9);
v___x_881_ = lean_nat_to_int(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___redArg(lean_object* v_inst_886_, lean_object* v_x_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_888_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__6));
v___x_889_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_890_ = l_Array_repr___redArg(v_inst_886_, v_x_887_);
v___x_891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = 0;
v___x_893_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*1, v___x_892_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_888_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_896_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_894_);
v___x_898_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_895_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*1, v___x_892_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr(lean_object* v_00_u03b1_902_, lean_object* v_inst_903_, lean_object* v_x_904_, lean_object* v_prec_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Doc_instReprListItem_repr___redArg(v_inst_903_, v_x_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___boxed(lean_object* v_00_u03b1_907_, lean_object* v_inst_908_, lean_object* v_x_909_, lean_object* v_prec_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Doc_instReprListItem_repr(v_00_u03b1_907_, v_inst_908_, v_x_909_, v_prec_910_);
lean_dec(v_prec_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem___redArg(lean_object* v_inst_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_913_, 0, lean_box(0));
lean_closure_set(v___x_913_, 1, v_inst_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem(lean_object* v_00_u03b1_914_, lean_object* v_inst_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_916_, 0, lean_box(0));
lean_closure_set(v___x_916_, 1, v_inst_915_);
return v___x_916_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq___redArg(lean_object* v_inst_917_, lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_array_get_size(v_x_918_);
v___x_921_ = lean_array_get_size(v_x_919_);
v___x_922_ = lean_nat_dec_eq(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_dec_ref(v_inst_917_);
return v___x_922_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = l_Array_isEqvAux___redArg(v_x_918_, v_x_919_, v_inst_917_, v___x_920_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___redArg___boxed(lean_object* v_inst_924_, lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
uint8_t v_res_927_; lean_object* v_r_928_; 
v_res_927_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_924_, v_x_925_, v_x_926_);
lean_dec_ref(v_x_926_);
lean_dec_ref(v_x_925_);
v_r_928_ = lean_box(v_res_927_);
return v_r_928_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq(lean_object* v_00_u03b1_929_, lean_object* v_inst_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_930_, v_x_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___boxed(lean_object* v_00_u03b1_934_, lean_object* v_inst_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
uint8_t v_res_938_; lean_object* v_r_939_; 
v_res_938_ = l_Lean_Doc_instBEqListItem_beq(v_00_u03b1_934_, v_inst_935_, v_x_936_, v_x_937_);
lean_dec_ref(v_x_937_);
lean_dec_ref(v_x_936_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem___redArg(lean_object* v_inst_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_941_, 0, lean_box(0));
lean_closure_set(v___x_941_, 1, v_inst_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem(lean_object* v_00_u03b1_942_, lean_object* v_inst_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_944_, 0, lean_box(0));
lean_closure_set(v___x_944_, 1, v_inst_943_);
return v___x_944_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord___redArg(lean_object* v_inst_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = l_Array_compareLex___redArg(v_inst_945_, v_x_946_, v_x_947_);
if (v___x_948_ == 1)
{
return v___x_948_;
}
else
{
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___redArg___boxed(lean_object* v_inst_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_949_, v_x_950_, v_x_951_);
lean_dec_ref(v_x_951_);
lean_dec_ref(v_x_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord(lean_object* v_00_u03b1_954_, lean_object* v_inst_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
uint8_t v___x_958_; 
v___x_958_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_955_, v_x_956_, v_x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___boxed(lean_object* v_00_u03b1_959_, lean_object* v_inst_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
uint8_t v_res_963_; lean_object* v_r_964_; 
v_res_963_ = l_Lean_Doc_instOrdListItem_ord(v_00_u03b1_959_, v_inst_960_, v_x_961_, v_x_962_);
lean_dec_ref(v_x_962_);
lean_dec_ref(v_x_961_);
v_r_964_ = lean_box(v_res_963_);
return v_r_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem___redArg(lean_object* v_inst_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_966_, 0, lean_box(0));
lean_closure_set(v___x_966_, 1, v_inst_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem(lean_object* v_00_u03b1_967_, lean_object* v_inst_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_969_, 0, lean_box(0));
lean_closure_set(v___x_969_, 1, v_inst_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg(){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l_Lean_Doc_instInhabitedListItem_default___redArg___closed__0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg___boxed(lean_object* v___dummy_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Doc_instInhabitedListItem_default___redArg();
return v_res_975_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedListItem_default___closed__0(void){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Doc_instInhabitedListItem_default___redArg();
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default(lean_object* v_00_u03b1_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem___redArg(){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem___redArg___boxed(lean_object* v___dummy_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Doc_instInhabitedListItem___redArg();
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem(lean_object* v_a_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_unsigned_to_nat(8u);
v___x_995_ = lean_nat_to_int(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___redArg(lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v_term_1005_; lean_object* v_desc_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1038_; 
v_term_1005_ = lean_ctor_get(v_x_1004_, 0);
v_desc_1006_ = lean_ctor_get(v_x_1004_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_x_1004_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1008_ = v_x_1004_;
v_isShared_1009_ = v_isSharedCheck_1038_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_desc_1006_);
lean_inc(v_term_1005_);
lean_dec(v_x_1004_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1038_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1010_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1011_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__3));
v___x_1012_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4);
v___x_1013_ = l_Array_repr___redArg(v_inst_1002_, v_term_1005_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set_tag(v___x_1008_, 4);
lean_ctor_set(v___x_1008_, 1, v___x_1013_);
lean_ctor_set(v___x_1008_, 0, v___x_1012_);
v___x_1015_ = v___x_1008_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1016_ = 0;
v___x_1017_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1011_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_box(1);
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__8));
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1010_);
v___x_1026_ = l_Array_repr___redArg(v_inst_1003_, v_desc_1006_);
v___x_1027_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1012_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set_uint8(v___x_1028_, sizeof(void*)*1, v___x_1016_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1025_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_1031_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_1029_);
v___x_1033_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_1034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1030_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*1, v___x_1016_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr(lean_object* v_00_u03b1_1039_, lean_object* v_00_u03b2_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_x_1043_, lean_object* v_prec_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_Doc_instReprDescItem_repr___redArg(v_inst_1041_, v_inst_1042_, v_x_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___boxed(lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_x_1050_, lean_object* v_prec_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Doc_instReprDescItem_repr(v_00_u03b1_1046_, v_00_u03b2_1047_, v_inst_1048_, v_inst_1049_, v_x_1050_, v_prec_1051_);
lean_dec(v_prec_1051_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem___redArg(lean_object* v_inst_1053_, lean_object* v_inst_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1055_, 0, lean_box(0));
lean_closure_set(v___x_1055_, 1, lean_box(0));
lean_closure_set(v___x_1055_, 2, v_inst_1053_);
lean_closure_set(v___x_1055_, 3, v_inst_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem(lean_object* v_00_u03b1_1056_, lean_object* v_00_u03b2_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1060_, 0, lean_box(0));
lean_closure_set(v___x_1060_, 1, lean_box(0));
lean_closure_set(v___x_1060_, 2, v_inst_1058_);
lean_closure_set(v___x_1060_, 3, v_inst_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq___redArg(lean_object* v_inst_1061_, lean_object* v_inst_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v_term_1065_; lean_object* v_desc_1066_; lean_object* v_term_1067_; lean_object* v_desc_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_term_1065_ = lean_ctor_get(v_x_1063_, 0);
v_desc_1066_ = lean_ctor_get(v_x_1063_, 1);
v_term_1067_ = lean_ctor_get(v_x_1064_, 0);
v_desc_1068_ = lean_ctor_get(v_x_1064_, 1);
v___x_1069_ = lean_array_get_size(v_term_1065_);
v___x_1070_ = lean_array_get_size(v_term_1067_);
v___x_1071_ = lean_nat_dec_eq(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v_inst_1062_);
lean_dec_ref(v_inst_1061_);
return v___x_1071_;
}
else
{
uint8_t v___x_1072_; 
v___x_1072_ = l_Array_isEqvAux___redArg(v_term_1065_, v_term_1067_, v_inst_1061_, v___x_1069_);
if (v___x_1072_ == 0)
{
lean_dec_ref(v_inst_1062_);
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1073_ = lean_array_get_size(v_desc_1066_);
v___x_1074_ = lean_array_get_size(v_desc_1068_);
v___x_1075_ = lean_nat_dec_eq(v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_dec_ref(v_inst_1062_);
return v___x_1075_;
}
else
{
uint8_t v___x_1076_; 
v___x_1076_ = l_Array_isEqvAux___redArg(v_desc_1066_, v_desc_1068_, v_inst_1062_, v___x_1073_);
return v___x_1076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___redArg___boxed(lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_res_1081_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1077_, v_inst_1078_, v_x_1079_, v_x_1080_);
lean_dec_ref(v_x_1080_);
lean_dec_ref(v_x_1079_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq(lean_object* v_00_u03b1_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
uint8_t v___x_1089_; 
v___x_1089_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1085_, v_inst_1086_, v_x_1087_, v_x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___boxed(lean_object* v_00_u03b1_1090_, lean_object* v_00_u03b2_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l_Lean_Doc_instBEqDescItem_beq(v_00_u03b1_1090_, v_00_u03b2_1091_, v_inst_1092_, v_inst_1093_, v_x_1094_, v_x_1095_);
lean_dec_ref(v_x_1095_);
lean_dec_ref(v_x_1094_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem___redArg(lean_object* v_inst_1098_, lean_object* v_inst_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1100_, 0, lean_box(0));
lean_closure_set(v___x_1100_, 1, lean_box(0));
lean_closure_set(v___x_1100_, 2, v_inst_1098_);
lean_closure_set(v___x_1100_, 3, v_inst_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem(lean_object* v_00_u03b1_1101_, lean_object* v_00_u03b2_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1105_, 0, lean_box(0));
lean_closure_set(v___x_1105_, 1, lean_box(0));
lean_closure_set(v___x_1105_, 2, v_inst_1103_);
lean_closure_set(v___x_1105_, 3, v_inst_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord___redArg(lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
lean_object* v_term_1110_; lean_object* v_desc_1111_; lean_object* v_term_1112_; lean_object* v_desc_1113_; uint8_t v___x_1114_; 
v_term_1110_ = lean_ctor_get(v_x_1108_, 0);
v_desc_1111_ = lean_ctor_get(v_x_1108_, 1);
v_term_1112_ = lean_ctor_get(v_x_1109_, 0);
v_desc_1113_ = lean_ctor_get(v_x_1109_, 1);
v___x_1114_ = l_Array_compareLex___redArg(v_inst_1106_, v_term_1110_, v_term_1112_);
if (v___x_1114_ == 1)
{
uint8_t v___x_1115_; 
v___x_1115_ = l_Array_compareLex___redArg(v_inst_1107_, v_desc_1111_, v_desc_1113_);
if (v___x_1115_ == 1)
{
return v___x_1115_;
}
else
{
return v___x_1115_;
}
}
else
{
lean_dec_ref(v_inst_1107_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___redArg___boxed(lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
uint8_t v_res_1120_; lean_object* v_r_1121_; 
v_res_1120_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1116_, v_inst_1117_, v_x_1118_, v_x_1119_);
lean_dec_ref(v_x_1119_);
lean_dec_ref(v_x_1118_);
v_r_1121_ = lean_box(v_res_1120_);
return v_r_1121_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord(lean_object* v_00_u03b1_1122_, lean_object* v_00_u03b2_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
uint8_t v___x_1128_; 
v___x_1128_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1124_, v_inst_1125_, v_x_1126_, v_x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
uint8_t v_res_1135_; lean_object* v_r_1136_; 
v_res_1135_ = l_Lean_Doc_instOrdDescItem_ord(v_00_u03b1_1129_, v_00_u03b2_1130_, v_inst_1131_, v_inst_1132_, v_x_1133_, v_x_1134_);
lean_dec_ref(v_x_1134_);
lean_dec_ref(v_x_1133_);
v_r_1136_ = lean_box(v_res_1135_);
return v_r_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem___redArg(lean_object* v_inst_1137_, lean_object* v_inst_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1139_, 0, lean_box(0));
lean_closure_set(v___x_1139_, 1, lean_box(0));
lean_closure_set(v___x_1139_, 2, v_inst_1137_);
lean_closure_set(v___x_1139_, 3, v_inst_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03b2_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1144_, 0, lean_box(0));
lean_closure_set(v___x_1144_, 1, lean_box(0));
lean_closure_set(v___x_1144_, 2, v_inst_1142_);
lean_closure_set(v___x_1144_, 3, v_inst_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg(){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = ((lean_object*)(l_Lean_Doc_instInhabitedDescItem_default___redArg___closed__0));
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg___boxed(lean_object* v___dummy_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
return v_res_1150_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0(void){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg(){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg___boxed(lean_object* v___dummy_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Doc_instInhabitedDescItem___redArg();
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem(lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg(lean_object* v_x_1162_){
_start:
{
switch(lean_obj_tag(v_x_1162_))
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
case 2:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_unsigned_to_nat(2u);
return v___x_1165_;
}
case 3:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_unsigned_to_nat(3u);
return v___x_1166_;
}
case 4:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_unsigned_to_nat(4u);
return v___x_1167_;
}
case 5:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_unsigned_to_nat(5u);
return v___x_1168_;
}
case 6:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_unsigned_to_nat(6u);
return v___x_1169_;
}
default: 
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_unsigned_to_nat(7u);
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg___boxed(lean_object* v_x_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1171_);
lean_dec_ref(v_x_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx(lean_object* v_i_1173_, lean_object* v_b_1174_, lean_object* v_x_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___boxed(lean_object* v_i_1177_, lean_object* v_b_1178_, lean_object* v_x_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Doc_Block_ctorIdx(v_i_1177_, v_b_1178_, v_x_1179_);
lean_dec_ref(v_x_1179_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___redArg(lean_object* v_t_1181_, lean_object* v_k_1182_){
_start:
{
switch(lean_obj_tag(v_t_1181_))
{
case 3:
{
lean_object* v_start_1183_; lean_object* v_items_1184_; lean_object* v___x_1185_; 
v_start_1183_ = lean_ctor_get(v_t_1181_, 0);
lean_inc(v_start_1183_);
v_items_1184_ = lean_ctor_get(v_t_1181_, 1);
lean_inc_ref(v_items_1184_);
lean_dec_ref_known(v_t_1181_, 2);
v___x_1185_ = lean_apply_2(v_k_1182_, v_start_1183_, v_items_1184_);
return v___x_1185_;
}
case 7:
{
lean_object* v_container_1186_; lean_object* v_content_1187_; lean_object* v___x_1188_; 
v_container_1186_ = lean_ctor_get(v_t_1181_, 0);
lean_inc(v_container_1186_);
v_content_1187_ = lean_ctor_get(v_t_1181_, 1);
lean_inc_ref(v_content_1187_);
lean_dec_ref_known(v_t_1181_, 2);
v___x_1188_ = lean_apply_2(v_k_1182_, v_container_1186_, v_content_1187_);
return v___x_1188_;
}
default: 
{
lean_object* v_contents_1189_; lean_object* v___x_1190_; 
v_contents_1189_ = lean_ctor_get(v_t_1181_, 0);
lean_inc_ref(v_contents_1189_);
lean_dec_ref(v_t_1181_);
v___x_1190_ = lean_apply_1(v_k_1182_, v_contents_1189_);
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim(lean_object* v_i_1191_, lean_object* v_b_1192_, lean_object* v_motive__1_1193_, lean_object* v_ctorIdx_1194_, lean_object* v_t_1195_, lean_object* v_h_1196_, lean_object* v_k_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1195_, v_k_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___boxed(lean_object* v_i_1199_, lean_object* v_b_1200_, lean_object* v_motive__1_1201_, lean_object* v_ctorIdx_1202_, lean_object* v_t_1203_, lean_object* v_h_1204_, lean_object* v_k_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Doc_Block_ctorElim(v_i_1199_, v_b_1200_, v_motive__1_1201_, v_ctorIdx_1202_, v_t_1203_, v_h_1204_, v_k_1205_);
lean_dec(v_ctorIdx_1202_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim___redArg(lean_object* v_t_1207_, lean_object* v_para_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1207_, v_para_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim(lean_object* v_i_1210_, lean_object* v_b_1211_, lean_object* v_motive__1_1212_, lean_object* v_t_1213_, lean_object* v_h_1214_, lean_object* v_para_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1213_, v_para_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim___redArg(lean_object* v_t_1217_, lean_object* v_code_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1217_, v_code_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim(lean_object* v_i_1220_, lean_object* v_b_1221_, lean_object* v_motive__1_1222_, lean_object* v_t_1223_, lean_object* v_h_1224_, lean_object* v_code_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1223_, v_code_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim___redArg(lean_object* v_t_1227_, lean_object* v_ul_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1227_, v_ul_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim(lean_object* v_i_1230_, lean_object* v_b_1231_, lean_object* v_motive__1_1232_, lean_object* v_t_1233_, lean_object* v_h_1234_, lean_object* v_ul_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1233_, v_ul_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim___redArg(lean_object* v_t_1237_, lean_object* v_ol_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1237_, v_ol_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim(lean_object* v_i_1240_, lean_object* v_b_1241_, lean_object* v_motive__1_1242_, lean_object* v_t_1243_, lean_object* v_h_1244_, lean_object* v_ol_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1243_, v_ol_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim___redArg(lean_object* v_t_1247_, lean_object* v_dl_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1247_, v_dl_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim(lean_object* v_i_1250_, lean_object* v_b_1251_, lean_object* v_motive__1_1252_, lean_object* v_t_1253_, lean_object* v_h_1254_, lean_object* v_dl_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1253_, v_dl_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim___redArg(lean_object* v_t_1257_, lean_object* v_blockquote_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1257_, v_blockquote_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim(lean_object* v_i_1260_, lean_object* v_b_1261_, lean_object* v_motive__1_1262_, lean_object* v_t_1263_, lean_object* v_h_1264_, lean_object* v_blockquote_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1263_, v_blockquote_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim___redArg(lean_object* v_t_1267_, lean_object* v_concat_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1267_, v_concat_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim(lean_object* v_i_1270_, lean_object* v_b_1271_, lean_object* v_motive__1_1272_, lean_object* v_t_1273_, lean_object* v_h_1274_, lean_object* v_concat_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1273_, v_concat_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim___redArg(lean_object* v_t_1277_, lean_object* v_other_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1277_, v_other_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim(lean_object* v_i_1280_, lean_object* v_b_1281_, lean_object* v_motive__1_1282_, lean_object* v_t_1283_, lean_object* v_h_1284_, lean_object* v_other_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1283_, v_other_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___redArg___boxed(lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_res_1291_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1287_, v_inst_1288_, v_x_1289_, v_x_1290_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq___redArg(lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_){
_start:
{
lean_object* v_localinst_1297_; lean_object* v_a_1299_; lean_object* v_b_1300_; 
lean_inc_ref(v_inst_1294_);
lean_inc_ref(v_inst_1293_);
v_localinst_1297_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1297_, 0, v_inst_1293_);
lean_closure_set(v_localinst_1297_, 1, v_inst_1294_);
switch(lean_obj_tag(v_x_1295_))
{
case 0:
{
lean_dec_ref(v_localinst_1297_);
lean_dec_ref(v_inst_1294_);
if (lean_obj_tag(v_x_1296_) == 0)
{
lean_object* v_contents_1305_; lean_object* v_contents_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_contents_1305_ = lean_ctor_get(v_x_1295_, 0);
lean_inc_ref(v_contents_1305_);
lean_dec_ref_known(v_x_1295_, 1);
v_contents_1306_ = lean_ctor_get(v_x_1296_, 0);
lean_inc_ref(v_contents_1306_);
lean_dec_ref_known(v_x_1296_, 1);
v___x_1307_ = lean_array_get_size(v_contents_1305_);
v___x_1308_ = lean_array_get_size(v_contents_1306_);
v___x_1309_ = lean_nat_dec_eq(v___x_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_dec_ref(v_contents_1306_);
lean_dec_ref(v_contents_1305_);
lean_dec_ref(v_inst_1293_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1310_, 0, lean_box(0));
lean_closure_set(v___x_1310_, 1, v_inst_1293_);
v___x_1311_ = l_Array_isEqvAux___redArg(v_contents_1305_, v_contents_1306_, v___x_1310_, v___x_1307_);
lean_dec_ref(v_contents_1306_);
lean_dec_ref(v_contents_1305_);
return v___x_1311_;
}
}
else
{
uint8_t v___x_1312_; 
lean_dec_ref_known(v_x_1295_, 1);
lean_dec_ref(v_x_1296_);
lean_dec_ref(v_inst_1293_);
v___x_1312_ = 0;
return v___x_1312_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1297_);
lean_dec_ref(v_inst_1294_);
lean_dec_ref(v_inst_1293_);
if (lean_obj_tag(v_x_1296_) == 1)
{
lean_object* v_content_1313_; lean_object* v_content_1314_; uint8_t v___x_1315_; 
v_content_1313_ = lean_ctor_get(v_x_1295_, 0);
lean_inc_ref(v_content_1313_);
lean_dec_ref_known(v_x_1295_, 1);
v_content_1314_ = lean_ctor_get(v_x_1296_, 0);
lean_inc_ref(v_content_1314_);
lean_dec_ref_known(v_x_1296_, 1);
v___x_1315_ = lean_string_dec_eq(v_content_1313_, v_content_1314_);
lean_dec_ref(v_content_1314_);
lean_dec_ref(v_content_1313_);
return v___x_1315_;
}
else
{
uint8_t v___x_1316_; 
lean_dec_ref_known(v_x_1295_, 1);
lean_dec_ref(v_x_1296_);
v___x_1316_ = 0;
return v___x_1316_;
}
}
case 2:
{
lean_dec_ref(v_inst_1294_);
lean_dec_ref(v_inst_1293_);
if (lean_obj_tag(v_x_1296_) == 2)
{
lean_object* v_items_1317_; lean_object* v_items_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_items_1317_ = lean_ctor_get(v_x_1295_, 0);
lean_inc_ref(v_items_1317_);
lean_dec_ref_known(v_x_1295_, 1);
v_items_1318_ = lean_ctor_get(v_x_1296_, 0);
lean_inc_ref(v_items_1318_);
lean_dec_ref_known(v_x_1296_, 1);
v___x_1319_ = lean_array_get_size(v_items_1317_);
v___x_1320_ = lean_array_get_size(v_items_1318_);
v___x_1321_ = lean_nat_dec_eq(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_dec_ref(v_items_1318_);
lean_dec_ref(v_items_1317_);
lean_dec_ref(v_localinst_1297_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1322_, 0, lean_box(0));
lean_closure_set(v___x_1322_, 1, v_localinst_1297_);
v___x_1323_ = l_Array_isEqvAux___redArg(v_items_1317_, v_items_1318_, v___x_1322_, v___x_1319_);
lean_dec_ref(v_items_1318_);
lean_dec_ref(v_items_1317_);
return v___x_1323_;
}
}
else
{
uint8_t v___x_1324_; 
lean_dec_ref_known(v_x_1295_, 1);
lean_dec_ref(v_localinst_1297_);
lean_dec_ref(v_x_1296_);
v___x_1324_ = 0;
return v___x_1324_;
}
}
case 3:
{
lean_dec_ref(v_inst_1294_);
lean_dec_ref(v_inst_1293_);
if (lean_obj_tag(v_x_1296_) == 3)
{
lean_object* v_start_1325_; lean_object* v_items_1326_; lean_object* v_start_1327_; lean_object* v_items_1328_; uint8_t v___x_1329_; 
v_start_1325_ = lean_ctor_get(v_x_1295_, 0);
lean_inc(v_start_1325_);
v_items_1326_ = lean_ctor_get(v_x_1295_, 1);
lean_inc_ref(v_items_1326_);
lean_dec_ref_known(v_x_1295_, 2);
v_start_1327_ = lean_ctor_get(v_x_1296_, 0);
lean_inc(v_start_1327_);
v_items_1328_ = lean_ctor_get(v_x_1296_, 1);
lean_inc_ref(v_items_1328_);
lean_dec_ref_known(v_x_1296_, 2);
v___x_1329_ = lean_int_dec_eq(v_start_1325_, v_start_1327_);
lean_dec(v_start_1327_);
lean_dec(v_start_1325_);
if (v___x_1329_ == 0)
{
lean_dec_ref(v_items_1328_);
lean_dec_ref(v_items_1326_);
lean_dec_ref(v_localinst_1297_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1330_ = lean_array_get_size(v_items_1326_);
v___x_1331_ = lean_array_get_size(v_items_1328_);
v___x_1332_ = lean_nat_dec_eq(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_dec_ref(v_items_1328_);
lean_dec_ref(v_items_1326_);
lean_dec_ref(v_localinst_1297_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1333_, 0, lean_box(0));
lean_closure_set(v___x_1333_, 1, v_localinst_1297_);
v___x_1334_ = l_Array_isEqvAux___redArg(v_items_1326_, v_items_1328_, v___x_1333_, v___x_1330_);
lean_dec_ref(v_items_1328_);
lean_dec_ref(v_items_1326_);
return v___x_1334_;
}
}
}
else
{
uint8_t v___x_1335_; 
lean_dec_ref_known(v_x_1295_, 2);
lean_dec_ref(v_localinst_1297_);
lean_dec_ref(v_x_1296_);
v___x_1335_ = 0;
return v___x_1335_;
}
}
case 4:
{
lean_dec_ref(v_inst_1294_);
if (lean_obj_tag(v_x_1296_) == 4)
{
lean_object* v_items_1336_; lean_object* v_items_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v_items_1336_ = lean_ctor_get(v_x_1295_, 0);
lean_inc_ref(v_items_1336_);
lean_dec_ref_known(v_x_1295_, 1);
v_items_1337_ = lean_ctor_get(v_x_1296_, 0);
lean_inc_ref(v_items_1337_);
lean_dec_ref_known(v_x_1296_, 1);
v___x_1338_ = lean_array_get_size(v_items_1336_);
v___x_1339_ = lean_array_get_size(v_items_1337_);
v___x_1340_ = lean_nat_dec_eq(v___x_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_dec_ref(v_items_1337_);
lean_dec_ref(v_items_1336_);
lean_dec_ref(v_localinst_1297_);
lean_dec_ref(v_inst_1293_);
return v___x_1340_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1341_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1341_, 0, lean_box(0));
lean_closure_set(v___x_1341_, 1, v_inst_1293_);
v___x_1342_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1342_, 0, lean_box(0));
lean_closure_set(v___x_1342_, 1, lean_box(0));
lean_closure_set(v___x_1342_, 2, v___x_1341_);
lean_closure_set(v___x_1342_, 3, v_localinst_1297_);
v___x_1343_ = l_Array_isEqvAux___redArg(v_items_1336_, v_items_1337_, v___x_1342_, v___x_1338_);
lean_dec_ref(v_items_1337_);
lean_dec_ref(v_items_1336_);
return v___x_1343_;
}
}
else
{
uint8_t v___x_1344_; 
lean_dec_ref_known(v_x_1295_, 1);
lean_dec_ref(v_localinst_1297_);
lean_dec_ref(v_x_1296_);
lean_dec_ref(v_inst_1293_);
v___x_1344_ = 0;
return v___x_1344_;
}
}
case 5:
{
lean_dec_ref(v_inst_1294_);
lean_dec_ref(v_inst_1293_);
if (lean_obj_tag(v_x_1296_) == 5)
{
lean_object* v_items_1345_; lean_object* v_items_1346_; 
v_items_1345_ = lean_ctor_get(v_x_1295_, 0);
lean_inc_ref(v_items_1345_);
lean_dec_ref_known(v_x_1295_, 1);
v_items_1346_ = lean_ctor_get(v_x_1296_, 0);
lean_inc_ref(v_items_1346_);
lean_dec_ref_known(v_x_1296_, 1);
v_a_1299_ = v_items_1345_;
v_b_1300_ = v_items_1346_;
goto v___jp_1298_;
}
else
{
uint8_t v___x_1347_; 
lean_dec_ref_known(v_x_1295_, 1);
lean_dec_ref(v_localinst_1297_);
lean_dec_ref(v_x_1296_);
v___x_1347_ = 0;
return v___x_1347_;
}
}
case 6:
{
lean_dec_ref(v_inst_1294_);
lean_dec_ref(v_inst_1293_);
if (lean_obj_tag(v_x_1296_) == 6)
{
lean_object* v_content_1348_; lean_object* v_content_1349_; 
v_content_1348_ = lean_ctor_get(v_x_1295_, 0);
lean_inc_ref(v_content_1348_);
lean_dec_ref_known(v_x_1295_, 1);
v_content_1349_ = lean_ctor_get(v_x_1296_, 0);
lean_inc_ref(v_content_1349_);
lean_dec_ref_known(v_x_1296_, 1);
v_a_1299_ = v_content_1348_;
v_b_1300_ = v_content_1349_;
goto v___jp_1298_;
}
else
{
uint8_t v___x_1350_; 
lean_dec_ref_known(v_x_1295_, 1);
lean_dec_ref(v_localinst_1297_);
lean_dec_ref(v_x_1296_);
v___x_1350_ = 0;
return v___x_1350_;
}
}
default: 
{
lean_dec_ref(v_inst_1293_);
if (lean_obj_tag(v_x_1296_) == 7)
{
lean_object* v_container_1351_; lean_object* v_content_1352_; lean_object* v_container_1353_; lean_object* v_content_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_container_1351_ = lean_ctor_get(v_x_1295_, 0);
lean_inc(v_container_1351_);
v_content_1352_ = lean_ctor_get(v_x_1295_, 1);
lean_inc_ref(v_content_1352_);
lean_dec_ref_known(v_x_1295_, 2);
v_container_1353_ = lean_ctor_get(v_x_1296_, 0);
lean_inc(v_container_1353_);
v_content_1354_ = lean_ctor_get(v_x_1296_, 1);
lean_inc_ref(v_content_1354_);
lean_dec_ref_known(v_x_1296_, 2);
v___x_1355_ = lean_apply_2(v_inst_1294_, v_container_1351_, v_container_1353_);
v___x_1356_ = lean_unbox(v___x_1355_);
if (v___x_1356_ == 0)
{
uint8_t v___x_1357_; 
lean_dec_ref(v_content_1354_);
lean_dec_ref(v_content_1352_);
lean_dec_ref(v_localinst_1297_);
v___x_1357_ = lean_unbox(v___x_1355_);
return v___x_1357_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1358_ = lean_array_get_size(v_content_1352_);
v___x_1359_ = lean_array_get_size(v_content_1354_);
v___x_1360_ = lean_nat_dec_eq(v___x_1358_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_dec_ref(v_content_1354_);
lean_dec_ref(v_content_1352_);
lean_dec_ref(v_localinst_1297_);
return v___x_1360_;
}
else
{
uint8_t v___x_1361_; 
v___x_1361_ = l_Array_isEqvAux___redArg(v_content_1352_, v_content_1354_, v_localinst_1297_, v___x_1358_);
lean_dec_ref(v_content_1354_);
lean_dec_ref(v_content_1352_);
return v___x_1361_;
}
}
}
else
{
uint8_t v___x_1362_; 
lean_dec_ref_known(v_x_1295_, 2);
lean_dec_ref(v_localinst_1297_);
lean_dec_ref(v_x_1296_);
lean_dec_ref(v_inst_1294_);
v___x_1362_ = 0;
return v___x_1362_;
}
}
}
v___jp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1301_ = lean_array_get_size(v_a_1299_);
v___x_1302_ = lean_array_get_size(v_b_1300_);
v___x_1303_ = lean_nat_dec_eq(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec_ref(v_b_1300_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_localinst_1297_);
return v___x_1303_;
}
else
{
uint8_t v___x_1304_; 
v___x_1304_ = l_Array_isEqvAux___redArg(v_a_1299_, v_b_1300_, v_localinst_1297_, v___x_1301_);
lean_dec_ref(v_b_1300_);
lean_dec_ref(v_a_1299_);
return v___x_1304_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq(lean_object* v_i_1363_, lean_object* v_b_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
uint8_t v___x_1369_; 
v___x_1369_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1365_, v_inst_1366_, v_x_1367_, v_x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___boxed(lean_object* v_i_1370_, lean_object* v_b_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_){
_start:
{
uint8_t v_res_1376_; lean_object* v_r_1377_; 
v_res_1376_ = l_Lean_Doc_instBEqBlock_beq(v_i_1370_, v_b_1371_, v_inst_1372_, v_inst_1373_, v_x_1374_, v_x_1375_);
v_r_1377_ = lean_box(v_res_1376_);
return v_r_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock___redArg(lean_object* v_inst_1378_, lean_object* v_inst_1379_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1380_, 0, lean_box(0));
lean_closure_set(v___x_1380_, 1, lean_box(0));
lean_closure_set(v___x_1380_, 2, v_inst_1378_);
lean_closure_set(v___x_1380_, 3, v_inst_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock(lean_object* v_i_1381_, lean_object* v_b_1382_, lean_object* v_inst_1383_, lean_object* v_inst_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1385_, 0, lean_box(0));
lean_closure_set(v___x_1385_, 1, lean_box(0));
lean_closure_set(v___x_1385_, 2, v_inst_1383_);
lean_closure_set(v___x_1385_, 3, v_inst_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___redArg___boxed(lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1386_, v_inst_1387_, v_x_1388_, v_x_1389_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord___redArg(lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v_localinst_1396_; lean_object* v_a_1398_; lean_object* v_b_1399_; 
lean_inc_ref(v_inst_1393_);
lean_inc_ref(v_inst_1392_);
v_localinst_1396_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1396_, 0, v_inst_1392_);
lean_closure_set(v_localinst_1396_, 1, v_inst_1393_);
switch(lean_obj_tag(v_x_1394_))
{
case 0:
{
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_inst_1393_);
switch(lean_obj_tag(v_x_1395_))
{
case 0:
{
lean_object* v_contents_1401_; lean_object* v_contents_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_contents_1401_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_contents_1401_);
lean_dec_ref_known(v_x_1394_, 1);
v_contents_1402_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_contents_1402_);
lean_dec_ref_known(v_x_1395_, 1);
v___x_1403_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1403_, 0, lean_box(0));
lean_closure_set(v___x_1403_, 1, v_inst_1392_);
v___x_1404_ = l_Array_compareLex___redArg(v___x_1403_, v_contents_1401_, v_contents_1402_);
lean_dec_ref(v_contents_1402_);
lean_dec_ref(v_contents_1401_);
if (v___x_1404_ == 1)
{
return v___x_1404_;
}
else
{
return v___x_1404_;
}
}
case 1:
{
uint8_t v___x_1405_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_inst_1392_);
v___x_1405_ = 0;
return v___x_1405_;
}
case 2:
{
uint8_t v___x_1406_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_inst_1392_);
v___x_1406_ = 0;
return v___x_1406_;
}
case 3:
{
uint8_t v___x_1407_; 
lean_dec_ref_known(v_x_1395_, 2);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_inst_1392_);
v___x_1407_ = 0;
return v___x_1407_;
}
case 4:
{
uint8_t v___x_1408_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_inst_1392_);
v___x_1408_ = 0;
return v___x_1408_;
}
case 5:
{
uint8_t v___x_1409_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_inst_1392_);
v___x_1409_ = 0;
return v___x_1409_;
}
case 6:
{
uint8_t v___x_1410_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_inst_1392_);
v___x_1410_ = 0;
return v___x_1410_;
}
default: 
{
uint8_t v___x_1411_; 
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_x_1395_);
lean_dec_ref(v_inst_1392_);
v___x_1411_ = 0;
return v___x_1411_;
}
}
}
case 1:
{
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
switch(lean_obj_tag(v_x_1395_))
{
case 0:
{
uint8_t v___x_1412_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
v___x_1412_ = 2;
return v___x_1412_;
}
case 1:
{
lean_object* v_content_1413_; lean_object* v_content_1414_; uint8_t v___x_1415_; 
v_content_1413_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_content_1413_);
lean_dec_ref_known(v_x_1394_, 1);
v_content_1414_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_content_1414_);
lean_dec_ref_known(v_x_1395_, 1);
v___x_1415_ = lean_string_compare(v_content_1413_, v_content_1414_);
lean_dec_ref(v_content_1414_);
lean_dec_ref(v_content_1413_);
if (v___x_1415_ == 1)
{
return v___x_1415_;
}
else
{
return v___x_1415_;
}
}
case 2:
{
uint8_t v___x_1416_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
v___x_1416_ = 0;
return v___x_1416_;
}
case 3:
{
uint8_t v___x_1417_; 
lean_dec_ref_known(v_x_1395_, 2);
lean_dec_ref_known(v_x_1394_, 1);
v___x_1417_ = 0;
return v___x_1417_;
}
case 4:
{
uint8_t v___x_1418_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
v___x_1418_ = 0;
return v___x_1418_;
}
case 5:
{
uint8_t v___x_1419_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
v___x_1419_ = 0;
return v___x_1419_;
}
case 6:
{
uint8_t v___x_1420_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
v___x_1420_ = 0;
return v___x_1420_;
}
default: 
{
uint8_t v___x_1421_; 
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_x_1395_);
v___x_1421_ = 0;
return v___x_1421_;
}
}
}
case 2:
{
lean_dec_ref(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
switch(lean_obj_tag(v_x_1395_))
{
case 0:
{
uint8_t v___x_1422_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1422_ = 2;
return v___x_1422_;
}
case 1:
{
uint8_t v___x_1423_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1423_ = 2;
return v___x_1423_;
}
case 2:
{
lean_object* v_items_1424_; lean_object* v_items_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_items_1424_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_items_1424_);
lean_dec_ref_known(v_x_1394_, 1);
v_items_1425_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_items_1425_);
lean_dec_ref_known(v_x_1395_, 1);
v___x_1426_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1426_, 0, lean_box(0));
lean_closure_set(v___x_1426_, 1, v_localinst_1396_);
v___x_1427_ = l_Array_compareLex___redArg(v___x_1426_, v_items_1424_, v_items_1425_);
lean_dec_ref(v_items_1425_);
lean_dec_ref(v_items_1424_);
if (v___x_1427_ == 1)
{
return v___x_1427_;
}
else
{
return v___x_1427_;
}
}
case 3:
{
uint8_t v___x_1428_; 
lean_dec_ref_known(v_x_1395_, 2);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1428_ = 0;
return v___x_1428_;
}
case 4:
{
uint8_t v___x_1429_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1429_ = 0;
return v___x_1429_;
}
case 5:
{
uint8_t v___x_1430_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1430_ = 0;
return v___x_1430_;
}
case 6:
{
uint8_t v___x_1431_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1431_ = 0;
return v___x_1431_;
}
default: 
{
uint8_t v___x_1432_; 
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_x_1395_);
v___x_1432_ = 0;
return v___x_1432_;
}
}
}
case 3:
{
lean_dec_ref(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
switch(lean_obj_tag(v_x_1395_))
{
case 0:
{
uint8_t v___x_1433_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 2);
lean_dec_ref(v_localinst_1396_);
v___x_1433_ = 2;
return v___x_1433_;
}
case 1:
{
uint8_t v___x_1434_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 2);
lean_dec_ref(v_localinst_1396_);
v___x_1434_ = 2;
return v___x_1434_;
}
case 2:
{
uint8_t v___x_1435_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 2);
lean_dec_ref(v_localinst_1396_);
v___x_1435_ = 2;
return v___x_1435_;
}
case 3:
{
lean_object* v_start_1436_; lean_object* v_items_1437_; lean_object* v_start_1438_; lean_object* v_items_1439_; uint8_t v___x_1440_; 
v_start_1436_ = lean_ctor_get(v_x_1394_, 0);
lean_inc(v_start_1436_);
v_items_1437_ = lean_ctor_get(v_x_1394_, 1);
lean_inc_ref(v_items_1437_);
lean_dec_ref_known(v_x_1394_, 2);
v_start_1438_ = lean_ctor_get(v_x_1395_, 0);
lean_inc(v_start_1438_);
v_items_1439_ = lean_ctor_get(v_x_1395_, 1);
lean_inc_ref(v_items_1439_);
lean_dec_ref_known(v_x_1395_, 2);
v___x_1440_ = lean_int_dec_lt(v_start_1436_, v_start_1438_);
if (v___x_1440_ == 0)
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_int_dec_eq(v_start_1436_, v_start_1438_);
lean_dec(v_start_1438_);
lean_dec(v_start_1436_);
if (v___x_1441_ == 0)
{
uint8_t v___x_1442_; 
lean_dec_ref(v_items_1439_);
lean_dec_ref(v_items_1437_);
lean_dec_ref(v_localinst_1396_);
v___x_1442_ = 2;
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1443_, 0, lean_box(0));
lean_closure_set(v___x_1443_, 1, v_localinst_1396_);
v___x_1444_ = l_Array_compareLex___redArg(v___x_1443_, v_items_1437_, v_items_1439_);
lean_dec_ref(v_items_1439_);
lean_dec_ref(v_items_1437_);
if (v___x_1444_ == 1)
{
return v___x_1444_;
}
else
{
return v___x_1444_;
}
}
}
else
{
uint8_t v___x_1445_; 
lean_dec_ref(v_items_1439_);
lean_dec(v_start_1438_);
lean_dec_ref(v_items_1437_);
lean_dec(v_start_1436_);
lean_dec_ref(v_localinst_1396_);
v___x_1445_ = 0;
return v___x_1445_;
}
}
case 4:
{
uint8_t v___x_1446_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 2);
lean_dec_ref(v_localinst_1396_);
v___x_1446_ = 0;
return v___x_1446_;
}
case 5:
{
uint8_t v___x_1447_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 2);
lean_dec_ref(v_localinst_1396_);
v___x_1447_ = 0;
return v___x_1447_;
}
case 6:
{
uint8_t v___x_1448_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 2);
lean_dec_ref(v_localinst_1396_);
v___x_1448_ = 0;
return v___x_1448_;
}
default: 
{
uint8_t v___x_1449_; 
lean_dec_ref_known(v_x_1394_, 2);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_x_1395_);
v___x_1449_ = 0;
return v___x_1449_;
}
}
}
case 4:
{
lean_dec_ref(v_inst_1393_);
switch(lean_obj_tag(v_x_1395_))
{
case 0:
{
uint8_t v___x_1450_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_inst_1392_);
v___x_1450_ = 2;
return v___x_1450_;
}
case 1:
{
uint8_t v___x_1451_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_inst_1392_);
v___x_1451_ = 2;
return v___x_1451_;
}
case 2:
{
uint8_t v___x_1452_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_inst_1392_);
v___x_1452_ = 2;
return v___x_1452_;
}
case 3:
{
uint8_t v___x_1453_; 
lean_dec_ref_known(v_x_1395_, 2);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_inst_1392_);
v___x_1453_ = 2;
return v___x_1453_;
}
case 4:
{
lean_object* v_items_1454_; lean_object* v_items_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v_items_1454_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_items_1454_);
lean_dec_ref_known(v_x_1394_, 1);
v_items_1455_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_items_1455_);
lean_dec_ref_known(v_x_1395_, 1);
v___x_1456_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1456_, 0, lean_box(0));
lean_closure_set(v___x_1456_, 1, v_inst_1392_);
v___x_1457_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1457_, 0, lean_box(0));
lean_closure_set(v___x_1457_, 1, lean_box(0));
lean_closure_set(v___x_1457_, 2, v___x_1456_);
lean_closure_set(v___x_1457_, 3, v_localinst_1396_);
v___x_1458_ = l_Array_compareLex___redArg(v___x_1457_, v_items_1454_, v_items_1455_);
lean_dec_ref(v_items_1455_);
lean_dec_ref(v_items_1454_);
if (v___x_1458_ == 1)
{
return v___x_1458_;
}
else
{
return v___x_1458_;
}
}
case 5:
{
uint8_t v___x_1459_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_inst_1392_);
v___x_1459_ = 0;
return v___x_1459_;
}
case 6:
{
uint8_t v___x_1460_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_inst_1392_);
v___x_1460_ = 0;
return v___x_1460_;
}
default: 
{
uint8_t v___x_1461_; 
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_x_1395_);
lean_dec_ref(v_inst_1392_);
v___x_1461_ = 0;
return v___x_1461_;
}
}
}
case 5:
{
lean_dec_ref(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
switch(lean_obj_tag(v_x_1395_))
{
case 0:
{
uint8_t v___x_1462_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1462_ = 2;
return v___x_1462_;
}
case 1:
{
uint8_t v___x_1463_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1463_ = 2;
return v___x_1463_;
}
case 2:
{
uint8_t v___x_1464_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1464_ = 2;
return v___x_1464_;
}
case 3:
{
uint8_t v___x_1465_; 
lean_dec_ref_known(v_x_1395_, 2);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1465_ = 2;
return v___x_1465_;
}
case 4:
{
uint8_t v___x_1466_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1466_ = 2;
return v___x_1466_;
}
case 5:
{
lean_object* v_items_1467_; lean_object* v_items_1468_; 
v_items_1467_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_items_1467_);
lean_dec_ref_known(v_x_1394_, 1);
v_items_1468_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_items_1468_);
lean_dec_ref_known(v_x_1395_, 1);
v_a_1398_ = v_items_1467_;
v_b_1399_ = v_items_1468_;
goto v___jp_1397_;
}
case 6:
{
uint8_t v___x_1469_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1469_ = 0;
return v___x_1469_;
}
default: 
{
uint8_t v___x_1470_; 
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_x_1395_);
v___x_1470_ = 0;
return v___x_1470_;
}
}
}
case 6:
{
lean_dec_ref(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
switch(lean_obj_tag(v_x_1395_))
{
case 0:
{
uint8_t v___x_1471_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1471_ = 2;
return v___x_1471_;
}
case 1:
{
uint8_t v___x_1472_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1472_ = 2;
return v___x_1472_;
}
case 2:
{
uint8_t v___x_1473_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1473_ = 2;
return v___x_1473_;
}
case 3:
{
uint8_t v___x_1474_; 
lean_dec_ref_known(v_x_1395_, 2);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1474_ = 2;
return v___x_1474_;
}
case 4:
{
uint8_t v___x_1475_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1475_ = 2;
return v___x_1475_;
}
case 5:
{
uint8_t v___x_1476_; 
lean_dec_ref_known(v_x_1395_, 1);
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
v___x_1476_ = 2;
return v___x_1476_;
}
case 6:
{
lean_object* v_content_1477_; lean_object* v_content_1478_; 
v_content_1477_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_content_1477_);
lean_dec_ref_known(v_x_1394_, 1);
v_content_1478_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_content_1478_);
lean_dec_ref_known(v_x_1395_, 1);
v_a_1398_ = v_content_1477_;
v_b_1399_ = v_content_1478_;
goto v___jp_1397_;
}
default: 
{
uint8_t v___x_1479_; 
lean_dec_ref_known(v_x_1394_, 1);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_x_1395_);
v___x_1479_ = 0;
return v___x_1479_;
}
}
}
default: 
{
lean_dec_ref(v_inst_1392_);
if (lean_obj_tag(v_x_1395_) == 7)
{
lean_object* v_container_1480_; lean_object* v_content_1481_; lean_object* v_container_1482_; lean_object* v_content_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v_container_1480_ = lean_ctor_get(v_x_1394_, 0);
lean_inc(v_container_1480_);
v_content_1481_ = lean_ctor_get(v_x_1394_, 1);
lean_inc_ref(v_content_1481_);
lean_dec_ref_known(v_x_1394_, 2);
v_container_1482_ = lean_ctor_get(v_x_1395_, 0);
lean_inc(v_container_1482_);
v_content_1483_ = lean_ctor_get(v_x_1395_, 1);
lean_inc_ref(v_content_1483_);
lean_dec_ref_known(v_x_1395_, 2);
v___x_1484_ = lean_apply_2(v_inst_1393_, v_container_1480_, v_container_1482_);
v___x_1485_ = lean_unbox(v___x_1484_);
if (v___x_1485_ == 1)
{
uint8_t v___x_1486_; 
v___x_1486_ = l_Array_compareLex___redArg(v_localinst_1396_, v_content_1481_, v_content_1483_);
lean_dec_ref(v_content_1483_);
lean_dec_ref(v_content_1481_);
if (v___x_1486_ == 1)
{
return v___x_1486_;
}
else
{
return v___x_1486_;
}
}
else
{
uint8_t v___x_1487_; 
lean_dec_ref(v_content_1483_);
lean_dec_ref(v_content_1481_);
lean_dec_ref(v_localinst_1396_);
v___x_1487_ = lean_unbox(v___x_1484_);
return v___x_1487_;
}
}
else
{
uint8_t v___x_1488_; 
lean_dec_ref_known(v_x_1394_, 2);
lean_dec_ref(v_localinst_1396_);
lean_dec_ref(v_x_1395_);
lean_dec_ref(v_inst_1393_);
v___x_1488_ = 2;
return v___x_1488_;
}
}
}
v___jp_1397_:
{
uint8_t v___x_1400_; 
v___x_1400_ = l_Array_compareLex___redArg(v_localinst_1396_, v_a_1398_, v_b_1399_);
lean_dec_ref(v_b_1399_);
lean_dec_ref(v_a_1398_);
if (v___x_1400_ == 1)
{
return v___x_1400_;
}
else
{
return v___x_1400_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord(lean_object* v_i_1489_, lean_object* v_b_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
uint8_t v___x_1495_; 
v___x_1495_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1491_, v_inst_1492_, v_x_1493_, v_x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___boxed(lean_object* v_i_1496_, lean_object* v_b_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
uint8_t v_res_1502_; lean_object* v_r_1503_; 
v_res_1502_ = l_Lean_Doc_instOrdBlock_ord(v_i_1496_, v_b_1497_, v_inst_1498_, v_inst_1499_, v_x_1500_, v_x_1501_);
v_r_1503_ = lean_box(v_res_1502_);
return v_r_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock___redArg(lean_object* v_inst_1504_, lean_object* v_inst_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1506_, 0, lean_box(0));
lean_closure_set(v___x_1506_, 1, lean_box(0));
lean_closure_set(v___x_1506_, 2, v_inst_1504_);
lean_closure_set(v___x_1506_, 3, v_inst_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock(lean_object* v_i_1507_, lean_object* v_b_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1511_, 0, lean_box(0));
lean_closure_set(v___x_1511_, 1, lean_box(0));
lean_closure_set(v___x_1511_, 2, v_inst_1509_);
lean_closure_set(v___x_1511_, 3, v_inst_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_nat_to_int(v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg___boxed(lean_object* v_inst_1562_, lean_object* v_inst_1563_, lean_object* v_x_1564_, lean_object* v_prec_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1562_, v_inst_1563_, v_x_1564_, v_prec_1565_);
lean_dec(v_prec_1565_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg(lean_object* v_inst_1567_, lean_object* v_inst_1568_, lean_object* v_x_1569_, lean_object* v_prec_1570_){
_start:
{
lean_object* v_localinst_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_inc_ref(v_inst_1568_);
lean_inc_ref(v_inst_1567_);
v_localinst_1571_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1571_, 0, v_inst_1567_);
lean_closure_set(v_localinst_1571_, 1, v_inst_1568_);
v___x_1572_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1572_, 0, lean_box(0));
lean_closure_set(v___x_1572_, 1, v_inst_1567_);
lean_inc_ref(v_localinst_1571_);
v___x_1573_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_1573_, 0, lean_box(0));
lean_closure_set(v___x_1573_, 1, v_localinst_1571_);
switch(lean_obj_tag(v_x_1569_))
{
case 0:
{
lean_object* v_contents_1574_; lean_object* v___y_1576_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
lean_dec_ref(v___x_1573_);
lean_dec_ref(v_localinst_1571_);
lean_dec_ref(v_inst_1568_);
v_contents_1574_ = lean_ctor_get(v_x_1569_, 0);
lean_inc_ref(v_contents_1574_);
lean_dec_ref_known(v_x_1569_, 1);
v___x_1584_ = lean_unsigned_to_nat(1024u);
v___x_1585_ = lean_nat_dec_le(v___x_1584_, v_prec_1570_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1576_ = v___x_1586_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1576_ = v___x_1587_;
goto v___jp_1575_;
}
v___jp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1577_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__2));
v___x_1578_ = l_Array_repr___redArg(v___x_1572_, v_contents_1574_);
v___x_1579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
lean_inc(v___y_1576_);
v___x_1580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___y_1576_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = 0;
v___x_1582_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set_uint8(v___x_1582_, sizeof(void*)*1, v___x_1581_);
v___x_1583_ = l_Repr_addAppParen(v___x_1582_, v_prec_1570_);
return v___x_1583_;
}
}
case 1:
{
lean_object* v_content_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v___x_1573_);
lean_dec_ref(v___x_1572_);
lean_dec_ref(v_localinst_1571_);
lean_dec_ref(v_inst_1568_);
v_content_1588_ = lean_ctor_get(v_x_1569_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_x_1569_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1590_ = v_x_1569_;
v_isShared_1591_ = v_isSharedCheck_1608_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_content_1588_);
lean_dec(v_x_1569_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1608_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___y_1593_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1604_ = lean_unsigned_to_nat(1024u);
v___x_1605_ = lean_nat_dec_le(v___x_1604_, v_prec_1570_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1593_ = v___x_1606_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1593_ = v___x_1607_;
goto v___jp_1592_;
}
v___jp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1594_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__5));
v___x_1595_ = l_String_quote(v_content_1588_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 3);
lean_ctor_set(v___x_1590_, 0, v___x_1595_);
v___x_1597_ = v___x_1590_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1594_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
lean_inc(v___y_1593_);
v___x_1599_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___y_1593_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = 0;
v___x_1601_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*1, v___x_1600_);
v___x_1602_ = l_Repr_addAppParen(v___x_1601_, v_prec_1570_);
return v___x_1602_;
}
}
}
}
case 2:
{
lean_object* v_items_1609_; lean_object* v___y_1611_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
lean_dec_ref(v___x_1572_);
lean_dec_ref(v_localinst_1571_);
lean_dec_ref(v_inst_1568_);
v_items_1609_ = lean_ctor_get(v_x_1569_, 0);
lean_inc_ref(v_items_1609_);
lean_dec_ref_known(v_x_1569_, 1);
v___x_1619_ = lean_unsigned_to_nat(1024u);
v___x_1620_ = lean_nat_dec_le(v___x_1619_, v_prec_1570_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1611_ = v___x_1621_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1611_ = v___x_1622_;
goto v___jp_1610_;
}
v___jp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1612_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__8));
v___x_1613_ = l_Array_repr___redArg(v___x_1573_, v_items_1609_);
v___x_1614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
lean_inc(v___y_1611_);
v___x_1615_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___y_1611_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = 0;
v___x_1617_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*1, v___x_1616_);
v___x_1618_ = l_Repr_addAppParen(v___x_1617_, v_prec_1570_);
return v___x_1618_;
}
}
case 3:
{
lean_object* v_start_1623_; lean_object* v_items_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___x_1572_);
lean_dec_ref(v_localinst_1571_);
lean_dec_ref(v_inst_1568_);
v_start_1623_ = lean_ctor_get(v_x_1569_, 0);
v_items_1624_ = lean_ctor_get(v_x_1569_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_x_1569_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1626_ = v_x_1569_;
v_isShared_1627_ = v_isSharedCheck_1659_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_items_1624_);
lean_inc(v_start_1623_);
lean_dec(v_x_1569_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1659_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1644_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = lean_unsigned_to_nat(1024u);
v___x_1656_ = lean_nat_dec_le(v___x_1655_, v_prec_1570_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1644_ = v___x_1657_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1644_ = v___x_1658_;
goto v___jp_1643_;
}
v___jp_1628_:
{
lean_object* v___x_1634_; 
lean_inc(v___y_1629_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 5);
lean_ctor_set(v___x_1626_, 1, v___y_1632_);
lean_ctor_set(v___x_1626_, 0, v___y_1629_);
v___x_1634_ = v___x_1626_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___y_1629_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___y_1632_);
v___x_1634_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_inc(v___y_1630_);
v___x_1635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
lean_ctor_set(v___x_1635_, 1, v___y_1630_);
v___x_1636_ = l_Array_repr___redArg(v___x_1573_, v_items_1624_);
v___x_1637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
lean_inc(v___y_1631_);
v___x_1638_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___y_1631_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = 0;
v___x_1640_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set_uint8(v___x_1640_, sizeof(void*)*1, v___x_1639_);
v___x_1641_ = l_Repr_addAppParen(v___x_1640_, v_prec_1570_);
return v___x_1641_;
}
}
v___jp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1645_ = lean_box(1);
v___x_1646_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__11));
v___x_1647_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___redArg___closed__12, &l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12);
v___x_1648_ = lean_int_dec_lt(v_start_1623_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = l_Int_repr(v_start_1623_);
lean_dec(v_start_1623_);
v___x_1650_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
v___y_1629_ = v___x_1646_;
v___y_1630_ = v___x_1645_;
v___y_1631_ = v___y_1644_;
v___y_1632_ = v___x_1650_;
goto v___jp_1628_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1651_ = lean_unsigned_to_nat(1024u);
v___x_1652_ = l_Int_repr(v_start_1623_);
lean_dec(v_start_1623_);
v___x_1653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
v___x_1654_ = l_Repr_addAppParen(v___x_1653_, v___x_1651_);
v___y_1629_ = v___x_1646_;
v___y_1630_ = v___x_1645_;
v___y_1631_ = v___y_1644_;
v___y_1632_ = v___x_1654_;
goto v___jp_1628_;
}
}
}
}
case 4:
{
lean_object* v_items_1660_; lean_object* v___x_1661_; lean_object* v___y_1663_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
lean_dec_ref(v___x_1573_);
lean_dec_ref(v_inst_1568_);
v_items_1660_ = lean_ctor_get(v_x_1569_, 0);
lean_inc_ref(v_items_1660_);
lean_dec_ref_known(v_x_1569_, 1);
v___x_1661_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1661_, 0, lean_box(0));
lean_closure_set(v___x_1661_, 1, lean_box(0));
lean_closure_set(v___x_1661_, 2, v___x_1572_);
lean_closure_set(v___x_1661_, 3, v_localinst_1571_);
v___x_1671_ = lean_unsigned_to_nat(1024u);
v___x_1672_ = lean_nat_dec_le(v___x_1671_, v_prec_1570_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1663_ = v___x_1673_;
goto v___jp_1662_;
}
else
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1663_ = v___x_1674_;
goto v___jp_1662_;
}
v___jp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1664_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__15));
v___x_1665_ = l_Array_repr___redArg(v___x_1661_, v_items_1660_);
v___x_1666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
lean_inc(v___y_1663_);
v___x_1667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___y_1663_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = 0;
v___x_1669_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*1, v___x_1668_);
v___x_1670_ = l_Repr_addAppParen(v___x_1669_, v_prec_1570_);
return v___x_1670_;
}
}
case 5:
{
lean_object* v_items_1675_; lean_object* v___y_1677_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
lean_dec_ref(v___x_1573_);
lean_dec_ref(v___x_1572_);
lean_dec_ref(v_inst_1568_);
v_items_1675_ = lean_ctor_get(v_x_1569_, 0);
lean_inc_ref(v_items_1675_);
lean_dec_ref_known(v_x_1569_, 1);
v___x_1685_ = lean_unsigned_to_nat(1024u);
v___x_1686_ = lean_nat_dec_le(v___x_1685_, v_prec_1570_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1677_ = v___x_1687_;
goto v___jp_1676_;
}
else
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1677_ = v___x_1688_;
goto v___jp_1676_;
}
v___jp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1678_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__18));
v___x_1679_ = l_Array_repr___redArg(v_localinst_1571_, v_items_1675_);
v___x_1680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
lean_inc(v___y_1677_);
v___x_1681_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___y_1677_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = 0;
v___x_1683_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set_uint8(v___x_1683_, sizeof(void*)*1, v___x_1682_);
v___x_1684_ = l_Repr_addAppParen(v___x_1683_, v_prec_1570_);
return v___x_1684_;
}
}
case 6:
{
lean_object* v_content_1689_; lean_object* v___y_1691_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
lean_dec_ref(v___x_1573_);
lean_dec_ref(v___x_1572_);
lean_dec_ref(v_inst_1568_);
v_content_1689_ = lean_ctor_get(v_x_1569_, 0);
lean_inc_ref(v_content_1689_);
lean_dec_ref_known(v_x_1569_, 1);
v___x_1699_ = lean_unsigned_to_nat(1024u);
v___x_1700_ = lean_nat_dec_le(v___x_1699_, v_prec_1570_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1691_ = v___x_1701_;
goto v___jp_1690_;
}
else
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1691_ = v___x_1702_;
goto v___jp_1690_;
}
v___jp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1692_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__21));
v___x_1693_ = l_Array_repr___redArg(v_localinst_1571_, v_content_1689_);
v___x_1694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
lean_inc(v___y_1691_);
v___x_1695_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___y_1691_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = 0;
v___x_1697_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set_uint8(v___x_1697_, sizeof(void*)*1, v___x_1696_);
v___x_1698_ = l_Repr_addAppParen(v___x_1697_, v_prec_1570_);
return v___x_1698_;
}
}
default: 
{
lean_object* v_container_1703_; lean_object* v_content_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v___x_1573_);
lean_dec_ref(v___x_1572_);
v_container_1703_ = lean_ctor_get(v_x_1569_, 0);
v_content_1704_ = lean_ctor_get(v_x_1569_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_x_1569_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1706_ = v_x_1569_;
v_isShared_1707_ = v_isSharedCheck_1728_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_content_1704_);
lean_inc(v_container_1703_);
lean_dec(v_x_1569_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1728_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___y_1709_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = lean_unsigned_to_nat(1024u);
v___x_1725_ = lean_nat_dec_le(v___x_1724_, v_prec_1570_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1709_ = v___x_1726_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1709_ = v___x_1727_;
goto v___jp_1708_;
}
v___jp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1710_ = lean_box(1);
v___x_1711_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__24));
v___x_1712_ = lean_unsigned_to_nat(1024u);
v___x_1713_ = lean_apply_2(v_inst_1568_, v_container_1703_, v___x_1712_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 5);
lean_ctor_set(v___x_1706_, 1, v___x_1713_);
lean_ctor_set(v___x_1706_, 0, v___x_1711_);
v___x_1715_ = v___x_1706_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v___x_1710_);
v___x_1717_ = l_Array_repr___redArg(v_localinst_1571_, v_content_1704_);
v___x_1718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1716_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
lean_inc(v___y_1709_);
v___x_1719_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___y_1709_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = 0;
v___x_1721_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1721_, 0, v___x_1719_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*1, v___x_1720_);
v___x_1722_ = l_Repr_addAppParen(v___x_1721_, v_prec_1570_);
return v___x_1722_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr(lean_object* v_i_1729_, lean_object* v_b_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_x_1733_, lean_object* v_prec_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1731_, v_inst_1732_, v_x_1733_, v_prec_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___boxed(lean_object* v_i_1736_, lean_object* v_b_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_x_1740_, lean_object* v_prec_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Doc_instReprBlock_repr(v_i_1736_, v_b_1737_, v_inst_1738_, v_inst_1739_, v_x_1740_, v_prec_1741_);
lean_dec(v_prec_1741_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock___redArg(lean_object* v_inst_1743_, lean_object* v_inst_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1745_, 0, lean_box(0));
lean_closure_set(v___x_1745_, 1, lean_box(0));
lean_closure_set(v___x_1745_, 2, v_inst_1743_);
lean_closure_set(v___x_1745_, 3, v_inst_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock(lean_object* v_i_1746_, lean_object* v_b_1747_, lean_object* v_inst_1748_, lean_object* v_inst_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1750_, 0, lean_box(0));
lean_closure_set(v___x_1750_, 1, lean_box(0));
lean_closure_set(v___x_1750_, 2, v_inst_1748_);
lean_closure_set(v___x_1750_, 3, v_inst_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg(){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlock_default___redArg___closed__1));
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg___boxed(lean_object* v___dummy_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
return v_res_1758_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedBlock_default___closed__0(void){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default(lean_object* v_i_1760_, lean_object* v_b_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg(){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg___boxed(lean_object* v___dummy_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Doc_instInhabitedBlock___redArg();
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock(lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg(){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = ((lean_object*)(l_Lean_Doc_Block_empty___redArg___closed__1));
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg___boxed(lean_object* v___dummy_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Doc_Block_empty___redArg();
return v_res_1777_;
}
}
static lean_object* _init_l_Lean_Doc_Block_empty___closed__0(void){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Doc_Block_empty___redArg();
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty(lean_object* v_i_1779_, lean_object* v_b_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_obj_once(&l_Lean_Doc_Block_empty___closed__0, &l_Lean_Doc_Block_empty___closed__0_once, _init_l_Lean_Doc_Block_empty___closed__0);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg(lean_object* v_x_1782_){
_start:
{
lean_inc_ref(v_x_1782_);
return v_x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg___boxed(lean_object* v_x_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Doc_Block_cast___redArg(v_x_1783_);
lean_dec_ref(v_x_1783_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast(lean_object* v_i_1785_, lean_object* v_i_x27_1786_, lean_object* v_b_1787_, lean_object* v_b_x27_1788_, lean_object* v_inlines__eq_1789_, lean_object* v_blocks__eq_1790_, lean_object* v_x_1791_){
_start:
{
lean_inc_ref(v_x_1791_);
return v_x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___boxed(lean_object* v_i_1792_, lean_object* v_i_x27_1793_, lean_object* v_b_1794_, lean_object* v_b_x27_1795_, lean_object* v_inlines__eq_1796_, lean_object* v_blocks__eq_1797_, lean_object* v_x_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Doc_Block_cast(v_i_1792_, v_i_x27_1793_, v_b_1794_, v_b_x27_1795_, v_inlines__eq_1796_, v_blocks__eq_1797_, v_x_1798_);
lean_dec_ref(v_x_1798_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___redArg___boxed(lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_x_1803_, lean_object* v_x_1804_){
_start:
{
uint8_t v_res_1805_; lean_object* v_r_1806_; 
v_res_1805_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1800_, v_inst_1801_, v_inst_1802_, v_x_1803_, v_x_1804_);
v_r_1806_ = lean_box(v_res_1805_);
return v_r_1806_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq___redArg(lean_object* v_inst_1807_, lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
lean_object* v_title_1812_; lean_object* v_titleString_1813_; lean_object* v_metadata_1814_; lean_object* v_content_1815_; lean_object* v_subParts_1816_; lean_object* v_title_1817_; lean_object* v_titleString_1818_; lean_object* v_metadata_1819_; lean_object* v_content_1820_; lean_object* v_subParts_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v_title_1812_ = lean_ctor_get(v_x_1810_, 0);
lean_inc_ref(v_title_1812_);
v_titleString_1813_ = lean_ctor_get(v_x_1810_, 1);
lean_inc_ref(v_titleString_1813_);
v_metadata_1814_ = lean_ctor_get(v_x_1810_, 2);
lean_inc(v_metadata_1814_);
v_content_1815_ = lean_ctor_get(v_x_1810_, 3);
lean_inc_ref(v_content_1815_);
v_subParts_1816_ = lean_ctor_get(v_x_1810_, 4);
lean_inc_ref(v_subParts_1816_);
lean_dec_ref(v_x_1810_);
v_title_1817_ = lean_ctor_get(v_x_1811_, 0);
lean_inc_ref(v_title_1817_);
v_titleString_1818_ = lean_ctor_get(v_x_1811_, 1);
lean_inc_ref(v_titleString_1818_);
v_metadata_1819_ = lean_ctor_get(v_x_1811_, 2);
lean_inc(v_metadata_1819_);
v_content_1820_ = lean_ctor_get(v_x_1811_, 3);
lean_inc_ref(v_content_1820_);
v_subParts_1821_ = lean_ctor_get(v_x_1811_, 4);
lean_inc_ref(v_subParts_1821_);
lean_dec_ref(v_x_1811_);
v___x_1822_ = lean_array_get_size(v_title_1812_);
v___x_1823_ = lean_array_get_size(v_title_1817_);
v___x_1824_ = lean_nat_dec_eq(v___x_1822_, v___x_1823_);
if (v___x_1824_ == 0)
{
lean_dec_ref(v_subParts_1821_);
lean_dec_ref(v_content_1820_);
lean_dec(v_metadata_1819_);
lean_dec_ref(v_titleString_1818_);
lean_dec_ref(v_title_1817_);
lean_dec_ref(v_subParts_1816_);
lean_dec_ref(v_content_1815_);
lean_dec(v_metadata_1814_);
lean_dec_ref(v_titleString_1813_);
lean_dec_ref(v_title_1812_);
lean_dec_ref(v_inst_1809_);
lean_dec_ref(v_inst_1808_);
lean_dec_ref(v_inst_1807_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
lean_inc_ref(v_inst_1809_);
lean_inc_ref(v_inst_1808_);
lean_inc_ref_n(v_inst_1807_, 2);
v___x_1825_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___redArg___boxed), 5, 3);
lean_closure_set(v___x_1825_, 0, v_inst_1807_);
lean_closure_set(v___x_1825_, 1, v_inst_1808_);
lean_closure_set(v___x_1825_, 2, v_inst_1809_);
v___x_1826_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1826_, 0, lean_box(0));
lean_closure_set(v___x_1826_, 1, v_inst_1807_);
v___x_1827_ = l_Array_isEqvAux___redArg(v_title_1812_, v_title_1817_, v___x_1826_, v___x_1822_);
lean_dec_ref(v_title_1817_);
lean_dec_ref(v_title_1812_);
if (v___x_1827_ == 0)
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v_subParts_1821_);
lean_dec_ref(v_content_1820_);
lean_dec(v_metadata_1819_);
lean_dec_ref(v_titleString_1818_);
lean_dec_ref(v_subParts_1816_);
lean_dec_ref(v_content_1815_);
lean_dec(v_metadata_1814_);
lean_dec_ref(v_titleString_1813_);
lean_dec_ref(v_inst_1809_);
lean_dec_ref(v_inst_1808_);
lean_dec_ref(v_inst_1807_);
return v___x_1827_;
}
else
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_string_dec_eq(v_titleString_1813_, v_titleString_1818_);
lean_dec_ref(v_titleString_1818_);
lean_dec_ref(v_titleString_1813_);
if (v___x_1828_ == 0)
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v_subParts_1821_);
lean_dec_ref(v_content_1820_);
lean_dec(v_metadata_1819_);
lean_dec_ref(v_subParts_1816_);
lean_dec_ref(v_content_1815_);
lean_dec(v_metadata_1814_);
lean_dec_ref(v_inst_1809_);
lean_dec_ref(v_inst_1808_);
lean_dec_ref(v_inst_1807_);
return v___x_1828_;
}
else
{
uint8_t v___x_1829_; 
v___x_1829_ = l_Option_instBEq_beq___redArg(v_inst_1809_, v_metadata_1814_, v_metadata_1819_);
if (v___x_1829_ == 0)
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v_subParts_1821_);
lean_dec_ref(v_content_1820_);
lean_dec_ref(v_subParts_1816_);
lean_dec_ref(v_content_1815_);
lean_dec_ref(v_inst_1808_);
lean_dec_ref(v_inst_1807_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1830_ = lean_array_get_size(v_content_1815_);
v___x_1831_ = lean_array_get_size(v_content_1820_);
v___x_1832_ = lean_nat_dec_eq(v___x_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v_subParts_1821_);
lean_dec_ref(v_content_1820_);
lean_dec_ref(v_subParts_1816_);
lean_dec_ref(v_content_1815_);
lean_dec_ref(v_inst_1808_);
lean_dec_ref(v_inst_1807_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1833_, 0, lean_box(0));
lean_closure_set(v___x_1833_, 1, lean_box(0));
lean_closure_set(v___x_1833_, 2, v_inst_1807_);
lean_closure_set(v___x_1833_, 3, v_inst_1808_);
v___x_1834_ = l_Array_isEqvAux___redArg(v_content_1815_, v_content_1820_, v___x_1833_, v___x_1830_);
lean_dec_ref(v_content_1820_);
lean_dec_ref(v_content_1815_);
if (v___x_1834_ == 0)
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v_subParts_1821_);
lean_dec_ref(v_subParts_1816_);
return v___x_1834_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_array_get_size(v_subParts_1816_);
v___x_1836_ = lean_array_get_size(v_subParts_1821_);
v___x_1837_ = lean_nat_dec_eq(v___x_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v_subParts_1821_);
lean_dec_ref(v_subParts_1816_);
return v___x_1837_;
}
else
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Array_isEqvAux___redArg(v_subParts_1816_, v_subParts_1821_, v___x_1825_, v___x_1835_);
lean_dec_ref(v_subParts_1821_);
lean_dec_ref(v_subParts_1816_);
return v___x_1838_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq(lean_object* v_i_1839_, lean_object* v_b_1840_, lean_object* v_p_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_){
_start:
{
uint8_t v___x_1847_; 
v___x_1847_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1842_, v_inst_1843_, v_inst_1844_, v_x_1845_, v_x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___boxed(lean_object* v_i_1848_, lean_object* v_b_1849_, lean_object* v_p_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
uint8_t v_res_1856_; lean_object* v_r_1857_; 
v_res_1856_ = l_Lean_Doc_instBEqPart_beq(v_i_1848_, v_b_1849_, v_p_1850_, v_inst_1851_, v_inst_1852_, v_inst_1853_, v_x_1854_, v_x_1855_);
v_r_1857_ = lean_box(v_res_1856_);
return v_r_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart___redArg(lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1861_, 0, lean_box(0));
lean_closure_set(v___x_1861_, 1, lean_box(0));
lean_closure_set(v___x_1861_, 2, lean_box(0));
lean_closure_set(v___x_1861_, 3, v_inst_1858_);
lean_closure_set(v___x_1861_, 4, v_inst_1859_);
lean_closure_set(v___x_1861_, 5, v_inst_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart(lean_object* v_i_1862_, lean_object* v_b_1863_, lean_object* v_p_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1868_, 0, lean_box(0));
lean_closure_set(v___x_1868_, 1, lean_box(0));
lean_closure_set(v___x_1868_, 2, lean_box(0));
lean_closure_set(v___x_1868_, 3, v_inst_1865_);
lean_closure_set(v___x_1868_, 4, v_inst_1866_);
lean_closure_set(v___x_1868_, 5, v_inst_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___redArg___boxed(lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
uint8_t v_res_1874_; lean_object* v_r_1875_; 
v_res_1874_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1869_, v_inst_1870_, v_inst_1871_, v_x_1872_, v_x_1873_);
v_r_1875_ = lean_box(v_res_1874_);
return v_r_1875_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord___redArg(lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_){
_start:
{
lean_object* v_title_1881_; lean_object* v_titleString_1882_; lean_object* v_metadata_1883_; lean_object* v_content_1884_; lean_object* v_subParts_1885_; lean_object* v_title_1886_; lean_object* v_titleString_1887_; lean_object* v_metadata_1888_; lean_object* v_content_1889_; lean_object* v_subParts_1890_; lean_object* v___x_1891_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v_title_1881_ = lean_ctor_get(v_x_1879_, 0);
lean_inc_ref(v_title_1881_);
v_titleString_1882_ = lean_ctor_get(v_x_1879_, 1);
lean_inc_ref(v_titleString_1882_);
v_metadata_1883_ = lean_ctor_get(v_x_1879_, 2);
lean_inc(v_metadata_1883_);
v_content_1884_ = lean_ctor_get(v_x_1879_, 3);
lean_inc_ref(v_content_1884_);
v_subParts_1885_ = lean_ctor_get(v_x_1879_, 4);
lean_inc_ref(v_subParts_1885_);
lean_dec_ref(v_x_1879_);
v_title_1886_ = lean_ctor_get(v_x_1880_, 0);
lean_inc_ref(v_title_1886_);
v_titleString_1887_ = lean_ctor_get(v_x_1880_, 1);
lean_inc_ref(v_titleString_1887_);
v_metadata_1888_ = lean_ctor_get(v_x_1880_, 2);
lean_inc(v_metadata_1888_);
v_content_1889_ = lean_ctor_get(v_x_1880_, 3);
lean_inc_ref(v_content_1889_);
v_subParts_1890_ = lean_ctor_get(v_x_1880_, 4);
lean_inc_ref(v_subParts_1890_);
lean_dec_ref(v_x_1880_);
lean_inc_ref(v_inst_1878_);
lean_inc_ref(v_inst_1877_);
lean_inc_ref_n(v_inst_1876_, 2);
v___x_1891_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___redArg___boxed), 5, 3);
lean_closure_set(v___x_1891_, 0, v_inst_1876_);
lean_closure_set(v___x_1891_, 1, v_inst_1877_);
lean_closure_set(v___x_1891_, 2, v_inst_1878_);
v___x_1896_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1896_, 0, lean_box(0));
lean_closure_set(v___x_1896_, 1, v_inst_1876_);
v___x_1897_ = l_Array_compareLex___redArg(v___x_1896_, v_title_1881_, v_title_1886_);
lean_dec_ref(v_title_1886_);
lean_dec_ref(v_title_1881_);
if (v___x_1897_ == 1)
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_string_compare(v_titleString_1882_, v_titleString_1887_);
lean_dec_ref(v_titleString_1887_);
lean_dec_ref(v_titleString_1882_);
if (v___x_1898_ == 1)
{
if (lean_obj_tag(v_metadata_1883_) == 0)
{
lean_dec_ref(v_inst_1878_);
if (lean_obj_tag(v_metadata_1888_) == 0)
{
goto v___jp_1892_;
}
else
{
uint8_t v___x_1899_; 
lean_dec_ref_known(v_metadata_1888_, 1);
lean_dec_ref(v___x_1891_);
lean_dec_ref(v_subParts_1890_);
lean_dec_ref(v_content_1889_);
lean_dec_ref(v_subParts_1885_);
lean_dec_ref(v_content_1884_);
lean_dec_ref(v_inst_1877_);
lean_dec_ref(v_inst_1876_);
v___x_1899_ = 0;
return v___x_1899_;
}
}
else
{
if (lean_obj_tag(v_metadata_1888_) == 0)
{
uint8_t v___x_1900_; 
lean_dec_ref_known(v_metadata_1883_, 1);
lean_dec_ref(v___x_1891_);
lean_dec_ref(v_subParts_1890_);
lean_dec_ref(v_content_1889_);
lean_dec_ref(v_subParts_1885_);
lean_dec_ref(v_content_1884_);
lean_dec_ref(v_inst_1878_);
lean_dec_ref(v_inst_1877_);
lean_dec_ref(v_inst_1876_);
v___x_1900_ = 2;
return v___x_1900_;
}
else
{
lean_object* v_val_1901_; lean_object* v_val_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v_val_1901_ = lean_ctor_get(v_metadata_1883_, 0);
lean_inc(v_val_1901_);
lean_dec_ref_known(v_metadata_1883_, 1);
v_val_1902_ = lean_ctor_get(v_metadata_1888_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v_metadata_1888_, 1);
v___x_1903_ = lean_apply_2(v_inst_1878_, v_val_1901_, v_val_1902_);
v___x_1904_ = lean_unbox(v___x_1903_);
if (v___x_1904_ == 1)
{
goto v___jp_1892_;
}
else
{
uint8_t v___x_1905_; 
lean_dec_ref(v___x_1891_);
lean_dec_ref(v_subParts_1890_);
lean_dec_ref(v_content_1889_);
lean_dec_ref(v_subParts_1885_);
lean_dec_ref(v_content_1884_);
lean_dec_ref(v_inst_1877_);
lean_dec_ref(v_inst_1876_);
v___x_1905_ = lean_unbox(v___x_1903_);
return v___x_1905_;
}
}
}
}
else
{
lean_dec_ref(v___x_1891_);
lean_dec_ref(v_subParts_1890_);
lean_dec_ref(v_content_1889_);
lean_dec(v_metadata_1888_);
lean_dec_ref(v_subParts_1885_);
lean_dec_ref(v_content_1884_);
lean_dec(v_metadata_1883_);
lean_dec_ref(v_inst_1878_);
lean_dec_ref(v_inst_1877_);
lean_dec_ref(v_inst_1876_);
return v___x_1898_;
}
}
else
{
lean_dec_ref(v___x_1891_);
lean_dec_ref(v_subParts_1890_);
lean_dec_ref(v_content_1889_);
lean_dec(v_metadata_1888_);
lean_dec_ref(v_titleString_1887_);
lean_dec_ref(v_subParts_1885_);
lean_dec_ref(v_content_1884_);
lean_dec(v_metadata_1883_);
lean_dec_ref(v_titleString_1882_);
lean_dec_ref(v_inst_1878_);
lean_dec_ref(v_inst_1877_);
lean_dec_ref(v_inst_1876_);
return v___x_1897_;
}
v___jp_1892_:
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1893_, 0, lean_box(0));
lean_closure_set(v___x_1893_, 1, lean_box(0));
lean_closure_set(v___x_1893_, 2, v_inst_1876_);
lean_closure_set(v___x_1893_, 3, v_inst_1877_);
v___x_1894_ = l_Array_compareLex___redArg(v___x_1893_, v_content_1884_, v_content_1889_);
lean_dec_ref(v_content_1889_);
lean_dec_ref(v_content_1884_);
if (v___x_1894_ == 1)
{
uint8_t v___x_1895_; 
v___x_1895_ = l_Array_compareLex___redArg(v___x_1891_, v_subParts_1885_, v_subParts_1890_);
lean_dec_ref(v_subParts_1890_);
lean_dec_ref(v_subParts_1885_);
if (v___x_1895_ == 1)
{
return v___x_1895_;
}
else
{
return v___x_1895_;
}
}
else
{
lean_dec_ref(v___x_1891_);
lean_dec_ref(v_subParts_1890_);
lean_dec_ref(v_subParts_1885_);
return v___x_1894_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord(lean_object* v_i_1906_, lean_object* v_b_1907_, lean_object* v_p_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_inst_1911_, lean_object* v_x_1912_, lean_object* v_x_1913_){
_start:
{
uint8_t v___x_1914_; 
v___x_1914_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1909_, v_inst_1910_, v_inst_1911_, v_x_1912_, v_x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___boxed(lean_object* v_i_1915_, lean_object* v_b_1916_, lean_object* v_p_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_inst_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_){
_start:
{
uint8_t v_res_1923_; lean_object* v_r_1924_; 
v_res_1923_ = l_Lean_Doc_instOrdPart_ord(v_i_1915_, v_b_1916_, v_p_1917_, v_inst_1918_, v_inst_1919_, v_inst_1920_, v_x_1921_, v_x_1922_);
v_r_1924_ = lean_box(v_res_1923_);
return v_r_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart___redArg(lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_inst_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1928_, 0, lean_box(0));
lean_closure_set(v___x_1928_, 1, lean_box(0));
lean_closure_set(v___x_1928_, 2, lean_box(0));
lean_closure_set(v___x_1928_, 3, v_inst_1925_);
lean_closure_set(v___x_1928_, 4, v_inst_1926_);
lean_closure_set(v___x_1928_, 5, v_inst_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart(lean_object* v_i_1929_, lean_object* v_b_1930_, lean_object* v_p_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1935_, 0, lean_box(0));
lean_closure_set(v___x_1935_, 1, lean_box(0));
lean_closure_set(v___x_1935_, 2, lean_box(0));
lean_closure_set(v___x_1935_, 3, v_inst_1932_);
lean_closure_set(v___x_1935_, 4, v_inst_1933_);
lean_closure_set(v___x_1935_, 5, v_inst_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_unsigned_to_nat(9u);
v___x_1946_ = lean_nat_to_int(v___x_1945_);
return v___x_1946_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = lean_unsigned_to_nat(15u);
v___x_1951_ = lean_nat_to_int(v___x_1950_);
return v___x_1951_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = lean_unsigned_to_nat(11u);
v___x_1959_ = lean_nat_to_int(v___x_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg___boxed(lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_inst_1965_, lean_object* v_x_1966_, lean_object* v_prec_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_1963_, v_inst_1964_, v_inst_1965_, v_x_1966_, v_prec_1967_);
lean_dec(v_prec_1967_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg(lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_x_1972_, lean_object* v_prec_1973_){
_start:
{
lean_object* v_title_1974_; lean_object* v_titleString_1975_; lean_object* v_metadata_1976_; lean_object* v_content_1977_; lean_object* v_subParts_1978_; lean_object* v_localinst_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_title_1974_ = lean_ctor_get(v_x_1972_, 0);
lean_inc_ref(v_title_1974_);
v_titleString_1975_ = lean_ctor_get(v_x_1972_, 1);
lean_inc_ref(v_titleString_1975_);
v_metadata_1976_ = lean_ctor_get(v_x_1972_, 2);
lean_inc(v_metadata_1976_);
v_content_1977_ = lean_ctor_get(v_x_1972_, 3);
lean_inc_ref(v_content_1977_);
v_subParts_1978_ = lean_ctor_get(v_x_1972_, 4);
lean_inc_ref(v_subParts_1978_);
lean_dec_ref(v_x_1972_);
lean_inc_ref(v_inst_1971_);
lean_inc_ref(v_inst_1970_);
lean_inc_ref_n(v_inst_1969_, 2);
v_localinst_1979_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___redArg___boxed), 5, 3);
lean_closure_set(v_localinst_1979_, 0, v_inst_1969_);
lean_closure_set(v_localinst_1979_, 1, v_inst_1970_);
lean_closure_set(v_localinst_1979_, 2, v_inst_1971_);
v___x_1980_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1981_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__3));
v___x_1982_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4);
v___x_1983_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1983_, 0, lean_box(0));
lean_closure_set(v___x_1983_, 1, v_inst_1969_);
v___x_1984_ = l_Array_repr___redArg(v___x_1983_, v_title_1974_);
v___x_1985_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1982_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = 0;
v___x_1987_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*1, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1981_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = lean_box(1);
v___x_1992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__6));
v___x_1994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v___x_1980_);
v___x_1996_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7);
v___x_1997_ = l_String_quote(v_titleString_1975_);
v___x_1998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1996_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*1, v___x_1986_);
v___x_2001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1995_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v___x_1989_);
v___x_2003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_1991_);
v___x_2004_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__9));
v___x_2005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v___x_1980_);
v___x_2007_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_2008_ = lean_unsigned_to_nat(0u);
v___x_2009_ = l_Option_repr___redArg(v_inst_1971_, v_metadata_1976_, v___x_2008_);
v___x_2010_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2007_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*1, v___x_1986_);
v___x_2012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2006_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v___x_1989_);
v___x_2014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___x_1991_);
v___x_2015_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__11));
v___x_2016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v___x_1980_);
v___x_2018_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12);
v___x_2019_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_2019_, 0, lean_box(0));
lean_closure_set(v___x_2019_, 1, lean_box(0));
lean_closure_set(v___x_2019_, 2, v_inst_1969_);
lean_closure_set(v___x_2019_, 3, v_inst_1970_);
v___x_2020_ = l_Array_repr___redArg(v___x_2019_, v_content_1977_);
v___x_2021_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2018_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*1, v___x_1986_);
v___x_2023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2017_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
lean_ctor_set(v___x_2024_, 1, v___x_1989_);
v___x_2025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
lean_ctor_set(v___x_2025_, 1, v___x_1991_);
v___x_2026_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__14));
v___x_2027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_1980_);
v___x_2029_ = l_Array_repr___redArg(v_localinst_1979_, v_subParts_1978_);
v___x_2030_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2007_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*1, v___x_1986_);
v___x_2032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2028_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_2034_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_2035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
lean_ctor_set(v___x_2035_, 1, v___x_2032_);
v___x_2036_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_2037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2035_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2033_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
lean_ctor_set_uint8(v___x_2039_, sizeof(void*)*1, v___x_1986_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr(lean_object* v_i_2040_, lean_object* v_b_2041_, lean_object* v_p_2042_, lean_object* v_inst_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_x_2046_, lean_object* v_prec_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_2043_, v_inst_2044_, v_inst_2045_, v_x_2046_, v_prec_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___boxed(lean_object* v_i_2049_, lean_object* v_b_2050_, lean_object* v_p_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_x_2055_, lean_object* v_prec_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_Doc_instReprPart_repr(v_i_2049_, v_b_2050_, v_p_2051_, v_inst_2052_, v_inst_2053_, v_inst_2054_, v_x_2055_, v_prec_2056_);
lean_dec(v_prec_2056_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart___redArg(lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_inst_2060_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2061_, 0, lean_box(0));
lean_closure_set(v___x_2061_, 1, lean_box(0));
lean_closure_set(v___x_2061_, 2, lean_box(0));
lean_closure_set(v___x_2061_, 3, v_inst_2058_);
lean_closure_set(v___x_2061_, 4, v_inst_2059_);
lean_closure_set(v___x_2061_, 5, v_inst_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart(lean_object* v_i_2062_, lean_object* v_b_2063_, lean_object* v_p_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_inst_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2068_, 0, lean_box(0));
lean_closure_set(v___x_2068_, 1, lean_box(0));
lean_closure_set(v___x_2068_, 2, lean_box(0));
lean_closure_set(v___x_2068_, 3, v_inst_2065_);
lean_closure_set(v___x_2068_, 4, v_inst_2066_);
lean_closure_set(v___x_2068_, 5, v_inst_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg(){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = ((lean_object*)(l_Lean_Doc_instInhabitedPart_default___redArg___closed__0));
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg___boxed(lean_object* v___dummy_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_Doc_instInhabitedPart_default___redArg();
return v_res_2076_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedPart_default___closed__0(void){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Doc_instInhabitedPart_default___redArg();
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default(lean_object* v_i_2078_, lean_object* v_b_2079_, lean_object* v_p_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg(){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg___boxed(lean_object* v___dummy_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_Doc_instInhabitedPart___redArg();
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart(lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg(lean_object* v_x_2090_){
_start:
{
lean_inc_ref(v_x_2090_);
return v_x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg___boxed(lean_object* v_x_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Doc_Part_cast___redArg(v_x_2091_);
lean_dec_ref(v_x_2091_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast(lean_object* v_i_2093_, lean_object* v_i_x27_2094_, lean_object* v_b_2095_, lean_object* v_b_x27_2096_, lean_object* v_p_2097_, lean_object* v_p_x27_2098_, lean_object* v_inlines__eq_2099_, lean_object* v_blocks__eq_2100_, lean_object* v_metadata__eq_2101_, lean_object* v_x_2102_){
_start:
{
lean_inc_ref(v_x_2102_);
return v_x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___boxed(lean_object* v_i_2103_, lean_object* v_i_x27_2104_, lean_object* v_b_2105_, lean_object* v_b_x27_2106_, lean_object* v_p_2107_, lean_object* v_p_x27_2108_, lean_object* v_inlines__eq_2109_, lean_object* v_blocks__eq_2110_, lean_object* v_metadata__eq_2111_, lean_object* v_x_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_Doc_Part_cast(v_i_2103_, v_i_x27_2104_, v_b_2105_, v_b_x27_2106_, v_p_2107_, v_p_x27_2108_, v_inlines__eq_2109_, v_blocks__eq_2110_, v_metadata__eq_2111_, v_x_2112_);
lean_dec_ref(v_x_2112_);
return v_res_2113_;
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
