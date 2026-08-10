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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
static const lean_string_object l_Lean_Doc_instInhabitedInline_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Doc_instInhabitedInline_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedInline_default___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instInhabitedInline_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedInline_default___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedInline_default___closed__1 = (const lean_object*)&l_Lean_Doc_instInhabitedInline_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default(lean_object*);
static lean_once_cell_t l_Lean_Doc_instInhabitedInline___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instInhabitedInline___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instAppendInline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instAppendInline___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instAppendInline___closed__0 = (const lean_object*)&l_Lean_Doc_instAppendInline___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline(lean_object*);
static const lean_array_object l_Lean_Doc_Inline_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_Inline_empty___closed__0 = (const lean_object*)&l_Lean_Doc_Inline_empty___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Inline_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Doc_Inline_empty___closed__0_value)}};
static const lean_object* l_Lean_Doc_Inline_empty___closed__1 = (const lean_object*)&l_Lean_Doc_Inline_empty___closed__1_value;
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
static const lean_array_object l_Lean_Doc_instInhabitedListItem_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_instInhabitedListItem_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedListItem_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default(lean_object*);
static lean_once_cell_t l_Lean_Doc_instInhabitedListItem___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instInhabitedListItem___closed__0;
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
static const lean_ctor_object l_Lean_Doc_instInhabitedDescItem_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedListItem_default___closed__0_value),((lean_object*)&l_Lean_Doc_instInhabitedListItem_default___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedDescItem_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedDescItem_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_instInhabitedDescItem___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instInhabitedDescItem___closed__0;
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
static const lean_array_object l_Lean_Doc_instInhabitedBlock_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_instInhabitedBlock_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedBlock_default___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instInhabitedBlock_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedBlock_default___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedBlock_default___closed__1 = (const lean_object*)&l_Lean_Doc_instInhabitedBlock_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_instInhabitedBlock___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instInhabitedBlock___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock(lean_object*, lean_object*);
static const lean_array_object l_Lean_Doc_Block_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_Block_empty___closed__0 = (const lean_object*)&l_Lean_Doc_Block_empty___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Block_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Doc_Block_empty___closed__0_value)}};
static const lean_object* l_Lean_Doc_Block_empty___closed__1 = (const lean_object*)&l_Lean_Doc_Block_empty___closed__1_value;
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
static const lean_ctor_object l_Lean_Doc_instInhabitedPart_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedBlock_default___closed__0_value),((lean_object*)&l_Lean_Doc_instInhabitedInline_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instInhabitedBlock_default___closed__0_value),((lean_object*)&l_Lean_Doc_instInhabitedBlock_default___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedPart_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedPart_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_instInhabitedPart___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instInhabitedPart___closed__0;
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
uint8_t v_x_121__boxed_84_; lean_object* v_res_85_; 
v_x_121__boxed_84_ = lean_unbox(v_x_82_);
v_res_85_ = l_Lean_Doc_instReprMathMode_repr(v_x_121__boxed_84_, v_prec_83_);
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
uint8_t v_x_17__boxed_95_; uint8_t v_y_18__boxed_96_; uint8_t v_res_97_; lean_object* v_r_98_; 
v_x_17__boxed_95_ = lean_unbox(v_x_93_);
v_y_18__boxed_96_ = lean_unbox(v_y_94_);
v_res_97_ = l_Lean_Doc_instBEqMathMode_beq(v_x_17__boxed_95_, v_y_18__boxed_96_);
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
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_286_);
v___x_289_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_287_);
v___x_290_ = lean_nat_dec_eq(v___x_288_, v___x_289_);
lean_dec(v___x_289_);
lean_dec(v___x_288_);
if (v___x_290_ == 0)
{
lean_dec_ref(v_x_287_);
lean_dec_ref(v_x_286_);
lean_dec_ref(v_inst_285_);
return v___x_290_;
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
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default(lean_object* v_i_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = ((lean_object*)(l_Lean_Doc_instInhabitedInline_default___closed__1));
return v___x_774_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedInline___closed__0(void){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Doc_instInhabitedInline_default(lean_box(0));
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline(lean_object* v_a_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline___closed__0, &l_Lean_Doc_instInhabitedInline___closed__0_once, _init_l_Lean_Doc_instInhabitedInline___closed__0);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg(lean_object* v_x_778_){
_start:
{
lean_inc_ref(v_x_778_);
return v_x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg___boxed(lean_object* v_x_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Doc_Inline_cast___redArg(v_x_779_);
lean_dec_ref(v_x_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast(lean_object* v_i_781_, lean_object* v_i_x27_782_, lean_object* v_inlines__eq_783_, lean_object* v_x_784_){
_start:
{
lean_inc_ref(v_x_784_);
return v_x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___boxed(lean_object* v_i_785_, lean_object* v_i_x27_786_, lean_object* v_inlines__eq_787_, lean_object* v_x_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Doc_Inline_cast(v_i_785_, v_i_x27_786_, v_inlines__eq_787_, v_x_788_);
lean_dec_ref(v_x_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___lam__0(lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_790_) == 9)
{
lean_object* v_content_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_content_792_ = lean_ctor_get(v_x_790_, 0);
v___x_793_ = lean_array_get_size(v_content_792_);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_nat_dec_eq(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
if (lean_obj_tag(v_x_791_) == 9)
{
lean_object* v_content_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_806_; 
v_content_796_ = lean_ctor_get(v_x_791_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_791_);
if (v_isSharedCheck_806_ == 0)
{
v___x_798_ = v_x_791_;
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_content_796_);
lean_dec(v_x_791_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = lean_array_get_size(v_content_796_);
v___x_801_ = lean_nat_dec_eq(v___x_800_, v___x_794_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_inc_ref(v_content_792_);
lean_dec_ref_known(v_x_790_, 1);
v___x_802_ = l_Array_append___redArg(v_content_792_, v_content_796_);
lean_dec_ref(v_content_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_802_);
v___x_804_ = v___x_798_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
lean_del_object(v___x_798_);
lean_dec_ref(v_content_796_);
return v_x_790_;
}
}
}
else
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
lean_inc_ref(v_content_792_);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_790_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_x_790_, 0);
lean_dec(v_unused_815_);
v___x_808_ = v_x_790_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_dec(v_x_790_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_array_push(v_content_792_, v_x_791_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_812_ = v___x_808_;
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
}
}
else
{
lean_dec_ref_known(v_x_790_, 1);
return v_x_791_;
}
}
else
{
if (lean_obj_tag(v_x_791_) == 9)
{
lean_object* v_content_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_830_; 
v_content_816_ = lean_ctor_get(v_x_791_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_791_);
if (v_isSharedCheck_830_ == 0)
{
v___x_818_ = v_x_791_;
v_isShared_819_ = v_isSharedCheck_830_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_content_816_);
lean_dec(v_x_791_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_830_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_820_ = lean_array_get_size(v_content_816_);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_nat_dec_eq(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_mk_empty_array_with_capacity(v___x_823_);
v___x_825_ = lean_array_push(v___x_824_, v_x_790_);
v___x_826_ = l_Array_append___redArg(v___x_825_, v_content_816_);
lean_dec_ref(v_content_816_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_826_);
v___x_828_ = v___x_818_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
lean_del_object(v___x_818_);
lean_dec_ref(v_content_816_);
return v_x_790_;
}
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_831_ = lean_unsigned_to_nat(2u);
v___x_832_ = lean_mk_empty_array_with_capacity(v___x_831_);
v___x_833_ = lean_array_push(v___x_832_, v_x_790_);
v___x_834_ = lean_array_push(v___x_833_, v_x_791_);
v___x_835_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline(lean_object* v_i_837_){
_start:
{
lean_object* v___f_838_; 
v___f_838_ = ((lean_object*)(l_Lean_Doc_instAppendInline___closed__0));
return v___f_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty(lean_object* v_i_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = ((lean_object*)(l_Lean_Doc_Inline_empty___closed__1));
return v___x_844_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(12u);
v___x_859_ = lean_nat_to_int(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__0));
v___x_862_ = lean_string_length(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9);
v___x_864_ = lean_nat_to_int(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___redArg(lean_object* v_inst_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_871_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__6));
v___x_872_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_873_ = l_Array_repr___redArg(v_inst_869_, v_x_870_);
v___x_874_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = 0;
v___x_876_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*1, v___x_875_);
v___x_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_871_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_879_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_877_);
v___x_881_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_878_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1, v___x_875_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr(lean_object* v_00_u03b1_885_, lean_object* v_inst_886_, lean_object* v_x_887_, lean_object* v_prec_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_Doc_instReprListItem_repr___redArg(v_inst_886_, v_x_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___boxed(lean_object* v_00_u03b1_890_, lean_object* v_inst_891_, lean_object* v_x_892_, lean_object* v_prec_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Doc_instReprListItem_repr(v_00_u03b1_890_, v_inst_891_, v_x_892_, v_prec_893_);
lean_dec(v_prec_893_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem___redArg(lean_object* v_inst_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_896_, 0, lean_box(0));
lean_closure_set(v___x_896_, 1, v_inst_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem(lean_object* v_00_u03b1_897_, lean_object* v_inst_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_899_, 0, lean_box(0));
lean_closure_set(v___x_899_, 1, v_inst_898_);
return v___x_899_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq___redArg(lean_object* v_inst_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_903_ = lean_array_get_size(v_x_901_);
v___x_904_ = lean_array_get_size(v_x_902_);
v___x_905_ = lean_nat_dec_eq(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
lean_dec_ref(v_inst_900_);
return v___x_905_;
}
else
{
uint8_t v___x_906_; 
v___x_906_ = l_Array_isEqvAux___redArg(v_x_901_, v_x_902_, v_inst_900_, v___x_903_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___redArg___boxed(lean_object* v_inst_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
uint8_t v_res_910_; lean_object* v_r_911_; 
v_res_910_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_907_, v_x_908_, v_x_909_);
lean_dec_ref(v_x_909_);
lean_dec_ref(v_x_908_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq(lean_object* v_00_u03b1_912_, lean_object* v_inst_913_, lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_913_, v_x_914_, v_x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___boxed(lean_object* v_00_u03b1_917_, lean_object* v_inst_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
uint8_t v_res_921_; lean_object* v_r_922_; 
v_res_921_ = l_Lean_Doc_instBEqListItem_beq(v_00_u03b1_917_, v_inst_918_, v_x_919_, v_x_920_);
lean_dec_ref(v_x_920_);
lean_dec_ref(v_x_919_);
v_r_922_ = lean_box(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem___redArg(lean_object* v_inst_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_924_, 0, lean_box(0));
lean_closure_set(v___x_924_, 1, v_inst_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem(lean_object* v_00_u03b1_925_, lean_object* v_inst_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_927_, 0, lean_box(0));
lean_closure_set(v___x_927_, 1, v_inst_926_);
return v___x_927_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord___redArg(lean_object* v_inst_928_, lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = l_Array_compareLex___redArg(v_inst_928_, v_x_929_, v_x_930_);
if (v___x_931_ == 1)
{
return v___x_931_;
}
else
{
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___redArg___boxed(lean_object* v_inst_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
uint8_t v_res_935_; lean_object* v_r_936_; 
v_res_935_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_932_, v_x_933_, v_x_934_);
lean_dec_ref(v_x_934_);
lean_dec_ref(v_x_933_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord(lean_object* v_00_u03b1_937_, lean_object* v_inst_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_938_, v_x_939_, v_x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___boxed(lean_object* v_00_u03b1_942_, lean_object* v_inst_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
uint8_t v_res_946_; lean_object* v_r_947_; 
v_res_946_ = l_Lean_Doc_instOrdListItem_ord(v_00_u03b1_942_, v_inst_943_, v_x_944_, v_x_945_);
lean_dec_ref(v_x_945_);
lean_dec_ref(v_x_944_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem___redArg(lean_object* v_inst_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_949_, 0, lean_box(0));
lean_closure_set(v___x_949_, 1, v_inst_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem(lean_object* v_00_u03b1_950_, lean_object* v_inst_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_952_, 0, lean_box(0));
lean_closure_set(v___x_952_, 1, v_inst_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default(lean_object* v_00_u03b1_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = ((lean_object*)(l_Lean_Doc_instInhabitedListItem_default___closed__0));
return v___x_956_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedListItem___closed__0(void){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Doc_instInhabitedListItem_default(lean_box(0));
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem(lean_object* v_a_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem___closed__0, &l_Lean_Doc_instInhabitedListItem___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem___closed__0);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_unsigned_to_nat(8u);
v___x_970_ = lean_nat_to_int(v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___redArg(lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v_x_979_){
_start:
{
lean_object* v_term_980_; lean_object* v_desc_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1013_; 
v_term_980_ = lean_ctor_get(v_x_979_, 0);
v_desc_981_ = lean_ctor_get(v_x_979_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_x_979_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_983_ = v_x_979_;
v_isShared_984_ = v_isSharedCheck_1013_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_desc_981_);
lean_inc(v_term_980_);
lean_dec(v_x_979_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1013_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_985_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_986_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__3));
v___x_987_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4);
v___x_988_ = l_Array_repr___redArg(v_inst_977_, v_term_980_);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 4);
lean_ctor_set(v___x_983_, 1, v___x_988_);
lean_ctor_set(v___x_983_, 0, v___x_987_);
v___x_990_ = v___x_983_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_988_);
v___x_990_ = v_reuseFailAlloc_1012_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_991_ = 0;
v___x_992_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*1, v___x_991_);
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_986_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_box(1);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__8));
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_985_);
v___x_1001_ = l_Array_repr___redArg(v_inst_978_, v_desc_981_);
v___x_1002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_987_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set_uint8(v___x_1003_, sizeof(void*)*1, v___x_991_);
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1000_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_1006_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1004_);
v___x_1008_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1005_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set_uint8(v___x_1011_, sizeof(void*)*1, v___x_991_);
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_x_1018_, lean_object* v_prec_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_Doc_instReprDescItem_repr___redArg(v_inst_1016_, v_inst_1017_, v_x_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___boxed(lean_object* v_00_u03b1_1021_, lean_object* v_00_u03b2_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_x_1025_, lean_object* v_prec_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Doc_instReprDescItem_repr(v_00_u03b1_1021_, v_00_u03b2_1022_, v_inst_1023_, v_inst_1024_, v_x_1025_, v_prec_1026_);
lean_dec(v_prec_1026_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem___redArg(lean_object* v_inst_1028_, lean_object* v_inst_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1030_, 0, lean_box(0));
lean_closure_set(v___x_1030_, 1, lean_box(0));
lean_closure_set(v___x_1030_, 2, v_inst_1028_);
lean_closure_set(v___x_1030_, 3, v_inst_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem(lean_object* v_00_u03b1_1031_, lean_object* v_00_u03b2_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1035_, 0, lean_box(0));
lean_closure_set(v___x_1035_, 1, lean_box(0));
lean_closure_set(v___x_1035_, 2, v_inst_1033_);
lean_closure_set(v___x_1035_, 3, v_inst_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq___redArg(lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_){
_start:
{
lean_object* v_term_1040_; lean_object* v_desc_1041_; lean_object* v_term_1042_; lean_object* v_desc_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_term_1040_ = lean_ctor_get(v_x_1038_, 0);
v_desc_1041_ = lean_ctor_get(v_x_1038_, 1);
v_term_1042_ = lean_ctor_get(v_x_1039_, 0);
v_desc_1043_ = lean_ctor_get(v_x_1039_, 1);
v___x_1044_ = lean_array_get_size(v_term_1040_);
v___x_1045_ = lean_array_get_size(v_term_1042_);
v___x_1046_ = lean_nat_dec_eq(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_dec_ref(v_inst_1037_);
lean_dec_ref(v_inst_1036_);
return v___x_1046_;
}
else
{
uint8_t v___x_1047_; 
v___x_1047_ = l_Array_isEqvAux___redArg(v_term_1040_, v_term_1042_, v_inst_1036_, v___x_1044_);
if (v___x_1047_ == 0)
{
lean_dec_ref(v_inst_1037_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1048_ = lean_array_get_size(v_desc_1041_);
v___x_1049_ = lean_array_get_size(v_desc_1043_);
v___x_1050_ = lean_nat_dec_eq(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_dec_ref(v_inst_1037_);
return v___x_1050_;
}
else
{
uint8_t v___x_1051_; 
v___x_1051_ = l_Array_isEqvAux___redArg(v_desc_1041_, v_desc_1043_, v_inst_1037_, v___x_1048_);
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___redArg___boxed(lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
uint8_t v_res_1056_; lean_object* v_r_1057_; 
v_res_1056_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1052_, v_inst_1053_, v_x_1054_, v_x_1055_);
lean_dec_ref(v_x_1055_);
lean_dec_ref(v_x_1054_);
v_r_1057_ = lean_box(v_res_1056_);
return v_r_1057_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq(lean_object* v_00_u03b1_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
uint8_t v___x_1064_; 
v___x_1064_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1060_, v_inst_1061_, v_x_1062_, v_x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_00_u03b2_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Lean_Doc_instBEqDescItem_beq(v_00_u03b1_1065_, v_00_u03b2_1066_, v_inst_1067_, v_inst_1068_, v_x_1069_, v_x_1070_);
lean_dec_ref(v_x_1070_);
lean_dec_ref(v_x_1069_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem___redArg(lean_object* v_inst_1073_, lean_object* v_inst_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1075_, 0, lean_box(0));
lean_closure_set(v___x_1075_, 1, lean_box(0));
lean_closure_set(v___x_1075_, 2, v_inst_1073_);
lean_closure_set(v___x_1075_, 3, v_inst_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem(lean_object* v_00_u03b1_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1080_, 0, lean_box(0));
lean_closure_set(v___x_1080_, 1, lean_box(0));
lean_closure_set(v___x_1080_, 2, v_inst_1078_);
lean_closure_set(v___x_1080_, 3, v_inst_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord___redArg(lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v_term_1085_; lean_object* v_desc_1086_; lean_object* v_term_1087_; lean_object* v_desc_1088_; uint8_t v___x_1089_; 
v_term_1085_ = lean_ctor_get(v_x_1083_, 0);
v_desc_1086_ = lean_ctor_get(v_x_1083_, 1);
v_term_1087_ = lean_ctor_get(v_x_1084_, 0);
v_desc_1088_ = lean_ctor_get(v_x_1084_, 1);
v___x_1089_ = l_Array_compareLex___redArg(v_inst_1081_, v_term_1085_, v_term_1087_);
if (v___x_1089_ == 1)
{
uint8_t v___x_1090_; 
v___x_1090_ = l_Array_compareLex___redArg(v_inst_1082_, v_desc_1086_, v_desc_1088_);
if (v___x_1090_ == 1)
{
return v___x_1090_;
}
else
{
return v___x_1090_;
}
}
else
{
lean_dec_ref(v_inst_1082_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___redArg___boxed(lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_res_1095_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1091_, v_inst_1092_, v_x_1093_, v_x_1094_);
lean_dec_ref(v_x_1094_);
lean_dec_ref(v_x_1093_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord(lean_object* v_00_u03b1_1097_, lean_object* v_00_u03b2_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1099_, v_inst_1100_, v_x_1101_, v_x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___boxed(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_res_1110_ = l_Lean_Doc_instOrdDescItem_ord(v_00_u03b1_1104_, v_00_u03b2_1105_, v_inst_1106_, v_inst_1107_, v_x_1108_, v_x_1109_);
lean_dec_ref(v_x_1109_);
lean_dec_ref(v_x_1108_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem___redArg(lean_object* v_inst_1112_, lean_object* v_inst_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1114_, 0, lean_box(0));
lean_closure_set(v___x_1114_, 1, lean_box(0));
lean_closure_set(v___x_1114_, 2, v_inst_1112_);
lean_closure_set(v___x_1114_, 3, v_inst_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem(lean_object* v_00_u03b1_1115_, lean_object* v_00_u03b2_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1119_, 0, lean_box(0));
lean_closure_set(v___x_1119_, 1, lean_box(0));
lean_closure_set(v___x_1119_, 2, v_inst_1117_);
lean_closure_set(v___x_1119_, 3, v_inst_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default(lean_object* v_00_u03b1_1122_, lean_object* v_00_u03b2_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = ((lean_object*)(l_Lean_Doc_instInhabitedDescItem_default___closed__0));
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedDescItem___closed__0(void){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Doc_instInhabitedDescItem_default(lean_box(0), lean_box(0));
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem(lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem___closed__0, &l_Lean_Doc_instInhabitedDescItem___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem___closed__0);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg(lean_object* v_x_1129_){
_start:
{
switch(lean_obj_tag(v_x_1129_))
{
case 0:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_unsigned_to_nat(0u);
return v___x_1130_;
}
case 1:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_unsigned_to_nat(1u);
return v___x_1131_;
}
case 2:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_unsigned_to_nat(2u);
return v___x_1132_;
}
case 3:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_unsigned_to_nat(3u);
return v___x_1133_;
}
case 4:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_unsigned_to_nat(4u);
return v___x_1134_;
}
case 5:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_unsigned_to_nat(5u);
return v___x_1135_;
}
case 6:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_unsigned_to_nat(6u);
return v___x_1136_;
}
default: 
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_unsigned_to_nat(7u);
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg___boxed(lean_object* v_x_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1138_);
lean_dec_ref(v_x_1138_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx(lean_object* v_i_1140_, lean_object* v_b_1141_, lean_object* v_x_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___boxed(lean_object* v_i_1144_, lean_object* v_b_1145_, lean_object* v_x_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Doc_Block_ctorIdx(v_i_1144_, v_b_1145_, v_x_1146_);
lean_dec_ref(v_x_1146_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___redArg(lean_object* v_t_1148_, lean_object* v_k_1149_){
_start:
{
switch(lean_obj_tag(v_t_1148_))
{
case 3:
{
lean_object* v_start_1150_; lean_object* v_items_1151_; lean_object* v___x_1152_; 
v_start_1150_ = lean_ctor_get(v_t_1148_, 0);
lean_inc(v_start_1150_);
v_items_1151_ = lean_ctor_get(v_t_1148_, 1);
lean_inc_ref(v_items_1151_);
lean_dec_ref_known(v_t_1148_, 2);
v___x_1152_ = lean_apply_2(v_k_1149_, v_start_1150_, v_items_1151_);
return v___x_1152_;
}
case 7:
{
lean_object* v_container_1153_; lean_object* v_content_1154_; lean_object* v___x_1155_; 
v_container_1153_ = lean_ctor_get(v_t_1148_, 0);
lean_inc(v_container_1153_);
v_content_1154_ = lean_ctor_get(v_t_1148_, 1);
lean_inc_ref(v_content_1154_);
lean_dec_ref_known(v_t_1148_, 2);
v___x_1155_ = lean_apply_2(v_k_1149_, v_container_1153_, v_content_1154_);
return v___x_1155_;
}
default: 
{
lean_object* v_contents_1156_; lean_object* v___x_1157_; 
v_contents_1156_ = lean_ctor_get(v_t_1148_, 0);
lean_inc_ref(v_contents_1156_);
lean_dec_ref(v_t_1148_);
v___x_1157_ = lean_apply_1(v_k_1149_, v_contents_1156_);
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim(lean_object* v_i_1158_, lean_object* v_b_1159_, lean_object* v_motive__1_1160_, lean_object* v_ctorIdx_1161_, lean_object* v_t_1162_, lean_object* v_h_1163_, lean_object* v_k_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1162_, v_k_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___boxed(lean_object* v_i_1166_, lean_object* v_b_1167_, lean_object* v_motive__1_1168_, lean_object* v_ctorIdx_1169_, lean_object* v_t_1170_, lean_object* v_h_1171_, lean_object* v_k_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Doc_Block_ctorElim(v_i_1166_, v_b_1167_, v_motive__1_1168_, v_ctorIdx_1169_, v_t_1170_, v_h_1171_, v_k_1172_);
lean_dec(v_ctorIdx_1169_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim___redArg(lean_object* v_t_1174_, lean_object* v_para_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1174_, v_para_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim(lean_object* v_i_1177_, lean_object* v_b_1178_, lean_object* v_motive__1_1179_, lean_object* v_t_1180_, lean_object* v_h_1181_, lean_object* v_para_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1180_, v_para_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim___redArg(lean_object* v_t_1184_, lean_object* v_code_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1184_, v_code_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim(lean_object* v_i_1187_, lean_object* v_b_1188_, lean_object* v_motive__1_1189_, lean_object* v_t_1190_, lean_object* v_h_1191_, lean_object* v_code_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1190_, v_code_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim___redArg(lean_object* v_t_1194_, lean_object* v_ul_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1194_, v_ul_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim(lean_object* v_i_1197_, lean_object* v_b_1198_, lean_object* v_motive__1_1199_, lean_object* v_t_1200_, lean_object* v_h_1201_, lean_object* v_ul_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1200_, v_ul_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim___redArg(lean_object* v_t_1204_, lean_object* v_ol_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1204_, v_ol_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim(lean_object* v_i_1207_, lean_object* v_b_1208_, lean_object* v_motive__1_1209_, lean_object* v_t_1210_, lean_object* v_h_1211_, lean_object* v_ol_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1210_, v_ol_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim___redArg(lean_object* v_t_1214_, lean_object* v_dl_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1214_, v_dl_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim(lean_object* v_i_1217_, lean_object* v_b_1218_, lean_object* v_motive__1_1219_, lean_object* v_t_1220_, lean_object* v_h_1221_, lean_object* v_dl_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1220_, v_dl_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim___redArg(lean_object* v_t_1224_, lean_object* v_blockquote_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1224_, v_blockquote_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim(lean_object* v_i_1227_, lean_object* v_b_1228_, lean_object* v_motive__1_1229_, lean_object* v_t_1230_, lean_object* v_h_1231_, lean_object* v_blockquote_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1230_, v_blockquote_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim___redArg(lean_object* v_t_1234_, lean_object* v_concat_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1234_, v_concat_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim(lean_object* v_i_1237_, lean_object* v_b_1238_, lean_object* v_motive__1_1239_, lean_object* v_t_1240_, lean_object* v_h_1241_, lean_object* v_concat_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1240_, v_concat_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim___redArg(lean_object* v_t_1244_, lean_object* v_other_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1244_, v_other_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim(lean_object* v_i_1247_, lean_object* v_b_1248_, lean_object* v_motive__1_1249_, lean_object* v_t_1250_, lean_object* v_h_1251_, lean_object* v_other_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1250_, v_other_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___redArg___boxed(lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1254_, v_inst_1255_, v_x_1256_, v_x_1257_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq___redArg(lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v_localinst_1264_; lean_object* v_a_1266_; lean_object* v_b_1267_; 
lean_inc_ref(v_inst_1261_);
lean_inc_ref(v_inst_1260_);
v_localinst_1264_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1264_, 0, v_inst_1260_);
lean_closure_set(v_localinst_1264_, 1, v_inst_1261_);
switch(lean_obj_tag(v_x_1262_))
{
case 0:
{
lean_dec_ref(v_localinst_1264_);
lean_dec_ref(v_inst_1261_);
if (lean_obj_tag(v_x_1263_) == 0)
{
lean_object* v_contents_1272_; lean_object* v_contents_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v_contents_1272_ = lean_ctor_get(v_x_1262_, 0);
lean_inc_ref(v_contents_1272_);
lean_dec_ref_known(v_x_1262_, 1);
v_contents_1273_ = lean_ctor_get(v_x_1263_, 0);
lean_inc_ref(v_contents_1273_);
lean_dec_ref_known(v_x_1263_, 1);
v___x_1274_ = lean_array_get_size(v_contents_1272_);
v___x_1275_ = lean_array_get_size(v_contents_1273_);
v___x_1276_ = lean_nat_dec_eq(v___x_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec_ref(v_contents_1273_);
lean_dec_ref(v_contents_1272_);
lean_dec_ref(v_inst_1260_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1277_, 0, lean_box(0));
lean_closure_set(v___x_1277_, 1, v_inst_1260_);
v___x_1278_ = l_Array_isEqvAux___redArg(v_contents_1272_, v_contents_1273_, v___x_1277_, v___x_1274_);
lean_dec_ref(v_contents_1273_);
lean_dec_ref(v_contents_1272_);
return v___x_1278_;
}
}
else
{
uint8_t v___x_1279_; 
lean_dec_ref_known(v_x_1262_, 1);
lean_dec_ref(v_x_1263_);
lean_dec_ref(v_inst_1260_);
v___x_1279_ = 0;
return v___x_1279_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1264_);
lean_dec_ref(v_inst_1261_);
lean_dec_ref(v_inst_1260_);
if (lean_obj_tag(v_x_1263_) == 1)
{
lean_object* v_content_1280_; lean_object* v_content_1281_; uint8_t v___x_1282_; 
v_content_1280_ = lean_ctor_get(v_x_1262_, 0);
lean_inc_ref(v_content_1280_);
lean_dec_ref_known(v_x_1262_, 1);
v_content_1281_ = lean_ctor_get(v_x_1263_, 0);
lean_inc_ref(v_content_1281_);
lean_dec_ref_known(v_x_1263_, 1);
v___x_1282_ = lean_string_dec_eq(v_content_1280_, v_content_1281_);
lean_dec_ref(v_content_1281_);
lean_dec_ref(v_content_1280_);
return v___x_1282_;
}
else
{
uint8_t v___x_1283_; 
lean_dec_ref_known(v_x_1262_, 1);
lean_dec_ref(v_x_1263_);
v___x_1283_ = 0;
return v___x_1283_;
}
}
case 2:
{
lean_dec_ref(v_inst_1261_);
lean_dec_ref(v_inst_1260_);
if (lean_obj_tag(v_x_1263_) == 2)
{
lean_object* v_items_1284_; lean_object* v_items_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_items_1284_ = lean_ctor_get(v_x_1262_, 0);
lean_inc_ref(v_items_1284_);
lean_dec_ref_known(v_x_1262_, 1);
v_items_1285_ = lean_ctor_get(v_x_1263_, 0);
lean_inc_ref(v_items_1285_);
lean_dec_ref_known(v_x_1263_, 1);
v___x_1286_ = lean_array_get_size(v_items_1284_);
v___x_1287_ = lean_array_get_size(v_items_1285_);
v___x_1288_ = lean_nat_dec_eq(v___x_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_dec_ref(v_items_1285_);
lean_dec_ref(v_items_1284_);
lean_dec_ref(v_localinst_1264_);
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1289_, 0, lean_box(0));
lean_closure_set(v___x_1289_, 1, v_localinst_1264_);
v___x_1290_ = l_Array_isEqvAux___redArg(v_items_1284_, v_items_1285_, v___x_1289_, v___x_1286_);
lean_dec_ref(v_items_1285_);
lean_dec_ref(v_items_1284_);
return v___x_1290_;
}
}
else
{
uint8_t v___x_1291_; 
lean_dec_ref_known(v_x_1262_, 1);
lean_dec_ref(v_localinst_1264_);
lean_dec_ref(v_x_1263_);
v___x_1291_ = 0;
return v___x_1291_;
}
}
case 3:
{
lean_dec_ref(v_inst_1261_);
lean_dec_ref(v_inst_1260_);
if (lean_obj_tag(v_x_1263_) == 3)
{
lean_object* v_start_1292_; lean_object* v_items_1293_; lean_object* v_start_1294_; lean_object* v_items_1295_; uint8_t v___x_1296_; 
v_start_1292_ = lean_ctor_get(v_x_1262_, 0);
lean_inc(v_start_1292_);
v_items_1293_ = lean_ctor_get(v_x_1262_, 1);
lean_inc_ref(v_items_1293_);
lean_dec_ref_known(v_x_1262_, 2);
v_start_1294_ = lean_ctor_get(v_x_1263_, 0);
lean_inc(v_start_1294_);
v_items_1295_ = lean_ctor_get(v_x_1263_, 1);
lean_inc_ref(v_items_1295_);
lean_dec_ref_known(v_x_1263_, 2);
v___x_1296_ = lean_int_dec_eq(v_start_1292_, v_start_1294_);
lean_dec(v_start_1294_);
lean_dec(v_start_1292_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v_items_1295_);
lean_dec_ref(v_items_1293_);
lean_dec_ref(v_localinst_1264_);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1297_ = lean_array_get_size(v_items_1293_);
v___x_1298_ = lean_array_get_size(v_items_1295_);
v___x_1299_ = lean_nat_dec_eq(v___x_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_dec_ref(v_items_1295_);
lean_dec_ref(v_items_1293_);
lean_dec_ref(v_localinst_1264_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1300_, 0, lean_box(0));
lean_closure_set(v___x_1300_, 1, v_localinst_1264_);
v___x_1301_ = l_Array_isEqvAux___redArg(v_items_1293_, v_items_1295_, v___x_1300_, v___x_1297_);
lean_dec_ref(v_items_1295_);
lean_dec_ref(v_items_1293_);
return v___x_1301_;
}
}
}
else
{
uint8_t v___x_1302_; 
lean_dec_ref_known(v_x_1262_, 2);
lean_dec_ref(v_localinst_1264_);
lean_dec_ref(v_x_1263_);
v___x_1302_ = 0;
return v___x_1302_;
}
}
case 4:
{
lean_dec_ref(v_inst_1261_);
if (lean_obj_tag(v_x_1263_) == 4)
{
lean_object* v_items_1303_; lean_object* v_items_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_items_1303_ = lean_ctor_get(v_x_1262_, 0);
lean_inc_ref(v_items_1303_);
lean_dec_ref_known(v_x_1262_, 1);
v_items_1304_ = lean_ctor_get(v_x_1263_, 0);
lean_inc_ref(v_items_1304_);
lean_dec_ref_known(v_x_1263_, 1);
v___x_1305_ = lean_array_get_size(v_items_1303_);
v___x_1306_ = lean_array_get_size(v_items_1304_);
v___x_1307_ = lean_nat_dec_eq(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec_ref(v_items_1304_);
lean_dec_ref(v_items_1303_);
lean_dec_ref(v_localinst_1264_);
lean_dec_ref(v_inst_1260_);
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1308_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1308_, 0, lean_box(0));
lean_closure_set(v___x_1308_, 1, v_inst_1260_);
v___x_1309_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1309_, 0, lean_box(0));
lean_closure_set(v___x_1309_, 1, lean_box(0));
lean_closure_set(v___x_1309_, 2, v___x_1308_);
lean_closure_set(v___x_1309_, 3, v_localinst_1264_);
v___x_1310_ = l_Array_isEqvAux___redArg(v_items_1303_, v_items_1304_, v___x_1309_, v___x_1305_);
lean_dec_ref(v_items_1304_);
lean_dec_ref(v_items_1303_);
return v___x_1310_;
}
}
else
{
uint8_t v___x_1311_; 
lean_dec_ref_known(v_x_1262_, 1);
lean_dec_ref(v_localinst_1264_);
lean_dec_ref(v_x_1263_);
lean_dec_ref(v_inst_1260_);
v___x_1311_ = 0;
return v___x_1311_;
}
}
case 5:
{
lean_dec_ref(v_inst_1261_);
lean_dec_ref(v_inst_1260_);
if (lean_obj_tag(v_x_1263_) == 5)
{
lean_object* v_items_1312_; lean_object* v_items_1313_; 
v_items_1312_ = lean_ctor_get(v_x_1262_, 0);
lean_inc_ref(v_items_1312_);
lean_dec_ref_known(v_x_1262_, 1);
v_items_1313_ = lean_ctor_get(v_x_1263_, 0);
lean_inc_ref(v_items_1313_);
lean_dec_ref_known(v_x_1263_, 1);
v_a_1266_ = v_items_1312_;
v_b_1267_ = v_items_1313_;
goto v___jp_1265_;
}
else
{
uint8_t v___x_1314_; 
lean_dec_ref_known(v_x_1262_, 1);
lean_dec_ref(v_localinst_1264_);
lean_dec_ref(v_x_1263_);
v___x_1314_ = 0;
return v___x_1314_;
}
}
case 6:
{
lean_dec_ref(v_inst_1261_);
lean_dec_ref(v_inst_1260_);
if (lean_obj_tag(v_x_1263_) == 6)
{
lean_object* v_content_1315_; lean_object* v_content_1316_; 
v_content_1315_ = lean_ctor_get(v_x_1262_, 0);
lean_inc_ref(v_content_1315_);
lean_dec_ref_known(v_x_1262_, 1);
v_content_1316_ = lean_ctor_get(v_x_1263_, 0);
lean_inc_ref(v_content_1316_);
lean_dec_ref_known(v_x_1263_, 1);
v_a_1266_ = v_content_1315_;
v_b_1267_ = v_content_1316_;
goto v___jp_1265_;
}
else
{
uint8_t v___x_1317_; 
lean_dec_ref_known(v_x_1262_, 1);
lean_dec_ref(v_localinst_1264_);
lean_dec_ref(v_x_1263_);
v___x_1317_ = 0;
return v___x_1317_;
}
}
default: 
{
lean_dec_ref(v_inst_1260_);
if (lean_obj_tag(v_x_1263_) == 7)
{
lean_object* v_container_1318_; lean_object* v_content_1319_; lean_object* v_container_1320_; lean_object* v_content_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_container_1318_ = lean_ctor_get(v_x_1262_, 0);
lean_inc(v_container_1318_);
v_content_1319_ = lean_ctor_get(v_x_1262_, 1);
lean_inc_ref(v_content_1319_);
lean_dec_ref_known(v_x_1262_, 2);
v_container_1320_ = lean_ctor_get(v_x_1263_, 0);
lean_inc(v_container_1320_);
v_content_1321_ = lean_ctor_get(v_x_1263_, 1);
lean_inc_ref(v_content_1321_);
lean_dec_ref_known(v_x_1263_, 2);
v___x_1322_ = lean_apply_2(v_inst_1261_, v_container_1318_, v_container_1320_);
v___x_1323_ = lean_unbox(v___x_1322_);
if (v___x_1323_ == 0)
{
uint8_t v___x_1324_; 
lean_dec_ref(v_content_1321_);
lean_dec_ref(v_content_1319_);
lean_dec_ref(v_localinst_1264_);
v___x_1324_ = lean_unbox(v___x_1322_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1325_ = lean_array_get_size(v_content_1319_);
v___x_1326_ = lean_array_get_size(v_content_1321_);
v___x_1327_ = lean_nat_dec_eq(v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_dec_ref(v_content_1321_);
lean_dec_ref(v_content_1319_);
lean_dec_ref(v_localinst_1264_);
return v___x_1327_;
}
else
{
uint8_t v___x_1328_; 
v___x_1328_ = l_Array_isEqvAux___redArg(v_content_1319_, v_content_1321_, v_localinst_1264_, v___x_1325_);
lean_dec_ref(v_content_1321_);
lean_dec_ref(v_content_1319_);
return v___x_1328_;
}
}
}
else
{
uint8_t v___x_1329_; 
lean_dec_ref_known(v_x_1262_, 2);
lean_dec_ref(v_localinst_1264_);
lean_dec_ref(v_x_1263_);
lean_dec_ref(v_inst_1261_);
v___x_1329_ = 0;
return v___x_1329_;
}
}
}
v___jp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1268_ = lean_array_get_size(v_a_1266_);
v___x_1269_ = lean_array_get_size(v_b_1267_);
v___x_1270_ = lean_nat_dec_eq(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_dec_ref(v_b_1267_);
lean_dec_ref(v_a_1266_);
lean_dec_ref(v_localinst_1264_);
return v___x_1270_;
}
else
{
uint8_t v___x_1271_; 
v___x_1271_ = l_Array_isEqvAux___redArg(v_a_1266_, v_b_1267_, v_localinst_1264_, v___x_1268_);
lean_dec_ref(v_b_1267_);
lean_dec_ref(v_a_1266_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq(lean_object* v_i_1330_, lean_object* v_b_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1332_, v_inst_1333_, v_x_1334_, v_x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___boxed(lean_object* v_i_1337_, lean_object* v_b_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_){
_start:
{
uint8_t v_res_1343_; lean_object* v_r_1344_; 
v_res_1343_ = l_Lean_Doc_instBEqBlock_beq(v_i_1337_, v_b_1338_, v_inst_1339_, v_inst_1340_, v_x_1341_, v_x_1342_);
v_r_1344_ = lean_box(v_res_1343_);
return v_r_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock___redArg(lean_object* v_inst_1345_, lean_object* v_inst_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1347_, 0, lean_box(0));
lean_closure_set(v___x_1347_, 1, lean_box(0));
lean_closure_set(v___x_1347_, 2, v_inst_1345_);
lean_closure_set(v___x_1347_, 3, v_inst_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock(lean_object* v_i_1348_, lean_object* v_b_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1352_, 0, lean_box(0));
lean_closure_set(v___x_1352_, 1, lean_box(0));
lean_closure_set(v___x_1352_, 2, v_inst_1350_);
lean_closure_set(v___x_1352_, 3, v_inst_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___redArg___boxed(lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
uint8_t v_res_1357_; lean_object* v_r_1358_; 
v_res_1357_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1353_, v_inst_1354_, v_x_1355_, v_x_1356_);
v_r_1358_ = lean_box(v_res_1357_);
return v_r_1358_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord___redArg(lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v_localinst_1363_; lean_object* v_a_1365_; lean_object* v_b_1366_; 
lean_inc_ref(v_inst_1360_);
lean_inc_ref(v_inst_1359_);
v_localinst_1363_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1363_, 0, v_inst_1359_);
lean_closure_set(v_localinst_1363_, 1, v_inst_1360_);
switch(lean_obj_tag(v_x_1361_))
{
case 0:
{
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_inst_1360_);
switch(lean_obj_tag(v_x_1362_))
{
case 0:
{
lean_object* v_contents_1368_; lean_object* v_contents_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_contents_1368_ = lean_ctor_get(v_x_1361_, 0);
lean_inc_ref(v_contents_1368_);
lean_dec_ref_known(v_x_1361_, 1);
v_contents_1369_ = lean_ctor_get(v_x_1362_, 0);
lean_inc_ref(v_contents_1369_);
lean_dec_ref_known(v_x_1362_, 1);
v___x_1370_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1370_, 0, lean_box(0));
lean_closure_set(v___x_1370_, 1, v_inst_1359_);
v___x_1371_ = l_Array_compareLex___redArg(v___x_1370_, v_contents_1368_, v_contents_1369_);
lean_dec_ref(v_contents_1369_);
lean_dec_ref(v_contents_1368_);
if (v___x_1371_ == 1)
{
return v___x_1371_;
}
else
{
return v___x_1371_;
}
}
case 1:
{
uint8_t v___x_1372_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_inst_1359_);
v___x_1372_ = 0;
return v___x_1372_;
}
case 2:
{
uint8_t v___x_1373_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_inst_1359_);
v___x_1373_ = 0;
return v___x_1373_;
}
case 3:
{
uint8_t v___x_1374_; 
lean_dec_ref_known(v_x_1362_, 2);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_inst_1359_);
v___x_1374_ = 0;
return v___x_1374_;
}
case 4:
{
uint8_t v___x_1375_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_inst_1359_);
v___x_1375_ = 0;
return v___x_1375_;
}
case 5:
{
uint8_t v___x_1376_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_inst_1359_);
v___x_1376_ = 0;
return v___x_1376_;
}
case 6:
{
uint8_t v___x_1377_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_inst_1359_);
v___x_1377_ = 0;
return v___x_1377_;
}
default: 
{
uint8_t v___x_1378_; 
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_x_1362_);
lean_dec_ref(v_inst_1359_);
v___x_1378_ = 0;
return v___x_1378_;
}
}
}
case 1:
{
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
switch(lean_obj_tag(v_x_1362_))
{
case 0:
{
uint8_t v___x_1379_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
v___x_1379_ = 2;
return v___x_1379_;
}
case 1:
{
lean_object* v_content_1380_; lean_object* v_content_1381_; uint8_t v___x_1382_; 
v_content_1380_ = lean_ctor_get(v_x_1361_, 0);
lean_inc_ref(v_content_1380_);
lean_dec_ref_known(v_x_1361_, 1);
v_content_1381_ = lean_ctor_get(v_x_1362_, 0);
lean_inc_ref(v_content_1381_);
lean_dec_ref_known(v_x_1362_, 1);
v___x_1382_ = lean_string_compare(v_content_1380_, v_content_1381_);
lean_dec_ref(v_content_1381_);
lean_dec_ref(v_content_1380_);
if (v___x_1382_ == 1)
{
return v___x_1382_;
}
else
{
return v___x_1382_;
}
}
case 2:
{
uint8_t v___x_1383_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
v___x_1383_ = 0;
return v___x_1383_;
}
case 3:
{
uint8_t v___x_1384_; 
lean_dec_ref_known(v_x_1362_, 2);
lean_dec_ref_known(v_x_1361_, 1);
v___x_1384_ = 0;
return v___x_1384_;
}
case 4:
{
uint8_t v___x_1385_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
v___x_1385_ = 0;
return v___x_1385_;
}
case 5:
{
uint8_t v___x_1386_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
v___x_1386_ = 0;
return v___x_1386_;
}
case 6:
{
uint8_t v___x_1387_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
v___x_1387_ = 0;
return v___x_1387_;
}
default: 
{
uint8_t v___x_1388_; 
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_x_1362_);
v___x_1388_ = 0;
return v___x_1388_;
}
}
}
case 2:
{
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
switch(lean_obj_tag(v_x_1362_))
{
case 0:
{
uint8_t v___x_1389_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1389_ = 2;
return v___x_1389_;
}
case 1:
{
uint8_t v___x_1390_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1390_ = 2;
return v___x_1390_;
}
case 2:
{
lean_object* v_items_1391_; lean_object* v_items_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_items_1391_ = lean_ctor_get(v_x_1361_, 0);
lean_inc_ref(v_items_1391_);
lean_dec_ref_known(v_x_1361_, 1);
v_items_1392_ = lean_ctor_get(v_x_1362_, 0);
lean_inc_ref(v_items_1392_);
lean_dec_ref_known(v_x_1362_, 1);
v___x_1393_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1393_, 0, lean_box(0));
lean_closure_set(v___x_1393_, 1, v_localinst_1363_);
v___x_1394_ = l_Array_compareLex___redArg(v___x_1393_, v_items_1391_, v_items_1392_);
lean_dec_ref(v_items_1392_);
lean_dec_ref(v_items_1391_);
if (v___x_1394_ == 1)
{
return v___x_1394_;
}
else
{
return v___x_1394_;
}
}
case 3:
{
uint8_t v___x_1395_; 
lean_dec_ref_known(v_x_1362_, 2);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1395_ = 0;
return v___x_1395_;
}
case 4:
{
uint8_t v___x_1396_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1396_ = 0;
return v___x_1396_;
}
case 5:
{
uint8_t v___x_1397_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1397_ = 0;
return v___x_1397_;
}
case 6:
{
uint8_t v___x_1398_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1398_ = 0;
return v___x_1398_;
}
default: 
{
uint8_t v___x_1399_; 
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_x_1362_);
v___x_1399_ = 0;
return v___x_1399_;
}
}
}
case 3:
{
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
switch(lean_obj_tag(v_x_1362_))
{
case 0:
{
uint8_t v___x_1400_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 2);
lean_dec_ref(v_localinst_1363_);
v___x_1400_ = 2;
return v___x_1400_;
}
case 1:
{
uint8_t v___x_1401_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 2);
lean_dec_ref(v_localinst_1363_);
v___x_1401_ = 2;
return v___x_1401_;
}
case 2:
{
uint8_t v___x_1402_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 2);
lean_dec_ref(v_localinst_1363_);
v___x_1402_ = 2;
return v___x_1402_;
}
case 3:
{
lean_object* v_start_1403_; lean_object* v_items_1404_; lean_object* v_start_1405_; lean_object* v_items_1406_; uint8_t v___x_1407_; 
v_start_1403_ = lean_ctor_get(v_x_1361_, 0);
lean_inc(v_start_1403_);
v_items_1404_ = lean_ctor_get(v_x_1361_, 1);
lean_inc_ref(v_items_1404_);
lean_dec_ref_known(v_x_1361_, 2);
v_start_1405_ = lean_ctor_get(v_x_1362_, 0);
lean_inc(v_start_1405_);
v_items_1406_ = lean_ctor_get(v_x_1362_, 1);
lean_inc_ref(v_items_1406_);
lean_dec_ref_known(v_x_1362_, 2);
v___x_1407_ = lean_int_dec_lt(v_start_1403_, v_start_1405_);
if (v___x_1407_ == 0)
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_int_dec_eq(v_start_1403_, v_start_1405_);
lean_dec(v_start_1405_);
lean_dec(v_start_1403_);
if (v___x_1408_ == 0)
{
uint8_t v___x_1409_; 
lean_dec_ref(v_items_1406_);
lean_dec_ref(v_items_1404_);
lean_dec_ref(v_localinst_1363_);
v___x_1409_ = 2;
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1410_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1410_, 0, lean_box(0));
lean_closure_set(v___x_1410_, 1, v_localinst_1363_);
v___x_1411_ = l_Array_compareLex___redArg(v___x_1410_, v_items_1404_, v_items_1406_);
lean_dec_ref(v_items_1406_);
lean_dec_ref(v_items_1404_);
if (v___x_1411_ == 1)
{
return v___x_1411_;
}
else
{
return v___x_1411_;
}
}
}
else
{
uint8_t v___x_1412_; 
lean_dec_ref(v_items_1406_);
lean_dec(v_start_1405_);
lean_dec_ref(v_items_1404_);
lean_dec(v_start_1403_);
lean_dec_ref(v_localinst_1363_);
v___x_1412_ = 0;
return v___x_1412_;
}
}
case 4:
{
uint8_t v___x_1413_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 2);
lean_dec_ref(v_localinst_1363_);
v___x_1413_ = 0;
return v___x_1413_;
}
case 5:
{
uint8_t v___x_1414_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 2);
lean_dec_ref(v_localinst_1363_);
v___x_1414_ = 0;
return v___x_1414_;
}
case 6:
{
uint8_t v___x_1415_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 2);
lean_dec_ref(v_localinst_1363_);
v___x_1415_ = 0;
return v___x_1415_;
}
default: 
{
uint8_t v___x_1416_; 
lean_dec_ref_known(v_x_1361_, 2);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_x_1362_);
v___x_1416_ = 0;
return v___x_1416_;
}
}
}
case 4:
{
lean_dec_ref(v_inst_1360_);
switch(lean_obj_tag(v_x_1362_))
{
case 0:
{
uint8_t v___x_1417_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_inst_1359_);
v___x_1417_ = 2;
return v___x_1417_;
}
case 1:
{
uint8_t v___x_1418_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_inst_1359_);
v___x_1418_ = 2;
return v___x_1418_;
}
case 2:
{
uint8_t v___x_1419_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_inst_1359_);
v___x_1419_ = 2;
return v___x_1419_;
}
case 3:
{
uint8_t v___x_1420_; 
lean_dec_ref_known(v_x_1362_, 2);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_inst_1359_);
v___x_1420_ = 2;
return v___x_1420_;
}
case 4:
{
lean_object* v_items_1421_; lean_object* v_items_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_items_1421_ = lean_ctor_get(v_x_1361_, 0);
lean_inc_ref(v_items_1421_);
lean_dec_ref_known(v_x_1361_, 1);
v_items_1422_ = lean_ctor_get(v_x_1362_, 0);
lean_inc_ref(v_items_1422_);
lean_dec_ref_known(v_x_1362_, 1);
v___x_1423_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1423_, 0, lean_box(0));
lean_closure_set(v___x_1423_, 1, v_inst_1359_);
v___x_1424_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1424_, 0, lean_box(0));
lean_closure_set(v___x_1424_, 1, lean_box(0));
lean_closure_set(v___x_1424_, 2, v___x_1423_);
lean_closure_set(v___x_1424_, 3, v_localinst_1363_);
v___x_1425_ = l_Array_compareLex___redArg(v___x_1424_, v_items_1421_, v_items_1422_);
lean_dec_ref(v_items_1422_);
lean_dec_ref(v_items_1421_);
if (v___x_1425_ == 1)
{
return v___x_1425_;
}
else
{
return v___x_1425_;
}
}
case 5:
{
uint8_t v___x_1426_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_inst_1359_);
v___x_1426_ = 0;
return v___x_1426_;
}
case 6:
{
uint8_t v___x_1427_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_inst_1359_);
v___x_1427_ = 0;
return v___x_1427_;
}
default: 
{
uint8_t v___x_1428_; 
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_x_1362_);
lean_dec_ref(v_inst_1359_);
v___x_1428_ = 0;
return v___x_1428_;
}
}
}
case 5:
{
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
switch(lean_obj_tag(v_x_1362_))
{
case 0:
{
uint8_t v___x_1429_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1429_ = 2;
return v___x_1429_;
}
case 1:
{
uint8_t v___x_1430_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1430_ = 2;
return v___x_1430_;
}
case 2:
{
uint8_t v___x_1431_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1431_ = 2;
return v___x_1431_;
}
case 3:
{
uint8_t v___x_1432_; 
lean_dec_ref_known(v_x_1362_, 2);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1432_ = 2;
return v___x_1432_;
}
case 4:
{
uint8_t v___x_1433_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1433_ = 2;
return v___x_1433_;
}
case 5:
{
lean_object* v_items_1434_; lean_object* v_items_1435_; 
v_items_1434_ = lean_ctor_get(v_x_1361_, 0);
lean_inc_ref(v_items_1434_);
lean_dec_ref_known(v_x_1361_, 1);
v_items_1435_ = lean_ctor_get(v_x_1362_, 0);
lean_inc_ref(v_items_1435_);
lean_dec_ref_known(v_x_1362_, 1);
v_a_1365_ = v_items_1434_;
v_b_1366_ = v_items_1435_;
goto v___jp_1364_;
}
case 6:
{
uint8_t v___x_1436_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1436_ = 0;
return v___x_1436_;
}
default: 
{
uint8_t v___x_1437_; 
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_x_1362_);
v___x_1437_ = 0;
return v___x_1437_;
}
}
}
case 6:
{
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
switch(lean_obj_tag(v_x_1362_))
{
case 0:
{
uint8_t v___x_1438_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1438_ = 2;
return v___x_1438_;
}
case 1:
{
uint8_t v___x_1439_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1439_ = 2;
return v___x_1439_;
}
case 2:
{
uint8_t v___x_1440_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1440_ = 2;
return v___x_1440_;
}
case 3:
{
uint8_t v___x_1441_; 
lean_dec_ref_known(v_x_1362_, 2);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1441_ = 2;
return v___x_1441_;
}
case 4:
{
uint8_t v___x_1442_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1442_ = 2;
return v___x_1442_;
}
case 5:
{
uint8_t v___x_1443_; 
lean_dec_ref_known(v_x_1362_, 1);
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
v___x_1443_ = 2;
return v___x_1443_;
}
case 6:
{
lean_object* v_content_1444_; lean_object* v_content_1445_; 
v_content_1444_ = lean_ctor_get(v_x_1361_, 0);
lean_inc_ref(v_content_1444_);
lean_dec_ref_known(v_x_1361_, 1);
v_content_1445_ = lean_ctor_get(v_x_1362_, 0);
lean_inc_ref(v_content_1445_);
lean_dec_ref_known(v_x_1362_, 1);
v_a_1365_ = v_content_1444_;
v_b_1366_ = v_content_1445_;
goto v___jp_1364_;
}
default: 
{
uint8_t v___x_1446_; 
lean_dec_ref_known(v_x_1361_, 1);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_x_1362_);
v___x_1446_ = 0;
return v___x_1446_;
}
}
}
default: 
{
lean_dec_ref(v_inst_1359_);
if (lean_obj_tag(v_x_1362_) == 7)
{
lean_object* v_container_1447_; lean_object* v_content_1448_; lean_object* v_container_1449_; lean_object* v_content_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_container_1447_ = lean_ctor_get(v_x_1361_, 0);
lean_inc(v_container_1447_);
v_content_1448_ = lean_ctor_get(v_x_1361_, 1);
lean_inc_ref(v_content_1448_);
lean_dec_ref_known(v_x_1361_, 2);
v_container_1449_ = lean_ctor_get(v_x_1362_, 0);
lean_inc(v_container_1449_);
v_content_1450_ = lean_ctor_get(v_x_1362_, 1);
lean_inc_ref(v_content_1450_);
lean_dec_ref_known(v_x_1362_, 2);
v___x_1451_ = lean_apply_2(v_inst_1360_, v_container_1447_, v_container_1449_);
v___x_1452_ = lean_unbox(v___x_1451_);
if (v___x_1452_ == 1)
{
uint8_t v___x_1453_; 
v___x_1453_ = l_Array_compareLex___redArg(v_localinst_1363_, v_content_1448_, v_content_1450_);
lean_dec_ref(v_content_1450_);
lean_dec_ref(v_content_1448_);
if (v___x_1453_ == 1)
{
return v___x_1453_;
}
else
{
return v___x_1453_;
}
}
else
{
uint8_t v___x_1454_; 
lean_dec_ref(v_content_1450_);
lean_dec_ref(v_content_1448_);
lean_dec_ref(v_localinst_1363_);
v___x_1454_ = lean_unbox(v___x_1451_);
return v___x_1454_;
}
}
else
{
uint8_t v___x_1455_; 
lean_dec_ref_known(v_x_1361_, 2);
lean_dec_ref(v_localinst_1363_);
lean_dec_ref(v_x_1362_);
lean_dec_ref(v_inst_1360_);
v___x_1455_ = 2;
return v___x_1455_;
}
}
}
v___jp_1364_:
{
uint8_t v___x_1367_; 
v___x_1367_ = l_Array_compareLex___redArg(v_localinst_1363_, v_a_1365_, v_b_1366_);
lean_dec_ref(v_b_1366_);
lean_dec_ref(v_a_1365_);
if (v___x_1367_ == 1)
{
return v___x_1367_;
}
else
{
return v___x_1367_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord(lean_object* v_i_1456_, lean_object* v_b_1457_, lean_object* v_inst_1458_, lean_object* v_inst_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1458_, v_inst_1459_, v_x_1460_, v_x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___boxed(lean_object* v_i_1463_, lean_object* v_b_1464_, lean_object* v_inst_1465_, lean_object* v_inst_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_res_1469_ = l_Lean_Doc_instOrdBlock_ord(v_i_1463_, v_b_1464_, v_inst_1465_, v_inst_1466_, v_x_1467_, v_x_1468_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock___redArg(lean_object* v_inst_1471_, lean_object* v_inst_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1473_, 0, lean_box(0));
lean_closure_set(v___x_1473_, 1, lean_box(0));
lean_closure_set(v___x_1473_, 2, v_inst_1471_);
lean_closure_set(v___x_1473_, 3, v_inst_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock(lean_object* v_i_1474_, lean_object* v_b_1475_, lean_object* v_inst_1476_, lean_object* v_inst_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1478_, 0, lean_box(0));
lean_closure_set(v___x_1478_, 1, lean_box(0));
lean_closure_set(v___x_1478_, 2, v_inst_1476_);
lean_closure_set(v___x_1478_, 3, v_inst_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_nat_to_int(v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg___boxed(lean_object* v_inst_1529_, lean_object* v_inst_1530_, lean_object* v_x_1531_, lean_object* v_prec_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1529_, v_inst_1530_, v_x_1531_, v_prec_1532_);
lean_dec(v_prec_1532_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg(lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_x_1536_, lean_object* v_prec_1537_){
_start:
{
lean_object* v_localinst_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_inc_ref(v_inst_1535_);
lean_inc_ref(v_inst_1534_);
v_localinst_1538_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1538_, 0, v_inst_1534_);
lean_closure_set(v_localinst_1538_, 1, v_inst_1535_);
v___x_1539_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1539_, 0, lean_box(0));
lean_closure_set(v___x_1539_, 1, v_inst_1534_);
lean_inc_ref(v_localinst_1538_);
v___x_1540_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_1540_, 0, lean_box(0));
lean_closure_set(v___x_1540_, 1, v_localinst_1538_);
switch(lean_obj_tag(v_x_1536_))
{
case 0:
{
lean_object* v_contents_1541_; lean_object* v___y_1543_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
lean_dec_ref(v___x_1540_);
lean_dec_ref(v_localinst_1538_);
lean_dec_ref(v_inst_1535_);
v_contents_1541_ = lean_ctor_get(v_x_1536_, 0);
lean_inc_ref(v_contents_1541_);
lean_dec_ref_known(v_x_1536_, 1);
v___x_1551_ = lean_unsigned_to_nat(1024u);
v___x_1552_ = lean_nat_dec_le(v___x_1551_, v_prec_1537_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1543_ = v___x_1553_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1543_ = v___x_1554_;
goto v___jp_1542_;
}
v___jp_1542_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1544_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__2));
v___x_1545_ = l_Array_repr___redArg(v___x_1539_, v_contents_1541_);
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
lean_inc(v___y_1543_);
v___x_1547_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___y_1543_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = 0;
v___x_1549_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set_uint8(v___x_1549_, sizeof(void*)*1, v___x_1548_);
v___x_1550_ = l_Repr_addAppParen(v___x_1549_, v_prec_1537_);
return v___x_1550_;
}
}
case 1:
{
lean_object* v_content_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v___x_1540_);
lean_dec_ref(v___x_1539_);
lean_dec_ref(v_localinst_1538_);
lean_dec_ref(v_inst_1535_);
v_content_1555_ = lean_ctor_get(v_x_1536_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_x_1536_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1557_ = v_x_1536_;
v_isShared_1558_ = v_isSharedCheck_1575_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_content_1555_);
lean_dec(v_x_1536_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1575_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___y_1560_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = lean_unsigned_to_nat(1024u);
v___x_1572_ = lean_nat_dec_le(v___x_1571_, v_prec_1537_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1560_ = v___x_1573_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1560_ = v___x_1574_;
goto v___jp_1559_;
}
v___jp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1561_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__5));
v___x_1562_ = l_String_quote(v_content_1555_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set_tag(v___x_1557_, 3);
lean_ctor_set(v___x_1557_, 0, v___x_1562_);
v___x_1564_ = v___x_1557_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1561_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
lean_inc(v___y_1560_);
v___x_1566_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___y_1560_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = 0;
v___x_1568_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*1, v___x_1567_);
v___x_1569_ = l_Repr_addAppParen(v___x_1568_, v_prec_1537_);
return v___x_1569_;
}
}
}
}
case 2:
{
lean_object* v_items_1576_; lean_object* v___y_1578_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
lean_dec_ref(v___x_1539_);
lean_dec_ref(v_localinst_1538_);
lean_dec_ref(v_inst_1535_);
v_items_1576_ = lean_ctor_get(v_x_1536_, 0);
lean_inc_ref(v_items_1576_);
lean_dec_ref_known(v_x_1536_, 1);
v___x_1586_ = lean_unsigned_to_nat(1024u);
v___x_1587_ = lean_nat_dec_le(v___x_1586_, v_prec_1537_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1578_ = v___x_1588_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1578_ = v___x_1589_;
goto v___jp_1577_;
}
v___jp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1579_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__8));
v___x_1580_ = l_Array_repr___redArg(v___x_1540_, v_items_1576_);
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
lean_inc(v___y_1578_);
v___x_1582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___y_1578_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = 0;
v___x_1584_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*1, v___x_1583_);
v___x_1585_ = l_Repr_addAppParen(v___x_1584_, v_prec_1537_);
return v___x_1585_;
}
}
case 3:
{
lean_object* v_start_1590_; lean_object* v_items_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v___x_1539_);
lean_dec_ref(v_localinst_1538_);
lean_dec_ref(v_inst_1535_);
v_start_1590_ = lean_ctor_get(v_x_1536_, 0);
v_items_1591_ = lean_ctor_get(v_x_1536_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_x_1536_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1593_ = v_x_1536_;
v_isShared_1594_ = v_isSharedCheck_1626_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_items_1591_);
lean_inc(v_start_1590_);
lean_dec(v_x_1536_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1626_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1611_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = lean_unsigned_to_nat(1024u);
v___x_1623_ = lean_nat_dec_le(v___x_1622_, v_prec_1537_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1611_ = v___x_1624_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1611_ = v___x_1625_;
goto v___jp_1610_;
}
v___jp_1595_:
{
lean_object* v___x_1601_; 
lean_inc(v___y_1596_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set_tag(v___x_1593_, 5);
lean_ctor_set(v___x_1593_, 1, v___y_1599_);
lean_ctor_set(v___x_1593_, 0, v___y_1596_);
v___x_1601_ = v___x_1593_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___y_1596_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___y_1599_);
v___x_1601_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_inc(v___y_1598_);
v___x_1602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___y_1598_);
v___x_1603_ = l_Array_repr___redArg(v___x_1540_, v_items_1591_);
v___x_1604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
lean_inc(v___y_1597_);
v___x_1605_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___y_1597_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = 0;
v___x_1607_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*1, v___x_1606_);
v___x_1608_ = l_Repr_addAppParen(v___x_1607_, v_prec_1537_);
return v___x_1608_;
}
}
v___jp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1612_ = lean_box(1);
v___x_1613_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__11));
v___x_1614_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___redArg___closed__12, &l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12);
v___x_1615_ = lean_int_dec_lt(v_start_1590_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = l_Int_repr(v_start_1590_);
lean_dec(v_start_1590_);
v___x_1617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
v___y_1596_ = v___x_1613_;
v___y_1597_ = v___y_1611_;
v___y_1598_ = v___x_1612_;
v___y_1599_ = v___x_1617_;
goto v___jp_1595_;
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1618_ = lean_unsigned_to_nat(1024u);
v___x_1619_ = l_Int_repr(v_start_1590_);
lean_dec(v_start_1590_);
v___x_1620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
v___x_1621_ = l_Repr_addAppParen(v___x_1620_, v___x_1618_);
v___y_1596_ = v___x_1613_;
v___y_1597_ = v___y_1611_;
v___y_1598_ = v___x_1612_;
v___y_1599_ = v___x_1621_;
goto v___jp_1595_;
}
}
}
}
case 4:
{
lean_object* v_items_1627_; lean_object* v___x_1628_; lean_object* v___y_1630_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
lean_dec_ref(v___x_1540_);
lean_dec_ref(v_inst_1535_);
v_items_1627_ = lean_ctor_get(v_x_1536_, 0);
lean_inc_ref(v_items_1627_);
lean_dec_ref_known(v_x_1536_, 1);
v___x_1628_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1628_, 0, lean_box(0));
lean_closure_set(v___x_1628_, 1, lean_box(0));
lean_closure_set(v___x_1628_, 2, v___x_1539_);
lean_closure_set(v___x_1628_, 3, v_localinst_1538_);
v___x_1638_ = lean_unsigned_to_nat(1024u);
v___x_1639_ = lean_nat_dec_le(v___x_1638_, v_prec_1537_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1630_ = v___x_1640_;
goto v___jp_1629_;
}
else
{
lean_object* v___x_1641_; 
v___x_1641_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1630_ = v___x_1641_;
goto v___jp_1629_;
}
v___jp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1631_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__15));
v___x_1632_ = l_Array_repr___redArg(v___x_1628_, v_items_1627_);
v___x_1633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
lean_inc(v___y_1630_);
v___x_1634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___y_1630_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = 0;
v___x_1636_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*1, v___x_1635_);
v___x_1637_ = l_Repr_addAppParen(v___x_1636_, v_prec_1537_);
return v___x_1637_;
}
}
case 5:
{
lean_object* v_items_1642_; lean_object* v___y_1644_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
lean_dec_ref(v___x_1540_);
lean_dec_ref(v___x_1539_);
lean_dec_ref(v_inst_1535_);
v_items_1642_ = lean_ctor_get(v_x_1536_, 0);
lean_inc_ref(v_items_1642_);
lean_dec_ref_known(v_x_1536_, 1);
v___x_1652_ = lean_unsigned_to_nat(1024u);
v___x_1653_ = lean_nat_dec_le(v___x_1652_, v_prec_1537_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1644_ = v___x_1654_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1644_ = v___x_1655_;
goto v___jp_1643_;
}
v___jp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1645_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__18));
v___x_1646_ = l_Array_repr___redArg(v_localinst_1538_, v_items_1642_);
v___x_1647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
lean_inc(v___y_1644_);
v___x_1648_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___y_1644_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = 0;
v___x_1650_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set_uint8(v___x_1650_, sizeof(void*)*1, v___x_1649_);
v___x_1651_ = l_Repr_addAppParen(v___x_1650_, v_prec_1537_);
return v___x_1651_;
}
}
case 6:
{
lean_object* v_content_1656_; lean_object* v___y_1658_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
lean_dec_ref(v___x_1540_);
lean_dec_ref(v___x_1539_);
lean_dec_ref(v_inst_1535_);
v_content_1656_ = lean_ctor_get(v_x_1536_, 0);
lean_inc_ref(v_content_1656_);
lean_dec_ref_known(v_x_1536_, 1);
v___x_1666_ = lean_unsigned_to_nat(1024u);
v___x_1667_ = lean_nat_dec_le(v___x_1666_, v_prec_1537_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1658_ = v___x_1668_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1658_ = v___x_1669_;
goto v___jp_1657_;
}
v___jp_1657_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1659_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__21));
v___x_1660_ = l_Array_repr___redArg(v_localinst_1538_, v_content_1656_);
v___x_1661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1659_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
lean_inc(v___y_1658_);
v___x_1662_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___y_1658_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = 0;
v___x_1664_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set_uint8(v___x_1664_, sizeof(void*)*1, v___x_1663_);
v___x_1665_ = l_Repr_addAppParen(v___x_1664_, v_prec_1537_);
return v___x_1665_;
}
}
default: 
{
lean_object* v_container_1670_; lean_object* v_content_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v___x_1540_);
lean_dec_ref(v___x_1539_);
v_container_1670_ = lean_ctor_get(v_x_1536_, 0);
v_content_1671_ = lean_ctor_get(v_x_1536_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_x_1536_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1673_ = v_x_1536_;
v_isShared_1674_ = v_isSharedCheck_1695_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_content_1671_);
lean_inc(v_container_1670_);
lean_dec(v_x_1536_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1695_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___y_1676_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = lean_unsigned_to_nat(1024u);
v___x_1692_ = lean_nat_dec_le(v___x_1691_, v_prec_1537_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1676_ = v___x_1693_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1676_ = v___x_1694_;
goto v___jp_1675_;
}
v___jp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1677_ = lean_box(1);
v___x_1678_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__24));
v___x_1679_ = lean_unsigned_to_nat(1024u);
v___x_1680_ = lean_apply_2(v_inst_1535_, v_container_1670_, v___x_1679_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 5);
lean_ctor_set(v___x_1673_, 1, v___x_1680_);
lean_ctor_set(v___x_1673_, 0, v___x_1678_);
v___x_1682_ = v___x_1673_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___x_1677_);
v___x_1684_ = l_Array_repr___redArg(v_localinst_1538_, v_content_1671_);
v___x_1685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
lean_inc(v___y_1676_);
v___x_1686_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___y_1676_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = 0;
v___x_1688_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set_uint8(v___x_1688_, sizeof(void*)*1, v___x_1687_);
v___x_1689_ = l_Repr_addAppParen(v___x_1688_, v_prec_1537_);
return v___x_1689_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr(lean_object* v_i_1696_, lean_object* v_b_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_x_1700_, lean_object* v_prec_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1698_, v_inst_1699_, v_x_1700_, v_prec_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___boxed(lean_object* v_i_1703_, lean_object* v_b_1704_, lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_x_1707_, lean_object* v_prec_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Doc_instReprBlock_repr(v_i_1703_, v_b_1704_, v_inst_1705_, v_inst_1706_, v_x_1707_, v_prec_1708_);
lean_dec(v_prec_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock___redArg(lean_object* v_inst_1710_, lean_object* v_inst_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1712_, 0, lean_box(0));
lean_closure_set(v___x_1712_, 1, lean_box(0));
lean_closure_set(v___x_1712_, 2, v_inst_1710_);
lean_closure_set(v___x_1712_, 3, v_inst_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock(lean_object* v_i_1713_, lean_object* v_b_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1717_, 0, lean_box(0));
lean_closure_set(v___x_1717_, 1, lean_box(0));
lean_closure_set(v___x_1717_, 2, v_inst_1715_);
lean_closure_set(v___x_1717_, 3, v_inst_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default(lean_object* v_i_1722_, lean_object* v_b_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlock_default___closed__1));
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedBlock___closed__0(void){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Doc_instInhabitedBlock_default(lean_box(0), lean_box(0));
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock(lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock___closed__0, &l_Lean_Doc_instInhabitedBlock___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock___closed__0);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty(lean_object* v_i_1733_, lean_object* v_b_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = ((lean_object*)(l_Lean_Doc_Block_empty___closed__1));
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg(lean_object* v_x_1736_){
_start:
{
lean_inc_ref(v_x_1736_);
return v_x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg___boxed(lean_object* v_x_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Doc_Block_cast___redArg(v_x_1737_);
lean_dec_ref(v_x_1737_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast(lean_object* v_i_1739_, lean_object* v_i_x27_1740_, lean_object* v_b_1741_, lean_object* v_b_x27_1742_, lean_object* v_inlines__eq_1743_, lean_object* v_blocks__eq_1744_, lean_object* v_x_1745_){
_start:
{
lean_inc_ref(v_x_1745_);
return v_x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___boxed(lean_object* v_i_1746_, lean_object* v_i_x27_1747_, lean_object* v_b_1748_, lean_object* v_b_x27_1749_, lean_object* v_inlines__eq_1750_, lean_object* v_blocks__eq_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Doc_Block_cast(v_i_1746_, v_i_x27_1747_, v_b_1748_, v_b_x27_1749_, v_inlines__eq_1750_, v_blocks__eq_1751_, v_x_1752_);
lean_dec_ref(v_x_1752_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___redArg___boxed(lean_object* v_inst_1754_, lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
uint8_t v_res_1759_; lean_object* v_r_1760_; 
v_res_1759_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1754_, v_inst_1755_, v_inst_1756_, v_x_1757_, v_x_1758_);
v_r_1760_ = lean_box(v_res_1759_);
return v_r_1760_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq___redArg(lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
lean_object* v_title_1766_; lean_object* v_titleString_1767_; lean_object* v_metadata_1768_; lean_object* v_content_1769_; lean_object* v_subParts_1770_; lean_object* v_title_1771_; lean_object* v_titleString_1772_; lean_object* v_metadata_1773_; lean_object* v_content_1774_; lean_object* v_subParts_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_title_1766_ = lean_ctor_get(v_x_1764_, 0);
lean_inc_ref(v_title_1766_);
v_titleString_1767_ = lean_ctor_get(v_x_1764_, 1);
lean_inc_ref(v_titleString_1767_);
v_metadata_1768_ = lean_ctor_get(v_x_1764_, 2);
lean_inc(v_metadata_1768_);
v_content_1769_ = lean_ctor_get(v_x_1764_, 3);
lean_inc_ref(v_content_1769_);
v_subParts_1770_ = lean_ctor_get(v_x_1764_, 4);
lean_inc_ref(v_subParts_1770_);
lean_dec_ref(v_x_1764_);
v_title_1771_ = lean_ctor_get(v_x_1765_, 0);
lean_inc_ref(v_title_1771_);
v_titleString_1772_ = lean_ctor_get(v_x_1765_, 1);
lean_inc_ref(v_titleString_1772_);
v_metadata_1773_ = lean_ctor_get(v_x_1765_, 2);
lean_inc(v_metadata_1773_);
v_content_1774_ = lean_ctor_get(v_x_1765_, 3);
lean_inc_ref(v_content_1774_);
v_subParts_1775_ = lean_ctor_get(v_x_1765_, 4);
lean_inc_ref(v_subParts_1775_);
lean_dec_ref(v_x_1765_);
v___x_1776_ = lean_array_get_size(v_title_1766_);
v___x_1777_ = lean_array_get_size(v_title_1771_);
v___x_1778_ = lean_nat_dec_eq(v___x_1776_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_content_1774_);
lean_dec(v_metadata_1773_);
lean_dec_ref(v_titleString_1772_);
lean_dec_ref(v_title_1771_);
lean_dec_ref(v_subParts_1770_);
lean_dec_ref(v_content_1769_);
lean_dec(v_metadata_1768_);
lean_dec_ref(v_titleString_1767_);
lean_dec_ref(v_title_1766_);
lean_dec_ref(v_inst_1763_);
lean_dec_ref(v_inst_1762_);
lean_dec_ref(v_inst_1761_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
lean_inc_ref(v_inst_1763_);
lean_inc_ref(v_inst_1762_);
lean_inc_ref_n(v_inst_1761_, 2);
v___x_1779_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___redArg___boxed), 5, 3);
lean_closure_set(v___x_1779_, 0, v_inst_1761_);
lean_closure_set(v___x_1779_, 1, v_inst_1762_);
lean_closure_set(v___x_1779_, 2, v_inst_1763_);
v___x_1780_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1780_, 0, lean_box(0));
lean_closure_set(v___x_1780_, 1, v_inst_1761_);
v___x_1781_ = l_Array_isEqvAux___redArg(v_title_1766_, v_title_1771_, v___x_1780_, v___x_1776_);
lean_dec_ref(v_title_1771_);
lean_dec_ref(v_title_1766_);
if (v___x_1781_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_content_1774_);
lean_dec(v_metadata_1773_);
lean_dec_ref(v_titleString_1772_);
lean_dec_ref(v_subParts_1770_);
lean_dec_ref(v_content_1769_);
lean_dec(v_metadata_1768_);
lean_dec_ref(v_titleString_1767_);
lean_dec_ref(v_inst_1763_);
lean_dec_ref(v_inst_1762_);
lean_dec_ref(v_inst_1761_);
return v___x_1781_;
}
else
{
uint8_t v___x_1782_; 
v___x_1782_ = lean_string_dec_eq(v_titleString_1767_, v_titleString_1772_);
lean_dec_ref(v_titleString_1772_);
lean_dec_ref(v_titleString_1767_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_content_1774_);
lean_dec(v_metadata_1773_);
lean_dec_ref(v_subParts_1770_);
lean_dec_ref(v_content_1769_);
lean_dec(v_metadata_1768_);
lean_dec_ref(v_inst_1763_);
lean_dec_ref(v_inst_1762_);
lean_dec_ref(v_inst_1761_);
return v___x_1782_;
}
else
{
uint8_t v___x_1783_; 
v___x_1783_ = l_Option_instBEq_beq___redArg(v_inst_1763_, v_metadata_1768_, v_metadata_1773_);
if (v___x_1783_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_content_1774_);
lean_dec_ref(v_subParts_1770_);
lean_dec_ref(v_content_1769_);
lean_dec_ref(v_inst_1762_);
lean_dec_ref(v_inst_1761_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1784_ = lean_array_get_size(v_content_1769_);
v___x_1785_ = lean_array_get_size(v_content_1774_);
v___x_1786_ = lean_nat_dec_eq(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_content_1774_);
lean_dec_ref(v_subParts_1770_);
lean_dec_ref(v_content_1769_);
lean_dec_ref(v_inst_1762_);
lean_dec_ref(v_inst_1761_);
return v___x_1786_;
}
else
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1787_, 0, lean_box(0));
lean_closure_set(v___x_1787_, 1, lean_box(0));
lean_closure_set(v___x_1787_, 2, v_inst_1761_);
lean_closure_set(v___x_1787_, 3, v_inst_1762_);
v___x_1788_ = l_Array_isEqvAux___redArg(v_content_1769_, v_content_1774_, v___x_1787_, v___x_1784_);
lean_dec_ref(v_content_1774_);
lean_dec_ref(v_content_1769_);
if (v___x_1788_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_subParts_1770_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1789_ = lean_array_get_size(v_subParts_1770_);
v___x_1790_ = lean_array_get_size(v_subParts_1775_);
v___x_1791_ = lean_nat_dec_eq(v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_subParts_1770_);
return v___x_1791_;
}
else
{
uint8_t v___x_1792_; 
v___x_1792_ = l_Array_isEqvAux___redArg(v_subParts_1770_, v_subParts_1775_, v___x_1779_, v___x_1789_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_subParts_1770_);
return v___x_1792_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq(lean_object* v_i_1793_, lean_object* v_b_1794_, lean_object* v_p_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_x_1799_, lean_object* v_x_1800_){
_start:
{
uint8_t v___x_1801_; 
v___x_1801_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1796_, v_inst_1797_, v_inst_1798_, v_x_1799_, v_x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___boxed(lean_object* v_i_1802_, lean_object* v_b_1803_, lean_object* v_p_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
uint8_t v_res_1810_; lean_object* v_r_1811_; 
v_res_1810_ = l_Lean_Doc_instBEqPart_beq(v_i_1802_, v_b_1803_, v_p_1804_, v_inst_1805_, v_inst_1806_, v_inst_1807_, v_x_1808_, v_x_1809_);
v_r_1811_ = lean_box(v_res_1810_);
return v_r_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart___redArg(lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1815_, 0, lean_box(0));
lean_closure_set(v___x_1815_, 1, lean_box(0));
lean_closure_set(v___x_1815_, 2, lean_box(0));
lean_closure_set(v___x_1815_, 3, v_inst_1812_);
lean_closure_set(v___x_1815_, 4, v_inst_1813_);
lean_closure_set(v___x_1815_, 5, v_inst_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart(lean_object* v_i_1816_, lean_object* v_b_1817_, lean_object* v_p_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1822_, 0, lean_box(0));
lean_closure_set(v___x_1822_, 1, lean_box(0));
lean_closure_set(v___x_1822_, 2, lean_box(0));
lean_closure_set(v___x_1822_, 3, v_inst_1819_);
lean_closure_set(v___x_1822_, 4, v_inst_1820_);
lean_closure_set(v___x_1822_, 5, v_inst_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___redArg___boxed(lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
uint8_t v_res_1828_; lean_object* v_r_1829_; 
v_res_1828_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1823_, v_inst_1824_, v_inst_1825_, v_x_1826_, v_x_1827_);
v_r_1829_ = lean_box(v_res_1828_);
return v_r_1829_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord___redArg(lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_){
_start:
{
lean_object* v_title_1835_; lean_object* v_titleString_1836_; lean_object* v_metadata_1837_; lean_object* v_content_1838_; lean_object* v_subParts_1839_; lean_object* v_title_1840_; lean_object* v_titleString_1841_; lean_object* v_metadata_1842_; lean_object* v_content_1843_; lean_object* v_subParts_1844_; lean_object* v___x_1845_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_title_1835_ = lean_ctor_get(v_x_1833_, 0);
lean_inc_ref(v_title_1835_);
v_titleString_1836_ = lean_ctor_get(v_x_1833_, 1);
lean_inc_ref(v_titleString_1836_);
v_metadata_1837_ = lean_ctor_get(v_x_1833_, 2);
lean_inc(v_metadata_1837_);
v_content_1838_ = lean_ctor_get(v_x_1833_, 3);
lean_inc_ref(v_content_1838_);
v_subParts_1839_ = lean_ctor_get(v_x_1833_, 4);
lean_inc_ref(v_subParts_1839_);
lean_dec_ref(v_x_1833_);
v_title_1840_ = lean_ctor_get(v_x_1834_, 0);
lean_inc_ref(v_title_1840_);
v_titleString_1841_ = lean_ctor_get(v_x_1834_, 1);
lean_inc_ref(v_titleString_1841_);
v_metadata_1842_ = lean_ctor_get(v_x_1834_, 2);
lean_inc(v_metadata_1842_);
v_content_1843_ = lean_ctor_get(v_x_1834_, 3);
lean_inc_ref(v_content_1843_);
v_subParts_1844_ = lean_ctor_get(v_x_1834_, 4);
lean_inc_ref(v_subParts_1844_);
lean_dec_ref(v_x_1834_);
lean_inc_ref(v_inst_1832_);
lean_inc_ref(v_inst_1831_);
lean_inc_ref_n(v_inst_1830_, 2);
v___x_1845_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___redArg___boxed), 5, 3);
lean_closure_set(v___x_1845_, 0, v_inst_1830_);
lean_closure_set(v___x_1845_, 1, v_inst_1831_);
lean_closure_set(v___x_1845_, 2, v_inst_1832_);
v___x_1850_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1850_, 0, lean_box(0));
lean_closure_set(v___x_1850_, 1, v_inst_1830_);
v___x_1851_ = l_Array_compareLex___redArg(v___x_1850_, v_title_1835_, v_title_1840_);
lean_dec_ref(v_title_1840_);
lean_dec_ref(v_title_1835_);
if (v___x_1851_ == 1)
{
uint8_t v___x_1852_; 
v___x_1852_ = lean_string_compare(v_titleString_1836_, v_titleString_1841_);
lean_dec_ref(v_titleString_1841_);
lean_dec_ref(v_titleString_1836_);
if (v___x_1852_ == 1)
{
if (lean_obj_tag(v_metadata_1837_) == 0)
{
lean_dec_ref(v_inst_1832_);
if (lean_obj_tag(v_metadata_1842_) == 0)
{
goto v___jp_1846_;
}
else
{
uint8_t v___x_1853_; 
lean_dec_ref_known(v_metadata_1842_, 1);
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_content_1843_);
lean_dec_ref(v_subParts_1839_);
lean_dec_ref(v_content_1838_);
lean_dec_ref(v_inst_1831_);
lean_dec_ref(v_inst_1830_);
v___x_1853_ = 0;
return v___x_1853_;
}
}
else
{
if (lean_obj_tag(v_metadata_1842_) == 0)
{
uint8_t v___x_1854_; 
lean_dec_ref_known(v_metadata_1837_, 1);
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_content_1843_);
lean_dec_ref(v_subParts_1839_);
lean_dec_ref(v_content_1838_);
lean_dec_ref(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
lean_dec_ref(v_inst_1830_);
v___x_1854_ = 2;
return v___x_1854_;
}
else
{
lean_object* v_val_1855_; lean_object* v_val_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v_val_1855_ = lean_ctor_get(v_metadata_1837_, 0);
lean_inc(v_val_1855_);
lean_dec_ref_known(v_metadata_1837_, 1);
v_val_1856_ = lean_ctor_get(v_metadata_1842_, 0);
lean_inc(v_val_1856_);
lean_dec_ref_known(v_metadata_1842_, 1);
v___x_1857_ = lean_apply_2(v_inst_1832_, v_val_1855_, v_val_1856_);
v___x_1858_ = lean_unbox(v___x_1857_);
if (v___x_1858_ == 1)
{
goto v___jp_1846_;
}
else
{
uint8_t v___x_1859_; 
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_content_1843_);
lean_dec_ref(v_subParts_1839_);
lean_dec_ref(v_content_1838_);
lean_dec_ref(v_inst_1831_);
lean_dec_ref(v_inst_1830_);
v___x_1859_ = lean_unbox(v___x_1857_);
return v___x_1859_;
}
}
}
}
else
{
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_content_1843_);
lean_dec(v_metadata_1842_);
lean_dec_ref(v_subParts_1839_);
lean_dec_ref(v_content_1838_);
lean_dec(v_metadata_1837_);
lean_dec_ref(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
lean_dec_ref(v_inst_1830_);
return v___x_1852_;
}
}
else
{
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_content_1843_);
lean_dec(v_metadata_1842_);
lean_dec_ref(v_titleString_1841_);
lean_dec_ref(v_subParts_1839_);
lean_dec_ref(v_content_1838_);
lean_dec(v_metadata_1837_);
lean_dec_ref(v_titleString_1836_);
lean_dec_ref(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
lean_dec_ref(v_inst_1830_);
return v___x_1851_;
}
v___jp_1846_:
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1847_, 0, lean_box(0));
lean_closure_set(v___x_1847_, 1, lean_box(0));
lean_closure_set(v___x_1847_, 2, v_inst_1830_);
lean_closure_set(v___x_1847_, 3, v_inst_1831_);
v___x_1848_ = l_Array_compareLex___redArg(v___x_1847_, v_content_1838_, v_content_1843_);
lean_dec_ref(v_content_1843_);
lean_dec_ref(v_content_1838_);
if (v___x_1848_ == 1)
{
uint8_t v___x_1849_; 
v___x_1849_ = l_Array_compareLex___redArg(v___x_1845_, v_subParts_1839_, v_subParts_1844_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_subParts_1839_);
if (v___x_1849_ == 1)
{
return v___x_1849_;
}
else
{
return v___x_1849_;
}
}
else
{
lean_dec_ref(v___x_1845_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_subParts_1839_);
return v___x_1848_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord(lean_object* v_i_1860_, lean_object* v_b_1861_, lean_object* v_p_1862_, lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
uint8_t v___x_1868_; 
v___x_1868_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1863_, v_inst_1864_, v_inst_1865_, v_x_1866_, v_x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___boxed(lean_object* v_i_1869_, lean_object* v_b_1870_, lean_object* v_p_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
uint8_t v_res_1877_; lean_object* v_r_1878_; 
v_res_1877_ = l_Lean_Doc_instOrdPart_ord(v_i_1869_, v_b_1870_, v_p_1871_, v_inst_1872_, v_inst_1873_, v_inst_1874_, v_x_1875_, v_x_1876_);
v_r_1878_ = lean_box(v_res_1877_);
return v_r_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart___redArg(lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_inst_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1882_, 0, lean_box(0));
lean_closure_set(v___x_1882_, 1, lean_box(0));
lean_closure_set(v___x_1882_, 2, lean_box(0));
lean_closure_set(v___x_1882_, 3, v_inst_1879_);
lean_closure_set(v___x_1882_, 4, v_inst_1880_);
lean_closure_set(v___x_1882_, 5, v_inst_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart(lean_object* v_i_1883_, lean_object* v_b_1884_, lean_object* v_p_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1889_, 0, lean_box(0));
lean_closure_set(v___x_1889_, 1, lean_box(0));
lean_closure_set(v___x_1889_, 2, lean_box(0));
lean_closure_set(v___x_1889_, 3, v_inst_1886_);
lean_closure_set(v___x_1889_, 4, v_inst_1887_);
lean_closure_set(v___x_1889_, 5, v_inst_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_unsigned_to_nat(9u);
v___x_1900_ = lean_nat_to_int(v___x_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_unsigned_to_nat(15u);
v___x_1905_ = lean_nat_to_int(v___x_1904_);
return v___x_1905_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_unsigned_to_nat(11u);
v___x_1913_ = lean_nat_to_int(v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg___boxed(lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_x_1920_, lean_object* v_prec_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_1917_, v_inst_1918_, v_inst_1919_, v_x_1920_, v_prec_1921_);
lean_dec(v_prec_1921_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg(lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_x_1926_, lean_object* v_prec_1927_){
_start:
{
lean_object* v_title_1928_; lean_object* v_titleString_1929_; lean_object* v_metadata_1930_; lean_object* v_content_1931_; lean_object* v_subParts_1932_; lean_object* v_localinst_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_title_1928_ = lean_ctor_get(v_x_1926_, 0);
lean_inc_ref(v_title_1928_);
v_titleString_1929_ = lean_ctor_get(v_x_1926_, 1);
lean_inc_ref(v_titleString_1929_);
v_metadata_1930_ = lean_ctor_get(v_x_1926_, 2);
lean_inc(v_metadata_1930_);
v_content_1931_ = lean_ctor_get(v_x_1926_, 3);
lean_inc_ref(v_content_1931_);
v_subParts_1932_ = lean_ctor_get(v_x_1926_, 4);
lean_inc_ref(v_subParts_1932_);
lean_dec_ref(v_x_1926_);
lean_inc_ref(v_inst_1925_);
lean_inc_ref(v_inst_1924_);
lean_inc_ref_n(v_inst_1923_, 2);
v_localinst_1933_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___redArg___boxed), 5, 3);
lean_closure_set(v_localinst_1933_, 0, v_inst_1923_);
lean_closure_set(v_localinst_1933_, 1, v_inst_1924_);
lean_closure_set(v_localinst_1933_, 2, v_inst_1925_);
v___x_1934_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1935_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__3));
v___x_1936_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4);
v___x_1937_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1937_, 0, lean_box(0));
lean_closure_set(v___x_1937_, 1, v_inst_1923_);
v___x_1938_ = l_Array_repr___redArg(v___x_1937_, v_title_1928_);
v___x_1939_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1936_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = 0;
v___x_1941_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1941_, 0, v___x_1939_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*1, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1935_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_box(1);
v___x_1946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1944_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__6));
v___x_1948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v___x_1934_);
v___x_1950_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7);
v___x_1951_ = l_String_quote(v_titleString_1929_);
v___x_1952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1950_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set_uint8(v___x_1954_, sizeof(void*)*1, v___x_1940_);
v___x_1955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1949_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
lean_ctor_set(v___x_1956_, 1, v___x_1943_);
v___x_1957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v___x_1945_);
v___x_1958_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__9));
v___x_1959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v___x_1934_);
v___x_1961_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = l_Option_repr___redArg(v_inst_1925_, v_metadata_1930_, v___x_1962_);
v___x_1964_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1961_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*1, v___x_1940_);
v___x_1966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1960_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
lean_ctor_set(v___x_1967_, 1, v___x_1943_);
v___x_1968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v___x_1945_);
v___x_1969_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__11));
v___x_1970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v___x_1934_);
v___x_1972_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12);
v___x_1973_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1973_, 0, lean_box(0));
lean_closure_set(v___x_1973_, 1, lean_box(0));
lean_closure_set(v___x_1973_, 2, v_inst_1923_);
lean_closure_set(v___x_1973_, 3, v_inst_1924_);
v___x_1974_ = l_Array_repr___redArg(v___x_1973_, v_content_1931_);
v___x_1975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set_uint8(v___x_1976_, sizeof(void*)*1, v___x_1940_);
v___x_1977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1971_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v___x_1943_);
v___x_1979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v___x_1945_);
v___x_1980_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__14));
v___x_1981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v___x_1934_);
v___x_1983_ = l_Array_repr___redArg(v_localinst_1933_, v_subParts_1932_);
v___x_1984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1961_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*1, v___x_1940_);
v___x_1986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1982_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_1988_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_1989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v___x_1986_);
v___x_1990_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_1991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1987_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*1, v___x_1940_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr(lean_object* v_i_1994_, lean_object* v_b_1995_, lean_object* v_p_1996_, lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_inst_1999_, lean_object* v_x_2000_, lean_object* v_prec_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_1997_, v_inst_1998_, v_inst_1999_, v_x_2000_, v_prec_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___boxed(lean_object* v_i_2003_, lean_object* v_b_2004_, lean_object* v_p_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_x_2009_, lean_object* v_prec_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_Doc_instReprPart_repr(v_i_2003_, v_b_2004_, v_p_2005_, v_inst_2006_, v_inst_2007_, v_inst_2008_, v_x_2009_, v_prec_2010_);
lean_dec(v_prec_2010_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart___redArg(lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2015_, 0, lean_box(0));
lean_closure_set(v___x_2015_, 1, lean_box(0));
lean_closure_set(v___x_2015_, 2, lean_box(0));
lean_closure_set(v___x_2015_, 3, v_inst_2012_);
lean_closure_set(v___x_2015_, 4, v_inst_2013_);
lean_closure_set(v___x_2015_, 5, v_inst_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart(lean_object* v_i_2016_, lean_object* v_b_2017_, lean_object* v_p_2018_, lean_object* v_inst_2019_, lean_object* v_inst_2020_, lean_object* v_inst_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2022_, 0, lean_box(0));
lean_closure_set(v___x_2022_, 1, lean_box(0));
lean_closure_set(v___x_2022_, 2, lean_box(0));
lean_closure_set(v___x_2022_, 3, v_inst_2019_);
lean_closure_set(v___x_2022_, 4, v_inst_2020_);
lean_closure_set(v___x_2022_, 5, v_inst_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default(lean_object* v_i_2027_, lean_object* v_b_2028_, lean_object* v_p_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = ((lean_object*)(l_Lean_Doc_instInhabitedPart_default___closed__0));
return v___x_2030_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedPart___closed__0(void){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_Doc_instInhabitedPart_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart(lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart___closed__0, &l_Lean_Doc_instInhabitedPart___closed__0_once, _init_l_Lean_Doc_instInhabitedPart___closed__0);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg(lean_object* v_x_2036_){
_start:
{
lean_inc_ref(v_x_2036_);
return v_x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg___boxed(lean_object* v_x_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_Doc_Part_cast___redArg(v_x_2037_);
lean_dec_ref(v_x_2037_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast(lean_object* v_i_2039_, lean_object* v_i_x27_2040_, lean_object* v_b_2041_, lean_object* v_b_x27_2042_, lean_object* v_p_2043_, lean_object* v_p_x27_2044_, lean_object* v_inlines__eq_2045_, lean_object* v_blocks__eq_2046_, lean_object* v_metadata__eq_2047_, lean_object* v_x_2048_){
_start:
{
lean_inc_ref(v_x_2048_);
return v_x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___boxed(lean_object* v_i_2049_, lean_object* v_i_x27_2050_, lean_object* v_b_2051_, lean_object* v_b_x27_2052_, lean_object* v_p_2053_, lean_object* v_p_x27_2054_, lean_object* v_inlines__eq_2055_, lean_object* v_blocks__eq_2056_, lean_object* v_metadata__eq_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Doc_Part_cast(v_i_2049_, v_i_x27_2050_, v_b_2051_, v_b_x27_2052_, v_p_2053_, v_p_x27_2054_, v_inlines__eq_2055_, v_blocks__eq_2056_, v_metadata__eq_2057_, v_x_2058_);
lean_dec_ref(v_x_2058_);
return v_res_2059_;
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
