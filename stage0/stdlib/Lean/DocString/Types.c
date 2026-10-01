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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
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
lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_373_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_371_);
v___x_374_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_372_);
v___x_375_ = lean_nat_dec_lt(v___x_373_, v___x_374_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; 
v___x_376_ = lean_nat_dec_eq(v___x_373_, v___x_374_);
lean_dec(v___x_374_);
lean_dec(v___x_373_);
if (v___x_376_ == 0)
{
uint8_t v___x_377_; 
lean_dec_ref(v_x_372_);
lean_dec_ref(v_x_371_);
lean_dec_ref(v_inst_370_);
v___x_377_ = 2;
return v___x_377_;
}
else
{
lean_object* v___x_378_; 
lean_inc_ref(v_inst_370_);
v___x_378_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___redArg___boxed), 3, 1);
lean_closure_set(v___x_378_, 0, v_inst_370_);
switch(lean_obj_tag(v_x_371_))
{
case 1:
{
lean_object* v_content_379_; lean_object* v_content_380_; uint8_t v___x_381_; 
lean_dec_ref(v_inst_370_);
v_content_379_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_379_);
lean_dec_ref_known(v_x_371_, 1);
v_content_380_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_380_);
lean_dec_ref(v_x_372_);
v___x_381_ = l_Array_compareLex___redArg(v___x_378_, v_content_379_, v_content_380_);
lean_dec_ref(v_content_380_);
lean_dec_ref(v_content_379_);
return v___x_381_;
}
case 2:
{
lean_object* v_content_382_; lean_object* v_content_383_; uint8_t v___x_384_; 
lean_dec_ref(v_inst_370_);
v_content_382_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_382_);
lean_dec_ref_known(v_x_371_, 1);
v_content_383_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_383_);
lean_dec_ref(v_x_372_);
v___x_384_ = l_Array_compareLex___redArg(v___x_378_, v_content_382_, v_content_383_);
lean_dec_ref(v_content_383_);
lean_dec_ref(v_content_382_);
return v___x_384_;
}
case 4:
{
uint8_t v_mode_385_; lean_object* v_string_386_; uint8_t v_mode_387_; lean_object* v_string_388_; uint8_t v___x_389_; 
lean_dec_ref(v___x_378_);
lean_dec_ref(v_inst_370_);
v_mode_385_ = lean_ctor_get_uint8(v_x_371_, sizeof(void*)*1);
v_string_386_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_string_386_);
lean_dec_ref_known(v_x_371_, 1);
v_mode_387_ = lean_ctor_get_uint8(v_x_372_, sizeof(void*)*1);
v_string_388_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_string_388_);
lean_dec_ref(v_x_372_);
v___x_389_ = l_Lean_Doc_instOrdMathMode_ord(v_mode_385_, v_mode_387_);
if (v___x_389_ == 1)
{
uint8_t v___x_390_; 
v___x_390_ = lean_string_compare(v_string_386_, v_string_388_);
lean_dec_ref(v_string_388_);
lean_dec_ref(v_string_386_);
return v___x_390_;
}
else
{
lean_dec_ref(v_string_388_);
lean_dec_ref(v_string_386_);
return v___x_389_;
}
}
case 6:
{
lean_object* v_content_391_; lean_object* v_url_392_; lean_object* v_content_393_; lean_object* v_url_394_; uint8_t v___x_395_; 
lean_dec_ref(v_inst_370_);
v_content_391_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_391_);
v_url_392_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_url_392_);
lean_dec_ref_known(v_x_371_, 2);
v_content_393_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_393_);
v_url_394_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_url_394_);
lean_dec_ref(v_x_372_);
v___x_395_ = l_Array_compareLex___redArg(v___x_378_, v_content_391_, v_content_393_);
lean_dec_ref(v_content_393_);
lean_dec_ref(v_content_391_);
if (v___x_395_ == 1)
{
uint8_t v___x_396_; 
v___x_396_ = lean_string_compare(v_url_392_, v_url_394_);
lean_dec_ref(v_url_394_);
lean_dec_ref(v_url_392_);
return v___x_396_;
}
else
{
lean_dec_ref(v_url_394_);
lean_dec_ref(v_url_392_);
return v___x_395_;
}
}
case 7:
{
lean_object* v_name_397_; lean_object* v_content_398_; lean_object* v_name_399_; lean_object* v_content_400_; uint8_t v___x_401_; 
lean_dec_ref(v_inst_370_);
v_name_397_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_name_397_);
v_content_398_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_content_398_);
lean_dec_ref_known(v_x_371_, 2);
v_name_399_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_name_399_);
v_content_400_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_content_400_);
lean_dec_ref(v_x_372_);
v___x_401_ = lean_string_compare(v_name_397_, v_name_399_);
lean_dec_ref(v_name_399_);
lean_dec_ref(v_name_397_);
if (v___x_401_ == 1)
{
uint8_t v___x_402_; 
v___x_402_ = l_Array_compareLex___redArg(v___x_378_, v_content_398_, v_content_400_);
lean_dec_ref(v_content_400_);
lean_dec_ref(v_content_398_);
return v___x_402_;
}
else
{
lean_dec_ref(v_content_400_);
lean_dec_ref(v_content_398_);
lean_dec_ref(v___x_378_);
return v___x_401_;
}
}
case 8:
{
lean_object* v_alt_403_; lean_object* v_url_404_; lean_object* v_alt_405_; lean_object* v_url_406_; uint8_t v___x_407_; 
lean_dec_ref(v___x_378_);
lean_dec_ref(v_inst_370_);
v_alt_403_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_alt_403_);
v_url_404_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_url_404_);
lean_dec_ref_known(v_x_371_, 2);
v_alt_405_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_alt_405_);
v_url_406_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_url_406_);
lean_dec_ref(v_x_372_);
v___x_407_ = lean_string_compare(v_alt_403_, v_alt_405_);
lean_dec_ref(v_alt_405_);
lean_dec_ref(v_alt_403_);
if (v___x_407_ == 1)
{
uint8_t v___x_408_; 
v___x_408_ = lean_string_compare(v_url_404_, v_url_406_);
lean_dec_ref(v_url_406_);
lean_dec_ref(v_url_404_);
return v___x_408_;
}
else
{
lean_dec_ref(v_url_406_);
lean_dec_ref(v_url_404_);
return v___x_407_;
}
}
case 9:
{
lean_object* v_content_409_; lean_object* v_content_410_; uint8_t v___x_411_; 
lean_dec_ref(v_inst_370_);
v_content_409_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_409_);
lean_dec_ref_known(v_x_371_, 1);
v_content_410_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_410_);
lean_dec_ref(v_x_372_);
v___x_411_ = l_Array_compareLex___redArg(v___x_378_, v_content_409_, v_content_410_);
lean_dec_ref(v_content_410_);
lean_dec_ref(v_content_409_);
return v___x_411_;
}
case 10:
{
lean_object* v_container_412_; lean_object* v_content_413_; lean_object* v_container_414_; lean_object* v_content_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_container_412_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_container_412_);
v_content_413_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_content_413_);
lean_dec_ref_known(v_x_371_, 2);
v_container_414_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_container_414_);
v_content_415_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_content_415_);
lean_dec_ref(v_x_372_);
v___x_416_ = lean_apply_2(v_inst_370_, v_container_412_, v_container_414_);
v___x_417_ = lean_unbox(v___x_416_);
if (v___x_417_ == 1)
{
uint8_t v___x_418_; 
v___x_418_ = l_Array_compareLex___redArg(v___x_378_, v_content_413_, v_content_415_);
lean_dec_ref(v_content_415_);
lean_dec_ref(v_content_413_);
return v___x_418_;
}
else
{
uint8_t v___x_419_; 
lean_dec_ref(v_content_415_);
lean_dec_ref(v_content_413_);
lean_dec_ref(v___x_378_);
v___x_419_ = lean_unbox(v___x_416_);
return v___x_419_;
}
}
default: 
{
lean_object* v_string_420_; lean_object* v_string_421_; uint8_t v___x_422_; 
lean_dec_ref(v___x_378_);
lean_dec_ref(v_inst_370_);
v_string_420_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_string_420_);
lean_dec_ref(v_x_371_);
v_string_421_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_string_421_);
lean_dec_ref(v_x_372_);
v___x_422_ = lean_string_compare(v_string_420_, v_string_421_);
lean_dec_ref(v_string_421_);
lean_dec_ref(v_string_420_);
return v___x_422_;
}
}
}
}
else
{
uint8_t v___x_423_; 
lean_dec(v___x_374_);
lean_dec(v___x_373_);
lean_dec_ref(v_x_372_);
lean_dec_ref(v_x_371_);
lean_dec_ref(v_inst_370_);
v___x_423_ = 0;
return v___x_423_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord(lean_object* v_i_424_, lean_object* v_inst_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_425_, v_x_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___boxed(lean_object* v_i_429_, lean_object* v_inst_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Lean_Doc_instOrdInline_ord(v_i_429_, v_inst_430_, v_x_431_, v_x_432_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline___redArg(lean_object* v_inst_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_436_, 0, lean_box(0));
lean_closure_set(v___x_436_, 1, v_inst_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline(lean_object* v_i_437_, lean_object* v_inst_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_439_, 0, lean_box(0));
lean_closure_set(v___x_439_, 1, v_inst_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg___boxed(lean_object* v_inst_506_, lean_object* v_x_507_, lean_object* v_prec_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_506_, v_x_507_, v_prec_508_);
lean_dec(v_prec_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg(lean_object* v_inst_510_, lean_object* v_x_511_, lean_object* v_prec_512_){
_start:
{
lean_object* v_localinst_513_; 
lean_inc_ref(v_inst_510_);
v_localinst_513_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_513_, 0, v_inst_510_);
switch(lean_obj_tag(v_x_511_))
{
case 0:
{
lean_object* v_string_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_534_; 
lean_dec_ref(v_localinst_513_);
lean_dec_ref(v_inst_510_);
v_string_514_ = lean_ctor_get(v_x_511_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_534_ == 0)
{
v___x_516_ = v_x_511_;
v_isShared_517_ = v_isSharedCheck_534_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_string_514_);
lean_dec(v_x_511_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_534_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___y_519_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(1024u);
v___x_531_ = lean_nat_dec_le(v___x_530_, v_prec_512_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_519_ = v___x_532_;
goto v___jp_518_;
}
else
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_519_ = v___x_533_;
goto v___jp_518_;
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__2));
v___x_521_ = l_String_quote(v_string_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 3);
lean_ctor_set(v___x_516_, 0, v___x_521_);
v___x_523_ = v___x_516_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_529_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_520_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
lean_inc(v___y_519_);
v___x_525_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_525_, 0, v___y_519_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = 0;
v___x_527_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*1, v___x_526_);
v___x_528_ = l_Repr_addAppParen(v___x_527_, v_prec_512_);
return v___x_528_;
}
}
}
}
case 1:
{
lean_object* v_content_535_; lean_object* v___y_537_; lean_object* v___x_545_; uint8_t v___x_546_; 
lean_dec_ref(v_inst_510_);
v_content_535_ = lean_ctor_get(v_x_511_, 0);
lean_inc_ref(v_content_535_);
lean_dec_ref_known(v_x_511_, 1);
v___x_545_ = lean_unsigned_to_nat(1024u);
v___x_546_ = lean_nat_dec_le(v___x_545_, v_prec_512_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
v___x_547_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_537_ = v___x_547_;
goto v___jp_536_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_537_ = v___x_548_;
goto v___jp_536_;
}
v___jp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_538_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__5));
v___x_539_ = l_Array_repr___redArg(v_localinst_513_, v_content_535_);
v___x_540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
lean_inc(v___y_537_);
v___x_541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_541_, 0, v___y_537_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = 0;
v___x_543_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*1, v___x_542_);
v___x_544_ = l_Repr_addAppParen(v___x_543_, v_prec_512_);
return v___x_544_;
}
}
case 2:
{
lean_object* v_content_549_; lean_object* v___y_551_; lean_object* v___x_559_; uint8_t v___x_560_; 
lean_dec_ref(v_inst_510_);
v_content_549_ = lean_ctor_get(v_x_511_, 0);
lean_inc_ref(v_content_549_);
lean_dec_ref_known(v_x_511_, 1);
v___x_559_ = lean_unsigned_to_nat(1024u);
v___x_560_ = lean_nat_dec_le(v___x_559_, v_prec_512_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_551_ = v___x_561_;
goto v___jp_550_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_551_ = v___x_562_;
goto v___jp_550_;
}
v___jp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_552_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__8));
v___x_553_ = l_Array_repr___redArg(v_localinst_513_, v_content_549_);
v___x_554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
lean_inc(v___y_551_);
v___x_555_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_555_, 0, v___y_551_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = 0;
v___x_557_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*1, v___x_556_);
v___x_558_ = l_Repr_addAppParen(v___x_557_, v_prec_512_);
return v___x_558_;
}
}
case 3:
{
lean_object* v_string_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v_localinst_513_);
lean_dec_ref(v_inst_510_);
v_string_563_ = lean_ctor_get(v_x_511_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_583_ == 0)
{
v___x_565_ = v_x_511_;
v_isShared_566_ = v_isSharedCheck_583_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_string_563_);
lean_dec(v_x_511_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_583_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___y_568_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(1024u);
v___x_580_ = lean_nat_dec_le(v___x_579_, v_prec_512_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_568_ = v___x_581_;
goto v___jp_567_;
}
else
{
lean_object* v___x_582_; 
v___x_582_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_568_ = v___x_582_;
goto v___jp_567_;
}
v___jp_567_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__11));
v___x_570_ = l_String_quote(v_string_563_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_570_);
v___x_572_ = v___x_565_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_578_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_569_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
lean_inc(v___y_568_);
v___x_574_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_574_, 0, v___y_568_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = 0;
v___x_576_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*1, v___x_575_);
v___x_577_ = l_Repr_addAppParen(v___x_576_, v_prec_512_);
return v___x_577_;
}
}
}
}
case 4:
{
uint8_t v_mode_584_; lean_object* v_string_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v_localinst_513_);
lean_dec_ref(v_inst_510_);
v_mode_584_ = lean_ctor_get_uint8(v_x_511_, sizeof(void*)*1);
v_string_585_ = lean_ctor_get(v_x_511_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_610_ == 0)
{
v___x_587_ = v_x_511_;
v_isShared_588_ = v_isSharedCheck_610_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_string_585_);
lean_dec(v_x_511_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_610_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___y_590_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1024u);
v___x_607_ = lean_nat_dec_le(v___x_606_, v_prec_512_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
v___x_608_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_590_ = v___x_608_;
goto v___jp_589_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_590_ = v___x_609_;
goto v___jp_589_;
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_603_; 
v___x_591_ = lean_box(1);
v___x_592_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__14));
v___x_593_ = lean_unsigned_to_nat(1024u);
v___x_594_ = l_Lean_Doc_instReprMathMode_repr(v_mode_584_, v___x_593_);
v___x_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_592_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_591_);
v___x_597_ = l_String_quote(v_string_585_);
v___x_598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_596_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_inc(v___y_590_);
v___x_600_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_600_, 0, v___y_590_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = 0;
if (v_isShared_588_ == 0)
{
lean_ctor_set_tag(v___x_587_, 6);
lean_ctor_set(v___x_587_, 0, v___x_600_);
v___x_603_ = v___x_587_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_600_);
v___x_603_ = v_reuseFailAlloc_605_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; 
lean_ctor_set_uint8(v___x_603_, sizeof(void*)*1, v___x_601_);
v___x_604_ = l_Repr_addAppParen(v___x_603_, v_prec_512_);
return v___x_604_;
}
}
}
}
case 5:
{
lean_object* v_string_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_localinst_513_);
lean_dec_ref(v_inst_510_);
v_string_611_ = lean_ctor_get(v_x_511_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_631_ == 0)
{
v___x_613_ = v_x_511_;
v_isShared_614_ = v_isSharedCheck_631_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_string_611_);
lean_dec(v_x_511_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_631_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___y_616_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(1024u);
v___x_628_ = lean_nat_dec_le(v___x_627_, v_prec_512_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_616_ = v___x_629_;
goto v___jp_615_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_616_ = v___x_630_;
goto v___jp_615_;
}
v___jp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_617_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__17));
v___x_618_ = l_String_quote(v_string_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 3);
lean_ctor_set(v___x_613_, 0, v___x_618_);
v___x_620_ = v___x_613_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_626_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_617_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_inc(v___y_616_);
v___x_622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_622_, 0, v___y_616_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = 0;
v___x_624_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*1, v___x_623_);
v___x_625_ = l_Repr_addAppParen(v___x_624_, v_prec_512_);
return v___x_625_;
}
}
}
}
case 6:
{
lean_object* v_content_632_; lean_object* v_url_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v_inst_510_);
v_content_632_ = lean_ctor_get(v_x_511_, 0);
v_url_633_ = lean_ctor_get(v_x_511_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_657_ == 0)
{
v___x_635_ = v_x_511_;
v_isShared_636_ = v_isSharedCheck_657_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_url_633_);
lean_inc(v_content_632_);
lean_dec(v_x_511_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_657_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___y_638_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(1024u);
v___x_654_ = lean_nat_dec_le(v___x_653_, v_prec_512_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_638_ = v___x_655_;
goto v___jp_637_;
}
else
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_638_ = v___x_656_;
goto v___jp_637_;
}
v___jp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_639_ = lean_box(1);
v___x_640_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__20));
v___x_641_ = l_Array_repr___redArg(v_localinst_513_, v_content_632_);
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 5);
lean_ctor_set(v___x_635_, 1, v___x_641_);
lean_ctor_set(v___x_635_, 0, v___x_640_);
v___x_643_ = v___x_635_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_652_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_639_);
v___x_645_ = l_String_quote(v_url_633_);
v___x_646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_644_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_inc(v___y_638_);
v___x_648_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_648_, 0, v___y_638_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = 0;
v___x_650_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*1, v___x_649_);
v___x_651_ = l_Repr_addAppParen(v___x_650_, v_prec_512_);
return v___x_651_;
}
}
}
}
case 7:
{
lean_object* v_name_658_; lean_object* v_content_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_inst_510_);
v_name_658_ = lean_ctor_get(v_x_511_, 0);
v_content_659_ = lean_ctor_get(v_x_511_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_683_ == 0)
{
v___x_661_ = v_x_511_;
v_isShared_662_ = v_isSharedCheck_683_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_content_659_);
lean_inc(v_name_658_);
lean_dec(v_x_511_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_683_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___y_664_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_unsigned_to_nat(1024u);
v___x_680_ = lean_nat_dec_le(v___x_679_, v_prec_512_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_664_ = v___x_681_;
goto v___jp_663_;
}
else
{
lean_object* v___x_682_; 
v___x_682_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_664_ = v___x_682_;
goto v___jp_663_;
}
v___jp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_665_ = lean_box(1);
v___x_666_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__23));
v___x_667_ = l_String_quote(v_name_658_);
v___x_668_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 5);
lean_ctor_set(v___x_661_, 1, v___x_668_);
lean_ctor_set(v___x_661_, 0, v___x_666_);
v___x_670_ = v___x_661_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_668_);
v___x_670_ = v_reuseFailAlloc_678_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_665_);
v___x_672_ = l_Array_repr___redArg(v_localinst_513_, v_content_659_);
v___x_673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
lean_inc(v___y_664_);
v___x_674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_664_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = 0;
v___x_676_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*1, v___x_675_);
v___x_677_ = l_Repr_addAppParen(v___x_676_, v_prec_512_);
return v___x_677_;
}
}
}
}
case 8:
{
lean_object* v_alt_684_; lean_object* v_url_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v_localinst_513_);
lean_dec_ref(v_inst_510_);
v_alt_684_ = lean_ctor_get(v_x_511_, 0);
v_url_685_ = lean_ctor_get(v_x_511_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_710_ == 0)
{
v___x_687_ = v_x_511_;
v_isShared_688_ = v_isSharedCheck_710_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_url_685_);
lean_inc(v_alt_684_);
lean_dec(v_x_511_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_710_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___y_690_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_unsigned_to_nat(1024u);
v___x_707_ = lean_nat_dec_le(v___x_706_, v_prec_512_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_690_ = v___x_708_;
goto v___jp_689_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_690_ = v___x_709_;
goto v___jp_689_;
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_691_ = lean_box(1);
v___x_692_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__26));
v___x_693_ = l_String_quote(v_alt_684_);
v___x_694_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
if (v_isShared_688_ == 0)
{
lean_ctor_set_tag(v___x_687_, 5);
lean_ctor_set(v___x_687_, 1, v___x_694_);
lean_ctor_set(v___x_687_, 0, v___x_692_);
v___x_696_ = v___x_687_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_705_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_691_);
v___x_698_ = l_String_quote(v_url_685_);
v___x_699_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
v___x_700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_697_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
lean_inc(v___y_690_);
v___x_701_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_701_, 0, v___y_690_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = 0;
v___x_703_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*1, v___x_702_);
v___x_704_ = l_Repr_addAppParen(v___x_703_, v_prec_512_);
return v___x_704_;
}
}
}
}
case 9:
{
lean_object* v_content_711_; lean_object* v___y_713_; lean_object* v___x_721_; uint8_t v___x_722_; 
lean_dec_ref(v_inst_510_);
v_content_711_ = lean_ctor_get(v_x_511_, 0);
lean_inc_ref(v_content_711_);
lean_dec_ref_known(v_x_511_, 1);
v___x_721_ = lean_unsigned_to_nat(1024u);
v___x_722_ = lean_nat_dec_le(v___x_721_, v_prec_512_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
v___x_723_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_713_ = v___x_723_;
goto v___jp_712_;
}
else
{
lean_object* v___x_724_; 
v___x_724_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_713_ = v___x_724_;
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_714_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__29));
v___x_715_ = l_Array_repr___redArg(v_localinst_513_, v_content_711_);
v___x_716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
lean_inc(v___y_713_);
v___x_717_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_717_, 0, v___y_713_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = 0;
v___x_719_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*1, v___x_718_);
v___x_720_ = l_Repr_addAppParen(v___x_719_, v_prec_512_);
return v___x_720_;
}
}
default: 
{
lean_object* v_container_725_; lean_object* v_content_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_750_; 
v_container_725_ = lean_ctor_get(v_x_511_, 0);
v_content_726_ = lean_ctor_get(v_x_511_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_750_ == 0)
{
v___x_728_ = v_x_511_;
v_isShared_729_ = v_isSharedCheck_750_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_content_726_);
lean_inc(v_container_725_);
lean_dec(v_x_511_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_750_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___y_731_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_unsigned_to_nat(1024u);
v___x_747_ = lean_nat_dec_le(v___x_746_, v_prec_512_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_731_ = v___x_748_;
goto v___jp_730_;
}
else
{
lean_object* v___x_749_; 
v___x_749_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_731_ = v___x_749_;
goto v___jp_730_;
}
v___jp_730_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_732_ = lean_box(1);
v___x_733_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__32));
v___x_734_ = lean_unsigned_to_nat(1024u);
v___x_735_ = lean_apply_2(v_inst_510_, v_container_725_, v___x_734_);
if (v_isShared_729_ == 0)
{
lean_ctor_set_tag(v___x_728_, 5);
lean_ctor_set(v___x_728_, 1, v___x_735_);
lean_ctor_set(v___x_728_, 0, v___x_733_);
v___x_737_ = v___x_728_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_745_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_732_);
v___x_739_ = l_Array_repr___redArg(v_localinst_513_, v_content_726_);
v___x_740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
lean_inc(v___y_731_);
v___x_741_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_741_, 0, v___y_731_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = 0;
v___x_743_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*1, v___x_742_);
v___x_744_ = l_Repr_addAppParen(v___x_743_, v_prec_512_);
return v___x_744_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr(lean_object* v_i_751_, lean_object* v_inst_752_, lean_object* v_x_753_, lean_object* v_prec_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_752_, v_x_753_, v_prec_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___boxed(lean_object* v_i_756_, lean_object* v_inst_757_, lean_object* v_x_758_, lean_object* v_prec_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Doc_instReprInline_repr(v_i_756_, v_inst_757_, v_x_758_, v_prec_759_);
lean_dec(v_prec_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline___redArg(lean_object* v_inst_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_762_, 0, lean_box(0));
lean_closure_set(v___x_762_, 1, v_inst_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline(lean_object* v_i_763_, lean_object* v_inst_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_765_, 0, lean_box(0));
lean_closure_set(v___x_765_, 1, v_inst_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg(){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = ((lean_object*)(l_Lean_Doc_instInhabitedInline_default___redArg___closed__1));
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg___boxed(lean_object* v___dummy_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Doc_instInhabitedInline_default___redArg();
return v_res_772_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedInline_default___closed__0(void){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Doc_instInhabitedInline_default___redArg();
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default(lean_object* v_i_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg(){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg___boxed(lean_object* v___dummy_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Doc_instInhabitedInline___redArg();
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline(lean_object* v_a_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg(lean_object* v_x_782_){
_start:
{
lean_inc_ref(v_x_782_);
return v_x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg___boxed(lean_object* v_x_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Doc_Inline_cast___redArg(v_x_783_);
lean_dec_ref(v_x_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast(lean_object* v_i_785_, lean_object* v_i_x27_786_, lean_object* v_inlines__eq_787_, lean_object* v_x_788_){
_start:
{
lean_inc_ref(v_x_788_);
return v_x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___boxed(lean_object* v_i_789_, lean_object* v_i_x27_790_, lean_object* v_inlines__eq_791_, lean_object* v_x_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_Doc_Inline_cast(v_i_789_, v_i_x27_790_, v_inlines__eq_791_, v_x_792_);
lean_dec_ref(v_x_792_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___lam__0(lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
if (lean_obj_tag(v_x_794_) == 9)
{
lean_object* v_content_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_content_796_ = lean_ctor_get(v_x_794_, 0);
v___x_797_ = lean_array_get_size(v_content_796_);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_nat_dec_eq(v___x_797_, v___x_798_);
if (v___x_799_ == 0)
{
if (lean_obj_tag(v_x_795_) == 9)
{
lean_object* v_content_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_810_; 
v_content_800_ = lean_ctor_get(v_x_795_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_x_795_);
if (v_isSharedCheck_810_ == 0)
{
v___x_802_ = v_x_795_;
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_content_800_);
lean_dec(v_x_795_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = lean_array_get_size(v_content_800_);
v___x_805_ = lean_nat_dec_eq(v___x_804_, v___x_798_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_inc_ref(v_content_796_);
lean_dec_ref_known(v_x_794_, 1);
v___x_806_ = l_Array_append___redArg(v_content_796_, v_content_800_);
lean_dec_ref(v_content_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_806_);
v___x_808_ = v___x_802_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_del_object(v___x_802_);
lean_dec_ref(v_content_800_);
return v_x_794_;
}
}
}
else
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_818_; 
lean_inc_ref(v_content_796_);
v_isSharedCheck_818_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_x_794_, 0);
lean_dec(v_unused_819_);
v___x_812_ = v_x_794_;
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
else
{
lean_dec(v_x_794_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_array_push(v_content_796_, v_x_795_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_dec_ref_known(v_x_794_, 1);
return v_x_795_;
}
}
else
{
if (lean_obj_tag(v_x_795_) == 9)
{
lean_object* v_content_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_834_; 
v_content_820_ = lean_ctor_get(v_x_795_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_x_795_);
if (v_isSharedCheck_834_ == 0)
{
v___x_822_ = v_x_795_;
v_isShared_823_ = v_isSharedCheck_834_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_content_820_);
lean_dec(v_x_795_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_834_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_824_ = lean_array_get_size(v_content_820_);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_nat_dec_eq(v___x_824_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_mk_empty_array_with_capacity(v___x_827_);
v___x_829_ = lean_array_push(v___x_828_, v_x_794_);
v___x_830_ = l_Array_append___redArg(v___x_829_, v_content_820_);
lean_dec_ref(v_content_820_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_830_);
v___x_832_ = v___x_822_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
else
{
lean_del_object(v___x_822_);
lean_dec_ref(v_content_820_);
return v_x_794_;
}
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_835_ = lean_unsigned_to_nat(2u);
v___x_836_ = lean_mk_empty_array_with_capacity(v___x_835_);
v___x_837_ = lean_array_push(v___x_836_, v_x_794_);
v___x_838_ = lean_array_push(v___x_837_, v_x_795_);
v___x_839_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg(){
_start:
{
lean_object* v___f_842_; 
v___f_842_ = ((lean_object*)(l_Lean_Doc_instAppendInline___redArg___closed__0));
return v___f_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___boxed(lean_object* v___dummy_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Doc_instAppendInline___redArg();
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline(lean_object* v_i_845_){
_start:
{
lean_object* v___f_846_; 
v___f_846_ = ((lean_object*)(l_Lean_Doc_instAppendInline___redArg___closed__0));
return v___f_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg(){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = ((lean_object*)(l_Lean_Doc_Inline_empty___redArg___closed__1));
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg___boxed(lean_object* v___dummy_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Doc_Inline_empty___redArg();
return v_res_854_;
}
}
static lean_object* _init_l_Lean_Doc_Inline_empty___closed__0(void){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Doc_Inline_empty___redArg();
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty(lean_object* v_i_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = lean_obj_once(&l_Lean_Doc_Inline_empty___closed__0, &l_Lean_Doc_Inline_empty___closed__0_once, _init_l_Lean_Doc_Inline_empty___closed__0);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_unsigned_to_nat(12u);
v___x_872_ = lean_nat_to_int(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__0));
v___x_875_ = lean_string_length(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9);
v___x_877_ = lean_nat_to_int(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___redArg(lean_object* v_inst_882_, lean_object* v_x_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_884_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__6));
v___x_885_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_886_ = l_Array_repr___redArg(v_inst_882_, v_x_883_);
v___x_887_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = 0;
v___x_889_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*1, v___x_888_);
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_884_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_892_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v___x_890_);
v___x_894_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_891_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1, v___x_888_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr(lean_object* v_00_u03b1_898_, lean_object* v_inst_899_, lean_object* v_x_900_, lean_object* v_prec_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Doc_instReprListItem_repr___redArg(v_inst_899_, v_x_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___boxed(lean_object* v_00_u03b1_903_, lean_object* v_inst_904_, lean_object* v_x_905_, lean_object* v_prec_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Doc_instReprListItem_repr(v_00_u03b1_903_, v_inst_904_, v_x_905_, v_prec_906_);
lean_dec(v_prec_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem___redArg(lean_object* v_inst_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_909_, 0, lean_box(0));
lean_closure_set(v___x_909_, 1, v_inst_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem(lean_object* v_00_u03b1_910_, lean_object* v_inst_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_912_, 0, lean_box(0));
lean_closure_set(v___x_912_, 1, v_inst_911_);
return v___x_912_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq___redArg(lean_object* v_inst_913_, lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_916_ = lean_array_get_size(v_x_914_);
v___x_917_ = lean_array_get_size(v_x_915_);
v___x_918_ = lean_nat_dec_eq(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_dec_ref(v_inst_913_);
return v___x_918_;
}
else
{
uint8_t v___x_919_; 
v___x_919_ = l_Array_isEqvAux___redArg(v_x_914_, v_x_915_, v_inst_913_, v___x_916_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___redArg___boxed(lean_object* v_inst_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_920_, v_x_921_, v_x_922_);
lean_dec_ref(v_x_922_);
lean_dec_ref(v_x_921_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq(lean_object* v_00_u03b1_925_, lean_object* v_inst_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_926_, v_x_927_, v_x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___boxed(lean_object* v_00_u03b1_930_, lean_object* v_inst_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
uint8_t v_res_934_; lean_object* v_r_935_; 
v_res_934_ = l_Lean_Doc_instBEqListItem_beq(v_00_u03b1_930_, v_inst_931_, v_x_932_, v_x_933_);
lean_dec_ref(v_x_933_);
lean_dec_ref(v_x_932_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem___redArg(lean_object* v_inst_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_937_, 0, lean_box(0));
lean_closure_set(v___x_937_, 1, v_inst_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem(lean_object* v_00_u03b1_938_, lean_object* v_inst_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_940_, 0, lean_box(0));
lean_closure_set(v___x_940_, 1, v_inst_939_);
return v___x_940_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord___redArg(lean_object* v_inst_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
uint8_t v___x_944_; 
v___x_944_ = l_Array_compareLex___redArg(v_inst_941_, v_x_942_, v_x_943_);
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
v___x_954_ = l_Array_compareLex___redArg(v_inst_951_, v_x_952_, v_x_953_);
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
lean_object* v_term_1106_; lean_object* v_desc_1107_; lean_object* v_term_1108_; lean_object* v_desc_1109_; uint8_t v___x_1110_; 
v_term_1106_ = lean_ctor_get(v_x_1104_, 0);
v_desc_1107_ = lean_ctor_get(v_x_1104_, 1);
v_term_1108_ = lean_ctor_get(v_x_1105_, 0);
v_desc_1109_ = lean_ctor_get(v_x_1105_, 1);
v___x_1110_ = l_Array_compareLex___redArg(v_inst_1102_, v_term_1106_, v_term_1108_);
if (v___x_1110_ == 1)
{
uint8_t v___x_1111_; 
v___x_1111_ = l_Array_compareLex___redArg(v_inst_1103_, v_desc_1107_, v_desc_1109_);
return v___x_1111_;
}
else
{
lean_dec_ref(v_inst_1103_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___redArg___boxed(lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
uint8_t v_res_1116_; lean_object* v_r_1117_; 
v_res_1116_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1112_, v_inst_1113_, v_x_1114_, v_x_1115_);
lean_dec_ref(v_x_1115_);
lean_dec_ref(v_x_1114_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord(lean_object* v_00_u03b1_1118_, lean_object* v_00_u03b2_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
uint8_t v___x_1124_; 
v___x_1124_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1120_, v_inst_1121_, v_x_1122_, v_x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Lean_Doc_instOrdDescItem_ord(v_00_u03b1_1125_, v_00_u03b2_1126_, v_inst_1127_, v_inst_1128_, v_x_1129_, v_x_1130_);
lean_dec_ref(v_x_1130_);
lean_dec_ref(v_x_1129_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem___redArg(lean_object* v_inst_1133_, lean_object* v_inst_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1135_, 0, lean_box(0));
lean_closure_set(v___x_1135_, 1, lean_box(0));
lean_closure_set(v___x_1135_, 2, v_inst_1133_);
lean_closure_set(v___x_1135_, 3, v_inst_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1140_, 0, lean_box(0));
lean_closure_set(v___x_1140_, 1, lean_box(0));
lean_closure_set(v___x_1140_, 2, v_inst_1138_);
lean_closure_set(v___x_1140_, 3, v_inst_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg(){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = ((lean_object*)(l_Lean_Doc_instInhabitedDescItem_default___redArg___closed__0));
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg___boxed(lean_object* v___dummy_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
return v_res_1146_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0(void){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default(lean_object* v_00_u03b1_1148_, lean_object* v_00_u03b2_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg(){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg___boxed(lean_object* v___dummy_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Doc_instInhabitedDescItem___redArg();
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem(lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg(lean_object* v_x_1158_){
_start:
{
switch(lean_obj_tag(v_x_1158_))
{
case 0:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
return v___x_1159_;
}
case 1:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_unsigned_to_nat(1u);
return v___x_1160_;
}
case 2:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_unsigned_to_nat(2u);
return v___x_1161_;
}
case 3:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_unsigned_to_nat(3u);
return v___x_1162_;
}
case 4:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_unsigned_to_nat(4u);
return v___x_1163_;
}
case 5:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_unsigned_to_nat(5u);
return v___x_1164_;
}
case 6:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_unsigned_to_nat(6u);
return v___x_1165_;
}
default: 
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_unsigned_to_nat(7u);
return v___x_1166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg___boxed(lean_object* v_x_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1167_);
lean_dec_ref(v_x_1167_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx(lean_object* v_i_1169_, lean_object* v_b_1170_, lean_object* v_x_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___boxed(lean_object* v_i_1173_, lean_object* v_b_1174_, lean_object* v_x_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Doc_Block_ctorIdx(v_i_1173_, v_b_1174_, v_x_1175_);
lean_dec_ref(v_x_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___redArg(lean_object* v_t_1177_, lean_object* v_k_1178_){
_start:
{
switch(lean_obj_tag(v_t_1177_))
{
case 3:
{
lean_object* v_start_1179_; lean_object* v_items_1180_; lean_object* v___x_1181_; 
v_start_1179_ = lean_ctor_get(v_t_1177_, 0);
lean_inc(v_start_1179_);
v_items_1180_ = lean_ctor_get(v_t_1177_, 1);
lean_inc_ref(v_items_1180_);
lean_dec_ref_known(v_t_1177_, 2);
v___x_1181_ = lean_apply_2(v_k_1178_, v_start_1179_, v_items_1180_);
return v___x_1181_;
}
case 7:
{
lean_object* v_container_1182_; lean_object* v_content_1183_; lean_object* v___x_1184_; 
v_container_1182_ = lean_ctor_get(v_t_1177_, 0);
lean_inc(v_container_1182_);
v_content_1183_ = lean_ctor_get(v_t_1177_, 1);
lean_inc_ref(v_content_1183_);
lean_dec_ref_known(v_t_1177_, 2);
v___x_1184_ = lean_apply_2(v_k_1178_, v_container_1182_, v_content_1183_);
return v___x_1184_;
}
default: 
{
lean_object* v_contents_1185_; lean_object* v___x_1186_; 
v_contents_1185_ = lean_ctor_get(v_t_1177_, 0);
lean_inc_ref(v_contents_1185_);
lean_dec_ref(v_t_1177_);
v___x_1186_ = lean_apply_1(v_k_1178_, v_contents_1185_);
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim(lean_object* v_i_1187_, lean_object* v_b_1188_, lean_object* v_motive__1_1189_, lean_object* v_ctorIdx_1190_, lean_object* v_t_1191_, lean_object* v_h_1192_, lean_object* v_k_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1191_, v_k_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___boxed(lean_object* v_i_1195_, lean_object* v_b_1196_, lean_object* v_motive__1_1197_, lean_object* v_ctorIdx_1198_, lean_object* v_t_1199_, lean_object* v_h_1200_, lean_object* v_k_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Doc_Block_ctorElim(v_i_1195_, v_b_1196_, v_motive__1_1197_, v_ctorIdx_1198_, v_t_1199_, v_h_1200_, v_k_1201_);
lean_dec(v_ctorIdx_1198_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim___redArg(lean_object* v_t_1203_, lean_object* v_para_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1203_, v_para_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim(lean_object* v_i_1206_, lean_object* v_b_1207_, lean_object* v_motive__1_1208_, lean_object* v_t_1209_, lean_object* v_h_1210_, lean_object* v_para_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1209_, v_para_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim___redArg(lean_object* v_t_1213_, lean_object* v_code_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1213_, v_code_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim(lean_object* v_i_1216_, lean_object* v_b_1217_, lean_object* v_motive__1_1218_, lean_object* v_t_1219_, lean_object* v_h_1220_, lean_object* v_code_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1219_, v_code_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim___redArg(lean_object* v_t_1223_, lean_object* v_ul_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1223_, v_ul_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim(lean_object* v_i_1226_, lean_object* v_b_1227_, lean_object* v_motive__1_1228_, lean_object* v_t_1229_, lean_object* v_h_1230_, lean_object* v_ul_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1229_, v_ul_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim___redArg(lean_object* v_t_1233_, lean_object* v_ol_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1233_, v_ol_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim(lean_object* v_i_1236_, lean_object* v_b_1237_, lean_object* v_motive__1_1238_, lean_object* v_t_1239_, lean_object* v_h_1240_, lean_object* v_ol_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1239_, v_ol_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim___redArg(lean_object* v_t_1243_, lean_object* v_dl_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1243_, v_dl_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim(lean_object* v_i_1246_, lean_object* v_b_1247_, lean_object* v_motive__1_1248_, lean_object* v_t_1249_, lean_object* v_h_1250_, lean_object* v_dl_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1249_, v_dl_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim___redArg(lean_object* v_t_1253_, lean_object* v_blockquote_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1253_, v_blockquote_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim(lean_object* v_i_1256_, lean_object* v_b_1257_, lean_object* v_motive__1_1258_, lean_object* v_t_1259_, lean_object* v_h_1260_, lean_object* v_blockquote_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1259_, v_blockquote_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim___redArg(lean_object* v_t_1263_, lean_object* v_concat_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1263_, v_concat_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim(lean_object* v_i_1266_, lean_object* v_b_1267_, lean_object* v_motive__1_1268_, lean_object* v_t_1269_, lean_object* v_h_1270_, lean_object* v_concat_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1269_, v_concat_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim___redArg(lean_object* v_t_1273_, lean_object* v_other_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1273_, v_other_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim(lean_object* v_i_1276_, lean_object* v_b_1277_, lean_object* v_motive__1_1278_, lean_object* v_t_1279_, lean_object* v_h_1280_, lean_object* v_other_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1279_, v_other_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___redArg___boxed(lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1283_, v_inst_1284_, v_x_1285_, v_x_1286_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq___redArg(lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
lean_object* v_localinst_1293_; lean_object* v_a_1295_; lean_object* v_b_1296_; 
lean_inc_ref(v_inst_1290_);
lean_inc_ref(v_inst_1289_);
v_localinst_1293_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1293_, 0, v_inst_1289_);
lean_closure_set(v_localinst_1293_, 1, v_inst_1290_);
switch(lean_obj_tag(v_x_1291_))
{
case 0:
{
lean_dec_ref(v_localinst_1293_);
lean_dec_ref(v_inst_1290_);
if (lean_obj_tag(v_x_1292_) == 0)
{
lean_object* v_contents_1301_; lean_object* v_contents_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_contents_1301_ = lean_ctor_get(v_x_1291_, 0);
lean_inc_ref(v_contents_1301_);
lean_dec_ref_known(v_x_1291_, 1);
v_contents_1302_ = lean_ctor_get(v_x_1292_, 0);
lean_inc_ref(v_contents_1302_);
lean_dec_ref_known(v_x_1292_, 1);
v___x_1303_ = lean_array_get_size(v_contents_1301_);
v___x_1304_ = lean_array_get_size(v_contents_1302_);
v___x_1305_ = lean_nat_dec_eq(v___x_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_dec_ref(v_contents_1302_);
lean_dec_ref(v_contents_1301_);
lean_dec_ref(v_inst_1289_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1306_, 0, lean_box(0));
lean_closure_set(v___x_1306_, 1, v_inst_1289_);
v___x_1307_ = l_Array_isEqvAux___redArg(v_contents_1301_, v_contents_1302_, v___x_1306_, v___x_1303_);
lean_dec_ref(v_contents_1302_);
lean_dec_ref(v_contents_1301_);
return v___x_1307_;
}
}
else
{
uint8_t v___x_1308_; 
lean_dec_ref_known(v_x_1291_, 1);
lean_dec_ref(v_x_1292_);
lean_dec_ref(v_inst_1289_);
v___x_1308_ = 0;
return v___x_1308_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1293_);
lean_dec_ref(v_inst_1290_);
lean_dec_ref(v_inst_1289_);
if (lean_obj_tag(v_x_1292_) == 1)
{
lean_object* v_content_1309_; lean_object* v_content_1310_; uint8_t v___x_1311_; 
v_content_1309_ = lean_ctor_get(v_x_1291_, 0);
lean_inc_ref(v_content_1309_);
lean_dec_ref_known(v_x_1291_, 1);
v_content_1310_ = lean_ctor_get(v_x_1292_, 0);
lean_inc_ref(v_content_1310_);
lean_dec_ref_known(v_x_1292_, 1);
v___x_1311_ = lean_string_dec_eq(v_content_1309_, v_content_1310_);
lean_dec_ref(v_content_1310_);
lean_dec_ref(v_content_1309_);
return v___x_1311_;
}
else
{
uint8_t v___x_1312_; 
lean_dec_ref_known(v_x_1291_, 1);
lean_dec_ref(v_x_1292_);
v___x_1312_ = 0;
return v___x_1312_;
}
}
case 2:
{
lean_dec_ref(v_inst_1290_);
lean_dec_ref(v_inst_1289_);
if (lean_obj_tag(v_x_1292_) == 2)
{
lean_object* v_items_1313_; lean_object* v_items_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v_items_1313_ = lean_ctor_get(v_x_1291_, 0);
lean_inc_ref(v_items_1313_);
lean_dec_ref_known(v_x_1291_, 1);
v_items_1314_ = lean_ctor_get(v_x_1292_, 0);
lean_inc_ref(v_items_1314_);
lean_dec_ref_known(v_x_1292_, 1);
v___x_1315_ = lean_array_get_size(v_items_1313_);
v___x_1316_ = lean_array_get_size(v_items_1314_);
v___x_1317_ = lean_nat_dec_eq(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_dec_ref(v_items_1314_);
lean_dec_ref(v_items_1313_);
lean_dec_ref(v_localinst_1293_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1318_, 0, lean_box(0));
lean_closure_set(v___x_1318_, 1, v_localinst_1293_);
v___x_1319_ = l_Array_isEqvAux___redArg(v_items_1313_, v_items_1314_, v___x_1318_, v___x_1315_);
lean_dec_ref(v_items_1314_);
lean_dec_ref(v_items_1313_);
return v___x_1319_;
}
}
else
{
uint8_t v___x_1320_; 
lean_dec_ref_known(v_x_1291_, 1);
lean_dec_ref(v_localinst_1293_);
lean_dec_ref(v_x_1292_);
v___x_1320_ = 0;
return v___x_1320_;
}
}
case 3:
{
lean_dec_ref(v_inst_1290_);
lean_dec_ref(v_inst_1289_);
if (lean_obj_tag(v_x_1292_) == 3)
{
lean_object* v_start_1321_; lean_object* v_items_1322_; lean_object* v_start_1323_; lean_object* v_items_1324_; uint8_t v___x_1325_; 
v_start_1321_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_start_1321_);
v_items_1322_ = lean_ctor_get(v_x_1291_, 1);
lean_inc_ref(v_items_1322_);
lean_dec_ref_known(v_x_1291_, 2);
v_start_1323_ = lean_ctor_get(v_x_1292_, 0);
lean_inc(v_start_1323_);
v_items_1324_ = lean_ctor_get(v_x_1292_, 1);
lean_inc_ref(v_items_1324_);
lean_dec_ref_known(v_x_1292_, 2);
v___x_1325_ = lean_int_dec_eq(v_start_1321_, v_start_1323_);
lean_dec(v_start_1323_);
lean_dec(v_start_1321_);
if (v___x_1325_ == 0)
{
lean_dec_ref(v_items_1324_);
lean_dec_ref(v_items_1322_);
lean_dec_ref(v_localinst_1293_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = lean_array_get_size(v_items_1322_);
v___x_1327_ = lean_array_get_size(v_items_1324_);
v___x_1328_ = lean_nat_dec_eq(v___x_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_dec_ref(v_items_1324_);
lean_dec_ref(v_items_1322_);
lean_dec_ref(v_localinst_1293_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1329_, 0, lean_box(0));
lean_closure_set(v___x_1329_, 1, v_localinst_1293_);
v___x_1330_ = l_Array_isEqvAux___redArg(v_items_1322_, v_items_1324_, v___x_1329_, v___x_1326_);
lean_dec_ref(v_items_1324_);
lean_dec_ref(v_items_1322_);
return v___x_1330_;
}
}
}
else
{
uint8_t v___x_1331_; 
lean_dec_ref_known(v_x_1291_, 2);
lean_dec_ref(v_localinst_1293_);
lean_dec_ref(v_x_1292_);
v___x_1331_ = 0;
return v___x_1331_;
}
}
case 4:
{
lean_dec_ref(v_inst_1290_);
if (lean_obj_tag(v_x_1292_) == 4)
{
lean_object* v_items_1332_; lean_object* v_items_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_items_1332_ = lean_ctor_get(v_x_1291_, 0);
lean_inc_ref(v_items_1332_);
lean_dec_ref_known(v_x_1291_, 1);
v_items_1333_ = lean_ctor_get(v_x_1292_, 0);
lean_inc_ref(v_items_1333_);
lean_dec_ref_known(v_x_1292_, 1);
v___x_1334_ = lean_array_get_size(v_items_1332_);
v___x_1335_ = lean_array_get_size(v_items_1333_);
v___x_1336_ = lean_nat_dec_eq(v___x_1334_, v___x_1335_);
if (v___x_1336_ == 0)
{
lean_dec_ref(v_items_1333_);
lean_dec_ref(v_items_1332_);
lean_dec_ref(v_localinst_1293_);
lean_dec_ref(v_inst_1289_);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1337_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1337_, 0, lean_box(0));
lean_closure_set(v___x_1337_, 1, v_inst_1289_);
v___x_1338_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1338_, 0, lean_box(0));
lean_closure_set(v___x_1338_, 1, lean_box(0));
lean_closure_set(v___x_1338_, 2, v___x_1337_);
lean_closure_set(v___x_1338_, 3, v_localinst_1293_);
v___x_1339_ = l_Array_isEqvAux___redArg(v_items_1332_, v_items_1333_, v___x_1338_, v___x_1334_);
lean_dec_ref(v_items_1333_);
lean_dec_ref(v_items_1332_);
return v___x_1339_;
}
}
else
{
uint8_t v___x_1340_; 
lean_dec_ref_known(v_x_1291_, 1);
lean_dec_ref(v_localinst_1293_);
lean_dec_ref(v_x_1292_);
lean_dec_ref(v_inst_1289_);
v___x_1340_ = 0;
return v___x_1340_;
}
}
case 5:
{
lean_dec_ref(v_inst_1290_);
lean_dec_ref(v_inst_1289_);
if (lean_obj_tag(v_x_1292_) == 5)
{
lean_object* v_items_1341_; lean_object* v_items_1342_; 
v_items_1341_ = lean_ctor_get(v_x_1291_, 0);
lean_inc_ref(v_items_1341_);
lean_dec_ref_known(v_x_1291_, 1);
v_items_1342_ = lean_ctor_get(v_x_1292_, 0);
lean_inc_ref(v_items_1342_);
lean_dec_ref_known(v_x_1292_, 1);
v_a_1295_ = v_items_1341_;
v_b_1296_ = v_items_1342_;
goto v___jp_1294_;
}
else
{
uint8_t v___x_1343_; 
lean_dec_ref_known(v_x_1291_, 1);
lean_dec_ref(v_localinst_1293_);
lean_dec_ref(v_x_1292_);
v___x_1343_ = 0;
return v___x_1343_;
}
}
case 6:
{
lean_dec_ref(v_inst_1290_);
lean_dec_ref(v_inst_1289_);
if (lean_obj_tag(v_x_1292_) == 6)
{
lean_object* v_content_1344_; lean_object* v_content_1345_; 
v_content_1344_ = lean_ctor_get(v_x_1291_, 0);
lean_inc_ref(v_content_1344_);
lean_dec_ref_known(v_x_1291_, 1);
v_content_1345_ = lean_ctor_get(v_x_1292_, 0);
lean_inc_ref(v_content_1345_);
lean_dec_ref_known(v_x_1292_, 1);
v_a_1295_ = v_content_1344_;
v_b_1296_ = v_content_1345_;
goto v___jp_1294_;
}
else
{
uint8_t v___x_1346_; 
lean_dec_ref_known(v_x_1291_, 1);
lean_dec_ref(v_localinst_1293_);
lean_dec_ref(v_x_1292_);
v___x_1346_ = 0;
return v___x_1346_;
}
}
default: 
{
lean_dec_ref(v_inst_1289_);
if (lean_obj_tag(v_x_1292_) == 7)
{
lean_object* v_container_1347_; lean_object* v_content_1348_; lean_object* v_container_1349_; lean_object* v_content_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_container_1347_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_container_1347_);
v_content_1348_ = lean_ctor_get(v_x_1291_, 1);
lean_inc_ref(v_content_1348_);
lean_dec_ref_known(v_x_1291_, 2);
v_container_1349_ = lean_ctor_get(v_x_1292_, 0);
lean_inc(v_container_1349_);
v_content_1350_ = lean_ctor_get(v_x_1292_, 1);
lean_inc_ref(v_content_1350_);
lean_dec_ref_known(v_x_1292_, 2);
v___x_1351_ = lean_apply_2(v_inst_1290_, v_container_1347_, v_container_1349_);
v___x_1352_ = lean_unbox(v___x_1351_);
if (v___x_1352_ == 0)
{
uint8_t v___x_1353_; 
lean_dec_ref(v_content_1350_);
lean_dec_ref(v_content_1348_);
lean_dec_ref(v_localinst_1293_);
v___x_1353_ = lean_unbox(v___x_1351_);
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1354_ = lean_array_get_size(v_content_1348_);
v___x_1355_ = lean_array_get_size(v_content_1350_);
v___x_1356_ = lean_nat_dec_eq(v___x_1354_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_dec_ref(v_content_1350_);
lean_dec_ref(v_content_1348_);
lean_dec_ref(v_localinst_1293_);
return v___x_1356_;
}
else
{
uint8_t v___x_1357_; 
v___x_1357_ = l_Array_isEqvAux___redArg(v_content_1348_, v_content_1350_, v_localinst_1293_, v___x_1354_);
lean_dec_ref(v_content_1350_);
lean_dec_ref(v_content_1348_);
return v___x_1357_;
}
}
}
else
{
uint8_t v___x_1358_; 
lean_dec_ref_known(v_x_1291_, 2);
lean_dec_ref(v_localinst_1293_);
lean_dec_ref(v_x_1292_);
lean_dec_ref(v_inst_1290_);
v___x_1358_ = 0;
return v___x_1358_;
}
}
}
v___jp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1297_ = lean_array_get_size(v_a_1295_);
v___x_1298_ = lean_array_get_size(v_b_1296_);
v___x_1299_ = lean_nat_dec_eq(v___x_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_dec_ref(v_b_1296_);
lean_dec_ref(v_a_1295_);
lean_dec_ref(v_localinst_1293_);
return v___x_1299_;
}
else
{
uint8_t v___x_1300_; 
v___x_1300_ = l_Array_isEqvAux___redArg(v_a_1295_, v_b_1296_, v_localinst_1293_, v___x_1297_);
lean_dec_ref(v_b_1296_);
lean_dec_ref(v_a_1295_);
return v___x_1300_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq(lean_object* v_i_1359_, lean_object* v_b_1360_, lean_object* v_inst_1361_, lean_object* v_inst_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
uint8_t v___x_1365_; 
v___x_1365_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1361_, v_inst_1362_, v_x_1363_, v_x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___boxed(lean_object* v_i_1366_, lean_object* v_b_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_res_1372_ = l_Lean_Doc_instBEqBlock_beq(v_i_1366_, v_b_1367_, v_inst_1368_, v_inst_1369_, v_x_1370_, v_x_1371_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock___redArg(lean_object* v_inst_1374_, lean_object* v_inst_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1376_, 0, lean_box(0));
lean_closure_set(v___x_1376_, 1, lean_box(0));
lean_closure_set(v___x_1376_, 2, v_inst_1374_);
lean_closure_set(v___x_1376_, 3, v_inst_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock(lean_object* v_i_1377_, lean_object* v_b_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1381_, 0, lean_box(0));
lean_closure_set(v___x_1381_, 1, lean_box(0));
lean_closure_set(v___x_1381_, 2, v_inst_1379_);
lean_closure_set(v___x_1381_, 3, v_inst_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___redArg___boxed(lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_res_1386_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1382_, v_inst_1383_, v_x_1384_, v_x_1385_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord___redArg(lean_object* v_inst_1388_, lean_object* v_inst_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
lean_object* v_localinst_1392_; 
lean_inc_ref(v_inst_1389_);
lean_inc_ref(v_inst_1388_);
v_localinst_1392_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1392_, 0, v_inst_1388_);
lean_closure_set(v_localinst_1392_, 1, v_inst_1389_);
switch(lean_obj_tag(v_x_1390_))
{
case 0:
{
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_inst_1389_);
if (lean_obj_tag(v_x_1391_) == 0)
{
lean_object* v_contents_1393_; lean_object* v_contents_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_contents_1393_ = lean_ctor_get(v_x_1390_, 0);
lean_inc_ref(v_contents_1393_);
lean_dec_ref_known(v_x_1390_, 1);
v_contents_1394_ = lean_ctor_get(v_x_1391_, 0);
lean_inc_ref(v_contents_1394_);
lean_dec_ref_known(v_x_1391_, 1);
v___x_1395_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1395_, 0, lean_box(0));
lean_closure_set(v___x_1395_, 1, v_inst_1388_);
v___x_1396_ = l_Array_compareLex___redArg(v___x_1395_, v_contents_1393_, v_contents_1394_);
lean_dec_ref(v_contents_1394_);
lean_dec_ref(v_contents_1393_);
return v___x_1396_;
}
else
{
uint8_t v___x_1397_; 
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_x_1391_);
lean_dec_ref(v_inst_1388_);
v___x_1397_ = 0;
return v___x_1397_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_inst_1388_);
switch(lean_obj_tag(v_x_1391_))
{
case 0:
{
uint8_t v___x_1398_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
v___x_1398_ = 2;
return v___x_1398_;
}
case 1:
{
lean_object* v_content_1399_; lean_object* v_content_1400_; uint8_t v___x_1401_; 
v_content_1399_ = lean_ctor_get(v_x_1390_, 0);
lean_inc_ref(v_content_1399_);
lean_dec_ref_known(v_x_1390_, 1);
v_content_1400_ = lean_ctor_get(v_x_1391_, 0);
lean_inc_ref(v_content_1400_);
lean_dec_ref_known(v_x_1391_, 1);
v___x_1401_ = lean_string_compare(v_content_1399_, v_content_1400_);
lean_dec_ref(v_content_1400_);
lean_dec_ref(v_content_1399_);
return v___x_1401_;
}
default: 
{
uint8_t v___x_1402_; 
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_x_1391_);
v___x_1402_ = 0;
return v___x_1402_;
}
}
}
case 2:
{
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_inst_1388_);
switch(lean_obj_tag(v_x_1391_))
{
case 0:
{
uint8_t v___x_1403_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1403_ = 2;
return v___x_1403_;
}
case 1:
{
uint8_t v___x_1404_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1404_ = 2;
return v___x_1404_;
}
case 2:
{
lean_object* v_items_1405_; lean_object* v_items_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v_items_1405_ = lean_ctor_get(v_x_1390_, 0);
lean_inc_ref(v_items_1405_);
lean_dec_ref_known(v_x_1390_, 1);
v_items_1406_ = lean_ctor_get(v_x_1391_, 0);
lean_inc_ref(v_items_1406_);
lean_dec_ref_known(v_x_1391_, 1);
v___x_1407_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1407_, 0, lean_box(0));
lean_closure_set(v___x_1407_, 1, v_localinst_1392_);
v___x_1408_ = l_Array_compareLex___redArg(v___x_1407_, v_items_1405_, v_items_1406_);
lean_dec_ref(v_items_1406_);
lean_dec_ref(v_items_1405_);
return v___x_1408_;
}
default: 
{
uint8_t v___x_1409_; 
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_x_1391_);
v___x_1409_ = 0;
return v___x_1409_;
}
}
}
case 3:
{
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_inst_1388_);
switch(lean_obj_tag(v_x_1391_))
{
case 0:
{
uint8_t v___x_1410_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 2);
lean_dec_ref(v_localinst_1392_);
v___x_1410_ = 2;
return v___x_1410_;
}
case 1:
{
uint8_t v___x_1411_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 2);
lean_dec_ref(v_localinst_1392_);
v___x_1411_ = 2;
return v___x_1411_;
}
case 2:
{
uint8_t v___x_1412_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 2);
lean_dec_ref(v_localinst_1392_);
v___x_1412_ = 2;
return v___x_1412_;
}
case 3:
{
lean_object* v_start_1413_; lean_object* v_items_1414_; lean_object* v_start_1415_; lean_object* v_items_1416_; uint8_t v___x_1417_; 
v_start_1413_ = lean_ctor_get(v_x_1390_, 0);
lean_inc(v_start_1413_);
v_items_1414_ = lean_ctor_get(v_x_1390_, 1);
lean_inc_ref(v_items_1414_);
lean_dec_ref_known(v_x_1390_, 2);
v_start_1415_ = lean_ctor_get(v_x_1391_, 0);
lean_inc(v_start_1415_);
v_items_1416_ = lean_ctor_get(v_x_1391_, 1);
lean_inc_ref(v_items_1416_);
lean_dec_ref_known(v_x_1391_, 2);
v___x_1417_ = lean_int_dec_lt(v_start_1413_, v_start_1415_);
if (v___x_1417_ == 0)
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_int_dec_eq(v_start_1413_, v_start_1415_);
lean_dec(v_start_1415_);
lean_dec(v_start_1413_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; 
lean_dec_ref(v_items_1416_);
lean_dec_ref(v_items_1414_);
lean_dec_ref(v_localinst_1392_);
v___x_1419_ = 2;
return v___x_1419_;
}
else
{
lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1420_, 0, lean_box(0));
lean_closure_set(v___x_1420_, 1, v_localinst_1392_);
v___x_1421_ = l_Array_compareLex___redArg(v___x_1420_, v_items_1414_, v_items_1416_);
lean_dec_ref(v_items_1416_);
lean_dec_ref(v_items_1414_);
return v___x_1421_;
}
}
else
{
uint8_t v___x_1422_; 
lean_dec_ref(v_items_1416_);
lean_dec(v_start_1415_);
lean_dec_ref(v_items_1414_);
lean_dec(v_start_1413_);
lean_dec_ref(v_localinst_1392_);
v___x_1422_ = 0;
return v___x_1422_;
}
}
default: 
{
uint8_t v___x_1423_; 
lean_dec_ref_known(v_x_1390_, 2);
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_x_1391_);
v___x_1423_ = 0;
return v___x_1423_;
}
}
}
case 4:
{
lean_dec_ref(v_inst_1389_);
switch(lean_obj_tag(v_x_1391_))
{
case 0:
{
uint8_t v___x_1424_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_inst_1388_);
v___x_1424_ = 2;
return v___x_1424_;
}
case 1:
{
uint8_t v___x_1425_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_inst_1388_);
v___x_1425_ = 2;
return v___x_1425_;
}
case 2:
{
uint8_t v___x_1426_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_inst_1388_);
v___x_1426_ = 2;
return v___x_1426_;
}
case 3:
{
uint8_t v___x_1427_; 
lean_dec_ref_known(v_x_1391_, 2);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_inst_1388_);
v___x_1427_ = 2;
return v___x_1427_;
}
case 4:
{
lean_object* v_items_1428_; lean_object* v_items_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v_items_1428_ = lean_ctor_get(v_x_1390_, 0);
lean_inc_ref(v_items_1428_);
lean_dec_ref_known(v_x_1390_, 1);
v_items_1429_ = lean_ctor_get(v_x_1391_, 0);
lean_inc_ref(v_items_1429_);
lean_dec_ref_known(v_x_1391_, 1);
v___x_1430_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1430_, 0, lean_box(0));
lean_closure_set(v___x_1430_, 1, v_inst_1388_);
v___x_1431_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1431_, 0, lean_box(0));
lean_closure_set(v___x_1431_, 1, lean_box(0));
lean_closure_set(v___x_1431_, 2, v___x_1430_);
lean_closure_set(v___x_1431_, 3, v_localinst_1392_);
v___x_1432_ = l_Array_compareLex___redArg(v___x_1431_, v_items_1428_, v_items_1429_);
lean_dec_ref(v_items_1429_);
lean_dec_ref(v_items_1428_);
return v___x_1432_;
}
default: 
{
uint8_t v___x_1433_; 
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_x_1391_);
lean_dec_ref(v_inst_1388_);
v___x_1433_ = 0;
return v___x_1433_;
}
}
}
case 5:
{
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_inst_1388_);
switch(lean_obj_tag(v_x_1391_))
{
case 0:
{
uint8_t v___x_1434_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1434_ = 2;
return v___x_1434_;
}
case 1:
{
uint8_t v___x_1435_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1435_ = 2;
return v___x_1435_;
}
case 2:
{
uint8_t v___x_1436_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1436_ = 2;
return v___x_1436_;
}
case 3:
{
uint8_t v___x_1437_; 
lean_dec_ref_known(v_x_1391_, 2);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1437_ = 2;
return v___x_1437_;
}
case 4:
{
uint8_t v___x_1438_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1438_ = 2;
return v___x_1438_;
}
case 5:
{
lean_object* v_items_1439_; lean_object* v_items_1440_; uint8_t v___x_1441_; 
v_items_1439_ = lean_ctor_get(v_x_1390_, 0);
lean_inc_ref(v_items_1439_);
lean_dec_ref_known(v_x_1390_, 1);
v_items_1440_ = lean_ctor_get(v_x_1391_, 0);
lean_inc_ref(v_items_1440_);
lean_dec_ref_known(v_x_1391_, 1);
v___x_1441_ = l_Array_compareLex___redArg(v_localinst_1392_, v_items_1439_, v_items_1440_);
lean_dec_ref(v_items_1440_);
lean_dec_ref(v_items_1439_);
return v___x_1441_;
}
default: 
{
uint8_t v___x_1442_; 
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_x_1391_);
v___x_1442_ = 0;
return v___x_1442_;
}
}
}
case 6:
{
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_inst_1388_);
switch(lean_obj_tag(v_x_1391_))
{
case 0:
{
uint8_t v___x_1443_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1443_ = 2;
return v___x_1443_;
}
case 1:
{
uint8_t v___x_1444_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1444_ = 2;
return v___x_1444_;
}
case 2:
{
uint8_t v___x_1445_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1445_ = 2;
return v___x_1445_;
}
case 3:
{
uint8_t v___x_1446_; 
lean_dec_ref_known(v_x_1391_, 2);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1446_ = 2;
return v___x_1446_;
}
case 4:
{
uint8_t v___x_1447_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1447_ = 2;
return v___x_1447_;
}
case 5:
{
uint8_t v___x_1448_; 
lean_dec_ref_known(v_x_1391_, 1);
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
v___x_1448_ = 2;
return v___x_1448_;
}
case 6:
{
lean_object* v_content_1449_; lean_object* v_content_1450_; uint8_t v___x_1451_; 
v_content_1449_ = lean_ctor_get(v_x_1390_, 0);
lean_inc_ref(v_content_1449_);
lean_dec_ref_known(v_x_1390_, 1);
v_content_1450_ = lean_ctor_get(v_x_1391_, 0);
lean_inc_ref(v_content_1450_);
lean_dec_ref_known(v_x_1391_, 1);
v___x_1451_ = l_Array_compareLex___redArg(v_localinst_1392_, v_content_1449_, v_content_1450_);
lean_dec_ref(v_content_1450_);
lean_dec_ref(v_content_1449_);
return v___x_1451_;
}
default: 
{
uint8_t v___x_1452_; 
lean_dec_ref_known(v_x_1390_, 1);
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_x_1391_);
v___x_1452_ = 0;
return v___x_1452_;
}
}
}
default: 
{
lean_dec_ref(v_inst_1388_);
if (lean_obj_tag(v_x_1391_) == 7)
{
lean_object* v_container_1453_; lean_object* v_content_1454_; lean_object* v_container_1455_; lean_object* v_content_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v_container_1453_ = lean_ctor_get(v_x_1390_, 0);
lean_inc(v_container_1453_);
v_content_1454_ = lean_ctor_get(v_x_1390_, 1);
lean_inc_ref(v_content_1454_);
lean_dec_ref_known(v_x_1390_, 2);
v_container_1455_ = lean_ctor_get(v_x_1391_, 0);
lean_inc(v_container_1455_);
v_content_1456_ = lean_ctor_get(v_x_1391_, 1);
lean_inc_ref(v_content_1456_);
lean_dec_ref_known(v_x_1391_, 2);
v___x_1457_ = lean_apply_2(v_inst_1389_, v_container_1453_, v_container_1455_);
v___x_1458_ = lean_unbox(v___x_1457_);
if (v___x_1458_ == 1)
{
uint8_t v___x_1459_; 
v___x_1459_ = l_Array_compareLex___redArg(v_localinst_1392_, v_content_1454_, v_content_1456_);
lean_dec_ref(v_content_1456_);
lean_dec_ref(v_content_1454_);
return v___x_1459_;
}
else
{
uint8_t v___x_1460_; 
lean_dec_ref(v_content_1456_);
lean_dec_ref(v_content_1454_);
lean_dec_ref(v_localinst_1392_);
v___x_1460_ = lean_unbox(v___x_1457_);
return v___x_1460_;
}
}
else
{
uint8_t v___x_1461_; 
lean_dec_ref_known(v_x_1390_, 2);
lean_dec_ref(v_localinst_1392_);
lean_dec_ref(v_x_1391_);
lean_dec_ref(v_inst_1389_);
v___x_1461_ = 2;
return v___x_1461_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord(lean_object* v_i_1462_, lean_object* v_b_1463_, lean_object* v_inst_1464_, lean_object* v_inst_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
uint8_t v___x_1468_; 
v___x_1468_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1464_, v_inst_1465_, v_x_1466_, v_x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___boxed(lean_object* v_i_1469_, lean_object* v_b_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_){
_start:
{
uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_res_1475_ = l_Lean_Doc_instOrdBlock_ord(v_i_1469_, v_b_1470_, v_inst_1471_, v_inst_1472_, v_x_1473_, v_x_1474_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock___redArg(lean_object* v_inst_1477_, lean_object* v_inst_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1479_, 0, lean_box(0));
lean_closure_set(v___x_1479_, 1, lean_box(0));
lean_closure_set(v___x_1479_, 2, v_inst_1477_);
lean_closure_set(v___x_1479_, 3, v_inst_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock(lean_object* v_i_1480_, lean_object* v_b_1481_, lean_object* v_inst_1482_, lean_object* v_inst_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1484_, 0, lean_box(0));
lean_closure_set(v___x_1484_, 1, lean_box(0));
lean_closure_set(v___x_1484_, 2, v_inst_1482_);
lean_closure_set(v___x_1484_, 3, v_inst_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_nat_to_int(v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg___boxed(lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_x_1537_, lean_object* v_prec_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1535_, v_inst_1536_, v_x_1537_, v_prec_1538_);
lean_dec(v_prec_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg(lean_object* v_inst_1540_, lean_object* v_inst_1541_, lean_object* v_x_1542_, lean_object* v_prec_1543_){
_start:
{
lean_object* v_localinst_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_inc_ref(v_inst_1541_);
lean_inc_ref(v_inst_1540_);
v_localinst_1544_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1544_, 0, v_inst_1540_);
lean_closure_set(v_localinst_1544_, 1, v_inst_1541_);
v___x_1545_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1545_, 0, lean_box(0));
lean_closure_set(v___x_1545_, 1, v_inst_1540_);
lean_inc_ref(v_localinst_1544_);
v___x_1546_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_1546_, 0, lean_box(0));
lean_closure_set(v___x_1546_, 1, v_localinst_1544_);
switch(lean_obj_tag(v_x_1542_))
{
case 0:
{
lean_object* v_contents_1547_; lean_object* v___y_1549_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
lean_dec_ref(v___x_1546_);
lean_dec_ref(v_localinst_1544_);
lean_dec_ref(v_inst_1541_);
v_contents_1547_ = lean_ctor_get(v_x_1542_, 0);
lean_inc_ref(v_contents_1547_);
lean_dec_ref_known(v_x_1542_, 1);
v___x_1557_ = lean_unsigned_to_nat(1024u);
v___x_1558_ = lean_nat_dec_le(v___x_1557_, v_prec_1543_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1549_ = v___x_1559_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1549_ = v___x_1560_;
goto v___jp_1548_;
}
v___jp_1548_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1550_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__2));
v___x_1551_ = l_Array_repr___redArg(v___x_1545_, v_contents_1547_);
v___x_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
lean_inc(v___y_1549_);
v___x_1553_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___y_1549_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = 0;
v___x_1555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*1, v___x_1554_);
v___x_1556_ = l_Repr_addAppParen(v___x_1555_, v_prec_1543_);
return v___x_1556_;
}
}
case 1:
{
lean_object* v_content_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v___x_1546_);
lean_dec_ref(v___x_1545_);
lean_dec_ref(v_localinst_1544_);
lean_dec_ref(v_inst_1541_);
v_content_1561_ = lean_ctor_get(v_x_1542_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1563_ = v_x_1542_;
v_isShared_1564_ = v_isSharedCheck_1581_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_content_1561_);
lean_dec(v_x_1542_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1581_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___y_1566_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = lean_unsigned_to_nat(1024u);
v___x_1578_ = lean_nat_dec_le(v___x_1577_, v_prec_1543_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1566_ = v___x_1579_;
goto v___jp_1565_;
}
else
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1566_ = v___x_1580_;
goto v___jp_1565_;
}
v___jp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1567_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__5));
v___x_1568_ = l_String_quote(v_content_1561_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set_tag(v___x_1563_, 3);
lean_ctor_set(v___x_1563_, 0, v___x_1568_);
v___x_1570_ = v___x_1563_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1567_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
lean_inc(v___y_1566_);
v___x_1572_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___y_1566_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = 0;
v___x_1574_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set_uint8(v___x_1574_, sizeof(void*)*1, v___x_1573_);
v___x_1575_ = l_Repr_addAppParen(v___x_1574_, v_prec_1543_);
return v___x_1575_;
}
}
}
}
case 2:
{
lean_object* v_items_1582_; lean_object* v___y_1584_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
lean_dec_ref(v___x_1545_);
lean_dec_ref(v_localinst_1544_);
lean_dec_ref(v_inst_1541_);
v_items_1582_ = lean_ctor_get(v_x_1542_, 0);
lean_inc_ref(v_items_1582_);
lean_dec_ref_known(v_x_1542_, 1);
v___x_1592_ = lean_unsigned_to_nat(1024u);
v___x_1593_ = lean_nat_dec_le(v___x_1592_, v_prec_1543_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1584_ = v___x_1594_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1584_ = v___x_1595_;
goto v___jp_1583_;
}
v___jp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1585_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__8));
v___x_1586_ = l_Array_repr___redArg(v___x_1546_, v_items_1582_);
v___x_1587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
lean_inc(v___y_1584_);
v___x_1588_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___y_1584_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = 0;
v___x_1590_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*1, v___x_1589_);
v___x_1591_ = l_Repr_addAppParen(v___x_1590_, v_prec_1543_);
return v___x_1591_;
}
}
case 3:
{
lean_object* v_start_1596_; lean_object* v_items_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v___x_1545_);
lean_dec_ref(v_localinst_1544_);
lean_dec_ref(v_inst_1541_);
v_start_1596_ = lean_ctor_get(v_x_1542_, 0);
v_items_1597_ = lean_ctor_get(v_x_1542_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1599_ = v_x_1542_;
v_isShared_1600_ = v_isSharedCheck_1632_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_items_1597_);
lean_inc(v_start_1596_);
lean_dec(v_x_1542_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1632_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1617_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = lean_unsigned_to_nat(1024u);
v___x_1629_ = lean_nat_dec_le(v___x_1628_, v_prec_1543_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1617_ = v___x_1630_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1617_ = v___x_1631_;
goto v___jp_1616_;
}
v___jp_1601_:
{
lean_object* v___x_1607_; 
lean_inc(v___y_1604_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 5);
lean_ctor_set(v___x_1599_, 1, v___y_1605_);
lean_ctor_set(v___x_1599_, 0, v___y_1604_);
v___x_1607_ = v___x_1599_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___y_1604_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v___y_1605_);
v___x_1607_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_inc(v___y_1602_);
v___x_1608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v___y_1602_);
v___x_1609_ = l_Array_repr___redArg(v___x_1546_, v_items_1597_);
v___x_1610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
lean_inc(v___y_1603_);
v___x_1611_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___y_1603_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = 0;
v___x_1613_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*1, v___x_1612_);
v___x_1614_ = l_Repr_addAppParen(v___x_1613_, v_prec_1543_);
return v___x_1614_;
}
}
v___jp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1618_ = lean_box(1);
v___x_1619_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__11));
v___x_1620_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___redArg___closed__12, &l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12);
v___x_1621_ = lean_int_dec_lt(v_start_1596_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = l_Int_repr(v_start_1596_);
lean_dec(v_start_1596_);
v___x_1623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
v___y_1602_ = v___x_1618_;
v___y_1603_ = v___y_1617_;
v___y_1604_ = v___x_1619_;
v___y_1605_ = v___x_1623_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1624_ = lean_unsigned_to_nat(1024u);
v___x_1625_ = l_Int_repr(v_start_1596_);
lean_dec(v_start_1596_);
v___x_1626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
v___x_1627_ = l_Repr_addAppParen(v___x_1626_, v___x_1624_);
v___y_1602_ = v___x_1618_;
v___y_1603_ = v___y_1617_;
v___y_1604_ = v___x_1619_;
v___y_1605_ = v___x_1627_;
goto v___jp_1601_;
}
}
}
}
case 4:
{
lean_object* v_items_1633_; lean_object* v___x_1634_; lean_object* v___y_1636_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
lean_dec_ref(v___x_1546_);
lean_dec_ref(v_inst_1541_);
v_items_1633_ = lean_ctor_get(v_x_1542_, 0);
lean_inc_ref(v_items_1633_);
lean_dec_ref_known(v_x_1542_, 1);
v___x_1634_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1634_, 0, lean_box(0));
lean_closure_set(v___x_1634_, 1, lean_box(0));
lean_closure_set(v___x_1634_, 2, v___x_1545_);
lean_closure_set(v___x_1634_, 3, v_localinst_1544_);
v___x_1644_ = lean_unsigned_to_nat(1024u);
v___x_1645_ = lean_nat_dec_le(v___x_1644_, v_prec_1543_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1636_ = v___x_1646_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1636_ = v___x_1647_;
goto v___jp_1635_;
}
v___jp_1635_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1637_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__15));
v___x_1638_ = l_Array_repr___redArg(v___x_1634_, v_items_1633_);
v___x_1639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
lean_inc(v___y_1636_);
v___x_1640_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___y_1636_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = 0;
v___x_1642_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*1, v___x_1641_);
v___x_1643_ = l_Repr_addAppParen(v___x_1642_, v_prec_1543_);
return v___x_1643_;
}
}
case 5:
{
lean_object* v_items_1648_; lean_object* v___y_1650_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
lean_dec_ref(v___x_1546_);
lean_dec_ref(v___x_1545_);
lean_dec_ref(v_inst_1541_);
v_items_1648_ = lean_ctor_get(v_x_1542_, 0);
lean_inc_ref(v_items_1648_);
lean_dec_ref_known(v_x_1542_, 1);
v___x_1658_ = lean_unsigned_to_nat(1024u);
v___x_1659_ = lean_nat_dec_le(v___x_1658_, v_prec_1543_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1650_ = v___x_1660_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1650_ = v___x_1661_;
goto v___jp_1649_;
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1651_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__18));
v___x_1652_ = l_Array_repr___redArg(v_localinst_1544_, v_items_1648_);
v___x_1653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
lean_inc(v___y_1650_);
v___x_1654_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___y_1650_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = 0;
v___x_1656_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set_uint8(v___x_1656_, sizeof(void*)*1, v___x_1655_);
v___x_1657_ = l_Repr_addAppParen(v___x_1656_, v_prec_1543_);
return v___x_1657_;
}
}
case 6:
{
lean_object* v_content_1662_; lean_object* v___y_1664_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
lean_dec_ref(v___x_1546_);
lean_dec_ref(v___x_1545_);
lean_dec_ref(v_inst_1541_);
v_content_1662_ = lean_ctor_get(v_x_1542_, 0);
lean_inc_ref(v_content_1662_);
lean_dec_ref_known(v_x_1542_, 1);
v___x_1672_ = lean_unsigned_to_nat(1024u);
v___x_1673_ = lean_nat_dec_le(v___x_1672_, v_prec_1543_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1664_ = v___x_1674_;
goto v___jp_1663_;
}
else
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1664_ = v___x_1675_;
goto v___jp_1663_;
}
v___jp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1665_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__21));
v___x_1666_ = l_Array_repr___redArg(v_localinst_1544_, v_content_1662_);
v___x_1667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
lean_inc(v___y_1664_);
v___x_1668_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___y_1664_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = 0;
v___x_1670_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*1, v___x_1669_);
v___x_1671_ = l_Repr_addAppParen(v___x_1670_, v_prec_1543_);
return v___x_1671_;
}
}
default: 
{
lean_object* v_container_1676_; lean_object* v_content_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v___x_1546_);
lean_dec_ref(v___x_1545_);
v_container_1676_ = lean_ctor_get(v_x_1542_, 0);
v_content_1677_ = lean_ctor_get(v_x_1542_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1679_ = v_x_1542_;
v_isShared_1680_ = v_isSharedCheck_1701_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_content_1677_);
lean_inc(v_container_1676_);
lean_dec(v_x_1542_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1701_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___y_1682_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1697_ = lean_unsigned_to_nat(1024u);
v___x_1698_ = lean_nat_dec_le(v___x_1697_, v_prec_1543_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1682_ = v___x_1699_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1682_ = v___x_1700_;
goto v___jp_1681_;
}
v___jp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1683_ = lean_box(1);
v___x_1684_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__24));
v___x_1685_ = lean_unsigned_to_nat(1024u);
v___x_1686_ = lean_apply_2(v_inst_1541_, v_container_1676_, v___x_1685_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set_tag(v___x_1679_, 5);
lean_ctor_set(v___x_1679_, 1, v___x_1686_);
lean_ctor_set(v___x_1679_, 0, v___x_1684_);
v___x_1688_ = v___x_1679_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v___x_1683_);
v___x_1690_ = l_Array_repr___redArg(v_localinst_1544_, v_content_1677_);
v___x_1691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
lean_inc(v___y_1682_);
v___x_1692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___y_1682_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = 0;
v___x_1694_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*1, v___x_1693_);
v___x_1695_ = l_Repr_addAppParen(v___x_1694_, v_prec_1543_);
return v___x_1695_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr(lean_object* v_i_1702_, lean_object* v_b_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_x_1706_, lean_object* v_prec_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1704_, v_inst_1705_, v_x_1706_, v_prec_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___boxed(lean_object* v_i_1709_, lean_object* v_b_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_x_1713_, lean_object* v_prec_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Doc_instReprBlock_repr(v_i_1709_, v_b_1710_, v_inst_1711_, v_inst_1712_, v_x_1713_, v_prec_1714_);
lean_dec(v_prec_1714_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock___redArg(lean_object* v_inst_1716_, lean_object* v_inst_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1718_, 0, lean_box(0));
lean_closure_set(v___x_1718_, 1, lean_box(0));
lean_closure_set(v___x_1718_, 2, v_inst_1716_);
lean_closure_set(v___x_1718_, 3, v_inst_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock(lean_object* v_i_1719_, lean_object* v_b_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1723_, 0, lean_box(0));
lean_closure_set(v___x_1723_, 1, lean_box(0));
lean_closure_set(v___x_1723_, 2, v_inst_1721_);
lean_closure_set(v___x_1723_, 3, v_inst_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg(){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlock_default___redArg___closed__1));
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg___boxed(lean_object* v___dummy_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
return v_res_1731_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedBlock_default___closed__0(void){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default(lean_object* v_i_1733_, lean_object* v_b_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg(){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg___boxed(lean_object* v___dummy_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Doc_instInhabitedBlock___redArg();
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock(lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg(){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = ((lean_object*)(l_Lean_Doc_Block_empty___redArg___closed__1));
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg___boxed(lean_object* v___dummy_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Doc_Block_empty___redArg();
return v_res_1750_;
}
}
static lean_object* _init_l_Lean_Doc_Block_empty___closed__0(void){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Doc_Block_empty___redArg();
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty(lean_object* v_i_1752_, lean_object* v_b_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_obj_once(&l_Lean_Doc_Block_empty___closed__0, &l_Lean_Doc_Block_empty___closed__0_once, _init_l_Lean_Doc_Block_empty___closed__0);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg(lean_object* v_x_1755_){
_start:
{
lean_inc_ref(v_x_1755_);
return v_x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg___boxed(lean_object* v_x_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Doc_Block_cast___redArg(v_x_1756_);
lean_dec_ref(v_x_1756_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast(lean_object* v_i_1758_, lean_object* v_i_x27_1759_, lean_object* v_b_1760_, lean_object* v_b_x27_1761_, lean_object* v_inlines__eq_1762_, lean_object* v_blocks__eq_1763_, lean_object* v_x_1764_){
_start:
{
lean_inc_ref(v_x_1764_);
return v_x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___boxed(lean_object* v_i_1765_, lean_object* v_i_x27_1766_, lean_object* v_b_1767_, lean_object* v_b_x27_1768_, lean_object* v_inlines__eq_1769_, lean_object* v_blocks__eq_1770_, lean_object* v_x_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Doc_Block_cast(v_i_1765_, v_i_x27_1766_, v_b_1767_, v_b_x27_1768_, v_inlines__eq_1769_, v_blocks__eq_1770_, v_x_1771_);
lean_dec_ref(v_x_1771_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___redArg___boxed(lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_x_1776_, lean_object* v_x_1777_){
_start:
{
uint8_t v_res_1778_; lean_object* v_r_1779_; 
v_res_1778_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1773_, v_inst_1774_, v_inst_1775_, v_x_1776_, v_x_1777_);
v_r_1779_ = lean_box(v_res_1778_);
return v_r_1779_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq___redArg(lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_){
_start:
{
lean_object* v_title_1785_; lean_object* v_titleString_1786_; lean_object* v_metadata_1787_; lean_object* v_content_1788_; lean_object* v_subParts_1789_; lean_object* v_title_1790_; lean_object* v_titleString_1791_; lean_object* v_metadata_1792_; lean_object* v_content_1793_; lean_object* v_subParts_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_title_1785_ = lean_ctor_get(v_x_1783_, 0);
lean_inc_ref(v_title_1785_);
v_titleString_1786_ = lean_ctor_get(v_x_1783_, 1);
lean_inc_ref(v_titleString_1786_);
v_metadata_1787_ = lean_ctor_get(v_x_1783_, 2);
lean_inc(v_metadata_1787_);
v_content_1788_ = lean_ctor_get(v_x_1783_, 3);
lean_inc_ref(v_content_1788_);
v_subParts_1789_ = lean_ctor_get(v_x_1783_, 4);
lean_inc_ref(v_subParts_1789_);
lean_dec_ref(v_x_1783_);
v_title_1790_ = lean_ctor_get(v_x_1784_, 0);
lean_inc_ref(v_title_1790_);
v_titleString_1791_ = lean_ctor_get(v_x_1784_, 1);
lean_inc_ref(v_titleString_1791_);
v_metadata_1792_ = lean_ctor_get(v_x_1784_, 2);
lean_inc(v_metadata_1792_);
v_content_1793_ = lean_ctor_get(v_x_1784_, 3);
lean_inc_ref(v_content_1793_);
v_subParts_1794_ = lean_ctor_get(v_x_1784_, 4);
lean_inc_ref(v_subParts_1794_);
lean_dec_ref(v_x_1784_);
v___x_1795_ = lean_array_get_size(v_title_1785_);
v___x_1796_ = lean_array_get_size(v_title_1790_);
v___x_1797_ = lean_nat_dec_eq(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_dec_ref(v_subParts_1794_);
lean_dec_ref(v_content_1793_);
lean_dec(v_metadata_1792_);
lean_dec_ref(v_titleString_1791_);
lean_dec_ref(v_title_1790_);
lean_dec_ref(v_subParts_1789_);
lean_dec_ref(v_content_1788_);
lean_dec(v_metadata_1787_);
lean_dec_ref(v_titleString_1786_);
lean_dec_ref(v_title_1785_);
lean_dec_ref(v_inst_1782_);
lean_dec_ref(v_inst_1781_);
lean_dec_ref(v_inst_1780_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
lean_inc_ref(v_inst_1782_);
lean_inc_ref(v_inst_1781_);
lean_inc_ref_n(v_inst_1780_, 2);
v___x_1798_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___redArg___boxed), 5, 3);
lean_closure_set(v___x_1798_, 0, v_inst_1780_);
lean_closure_set(v___x_1798_, 1, v_inst_1781_);
lean_closure_set(v___x_1798_, 2, v_inst_1782_);
v___x_1799_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1799_, 0, lean_box(0));
lean_closure_set(v___x_1799_, 1, v_inst_1780_);
v___x_1800_ = l_Array_isEqvAux___redArg(v_title_1785_, v_title_1790_, v___x_1799_, v___x_1795_);
lean_dec_ref(v_title_1790_);
lean_dec_ref(v_title_1785_);
if (v___x_1800_ == 0)
{
lean_dec_ref(v___x_1798_);
lean_dec_ref(v_subParts_1794_);
lean_dec_ref(v_content_1793_);
lean_dec(v_metadata_1792_);
lean_dec_ref(v_titleString_1791_);
lean_dec_ref(v_subParts_1789_);
lean_dec_ref(v_content_1788_);
lean_dec(v_metadata_1787_);
lean_dec_ref(v_titleString_1786_);
lean_dec_ref(v_inst_1782_);
lean_dec_ref(v_inst_1781_);
lean_dec_ref(v_inst_1780_);
return v___x_1800_;
}
else
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_string_dec_eq(v_titleString_1786_, v_titleString_1791_);
lean_dec_ref(v_titleString_1791_);
lean_dec_ref(v_titleString_1786_);
if (v___x_1801_ == 0)
{
lean_dec_ref(v___x_1798_);
lean_dec_ref(v_subParts_1794_);
lean_dec_ref(v_content_1793_);
lean_dec(v_metadata_1792_);
lean_dec_ref(v_subParts_1789_);
lean_dec_ref(v_content_1788_);
lean_dec(v_metadata_1787_);
lean_dec_ref(v_inst_1782_);
lean_dec_ref(v_inst_1781_);
lean_dec_ref(v_inst_1780_);
return v___x_1801_;
}
else
{
uint8_t v___x_1802_; 
v___x_1802_ = l_Option_instBEq_beq___redArg(v_inst_1782_, v_metadata_1787_, v_metadata_1792_);
if (v___x_1802_ == 0)
{
lean_dec_ref(v___x_1798_);
lean_dec_ref(v_subParts_1794_);
lean_dec_ref(v_content_1793_);
lean_dec_ref(v_subParts_1789_);
lean_dec_ref(v_content_1788_);
lean_dec_ref(v_inst_1781_);
lean_dec_ref(v_inst_1780_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1803_ = lean_array_get_size(v_content_1788_);
v___x_1804_ = lean_array_get_size(v_content_1793_);
v___x_1805_ = lean_nat_dec_eq(v___x_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_dec_ref(v___x_1798_);
lean_dec_ref(v_subParts_1794_);
lean_dec_ref(v_content_1793_);
lean_dec_ref(v_subParts_1789_);
lean_dec_ref(v_content_1788_);
lean_dec_ref(v_inst_1781_);
lean_dec_ref(v_inst_1780_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1806_, 0, lean_box(0));
lean_closure_set(v___x_1806_, 1, lean_box(0));
lean_closure_set(v___x_1806_, 2, v_inst_1780_);
lean_closure_set(v___x_1806_, 3, v_inst_1781_);
v___x_1807_ = l_Array_isEqvAux___redArg(v_content_1788_, v_content_1793_, v___x_1806_, v___x_1803_);
lean_dec_ref(v_content_1793_);
lean_dec_ref(v_content_1788_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v___x_1798_);
lean_dec_ref(v_subParts_1794_);
lean_dec_ref(v_subParts_1789_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1808_ = lean_array_get_size(v_subParts_1789_);
v___x_1809_ = lean_array_get_size(v_subParts_1794_);
v___x_1810_ = lean_nat_dec_eq(v___x_1808_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_dec_ref(v___x_1798_);
lean_dec_ref(v_subParts_1794_);
lean_dec_ref(v_subParts_1789_);
return v___x_1810_;
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = l_Array_isEqvAux___redArg(v_subParts_1789_, v_subParts_1794_, v___x_1798_, v___x_1808_);
lean_dec_ref(v_subParts_1794_);
lean_dec_ref(v_subParts_1789_);
return v___x_1811_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq(lean_object* v_i_1812_, lean_object* v_b_1813_, lean_object* v_p_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
uint8_t v___x_1820_; 
v___x_1820_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1815_, v_inst_1816_, v_inst_1817_, v_x_1818_, v_x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___boxed(lean_object* v_i_1821_, lean_object* v_b_1822_, lean_object* v_p_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
uint8_t v_res_1829_; lean_object* v_r_1830_; 
v_res_1829_ = l_Lean_Doc_instBEqPart_beq(v_i_1821_, v_b_1822_, v_p_1823_, v_inst_1824_, v_inst_1825_, v_inst_1826_, v_x_1827_, v_x_1828_);
v_r_1830_ = lean_box(v_res_1829_);
return v_r_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart___redArg(lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1834_, 0, lean_box(0));
lean_closure_set(v___x_1834_, 1, lean_box(0));
lean_closure_set(v___x_1834_, 2, lean_box(0));
lean_closure_set(v___x_1834_, 3, v_inst_1831_);
lean_closure_set(v___x_1834_, 4, v_inst_1832_);
lean_closure_set(v___x_1834_, 5, v_inst_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart(lean_object* v_i_1835_, lean_object* v_b_1836_, lean_object* v_p_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1841_, 0, lean_box(0));
lean_closure_set(v___x_1841_, 1, lean_box(0));
lean_closure_set(v___x_1841_, 2, lean_box(0));
lean_closure_set(v___x_1841_, 3, v_inst_1838_);
lean_closure_set(v___x_1841_, 4, v_inst_1839_);
lean_closure_set(v___x_1841_, 5, v_inst_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___redArg___boxed(lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_){
_start:
{
uint8_t v_res_1847_; lean_object* v_r_1848_; 
v_res_1847_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1842_, v_inst_1843_, v_inst_1844_, v_x_1845_, v_x_1846_);
v_r_1848_ = lean_box(v_res_1847_);
return v_r_1848_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord___redArg(lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_){
_start:
{
lean_object* v_title_1854_; lean_object* v_titleString_1855_; lean_object* v_metadata_1856_; lean_object* v_content_1857_; lean_object* v_subParts_1858_; lean_object* v_title_1859_; lean_object* v_titleString_1860_; lean_object* v_metadata_1861_; lean_object* v_content_1862_; lean_object* v_subParts_1863_; lean_object* v___x_1864_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v_title_1854_ = lean_ctor_get(v_x_1852_, 0);
lean_inc_ref(v_title_1854_);
v_titleString_1855_ = lean_ctor_get(v_x_1852_, 1);
lean_inc_ref(v_titleString_1855_);
v_metadata_1856_ = lean_ctor_get(v_x_1852_, 2);
lean_inc(v_metadata_1856_);
v_content_1857_ = lean_ctor_get(v_x_1852_, 3);
lean_inc_ref(v_content_1857_);
v_subParts_1858_ = lean_ctor_get(v_x_1852_, 4);
lean_inc_ref(v_subParts_1858_);
lean_dec_ref(v_x_1852_);
v_title_1859_ = lean_ctor_get(v_x_1853_, 0);
lean_inc_ref(v_title_1859_);
v_titleString_1860_ = lean_ctor_get(v_x_1853_, 1);
lean_inc_ref(v_titleString_1860_);
v_metadata_1861_ = lean_ctor_get(v_x_1853_, 2);
lean_inc(v_metadata_1861_);
v_content_1862_ = lean_ctor_get(v_x_1853_, 3);
lean_inc_ref(v_content_1862_);
v_subParts_1863_ = lean_ctor_get(v_x_1853_, 4);
lean_inc_ref(v_subParts_1863_);
lean_dec_ref(v_x_1853_);
lean_inc_ref(v_inst_1851_);
lean_inc_ref(v_inst_1850_);
lean_inc_ref_n(v_inst_1849_, 2);
v___x_1864_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___redArg___boxed), 5, 3);
lean_closure_set(v___x_1864_, 0, v_inst_1849_);
lean_closure_set(v___x_1864_, 1, v_inst_1850_);
lean_closure_set(v___x_1864_, 2, v_inst_1851_);
v___x_1869_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1869_, 0, lean_box(0));
lean_closure_set(v___x_1869_, 1, v_inst_1849_);
v___x_1870_ = l_Array_compareLex___redArg(v___x_1869_, v_title_1854_, v_title_1859_);
lean_dec_ref(v_title_1859_);
lean_dec_ref(v_title_1854_);
if (v___x_1870_ == 1)
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_string_compare(v_titleString_1855_, v_titleString_1860_);
lean_dec_ref(v_titleString_1860_);
lean_dec_ref(v_titleString_1855_);
if (v___x_1871_ == 1)
{
if (lean_obj_tag(v_metadata_1856_) == 0)
{
lean_dec_ref(v_inst_1851_);
if (lean_obj_tag(v_metadata_1861_) == 0)
{
goto v___jp_1865_;
}
else
{
uint8_t v___x_1872_; 
lean_dec_ref_known(v_metadata_1861_, 1);
lean_dec_ref(v___x_1864_);
lean_dec_ref(v_subParts_1863_);
lean_dec_ref(v_content_1862_);
lean_dec_ref(v_subParts_1858_);
lean_dec_ref(v_content_1857_);
lean_dec_ref(v_inst_1850_);
lean_dec_ref(v_inst_1849_);
v___x_1872_ = 0;
return v___x_1872_;
}
}
else
{
if (lean_obj_tag(v_metadata_1861_) == 0)
{
uint8_t v___x_1873_; 
lean_dec_ref_known(v_metadata_1856_, 1);
lean_dec_ref(v___x_1864_);
lean_dec_ref(v_subParts_1863_);
lean_dec_ref(v_content_1862_);
lean_dec_ref(v_subParts_1858_);
lean_dec_ref(v_content_1857_);
lean_dec_ref(v_inst_1851_);
lean_dec_ref(v_inst_1850_);
lean_dec_ref(v_inst_1849_);
v___x_1873_ = 2;
return v___x_1873_;
}
else
{
lean_object* v_val_1874_; lean_object* v_val_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v_val_1874_ = lean_ctor_get(v_metadata_1856_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v_metadata_1856_, 1);
v_val_1875_ = lean_ctor_get(v_metadata_1861_, 0);
lean_inc(v_val_1875_);
lean_dec_ref_known(v_metadata_1861_, 1);
v___x_1876_ = lean_apply_2(v_inst_1851_, v_val_1874_, v_val_1875_);
v___x_1877_ = lean_unbox(v___x_1876_);
if (v___x_1877_ == 1)
{
goto v___jp_1865_;
}
else
{
uint8_t v___x_1878_; 
lean_dec_ref(v___x_1864_);
lean_dec_ref(v_subParts_1863_);
lean_dec_ref(v_content_1862_);
lean_dec_ref(v_subParts_1858_);
lean_dec_ref(v_content_1857_);
lean_dec_ref(v_inst_1850_);
lean_dec_ref(v_inst_1849_);
v___x_1878_ = lean_unbox(v___x_1876_);
return v___x_1878_;
}
}
}
}
else
{
lean_dec_ref(v___x_1864_);
lean_dec_ref(v_subParts_1863_);
lean_dec_ref(v_content_1862_);
lean_dec(v_metadata_1861_);
lean_dec_ref(v_subParts_1858_);
lean_dec_ref(v_content_1857_);
lean_dec(v_metadata_1856_);
lean_dec_ref(v_inst_1851_);
lean_dec_ref(v_inst_1850_);
lean_dec_ref(v_inst_1849_);
return v___x_1871_;
}
}
else
{
lean_dec_ref(v___x_1864_);
lean_dec_ref(v_subParts_1863_);
lean_dec_ref(v_content_1862_);
lean_dec(v_metadata_1861_);
lean_dec_ref(v_titleString_1860_);
lean_dec_ref(v_subParts_1858_);
lean_dec_ref(v_content_1857_);
lean_dec(v_metadata_1856_);
lean_dec_ref(v_titleString_1855_);
lean_dec_ref(v_inst_1851_);
lean_dec_ref(v_inst_1850_);
lean_dec_ref(v_inst_1849_);
return v___x_1870_;
}
v___jp_1865_:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1866_, 0, lean_box(0));
lean_closure_set(v___x_1866_, 1, lean_box(0));
lean_closure_set(v___x_1866_, 2, v_inst_1849_);
lean_closure_set(v___x_1866_, 3, v_inst_1850_);
v___x_1867_ = l_Array_compareLex___redArg(v___x_1866_, v_content_1857_, v_content_1862_);
lean_dec_ref(v_content_1862_);
lean_dec_ref(v_content_1857_);
if (v___x_1867_ == 1)
{
uint8_t v___x_1868_; 
v___x_1868_ = l_Array_compareLex___redArg(v___x_1864_, v_subParts_1858_, v_subParts_1863_);
lean_dec_ref(v_subParts_1863_);
lean_dec_ref(v_subParts_1858_);
return v___x_1868_;
}
else
{
lean_dec_ref(v___x_1864_);
lean_dec_ref(v_subParts_1863_);
lean_dec_ref(v_subParts_1858_);
return v___x_1867_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord(lean_object* v_i_1879_, lean_object* v_b_1880_, lean_object* v_p_1881_, lean_object* v_inst_1882_, lean_object* v_inst_1883_, lean_object* v_inst_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_){
_start:
{
uint8_t v___x_1887_; 
v___x_1887_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1882_, v_inst_1883_, v_inst_1884_, v_x_1885_, v_x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___boxed(lean_object* v_i_1888_, lean_object* v_b_1889_, lean_object* v_p_1890_, lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_inst_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
uint8_t v_res_1896_; lean_object* v_r_1897_; 
v_res_1896_ = l_Lean_Doc_instOrdPart_ord(v_i_1888_, v_b_1889_, v_p_1890_, v_inst_1891_, v_inst_1892_, v_inst_1893_, v_x_1894_, v_x_1895_);
v_r_1897_ = lean_box(v_res_1896_);
return v_r_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart___redArg(lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1901_, 0, lean_box(0));
lean_closure_set(v___x_1901_, 1, lean_box(0));
lean_closure_set(v___x_1901_, 2, lean_box(0));
lean_closure_set(v___x_1901_, 3, v_inst_1898_);
lean_closure_set(v___x_1901_, 4, v_inst_1899_);
lean_closure_set(v___x_1901_, 5, v_inst_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart(lean_object* v_i_1902_, lean_object* v_b_1903_, lean_object* v_p_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_inst_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1908_, 0, lean_box(0));
lean_closure_set(v___x_1908_, 1, lean_box(0));
lean_closure_set(v___x_1908_, 2, lean_box(0));
lean_closure_set(v___x_1908_, 3, v_inst_1905_);
lean_closure_set(v___x_1908_, 4, v_inst_1906_);
lean_closure_set(v___x_1908_, 5, v_inst_1907_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_unsigned_to_nat(9u);
v___x_1919_ = lean_nat_to_int(v___x_1918_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_unsigned_to_nat(15u);
v___x_1924_ = lean_nat_to_int(v___x_1923_);
return v___x_1924_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_unsigned_to_nat(11u);
v___x_1932_ = lean_nat_to_int(v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg___boxed(lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_inst_1938_, lean_object* v_x_1939_, lean_object* v_prec_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_1936_, v_inst_1937_, v_inst_1938_, v_x_1939_, v_prec_1940_);
lean_dec(v_prec_1940_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg(lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_x_1945_, lean_object* v_prec_1946_){
_start:
{
lean_object* v_title_1947_; lean_object* v_titleString_1948_; lean_object* v_metadata_1949_; lean_object* v_content_1950_; lean_object* v_subParts_1951_; lean_object* v_localinst_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_title_1947_ = lean_ctor_get(v_x_1945_, 0);
lean_inc_ref(v_title_1947_);
v_titleString_1948_ = lean_ctor_get(v_x_1945_, 1);
lean_inc_ref(v_titleString_1948_);
v_metadata_1949_ = lean_ctor_get(v_x_1945_, 2);
lean_inc(v_metadata_1949_);
v_content_1950_ = lean_ctor_get(v_x_1945_, 3);
lean_inc_ref(v_content_1950_);
v_subParts_1951_ = lean_ctor_get(v_x_1945_, 4);
lean_inc_ref(v_subParts_1951_);
lean_dec_ref(v_x_1945_);
lean_inc_ref(v_inst_1944_);
lean_inc_ref(v_inst_1943_);
lean_inc_ref_n(v_inst_1942_, 2);
v_localinst_1952_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___redArg___boxed), 5, 3);
lean_closure_set(v_localinst_1952_, 0, v_inst_1942_);
lean_closure_set(v_localinst_1952_, 1, v_inst_1943_);
lean_closure_set(v_localinst_1952_, 2, v_inst_1944_);
v___x_1953_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1954_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__3));
v___x_1955_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4);
v___x_1956_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1956_, 0, lean_box(0));
lean_closure_set(v___x_1956_, 1, v_inst_1942_);
v___x_1957_ = l_Array_repr___redArg(v___x_1956_, v_title_1947_);
v___x_1958_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1955_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = 0;
v___x_1960_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set_uint8(v___x_1960_, sizeof(void*)*1, v___x_1959_);
v___x_1961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1954_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = lean_box(1);
v___x_1965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__6));
v___x_1967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v___x_1953_);
v___x_1969_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7);
v___x_1970_ = l_String_quote(v_titleString_1948_);
v___x_1971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
v___x_1972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1969_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*1, v___x_1959_);
v___x_1974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1968_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
lean_ctor_set(v___x_1975_, 1, v___x_1962_);
v___x_1976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v___x_1964_);
v___x_1977_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__9));
v___x_1978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v___x_1953_);
v___x_1980_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = l_Option_repr___redArg(v_inst_1944_, v_metadata_1949_, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1980_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*1, v___x_1959_);
v___x_1985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1979_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
lean_ctor_set(v___x_1986_, 1, v___x_1962_);
v___x_1987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
lean_ctor_set(v___x_1987_, 1, v___x_1964_);
v___x_1988_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__11));
v___x_1989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v___x_1953_);
v___x_1991_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12);
v___x_1992_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1992_, 0, lean_box(0));
lean_closure_set(v___x_1992_, 1, lean_box(0));
lean_closure_set(v___x_1992_, 2, v_inst_1942_);
lean_closure_set(v___x_1992_, 3, v_inst_1943_);
v___x_1993_ = l_Array_repr___redArg(v___x_1992_, v_content_1950_);
v___x_1994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1991_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*1, v___x_1959_);
v___x_1996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1990_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v___x_1962_);
v___x_1998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set(v___x_1998_, 1, v___x_1964_);
v___x_1999_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__14));
v___x_2000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1998_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v___x_1953_);
v___x_2002_ = l_Array_repr___redArg(v_localinst_1952_, v_subParts_1951_);
v___x_2003_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_1980_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*1, v___x_1959_);
v___x_2005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2001_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_2007_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_2008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set(v___x_2008_, 1, v___x_2005_);
v___x_2009_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_2010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2008_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2006_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*1, v___x_1959_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr(lean_object* v_i_2013_, lean_object* v_b_2014_, lean_object* v_p_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_x_2019_, lean_object* v_prec_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_2016_, v_inst_2017_, v_inst_2018_, v_x_2019_, v_prec_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___boxed(lean_object* v_i_2022_, lean_object* v_b_2023_, lean_object* v_p_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_x_2028_, lean_object* v_prec_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Doc_instReprPart_repr(v_i_2022_, v_b_2023_, v_p_2024_, v_inst_2025_, v_inst_2026_, v_inst_2027_, v_x_2028_, v_prec_2029_);
lean_dec(v_prec_2029_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart___redArg(lean_object* v_inst_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2034_, 0, lean_box(0));
lean_closure_set(v___x_2034_, 1, lean_box(0));
lean_closure_set(v___x_2034_, 2, lean_box(0));
lean_closure_set(v___x_2034_, 3, v_inst_2031_);
lean_closure_set(v___x_2034_, 4, v_inst_2032_);
lean_closure_set(v___x_2034_, 5, v_inst_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart(lean_object* v_i_2035_, lean_object* v_b_2036_, lean_object* v_p_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2041_, 0, lean_box(0));
lean_closure_set(v___x_2041_, 1, lean_box(0));
lean_closure_set(v___x_2041_, 2, lean_box(0));
lean_closure_set(v___x_2041_, 3, v_inst_2038_);
lean_closure_set(v___x_2041_, 4, v_inst_2039_);
lean_closure_set(v___x_2041_, 5, v_inst_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg(){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = ((lean_object*)(l_Lean_Doc_instInhabitedPart_default___redArg___closed__0));
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg___boxed(lean_object* v___dummy_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Doc_instInhabitedPart_default___redArg();
return v_res_2049_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedPart_default___closed__0(void){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Doc_instInhabitedPart_default___redArg();
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default(lean_object* v_i_2051_, lean_object* v_b_2052_, lean_object* v_p_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg(){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg___boxed(lean_object* v___dummy_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Doc_instInhabitedPart___redArg();
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart(lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg(lean_object* v_x_2063_){
_start:
{
lean_inc_ref(v_x_2063_);
return v_x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg___boxed(lean_object* v_x_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_Doc_Part_cast___redArg(v_x_2064_);
lean_dec_ref(v_x_2064_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast(lean_object* v_i_2066_, lean_object* v_i_x27_2067_, lean_object* v_b_2068_, lean_object* v_b_x27_2069_, lean_object* v_p_2070_, lean_object* v_p_x27_2071_, lean_object* v_inlines__eq_2072_, lean_object* v_blocks__eq_2073_, lean_object* v_metadata__eq_2074_, lean_object* v_x_2075_){
_start:
{
lean_inc_ref(v_x_2075_);
return v_x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___boxed(lean_object* v_i_2076_, lean_object* v_i_x27_2077_, lean_object* v_b_2078_, lean_object* v_b_x27_2079_, lean_object* v_p_2080_, lean_object* v_p_x27_2081_, lean_object* v_inlines__eq_2082_, lean_object* v_blocks__eq_2083_, lean_object* v_metadata__eq_2084_, lean_object* v_x_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Doc_Part_cast(v_i_2076_, v_i_x27_2077_, v_b_2078_, v_b_x27_2079_, v_p_2080_, v_p_x27_2081_, v_inlines__eq_2082_, v_blocks__eq_2083_, v_metadata__eq_2084_, v_x_2085_);
lean_dec_ref(v_x_2085_);
return v_res_2086_;
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
