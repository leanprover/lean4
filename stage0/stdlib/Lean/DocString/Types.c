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
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Doc_MathMode_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Lean_Doc_MathMode_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Doc_MathMode_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Lean_Doc_MathMode_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___redArg(lean_object* v_inline_27_){
_start:
{
lean_inc(v_inline_27_);
return v_inline_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___redArg___boxed(lean_object* v_inline_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Doc_MathMode_inline_elim___redArg(v_inline_28_);
lean_dec(v_inline_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_inline_33_){
_start:
{
lean_inc(v_inline_33_);
return v_inline_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_inline_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_inline_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Lean_Doc_MathMode_inline_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_inline_37_);
lean_dec(v_inline_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___redArg(lean_object* v_display_40_){
_start:
{
lean_inc(v_display_40_);
return v_display_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___redArg___boxed(lean_object* v_display_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Doc_MathMode_display_elim___redArg(v_display_41_);
lean_dec(v_display_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_display_46_){
_start:
{
lean_inc(v_display_46_);
return v_display_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathMode_display_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_display_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Lean_Doc_MathMode_display_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_display_50_);
lean_dec(v_display_50_);
return v_res_52_;
}
}
static lean_object* _init_l_Lean_Doc_instReprMathMode_repr___closed__4(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(2u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Doc_instReprMathMode_repr___closed__5(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprMathMode_repr(uint8_t v_x_63_, lean_object* v_prec_64_){
_start:
{
lean_object* v___y_66_; lean_object* v___y_73_; 
if (v_x_63_ == 0)
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1024u);
v___x_80_ = lean_nat_dec_le(v___x_79_, v_prec_64_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_66_ = v___x_81_;
goto v___jp_65_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_66_ = v___x_82_;
goto v___jp_65_;
}
}
else
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(1024u);
v___x_84_ = lean_nat_dec_le(v___x_83_, v_prec_64_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_73_ = v___x_85_;
goto v___jp_72_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_73_ = v___x_86_;
goto v___jp_72_;
}
}
v___jp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_67_ = ((lean_object*)(l_Lean_Doc_instReprMathMode_repr___closed__1));
lean_inc(v___y_66_);
v___x_68_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_68_, 0, v___y_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = 0;
v___x_70_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*1, v___x_69_);
v___x_71_ = l_Repr_addAppParen(v___x_70_, v_prec_64_);
return v___x_71_;
}
v___jp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_74_ = ((lean_object*)(l_Lean_Doc_instReprMathMode_repr___closed__3));
lean_inc(v___y_73_);
v___x_75_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_75_, 0, v___y_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = 0;
v___x_77_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_76_);
v___x_78_ = l_Repr_addAppParen(v___x_77_, v_prec_64_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprMathMode_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
uint8_t v_x_121__boxed_89_; lean_object* v_res_90_; 
v_x_121__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Lean_Doc_instReprMathMode_repr(v_x_121__boxed_89_, v_prec_88_);
lean_dec(v_prec_88_);
return v_res_90_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqMathMode_beq(uint8_t v_x_93_, uint8_t v_y_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_95_ = l_Lean_Doc_MathMode_ctorIdx(v_x_93_);
v___x_96_ = l_Lean_Doc_MathMode_ctorIdx(v_y_94_);
v___x_97_ = lean_nat_dec_eq(v___x_95_, v___x_96_);
lean_dec(v___x_96_);
lean_dec(v___x_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqMathMode_beq___boxed(lean_object* v_x_98_, lean_object* v_y_99_){
_start:
{
uint8_t v_x_17__boxed_100_; uint8_t v_y_18__boxed_101_; uint8_t v_res_102_; lean_object* v_r_103_; 
v_x_17__boxed_100_ = lean_unbox(v_x_98_);
v_y_18__boxed_101_ = lean_unbox(v_y_99_);
v_res_102_ = l_Lean_Doc_instBEqMathMode_beq(v_x_17__boxed_100_, v_y_18__boxed_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint64_t l_Lean_Doc_instHashableMathMode_hash(uint8_t v_x_106_){
_start:
{
if (v_x_106_ == 0)
{
uint64_t v___x_107_; 
v___x_107_ = 0ULL;
return v___x_107_;
}
else
{
uint64_t v___x_108_; 
v___x_108_ = 1ULL;
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instHashableMathMode_hash___boxed(lean_object* v_x_109_){
_start:
{
uint8_t v_x_28__boxed_110_; uint64_t v_res_111_; lean_object* v_r_112_; 
v_x_28__boxed_110_ = lean_unbox(v_x_109_);
v_res_111_ = l_Lean_Doc_instHashableMathMode_hash(v_x_28__boxed_110_);
v_r_112_ = lean_box_uint64(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdMathMode_ord(uint8_t v_x_115_, uint8_t v_y_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = l_Lean_Doc_MathMode_ctorIdx(v_x_115_);
v___x_118_ = l_Lean_Doc_MathMode_ctorIdx(v_y_116_);
v___x_119_ = lean_nat_dec_lt(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = lean_nat_dec_eq(v___x_117_, v___x_118_);
lean_dec(v___x_118_);
lean_dec(v___x_117_);
if (v___x_120_ == 0)
{
uint8_t v___x_121_; 
v___x_121_ = 2;
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 1;
return v___x_122_;
}
}
else
{
uint8_t v___x_123_; 
lean_dec(v___x_118_);
lean_dec(v___x_117_);
v___x_123_ = 0;
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdMathMode_ord___boxed(lean_object* v_x_124_, lean_object* v_y_125_){
_start:
{
uint8_t v_x_30__boxed_126_; uint8_t v_y_31__boxed_127_; uint8_t v_res_128_; lean_object* v_r_129_; 
v_x_30__boxed_126_ = lean_unbox(v_x_124_);
v_y_31__boxed_127_ = lean_unbox(v_y_125_);
v_res_128_ = l_Lean_Doc_instOrdMathMode_ord(v_x_30__boxed_126_, v_y_31__boxed_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___redArg(lean_object* v_x_132_){
_start:
{
switch(lean_obj_tag(v_x_132_))
{
case 0:
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(0u);
return v___x_133_;
}
case 1:
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(1u);
return v___x_134_;
}
case 2:
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(2u);
return v___x_135_;
}
case 3:
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(3u);
return v___x_136_;
}
case 4:
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(4u);
return v___x_137_;
}
case 5:
{
lean_object* v___x_138_; 
v___x_138_ = lean_unsigned_to_nat(5u);
return v___x_138_;
}
case 6:
{
lean_object* v___x_139_; 
v___x_139_ = lean_unsigned_to_nat(6u);
return v___x_139_;
}
case 7:
{
lean_object* v___x_140_; 
v___x_140_ = lean_unsigned_to_nat(7u);
return v___x_140_;
}
case 8:
{
lean_object* v___x_141_; 
v___x_141_ = lean_unsigned_to_nat(8u);
return v___x_141_;
}
case 9:
{
lean_object* v___x_142_; 
v___x_142_ = lean_unsigned_to_nat(9u);
return v___x_142_;
}
default: 
{
lean_object* v___x_143_; 
v___x_143_ = lean_unsigned_to_nat(10u);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___redArg___boxed(lean_object* v_x_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_144_);
lean_dec_ref(v_x_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx(lean_object* v_i_146_, lean_object* v_x_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorIdx___boxed(lean_object* v_i_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Doc_Inline_ctorIdx(v_i_149_, v_x_150_);
lean_dec_ref(v_x_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim___redArg(lean_object* v_t_152_, lean_object* v_k_153_){
_start:
{
switch(lean_obj_tag(v_t_152_))
{
case 4:
{
uint8_t v_mode_154_; lean_object* v_string_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_mode_154_ = lean_ctor_get_uint8(v_t_152_, sizeof(void*)*1);
v_string_155_ = lean_ctor_get(v_t_152_, 0);
lean_inc_ref(v_string_155_);
lean_dec_ref_known(v_t_152_, 1);
v___x_156_ = lean_box(v_mode_154_);
v___x_157_ = lean_apply_2(v_k_153_, v___x_156_, v_string_155_);
return v___x_157_;
}
case 6:
{
lean_object* v_content_158_; lean_object* v_url_159_; lean_object* v___x_160_; 
v_content_158_ = lean_ctor_get(v_t_152_, 0);
lean_inc_ref(v_content_158_);
v_url_159_ = lean_ctor_get(v_t_152_, 1);
lean_inc_ref(v_url_159_);
lean_dec_ref_known(v_t_152_, 2);
v___x_160_ = lean_apply_2(v_k_153_, v_content_158_, v_url_159_);
return v___x_160_;
}
case 7:
{
lean_object* v_name_161_; lean_object* v_content_162_; lean_object* v___x_163_; 
v_name_161_ = lean_ctor_get(v_t_152_, 0);
lean_inc_ref(v_name_161_);
v_content_162_ = lean_ctor_get(v_t_152_, 1);
lean_inc_ref(v_content_162_);
lean_dec_ref_known(v_t_152_, 2);
v___x_163_ = lean_apply_2(v_k_153_, v_name_161_, v_content_162_);
return v___x_163_;
}
case 8:
{
lean_object* v_alt_164_; lean_object* v_url_165_; lean_object* v___x_166_; 
v_alt_164_ = lean_ctor_get(v_t_152_, 0);
lean_inc_ref(v_alt_164_);
v_url_165_ = lean_ctor_get(v_t_152_, 1);
lean_inc_ref(v_url_165_);
lean_dec_ref_known(v_t_152_, 2);
v___x_166_ = lean_apply_2(v_k_153_, v_alt_164_, v_url_165_);
return v___x_166_;
}
case 10:
{
lean_object* v_container_167_; lean_object* v_content_168_; lean_object* v___x_169_; 
v_container_167_ = lean_ctor_get(v_t_152_, 0);
lean_inc(v_container_167_);
v_content_168_ = lean_ctor_get(v_t_152_, 1);
lean_inc_ref(v_content_168_);
lean_dec_ref_known(v_t_152_, 2);
v___x_169_ = lean_apply_2(v_k_153_, v_container_167_, v_content_168_);
return v___x_169_;
}
default: 
{
lean_object* v_string_170_; lean_object* v___x_171_; 
v_string_170_ = lean_ctor_get(v_t_152_, 0);
lean_inc_ref(v_string_170_);
lean_dec_ref(v_t_152_);
v___x_171_ = lean_apply_1(v_k_153_, v_string_170_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim(lean_object* v_i_172_, lean_object* v_motive__1_173_, lean_object* v_ctorIdx_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_k_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_175_, v_k_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_ctorElim___boxed(lean_object* v_i_179_, lean_object* v_motive__1_180_, lean_object* v_ctorIdx_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_k_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Doc_Inline_ctorElim(v_i_179_, v_motive__1_180_, v_ctorIdx_181_, v_t_182_, v_h_183_, v_k_184_);
lean_dec(v_ctorIdx_181_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_text_elim___redArg(lean_object* v_t_186_, lean_object* v_text_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_186_, v_text_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_text_elim(lean_object* v_i_189_, lean_object* v_motive__1_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_text_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_191_, v_text_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_emph_elim___redArg(lean_object* v_t_195_, lean_object* v_emph_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_195_, v_emph_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_emph_elim(lean_object* v_i_198_, lean_object* v_motive__1_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_emph_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_200_, v_emph_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_bold_elim___redArg(lean_object* v_t_204_, lean_object* v_bold_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_204_, v_bold_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_bold_elim(lean_object* v_i_207_, lean_object* v_motive__1_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_bold_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_209_, v_bold_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_code_elim___redArg(lean_object* v_t_213_, lean_object* v_code_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_213_, v_code_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_code_elim(lean_object* v_i_216_, lean_object* v_motive__1_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_code_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_218_, v_code_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_math_elim___redArg(lean_object* v_t_222_, lean_object* v_math_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_222_, v_math_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_math_elim(lean_object* v_i_225_, lean_object* v_motive__1_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_math_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_227_, v_math_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_linebreak_elim___redArg(lean_object* v_t_231_, lean_object* v_linebreak_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_231_, v_linebreak_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_linebreak_elim(lean_object* v_i_234_, lean_object* v_motive__1_235_, lean_object* v_t_236_, lean_object* v_h_237_, lean_object* v_linebreak_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_236_, v_linebreak_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_link_elim___redArg(lean_object* v_t_240_, lean_object* v_link_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_240_, v_link_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_link_elim(lean_object* v_i_243_, lean_object* v_motive__1_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_link_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_245_, v_link_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_footnote_elim___redArg(lean_object* v_t_249_, lean_object* v_footnote_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_249_, v_footnote_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_footnote_elim(lean_object* v_i_252_, lean_object* v_motive__1_253_, lean_object* v_t_254_, lean_object* v_h_255_, lean_object* v_footnote_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_254_, v_footnote_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_image_elim___redArg(lean_object* v_t_258_, lean_object* v_image_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_258_, v_image_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_image_elim(lean_object* v_i_261_, lean_object* v_motive__1_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_image_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_263_, v_image_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_concat_elim___redArg(lean_object* v_t_267_, lean_object* v_concat_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_267_, v_concat_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_concat_elim(lean_object* v_i_270_, lean_object* v_motive__1_271_, lean_object* v_t_272_, lean_object* v_h_273_, lean_object* v_concat_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_272_, v_concat_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_other_elim___redArg(lean_object* v_t_276_, lean_object* v_other_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_276_, v_other_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_other_elim(lean_object* v_i_279_, lean_object* v_motive__1_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_other_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Doc_Inline_ctorElim___redArg(v_t_281_, v_other_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline_beq___redArg___boxed(lean_object* v_inst_285_, lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_285_, v_x_286_, v_x_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqInline_beq___redArg(lean_object* v_inst_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_291_);
v___x_294_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_292_);
v___x_295_ = lean_nat_dec_eq(v___x_293_, v___x_294_);
lean_dec(v___x_294_);
lean_dec(v___x_293_);
if (v___x_295_ == 0)
{
lean_dec_ref(v_x_292_);
lean_dec_ref(v_x_291_);
lean_dec_ref(v_inst_290_);
return v___x_295_;
}
else
{
lean_object* v___x_296_; lean_object* v_content_298_; lean_object* v_content_x27_299_; 
lean_inc_ref(v_inst_290_);
v___x_296_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___redArg___boxed), 3, 1);
lean_closure_set(v___x_296_, 0, v_inst_290_);
switch(lean_obj_tag(v_x_291_))
{
case 1:
{
lean_object* v_content_304_; lean_object* v_content_305_; 
lean_dec_ref(v_inst_290_);
v_content_304_ = lean_ctor_get(v_x_291_, 0);
lean_inc_ref(v_content_304_);
lean_dec_ref_known(v_x_291_, 1);
v_content_305_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_content_305_);
lean_dec_ref(v_x_292_);
v_content_298_ = v_content_304_;
v_content_x27_299_ = v_content_305_;
goto v___jp_297_;
}
case 2:
{
lean_object* v_content_306_; lean_object* v_content_307_; 
lean_dec_ref(v_inst_290_);
v_content_306_ = lean_ctor_get(v_x_291_, 0);
lean_inc_ref(v_content_306_);
lean_dec_ref_known(v_x_291_, 1);
v_content_307_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_content_307_);
lean_dec_ref(v_x_292_);
v_content_298_ = v_content_306_;
v_content_x27_299_ = v_content_307_;
goto v___jp_297_;
}
case 4:
{
uint8_t v_mode_308_; lean_object* v_string_309_; uint8_t v_mode_310_; lean_object* v_string_311_; uint8_t v___x_312_; 
lean_dec_ref(v___x_296_);
lean_dec_ref(v_inst_290_);
v_mode_308_ = lean_ctor_get_uint8(v_x_291_, sizeof(void*)*1);
v_string_309_ = lean_ctor_get(v_x_291_, 0);
lean_inc_ref(v_string_309_);
lean_dec_ref_known(v_x_291_, 1);
v_mode_310_ = lean_ctor_get_uint8(v_x_292_, sizeof(void*)*1);
v_string_311_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_string_311_);
lean_dec_ref(v_x_292_);
v___x_312_ = l_Lean_Doc_instBEqMathMode_beq(v_mode_308_, v_mode_310_);
if (v___x_312_ == 0)
{
lean_dec_ref(v_string_311_);
lean_dec_ref(v_string_309_);
return v___x_312_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = lean_string_dec_eq(v_string_309_, v_string_311_);
lean_dec_ref(v_string_311_);
lean_dec_ref(v_string_309_);
return v___x_313_;
}
}
case 6:
{
lean_object* v_content_314_; lean_object* v_url_315_; lean_object* v_content_316_; lean_object* v_url_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
lean_dec_ref(v_inst_290_);
v_content_314_ = lean_ctor_get(v_x_291_, 0);
lean_inc_ref(v_content_314_);
v_url_315_ = lean_ctor_get(v_x_291_, 1);
lean_inc_ref(v_url_315_);
lean_dec_ref_known(v_x_291_, 2);
v_content_316_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_content_316_);
v_url_317_ = lean_ctor_get(v_x_292_, 1);
lean_inc_ref(v_url_317_);
lean_dec_ref(v_x_292_);
v___x_318_ = lean_array_get_size(v_content_314_);
v___x_319_ = lean_array_get_size(v_content_316_);
v___x_320_ = lean_nat_dec_eq(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_dec_ref(v_url_317_);
lean_dec_ref(v_content_316_);
lean_dec_ref(v_url_315_);
lean_dec_ref(v_content_314_);
lean_dec_ref(v___x_296_);
return v___x_320_;
}
else
{
uint8_t v___x_321_; 
v___x_321_ = l_Array_isEqvAux___redArg(v_content_314_, v_content_316_, v___x_296_, v___x_318_);
lean_dec_ref(v_content_316_);
lean_dec_ref(v_content_314_);
if (v___x_321_ == 0)
{
lean_dec_ref(v_url_317_);
lean_dec_ref(v_url_315_);
return v___x_321_;
}
else
{
uint8_t v___x_322_; 
v___x_322_ = lean_string_dec_eq(v_url_315_, v_url_317_);
lean_dec_ref(v_url_317_);
lean_dec_ref(v_url_315_);
return v___x_322_;
}
}
}
case 7:
{
lean_object* v_name_323_; lean_object* v_content_324_; lean_object* v_name_325_; lean_object* v_content_326_; uint8_t v___x_327_; 
lean_dec_ref(v_inst_290_);
v_name_323_ = lean_ctor_get(v_x_291_, 0);
lean_inc_ref(v_name_323_);
v_content_324_ = lean_ctor_get(v_x_291_, 1);
lean_inc_ref(v_content_324_);
lean_dec_ref_known(v_x_291_, 2);
v_name_325_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_name_325_);
v_content_326_ = lean_ctor_get(v_x_292_, 1);
lean_inc_ref(v_content_326_);
lean_dec_ref(v_x_292_);
v___x_327_ = lean_string_dec_eq(v_name_323_, v_name_325_);
lean_dec_ref(v_name_325_);
lean_dec_ref(v_name_323_);
if (v___x_327_ == 0)
{
lean_dec_ref(v_content_326_);
lean_dec_ref(v_content_324_);
lean_dec_ref(v___x_296_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = lean_array_get_size(v_content_324_);
v___x_329_ = lean_array_get_size(v_content_326_);
v___x_330_ = lean_nat_dec_eq(v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_dec_ref(v_content_326_);
lean_dec_ref(v_content_324_);
lean_dec_ref(v___x_296_);
return v___x_330_;
}
else
{
uint8_t v___x_331_; 
v___x_331_ = l_Array_isEqvAux___redArg(v_content_324_, v_content_326_, v___x_296_, v___x_328_);
lean_dec_ref(v_content_326_);
lean_dec_ref(v_content_324_);
return v___x_331_;
}
}
}
case 8:
{
lean_object* v_alt_332_; lean_object* v_url_333_; lean_object* v_alt_334_; lean_object* v_url_335_; uint8_t v___x_336_; 
lean_dec_ref(v___x_296_);
lean_dec_ref(v_inst_290_);
v_alt_332_ = lean_ctor_get(v_x_291_, 0);
lean_inc_ref(v_alt_332_);
v_url_333_ = lean_ctor_get(v_x_291_, 1);
lean_inc_ref(v_url_333_);
lean_dec_ref_known(v_x_291_, 2);
v_alt_334_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_alt_334_);
v_url_335_ = lean_ctor_get(v_x_292_, 1);
lean_inc_ref(v_url_335_);
lean_dec_ref(v_x_292_);
v___x_336_ = lean_string_dec_eq(v_alt_332_, v_alt_334_);
lean_dec_ref(v_alt_334_);
lean_dec_ref(v_alt_332_);
if (v___x_336_ == 0)
{
lean_dec_ref(v_url_335_);
lean_dec_ref(v_url_333_);
return v___x_336_;
}
else
{
uint8_t v___x_337_; 
v___x_337_ = lean_string_dec_eq(v_url_333_, v_url_335_);
lean_dec_ref(v_url_335_);
lean_dec_ref(v_url_333_);
return v___x_337_;
}
}
case 9:
{
lean_object* v_content_338_; lean_object* v_content_339_; 
lean_dec_ref(v_inst_290_);
v_content_338_ = lean_ctor_get(v_x_291_, 0);
lean_inc_ref(v_content_338_);
lean_dec_ref_known(v_x_291_, 1);
v_content_339_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_content_339_);
lean_dec_ref(v_x_292_);
v_content_298_ = v_content_338_;
v_content_x27_299_ = v_content_339_;
goto v___jp_297_;
}
case 10:
{
lean_object* v_container_340_; lean_object* v_content_341_; lean_object* v_container_342_; lean_object* v_content_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_container_340_ = lean_ctor_get(v_x_291_, 0);
lean_inc(v_container_340_);
v_content_341_ = lean_ctor_get(v_x_291_, 1);
lean_inc_ref(v_content_341_);
lean_dec_ref_known(v_x_291_, 2);
v_container_342_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_container_342_);
v_content_343_ = lean_ctor_get(v_x_292_, 1);
lean_inc_ref(v_content_343_);
lean_dec_ref(v_x_292_);
v___x_344_ = lean_apply_2(v_inst_290_, v_container_340_, v_container_342_);
v___x_345_ = lean_unbox(v___x_344_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
lean_dec_ref(v_content_343_);
lean_dec_ref(v_content_341_);
lean_dec_ref(v___x_296_);
v___x_346_ = lean_unbox(v___x_344_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = lean_array_get_size(v_content_341_);
v___x_348_ = lean_array_get_size(v_content_343_);
v___x_349_ = lean_nat_dec_eq(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_dec_ref(v_content_343_);
lean_dec_ref(v_content_341_);
lean_dec_ref(v___x_296_);
return v___x_349_;
}
else
{
uint8_t v___x_350_; 
v___x_350_ = l_Array_isEqvAux___redArg(v_content_341_, v_content_343_, v___x_296_, v___x_347_);
lean_dec_ref(v_content_343_);
lean_dec_ref(v_content_341_);
return v___x_350_;
}
}
}
default: 
{
lean_object* v_string_351_; lean_object* v_string_352_; uint8_t v___x_353_; 
lean_dec_ref(v___x_296_);
lean_dec_ref(v_inst_290_);
v_string_351_ = lean_ctor_get(v_x_291_, 0);
lean_inc_ref(v_string_351_);
lean_dec_ref(v_x_291_);
v_string_352_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_string_352_);
lean_dec_ref(v_x_292_);
v___x_353_ = lean_string_dec_eq(v_string_351_, v_string_352_);
lean_dec_ref(v_string_352_);
lean_dec_ref(v_string_351_);
return v___x_353_;
}
}
v___jp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = lean_array_get_size(v_content_298_);
v___x_301_ = lean_array_get_size(v_content_x27_299_);
v___x_302_ = lean_nat_dec_eq(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_dec_ref(v_content_x27_299_);
lean_dec_ref(v_content_298_);
lean_dec_ref(v___x_296_);
return v___x_302_;
}
else
{
uint8_t v___x_303_; 
v___x_303_ = l_Array_isEqvAux___redArg(v_content_298_, v_content_x27_299_, v___x_296_, v___x_300_);
lean_dec_ref(v_content_x27_299_);
lean_dec_ref(v_content_298_);
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqInline_beq(lean_object* v_i_354_, lean_object* v_inst_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = l_Lean_Doc_instBEqInline_beq___redArg(v_inst_355_, v_x_356_, v_x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline_beq___boxed(lean_object* v_i_359_, lean_object* v_inst_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Lean_Doc_instBEqInline_beq(v_i_359_, v_inst_360_, v_x_361_, v_x_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline___redArg(lean_object* v_inst_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_366_, 0, lean_box(0));
lean_closure_set(v___x_366_, 1, v_inst_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqInline(lean_object* v_i_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_369_, 0, lean_box(0));
lean_closure_set(v___x_369_, 1, v_inst_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___redArg___boxed(lean_object* v_inst_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_370_, v_x_371_, v_x_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord___redArg(lean_object* v_inst_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_string_379_; lean_object* v_string_x27_380_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_382_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_376_);
v___x_383_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_377_);
v___x_384_ = lean_nat_dec_lt(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
v___x_385_ = lean_nat_dec_eq(v___x_382_, v___x_383_);
lean_dec(v___x_383_);
lean_dec(v___x_382_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; 
lean_dec_ref(v_x_377_);
lean_dec_ref(v_x_376_);
lean_dec_ref(v_inst_375_);
v___x_386_ = 2;
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v_content_389_; lean_object* v_content_x27_390_; 
lean_inc_ref(v_inst_375_);
v___x_387_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___redArg___boxed), 3, 1);
lean_closure_set(v___x_387_, 0, v_inst_375_);
switch(lean_obj_tag(v_x_376_))
{
case 1:
{
lean_object* v_content_392_; lean_object* v_content_393_; 
lean_dec_ref(v_inst_375_);
v_content_392_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_392_);
lean_dec_ref_known(v_x_376_, 1);
v_content_393_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_content_393_);
lean_dec_ref(v_x_377_);
v_content_389_ = v_content_392_;
v_content_x27_390_ = v_content_393_;
goto v___jp_388_;
}
case 2:
{
lean_object* v_content_394_; lean_object* v_content_395_; 
lean_dec_ref(v_inst_375_);
v_content_394_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_394_);
lean_dec_ref_known(v_x_376_, 1);
v_content_395_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_content_395_);
lean_dec_ref(v_x_377_);
v_content_389_ = v_content_394_;
v_content_x27_390_ = v_content_395_;
goto v___jp_388_;
}
case 4:
{
uint8_t v_mode_396_; lean_object* v_string_397_; uint8_t v_mode_398_; lean_object* v_string_399_; uint8_t v___x_400_; 
lean_dec_ref(v___x_387_);
lean_dec_ref(v_inst_375_);
v_mode_396_ = lean_ctor_get_uint8(v_x_376_, sizeof(void*)*1);
v_string_397_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_string_397_);
lean_dec_ref_known(v_x_376_, 1);
v_mode_398_ = lean_ctor_get_uint8(v_x_377_, sizeof(void*)*1);
v_string_399_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_string_399_);
lean_dec_ref(v_x_377_);
v___x_400_ = l_Lean_Doc_instOrdMathMode_ord(v_mode_396_, v_mode_398_);
if (v___x_400_ == 1)
{
uint8_t v___x_401_; 
v___x_401_ = lean_string_compare(v_string_397_, v_string_399_);
lean_dec_ref(v_string_399_);
lean_dec_ref(v_string_397_);
if (v___x_401_ == 1)
{
return v___x_401_;
}
else
{
return v___x_401_;
}
}
else
{
lean_dec_ref(v_string_399_);
lean_dec_ref(v_string_397_);
return v___x_400_;
}
}
case 6:
{
lean_object* v_content_402_; lean_object* v_url_403_; lean_object* v_content_404_; lean_object* v_url_405_; uint8_t v___x_406_; 
lean_dec_ref(v_inst_375_);
v_content_402_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_402_);
v_url_403_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_url_403_);
lean_dec_ref_known(v_x_376_, 2);
v_content_404_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_content_404_);
v_url_405_ = lean_ctor_get(v_x_377_, 1);
lean_inc_ref(v_url_405_);
lean_dec_ref(v_x_377_);
v___x_406_ = l_Array_compareLex___redArg(v___x_387_, v_content_402_, v_content_404_);
lean_dec_ref(v_content_404_);
lean_dec_ref(v_content_402_);
if (v___x_406_ == 1)
{
uint8_t v___x_407_; 
v___x_407_ = lean_string_compare(v_url_403_, v_url_405_);
lean_dec_ref(v_url_405_);
lean_dec_ref(v_url_403_);
if (v___x_407_ == 1)
{
return v___x_407_;
}
else
{
return v___x_407_;
}
}
else
{
lean_dec_ref(v_url_405_);
lean_dec_ref(v_url_403_);
return v___x_406_;
}
}
case 7:
{
lean_object* v_name_408_; lean_object* v_content_409_; lean_object* v_name_410_; lean_object* v_content_411_; uint8_t v___x_412_; 
lean_dec_ref(v_inst_375_);
v_name_408_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_name_408_);
v_content_409_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_content_409_);
lean_dec_ref_known(v_x_376_, 2);
v_name_410_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_name_410_);
v_content_411_ = lean_ctor_get(v_x_377_, 1);
lean_inc_ref(v_content_411_);
lean_dec_ref(v_x_377_);
v___x_412_ = lean_string_compare(v_name_408_, v_name_410_);
lean_dec_ref(v_name_410_);
lean_dec_ref(v_name_408_);
if (v___x_412_ == 1)
{
uint8_t v___x_413_; 
v___x_413_ = l_Array_compareLex___redArg(v___x_387_, v_content_409_, v_content_411_);
lean_dec_ref(v_content_411_);
lean_dec_ref(v_content_409_);
if (v___x_413_ == 1)
{
return v___x_413_;
}
else
{
return v___x_413_;
}
}
else
{
lean_dec_ref(v_content_411_);
lean_dec_ref(v_content_409_);
lean_dec_ref(v___x_387_);
return v___x_412_;
}
}
case 8:
{
lean_object* v_alt_414_; lean_object* v_url_415_; lean_object* v_alt_416_; lean_object* v_url_417_; uint8_t v___x_418_; 
lean_dec_ref(v___x_387_);
lean_dec_ref(v_inst_375_);
v_alt_414_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_alt_414_);
v_url_415_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_url_415_);
lean_dec_ref_known(v_x_376_, 2);
v_alt_416_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_alt_416_);
v_url_417_ = lean_ctor_get(v_x_377_, 1);
lean_inc_ref(v_url_417_);
lean_dec_ref(v_x_377_);
v___x_418_ = lean_string_compare(v_alt_414_, v_alt_416_);
lean_dec_ref(v_alt_416_);
lean_dec_ref(v_alt_414_);
if (v___x_418_ == 1)
{
uint8_t v___x_419_; 
v___x_419_ = lean_string_compare(v_url_415_, v_url_417_);
lean_dec_ref(v_url_417_);
lean_dec_ref(v_url_415_);
if (v___x_419_ == 1)
{
return v___x_419_;
}
else
{
return v___x_419_;
}
}
else
{
lean_dec_ref(v_url_417_);
lean_dec_ref(v_url_415_);
return v___x_418_;
}
}
case 9:
{
lean_object* v_content_420_; lean_object* v_content_421_; 
lean_dec_ref(v_inst_375_);
v_content_420_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_420_);
lean_dec_ref_known(v_x_376_, 1);
v_content_421_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_content_421_);
lean_dec_ref(v_x_377_);
v_content_389_ = v_content_420_;
v_content_x27_390_ = v_content_421_;
goto v___jp_388_;
}
case 10:
{
lean_object* v_container_422_; lean_object* v_content_423_; lean_object* v_container_424_; lean_object* v_content_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_container_422_ = lean_ctor_get(v_x_376_, 0);
lean_inc(v_container_422_);
v_content_423_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_content_423_);
lean_dec_ref_known(v_x_376_, 2);
v_container_424_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_container_424_);
v_content_425_ = lean_ctor_get(v_x_377_, 1);
lean_inc_ref(v_content_425_);
lean_dec_ref(v_x_377_);
v___x_426_ = lean_apply_2(v_inst_375_, v_container_422_, v_container_424_);
v___x_427_ = lean_unbox(v___x_426_);
if (v___x_427_ == 1)
{
uint8_t v___x_428_; 
v___x_428_ = l_Array_compareLex___redArg(v___x_387_, v_content_423_, v_content_425_);
lean_dec_ref(v_content_425_);
lean_dec_ref(v_content_423_);
if (v___x_428_ == 1)
{
return v___x_428_;
}
else
{
return v___x_428_;
}
}
else
{
uint8_t v___x_429_; 
lean_dec_ref(v_content_425_);
lean_dec_ref(v_content_423_);
lean_dec_ref(v___x_387_);
v___x_429_ = lean_unbox(v___x_426_);
return v___x_429_;
}
}
default: 
{
lean_object* v_string_430_; lean_object* v_string_431_; 
lean_dec_ref(v___x_387_);
lean_dec_ref(v_inst_375_);
v_string_430_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_string_430_);
lean_dec_ref(v_x_376_);
v_string_431_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_string_431_);
lean_dec_ref(v_x_377_);
v_string_379_ = v_string_430_;
v_string_x27_380_ = v_string_431_;
goto v___jp_378_;
}
}
v___jp_388_:
{
uint8_t v___x_391_; 
v___x_391_ = l_Array_compareLex___redArg(v___x_387_, v_content_389_, v_content_x27_390_);
lean_dec_ref(v_content_x27_390_);
lean_dec_ref(v_content_389_);
if (v___x_391_ == 1)
{
return v___x_391_;
}
else
{
return v___x_391_;
}
}
}
}
else
{
uint8_t v___x_432_; 
lean_dec(v___x_383_);
lean_dec(v___x_382_);
lean_dec_ref(v_x_377_);
lean_dec_ref(v_x_376_);
lean_dec_ref(v_inst_375_);
v___x_432_ = 0;
return v___x_432_;
}
v___jp_378_:
{
uint8_t v___x_381_; 
v___x_381_ = lean_string_compare(v_string_379_, v_string_x27_380_);
lean_dec_ref(v_string_x27_380_);
lean_dec_ref(v_string_379_);
if (v___x_381_ == 1)
{
return v___x_381_;
}
else
{
return v___x_381_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord(lean_object* v_i_433_, lean_object* v_inst_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_434_, v_x_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___boxed(lean_object* v_i_438_, lean_object* v_inst_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Lean_Doc_instOrdInline_ord(v_i_438_, v_inst_439_, v_x_440_, v_x_441_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline___redArg(lean_object* v_inst_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_445_, 0, lean_box(0));
lean_closure_set(v___x_445_, 1, v_inst_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline(lean_object* v_i_446_, lean_object* v_inst_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_448_, 0, lean_box(0));
lean_closure_set(v___x_448_, 1, v_inst_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg___boxed(lean_object* v_inst_515_, lean_object* v_x_516_, lean_object* v_prec_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_515_, v_x_516_, v_prec_517_);
lean_dec(v_prec_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg(lean_object* v_inst_519_, lean_object* v_x_520_, lean_object* v_prec_521_){
_start:
{
lean_object* v_localinst_522_; 
lean_inc_ref(v_inst_519_);
v_localinst_522_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_522_, 0, v_inst_519_);
switch(lean_obj_tag(v_x_520_))
{
case 0:
{
lean_object* v_string_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref(v_localinst_522_);
lean_dec_ref(v_inst_519_);
v_string_523_ = lean_ctor_get(v_x_520_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_543_ == 0)
{
v___x_525_ = v_x_520_;
v_isShared_526_ = v_isSharedCheck_543_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_string_523_);
lean_dec(v_x_520_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_543_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___y_528_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(1024u);
v___x_540_ = lean_nat_dec_le(v___x_539_, v_prec_521_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_528_ = v___x_541_;
goto v___jp_527_;
}
else
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_528_ = v___x_542_;
goto v___jp_527_;
}
v___jp_527_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_529_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__2));
v___x_530_ = l_String_quote(v_string_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 3);
lean_ctor_set(v___x_525_, 0, v___x_530_);
v___x_532_ = v___x_525_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_538_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_529_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
lean_inc(v___y_528_);
v___x_534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_534_, 0, v___y_528_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = 0;
v___x_536_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*1, v___x_535_);
v___x_537_ = l_Repr_addAppParen(v___x_536_, v_prec_521_);
return v___x_537_;
}
}
}
}
case 1:
{
lean_object* v_content_544_; lean_object* v___y_546_; lean_object* v___x_554_; uint8_t v___x_555_; 
lean_dec_ref(v_inst_519_);
v_content_544_ = lean_ctor_get(v_x_520_, 0);
lean_inc_ref(v_content_544_);
lean_dec_ref_known(v_x_520_, 1);
v___x_554_ = lean_unsigned_to_nat(1024u);
v___x_555_ = lean_nat_dec_le(v___x_554_, v_prec_521_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_546_ = v___x_556_;
goto v___jp_545_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_546_ = v___x_557_;
goto v___jp_545_;
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_547_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__5));
v___x_548_ = l_Array_repr___redArg(v_localinst_522_, v_content_544_);
v___x_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
lean_inc(v___y_546_);
v___x_550_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_550_, 0, v___y_546_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = 0;
v___x_552_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*1, v___x_551_);
v___x_553_ = l_Repr_addAppParen(v___x_552_, v_prec_521_);
return v___x_553_;
}
}
case 2:
{
lean_object* v_content_558_; lean_object* v___y_560_; lean_object* v___x_568_; uint8_t v___x_569_; 
lean_dec_ref(v_inst_519_);
v_content_558_ = lean_ctor_get(v_x_520_, 0);
lean_inc_ref(v_content_558_);
lean_dec_ref_known(v_x_520_, 1);
v___x_568_ = lean_unsigned_to_nat(1024u);
v___x_569_ = lean_nat_dec_le(v___x_568_, v_prec_521_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
v___x_570_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_560_ = v___x_570_;
goto v___jp_559_;
}
else
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_560_ = v___x_571_;
goto v___jp_559_;
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_561_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__8));
v___x_562_ = l_Array_repr___redArg(v_localinst_522_, v_content_558_);
v___x_563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
lean_inc(v___y_560_);
v___x_564_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_564_, 0, v___y_560_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = 0;
v___x_566_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_565_);
v___x_567_ = l_Repr_addAppParen(v___x_566_, v_prec_521_);
return v___x_567_;
}
}
case 3:
{
lean_object* v_string_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v_localinst_522_);
lean_dec_ref(v_inst_519_);
v_string_572_ = lean_ctor_get(v_x_520_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_592_ == 0)
{
v___x_574_ = v_x_520_;
v_isShared_575_ = v_isSharedCheck_592_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_string_572_);
lean_dec(v_x_520_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_592_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___y_577_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(1024u);
v___x_589_ = lean_nat_dec_le(v___x_588_, v_prec_521_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_577_ = v___x_590_;
goto v___jp_576_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_577_ = v___x_591_;
goto v___jp_576_;
}
v___jp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_578_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__11));
v___x_579_ = l_String_quote(v_string_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_579_);
v___x_581_ = v___x_574_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_587_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_578_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
lean_inc(v___y_577_);
v___x_583_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_583_, 0, v___y_577_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = 0;
v___x_585_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*1, v___x_584_);
v___x_586_ = l_Repr_addAppParen(v___x_585_, v_prec_521_);
return v___x_586_;
}
}
}
}
case 4:
{
uint8_t v_mode_593_; lean_object* v_string_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_localinst_522_);
lean_dec_ref(v_inst_519_);
v_mode_593_ = lean_ctor_get_uint8(v_x_520_, sizeof(void*)*1);
v_string_594_ = lean_ctor_get(v_x_520_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_619_ == 0)
{
v___x_596_ = v_x_520_;
v_isShared_597_ = v_isSharedCheck_619_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_string_594_);
lean_dec(v_x_520_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_619_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___y_599_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1024u);
v___x_616_ = lean_nat_dec_le(v___x_615_, v_prec_521_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_599_ = v___x_617_;
goto v___jp_598_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_599_ = v___x_618_;
goto v___jp_598_;
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; lean_object* v___x_612_; 
v___x_600_ = lean_box(1);
v___x_601_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__14));
v___x_602_ = lean_unsigned_to_nat(1024u);
v___x_603_ = l_Lean_Doc_instReprMathMode_repr(v_mode_593_, v___x_602_);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_601_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_600_);
v___x_606_ = l_String_quote(v_string_594_);
v___x_607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
v___x_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
lean_inc(v___y_599_);
v___x_609_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_609_, 0, v___y_599_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = 0;
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 6);
lean_ctor_set(v___x_596_, 0, v___x_609_);
v___x_612_ = v___x_596_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_609_);
v___x_612_ = v_reuseFailAlloc_614_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; 
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*1, v___x_610_);
v___x_613_ = l_Repr_addAppParen(v___x_612_, v_prec_521_);
return v___x_613_;
}
}
}
}
case 5:
{
lean_object* v_string_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v_localinst_522_);
lean_dec_ref(v_inst_519_);
v_string_620_ = lean_ctor_get(v_x_520_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_640_ == 0)
{
v___x_622_ = v_x_520_;
v_isShared_623_ = v_isSharedCheck_640_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_string_620_);
lean_dec(v_x_520_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_640_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___y_625_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(1024u);
v___x_637_ = lean_nat_dec_le(v___x_636_, v_prec_521_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_625_ = v___x_638_;
goto v___jp_624_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_625_ = v___x_639_;
goto v___jp_624_;
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_626_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__17));
v___x_627_ = l_String_quote(v_string_620_);
if (v_isShared_623_ == 0)
{
lean_ctor_set_tag(v___x_622_, 3);
lean_ctor_set(v___x_622_, 0, v___x_627_);
v___x_629_ = v___x_622_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_635_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_626_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
lean_inc(v___y_625_);
v___x_631_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_631_, 0, v___y_625_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = 0;
v___x_633_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*1, v___x_632_);
v___x_634_ = l_Repr_addAppParen(v___x_633_, v_prec_521_);
return v___x_634_;
}
}
}
}
case 6:
{
lean_object* v_content_641_; lean_object* v_url_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_666_; 
lean_dec_ref(v_inst_519_);
v_content_641_ = lean_ctor_get(v_x_520_, 0);
v_url_642_ = lean_ctor_get(v_x_520_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_666_ == 0)
{
v___x_644_ = v_x_520_;
v_isShared_645_ = v_isSharedCheck_666_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_url_642_);
lean_inc(v_content_641_);
lean_dec(v_x_520_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_666_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___y_647_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(1024u);
v___x_663_ = lean_nat_dec_le(v___x_662_, v_prec_521_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_647_ = v___x_664_;
goto v___jp_646_;
}
else
{
lean_object* v___x_665_; 
v___x_665_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_647_ = v___x_665_;
goto v___jp_646_;
}
v___jp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_648_ = lean_box(1);
v___x_649_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__20));
v___x_650_ = l_Array_repr___redArg(v_localinst_522_, v_content_641_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 5);
lean_ctor_set(v___x_644_, 1, v___x_650_);
lean_ctor_set(v___x_644_, 0, v___x_649_);
v___x_652_ = v___x_644_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_661_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_648_);
v___x_654_ = l_String_quote(v_url_642_);
v___x_655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
v___x_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_653_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
lean_inc(v___y_647_);
v___x_657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_657_, 0, v___y_647_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = 0;
v___x_659_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*1, v___x_658_);
v___x_660_ = l_Repr_addAppParen(v___x_659_, v_prec_521_);
return v___x_660_;
}
}
}
}
case 7:
{
lean_object* v_name_667_; lean_object* v_content_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_692_; 
lean_dec_ref(v_inst_519_);
v_name_667_ = lean_ctor_get(v_x_520_, 0);
v_content_668_ = lean_ctor_get(v_x_520_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_692_ == 0)
{
v___x_670_ = v_x_520_;
v_isShared_671_ = v_isSharedCheck_692_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_content_668_);
lean_inc(v_name_667_);
lean_dec(v_x_520_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_692_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___y_673_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_unsigned_to_nat(1024u);
v___x_689_ = lean_nat_dec_le(v___x_688_, v_prec_521_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_673_ = v___x_690_;
goto v___jp_672_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_673_ = v___x_691_;
goto v___jp_672_;
}
v___jp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_674_ = lean_box(1);
v___x_675_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__23));
v___x_676_ = l_String_quote(v_name_667_);
v___x_677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 5);
lean_ctor_set(v___x_670_, 1, v___x_677_);
lean_ctor_set(v___x_670_, 0, v___x_675_);
v___x_679_ = v___x_670_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_677_);
v___x_679_ = v_reuseFailAlloc_687_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_674_);
v___x_681_ = l_Array_repr___redArg(v_localinst_522_, v_content_668_);
v___x_682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
lean_inc(v___y_673_);
v___x_683_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_683_, 0, v___y_673_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = 0;
v___x_685_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*1, v___x_684_);
v___x_686_ = l_Repr_addAppParen(v___x_685_, v_prec_521_);
return v___x_686_;
}
}
}
}
case 8:
{
lean_object* v_alt_693_; lean_object* v_url_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v_localinst_522_);
lean_dec_ref(v_inst_519_);
v_alt_693_ = lean_ctor_get(v_x_520_, 0);
v_url_694_ = lean_ctor_get(v_x_520_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_719_ == 0)
{
v___x_696_ = v_x_520_;
v_isShared_697_ = v_isSharedCheck_719_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_url_694_);
lean_inc(v_alt_693_);
lean_dec(v_x_520_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_719_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___y_699_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = lean_unsigned_to_nat(1024u);
v___x_716_ = lean_nat_dec_le(v___x_715_, v_prec_521_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_699_ = v___x_717_;
goto v___jp_698_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_699_ = v___x_718_;
goto v___jp_698_;
}
v___jp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_700_ = lean_box(1);
v___x_701_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__26));
v___x_702_ = l_String_quote(v_alt_693_);
v___x_703_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 5);
lean_ctor_set(v___x_696_, 1, v___x_703_);
lean_ctor_set(v___x_696_, 0, v___x_701_);
v___x_705_ = v___x_696_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_714_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_700_);
v___x_707_ = l_String_quote(v_url_694_);
v___x_708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
v___x_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_706_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
lean_inc(v___y_699_);
v___x_710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_710_, 0, v___y_699_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = 0;
v___x_712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*1, v___x_711_);
v___x_713_ = l_Repr_addAppParen(v___x_712_, v_prec_521_);
return v___x_713_;
}
}
}
}
case 9:
{
lean_object* v_content_720_; lean_object* v___y_722_; lean_object* v___x_730_; uint8_t v___x_731_; 
lean_dec_ref(v_inst_519_);
v_content_720_ = lean_ctor_get(v_x_520_, 0);
lean_inc_ref(v_content_720_);
lean_dec_ref_known(v_x_520_, 1);
v___x_730_ = lean_unsigned_to_nat(1024u);
v___x_731_ = lean_nat_dec_le(v___x_730_, v_prec_521_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_722_ = v___x_732_;
goto v___jp_721_;
}
else
{
lean_object* v___x_733_; 
v___x_733_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_722_ = v___x_733_;
goto v___jp_721_;
}
v___jp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_723_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__29));
v___x_724_ = l_Array_repr___redArg(v_localinst_522_, v_content_720_);
v___x_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
lean_inc(v___y_722_);
v___x_726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_726_, 0, v___y_722_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = 0;
v___x_728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set_uint8(v___x_728_, sizeof(void*)*1, v___x_727_);
v___x_729_ = l_Repr_addAppParen(v___x_728_, v_prec_521_);
return v___x_729_;
}
}
default: 
{
lean_object* v_container_734_; lean_object* v_content_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_759_; 
v_container_734_ = lean_ctor_get(v_x_520_, 0);
v_content_735_ = lean_ctor_get(v_x_520_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_759_ == 0)
{
v___x_737_ = v_x_520_;
v_isShared_738_ = v_isSharedCheck_759_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_content_735_);
lean_inc(v_container_734_);
lean_dec(v_x_520_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_759_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___y_740_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(1024u);
v___x_756_ = lean_nat_dec_le(v___x_755_, v_prec_521_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
v___x_757_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_740_ = v___x_757_;
goto v___jp_739_;
}
else
{
lean_object* v___x_758_; 
v___x_758_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_740_ = v___x_758_;
goto v___jp_739_;
}
v___jp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_741_ = lean_box(1);
v___x_742_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__32));
v___x_743_ = lean_unsigned_to_nat(1024u);
v___x_744_ = lean_apply_2(v_inst_519_, v_container_734_, v___x_743_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 5);
lean_ctor_set(v___x_737_, 1, v___x_744_);
lean_ctor_set(v___x_737_, 0, v___x_742_);
v___x_746_ = v___x_737_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_754_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___x_741_);
v___x_748_ = l_Array_repr___redArg(v_localinst_522_, v_content_735_);
v___x_749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
lean_inc(v___y_740_);
v___x_750_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_750_, 0, v___y_740_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = 0;
v___x_752_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*1, v___x_751_);
v___x_753_ = l_Repr_addAppParen(v___x_752_, v_prec_521_);
return v___x_753_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr(lean_object* v_i_760_, lean_object* v_inst_761_, lean_object* v_x_762_, lean_object* v_prec_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_761_, v_x_762_, v_prec_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___boxed(lean_object* v_i_765_, lean_object* v_inst_766_, lean_object* v_x_767_, lean_object* v_prec_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Doc_instReprInline_repr(v_i_765_, v_inst_766_, v_x_767_, v_prec_768_);
lean_dec(v_prec_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline___redArg(lean_object* v_inst_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_771_, 0, lean_box(0));
lean_closure_set(v___x_771_, 1, v_inst_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline(lean_object* v_i_772_, lean_object* v_inst_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_774_, 0, lean_box(0));
lean_closure_set(v___x_774_, 1, v_inst_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default(lean_object* v_i_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = ((lean_object*)(l_Lean_Doc_instInhabitedInline_default___closed__1));
return v___x_779_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedInline___closed__0(void){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Doc_instInhabitedInline_default(lean_box(0));
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline(lean_object* v_a_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline___closed__0, &l_Lean_Doc_instInhabitedInline___closed__0_once, _init_l_Lean_Doc_instInhabitedInline___closed__0);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg(lean_object* v_x_783_){
_start:
{
lean_inc_ref(v_x_783_);
return v_x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg___boxed(lean_object* v_x_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Doc_Inline_cast___redArg(v_x_784_);
lean_dec_ref(v_x_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast(lean_object* v_i_786_, lean_object* v_i_x27_787_, lean_object* v_inlines__eq_788_, lean_object* v_x_789_){
_start:
{
lean_inc_ref(v_x_789_);
return v_x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___boxed(lean_object* v_i_790_, lean_object* v_i_x27_791_, lean_object* v_inlines__eq_792_, lean_object* v_x_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Doc_Inline_cast(v_i_790_, v_i_x27_791_, v_inlines__eq_792_, v_x_793_);
lean_dec_ref(v_x_793_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___lam__0(lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
if (lean_obj_tag(v_x_795_) == 9)
{
lean_object* v_content_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_content_797_ = lean_ctor_get(v_x_795_, 0);
v___x_798_ = lean_array_get_size(v_content_797_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_nat_dec_eq(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
if (lean_obj_tag(v_x_796_) == 9)
{
lean_object* v_content_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_811_; 
v_content_801_ = lean_ctor_get(v_x_796_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_811_ == 0)
{
v___x_803_ = v_x_796_;
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_content_801_);
lean_dec(v_x_796_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_array_get_size(v_content_801_);
v___x_806_ = lean_nat_dec_eq(v___x_805_, v___x_799_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_809_; 
lean_inc_ref(v_content_797_);
lean_dec_ref_known(v_x_795_, 1);
v___x_807_ = l_Array_append___redArg(v_content_797_, v_content_801_);
lean_dec_ref(v_content_801_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_807_);
v___x_809_ = v___x_803_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_del_object(v___x_803_);
lean_dec_ref(v_content_801_);
return v_x_795_;
}
}
}
else
{
lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
lean_inc_ref(v_content_797_);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_795_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_x_795_, 0);
lean_dec(v_unused_820_);
v___x_813_ = v_x_795_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_dec(v_x_795_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_array_push(v_content_797_, v_x_796_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_dec_ref_known(v_x_795_, 1);
return v_x_796_;
}
}
else
{
if (lean_obj_tag(v_x_796_) == 9)
{
lean_object* v_content_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_835_; 
v_content_821_ = lean_ctor_get(v_x_796_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_835_ == 0)
{
v___x_823_ = v_x_796_;
v_isShared_824_ = v_isSharedCheck_835_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_content_821_);
lean_dec(v_x_796_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_835_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_825_ = lean_array_get_size(v_content_821_);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_nat_dec_eq(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_828_ = lean_unsigned_to_nat(1u);
v___x_829_ = lean_mk_empty_array_with_capacity(v___x_828_);
v___x_830_ = lean_array_push(v___x_829_, v_x_795_);
v___x_831_ = l_Array_append___redArg(v___x_830_, v_content_821_);
lean_dec_ref(v_content_821_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_831_);
v___x_833_ = v___x_823_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_del_object(v___x_823_);
lean_dec_ref(v_content_821_);
return v_x_795_;
}
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_836_ = lean_unsigned_to_nat(2u);
v___x_837_ = lean_mk_empty_array_with_capacity(v___x_836_);
v___x_838_ = lean_array_push(v___x_837_, v_x_795_);
v___x_839_ = lean_array_push(v___x_838_, v_x_796_);
v___x_840_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline(lean_object* v_i_842_){
_start:
{
lean_object* v___f_843_; 
v___f_843_ = ((lean_object*)(l_Lean_Doc_instAppendInline___closed__0));
return v___f_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty(lean_object* v_i_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = ((lean_object*)(l_Lean_Doc_Inline_empty___closed__1));
return v___x_849_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_unsigned_to_nat(12u);
v___x_864_ = lean_nat_to_int(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__0));
v___x_867_ = lean_string_length(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9);
v___x_869_ = lean_nat_to_int(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___redArg(lean_object* v_inst_874_, lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_876_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__6));
v___x_877_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_878_ = l_Array_repr___redArg(v_inst_874_, v_x_875_);
v___x_879_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = 0;
v___x_881_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v___x_880_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_876_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_884_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_882_);
v___x_886_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_883_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*1, v___x_880_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr(lean_object* v_00_u03b1_890_, lean_object* v_inst_891_, lean_object* v_x_892_, lean_object* v_prec_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Doc_instReprListItem_repr___redArg(v_inst_891_, v_x_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___boxed(lean_object* v_00_u03b1_895_, lean_object* v_inst_896_, lean_object* v_x_897_, lean_object* v_prec_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Doc_instReprListItem_repr(v_00_u03b1_895_, v_inst_896_, v_x_897_, v_prec_898_);
lean_dec(v_prec_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem___redArg(lean_object* v_inst_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_901_, 0, lean_box(0));
lean_closure_set(v___x_901_, 1, v_inst_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem(lean_object* v_00_u03b1_902_, lean_object* v_inst_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_904_, 0, lean_box(0));
lean_closure_set(v___x_904_, 1, v_inst_903_);
return v___x_904_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq___redArg(lean_object* v_inst_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_908_ = lean_array_get_size(v_x_906_);
v___x_909_ = lean_array_get_size(v_x_907_);
v___x_910_ = lean_nat_dec_eq(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_dec_ref(v_inst_905_);
return v___x_910_;
}
else
{
uint8_t v___x_911_; 
v___x_911_ = l_Array_isEqvAux___redArg(v_x_906_, v_x_907_, v_inst_905_, v___x_908_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___redArg___boxed(lean_object* v_inst_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
uint8_t v_res_915_; lean_object* v_r_916_; 
v_res_915_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_912_, v_x_913_, v_x_914_);
lean_dec_ref(v_x_914_);
lean_dec_ref(v_x_913_);
v_r_916_ = lean_box(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq(lean_object* v_00_u03b1_917_, lean_object* v_inst_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_918_, v_x_919_, v_x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___boxed(lean_object* v_00_u03b1_922_, lean_object* v_inst_923_, lean_object* v_x_924_, lean_object* v_x_925_){
_start:
{
uint8_t v_res_926_; lean_object* v_r_927_; 
v_res_926_ = l_Lean_Doc_instBEqListItem_beq(v_00_u03b1_922_, v_inst_923_, v_x_924_, v_x_925_);
lean_dec_ref(v_x_925_);
lean_dec_ref(v_x_924_);
v_r_927_ = lean_box(v_res_926_);
return v_r_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem___redArg(lean_object* v_inst_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_929_, 0, lean_box(0));
lean_closure_set(v___x_929_, 1, v_inst_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem(lean_object* v_00_u03b1_930_, lean_object* v_inst_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_932_, 0, lean_box(0));
lean_closure_set(v___x_932_, 1, v_inst_931_);
return v___x_932_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord___redArg(lean_object* v_inst_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = l_Array_compareLex___redArg(v_inst_933_, v_x_934_, v_x_935_);
if (v___x_936_ == 1)
{
return v___x_936_;
}
else
{
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___redArg___boxed(lean_object* v_inst_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
uint8_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_937_, v_x_938_, v_x_939_);
lean_dec_ref(v_x_939_);
lean_dec_ref(v_x_938_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord(lean_object* v_00_u03b1_942_, lean_object* v_inst_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_943_, v_x_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___boxed(lean_object* v_00_u03b1_947_, lean_object* v_inst_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Lean_Doc_instOrdListItem_ord(v_00_u03b1_947_, v_inst_948_, v_x_949_, v_x_950_);
lean_dec_ref(v_x_950_);
lean_dec_ref(v_x_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem___redArg(lean_object* v_inst_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_954_, 0, lean_box(0));
lean_closure_set(v___x_954_, 1, v_inst_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem(lean_object* v_00_u03b1_955_, lean_object* v_inst_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_957_, 0, lean_box(0));
lean_closure_set(v___x_957_, 1, v_inst_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default(lean_object* v_00_u03b1_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = ((lean_object*)(l_Lean_Doc_instInhabitedListItem_default___closed__0));
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedListItem___closed__0(void){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Doc_instInhabitedListItem_default(lean_box(0));
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem(lean_object* v_a_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem___closed__0, &l_Lean_Doc_instInhabitedListItem___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem___closed__0);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_unsigned_to_nat(8u);
v___x_975_ = lean_nat_to_int(v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___redArg(lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_x_984_){
_start:
{
lean_object* v_term_985_; lean_object* v_desc_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1018_; 
v_term_985_ = lean_ctor_get(v_x_984_, 0);
v_desc_986_ = lean_ctor_get(v_x_984_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_x_984_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_988_ = v_x_984_;
v_isShared_989_ = v_isSharedCheck_1018_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_desc_986_);
lean_inc(v_term_985_);
lean_dec(v_x_984_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1018_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_990_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_991_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__3));
v___x_992_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4);
v___x_993_ = l_Array_repr___redArg(v_inst_982_, v_term_985_);
if (v_isShared_989_ == 0)
{
lean_ctor_set_tag(v___x_988_, 4);
lean_ctor_set(v___x_988_, 1, v___x_993_);
lean_ctor_set(v___x_988_, 0, v___x_992_);
v___x_995_ = v___x_988_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_1017_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_996_ = 0;
v___x_997_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*1, v___x_996_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_991_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_box(1);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__8));
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_990_);
v___x_1006_ = l_Array_repr___redArg(v_inst_983_, v_desc_986_);
v___x_1007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_992_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*1, v___x_996_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1005_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_1011_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_1009_);
v___x_1013_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1010_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*1, v___x_996_);
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr(lean_object* v_00_u03b1_1019_, lean_object* v_00_u03b2_1020_, lean_object* v_inst_1021_, lean_object* v_inst_1022_, lean_object* v_x_1023_, lean_object* v_prec_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Doc_instReprDescItem_repr___redArg(v_inst_1021_, v_inst_1022_, v_x_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_00_u03b2_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_x_1030_, lean_object* v_prec_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_Doc_instReprDescItem_repr(v_00_u03b1_1026_, v_00_u03b2_1027_, v_inst_1028_, v_inst_1029_, v_x_1030_, v_prec_1031_);
lean_dec(v_prec_1031_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem___redArg(lean_object* v_inst_1033_, lean_object* v_inst_1034_){
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
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1040_, 0, lean_box(0));
lean_closure_set(v___x_1040_, 1, lean_box(0));
lean_closure_set(v___x_1040_, 2, v_inst_1038_);
lean_closure_set(v___x_1040_, 3, v_inst_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq___redArg(lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v_term_1045_; lean_object* v_desc_1046_; lean_object* v_term_1047_; lean_object* v_desc_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_term_1045_ = lean_ctor_get(v_x_1043_, 0);
v_desc_1046_ = lean_ctor_get(v_x_1043_, 1);
v_term_1047_ = lean_ctor_get(v_x_1044_, 0);
v_desc_1048_ = lean_ctor_get(v_x_1044_, 1);
v___x_1049_ = lean_array_get_size(v_term_1045_);
v___x_1050_ = lean_array_get_size(v_term_1047_);
v___x_1051_ = lean_nat_dec_eq(v___x_1049_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_dec_ref(v_inst_1042_);
lean_dec_ref(v_inst_1041_);
return v___x_1051_;
}
else
{
uint8_t v___x_1052_; 
v___x_1052_ = l_Array_isEqvAux___redArg(v_term_1045_, v_term_1047_, v_inst_1041_, v___x_1049_);
if (v___x_1052_ == 0)
{
lean_dec_ref(v_inst_1042_);
return v___x_1052_;
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1053_ = lean_array_get_size(v_desc_1046_);
v___x_1054_ = lean_array_get_size(v_desc_1048_);
v___x_1055_ = lean_nat_dec_eq(v___x_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_dec_ref(v_inst_1042_);
return v___x_1055_;
}
else
{
uint8_t v___x_1056_; 
v___x_1056_ = l_Array_isEqvAux___redArg(v_desc_1046_, v_desc_1048_, v_inst_1042_, v___x_1053_);
return v___x_1056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___redArg___boxed(lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
uint8_t v_res_1061_; lean_object* v_r_1062_; 
v_res_1061_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1057_, v_inst_1058_, v_x_1059_, v_x_1060_);
lean_dec_ref(v_x_1060_);
lean_dec_ref(v_x_1059_);
v_r_1062_ = lean_box(v_res_1061_);
return v_r_1062_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq(lean_object* v_00_u03b1_1063_, lean_object* v_00_u03b2_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_){
_start:
{
uint8_t v___x_1069_; 
v___x_1069_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1065_, v_inst_1066_, v_x_1067_, v_x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___boxed(lean_object* v_00_u03b1_1070_, lean_object* v_00_u03b2_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = l_Lean_Doc_instBEqDescItem_beq(v_00_u03b1_1070_, v_00_u03b2_1071_, v_inst_1072_, v_inst_1073_, v_x_1074_, v_x_1075_);
lean_dec_ref(v_x_1075_);
lean_dec_ref(v_x_1074_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem___redArg(lean_object* v_inst_1078_, lean_object* v_inst_1079_){
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
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem(lean_object* v_00_u03b1_1081_, lean_object* v_00_u03b2_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1085_, 0, lean_box(0));
lean_closure_set(v___x_1085_, 1, lean_box(0));
lean_closure_set(v___x_1085_, 2, v_inst_1083_);
lean_closure_set(v___x_1085_, 3, v_inst_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord___redArg(lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v_term_1090_; lean_object* v_desc_1091_; lean_object* v_term_1092_; lean_object* v_desc_1093_; uint8_t v___x_1094_; 
v_term_1090_ = lean_ctor_get(v_x_1088_, 0);
v_desc_1091_ = lean_ctor_get(v_x_1088_, 1);
v_term_1092_ = lean_ctor_get(v_x_1089_, 0);
v_desc_1093_ = lean_ctor_get(v_x_1089_, 1);
v___x_1094_ = l_Array_compareLex___redArg(v_inst_1086_, v_term_1090_, v_term_1092_);
if (v___x_1094_ == 1)
{
uint8_t v___x_1095_; 
v___x_1095_ = l_Array_compareLex___redArg(v_inst_1087_, v_desc_1091_, v_desc_1093_);
if (v___x_1095_ == 1)
{
return v___x_1095_;
}
else
{
return v___x_1095_;
}
}
else
{
lean_dec_ref(v_inst_1087_);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___redArg___boxed(lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_res_1100_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1096_, v_inst_1097_, v_x_1098_, v_x_1099_);
lean_dec_ref(v_x_1099_);
lean_dec_ref(v_x_1098_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord(lean_object* v_00_u03b1_1102_, lean_object* v_00_u03b2_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
uint8_t v___x_1108_; 
v___x_1108_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1104_, v_inst_1105_, v_x_1106_, v_x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___boxed(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_inst_1111_, lean_object* v_inst_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
uint8_t v_res_1115_; lean_object* v_r_1116_; 
v_res_1115_ = l_Lean_Doc_instOrdDescItem_ord(v_00_u03b1_1109_, v_00_u03b2_1110_, v_inst_1111_, v_inst_1112_, v_x_1113_, v_x_1114_);
lean_dec_ref(v_x_1114_);
lean_dec_ref(v_x_1113_);
v_r_1116_ = lean_box(v_res_1115_);
return v_r_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem___redArg(lean_object* v_inst_1117_, lean_object* v_inst_1118_){
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
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem(lean_object* v_00_u03b1_1120_, lean_object* v_00_u03b2_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1124_, 0, lean_box(0));
lean_closure_set(v___x_1124_, 1, lean_box(0));
lean_closure_set(v___x_1124_, 2, v_inst_1122_);
lean_closure_set(v___x_1124_, 3, v_inst_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default(lean_object* v_00_u03b1_1127_, lean_object* v_00_u03b2_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = ((lean_object*)(l_Lean_Doc_instInhabitedDescItem_default___closed__0));
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedDescItem___closed__0(void){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Doc_instInhabitedDescItem_default(lean_box(0), lean_box(0));
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem(lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem___closed__0, &l_Lean_Doc_instInhabitedDescItem___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem___closed__0);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg(lean_object* v_x_1134_){
_start:
{
switch(lean_obj_tag(v_x_1134_))
{
case 0:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_unsigned_to_nat(0u);
return v___x_1135_;
}
case 1:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_unsigned_to_nat(1u);
return v___x_1136_;
}
case 2:
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_unsigned_to_nat(2u);
return v___x_1137_;
}
case 3:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_unsigned_to_nat(3u);
return v___x_1138_;
}
case 4:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_unsigned_to_nat(4u);
return v___x_1139_;
}
case 5:
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_unsigned_to_nat(5u);
return v___x_1140_;
}
case 6:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_unsigned_to_nat(6u);
return v___x_1141_;
}
default: 
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_unsigned_to_nat(7u);
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg___boxed(lean_object* v_x_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1143_);
lean_dec_ref(v_x_1143_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx(lean_object* v_i_1145_, lean_object* v_b_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___boxed(lean_object* v_i_1149_, lean_object* v_b_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Doc_Block_ctorIdx(v_i_1149_, v_b_1150_, v_x_1151_);
lean_dec_ref(v_x_1151_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___redArg(lean_object* v_t_1153_, lean_object* v_k_1154_){
_start:
{
switch(lean_obj_tag(v_t_1153_))
{
case 3:
{
lean_object* v_start_1155_; lean_object* v_items_1156_; lean_object* v___x_1157_; 
v_start_1155_ = lean_ctor_get(v_t_1153_, 0);
lean_inc(v_start_1155_);
v_items_1156_ = lean_ctor_get(v_t_1153_, 1);
lean_inc_ref(v_items_1156_);
lean_dec_ref_known(v_t_1153_, 2);
v___x_1157_ = lean_apply_2(v_k_1154_, v_start_1155_, v_items_1156_);
return v___x_1157_;
}
case 7:
{
lean_object* v_container_1158_; lean_object* v_content_1159_; lean_object* v___x_1160_; 
v_container_1158_ = lean_ctor_get(v_t_1153_, 0);
lean_inc(v_container_1158_);
v_content_1159_ = lean_ctor_get(v_t_1153_, 1);
lean_inc_ref(v_content_1159_);
lean_dec_ref_known(v_t_1153_, 2);
v___x_1160_ = lean_apply_2(v_k_1154_, v_container_1158_, v_content_1159_);
return v___x_1160_;
}
default: 
{
lean_object* v_contents_1161_; lean_object* v___x_1162_; 
v_contents_1161_ = lean_ctor_get(v_t_1153_, 0);
lean_inc_ref(v_contents_1161_);
lean_dec_ref(v_t_1153_);
v___x_1162_ = lean_apply_1(v_k_1154_, v_contents_1161_);
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim(lean_object* v_i_1163_, lean_object* v_b_1164_, lean_object* v_motive__1_1165_, lean_object* v_ctorIdx_1166_, lean_object* v_t_1167_, lean_object* v_h_1168_, lean_object* v_k_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1167_, v_k_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___boxed(lean_object* v_i_1171_, lean_object* v_b_1172_, lean_object* v_motive__1_1173_, lean_object* v_ctorIdx_1174_, lean_object* v_t_1175_, lean_object* v_h_1176_, lean_object* v_k_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Doc_Block_ctorElim(v_i_1171_, v_b_1172_, v_motive__1_1173_, v_ctorIdx_1174_, v_t_1175_, v_h_1176_, v_k_1177_);
lean_dec(v_ctorIdx_1174_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim___redArg(lean_object* v_t_1179_, lean_object* v_para_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1179_, v_para_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim(lean_object* v_i_1182_, lean_object* v_b_1183_, lean_object* v_motive__1_1184_, lean_object* v_t_1185_, lean_object* v_h_1186_, lean_object* v_para_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1185_, v_para_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim___redArg(lean_object* v_t_1189_, lean_object* v_code_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1189_, v_code_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim(lean_object* v_i_1192_, lean_object* v_b_1193_, lean_object* v_motive__1_1194_, lean_object* v_t_1195_, lean_object* v_h_1196_, lean_object* v_code_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1195_, v_code_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim___redArg(lean_object* v_t_1199_, lean_object* v_ul_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1199_, v_ul_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim(lean_object* v_i_1202_, lean_object* v_b_1203_, lean_object* v_motive__1_1204_, lean_object* v_t_1205_, lean_object* v_h_1206_, lean_object* v_ul_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1205_, v_ul_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim___redArg(lean_object* v_t_1209_, lean_object* v_ol_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1209_, v_ol_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim(lean_object* v_i_1212_, lean_object* v_b_1213_, lean_object* v_motive__1_1214_, lean_object* v_t_1215_, lean_object* v_h_1216_, lean_object* v_ol_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1215_, v_ol_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim___redArg(lean_object* v_t_1219_, lean_object* v_dl_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1219_, v_dl_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim(lean_object* v_i_1222_, lean_object* v_b_1223_, lean_object* v_motive__1_1224_, lean_object* v_t_1225_, lean_object* v_h_1226_, lean_object* v_dl_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1225_, v_dl_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim___redArg(lean_object* v_t_1229_, lean_object* v_blockquote_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1229_, v_blockquote_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim(lean_object* v_i_1232_, lean_object* v_b_1233_, lean_object* v_motive__1_1234_, lean_object* v_t_1235_, lean_object* v_h_1236_, lean_object* v_blockquote_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1235_, v_blockquote_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim___redArg(lean_object* v_t_1239_, lean_object* v_concat_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1239_, v_concat_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim(lean_object* v_i_1242_, lean_object* v_b_1243_, lean_object* v_motive__1_1244_, lean_object* v_t_1245_, lean_object* v_h_1246_, lean_object* v_concat_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1245_, v_concat_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim___redArg(lean_object* v_t_1249_, lean_object* v_other_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1249_, v_other_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim(lean_object* v_i_1252_, lean_object* v_b_1253_, lean_object* v_motive__1_1254_, lean_object* v_t_1255_, lean_object* v_h_1256_, lean_object* v_other_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1255_, v_other_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___redArg___boxed(lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
uint8_t v_res_1263_; lean_object* v_r_1264_; 
v_res_1263_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1259_, v_inst_1260_, v_x_1261_, v_x_1262_);
v_r_1264_ = lean_box(v_res_1263_);
return v_r_1264_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq___redArg(lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v_localinst_1269_; lean_object* v_a_1271_; lean_object* v_b_1272_; 
lean_inc_ref(v_inst_1266_);
lean_inc_ref(v_inst_1265_);
v_localinst_1269_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1269_, 0, v_inst_1265_);
lean_closure_set(v_localinst_1269_, 1, v_inst_1266_);
switch(lean_obj_tag(v_x_1267_))
{
case 0:
{
lean_dec_ref(v_localinst_1269_);
lean_dec_ref(v_inst_1266_);
if (lean_obj_tag(v_x_1268_) == 0)
{
lean_object* v_contents_1277_; lean_object* v_contents_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_contents_1277_ = lean_ctor_get(v_x_1267_, 0);
lean_inc_ref(v_contents_1277_);
lean_dec_ref_known(v_x_1267_, 1);
v_contents_1278_ = lean_ctor_get(v_x_1268_, 0);
lean_inc_ref(v_contents_1278_);
lean_dec_ref_known(v_x_1268_, 1);
v___x_1279_ = lean_array_get_size(v_contents_1277_);
v___x_1280_ = lean_array_get_size(v_contents_1278_);
v___x_1281_ = lean_nat_dec_eq(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_dec_ref(v_contents_1278_);
lean_dec_ref(v_contents_1277_);
lean_dec_ref(v_inst_1265_);
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1282_, 0, lean_box(0));
lean_closure_set(v___x_1282_, 1, v_inst_1265_);
v___x_1283_ = l_Array_isEqvAux___redArg(v_contents_1277_, v_contents_1278_, v___x_1282_, v___x_1279_);
lean_dec_ref(v_contents_1278_);
lean_dec_ref(v_contents_1277_);
return v___x_1283_;
}
}
else
{
uint8_t v___x_1284_; 
lean_dec_ref_known(v_x_1267_, 1);
lean_dec_ref(v_x_1268_);
lean_dec_ref(v_inst_1265_);
v___x_1284_ = 0;
return v___x_1284_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1269_);
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
if (lean_obj_tag(v_x_1268_) == 1)
{
lean_object* v_content_1285_; lean_object* v_content_1286_; uint8_t v___x_1287_; 
v_content_1285_ = lean_ctor_get(v_x_1267_, 0);
lean_inc_ref(v_content_1285_);
lean_dec_ref_known(v_x_1267_, 1);
v_content_1286_ = lean_ctor_get(v_x_1268_, 0);
lean_inc_ref(v_content_1286_);
lean_dec_ref_known(v_x_1268_, 1);
v___x_1287_ = lean_string_dec_eq(v_content_1285_, v_content_1286_);
lean_dec_ref(v_content_1286_);
lean_dec_ref(v_content_1285_);
return v___x_1287_;
}
else
{
uint8_t v___x_1288_; 
lean_dec_ref_known(v_x_1267_, 1);
lean_dec_ref(v_x_1268_);
v___x_1288_ = 0;
return v___x_1288_;
}
}
case 2:
{
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
if (lean_obj_tag(v_x_1268_) == 2)
{
lean_object* v_items_1289_; lean_object* v_items_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_items_1289_ = lean_ctor_get(v_x_1267_, 0);
lean_inc_ref(v_items_1289_);
lean_dec_ref_known(v_x_1267_, 1);
v_items_1290_ = lean_ctor_get(v_x_1268_, 0);
lean_inc_ref(v_items_1290_);
lean_dec_ref_known(v_x_1268_, 1);
v___x_1291_ = lean_array_get_size(v_items_1289_);
v___x_1292_ = lean_array_get_size(v_items_1290_);
v___x_1293_ = lean_nat_dec_eq(v___x_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v_items_1290_);
lean_dec_ref(v_items_1289_);
lean_dec_ref(v_localinst_1269_);
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1294_, 0, lean_box(0));
lean_closure_set(v___x_1294_, 1, v_localinst_1269_);
v___x_1295_ = l_Array_isEqvAux___redArg(v_items_1289_, v_items_1290_, v___x_1294_, v___x_1291_);
lean_dec_ref(v_items_1290_);
lean_dec_ref(v_items_1289_);
return v___x_1295_;
}
}
else
{
uint8_t v___x_1296_; 
lean_dec_ref_known(v_x_1267_, 1);
lean_dec_ref(v_localinst_1269_);
lean_dec_ref(v_x_1268_);
v___x_1296_ = 0;
return v___x_1296_;
}
}
case 3:
{
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
if (lean_obj_tag(v_x_1268_) == 3)
{
lean_object* v_start_1297_; lean_object* v_items_1298_; lean_object* v_start_1299_; lean_object* v_items_1300_; uint8_t v___x_1301_; 
v_start_1297_ = lean_ctor_get(v_x_1267_, 0);
lean_inc(v_start_1297_);
v_items_1298_ = lean_ctor_get(v_x_1267_, 1);
lean_inc_ref(v_items_1298_);
lean_dec_ref_known(v_x_1267_, 2);
v_start_1299_ = lean_ctor_get(v_x_1268_, 0);
lean_inc(v_start_1299_);
v_items_1300_ = lean_ctor_get(v_x_1268_, 1);
lean_inc_ref(v_items_1300_);
lean_dec_ref_known(v_x_1268_, 2);
v___x_1301_ = lean_int_dec_eq(v_start_1297_, v_start_1299_);
lean_dec(v_start_1299_);
lean_dec(v_start_1297_);
if (v___x_1301_ == 0)
{
lean_dec_ref(v_items_1300_);
lean_dec_ref(v_items_1298_);
lean_dec_ref(v_localinst_1269_);
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1302_ = lean_array_get_size(v_items_1298_);
v___x_1303_ = lean_array_get_size(v_items_1300_);
v___x_1304_ = lean_nat_dec_eq(v___x_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_dec_ref(v_items_1300_);
lean_dec_ref(v_items_1298_);
lean_dec_ref(v_localinst_1269_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1305_, 0, lean_box(0));
lean_closure_set(v___x_1305_, 1, v_localinst_1269_);
v___x_1306_ = l_Array_isEqvAux___redArg(v_items_1298_, v_items_1300_, v___x_1305_, v___x_1302_);
lean_dec_ref(v_items_1300_);
lean_dec_ref(v_items_1298_);
return v___x_1306_;
}
}
}
else
{
uint8_t v___x_1307_; 
lean_dec_ref_known(v_x_1267_, 2);
lean_dec_ref(v_localinst_1269_);
lean_dec_ref(v_x_1268_);
v___x_1307_ = 0;
return v___x_1307_;
}
}
case 4:
{
lean_dec_ref(v_inst_1266_);
if (lean_obj_tag(v_x_1268_) == 4)
{
lean_object* v_items_1308_; lean_object* v_items_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_items_1308_ = lean_ctor_get(v_x_1267_, 0);
lean_inc_ref(v_items_1308_);
lean_dec_ref_known(v_x_1267_, 1);
v_items_1309_ = lean_ctor_get(v_x_1268_, 0);
lean_inc_ref(v_items_1309_);
lean_dec_ref_known(v_x_1268_, 1);
v___x_1310_ = lean_array_get_size(v_items_1308_);
v___x_1311_ = lean_array_get_size(v_items_1309_);
v___x_1312_ = lean_nat_dec_eq(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_dec_ref(v_items_1309_);
lean_dec_ref(v_items_1308_);
lean_dec_ref(v_localinst_1269_);
lean_dec_ref(v_inst_1265_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1313_, 0, lean_box(0));
lean_closure_set(v___x_1313_, 1, v_inst_1265_);
v___x_1314_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1314_, 0, lean_box(0));
lean_closure_set(v___x_1314_, 1, lean_box(0));
lean_closure_set(v___x_1314_, 2, v___x_1313_);
lean_closure_set(v___x_1314_, 3, v_localinst_1269_);
v___x_1315_ = l_Array_isEqvAux___redArg(v_items_1308_, v_items_1309_, v___x_1314_, v___x_1310_);
lean_dec_ref(v_items_1309_);
lean_dec_ref(v_items_1308_);
return v___x_1315_;
}
}
else
{
uint8_t v___x_1316_; 
lean_dec_ref_known(v_x_1267_, 1);
lean_dec_ref(v_localinst_1269_);
lean_dec_ref(v_x_1268_);
lean_dec_ref(v_inst_1265_);
v___x_1316_ = 0;
return v___x_1316_;
}
}
case 5:
{
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
if (lean_obj_tag(v_x_1268_) == 5)
{
lean_object* v_items_1317_; lean_object* v_items_1318_; 
v_items_1317_ = lean_ctor_get(v_x_1267_, 0);
lean_inc_ref(v_items_1317_);
lean_dec_ref_known(v_x_1267_, 1);
v_items_1318_ = lean_ctor_get(v_x_1268_, 0);
lean_inc_ref(v_items_1318_);
lean_dec_ref_known(v_x_1268_, 1);
v_a_1271_ = v_items_1317_;
v_b_1272_ = v_items_1318_;
goto v___jp_1270_;
}
else
{
uint8_t v___x_1319_; 
lean_dec_ref_known(v_x_1267_, 1);
lean_dec_ref(v_localinst_1269_);
lean_dec_ref(v_x_1268_);
v___x_1319_ = 0;
return v___x_1319_;
}
}
case 6:
{
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
if (lean_obj_tag(v_x_1268_) == 6)
{
lean_object* v_content_1320_; lean_object* v_content_1321_; 
v_content_1320_ = lean_ctor_get(v_x_1267_, 0);
lean_inc_ref(v_content_1320_);
lean_dec_ref_known(v_x_1267_, 1);
v_content_1321_ = lean_ctor_get(v_x_1268_, 0);
lean_inc_ref(v_content_1321_);
lean_dec_ref_known(v_x_1268_, 1);
v_a_1271_ = v_content_1320_;
v_b_1272_ = v_content_1321_;
goto v___jp_1270_;
}
else
{
uint8_t v___x_1322_; 
lean_dec_ref_known(v_x_1267_, 1);
lean_dec_ref(v_localinst_1269_);
lean_dec_ref(v_x_1268_);
v___x_1322_ = 0;
return v___x_1322_;
}
}
default: 
{
lean_dec_ref(v_inst_1265_);
if (lean_obj_tag(v_x_1268_) == 7)
{
lean_object* v_container_1323_; lean_object* v_content_1324_; lean_object* v_container_1325_; lean_object* v_content_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v_container_1323_ = lean_ctor_get(v_x_1267_, 0);
lean_inc(v_container_1323_);
v_content_1324_ = lean_ctor_get(v_x_1267_, 1);
lean_inc_ref(v_content_1324_);
lean_dec_ref_known(v_x_1267_, 2);
v_container_1325_ = lean_ctor_get(v_x_1268_, 0);
lean_inc(v_container_1325_);
v_content_1326_ = lean_ctor_get(v_x_1268_, 1);
lean_inc_ref(v_content_1326_);
lean_dec_ref_known(v_x_1268_, 2);
v___x_1327_ = lean_apply_2(v_inst_1266_, v_container_1323_, v_container_1325_);
v___x_1328_ = lean_unbox(v___x_1327_);
if (v___x_1328_ == 0)
{
uint8_t v___x_1329_; 
lean_dec_ref(v_content_1326_);
lean_dec_ref(v_content_1324_);
lean_dec_ref(v_localinst_1269_);
v___x_1329_ = lean_unbox(v___x_1327_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1330_ = lean_array_get_size(v_content_1324_);
v___x_1331_ = lean_array_get_size(v_content_1326_);
v___x_1332_ = lean_nat_dec_eq(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_dec_ref(v_content_1326_);
lean_dec_ref(v_content_1324_);
lean_dec_ref(v_localinst_1269_);
return v___x_1332_;
}
else
{
uint8_t v___x_1333_; 
v___x_1333_ = l_Array_isEqvAux___redArg(v_content_1324_, v_content_1326_, v_localinst_1269_, v___x_1330_);
lean_dec_ref(v_content_1326_);
lean_dec_ref(v_content_1324_);
return v___x_1333_;
}
}
}
else
{
uint8_t v___x_1334_; 
lean_dec_ref_known(v_x_1267_, 2);
lean_dec_ref(v_localinst_1269_);
lean_dec_ref(v_x_1268_);
lean_dec_ref(v_inst_1266_);
v___x_1334_ = 0;
return v___x_1334_;
}
}
}
v___jp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1273_ = lean_array_get_size(v_a_1271_);
v___x_1274_ = lean_array_get_size(v_b_1272_);
v___x_1275_ = lean_nat_dec_eq(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec_ref(v_b_1272_);
lean_dec_ref(v_a_1271_);
lean_dec_ref(v_localinst_1269_);
return v___x_1275_;
}
else
{
uint8_t v___x_1276_; 
v___x_1276_ = l_Array_isEqvAux___redArg(v_a_1271_, v_b_1272_, v_localinst_1269_, v___x_1273_);
lean_dec_ref(v_b_1272_);
lean_dec_ref(v_a_1271_);
return v___x_1276_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq(lean_object* v_i_1335_, lean_object* v_b_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1337_, v_inst_1338_, v_x_1339_, v_x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___boxed(lean_object* v_i_1342_, lean_object* v_b_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_){
_start:
{
uint8_t v_res_1348_; lean_object* v_r_1349_; 
v_res_1348_ = l_Lean_Doc_instBEqBlock_beq(v_i_1342_, v_b_1343_, v_inst_1344_, v_inst_1345_, v_x_1346_, v_x_1347_);
v_r_1349_ = lean_box(v_res_1348_);
return v_r_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock___redArg(lean_object* v_inst_1350_, lean_object* v_inst_1351_){
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
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock(lean_object* v_i_1353_, lean_object* v_b_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1357_, 0, lean_box(0));
lean_closure_set(v___x_1357_, 1, lean_box(0));
lean_closure_set(v___x_1357_, 2, v_inst_1355_);
lean_closure_set(v___x_1357_, 3, v_inst_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___redArg___boxed(lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_){
_start:
{
uint8_t v_res_1362_; lean_object* v_r_1363_; 
v_res_1362_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1358_, v_inst_1359_, v_x_1360_, v_x_1361_);
v_r_1363_ = lean_box(v_res_1362_);
return v_r_1363_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord___redArg(lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
lean_object* v_localinst_1368_; lean_object* v_a_1370_; lean_object* v_b_1371_; 
lean_inc_ref(v_inst_1365_);
lean_inc_ref(v_inst_1364_);
v_localinst_1368_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1368_, 0, v_inst_1364_);
lean_closure_set(v_localinst_1368_, 1, v_inst_1365_);
switch(lean_obj_tag(v_x_1366_))
{
case 0:
{
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_inst_1365_);
switch(lean_obj_tag(v_x_1367_))
{
case 0:
{
lean_object* v_contents_1373_; lean_object* v_contents_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v_contents_1373_ = lean_ctor_get(v_x_1366_, 0);
lean_inc_ref(v_contents_1373_);
lean_dec_ref_known(v_x_1366_, 1);
v_contents_1374_ = lean_ctor_get(v_x_1367_, 0);
lean_inc_ref(v_contents_1374_);
lean_dec_ref_known(v_x_1367_, 1);
v___x_1375_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1375_, 0, lean_box(0));
lean_closure_set(v___x_1375_, 1, v_inst_1364_);
v___x_1376_ = l_Array_compareLex___redArg(v___x_1375_, v_contents_1373_, v_contents_1374_);
lean_dec_ref(v_contents_1374_);
lean_dec_ref(v_contents_1373_);
if (v___x_1376_ == 1)
{
return v___x_1376_;
}
else
{
return v___x_1376_;
}
}
case 1:
{
uint8_t v___x_1377_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_inst_1364_);
v___x_1377_ = 0;
return v___x_1377_;
}
case 2:
{
uint8_t v___x_1378_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_inst_1364_);
v___x_1378_ = 0;
return v___x_1378_;
}
case 3:
{
uint8_t v___x_1379_; 
lean_dec_ref_known(v_x_1367_, 2);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_inst_1364_);
v___x_1379_ = 0;
return v___x_1379_;
}
case 4:
{
uint8_t v___x_1380_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_inst_1364_);
v___x_1380_ = 0;
return v___x_1380_;
}
case 5:
{
uint8_t v___x_1381_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_inst_1364_);
v___x_1381_ = 0;
return v___x_1381_;
}
case 6:
{
uint8_t v___x_1382_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_inst_1364_);
v___x_1382_ = 0;
return v___x_1382_;
}
default: 
{
uint8_t v___x_1383_; 
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_x_1367_);
lean_dec_ref(v_inst_1364_);
v___x_1383_ = 0;
return v___x_1383_;
}
}
}
case 1:
{
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_inst_1365_);
lean_dec_ref(v_inst_1364_);
switch(lean_obj_tag(v_x_1367_))
{
case 0:
{
uint8_t v___x_1384_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
v___x_1384_ = 2;
return v___x_1384_;
}
case 1:
{
lean_object* v_content_1385_; lean_object* v_content_1386_; uint8_t v___x_1387_; 
v_content_1385_ = lean_ctor_get(v_x_1366_, 0);
lean_inc_ref(v_content_1385_);
lean_dec_ref_known(v_x_1366_, 1);
v_content_1386_ = lean_ctor_get(v_x_1367_, 0);
lean_inc_ref(v_content_1386_);
lean_dec_ref_known(v_x_1367_, 1);
v___x_1387_ = lean_string_compare(v_content_1385_, v_content_1386_);
lean_dec_ref(v_content_1386_);
lean_dec_ref(v_content_1385_);
if (v___x_1387_ == 1)
{
return v___x_1387_;
}
else
{
return v___x_1387_;
}
}
case 2:
{
uint8_t v___x_1388_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
v___x_1388_ = 0;
return v___x_1388_;
}
case 3:
{
uint8_t v___x_1389_; 
lean_dec_ref_known(v_x_1367_, 2);
lean_dec_ref_known(v_x_1366_, 1);
v___x_1389_ = 0;
return v___x_1389_;
}
case 4:
{
uint8_t v___x_1390_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
v___x_1390_ = 0;
return v___x_1390_;
}
case 5:
{
uint8_t v___x_1391_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
v___x_1391_ = 0;
return v___x_1391_;
}
case 6:
{
uint8_t v___x_1392_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
v___x_1392_ = 0;
return v___x_1392_;
}
default: 
{
uint8_t v___x_1393_; 
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_x_1367_);
v___x_1393_ = 0;
return v___x_1393_;
}
}
}
case 2:
{
lean_dec_ref(v_inst_1365_);
lean_dec_ref(v_inst_1364_);
switch(lean_obj_tag(v_x_1367_))
{
case 0:
{
uint8_t v___x_1394_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1394_ = 2;
return v___x_1394_;
}
case 1:
{
uint8_t v___x_1395_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1395_ = 2;
return v___x_1395_;
}
case 2:
{
lean_object* v_items_1396_; lean_object* v_items_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_items_1396_ = lean_ctor_get(v_x_1366_, 0);
lean_inc_ref(v_items_1396_);
lean_dec_ref_known(v_x_1366_, 1);
v_items_1397_ = lean_ctor_get(v_x_1367_, 0);
lean_inc_ref(v_items_1397_);
lean_dec_ref_known(v_x_1367_, 1);
v___x_1398_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1398_, 0, lean_box(0));
lean_closure_set(v___x_1398_, 1, v_localinst_1368_);
v___x_1399_ = l_Array_compareLex___redArg(v___x_1398_, v_items_1396_, v_items_1397_);
lean_dec_ref(v_items_1397_);
lean_dec_ref(v_items_1396_);
if (v___x_1399_ == 1)
{
return v___x_1399_;
}
else
{
return v___x_1399_;
}
}
case 3:
{
uint8_t v___x_1400_; 
lean_dec_ref_known(v_x_1367_, 2);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1400_ = 0;
return v___x_1400_;
}
case 4:
{
uint8_t v___x_1401_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1401_ = 0;
return v___x_1401_;
}
case 5:
{
uint8_t v___x_1402_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1402_ = 0;
return v___x_1402_;
}
case 6:
{
uint8_t v___x_1403_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1403_ = 0;
return v___x_1403_;
}
default: 
{
uint8_t v___x_1404_; 
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_x_1367_);
v___x_1404_ = 0;
return v___x_1404_;
}
}
}
case 3:
{
lean_dec_ref(v_inst_1365_);
lean_dec_ref(v_inst_1364_);
switch(lean_obj_tag(v_x_1367_))
{
case 0:
{
uint8_t v___x_1405_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 2);
lean_dec_ref(v_localinst_1368_);
v___x_1405_ = 2;
return v___x_1405_;
}
case 1:
{
uint8_t v___x_1406_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 2);
lean_dec_ref(v_localinst_1368_);
v___x_1406_ = 2;
return v___x_1406_;
}
case 2:
{
uint8_t v___x_1407_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 2);
lean_dec_ref(v_localinst_1368_);
v___x_1407_ = 2;
return v___x_1407_;
}
case 3:
{
lean_object* v_start_1408_; lean_object* v_items_1409_; lean_object* v_start_1410_; lean_object* v_items_1411_; uint8_t v___x_1412_; 
v_start_1408_ = lean_ctor_get(v_x_1366_, 0);
lean_inc(v_start_1408_);
v_items_1409_ = lean_ctor_get(v_x_1366_, 1);
lean_inc_ref(v_items_1409_);
lean_dec_ref_known(v_x_1366_, 2);
v_start_1410_ = lean_ctor_get(v_x_1367_, 0);
lean_inc(v_start_1410_);
v_items_1411_ = lean_ctor_get(v_x_1367_, 1);
lean_inc_ref(v_items_1411_);
lean_dec_ref_known(v_x_1367_, 2);
v___x_1412_ = lean_int_dec_lt(v_start_1408_, v_start_1410_);
if (v___x_1412_ == 0)
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_int_dec_eq(v_start_1408_, v_start_1410_);
lean_dec(v_start_1410_);
lean_dec(v_start_1408_);
if (v___x_1413_ == 0)
{
uint8_t v___x_1414_; 
lean_dec_ref(v_items_1411_);
lean_dec_ref(v_items_1409_);
lean_dec_ref(v_localinst_1368_);
v___x_1414_ = 2;
return v___x_1414_;
}
else
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1415_, 0, lean_box(0));
lean_closure_set(v___x_1415_, 1, v_localinst_1368_);
v___x_1416_ = l_Array_compareLex___redArg(v___x_1415_, v_items_1409_, v_items_1411_);
lean_dec_ref(v_items_1411_);
lean_dec_ref(v_items_1409_);
if (v___x_1416_ == 1)
{
return v___x_1416_;
}
else
{
return v___x_1416_;
}
}
}
else
{
uint8_t v___x_1417_; 
lean_dec_ref(v_items_1411_);
lean_dec(v_start_1410_);
lean_dec_ref(v_items_1409_);
lean_dec(v_start_1408_);
lean_dec_ref(v_localinst_1368_);
v___x_1417_ = 0;
return v___x_1417_;
}
}
case 4:
{
uint8_t v___x_1418_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 2);
lean_dec_ref(v_localinst_1368_);
v___x_1418_ = 0;
return v___x_1418_;
}
case 5:
{
uint8_t v___x_1419_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 2);
lean_dec_ref(v_localinst_1368_);
v___x_1419_ = 0;
return v___x_1419_;
}
case 6:
{
uint8_t v___x_1420_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 2);
lean_dec_ref(v_localinst_1368_);
v___x_1420_ = 0;
return v___x_1420_;
}
default: 
{
uint8_t v___x_1421_; 
lean_dec_ref_known(v_x_1366_, 2);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_x_1367_);
v___x_1421_ = 0;
return v___x_1421_;
}
}
}
case 4:
{
lean_dec_ref(v_inst_1365_);
switch(lean_obj_tag(v_x_1367_))
{
case 0:
{
uint8_t v___x_1422_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_inst_1364_);
v___x_1422_ = 2;
return v___x_1422_;
}
case 1:
{
uint8_t v___x_1423_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_inst_1364_);
v___x_1423_ = 2;
return v___x_1423_;
}
case 2:
{
uint8_t v___x_1424_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_inst_1364_);
v___x_1424_ = 2;
return v___x_1424_;
}
case 3:
{
uint8_t v___x_1425_; 
lean_dec_ref_known(v_x_1367_, 2);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_inst_1364_);
v___x_1425_ = 2;
return v___x_1425_;
}
case 4:
{
lean_object* v_items_1426_; lean_object* v_items_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v_items_1426_ = lean_ctor_get(v_x_1366_, 0);
lean_inc_ref(v_items_1426_);
lean_dec_ref_known(v_x_1366_, 1);
v_items_1427_ = lean_ctor_get(v_x_1367_, 0);
lean_inc_ref(v_items_1427_);
lean_dec_ref_known(v_x_1367_, 1);
v___x_1428_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1428_, 0, lean_box(0));
lean_closure_set(v___x_1428_, 1, v_inst_1364_);
v___x_1429_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1429_, 0, lean_box(0));
lean_closure_set(v___x_1429_, 1, lean_box(0));
lean_closure_set(v___x_1429_, 2, v___x_1428_);
lean_closure_set(v___x_1429_, 3, v_localinst_1368_);
v___x_1430_ = l_Array_compareLex___redArg(v___x_1429_, v_items_1426_, v_items_1427_);
lean_dec_ref(v_items_1427_);
lean_dec_ref(v_items_1426_);
if (v___x_1430_ == 1)
{
return v___x_1430_;
}
else
{
return v___x_1430_;
}
}
case 5:
{
uint8_t v___x_1431_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_inst_1364_);
v___x_1431_ = 0;
return v___x_1431_;
}
case 6:
{
uint8_t v___x_1432_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_inst_1364_);
v___x_1432_ = 0;
return v___x_1432_;
}
default: 
{
uint8_t v___x_1433_; 
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_x_1367_);
lean_dec_ref(v_inst_1364_);
v___x_1433_ = 0;
return v___x_1433_;
}
}
}
case 5:
{
lean_dec_ref(v_inst_1365_);
lean_dec_ref(v_inst_1364_);
switch(lean_obj_tag(v_x_1367_))
{
case 0:
{
uint8_t v___x_1434_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1434_ = 2;
return v___x_1434_;
}
case 1:
{
uint8_t v___x_1435_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1435_ = 2;
return v___x_1435_;
}
case 2:
{
uint8_t v___x_1436_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1436_ = 2;
return v___x_1436_;
}
case 3:
{
uint8_t v___x_1437_; 
lean_dec_ref_known(v_x_1367_, 2);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1437_ = 2;
return v___x_1437_;
}
case 4:
{
uint8_t v___x_1438_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1438_ = 2;
return v___x_1438_;
}
case 5:
{
lean_object* v_items_1439_; lean_object* v_items_1440_; 
v_items_1439_ = lean_ctor_get(v_x_1366_, 0);
lean_inc_ref(v_items_1439_);
lean_dec_ref_known(v_x_1366_, 1);
v_items_1440_ = lean_ctor_get(v_x_1367_, 0);
lean_inc_ref(v_items_1440_);
lean_dec_ref_known(v_x_1367_, 1);
v_a_1370_ = v_items_1439_;
v_b_1371_ = v_items_1440_;
goto v___jp_1369_;
}
case 6:
{
uint8_t v___x_1441_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1441_ = 0;
return v___x_1441_;
}
default: 
{
uint8_t v___x_1442_; 
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_x_1367_);
v___x_1442_ = 0;
return v___x_1442_;
}
}
}
case 6:
{
lean_dec_ref(v_inst_1365_);
lean_dec_ref(v_inst_1364_);
switch(lean_obj_tag(v_x_1367_))
{
case 0:
{
uint8_t v___x_1443_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1443_ = 2;
return v___x_1443_;
}
case 1:
{
uint8_t v___x_1444_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1444_ = 2;
return v___x_1444_;
}
case 2:
{
uint8_t v___x_1445_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1445_ = 2;
return v___x_1445_;
}
case 3:
{
uint8_t v___x_1446_; 
lean_dec_ref_known(v_x_1367_, 2);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1446_ = 2;
return v___x_1446_;
}
case 4:
{
uint8_t v___x_1447_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1447_ = 2;
return v___x_1447_;
}
case 5:
{
uint8_t v___x_1448_; 
lean_dec_ref_known(v_x_1367_, 1);
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
v___x_1448_ = 2;
return v___x_1448_;
}
case 6:
{
lean_object* v_content_1449_; lean_object* v_content_1450_; 
v_content_1449_ = lean_ctor_get(v_x_1366_, 0);
lean_inc_ref(v_content_1449_);
lean_dec_ref_known(v_x_1366_, 1);
v_content_1450_ = lean_ctor_get(v_x_1367_, 0);
lean_inc_ref(v_content_1450_);
lean_dec_ref_known(v_x_1367_, 1);
v_a_1370_ = v_content_1449_;
v_b_1371_ = v_content_1450_;
goto v___jp_1369_;
}
default: 
{
uint8_t v___x_1451_; 
lean_dec_ref_known(v_x_1366_, 1);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_x_1367_);
v___x_1451_ = 0;
return v___x_1451_;
}
}
}
default: 
{
lean_dec_ref(v_inst_1364_);
if (lean_obj_tag(v_x_1367_) == 7)
{
lean_object* v_container_1452_; lean_object* v_content_1453_; lean_object* v_container_1454_; lean_object* v_content_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_container_1452_ = lean_ctor_get(v_x_1366_, 0);
lean_inc(v_container_1452_);
v_content_1453_ = lean_ctor_get(v_x_1366_, 1);
lean_inc_ref(v_content_1453_);
lean_dec_ref_known(v_x_1366_, 2);
v_container_1454_ = lean_ctor_get(v_x_1367_, 0);
lean_inc(v_container_1454_);
v_content_1455_ = lean_ctor_get(v_x_1367_, 1);
lean_inc_ref(v_content_1455_);
lean_dec_ref_known(v_x_1367_, 2);
v___x_1456_ = lean_apply_2(v_inst_1365_, v_container_1452_, v_container_1454_);
v___x_1457_ = lean_unbox(v___x_1456_);
if (v___x_1457_ == 1)
{
uint8_t v___x_1458_; 
v___x_1458_ = l_Array_compareLex___redArg(v_localinst_1368_, v_content_1453_, v_content_1455_);
lean_dec_ref(v_content_1455_);
lean_dec_ref(v_content_1453_);
if (v___x_1458_ == 1)
{
return v___x_1458_;
}
else
{
return v___x_1458_;
}
}
else
{
uint8_t v___x_1459_; 
lean_dec_ref(v_content_1455_);
lean_dec_ref(v_content_1453_);
lean_dec_ref(v_localinst_1368_);
v___x_1459_ = lean_unbox(v___x_1456_);
return v___x_1459_;
}
}
else
{
uint8_t v___x_1460_; 
lean_dec_ref_known(v_x_1366_, 2);
lean_dec_ref(v_localinst_1368_);
lean_dec_ref(v_x_1367_);
lean_dec_ref(v_inst_1365_);
v___x_1460_ = 2;
return v___x_1460_;
}
}
}
v___jp_1369_:
{
uint8_t v___x_1372_; 
v___x_1372_ = l_Array_compareLex___redArg(v_localinst_1368_, v_a_1370_, v_b_1371_);
lean_dec_ref(v_b_1371_);
lean_dec_ref(v_a_1370_);
if (v___x_1372_ == 1)
{
return v___x_1372_;
}
else
{
return v___x_1372_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord(lean_object* v_i_1461_, lean_object* v_b_1462_, lean_object* v_inst_1463_, lean_object* v_inst_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_){
_start:
{
uint8_t v___x_1467_; 
v___x_1467_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1463_, v_inst_1464_, v_x_1465_, v_x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___boxed(lean_object* v_i_1468_, lean_object* v_b_1469_, lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
uint8_t v_res_1474_; lean_object* v_r_1475_; 
v_res_1474_ = l_Lean_Doc_instOrdBlock_ord(v_i_1468_, v_b_1469_, v_inst_1470_, v_inst_1471_, v_x_1472_, v_x_1473_);
v_r_1475_ = lean_box(v_res_1474_);
return v_r_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock___redArg(lean_object* v_inst_1476_, lean_object* v_inst_1477_){
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
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock(lean_object* v_i_1479_, lean_object* v_b_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1483_, 0, lean_box(0));
lean_closure_set(v___x_1483_, 1, lean_box(0));
lean_closure_set(v___x_1483_, 2, v_inst_1481_);
lean_closure_set(v___x_1483_, 3, v_inst_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = lean_nat_to_int(v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg___boxed(lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_x_1536_, lean_object* v_prec_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1534_, v_inst_1535_, v_x_1536_, v_prec_1537_);
lean_dec(v_prec_1537_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg(lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_x_1541_, lean_object* v_prec_1542_){
_start:
{
lean_object* v_localinst_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_inc_ref(v_inst_1540_);
lean_inc_ref(v_inst_1539_);
v_localinst_1543_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1543_, 0, v_inst_1539_);
lean_closure_set(v_localinst_1543_, 1, v_inst_1540_);
v___x_1544_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1544_, 0, lean_box(0));
lean_closure_set(v___x_1544_, 1, v_inst_1539_);
lean_inc_ref(v_localinst_1543_);
v___x_1545_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_1545_, 0, lean_box(0));
lean_closure_set(v___x_1545_, 1, v_localinst_1543_);
switch(lean_obj_tag(v_x_1541_))
{
case 0:
{
lean_object* v_contents_1546_; lean_object* v___y_1548_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
lean_dec_ref(v___x_1545_);
lean_dec_ref(v_localinst_1543_);
lean_dec_ref(v_inst_1540_);
v_contents_1546_ = lean_ctor_get(v_x_1541_, 0);
lean_inc_ref(v_contents_1546_);
lean_dec_ref_known(v_x_1541_, 1);
v___x_1556_ = lean_unsigned_to_nat(1024u);
v___x_1557_ = lean_nat_dec_le(v___x_1556_, v_prec_1542_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1548_ = v___x_1558_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1548_ = v___x_1559_;
goto v___jp_1547_;
}
v___jp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1549_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__2));
v___x_1550_ = l_Array_repr___redArg(v___x_1544_, v_contents_1546_);
v___x_1551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
lean_inc(v___y_1548_);
v___x_1552_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___y_1548_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = 0;
v___x_1554_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*1, v___x_1553_);
v___x_1555_ = l_Repr_addAppParen(v___x_1554_, v_prec_1542_);
return v___x_1555_;
}
}
case 1:
{
lean_object* v_content_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v___x_1545_);
lean_dec_ref(v___x_1544_);
lean_dec_ref(v_localinst_1543_);
lean_dec_ref(v_inst_1540_);
v_content_1560_ = lean_ctor_get(v_x_1541_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_x_1541_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1562_ = v_x_1541_;
v_isShared_1563_ = v_isSharedCheck_1580_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_content_1560_);
lean_dec(v_x_1541_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1580_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___y_1565_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_unsigned_to_nat(1024u);
v___x_1577_ = lean_nat_dec_le(v___x_1576_, v_prec_1542_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1565_ = v___x_1578_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1565_ = v___x_1579_;
goto v___jp_1564_;
}
v___jp_1564_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1566_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__5));
v___x_1567_ = l_String_quote(v_content_1560_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 3);
lean_ctor_set(v___x_1562_, 0, v___x_1567_);
v___x_1569_ = v___x_1562_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1566_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
lean_inc(v___y_1565_);
v___x_1571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___y_1565_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = 0;
v___x_1573_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*1, v___x_1572_);
v___x_1574_ = l_Repr_addAppParen(v___x_1573_, v_prec_1542_);
return v___x_1574_;
}
}
}
}
case 2:
{
lean_object* v_items_1581_; lean_object* v___y_1583_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
lean_dec_ref(v___x_1544_);
lean_dec_ref(v_localinst_1543_);
lean_dec_ref(v_inst_1540_);
v_items_1581_ = lean_ctor_get(v_x_1541_, 0);
lean_inc_ref(v_items_1581_);
lean_dec_ref_known(v_x_1541_, 1);
v___x_1591_ = lean_unsigned_to_nat(1024u);
v___x_1592_ = lean_nat_dec_le(v___x_1591_, v_prec_1542_);
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
v___x_1584_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__8));
v___x_1585_ = l_Array_repr___redArg(v___x_1545_, v_items_1581_);
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
v___x_1590_ = l_Repr_addAppParen(v___x_1589_, v_prec_1542_);
return v___x_1590_;
}
}
case 3:
{
lean_object* v_start_1595_; lean_object* v_items_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v___x_1544_);
lean_dec_ref(v_localinst_1543_);
lean_dec_ref(v_inst_1540_);
v_start_1595_ = lean_ctor_get(v_x_1541_, 0);
v_items_1596_ = lean_ctor_get(v_x_1541_, 1);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_x_1541_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1598_ = v_x_1541_;
v_isShared_1599_ = v_isSharedCheck_1631_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_items_1596_);
lean_inc(v_start_1595_);
lean_dec(v_x_1541_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1631_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1616_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = lean_unsigned_to_nat(1024u);
v___x_1628_ = lean_nat_dec_le(v___x_1627_, v_prec_1542_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1616_ = v___x_1629_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1616_ = v___x_1630_;
goto v___jp_1615_;
}
v___jp_1600_:
{
lean_object* v___x_1606_; 
lean_inc(v___y_1601_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 5);
lean_ctor_set(v___x_1598_, 1, v___y_1604_);
lean_ctor_set(v___x_1598_, 0, v___y_1601_);
v___x_1606_ = v___x_1598_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___y_1601_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v___y_1604_);
v___x_1606_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_inc(v___y_1603_);
v___x_1607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v___y_1603_);
v___x_1608_ = l_Array_repr___redArg(v___x_1545_, v_items_1596_);
v___x_1609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
lean_inc(v___y_1602_);
v___x_1610_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___y_1602_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = 0;
v___x_1612_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*1, v___x_1611_);
v___x_1613_ = l_Repr_addAppParen(v___x_1612_, v_prec_1542_);
return v___x_1613_;
}
}
v___jp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1617_ = lean_box(1);
v___x_1618_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__11));
v___x_1619_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___redArg___closed__12, &l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12);
v___x_1620_ = lean_int_dec_lt(v_start_1595_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = l_Int_repr(v_start_1595_);
lean_dec(v_start_1595_);
v___x_1622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
v___y_1601_ = v___x_1618_;
v___y_1602_ = v___y_1616_;
v___y_1603_ = v___x_1617_;
v___y_1604_ = v___x_1622_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1623_ = lean_unsigned_to_nat(1024u);
v___x_1624_ = l_Int_repr(v_start_1595_);
lean_dec(v_start_1595_);
v___x_1625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
v___x_1626_ = l_Repr_addAppParen(v___x_1625_, v___x_1623_);
v___y_1601_ = v___x_1618_;
v___y_1602_ = v___y_1616_;
v___y_1603_ = v___x_1617_;
v___y_1604_ = v___x_1626_;
goto v___jp_1600_;
}
}
}
}
case 4:
{
lean_object* v_items_1632_; lean_object* v___x_1633_; lean_object* v___y_1635_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
lean_dec_ref(v___x_1545_);
lean_dec_ref(v_inst_1540_);
v_items_1632_ = lean_ctor_get(v_x_1541_, 0);
lean_inc_ref(v_items_1632_);
lean_dec_ref_known(v_x_1541_, 1);
v___x_1633_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1633_, 0, lean_box(0));
lean_closure_set(v___x_1633_, 1, lean_box(0));
lean_closure_set(v___x_1633_, 2, v___x_1544_);
lean_closure_set(v___x_1633_, 3, v_localinst_1543_);
v___x_1643_ = lean_unsigned_to_nat(1024u);
v___x_1644_ = lean_nat_dec_le(v___x_1643_, v_prec_1542_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1635_ = v___x_1645_;
goto v___jp_1634_;
}
else
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1635_ = v___x_1646_;
goto v___jp_1634_;
}
v___jp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1636_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__15));
v___x_1637_ = l_Array_repr___redArg(v___x_1633_, v_items_1632_);
v___x_1638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
lean_inc(v___y_1635_);
v___x_1639_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___y_1635_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = 0;
v___x_1641_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set_uint8(v___x_1641_, sizeof(void*)*1, v___x_1640_);
v___x_1642_ = l_Repr_addAppParen(v___x_1641_, v_prec_1542_);
return v___x_1642_;
}
}
case 5:
{
lean_object* v_items_1647_; lean_object* v___y_1649_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
lean_dec_ref(v___x_1545_);
lean_dec_ref(v___x_1544_);
lean_dec_ref(v_inst_1540_);
v_items_1647_ = lean_ctor_get(v_x_1541_, 0);
lean_inc_ref(v_items_1647_);
lean_dec_ref_known(v_x_1541_, 1);
v___x_1657_ = lean_unsigned_to_nat(1024u);
v___x_1658_ = lean_nat_dec_le(v___x_1657_, v_prec_1542_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1649_ = v___x_1659_;
goto v___jp_1648_;
}
else
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1649_ = v___x_1660_;
goto v___jp_1648_;
}
v___jp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1650_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__18));
v___x_1651_ = l_Array_repr___redArg(v_localinst_1543_, v_items_1647_);
v___x_1652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
lean_inc(v___y_1649_);
v___x_1653_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___y_1649_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = 0;
v___x_1655_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set_uint8(v___x_1655_, sizeof(void*)*1, v___x_1654_);
v___x_1656_ = l_Repr_addAppParen(v___x_1655_, v_prec_1542_);
return v___x_1656_;
}
}
case 6:
{
lean_object* v_content_1661_; lean_object* v___y_1663_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
lean_dec_ref(v___x_1545_);
lean_dec_ref(v___x_1544_);
lean_dec_ref(v_inst_1540_);
v_content_1661_ = lean_ctor_get(v_x_1541_, 0);
lean_inc_ref(v_content_1661_);
lean_dec_ref_known(v_x_1541_, 1);
v___x_1671_ = lean_unsigned_to_nat(1024u);
v___x_1672_ = lean_nat_dec_le(v___x_1671_, v_prec_1542_);
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
v___x_1664_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__21));
v___x_1665_ = l_Array_repr___redArg(v_localinst_1543_, v_content_1661_);
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
v___x_1670_ = l_Repr_addAppParen(v___x_1669_, v_prec_1542_);
return v___x_1670_;
}
}
default: 
{
lean_object* v_container_1675_; lean_object* v_content_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1700_; 
lean_dec_ref(v___x_1545_);
lean_dec_ref(v___x_1544_);
v_container_1675_ = lean_ctor_get(v_x_1541_, 0);
v_content_1676_ = lean_ctor_get(v_x_1541_, 1);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_x_1541_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1678_ = v_x_1541_;
v_isShared_1679_ = v_isSharedCheck_1700_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_content_1676_);
lean_inc(v_container_1675_);
lean_dec(v_x_1541_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1700_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___y_1681_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = lean_unsigned_to_nat(1024u);
v___x_1697_ = lean_nat_dec_le(v___x_1696_, v_prec_1542_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1681_ = v___x_1698_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1681_ = v___x_1699_;
goto v___jp_1680_;
}
v___jp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1682_ = lean_box(1);
v___x_1683_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__24));
v___x_1684_ = lean_unsigned_to_nat(1024u);
v___x_1685_ = lean_apply_2(v_inst_1540_, v_container_1675_, v___x_1684_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 5);
lean_ctor_set(v___x_1678_, 1, v___x_1685_);
lean_ctor_set(v___x_1678_, 0, v___x_1683_);
v___x_1687_ = v___x_1678_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v___x_1682_);
v___x_1689_ = l_Array_repr___redArg(v_localinst_1543_, v_content_1676_);
v___x_1690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
lean_inc(v___y_1681_);
v___x_1691_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1681_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = 0;
v___x_1693_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*1, v___x_1692_);
v___x_1694_ = l_Repr_addAppParen(v___x_1693_, v_prec_1542_);
return v___x_1694_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr(lean_object* v_i_1701_, lean_object* v_b_1702_, lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_x_1705_, lean_object* v_prec_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1703_, v_inst_1704_, v_x_1705_, v_prec_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___boxed(lean_object* v_i_1708_, lean_object* v_b_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_x_1712_, lean_object* v_prec_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Doc_instReprBlock_repr(v_i_1708_, v_b_1709_, v_inst_1710_, v_inst_1711_, v_x_1712_, v_prec_1713_);
lean_dec(v_prec_1713_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock___redArg(lean_object* v_inst_1715_, lean_object* v_inst_1716_){
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
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock(lean_object* v_i_1718_, lean_object* v_b_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1722_, 0, lean_box(0));
lean_closure_set(v___x_1722_, 1, lean_box(0));
lean_closure_set(v___x_1722_, 2, v_inst_1720_);
lean_closure_set(v___x_1722_, 3, v_inst_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default(lean_object* v_i_1727_, lean_object* v_b_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlock_default___closed__1));
return v___x_1729_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedBlock___closed__0(void){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_Doc_instInhabitedBlock_default(lean_box(0), lean_box(0));
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock(lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock___closed__0, &l_Lean_Doc_instInhabitedBlock___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock___closed__0);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty(lean_object* v_i_1738_, lean_object* v_b_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = ((lean_object*)(l_Lean_Doc_Block_empty___closed__1));
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg(lean_object* v_x_1741_){
_start:
{
lean_inc_ref(v_x_1741_);
return v_x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg___boxed(lean_object* v_x_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_Doc_Block_cast___redArg(v_x_1742_);
lean_dec_ref(v_x_1742_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast(lean_object* v_i_1744_, lean_object* v_i_x27_1745_, lean_object* v_b_1746_, lean_object* v_b_x27_1747_, lean_object* v_inlines__eq_1748_, lean_object* v_blocks__eq_1749_, lean_object* v_x_1750_){
_start:
{
lean_inc_ref(v_x_1750_);
return v_x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___boxed(lean_object* v_i_1751_, lean_object* v_i_x27_1752_, lean_object* v_b_1753_, lean_object* v_b_x27_1754_, lean_object* v_inlines__eq_1755_, lean_object* v_blocks__eq_1756_, lean_object* v_x_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Doc_Block_cast(v_i_1751_, v_i_x27_1752_, v_b_1753_, v_b_x27_1754_, v_inlines__eq_1755_, v_blocks__eq_1756_, v_x_1757_);
lean_dec_ref(v_x_1757_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___redArg___boxed(lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
uint8_t v_res_1764_; lean_object* v_r_1765_; 
v_res_1764_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1759_, v_inst_1760_, v_inst_1761_, v_x_1762_, v_x_1763_);
v_r_1765_ = lean_box(v_res_1764_);
return v_r_1765_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq___redArg(lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_x_1769_, lean_object* v_x_1770_){
_start:
{
lean_object* v_title_1771_; lean_object* v_titleString_1772_; lean_object* v_metadata_1773_; lean_object* v_content_1774_; lean_object* v_subParts_1775_; lean_object* v_title_1776_; lean_object* v_titleString_1777_; lean_object* v_metadata_1778_; lean_object* v_content_1779_; lean_object* v_subParts_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v_title_1771_ = lean_ctor_get(v_x_1769_, 0);
lean_inc_ref(v_title_1771_);
v_titleString_1772_ = lean_ctor_get(v_x_1769_, 1);
lean_inc_ref(v_titleString_1772_);
v_metadata_1773_ = lean_ctor_get(v_x_1769_, 2);
lean_inc(v_metadata_1773_);
v_content_1774_ = lean_ctor_get(v_x_1769_, 3);
lean_inc_ref(v_content_1774_);
v_subParts_1775_ = lean_ctor_get(v_x_1769_, 4);
lean_inc_ref(v_subParts_1775_);
lean_dec_ref(v_x_1769_);
v_title_1776_ = lean_ctor_get(v_x_1770_, 0);
lean_inc_ref(v_title_1776_);
v_titleString_1777_ = lean_ctor_get(v_x_1770_, 1);
lean_inc_ref(v_titleString_1777_);
v_metadata_1778_ = lean_ctor_get(v_x_1770_, 2);
lean_inc(v_metadata_1778_);
v_content_1779_ = lean_ctor_get(v_x_1770_, 3);
lean_inc_ref(v_content_1779_);
v_subParts_1780_ = lean_ctor_get(v_x_1770_, 4);
lean_inc_ref(v_subParts_1780_);
lean_dec_ref(v_x_1770_);
v___x_1781_ = lean_array_get_size(v_title_1771_);
v___x_1782_ = lean_array_get_size(v_title_1776_);
v___x_1783_ = lean_nat_dec_eq(v___x_1781_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_dec_ref(v_subParts_1780_);
lean_dec_ref(v_content_1779_);
lean_dec(v_metadata_1778_);
lean_dec_ref(v_titleString_1777_);
lean_dec_ref(v_title_1776_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_content_1774_);
lean_dec(v_metadata_1773_);
lean_dec_ref(v_titleString_1772_);
lean_dec_ref(v_title_1771_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_inst_1767_);
lean_dec_ref(v_inst_1766_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
lean_inc_ref(v_inst_1768_);
lean_inc_ref(v_inst_1767_);
lean_inc_ref_n(v_inst_1766_, 2);
v___x_1784_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___redArg___boxed), 5, 3);
lean_closure_set(v___x_1784_, 0, v_inst_1766_);
lean_closure_set(v___x_1784_, 1, v_inst_1767_);
lean_closure_set(v___x_1784_, 2, v_inst_1768_);
v___x_1785_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1785_, 0, lean_box(0));
lean_closure_set(v___x_1785_, 1, v_inst_1766_);
v___x_1786_ = l_Array_isEqvAux___redArg(v_title_1771_, v_title_1776_, v___x_1785_, v___x_1781_);
lean_dec_ref(v_title_1776_);
lean_dec_ref(v_title_1771_);
if (v___x_1786_ == 0)
{
lean_dec_ref(v___x_1784_);
lean_dec_ref(v_subParts_1780_);
lean_dec_ref(v_content_1779_);
lean_dec(v_metadata_1778_);
lean_dec_ref(v_titleString_1777_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_content_1774_);
lean_dec(v_metadata_1773_);
lean_dec_ref(v_titleString_1772_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_inst_1767_);
lean_dec_ref(v_inst_1766_);
return v___x_1786_;
}
else
{
uint8_t v___x_1787_; 
v___x_1787_ = lean_string_dec_eq(v_titleString_1772_, v_titleString_1777_);
lean_dec_ref(v_titleString_1777_);
lean_dec_ref(v_titleString_1772_);
if (v___x_1787_ == 0)
{
lean_dec_ref(v___x_1784_);
lean_dec_ref(v_subParts_1780_);
lean_dec_ref(v_content_1779_);
lean_dec(v_metadata_1778_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_content_1774_);
lean_dec(v_metadata_1773_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_inst_1767_);
lean_dec_ref(v_inst_1766_);
return v___x_1787_;
}
else
{
uint8_t v___x_1788_; 
v___x_1788_ = l_Option_instBEq_beq___redArg(v_inst_1768_, v_metadata_1773_, v_metadata_1778_);
if (v___x_1788_ == 0)
{
lean_dec_ref(v___x_1784_);
lean_dec_ref(v_subParts_1780_);
lean_dec_ref(v_content_1779_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_content_1774_);
lean_dec_ref(v_inst_1767_);
lean_dec_ref(v_inst_1766_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1789_ = lean_array_get_size(v_content_1774_);
v___x_1790_ = lean_array_get_size(v_content_1779_);
v___x_1791_ = lean_nat_dec_eq(v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_dec_ref(v___x_1784_);
lean_dec_ref(v_subParts_1780_);
lean_dec_ref(v_content_1779_);
lean_dec_ref(v_subParts_1775_);
lean_dec_ref(v_content_1774_);
lean_dec_ref(v_inst_1767_);
lean_dec_ref(v_inst_1766_);
return v___x_1791_;
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1792_, 0, lean_box(0));
lean_closure_set(v___x_1792_, 1, lean_box(0));
lean_closure_set(v___x_1792_, 2, v_inst_1766_);
lean_closure_set(v___x_1792_, 3, v_inst_1767_);
v___x_1793_ = l_Array_isEqvAux___redArg(v_content_1774_, v_content_1779_, v___x_1792_, v___x_1789_);
lean_dec_ref(v_content_1779_);
lean_dec_ref(v_content_1774_);
if (v___x_1793_ == 0)
{
lean_dec_ref(v___x_1784_);
lean_dec_ref(v_subParts_1780_);
lean_dec_ref(v_subParts_1775_);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = lean_array_get_size(v_subParts_1775_);
v___x_1795_ = lean_array_get_size(v_subParts_1780_);
v___x_1796_ = lean_nat_dec_eq(v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_dec_ref(v___x_1784_);
lean_dec_ref(v_subParts_1780_);
lean_dec_ref(v_subParts_1775_);
return v___x_1796_;
}
else
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Array_isEqvAux___redArg(v_subParts_1775_, v_subParts_1780_, v___x_1784_, v___x_1794_);
lean_dec_ref(v_subParts_1780_);
lean_dec_ref(v_subParts_1775_);
return v___x_1797_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq(lean_object* v_i_1798_, lean_object* v_b_1799_, lean_object* v_p_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_x_1804_, lean_object* v_x_1805_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1801_, v_inst_1802_, v_inst_1803_, v_x_1804_, v_x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___boxed(lean_object* v_i_1807_, lean_object* v_b_1808_, lean_object* v_p_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_x_1813_, lean_object* v_x_1814_){
_start:
{
uint8_t v_res_1815_; lean_object* v_r_1816_; 
v_res_1815_ = l_Lean_Doc_instBEqPart_beq(v_i_1807_, v_b_1808_, v_p_1809_, v_inst_1810_, v_inst_1811_, v_inst_1812_, v_x_1813_, v_x_1814_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart___redArg(lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1820_, 0, lean_box(0));
lean_closure_set(v___x_1820_, 1, lean_box(0));
lean_closure_set(v___x_1820_, 2, lean_box(0));
lean_closure_set(v___x_1820_, 3, v_inst_1817_);
lean_closure_set(v___x_1820_, 4, v_inst_1818_);
lean_closure_set(v___x_1820_, 5, v_inst_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart(lean_object* v_i_1821_, lean_object* v_b_1822_, lean_object* v_p_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1827_, 0, lean_box(0));
lean_closure_set(v___x_1827_, 1, lean_box(0));
lean_closure_set(v___x_1827_, 2, lean_box(0));
lean_closure_set(v___x_1827_, 3, v_inst_1824_);
lean_closure_set(v___x_1827_, 4, v_inst_1825_);
lean_closure_set(v___x_1827_, 5, v_inst_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___redArg___boxed(lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_){
_start:
{
uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_res_1833_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1828_, v_inst_1829_, v_inst_1830_, v_x_1831_, v_x_1832_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord___redArg(lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v_title_1840_; lean_object* v_titleString_1841_; lean_object* v_metadata_1842_; lean_object* v_content_1843_; lean_object* v_subParts_1844_; lean_object* v_title_1845_; lean_object* v_titleString_1846_; lean_object* v_metadata_1847_; lean_object* v_content_1848_; lean_object* v_subParts_1849_; lean_object* v___x_1850_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v_title_1840_ = lean_ctor_get(v_x_1838_, 0);
lean_inc_ref(v_title_1840_);
v_titleString_1841_ = lean_ctor_get(v_x_1838_, 1);
lean_inc_ref(v_titleString_1841_);
v_metadata_1842_ = lean_ctor_get(v_x_1838_, 2);
lean_inc(v_metadata_1842_);
v_content_1843_ = lean_ctor_get(v_x_1838_, 3);
lean_inc_ref(v_content_1843_);
v_subParts_1844_ = lean_ctor_get(v_x_1838_, 4);
lean_inc_ref(v_subParts_1844_);
lean_dec_ref(v_x_1838_);
v_title_1845_ = lean_ctor_get(v_x_1839_, 0);
lean_inc_ref(v_title_1845_);
v_titleString_1846_ = lean_ctor_get(v_x_1839_, 1);
lean_inc_ref(v_titleString_1846_);
v_metadata_1847_ = lean_ctor_get(v_x_1839_, 2);
lean_inc(v_metadata_1847_);
v_content_1848_ = lean_ctor_get(v_x_1839_, 3);
lean_inc_ref(v_content_1848_);
v_subParts_1849_ = lean_ctor_get(v_x_1839_, 4);
lean_inc_ref(v_subParts_1849_);
lean_dec_ref(v_x_1839_);
lean_inc_ref(v_inst_1837_);
lean_inc_ref(v_inst_1836_);
lean_inc_ref_n(v_inst_1835_, 2);
v___x_1850_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___redArg___boxed), 5, 3);
lean_closure_set(v___x_1850_, 0, v_inst_1835_);
lean_closure_set(v___x_1850_, 1, v_inst_1836_);
lean_closure_set(v___x_1850_, 2, v_inst_1837_);
v___x_1855_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1855_, 0, lean_box(0));
lean_closure_set(v___x_1855_, 1, v_inst_1835_);
v___x_1856_ = l_Array_compareLex___redArg(v___x_1855_, v_title_1840_, v_title_1845_);
lean_dec_ref(v_title_1845_);
lean_dec_ref(v_title_1840_);
if (v___x_1856_ == 1)
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_string_compare(v_titleString_1841_, v_titleString_1846_);
lean_dec_ref(v_titleString_1846_);
lean_dec_ref(v_titleString_1841_);
if (v___x_1857_ == 1)
{
if (lean_obj_tag(v_metadata_1842_) == 0)
{
lean_dec_ref(v_inst_1837_);
if (lean_obj_tag(v_metadata_1847_) == 0)
{
goto v___jp_1851_;
}
else
{
uint8_t v___x_1858_; 
lean_dec_ref_known(v_metadata_1847_, 1);
lean_dec_ref(v___x_1850_);
lean_dec_ref(v_subParts_1849_);
lean_dec_ref(v_content_1848_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_content_1843_);
lean_dec_ref(v_inst_1836_);
lean_dec_ref(v_inst_1835_);
v___x_1858_ = 0;
return v___x_1858_;
}
}
else
{
if (lean_obj_tag(v_metadata_1847_) == 0)
{
uint8_t v___x_1859_; 
lean_dec_ref_known(v_metadata_1842_, 1);
lean_dec_ref(v___x_1850_);
lean_dec_ref(v_subParts_1849_);
lean_dec_ref(v_content_1848_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_content_1843_);
lean_dec_ref(v_inst_1837_);
lean_dec_ref(v_inst_1836_);
lean_dec_ref(v_inst_1835_);
v___x_1859_ = 2;
return v___x_1859_;
}
else
{
lean_object* v_val_1860_; lean_object* v_val_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_val_1860_ = lean_ctor_get(v_metadata_1842_, 0);
lean_inc(v_val_1860_);
lean_dec_ref_known(v_metadata_1842_, 1);
v_val_1861_ = lean_ctor_get(v_metadata_1847_, 0);
lean_inc(v_val_1861_);
lean_dec_ref_known(v_metadata_1847_, 1);
v___x_1862_ = lean_apply_2(v_inst_1837_, v_val_1860_, v_val_1861_);
v___x_1863_ = lean_unbox(v___x_1862_);
if (v___x_1863_ == 1)
{
goto v___jp_1851_;
}
else
{
uint8_t v___x_1864_; 
lean_dec_ref(v___x_1850_);
lean_dec_ref(v_subParts_1849_);
lean_dec_ref(v_content_1848_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_content_1843_);
lean_dec_ref(v_inst_1836_);
lean_dec_ref(v_inst_1835_);
v___x_1864_ = lean_unbox(v___x_1862_);
return v___x_1864_;
}
}
}
}
else
{
lean_dec_ref(v___x_1850_);
lean_dec_ref(v_subParts_1849_);
lean_dec_ref(v_content_1848_);
lean_dec(v_metadata_1847_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_content_1843_);
lean_dec(v_metadata_1842_);
lean_dec_ref(v_inst_1837_);
lean_dec_ref(v_inst_1836_);
lean_dec_ref(v_inst_1835_);
return v___x_1857_;
}
}
else
{
lean_dec_ref(v___x_1850_);
lean_dec_ref(v_subParts_1849_);
lean_dec_ref(v_content_1848_);
lean_dec(v_metadata_1847_);
lean_dec_ref(v_titleString_1846_);
lean_dec_ref(v_subParts_1844_);
lean_dec_ref(v_content_1843_);
lean_dec(v_metadata_1842_);
lean_dec_ref(v_titleString_1841_);
lean_dec_ref(v_inst_1837_);
lean_dec_ref(v_inst_1836_);
lean_dec_ref(v_inst_1835_);
return v___x_1856_;
}
v___jp_1851_:
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1852_, 0, lean_box(0));
lean_closure_set(v___x_1852_, 1, lean_box(0));
lean_closure_set(v___x_1852_, 2, v_inst_1835_);
lean_closure_set(v___x_1852_, 3, v_inst_1836_);
v___x_1853_ = l_Array_compareLex___redArg(v___x_1852_, v_content_1843_, v_content_1848_);
lean_dec_ref(v_content_1848_);
lean_dec_ref(v_content_1843_);
if (v___x_1853_ == 1)
{
uint8_t v___x_1854_; 
v___x_1854_ = l_Array_compareLex___redArg(v___x_1850_, v_subParts_1844_, v_subParts_1849_);
lean_dec_ref(v_subParts_1849_);
lean_dec_ref(v_subParts_1844_);
if (v___x_1854_ == 1)
{
return v___x_1854_;
}
else
{
return v___x_1854_;
}
}
else
{
lean_dec_ref(v___x_1850_);
lean_dec_ref(v_subParts_1849_);
lean_dec_ref(v_subParts_1844_);
return v___x_1853_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord(lean_object* v_i_1865_, lean_object* v_b_1866_, lean_object* v_p_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_){
_start:
{
uint8_t v___x_1873_; 
v___x_1873_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1868_, v_inst_1869_, v_inst_1870_, v_x_1871_, v_x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___boxed(lean_object* v_i_1874_, lean_object* v_b_1875_, lean_object* v_p_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_inst_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
uint8_t v_res_1882_; lean_object* v_r_1883_; 
v_res_1882_ = l_Lean_Doc_instOrdPart_ord(v_i_1874_, v_b_1875_, v_p_1876_, v_inst_1877_, v_inst_1878_, v_inst_1879_, v_x_1880_, v_x_1881_);
v_r_1883_ = lean_box(v_res_1882_);
return v_r_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart___redArg(lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_inst_1886_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1887_, 0, lean_box(0));
lean_closure_set(v___x_1887_, 1, lean_box(0));
lean_closure_set(v___x_1887_, 2, lean_box(0));
lean_closure_set(v___x_1887_, 3, v_inst_1884_);
lean_closure_set(v___x_1887_, 4, v_inst_1885_);
lean_closure_set(v___x_1887_, 5, v_inst_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart(lean_object* v_i_1888_, lean_object* v_b_1889_, lean_object* v_p_1890_, lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_inst_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1894_, 0, lean_box(0));
lean_closure_set(v___x_1894_, 1, lean_box(0));
lean_closure_set(v___x_1894_, 2, lean_box(0));
lean_closure_set(v___x_1894_, 3, v_inst_1891_);
lean_closure_set(v___x_1894_, 4, v_inst_1892_);
lean_closure_set(v___x_1894_, 5, v_inst_1893_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_unsigned_to_nat(9u);
v___x_1905_ = lean_nat_to_int(v___x_1904_);
return v___x_1905_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_unsigned_to_nat(15u);
v___x_1910_ = lean_nat_to_int(v___x_1909_);
return v___x_1910_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_unsigned_to_nat(11u);
v___x_1918_ = lean_nat_to_int(v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg___boxed(lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_x_1925_, lean_object* v_prec_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_1922_, v_inst_1923_, v_inst_1924_, v_x_1925_, v_prec_1926_);
lean_dec(v_prec_1926_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg(lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_x_1931_, lean_object* v_prec_1932_){
_start:
{
lean_object* v_title_1933_; lean_object* v_titleString_1934_; lean_object* v_metadata_1935_; lean_object* v_content_1936_; lean_object* v_subParts_1937_; lean_object* v_localinst_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_title_1933_ = lean_ctor_get(v_x_1931_, 0);
lean_inc_ref(v_title_1933_);
v_titleString_1934_ = lean_ctor_get(v_x_1931_, 1);
lean_inc_ref(v_titleString_1934_);
v_metadata_1935_ = lean_ctor_get(v_x_1931_, 2);
lean_inc(v_metadata_1935_);
v_content_1936_ = lean_ctor_get(v_x_1931_, 3);
lean_inc_ref(v_content_1936_);
v_subParts_1937_ = lean_ctor_get(v_x_1931_, 4);
lean_inc_ref(v_subParts_1937_);
lean_dec_ref(v_x_1931_);
lean_inc_ref(v_inst_1930_);
lean_inc_ref(v_inst_1929_);
lean_inc_ref_n(v_inst_1928_, 2);
v_localinst_1938_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___redArg___boxed), 5, 3);
lean_closure_set(v_localinst_1938_, 0, v_inst_1928_);
lean_closure_set(v_localinst_1938_, 1, v_inst_1929_);
lean_closure_set(v_localinst_1938_, 2, v_inst_1930_);
v___x_1939_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1940_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__3));
v___x_1941_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4);
v___x_1942_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1942_, 0, lean_box(0));
lean_closure_set(v___x_1942_, 1, v_inst_1928_);
v___x_1943_ = l_Array_repr___redArg(v___x_1942_, v_title_1933_);
v___x_1944_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1941_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = 0;
v___x_1946_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1946_, 0, v___x_1944_);
lean_ctor_set_uint8(v___x_1946_, sizeof(void*)*1, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1940_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_box(1);
v___x_1951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__6));
v___x_1953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v___x_1939_);
v___x_1955_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7);
v___x_1956_ = l_String_quote(v_titleString_1934_);
v___x_1957_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
v___x_1958_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1955_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*1, v___x_1945_);
v___x_1960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1954_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v___x_1948_);
v___x_1962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
lean_ctor_set(v___x_1962_, 1, v___x_1950_);
v___x_1963_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__9));
v___x_1964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
lean_ctor_set(v___x_1965_, 1, v___x_1939_);
v___x_1966_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = l_Option_repr___redArg(v_inst_1930_, v_metadata_1935_, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1966_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*1, v___x_1945_);
v___x_1971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1965_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
lean_ctor_set(v___x_1972_, 1, v___x_1948_);
v___x_1973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
lean_ctor_set(v___x_1973_, 1, v___x_1950_);
v___x_1974_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__11));
v___x_1975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v___x_1939_);
v___x_1977_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12);
v___x_1978_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1978_, 0, lean_box(0));
lean_closure_set(v___x_1978_, 1, lean_box(0));
lean_closure_set(v___x_1978_, 2, v_inst_1928_);
lean_closure_set(v___x_1978_, 3, v_inst_1929_);
v___x_1979_ = l_Array_repr___redArg(v___x_1978_, v_content_1936_);
v___x_1980_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1977_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*1, v___x_1945_);
v___x_1982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1976_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v___x_1948_);
v___x_1984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v___x_1950_);
v___x_1985_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__14));
v___x_1986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
lean_ctor_set(v___x_1987_, 1, v___x_1939_);
v___x_1988_ = l_Array_repr___redArg(v_localinst_1938_, v_subParts_1937_);
v___x_1989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1966_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*1, v___x_1945_);
v___x_1991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1987_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_1993_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_1994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v___x_1991_);
v___x_1995_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_1996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1992_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*1, v___x_1945_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr(lean_object* v_i_1999_, lean_object* v_b_2000_, lean_object* v_p_2001_, lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_inst_2004_, lean_object* v_x_2005_, lean_object* v_prec_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_2002_, v_inst_2003_, v_inst_2004_, v_x_2005_, v_prec_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___boxed(lean_object* v_i_2008_, lean_object* v_b_2009_, lean_object* v_p_2010_, lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_x_2014_, lean_object* v_prec_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Doc_instReprPart_repr(v_i_2008_, v_b_2009_, v_p_2010_, v_inst_2011_, v_inst_2012_, v_inst_2013_, v_x_2014_, v_prec_2015_);
lean_dec(v_prec_2015_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart___redArg(lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2020_, 0, lean_box(0));
lean_closure_set(v___x_2020_, 1, lean_box(0));
lean_closure_set(v___x_2020_, 2, lean_box(0));
lean_closure_set(v___x_2020_, 3, v_inst_2017_);
lean_closure_set(v___x_2020_, 4, v_inst_2018_);
lean_closure_set(v___x_2020_, 5, v_inst_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart(lean_object* v_i_2021_, lean_object* v_b_2022_, lean_object* v_p_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2027_, 0, lean_box(0));
lean_closure_set(v___x_2027_, 1, lean_box(0));
lean_closure_set(v___x_2027_, 2, lean_box(0));
lean_closure_set(v___x_2027_, 3, v_inst_2024_);
lean_closure_set(v___x_2027_, 4, v_inst_2025_);
lean_closure_set(v___x_2027_, 5, v_inst_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default(lean_object* v_i_2032_, lean_object* v_b_2033_, lean_object* v_p_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = ((lean_object*)(l_Lean_Doc_instInhabitedPart_default___closed__0));
return v___x_2035_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedPart___closed__0(void){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_Doc_instInhabitedPart_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart(lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart___closed__0, &l_Lean_Doc_instInhabitedPart___closed__0_once, _init_l_Lean_Doc_instInhabitedPart___closed__0);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg(lean_object* v_x_2041_){
_start:
{
lean_inc_ref(v_x_2041_);
return v_x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg___boxed(lean_object* v_x_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Doc_Part_cast___redArg(v_x_2042_);
lean_dec_ref(v_x_2042_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast(lean_object* v_i_2044_, lean_object* v_i_x27_2045_, lean_object* v_b_2046_, lean_object* v_b_x27_2047_, lean_object* v_p_2048_, lean_object* v_p_x27_2049_, lean_object* v_inlines__eq_2050_, lean_object* v_blocks__eq_2051_, lean_object* v_metadata__eq_2052_, lean_object* v_x_2053_){
_start:
{
lean_inc_ref(v_x_2053_);
return v_x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___boxed(lean_object* v_i_2054_, lean_object* v_i_x27_2055_, lean_object* v_b_2056_, lean_object* v_b_x27_2057_, lean_object* v_p_2058_, lean_object* v_p_x27_2059_, lean_object* v_inlines__eq_2060_, lean_object* v_blocks__eq_2061_, lean_object* v_metadata__eq_2062_, lean_object* v_x_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Doc_Part_cast(v_i_2054_, v_i_x27_2055_, v_b_2056_, v_b_x27_2057_, v_p_2058_, v_p_x27_2059_, v_inlines__eq_2060_, v_blocks__eq_2061_, v_metadata__eq_2062_, v_x_2063_);
lean_dec_ref(v_x_2063_);
return v_res_2064_;
}
}
lean_object* runtime_initialize_Init_Data_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Compare(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
