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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
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
lean_dec_ref(v_t_152_);
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
lean_dec_ref(v_t_152_);
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
lean_dec_ref(v_t_152_);
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
lean_dec_ref(v_t_152_);
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
lean_dec_ref(v_t_152_);
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
lean_dec_ref(v_x_291_);
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
lean_dec_ref(v_x_291_);
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
lean_dec_ref(v_x_291_);
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
lean_dec_ref(v_x_291_);
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
lean_dec_ref(v_x_291_);
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
lean_dec_ref(v_x_291_);
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
lean_dec_ref(v_x_291_);
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
lean_dec_ref(v_x_291_);
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
lean_object* v_string_379_; lean_object* v_string_x27_380_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_386_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_376_);
v___x_387_ = l_Lean_Doc_Inline_ctorIdx___redArg(v_x_377_);
v___x_388_ = lean_nat_dec_lt(v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; 
v___x_389_ = lean_nat_dec_eq(v___x_386_, v___x_387_);
lean_dec(v___x_387_);
lean_dec(v___x_386_);
if (v___x_389_ == 0)
{
uint8_t v___x_390_; 
lean_dec_ref(v_x_377_);
lean_dec_ref(v_x_376_);
lean_dec_ref(v_inst_375_);
v___x_390_ = 2;
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v_content_393_; lean_object* v_content_x27_394_; 
lean_inc_ref(v_inst_375_);
v___x_391_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___redArg___boxed), 3, 1);
lean_closure_set(v___x_391_, 0, v_inst_375_);
switch(lean_obj_tag(v_x_376_))
{
case 1:
{
lean_object* v_content_396_; lean_object* v_content_397_; 
lean_dec_ref(v_inst_375_);
v_content_396_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_396_);
lean_dec_ref(v_x_376_);
v_content_397_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_content_397_);
lean_dec_ref(v_x_377_);
v_content_393_ = v_content_396_;
v_content_x27_394_ = v_content_397_;
goto v___jp_392_;
}
case 2:
{
lean_object* v_content_398_; lean_object* v_content_399_; 
lean_dec_ref(v_inst_375_);
v_content_398_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_398_);
lean_dec_ref(v_x_376_);
v_content_399_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_content_399_);
lean_dec_ref(v_x_377_);
v_content_393_ = v_content_398_;
v_content_x27_394_ = v_content_399_;
goto v___jp_392_;
}
case 4:
{
uint8_t v_mode_400_; lean_object* v_string_401_; uint8_t v_mode_402_; lean_object* v_string_403_; uint8_t v___x_404_; 
lean_dec_ref(v___x_391_);
lean_dec_ref(v_inst_375_);
v_mode_400_ = lean_ctor_get_uint8(v_x_376_, sizeof(void*)*1);
v_string_401_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_string_401_);
lean_dec_ref(v_x_376_);
v_mode_402_ = lean_ctor_get_uint8(v_x_377_, sizeof(void*)*1);
v_string_403_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_string_403_);
lean_dec_ref(v_x_377_);
v___x_404_ = l_Lean_Doc_instOrdMathMode_ord(v_mode_400_, v_mode_402_);
if (v___x_404_ == 1)
{
uint8_t v___x_405_; 
v___x_405_ = lean_string_dec_lt(v_string_401_, v_string_403_);
if (v___x_405_ == 0)
{
uint8_t v___x_406_; 
v___x_406_ = lean_string_dec_eq(v_string_401_, v_string_403_);
lean_dec_ref(v_string_403_);
lean_dec_ref(v_string_401_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 2;
return v___x_407_;
}
else
{
return v___x_404_;
}
}
else
{
uint8_t v___x_408_; 
lean_dec_ref(v_string_403_);
lean_dec_ref(v_string_401_);
v___x_408_ = 0;
return v___x_408_;
}
}
else
{
lean_dec_ref(v_string_403_);
lean_dec_ref(v_string_401_);
return v___x_404_;
}
}
case 6:
{
lean_object* v_content_409_; lean_object* v_url_410_; lean_object* v_content_411_; lean_object* v_url_412_; uint8_t v___x_413_; 
lean_dec_ref(v_inst_375_);
v_content_409_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_409_);
v_url_410_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_url_410_);
lean_dec_ref(v_x_376_);
v_content_411_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_content_411_);
v_url_412_ = lean_ctor_get(v_x_377_, 1);
lean_inc_ref(v_url_412_);
lean_dec_ref(v_x_377_);
v___x_413_ = l_Array_compareLex___redArg(v___x_391_, v_content_409_, v_content_411_);
lean_dec_ref(v_content_411_);
lean_dec_ref(v_content_409_);
if (v___x_413_ == 1)
{
uint8_t v___x_414_; 
v___x_414_ = lean_string_dec_lt(v_url_410_, v_url_412_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; 
v___x_415_ = lean_string_dec_eq(v_url_410_, v_url_412_);
lean_dec_ref(v_url_412_);
lean_dec_ref(v_url_410_);
if (v___x_415_ == 0)
{
uint8_t v___x_416_; 
v___x_416_ = 2;
return v___x_416_;
}
else
{
return v___x_413_;
}
}
else
{
uint8_t v___x_417_; 
lean_dec_ref(v_url_412_);
lean_dec_ref(v_url_410_);
v___x_417_ = 0;
return v___x_417_;
}
}
else
{
lean_dec_ref(v_url_412_);
lean_dec_ref(v_url_410_);
return v___x_413_;
}
}
case 7:
{
lean_object* v_name_418_; lean_object* v_content_419_; lean_object* v_name_420_; lean_object* v_content_421_; uint8_t v___x_422_; 
lean_dec_ref(v_inst_375_);
v_name_418_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_name_418_);
v_content_419_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_content_419_);
lean_dec_ref(v_x_376_);
v_name_420_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_name_420_);
v_content_421_ = lean_ctor_get(v_x_377_, 1);
lean_inc_ref(v_content_421_);
lean_dec_ref(v_x_377_);
v___x_422_ = lean_string_dec_lt(v_name_418_, v_name_420_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; 
v___x_423_ = lean_string_dec_eq(v_name_418_, v_name_420_);
lean_dec_ref(v_name_420_);
lean_dec_ref(v_name_418_);
if (v___x_423_ == 0)
{
uint8_t v___x_424_; 
lean_dec_ref(v_content_421_);
lean_dec_ref(v_content_419_);
lean_dec_ref(v___x_391_);
v___x_424_ = 2;
return v___x_424_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = l_Array_compareLex___redArg(v___x_391_, v_content_419_, v_content_421_);
lean_dec_ref(v_content_421_);
lean_dec_ref(v_content_419_);
if (v___x_425_ == 1)
{
return v___x_425_;
}
else
{
return v___x_425_;
}
}
}
else
{
uint8_t v___x_426_; 
lean_dec_ref(v_content_421_);
lean_dec_ref(v_name_420_);
lean_dec_ref(v_content_419_);
lean_dec_ref(v_name_418_);
lean_dec_ref(v___x_391_);
v___x_426_ = 0;
return v___x_426_;
}
}
case 8:
{
lean_object* v_alt_427_; lean_object* v_url_428_; lean_object* v_alt_429_; lean_object* v_url_430_; uint8_t v___x_431_; 
lean_dec_ref(v___x_391_);
lean_dec_ref(v_inst_375_);
v_alt_427_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_alt_427_);
v_url_428_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_url_428_);
lean_dec_ref(v_x_376_);
v_alt_429_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_alt_429_);
v_url_430_ = lean_ctor_get(v_x_377_, 1);
lean_inc_ref(v_url_430_);
lean_dec_ref(v_x_377_);
v___x_431_ = lean_string_dec_lt(v_alt_427_, v_alt_429_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; 
v___x_432_ = lean_string_dec_eq(v_alt_427_, v_alt_429_);
lean_dec_ref(v_alt_429_);
lean_dec_ref(v_alt_427_);
if (v___x_432_ == 0)
{
uint8_t v___x_433_; 
lean_dec_ref(v_url_430_);
lean_dec_ref(v_url_428_);
v___x_433_ = 2;
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = lean_string_dec_lt(v_url_428_, v_url_430_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; 
v___x_435_ = lean_string_dec_eq(v_url_428_, v_url_430_);
lean_dec_ref(v_url_430_);
lean_dec_ref(v_url_428_);
if (v___x_435_ == 0)
{
uint8_t v___x_436_; 
v___x_436_ = 2;
return v___x_436_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = 1;
return v___x_437_;
}
}
else
{
uint8_t v___x_438_; 
lean_dec_ref(v_url_430_);
lean_dec_ref(v_url_428_);
v___x_438_ = 0;
return v___x_438_;
}
}
}
else
{
uint8_t v___x_439_; 
lean_dec_ref(v_url_430_);
lean_dec_ref(v_alt_429_);
lean_dec_ref(v_url_428_);
lean_dec_ref(v_alt_427_);
v___x_439_ = 0;
return v___x_439_;
}
}
case 9:
{
lean_object* v_content_440_; lean_object* v_content_441_; 
lean_dec_ref(v_inst_375_);
v_content_440_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_content_440_);
lean_dec_ref(v_x_376_);
v_content_441_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_content_441_);
lean_dec_ref(v_x_377_);
v_content_393_ = v_content_440_;
v_content_x27_394_ = v_content_441_;
goto v___jp_392_;
}
case 10:
{
lean_object* v_container_442_; lean_object* v_content_443_; lean_object* v_container_444_; lean_object* v_content_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_container_442_ = lean_ctor_get(v_x_376_, 0);
lean_inc(v_container_442_);
v_content_443_ = lean_ctor_get(v_x_376_, 1);
lean_inc_ref(v_content_443_);
lean_dec_ref(v_x_376_);
v_container_444_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_container_444_);
v_content_445_ = lean_ctor_get(v_x_377_, 1);
lean_inc_ref(v_content_445_);
lean_dec_ref(v_x_377_);
v___x_446_ = lean_apply_2(v_inst_375_, v_container_442_, v_container_444_);
v___x_447_ = lean_unbox(v___x_446_);
if (v___x_447_ == 1)
{
uint8_t v___x_448_; 
v___x_448_ = l_Array_compareLex___redArg(v___x_391_, v_content_443_, v_content_445_);
lean_dec_ref(v_content_445_);
lean_dec_ref(v_content_443_);
if (v___x_448_ == 1)
{
return v___x_448_;
}
else
{
return v___x_448_;
}
}
else
{
uint8_t v___x_449_; 
lean_dec_ref(v_content_445_);
lean_dec_ref(v_content_443_);
lean_dec_ref(v___x_391_);
v___x_449_ = lean_unbox(v___x_446_);
return v___x_449_;
}
}
default: 
{
lean_object* v_string_450_; lean_object* v_string_451_; 
lean_dec_ref(v___x_391_);
lean_dec_ref(v_inst_375_);
v_string_450_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_string_450_);
lean_dec_ref(v_x_376_);
v_string_451_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_string_451_);
lean_dec_ref(v_x_377_);
v_string_379_ = v_string_450_;
v_string_x27_380_ = v_string_451_;
goto v___jp_378_;
}
}
v___jp_392_:
{
uint8_t v___x_395_; 
v___x_395_ = l_Array_compareLex___redArg(v___x_391_, v_content_393_, v_content_x27_394_);
lean_dec_ref(v_content_x27_394_);
lean_dec_ref(v_content_393_);
if (v___x_395_ == 1)
{
return v___x_395_;
}
else
{
return v___x_395_;
}
}
}
}
else
{
uint8_t v___x_452_; 
lean_dec(v___x_387_);
lean_dec(v___x_386_);
lean_dec_ref(v_x_377_);
lean_dec_ref(v_x_376_);
lean_dec_ref(v_inst_375_);
v___x_452_ = 0;
return v___x_452_;
}
v___jp_378_:
{
uint8_t v___x_381_; 
v___x_381_ = lean_string_dec_lt(v_string_379_, v_string_x27_380_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; 
v___x_382_ = lean_string_dec_eq(v_string_379_, v_string_x27_380_);
lean_dec_ref(v_string_x27_380_);
lean_dec_ref(v_string_379_);
if (v___x_382_ == 0)
{
uint8_t v___x_383_; 
v___x_383_ = 2;
return v___x_383_;
}
else
{
uint8_t v___x_384_; 
v___x_384_ = 1;
return v___x_384_;
}
}
else
{
uint8_t v___x_385_; 
lean_dec_ref(v_string_x27_380_);
lean_dec_ref(v_string_379_);
v___x_385_ = 0;
return v___x_385_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord(lean_object* v_i_453_, lean_object* v_inst_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_454_, v_x_455_, v_x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___boxed(lean_object* v_i_458_, lean_object* v_inst_459_, lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Lean_Doc_instOrdInline_ord(v_i_458_, v_inst_459_, v_x_460_, v_x_461_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline___redArg(lean_object* v_inst_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_465_, 0, lean_box(0));
lean_closure_set(v___x_465_, 1, v_inst_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline(lean_object* v_i_466_, lean_object* v_inst_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_468_, 0, lean_box(0));
lean_closure_set(v___x_468_, 1, v_inst_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg___boxed(lean_object* v_inst_535_, lean_object* v_x_536_, lean_object* v_prec_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_535_, v_x_536_, v_prec_537_);
lean_dec(v_prec_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg(lean_object* v_inst_539_, lean_object* v_x_540_, lean_object* v_prec_541_){
_start:
{
lean_object* v_localinst_542_; 
lean_inc_ref(v_inst_539_);
v_localinst_542_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_542_, 0, v_inst_539_);
switch(lean_obj_tag(v_x_540_))
{
case 0:
{
lean_object* v_string_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v_localinst_542_);
lean_dec_ref(v_inst_539_);
v_string_543_ = lean_ctor_get(v_x_540_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_563_ == 0)
{
v___x_545_ = v_x_540_;
v_isShared_546_ = v_isSharedCheck_563_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_string_543_);
lean_dec(v_x_540_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_563_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___y_548_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(1024u);
v___x_560_ = lean_nat_dec_le(v___x_559_, v_prec_541_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_548_ = v___x_561_;
goto v___jp_547_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_548_ = v___x_562_;
goto v___jp_547_;
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_549_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__2));
v___x_550_ = l_String_quote(v_string_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 3);
lean_ctor_set(v___x_545_, 0, v___x_550_);
v___x_552_ = v___x_545_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_558_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_549_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
lean_inc(v___y_548_);
v___x_554_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_554_, 0, v___y_548_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = 0;
v___x_556_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*1, v___x_555_);
v___x_557_ = l_Repr_addAppParen(v___x_556_, v_prec_541_);
return v___x_557_;
}
}
}
}
case 1:
{
lean_object* v_content_564_; lean_object* v___y_566_; lean_object* v___x_574_; uint8_t v___x_575_; 
lean_dec_ref(v_inst_539_);
v_content_564_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_content_564_);
lean_dec_ref(v_x_540_);
v___x_574_ = lean_unsigned_to_nat(1024u);
v___x_575_ = lean_nat_dec_le(v___x_574_, v_prec_541_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_566_ = v___x_576_;
goto v___jp_565_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_566_ = v___x_577_;
goto v___jp_565_;
}
v___jp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_567_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__5));
v___x_568_ = l_Array_repr___redArg(v_localinst_542_, v_content_564_);
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
lean_inc(v___y_566_);
v___x_570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_566_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = 0;
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_571_);
v___x_573_ = l_Repr_addAppParen(v___x_572_, v_prec_541_);
return v___x_573_;
}
}
case 2:
{
lean_object* v_content_578_; lean_object* v___y_580_; lean_object* v___x_588_; uint8_t v___x_589_; 
lean_dec_ref(v_inst_539_);
v_content_578_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_content_578_);
lean_dec_ref(v_x_540_);
v___x_588_ = lean_unsigned_to_nat(1024u);
v___x_589_ = lean_nat_dec_le(v___x_588_, v_prec_541_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_580_ = v___x_590_;
goto v___jp_579_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_580_ = v___x_591_;
goto v___jp_579_;
}
v___jp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_581_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__8));
v___x_582_ = l_Array_repr___redArg(v_localinst_542_, v_content_578_);
v___x_583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
lean_inc(v___y_580_);
v___x_584_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_584_, 0, v___y_580_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = 0;
v___x_586_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set_uint8(v___x_586_, sizeof(void*)*1, v___x_585_);
v___x_587_ = l_Repr_addAppParen(v___x_586_, v_prec_541_);
return v___x_587_;
}
}
case 3:
{
lean_object* v_string_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_localinst_542_);
lean_dec_ref(v_inst_539_);
v_string_592_ = lean_ctor_get(v_x_540_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_612_ == 0)
{
v___x_594_ = v_x_540_;
v_isShared_595_ = v_isSharedCheck_612_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_string_592_);
lean_dec(v_x_540_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_612_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___y_597_; lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1024u);
v___x_609_ = lean_nat_dec_le(v___x_608_, v_prec_541_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_597_ = v___x_610_;
goto v___jp_596_;
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_597_ = v___x_611_;
goto v___jp_596_;
}
v___jp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_598_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__11));
v___x_599_ = l_String_quote(v_string_592_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_599_);
v___x_601_ = v___x_594_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_607_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_598_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_inc(v___y_597_);
v___x_603_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_603_, 0, v___y_597_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = 0;
v___x_605_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*1, v___x_604_);
v___x_606_ = l_Repr_addAppParen(v___x_605_, v_prec_541_);
return v___x_606_;
}
}
}
}
case 4:
{
uint8_t v_mode_613_; lean_object* v_string_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v_localinst_542_);
lean_dec_ref(v_inst_539_);
v_mode_613_ = lean_ctor_get_uint8(v_x_540_, sizeof(void*)*1);
v_string_614_ = lean_ctor_get(v_x_540_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_639_ == 0)
{
v___x_616_ = v_x_540_;
v_isShared_617_ = v_isSharedCheck_639_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_string_614_);
lean_dec(v_x_540_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_639_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___y_619_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(1024u);
v___x_636_ = lean_nat_dec_le(v___x_635_, v_prec_541_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_619_ = v___x_637_;
goto v___jp_618_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_619_ = v___x_638_;
goto v___jp_618_;
}
v___jp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_632_; 
v___x_620_ = lean_box(1);
v___x_621_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__14));
v___x_622_ = lean_unsigned_to_nat(1024u);
v___x_623_ = l_Lean_Doc_instReprMathMode_repr(v_mode_613_, v___x_622_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_621_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_620_);
v___x_626_ = l_String_quote(v_string_614_);
v___x_627_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_625_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
lean_inc(v___y_619_);
v___x_629_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_629_, 0, v___y_619_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = 0;
if (v_isShared_617_ == 0)
{
lean_ctor_set_tag(v___x_616_, 6);
lean_ctor_set(v___x_616_, 0, v___x_629_);
v___x_632_ = v___x_616_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_629_);
v___x_632_ = v_reuseFailAlloc_634_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; 
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*1, v___x_630_);
v___x_633_ = l_Repr_addAppParen(v___x_632_, v_prec_541_);
return v___x_633_;
}
}
}
}
case 5:
{
lean_object* v_string_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref(v_localinst_542_);
lean_dec_ref(v_inst_539_);
v_string_640_ = lean_ctor_get(v_x_540_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_660_ == 0)
{
v___x_642_ = v_x_540_;
v_isShared_643_ = v_isSharedCheck_660_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_string_640_);
lean_dec(v_x_540_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_660_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___y_645_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(1024u);
v___x_657_ = lean_nat_dec_le(v___x_656_, v_prec_541_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
v___x_658_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_645_ = v___x_658_;
goto v___jp_644_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_645_ = v___x_659_;
goto v___jp_644_;
}
v___jp_644_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_646_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__17));
v___x_647_ = l_String_quote(v_string_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 3);
lean_ctor_set(v___x_642_, 0, v___x_647_);
v___x_649_ = v___x_642_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_655_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_646_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
lean_inc(v___y_645_);
v___x_651_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_651_, 0, v___y_645_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = 0;
v___x_653_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*1, v___x_652_);
v___x_654_ = l_Repr_addAppParen(v___x_653_, v_prec_541_);
return v___x_654_;
}
}
}
}
case 6:
{
lean_object* v_content_661_; lean_object* v_url_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_inst_539_);
v_content_661_ = lean_ctor_get(v_x_540_, 0);
v_url_662_ = lean_ctor_get(v_x_540_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_686_ == 0)
{
v___x_664_ = v_x_540_;
v_isShared_665_ = v_isSharedCheck_686_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_url_662_);
lean_inc(v_content_661_);
lean_dec(v_x_540_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_686_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___y_667_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(1024u);
v___x_683_ = lean_nat_dec_le(v___x_682_, v_prec_541_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
v___x_684_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_667_ = v___x_684_;
goto v___jp_666_;
}
else
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_667_ = v___x_685_;
goto v___jp_666_;
}
v___jp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_668_ = lean_box(1);
v___x_669_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__20));
v___x_670_ = l_Array_repr___redArg(v_localinst_542_, v_content_661_);
if (v_isShared_665_ == 0)
{
lean_ctor_set_tag(v___x_664_, 5);
lean_ctor_set(v___x_664_, 1, v___x_670_);
lean_ctor_set(v___x_664_, 0, v___x_669_);
v___x_672_ = v___x_664_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_670_);
v___x_672_ = v_reuseFailAlloc_681_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_668_);
v___x_674_ = l_String_quote(v_url_662_);
v___x_675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
v___x_676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_673_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
lean_inc(v___y_667_);
v___x_677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_677_, 0, v___y_667_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = 0;
v___x_679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*1, v___x_678_);
v___x_680_ = l_Repr_addAppParen(v___x_679_, v_prec_541_);
return v___x_680_;
}
}
}
}
case 7:
{
lean_object* v_name_687_; lean_object* v_content_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v_inst_539_);
v_name_687_ = lean_ctor_get(v_x_540_, 0);
v_content_688_ = lean_ctor_get(v_x_540_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_712_ == 0)
{
v___x_690_ = v_x_540_;
v_isShared_691_ = v_isSharedCheck_712_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_content_688_);
lean_inc(v_name_687_);
lean_dec(v_x_540_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_712_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___y_693_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = lean_unsigned_to_nat(1024u);
v___x_709_ = lean_nat_dec_le(v___x_708_, v_prec_541_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_693_ = v___x_710_;
goto v___jp_692_;
}
else
{
lean_object* v___x_711_; 
v___x_711_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_693_ = v___x_711_;
goto v___jp_692_;
}
v___jp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_694_ = lean_box(1);
v___x_695_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__23));
v___x_696_ = l_String_quote(v_name_687_);
v___x_697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 5);
lean_ctor_set(v___x_690_, 1, v___x_697_);
lean_ctor_set(v___x_690_, 0, v___x_695_);
v___x_699_ = v___x_690_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_707_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_694_);
v___x_701_ = l_Array_repr___redArg(v_localinst_542_, v_content_688_);
v___x_702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
lean_inc(v___y_693_);
v___x_703_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_703_, 0, v___y_693_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = 0;
v___x_705_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*1, v___x_704_);
v___x_706_ = l_Repr_addAppParen(v___x_705_, v_prec_541_);
return v___x_706_;
}
}
}
}
case 8:
{
lean_object* v_alt_713_; lean_object* v_url_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v_localinst_542_);
lean_dec_ref(v_inst_539_);
v_alt_713_ = lean_ctor_get(v_x_540_, 0);
v_url_714_ = lean_ctor_get(v_x_540_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_739_ == 0)
{
v___x_716_ = v_x_540_;
v_isShared_717_ = v_isSharedCheck_739_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_url_714_);
lean_inc(v_alt_713_);
lean_dec(v_x_540_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_739_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___y_719_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = lean_unsigned_to_nat(1024u);
v___x_736_ = lean_nat_dec_le(v___x_735_, v_prec_541_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
v___x_737_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_719_ = v___x_737_;
goto v___jp_718_;
}
else
{
lean_object* v___x_738_; 
v___x_738_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_719_ = v___x_738_;
goto v___jp_718_;
}
v___jp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_720_ = lean_box(1);
v___x_721_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__26));
v___x_722_ = l_String_quote(v_alt_713_);
v___x_723_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 5);
lean_ctor_set(v___x_716_, 1, v___x_723_);
lean_ctor_set(v___x_716_, 0, v___x_721_);
v___x_725_ = v___x_716_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_734_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___x_720_);
v___x_727_ = l_String_quote(v_url_714_);
v___x_728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
v___x_729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_726_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
lean_inc(v___y_719_);
v___x_730_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_730_, 0, v___y_719_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = 0;
v___x_732_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*1, v___x_731_);
v___x_733_ = l_Repr_addAppParen(v___x_732_, v_prec_541_);
return v___x_733_;
}
}
}
}
case 9:
{
lean_object* v_content_740_; lean_object* v___y_742_; lean_object* v___x_750_; uint8_t v___x_751_; 
lean_dec_ref(v_inst_539_);
v_content_740_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_content_740_);
lean_dec_ref(v_x_540_);
v___x_750_ = lean_unsigned_to_nat(1024u);
v___x_751_ = lean_nat_dec_le(v___x_750_, v_prec_541_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_742_ = v___x_752_;
goto v___jp_741_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_742_ = v___x_753_;
goto v___jp_741_;
}
v___jp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_743_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__29));
v___x_744_ = l_Array_repr___redArg(v_localinst_542_, v_content_740_);
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_inc(v___y_742_);
v___x_746_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_746_, 0, v___y_742_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = 0;
v___x_748_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*1, v___x_747_);
v___x_749_ = l_Repr_addAppParen(v___x_748_, v_prec_541_);
return v___x_749_;
}
}
default: 
{
lean_object* v_container_754_; lean_object* v_content_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_779_; 
v_container_754_ = lean_ctor_get(v_x_540_, 0);
v_content_755_ = lean_ctor_get(v_x_540_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_779_ == 0)
{
v___x_757_ = v_x_540_;
v_isShared_758_ = v_isSharedCheck_779_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_content_755_);
lean_inc(v_container_754_);
lean_dec(v_x_540_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_779_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___y_760_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_unsigned_to_nat(1024u);
v___x_776_ = lean_nat_dec_le(v___x_775_, v_prec_541_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_760_ = v___x_777_;
goto v___jp_759_;
}
else
{
lean_object* v___x_778_; 
v___x_778_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_760_ = v___x_778_;
goto v___jp_759_;
}
v___jp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_761_ = lean_box(1);
v___x_762_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__32));
v___x_763_ = lean_unsigned_to_nat(1024u);
v___x_764_ = lean_apply_2(v_inst_539_, v_container_754_, v___x_763_);
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 5);
lean_ctor_set(v___x_757_, 1, v___x_764_);
lean_ctor_set(v___x_757_, 0, v___x_762_);
v___x_766_ = v___x_757_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_764_);
v___x_766_ = v_reuseFailAlloc_774_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_761_);
v___x_768_ = l_Array_repr___redArg(v_localinst_542_, v_content_755_);
v___x_769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
lean_inc(v___y_760_);
v___x_770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_770_, 0, v___y_760_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = 0;
v___x_772_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*1, v___x_771_);
v___x_773_ = l_Repr_addAppParen(v___x_772_, v_prec_541_);
return v___x_773_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr(lean_object* v_i_780_, lean_object* v_inst_781_, lean_object* v_x_782_, lean_object* v_prec_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_781_, v_x_782_, v_prec_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___boxed(lean_object* v_i_785_, lean_object* v_inst_786_, lean_object* v_x_787_, lean_object* v_prec_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Doc_instReprInline_repr(v_i_785_, v_inst_786_, v_x_787_, v_prec_788_);
lean_dec(v_prec_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline___redArg(lean_object* v_inst_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_791_, 0, lean_box(0));
lean_closure_set(v___x_791_, 1, v_inst_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline(lean_object* v_i_792_, lean_object* v_inst_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_794_, 0, lean_box(0));
lean_closure_set(v___x_794_, 1, v_inst_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default(lean_object* v_i_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = ((lean_object*)(l_Lean_Doc_instInhabitedInline_default___closed__1));
return v___x_799_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedInline___closed__0(void){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Doc_instInhabitedInline_default(lean_box(0));
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline(lean_object* v_a_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline___closed__0, &l_Lean_Doc_instInhabitedInline___closed__0_once, _init_l_Lean_Doc_instInhabitedInline___closed__0);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg(lean_object* v_x_803_){
_start:
{
lean_inc_ref(v_x_803_);
return v_x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg___boxed(lean_object* v_x_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Doc_Inline_cast___redArg(v_x_804_);
lean_dec_ref(v_x_804_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast(lean_object* v_i_806_, lean_object* v_i_x27_807_, lean_object* v_inlines__eq_808_, lean_object* v_x_809_){
_start:
{
lean_inc_ref(v_x_809_);
return v_x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___boxed(lean_object* v_i_810_, lean_object* v_i_x27_811_, lean_object* v_inlines__eq_812_, lean_object* v_x_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Doc_Inline_cast(v_i_810_, v_i_x27_811_, v_inlines__eq_812_, v_x_813_);
lean_dec_ref(v_x_813_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___lam__0(lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
if (lean_obj_tag(v_x_815_) == 9)
{
lean_object* v_content_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_content_817_ = lean_ctor_get(v_x_815_, 0);
v___x_818_ = lean_array_get_size(v_content_817_);
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_nat_dec_eq(v___x_818_, v___x_819_);
if (v___x_820_ == 0)
{
if (lean_obj_tag(v_x_816_) == 9)
{
lean_object* v_content_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_831_; 
v_content_821_ = lean_ctor_get(v_x_816_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v_x_816_);
if (v_isSharedCheck_831_ == 0)
{
v___x_823_ = v_x_816_;
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_content_821_);
lean_dec(v_x_816_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = lean_array_get_size(v_content_821_);
v___x_826_ = lean_nat_dec_eq(v___x_825_, v___x_819_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_inc_ref(v_content_817_);
lean_dec_ref(v_x_815_);
v___x_827_ = l_Array_append___redArg(v_content_817_, v_content_821_);
lean_dec_ref(v_content_821_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_827_);
v___x_829_ = v___x_823_;
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
else
{
lean_del_object(v___x_823_);
lean_dec_ref(v_content_821_);
return v_x_815_;
}
}
}
else
{
lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_839_; 
lean_inc_ref(v_content_817_);
v_isSharedCheck_839_ = !lean_is_exclusive(v_x_815_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v_x_815_, 0);
lean_dec(v_unused_840_);
v___x_833_ = v_x_815_;
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
else
{
lean_dec(v_x_815_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_array_push(v_content_817_, v_x_816_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_dec_ref(v_x_815_);
return v_x_816_;
}
}
else
{
if (lean_obj_tag(v_x_816_) == 9)
{
lean_object* v_content_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_855_; 
v_content_841_ = lean_ctor_get(v_x_816_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v_x_816_);
if (v_isSharedCheck_855_ == 0)
{
v___x_843_ = v_x_816_;
v_isShared_844_ = v_isSharedCheck_855_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_content_841_);
lean_dec(v_x_816_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_855_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_845_ = lean_array_get_size(v_content_841_);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_nat_dec_eq(v___x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_mk_empty_array_with_capacity(v___x_848_);
v___x_850_ = lean_array_push(v___x_849_, v_x_815_);
v___x_851_ = l_Array_append___redArg(v___x_850_, v_content_841_);
lean_dec_ref(v_content_841_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_851_);
v___x_853_ = v___x_843_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
else
{
lean_del_object(v___x_843_);
lean_dec_ref(v_content_841_);
return v_x_815_;
}
}
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_856_ = lean_unsigned_to_nat(2u);
v___x_857_ = lean_mk_empty_array_with_capacity(v___x_856_);
v___x_858_ = lean_array_push(v___x_857_, v_x_815_);
v___x_859_ = lean_array_push(v___x_858_, v_x_816_);
v___x_860_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline(lean_object* v_i_862_){
_start:
{
lean_object* v___f_863_; 
v___f_863_ = ((lean_object*)(l_Lean_Doc_instAppendInline___closed__0));
return v___f_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty(lean_object* v_i_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = ((lean_object*)(l_Lean_Doc_Inline_empty___closed__1));
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(12u);
v___x_884_ = lean_nat_to_int(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__0));
v___x_887_ = lean_string_length(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9);
v___x_889_ = lean_nat_to_int(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___redArg(lean_object* v_inst_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_896_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__6));
v___x_897_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_898_ = l_Array_repr___redArg(v_inst_894_, v_x_895_);
v___x_899_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = 0;
v___x_901_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*1, v___x_900_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_896_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_904_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_902_);
v___x_906_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_903_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set_uint8(v___x_909_, sizeof(void*)*1, v___x_900_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr(lean_object* v_00_u03b1_910_, lean_object* v_inst_911_, lean_object* v_x_912_, lean_object* v_prec_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Doc_instReprListItem_repr___redArg(v_inst_911_, v_x_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___boxed(lean_object* v_00_u03b1_915_, lean_object* v_inst_916_, lean_object* v_x_917_, lean_object* v_prec_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Doc_instReprListItem_repr(v_00_u03b1_915_, v_inst_916_, v_x_917_, v_prec_918_);
lean_dec(v_prec_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem___redArg(lean_object* v_inst_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_921_, 0, lean_box(0));
lean_closure_set(v___x_921_, 1, v_inst_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem(lean_object* v_00_u03b1_922_, lean_object* v_inst_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_924_, 0, lean_box(0));
lean_closure_set(v___x_924_, 1, v_inst_923_);
return v___x_924_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq___redArg(lean_object* v_inst_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_928_ = lean_array_get_size(v_x_926_);
v___x_929_ = lean_array_get_size(v_x_927_);
v___x_930_ = lean_nat_dec_eq(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_dec_ref(v_inst_925_);
return v___x_930_;
}
else
{
uint8_t v___x_931_; 
v___x_931_ = l_Array_isEqvAux___redArg(v_x_926_, v_x_927_, v_inst_925_, v___x_928_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___redArg___boxed(lean_object* v_inst_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
uint8_t v_res_935_; lean_object* v_r_936_; 
v_res_935_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_932_, v_x_933_, v_x_934_);
lean_dec_ref(v_x_934_);
lean_dec_ref(v_x_933_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq(lean_object* v_00_u03b1_937_, lean_object* v_inst_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_938_, v_x_939_, v_x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___boxed(lean_object* v_00_u03b1_942_, lean_object* v_inst_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
uint8_t v_res_946_; lean_object* v_r_947_; 
v_res_946_ = l_Lean_Doc_instBEqListItem_beq(v_00_u03b1_942_, v_inst_943_, v_x_944_, v_x_945_);
lean_dec_ref(v_x_945_);
lean_dec_ref(v_x_944_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem___redArg(lean_object* v_inst_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_949_, 0, lean_box(0));
lean_closure_set(v___x_949_, 1, v_inst_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem(lean_object* v_00_u03b1_950_, lean_object* v_inst_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_952_, 0, lean_box(0));
lean_closure_set(v___x_952_, 1, v_inst_951_);
return v___x_952_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord___redArg(lean_object* v_inst_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = l_Array_compareLex___redArg(v_inst_953_, v_x_954_, v_x_955_);
if (v___x_956_ == 1)
{
return v___x_956_;
}
else
{
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___redArg___boxed(lean_object* v_inst_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
uint8_t v_res_960_; lean_object* v_r_961_; 
v_res_960_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_957_, v_x_958_, v_x_959_);
lean_dec_ref(v_x_959_);
lean_dec_ref(v_x_958_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord(lean_object* v_00_u03b1_962_, lean_object* v_inst_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_963_, v_x_964_, v_x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___boxed(lean_object* v_00_u03b1_967_, lean_object* v_inst_968_, lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
uint8_t v_res_971_; lean_object* v_r_972_; 
v_res_971_ = l_Lean_Doc_instOrdListItem_ord(v_00_u03b1_967_, v_inst_968_, v_x_969_, v_x_970_);
lean_dec_ref(v_x_970_);
lean_dec_ref(v_x_969_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem___redArg(lean_object* v_inst_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_974_, 0, lean_box(0));
lean_closure_set(v___x_974_, 1, v_inst_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem(lean_object* v_00_u03b1_975_, lean_object* v_inst_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_977_, 0, lean_box(0));
lean_closure_set(v___x_977_, 1, v_inst_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default(lean_object* v_00_u03b1_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l_Lean_Doc_instInhabitedListItem_default___closed__0));
return v___x_981_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedListItem___closed__0(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Doc_instInhabitedListItem_default(lean_box(0));
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem(lean_object* v_a_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem___closed__0, &l_Lean_Doc_instInhabitedListItem___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem___closed__0);
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
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default(lean_object* v_00_u03b1_1147_, lean_object* v_00_u03b2_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = ((lean_object*)(l_Lean_Doc_instInhabitedDescItem_default___closed__0));
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedDescItem___closed__0(void){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Doc_instInhabitedDescItem_default(lean_box(0), lean_box(0));
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem(lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem___closed__0, &l_Lean_Doc_instInhabitedDescItem___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem___closed__0);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg(lean_object* v_x_1154_){
_start:
{
switch(lean_obj_tag(v_x_1154_))
{
case 0:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
return v___x_1155_;
}
case 1:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
return v___x_1156_;
}
case 2:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_unsigned_to_nat(2u);
return v___x_1157_;
}
case 3:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_unsigned_to_nat(3u);
return v___x_1158_;
}
case 4:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_unsigned_to_nat(4u);
return v___x_1159_;
}
case 5:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_unsigned_to_nat(5u);
return v___x_1160_;
}
case 6:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_unsigned_to_nat(6u);
return v___x_1161_;
}
default: 
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_unsigned_to_nat(7u);
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg___boxed(lean_object* v_x_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1163_);
lean_dec_ref(v_x_1163_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx(lean_object* v_i_1165_, lean_object* v_b_1166_, lean_object* v_x_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___boxed(lean_object* v_i_1169_, lean_object* v_b_1170_, lean_object* v_x_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Doc_Block_ctorIdx(v_i_1169_, v_b_1170_, v_x_1171_);
lean_dec_ref(v_x_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___redArg(lean_object* v_t_1173_, lean_object* v_k_1174_){
_start:
{
switch(lean_obj_tag(v_t_1173_))
{
case 3:
{
lean_object* v_start_1175_; lean_object* v_items_1176_; lean_object* v___x_1177_; 
v_start_1175_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_start_1175_);
v_items_1176_ = lean_ctor_get(v_t_1173_, 1);
lean_inc_ref(v_items_1176_);
lean_dec_ref(v_t_1173_);
v___x_1177_ = lean_apply_2(v_k_1174_, v_start_1175_, v_items_1176_);
return v___x_1177_;
}
case 7:
{
lean_object* v_container_1178_; lean_object* v_content_1179_; lean_object* v___x_1180_; 
v_container_1178_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_container_1178_);
v_content_1179_ = lean_ctor_get(v_t_1173_, 1);
lean_inc_ref(v_content_1179_);
lean_dec_ref(v_t_1173_);
v___x_1180_ = lean_apply_2(v_k_1174_, v_container_1178_, v_content_1179_);
return v___x_1180_;
}
default: 
{
lean_object* v_contents_1181_; lean_object* v___x_1182_; 
v_contents_1181_ = lean_ctor_get(v_t_1173_, 0);
lean_inc_ref(v_contents_1181_);
lean_dec_ref(v_t_1173_);
v___x_1182_ = lean_apply_1(v_k_1174_, v_contents_1181_);
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim(lean_object* v_i_1183_, lean_object* v_b_1184_, lean_object* v_motive__1_1185_, lean_object* v_ctorIdx_1186_, lean_object* v_t_1187_, lean_object* v_h_1188_, lean_object* v_k_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1187_, v_k_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___boxed(lean_object* v_i_1191_, lean_object* v_b_1192_, lean_object* v_motive__1_1193_, lean_object* v_ctorIdx_1194_, lean_object* v_t_1195_, lean_object* v_h_1196_, lean_object* v_k_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Doc_Block_ctorElim(v_i_1191_, v_b_1192_, v_motive__1_1193_, v_ctorIdx_1194_, v_t_1195_, v_h_1196_, v_k_1197_);
lean_dec(v_ctorIdx_1194_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim___redArg(lean_object* v_t_1199_, lean_object* v_para_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1199_, v_para_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim(lean_object* v_i_1202_, lean_object* v_b_1203_, lean_object* v_motive__1_1204_, lean_object* v_t_1205_, lean_object* v_h_1206_, lean_object* v_para_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1205_, v_para_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim___redArg(lean_object* v_t_1209_, lean_object* v_code_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1209_, v_code_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim(lean_object* v_i_1212_, lean_object* v_b_1213_, lean_object* v_motive__1_1214_, lean_object* v_t_1215_, lean_object* v_h_1216_, lean_object* v_code_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1215_, v_code_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim___redArg(lean_object* v_t_1219_, lean_object* v_ul_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1219_, v_ul_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim(lean_object* v_i_1222_, lean_object* v_b_1223_, lean_object* v_motive__1_1224_, lean_object* v_t_1225_, lean_object* v_h_1226_, lean_object* v_ul_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1225_, v_ul_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim___redArg(lean_object* v_t_1229_, lean_object* v_ol_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1229_, v_ol_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim(lean_object* v_i_1232_, lean_object* v_b_1233_, lean_object* v_motive__1_1234_, lean_object* v_t_1235_, lean_object* v_h_1236_, lean_object* v_ol_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1235_, v_ol_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim___redArg(lean_object* v_t_1239_, lean_object* v_dl_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1239_, v_dl_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim(lean_object* v_i_1242_, lean_object* v_b_1243_, lean_object* v_motive__1_1244_, lean_object* v_t_1245_, lean_object* v_h_1246_, lean_object* v_dl_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1245_, v_dl_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim___redArg(lean_object* v_t_1249_, lean_object* v_blockquote_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1249_, v_blockquote_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim(lean_object* v_i_1252_, lean_object* v_b_1253_, lean_object* v_motive__1_1254_, lean_object* v_t_1255_, lean_object* v_h_1256_, lean_object* v_blockquote_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1255_, v_blockquote_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim___redArg(lean_object* v_t_1259_, lean_object* v_concat_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1259_, v_concat_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim(lean_object* v_i_1262_, lean_object* v_b_1263_, lean_object* v_motive__1_1264_, lean_object* v_t_1265_, lean_object* v_h_1266_, lean_object* v_concat_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1265_, v_concat_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim___redArg(lean_object* v_t_1269_, lean_object* v_other_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1269_, v_other_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim(lean_object* v_i_1272_, lean_object* v_b_1273_, lean_object* v_motive__1_1274_, lean_object* v_t_1275_, lean_object* v_h_1276_, lean_object* v_other_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1275_, v_other_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___redArg___boxed(lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1279_, v_inst_1280_, v_x_1281_, v_x_1282_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq___redArg(lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
lean_object* v_localinst_1289_; lean_object* v_a_1291_; lean_object* v_b_1292_; 
lean_inc_ref(v_inst_1286_);
lean_inc_ref(v_inst_1285_);
v_localinst_1289_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1289_, 0, v_inst_1285_);
lean_closure_set(v_localinst_1289_, 1, v_inst_1286_);
switch(lean_obj_tag(v_x_1287_))
{
case 0:
{
lean_dec_ref(v_localinst_1289_);
lean_dec_ref(v_inst_1286_);
if (lean_obj_tag(v_x_1288_) == 0)
{
lean_object* v_contents_1297_; lean_object* v_contents_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_contents_1297_ = lean_ctor_get(v_x_1287_, 0);
lean_inc_ref(v_contents_1297_);
lean_dec_ref(v_x_1287_);
v_contents_1298_ = lean_ctor_get(v_x_1288_, 0);
lean_inc_ref(v_contents_1298_);
lean_dec_ref(v_x_1288_);
v___x_1299_ = lean_array_get_size(v_contents_1297_);
v___x_1300_ = lean_array_get_size(v_contents_1298_);
v___x_1301_ = lean_nat_dec_eq(v___x_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_dec_ref(v_contents_1298_);
lean_dec_ref(v_contents_1297_);
lean_dec_ref(v_inst_1285_);
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1302_, 0, lean_box(0));
lean_closure_set(v___x_1302_, 1, v_inst_1285_);
v___x_1303_ = l_Array_isEqvAux___redArg(v_contents_1297_, v_contents_1298_, v___x_1302_, v___x_1299_);
lean_dec_ref(v_contents_1298_);
lean_dec_ref(v_contents_1297_);
return v___x_1303_;
}
}
else
{
uint8_t v___x_1304_; 
lean_dec_ref(v_x_1287_);
lean_dec_ref(v_x_1288_);
lean_dec_ref(v_inst_1285_);
v___x_1304_ = 0;
return v___x_1304_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1289_);
lean_dec_ref(v_inst_1286_);
lean_dec_ref(v_inst_1285_);
if (lean_obj_tag(v_x_1288_) == 1)
{
lean_object* v_content_1305_; lean_object* v_content_1306_; uint8_t v___x_1307_; 
v_content_1305_ = lean_ctor_get(v_x_1287_, 0);
lean_inc_ref(v_content_1305_);
lean_dec_ref(v_x_1287_);
v_content_1306_ = lean_ctor_get(v_x_1288_, 0);
lean_inc_ref(v_content_1306_);
lean_dec_ref(v_x_1288_);
v___x_1307_ = lean_string_dec_eq(v_content_1305_, v_content_1306_);
lean_dec_ref(v_content_1306_);
lean_dec_ref(v_content_1305_);
return v___x_1307_;
}
else
{
uint8_t v___x_1308_; 
lean_dec_ref(v_x_1287_);
lean_dec_ref(v_x_1288_);
v___x_1308_ = 0;
return v___x_1308_;
}
}
case 2:
{
lean_dec_ref(v_inst_1286_);
lean_dec_ref(v_inst_1285_);
if (lean_obj_tag(v_x_1288_) == 2)
{
lean_object* v_items_1309_; lean_object* v_items_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_items_1309_ = lean_ctor_get(v_x_1287_, 0);
lean_inc_ref(v_items_1309_);
lean_dec_ref(v_x_1287_);
v_items_1310_ = lean_ctor_get(v_x_1288_, 0);
lean_inc_ref(v_items_1310_);
lean_dec_ref(v_x_1288_);
v___x_1311_ = lean_array_get_size(v_items_1309_);
v___x_1312_ = lean_array_get_size(v_items_1310_);
v___x_1313_ = lean_nat_dec_eq(v___x_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_dec_ref(v_items_1310_);
lean_dec_ref(v_items_1309_);
lean_dec_ref(v_localinst_1289_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1314_, 0, lean_box(0));
lean_closure_set(v___x_1314_, 1, v_localinst_1289_);
v___x_1315_ = l_Array_isEqvAux___redArg(v_items_1309_, v_items_1310_, v___x_1314_, v___x_1311_);
lean_dec_ref(v_items_1310_);
lean_dec_ref(v_items_1309_);
return v___x_1315_;
}
}
else
{
uint8_t v___x_1316_; 
lean_dec_ref(v_x_1287_);
lean_dec_ref(v_localinst_1289_);
lean_dec_ref(v_x_1288_);
v___x_1316_ = 0;
return v___x_1316_;
}
}
case 3:
{
lean_dec_ref(v_inst_1286_);
lean_dec_ref(v_inst_1285_);
if (lean_obj_tag(v_x_1288_) == 3)
{
lean_object* v_start_1317_; lean_object* v_items_1318_; lean_object* v_start_1319_; lean_object* v_items_1320_; uint8_t v___x_1321_; 
v_start_1317_ = lean_ctor_get(v_x_1287_, 0);
lean_inc(v_start_1317_);
v_items_1318_ = lean_ctor_get(v_x_1287_, 1);
lean_inc_ref(v_items_1318_);
lean_dec_ref(v_x_1287_);
v_start_1319_ = lean_ctor_get(v_x_1288_, 0);
lean_inc(v_start_1319_);
v_items_1320_ = lean_ctor_get(v_x_1288_, 1);
lean_inc_ref(v_items_1320_);
lean_dec_ref(v_x_1288_);
v___x_1321_ = lean_int_dec_eq(v_start_1317_, v_start_1319_);
lean_dec(v_start_1319_);
lean_dec(v_start_1317_);
if (v___x_1321_ == 0)
{
lean_dec_ref(v_items_1320_);
lean_dec_ref(v_items_1318_);
lean_dec_ref(v_localinst_1289_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1322_ = lean_array_get_size(v_items_1318_);
v___x_1323_ = lean_array_get_size(v_items_1320_);
v___x_1324_ = lean_nat_dec_eq(v___x_1322_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_dec_ref(v_items_1320_);
lean_dec_ref(v_items_1318_);
lean_dec_ref(v_localinst_1289_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1325_, 0, lean_box(0));
lean_closure_set(v___x_1325_, 1, v_localinst_1289_);
v___x_1326_ = l_Array_isEqvAux___redArg(v_items_1318_, v_items_1320_, v___x_1325_, v___x_1322_);
lean_dec_ref(v_items_1320_);
lean_dec_ref(v_items_1318_);
return v___x_1326_;
}
}
}
else
{
uint8_t v___x_1327_; 
lean_dec_ref(v_x_1287_);
lean_dec_ref(v_localinst_1289_);
lean_dec_ref(v_x_1288_);
v___x_1327_ = 0;
return v___x_1327_;
}
}
case 4:
{
lean_dec_ref(v_inst_1286_);
if (lean_obj_tag(v_x_1288_) == 4)
{
lean_object* v_items_1328_; lean_object* v_items_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_items_1328_ = lean_ctor_get(v_x_1287_, 0);
lean_inc_ref(v_items_1328_);
lean_dec_ref(v_x_1287_);
v_items_1329_ = lean_ctor_get(v_x_1288_, 0);
lean_inc_ref(v_items_1329_);
lean_dec_ref(v_x_1288_);
v___x_1330_ = lean_array_get_size(v_items_1328_);
v___x_1331_ = lean_array_get_size(v_items_1329_);
v___x_1332_ = lean_nat_dec_eq(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_dec_ref(v_items_1329_);
lean_dec_ref(v_items_1328_);
lean_dec_ref(v_localinst_1289_);
lean_dec_ref(v_inst_1285_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1333_, 0, lean_box(0));
lean_closure_set(v___x_1333_, 1, v_inst_1285_);
v___x_1334_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1334_, 0, lean_box(0));
lean_closure_set(v___x_1334_, 1, lean_box(0));
lean_closure_set(v___x_1334_, 2, v___x_1333_);
lean_closure_set(v___x_1334_, 3, v_localinst_1289_);
v___x_1335_ = l_Array_isEqvAux___redArg(v_items_1328_, v_items_1329_, v___x_1334_, v___x_1330_);
lean_dec_ref(v_items_1329_);
lean_dec_ref(v_items_1328_);
return v___x_1335_;
}
}
else
{
uint8_t v___x_1336_; 
lean_dec_ref(v_x_1287_);
lean_dec_ref(v_localinst_1289_);
lean_dec_ref(v_x_1288_);
lean_dec_ref(v_inst_1285_);
v___x_1336_ = 0;
return v___x_1336_;
}
}
case 5:
{
lean_dec_ref(v_inst_1286_);
lean_dec_ref(v_inst_1285_);
if (lean_obj_tag(v_x_1288_) == 5)
{
lean_object* v_items_1337_; lean_object* v_items_1338_; 
v_items_1337_ = lean_ctor_get(v_x_1287_, 0);
lean_inc_ref(v_items_1337_);
lean_dec_ref(v_x_1287_);
v_items_1338_ = lean_ctor_get(v_x_1288_, 0);
lean_inc_ref(v_items_1338_);
lean_dec_ref(v_x_1288_);
v_a_1291_ = v_items_1337_;
v_b_1292_ = v_items_1338_;
goto v___jp_1290_;
}
else
{
uint8_t v___x_1339_; 
lean_dec_ref(v_x_1287_);
lean_dec_ref(v_localinst_1289_);
lean_dec_ref(v_x_1288_);
v___x_1339_ = 0;
return v___x_1339_;
}
}
case 6:
{
lean_dec_ref(v_inst_1286_);
lean_dec_ref(v_inst_1285_);
if (lean_obj_tag(v_x_1288_) == 6)
{
lean_object* v_content_1340_; lean_object* v_content_1341_; 
v_content_1340_ = lean_ctor_get(v_x_1287_, 0);
lean_inc_ref(v_content_1340_);
lean_dec_ref(v_x_1287_);
v_content_1341_ = lean_ctor_get(v_x_1288_, 0);
lean_inc_ref(v_content_1341_);
lean_dec_ref(v_x_1288_);
v_a_1291_ = v_content_1340_;
v_b_1292_ = v_content_1341_;
goto v___jp_1290_;
}
else
{
uint8_t v___x_1342_; 
lean_dec_ref(v_x_1287_);
lean_dec_ref(v_localinst_1289_);
lean_dec_ref(v_x_1288_);
v___x_1342_ = 0;
return v___x_1342_;
}
}
default: 
{
lean_dec_ref(v_inst_1285_);
if (lean_obj_tag(v_x_1288_) == 7)
{
lean_object* v_container_1343_; lean_object* v_content_1344_; lean_object* v_container_1345_; lean_object* v_content_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_container_1343_ = lean_ctor_get(v_x_1287_, 0);
lean_inc(v_container_1343_);
v_content_1344_ = lean_ctor_get(v_x_1287_, 1);
lean_inc_ref(v_content_1344_);
lean_dec_ref(v_x_1287_);
v_container_1345_ = lean_ctor_get(v_x_1288_, 0);
lean_inc(v_container_1345_);
v_content_1346_ = lean_ctor_get(v_x_1288_, 1);
lean_inc_ref(v_content_1346_);
lean_dec_ref(v_x_1288_);
v___x_1347_ = lean_apply_2(v_inst_1286_, v_container_1343_, v_container_1345_);
v___x_1348_ = lean_unbox(v___x_1347_);
if (v___x_1348_ == 0)
{
uint8_t v___x_1349_; 
lean_dec_ref(v_content_1346_);
lean_dec_ref(v_content_1344_);
lean_dec_ref(v_localinst_1289_);
v___x_1349_ = lean_unbox(v___x_1347_);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = lean_array_get_size(v_content_1344_);
v___x_1351_ = lean_array_get_size(v_content_1346_);
v___x_1352_ = lean_nat_dec_eq(v___x_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec_ref(v_content_1346_);
lean_dec_ref(v_content_1344_);
lean_dec_ref(v_localinst_1289_);
return v___x_1352_;
}
else
{
uint8_t v___x_1353_; 
v___x_1353_ = l_Array_isEqvAux___redArg(v_content_1344_, v_content_1346_, v_localinst_1289_, v___x_1350_);
lean_dec_ref(v_content_1346_);
lean_dec_ref(v_content_1344_);
return v___x_1353_;
}
}
}
else
{
uint8_t v___x_1354_; 
lean_dec_ref(v_x_1287_);
lean_dec_ref(v_localinst_1289_);
lean_dec_ref(v_x_1288_);
lean_dec_ref(v_inst_1286_);
v___x_1354_ = 0;
return v___x_1354_;
}
}
}
v___jp_1290_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1293_ = lean_array_get_size(v_a_1291_);
v___x_1294_ = lean_array_get_size(v_b_1292_);
v___x_1295_ = lean_nat_dec_eq(v___x_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_dec_ref(v_b_1292_);
lean_dec_ref(v_a_1291_);
lean_dec_ref(v_localinst_1289_);
return v___x_1295_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Array_isEqvAux___redArg(v_a_1291_, v_b_1292_, v_localinst_1289_, v___x_1293_);
lean_dec_ref(v_b_1292_);
lean_dec_ref(v_a_1291_);
return v___x_1296_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq(lean_object* v_i_1355_, lean_object* v_b_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_){
_start:
{
uint8_t v___x_1361_; 
v___x_1361_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1357_, v_inst_1358_, v_x_1359_, v_x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___boxed(lean_object* v_i_1362_, lean_object* v_b_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
uint8_t v_res_1368_; lean_object* v_r_1369_; 
v_res_1368_ = l_Lean_Doc_instBEqBlock_beq(v_i_1362_, v_b_1363_, v_inst_1364_, v_inst_1365_, v_x_1366_, v_x_1367_);
v_r_1369_ = lean_box(v_res_1368_);
return v_r_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock___redArg(lean_object* v_inst_1370_, lean_object* v_inst_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1372_, 0, lean_box(0));
lean_closure_set(v___x_1372_, 1, lean_box(0));
lean_closure_set(v___x_1372_, 2, v_inst_1370_);
lean_closure_set(v___x_1372_, 3, v_inst_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock(lean_object* v_i_1373_, lean_object* v_b_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1377_, 0, lean_box(0));
lean_closure_set(v___x_1377_, 1, lean_box(0));
lean_closure_set(v___x_1377_, 2, v_inst_1375_);
lean_closure_set(v___x_1377_, 3, v_inst_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___redArg___boxed(lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_){
_start:
{
uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_res_1382_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1378_, v_inst_1379_, v_x_1380_, v_x_1381_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord___redArg(lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v_localinst_1388_; lean_object* v_a_1390_; lean_object* v_b_1391_; 
lean_inc_ref(v_inst_1385_);
lean_inc_ref(v_inst_1384_);
v_localinst_1388_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1388_, 0, v_inst_1384_);
lean_closure_set(v_localinst_1388_, 1, v_inst_1385_);
switch(lean_obj_tag(v_x_1386_))
{
case 0:
{
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_inst_1385_);
switch(lean_obj_tag(v_x_1387_))
{
case 0:
{
lean_object* v_contents_1393_; lean_object* v_contents_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_contents_1393_ = lean_ctor_get(v_x_1386_, 0);
lean_inc_ref(v_contents_1393_);
lean_dec_ref(v_x_1386_);
v_contents_1394_ = lean_ctor_get(v_x_1387_, 0);
lean_inc_ref(v_contents_1394_);
lean_dec_ref(v_x_1387_);
v___x_1395_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1395_, 0, lean_box(0));
lean_closure_set(v___x_1395_, 1, v_inst_1384_);
v___x_1396_ = l_Array_compareLex___redArg(v___x_1395_, v_contents_1393_, v_contents_1394_);
lean_dec_ref(v_contents_1394_);
lean_dec_ref(v_contents_1393_);
if (v___x_1396_ == 1)
{
return v___x_1396_;
}
else
{
return v___x_1396_;
}
}
case 1:
{
uint8_t v___x_1397_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_inst_1384_);
v___x_1397_ = 0;
return v___x_1397_;
}
case 2:
{
uint8_t v___x_1398_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_inst_1384_);
v___x_1398_ = 0;
return v___x_1398_;
}
case 3:
{
uint8_t v___x_1399_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_inst_1384_);
v___x_1399_ = 0;
return v___x_1399_;
}
case 4:
{
uint8_t v___x_1400_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_inst_1384_);
v___x_1400_ = 0;
return v___x_1400_;
}
case 5:
{
uint8_t v___x_1401_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_inst_1384_);
v___x_1401_ = 0;
return v___x_1401_;
}
case 6:
{
uint8_t v___x_1402_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_inst_1384_);
v___x_1402_ = 0;
return v___x_1402_;
}
default: 
{
uint8_t v___x_1403_; 
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_inst_1384_);
v___x_1403_ = 0;
return v___x_1403_;
}
}
}
case 1:
{
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_inst_1385_);
lean_dec_ref(v_inst_1384_);
switch(lean_obj_tag(v_x_1387_))
{
case 0:
{
uint8_t v___x_1404_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
v___x_1404_ = 2;
return v___x_1404_;
}
case 1:
{
lean_object* v_content_1405_; lean_object* v_content_1406_; uint8_t v___x_1407_; 
v_content_1405_ = lean_ctor_get(v_x_1386_, 0);
lean_inc_ref(v_content_1405_);
lean_dec_ref(v_x_1386_);
v_content_1406_ = lean_ctor_get(v_x_1387_, 0);
lean_inc_ref(v_content_1406_);
lean_dec_ref(v_x_1387_);
v___x_1407_ = lean_string_dec_lt(v_content_1405_, v_content_1406_);
if (v___x_1407_ == 0)
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_string_dec_eq(v_content_1405_, v_content_1406_);
lean_dec_ref(v_content_1406_);
lean_dec_ref(v_content_1405_);
if (v___x_1408_ == 0)
{
uint8_t v___x_1409_; 
v___x_1409_ = 2;
return v___x_1409_;
}
else
{
uint8_t v___x_1410_; 
v___x_1410_ = 1;
return v___x_1410_;
}
}
else
{
uint8_t v___x_1411_; 
lean_dec_ref(v_content_1406_);
lean_dec_ref(v_content_1405_);
v___x_1411_ = 0;
return v___x_1411_;
}
}
case 2:
{
uint8_t v___x_1412_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
v___x_1412_ = 0;
return v___x_1412_;
}
case 3:
{
uint8_t v___x_1413_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
v___x_1413_ = 0;
return v___x_1413_;
}
case 4:
{
uint8_t v___x_1414_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
v___x_1414_ = 0;
return v___x_1414_;
}
case 5:
{
uint8_t v___x_1415_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
v___x_1415_ = 0;
return v___x_1415_;
}
case 6:
{
uint8_t v___x_1416_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
v___x_1416_ = 0;
return v___x_1416_;
}
default: 
{
uint8_t v___x_1417_; 
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_x_1387_);
v___x_1417_ = 0;
return v___x_1417_;
}
}
}
case 2:
{
lean_dec_ref(v_inst_1385_);
lean_dec_ref(v_inst_1384_);
switch(lean_obj_tag(v_x_1387_))
{
case 0:
{
uint8_t v___x_1418_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1418_ = 2;
return v___x_1418_;
}
case 1:
{
uint8_t v___x_1419_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1419_ = 2;
return v___x_1419_;
}
case 2:
{
lean_object* v_items_1420_; lean_object* v_items_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v_items_1420_ = lean_ctor_get(v_x_1386_, 0);
lean_inc_ref(v_items_1420_);
lean_dec_ref(v_x_1386_);
v_items_1421_ = lean_ctor_get(v_x_1387_, 0);
lean_inc_ref(v_items_1421_);
lean_dec_ref(v_x_1387_);
v___x_1422_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1422_, 0, lean_box(0));
lean_closure_set(v___x_1422_, 1, v_localinst_1388_);
v___x_1423_ = l_Array_compareLex___redArg(v___x_1422_, v_items_1420_, v_items_1421_);
lean_dec_ref(v_items_1421_);
lean_dec_ref(v_items_1420_);
if (v___x_1423_ == 1)
{
return v___x_1423_;
}
else
{
return v___x_1423_;
}
}
case 3:
{
uint8_t v___x_1424_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1424_ = 0;
return v___x_1424_;
}
case 4:
{
uint8_t v___x_1425_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1425_ = 0;
return v___x_1425_;
}
case 5:
{
uint8_t v___x_1426_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1426_ = 0;
return v___x_1426_;
}
case 6:
{
uint8_t v___x_1427_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1427_ = 0;
return v___x_1427_;
}
default: 
{
uint8_t v___x_1428_; 
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_x_1387_);
v___x_1428_ = 0;
return v___x_1428_;
}
}
}
case 3:
{
lean_dec_ref(v_inst_1385_);
lean_dec_ref(v_inst_1384_);
switch(lean_obj_tag(v_x_1387_))
{
case 0:
{
uint8_t v___x_1429_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1429_ = 2;
return v___x_1429_;
}
case 1:
{
uint8_t v___x_1430_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1430_ = 2;
return v___x_1430_;
}
case 2:
{
uint8_t v___x_1431_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1431_ = 2;
return v___x_1431_;
}
case 3:
{
lean_object* v_start_1432_; lean_object* v_items_1433_; lean_object* v_start_1434_; lean_object* v_items_1435_; uint8_t v___x_1436_; 
v_start_1432_ = lean_ctor_get(v_x_1386_, 0);
lean_inc(v_start_1432_);
v_items_1433_ = lean_ctor_get(v_x_1386_, 1);
lean_inc_ref(v_items_1433_);
lean_dec_ref(v_x_1386_);
v_start_1434_ = lean_ctor_get(v_x_1387_, 0);
lean_inc(v_start_1434_);
v_items_1435_ = lean_ctor_get(v_x_1387_, 1);
lean_inc_ref(v_items_1435_);
lean_dec_ref(v_x_1387_);
v___x_1436_ = lean_int_dec_lt(v_start_1432_, v_start_1434_);
if (v___x_1436_ == 0)
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_int_dec_eq(v_start_1432_, v_start_1434_);
lean_dec(v_start_1434_);
lean_dec(v_start_1432_);
if (v___x_1437_ == 0)
{
uint8_t v___x_1438_; 
lean_dec_ref(v_items_1435_);
lean_dec_ref(v_items_1433_);
lean_dec_ref(v_localinst_1388_);
v___x_1438_ = 2;
return v___x_1438_;
}
else
{
lean_object* v___x_1439_; uint8_t v___x_1440_; 
v___x_1439_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1439_, 0, lean_box(0));
lean_closure_set(v___x_1439_, 1, v_localinst_1388_);
v___x_1440_ = l_Array_compareLex___redArg(v___x_1439_, v_items_1433_, v_items_1435_);
lean_dec_ref(v_items_1435_);
lean_dec_ref(v_items_1433_);
if (v___x_1440_ == 1)
{
return v___x_1440_;
}
else
{
return v___x_1440_;
}
}
}
else
{
uint8_t v___x_1441_; 
lean_dec_ref(v_items_1435_);
lean_dec(v_start_1434_);
lean_dec_ref(v_items_1433_);
lean_dec(v_start_1432_);
lean_dec_ref(v_localinst_1388_);
v___x_1441_ = 0;
return v___x_1441_;
}
}
case 4:
{
uint8_t v___x_1442_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1442_ = 0;
return v___x_1442_;
}
case 5:
{
uint8_t v___x_1443_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1443_ = 0;
return v___x_1443_;
}
case 6:
{
uint8_t v___x_1444_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1444_ = 0;
return v___x_1444_;
}
default: 
{
uint8_t v___x_1445_; 
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_x_1387_);
v___x_1445_ = 0;
return v___x_1445_;
}
}
}
case 4:
{
lean_dec_ref(v_inst_1385_);
switch(lean_obj_tag(v_x_1387_))
{
case 0:
{
uint8_t v___x_1446_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_inst_1384_);
v___x_1446_ = 2;
return v___x_1446_;
}
case 1:
{
uint8_t v___x_1447_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_inst_1384_);
v___x_1447_ = 2;
return v___x_1447_;
}
case 2:
{
uint8_t v___x_1448_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_inst_1384_);
v___x_1448_ = 2;
return v___x_1448_;
}
case 3:
{
uint8_t v___x_1449_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_inst_1384_);
v___x_1449_ = 2;
return v___x_1449_;
}
case 4:
{
lean_object* v_items_1450_; lean_object* v_items_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_items_1450_ = lean_ctor_get(v_x_1386_, 0);
lean_inc_ref(v_items_1450_);
lean_dec_ref(v_x_1386_);
v_items_1451_ = lean_ctor_get(v_x_1387_, 0);
lean_inc_ref(v_items_1451_);
lean_dec_ref(v_x_1387_);
v___x_1452_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1452_, 0, lean_box(0));
lean_closure_set(v___x_1452_, 1, v_inst_1384_);
v___x_1453_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1453_, 0, lean_box(0));
lean_closure_set(v___x_1453_, 1, lean_box(0));
lean_closure_set(v___x_1453_, 2, v___x_1452_);
lean_closure_set(v___x_1453_, 3, v_localinst_1388_);
v___x_1454_ = l_Array_compareLex___redArg(v___x_1453_, v_items_1450_, v_items_1451_);
lean_dec_ref(v_items_1451_);
lean_dec_ref(v_items_1450_);
if (v___x_1454_ == 1)
{
return v___x_1454_;
}
else
{
return v___x_1454_;
}
}
case 5:
{
uint8_t v___x_1455_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_inst_1384_);
v___x_1455_ = 0;
return v___x_1455_;
}
case 6:
{
uint8_t v___x_1456_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_inst_1384_);
v___x_1456_ = 0;
return v___x_1456_;
}
default: 
{
uint8_t v___x_1457_; 
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_inst_1384_);
v___x_1457_ = 0;
return v___x_1457_;
}
}
}
case 5:
{
lean_dec_ref(v_inst_1385_);
lean_dec_ref(v_inst_1384_);
switch(lean_obj_tag(v_x_1387_))
{
case 0:
{
uint8_t v___x_1458_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1458_ = 2;
return v___x_1458_;
}
case 1:
{
uint8_t v___x_1459_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1459_ = 2;
return v___x_1459_;
}
case 2:
{
uint8_t v___x_1460_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1460_ = 2;
return v___x_1460_;
}
case 3:
{
uint8_t v___x_1461_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1461_ = 2;
return v___x_1461_;
}
case 4:
{
uint8_t v___x_1462_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1462_ = 2;
return v___x_1462_;
}
case 5:
{
lean_object* v_items_1463_; lean_object* v_items_1464_; 
v_items_1463_ = lean_ctor_get(v_x_1386_, 0);
lean_inc_ref(v_items_1463_);
lean_dec_ref(v_x_1386_);
v_items_1464_ = lean_ctor_get(v_x_1387_, 0);
lean_inc_ref(v_items_1464_);
lean_dec_ref(v_x_1387_);
v_a_1390_ = v_items_1463_;
v_b_1391_ = v_items_1464_;
goto v___jp_1389_;
}
case 6:
{
uint8_t v___x_1465_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1465_ = 0;
return v___x_1465_;
}
default: 
{
uint8_t v___x_1466_; 
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_x_1387_);
v___x_1466_ = 0;
return v___x_1466_;
}
}
}
case 6:
{
lean_dec_ref(v_inst_1385_);
lean_dec_ref(v_inst_1384_);
switch(lean_obj_tag(v_x_1387_))
{
case 0:
{
uint8_t v___x_1467_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1467_ = 2;
return v___x_1467_;
}
case 1:
{
uint8_t v___x_1468_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1468_ = 2;
return v___x_1468_;
}
case 2:
{
uint8_t v___x_1469_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1469_ = 2;
return v___x_1469_;
}
case 3:
{
uint8_t v___x_1470_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1470_ = 2;
return v___x_1470_;
}
case 4:
{
uint8_t v___x_1471_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1471_ = 2;
return v___x_1471_;
}
case 5:
{
uint8_t v___x_1472_; 
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
v___x_1472_ = 2;
return v___x_1472_;
}
case 6:
{
lean_object* v_content_1473_; lean_object* v_content_1474_; 
v_content_1473_ = lean_ctor_get(v_x_1386_, 0);
lean_inc_ref(v_content_1473_);
lean_dec_ref(v_x_1386_);
v_content_1474_ = lean_ctor_get(v_x_1387_, 0);
lean_inc_ref(v_content_1474_);
lean_dec_ref(v_x_1387_);
v_a_1390_ = v_content_1473_;
v_b_1391_ = v_content_1474_;
goto v___jp_1389_;
}
default: 
{
uint8_t v___x_1475_; 
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_x_1387_);
v___x_1475_ = 0;
return v___x_1475_;
}
}
}
default: 
{
lean_dec_ref(v_inst_1384_);
if (lean_obj_tag(v_x_1387_) == 7)
{
lean_object* v_container_1476_; lean_object* v_content_1477_; lean_object* v_container_1478_; lean_object* v_content_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v_container_1476_ = lean_ctor_get(v_x_1386_, 0);
lean_inc(v_container_1476_);
v_content_1477_ = lean_ctor_get(v_x_1386_, 1);
lean_inc_ref(v_content_1477_);
lean_dec_ref(v_x_1386_);
v_container_1478_ = lean_ctor_get(v_x_1387_, 0);
lean_inc(v_container_1478_);
v_content_1479_ = lean_ctor_get(v_x_1387_, 1);
lean_inc_ref(v_content_1479_);
lean_dec_ref(v_x_1387_);
v___x_1480_ = lean_apply_2(v_inst_1385_, v_container_1476_, v_container_1478_);
v___x_1481_ = lean_unbox(v___x_1480_);
if (v___x_1481_ == 1)
{
uint8_t v___x_1482_; 
v___x_1482_ = l_Array_compareLex___redArg(v_localinst_1388_, v_content_1477_, v_content_1479_);
lean_dec_ref(v_content_1479_);
lean_dec_ref(v_content_1477_);
if (v___x_1482_ == 1)
{
return v___x_1482_;
}
else
{
return v___x_1482_;
}
}
else
{
uint8_t v___x_1483_; 
lean_dec_ref(v_content_1479_);
lean_dec_ref(v_content_1477_);
lean_dec_ref(v_localinst_1388_);
v___x_1483_ = lean_unbox(v___x_1480_);
return v___x_1483_;
}
}
else
{
uint8_t v___x_1484_; 
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_localinst_1388_);
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_inst_1385_);
v___x_1484_ = 2;
return v___x_1484_;
}
}
}
v___jp_1389_:
{
uint8_t v___x_1392_; 
v___x_1392_ = l_Array_compareLex___redArg(v_localinst_1388_, v_a_1390_, v_b_1391_);
lean_dec_ref(v_b_1391_);
lean_dec_ref(v_a_1390_);
if (v___x_1392_ == 1)
{
return v___x_1392_;
}
else
{
return v___x_1392_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord(lean_object* v_i_1485_, lean_object* v_b_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_){
_start:
{
uint8_t v___x_1491_; 
v___x_1491_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1487_, v_inst_1488_, v_x_1489_, v_x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___boxed(lean_object* v_i_1492_, lean_object* v_b_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
uint8_t v_res_1498_; lean_object* v_r_1499_; 
v_res_1498_ = l_Lean_Doc_instOrdBlock_ord(v_i_1492_, v_b_1493_, v_inst_1494_, v_inst_1495_, v_x_1496_, v_x_1497_);
v_r_1499_ = lean_box(v_res_1498_);
return v_r_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock___redArg(lean_object* v_inst_1500_, lean_object* v_inst_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1502_, 0, lean_box(0));
lean_closure_set(v___x_1502_, 1, lean_box(0));
lean_closure_set(v___x_1502_, 2, v_inst_1500_);
lean_closure_set(v___x_1502_, 3, v_inst_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock(lean_object* v_i_1503_, lean_object* v_b_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1507_, 0, lean_box(0));
lean_closure_set(v___x_1507_, 1, lean_box(0));
lean_closure_set(v___x_1507_, 2, v_inst_1505_);
lean_closure_set(v___x_1507_, 3, v_inst_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = lean_nat_to_int(v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg___boxed(lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_x_1560_, lean_object* v_prec_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1558_, v_inst_1559_, v_x_1560_, v_prec_1561_);
lean_dec(v_prec_1561_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg(lean_object* v_inst_1563_, lean_object* v_inst_1564_, lean_object* v_x_1565_, lean_object* v_prec_1566_){
_start:
{
lean_object* v_localinst_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_inc_ref(v_inst_1564_);
lean_inc_ref(v_inst_1563_);
v_localinst_1567_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1567_, 0, v_inst_1563_);
lean_closure_set(v_localinst_1567_, 1, v_inst_1564_);
v___x_1568_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1568_, 0, lean_box(0));
lean_closure_set(v___x_1568_, 1, v_inst_1563_);
lean_inc_ref(v_localinst_1567_);
v___x_1569_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_1569_, 0, lean_box(0));
lean_closure_set(v___x_1569_, 1, v_localinst_1567_);
switch(lean_obj_tag(v_x_1565_))
{
case 0:
{
lean_object* v_contents_1570_; lean_object* v___y_1572_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
lean_dec_ref(v___x_1569_);
lean_dec_ref(v_localinst_1567_);
lean_dec_ref(v_inst_1564_);
v_contents_1570_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_contents_1570_);
lean_dec_ref(v_x_1565_);
v___x_1580_ = lean_unsigned_to_nat(1024u);
v___x_1581_ = lean_nat_dec_le(v___x_1580_, v_prec_1566_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1572_ = v___x_1582_;
goto v___jp_1571_;
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1572_ = v___x_1583_;
goto v___jp_1571_;
}
v___jp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1573_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__2));
v___x_1574_ = l_Array_repr___redArg(v___x_1568_, v_contents_1570_);
v___x_1575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
lean_inc(v___y_1572_);
v___x_1576_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___y_1572_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = 0;
v___x_1578_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*1, v___x_1577_);
v___x_1579_ = l_Repr_addAppParen(v___x_1578_, v_prec_1566_);
return v___x_1579_;
}
}
case 1:
{
lean_object* v_content_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v___x_1569_);
lean_dec_ref(v___x_1568_);
lean_dec_ref(v_localinst_1567_);
lean_dec_ref(v_inst_1564_);
v_content_1584_ = lean_ctor_get(v_x_1565_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_x_1565_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1586_ = v_x_1565_;
v_isShared_1587_ = v_isSharedCheck_1604_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_content_1584_);
lean_dec(v_x_1565_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1604_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___y_1589_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = lean_unsigned_to_nat(1024u);
v___x_1601_ = lean_nat_dec_le(v___x_1600_, v_prec_1566_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1589_ = v___x_1602_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1589_ = v___x_1603_;
goto v___jp_1588_;
}
v___jp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__5));
v___x_1591_ = l_String_quote(v_content_1584_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set_tag(v___x_1586_, 3);
lean_ctor_set(v___x_1586_, 0, v___x_1591_);
v___x_1593_ = v___x_1586_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1590_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
lean_inc(v___y_1589_);
v___x_1595_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___y_1589_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = 0;
v___x_1597_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*1, v___x_1596_);
v___x_1598_ = l_Repr_addAppParen(v___x_1597_, v_prec_1566_);
return v___x_1598_;
}
}
}
}
case 2:
{
lean_object* v_items_1605_; lean_object* v___y_1607_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
lean_dec_ref(v___x_1568_);
lean_dec_ref(v_localinst_1567_);
lean_dec_ref(v_inst_1564_);
v_items_1605_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_items_1605_);
lean_dec_ref(v_x_1565_);
v___x_1615_ = lean_unsigned_to_nat(1024u);
v___x_1616_ = lean_nat_dec_le(v___x_1615_, v_prec_1566_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1607_ = v___x_1617_;
goto v___jp_1606_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1607_ = v___x_1618_;
goto v___jp_1606_;
}
v___jp_1606_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1608_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__8));
v___x_1609_ = l_Array_repr___redArg(v___x_1569_, v_items_1605_);
v___x_1610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
lean_inc(v___y_1607_);
v___x_1611_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___y_1607_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = 0;
v___x_1613_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*1, v___x_1612_);
v___x_1614_ = l_Repr_addAppParen(v___x_1613_, v_prec_1566_);
return v___x_1614_;
}
}
case 3:
{
lean_object* v_start_1619_; lean_object* v_items_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1655_; 
lean_dec_ref(v___x_1568_);
lean_dec_ref(v_localinst_1567_);
lean_dec_ref(v_inst_1564_);
v_start_1619_ = lean_ctor_get(v_x_1565_, 0);
v_items_1620_ = lean_ctor_get(v_x_1565_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_x_1565_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1622_ = v_x_1565_;
v_isShared_1623_ = v_isSharedCheck_1655_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_items_1620_);
lean_inc(v_start_1619_);
lean_dec(v_x_1565_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1655_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1640_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = lean_unsigned_to_nat(1024u);
v___x_1652_ = lean_nat_dec_le(v___x_1651_, v_prec_1566_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1640_ = v___x_1653_;
goto v___jp_1639_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1640_ = v___x_1654_;
goto v___jp_1639_;
}
v___jp_1624_:
{
lean_object* v___x_1630_; 
lean_inc(v___y_1625_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 5);
lean_ctor_set(v___x_1622_, 1, v___y_1628_);
lean_ctor_set(v___x_1622_, 0, v___y_1625_);
v___x_1630_ = v___x_1622_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___y_1625_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v___y_1628_);
v___x_1630_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_inc(v___y_1626_);
v___x_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v___y_1626_);
v___x_1632_ = l_Array_repr___redArg(v___x_1569_, v_items_1620_);
v___x_1633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
lean_inc(v___y_1627_);
v___x_1634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___y_1627_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = 0;
v___x_1636_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*1, v___x_1635_);
v___x_1637_ = l_Repr_addAppParen(v___x_1636_, v_prec_1566_);
return v___x_1637_;
}
}
v___jp_1639_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1641_ = lean_box(1);
v___x_1642_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__11));
v___x_1643_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___redArg___closed__12, &l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12);
v___x_1644_ = lean_int_dec_lt(v_start_1619_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = l_Int_repr(v_start_1619_);
lean_dec(v_start_1619_);
v___x_1646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
v___y_1625_ = v___x_1642_;
v___y_1626_ = v___x_1641_;
v___y_1627_ = v___y_1640_;
v___y_1628_ = v___x_1646_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1647_ = lean_unsigned_to_nat(1024u);
v___x_1648_ = l_Int_repr(v_start_1619_);
lean_dec(v_start_1619_);
v___x_1649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
v___x_1650_ = l_Repr_addAppParen(v___x_1649_, v___x_1647_);
v___y_1625_ = v___x_1642_;
v___y_1626_ = v___x_1641_;
v___y_1627_ = v___y_1640_;
v___y_1628_ = v___x_1650_;
goto v___jp_1624_;
}
}
}
}
case 4:
{
lean_object* v_items_1656_; lean_object* v___x_1657_; lean_object* v___y_1659_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
lean_dec_ref(v___x_1569_);
lean_dec_ref(v_inst_1564_);
v_items_1656_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_items_1656_);
lean_dec_ref(v_x_1565_);
v___x_1657_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1657_, 0, lean_box(0));
lean_closure_set(v___x_1657_, 1, lean_box(0));
lean_closure_set(v___x_1657_, 2, v___x_1568_);
lean_closure_set(v___x_1657_, 3, v_localinst_1567_);
v___x_1667_ = lean_unsigned_to_nat(1024u);
v___x_1668_ = lean_nat_dec_le(v___x_1667_, v_prec_1566_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1659_ = v___x_1669_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1659_ = v___x_1670_;
goto v___jp_1658_;
}
v___jp_1658_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1660_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__15));
v___x_1661_ = l_Array_repr___redArg(v___x_1657_, v_items_1656_);
v___x_1662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
lean_inc(v___y_1659_);
v___x_1663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___y_1659_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = 0;
v___x_1665_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*1, v___x_1664_);
v___x_1666_ = l_Repr_addAppParen(v___x_1665_, v_prec_1566_);
return v___x_1666_;
}
}
case 5:
{
lean_object* v_items_1671_; lean_object* v___y_1673_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
lean_dec_ref(v___x_1569_);
lean_dec_ref(v___x_1568_);
lean_dec_ref(v_inst_1564_);
v_items_1671_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_items_1671_);
lean_dec_ref(v_x_1565_);
v___x_1681_ = lean_unsigned_to_nat(1024u);
v___x_1682_ = lean_nat_dec_le(v___x_1681_, v_prec_1566_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1673_ = v___x_1683_;
goto v___jp_1672_;
}
else
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1673_ = v___x_1684_;
goto v___jp_1672_;
}
v___jp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1674_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__18));
v___x_1675_ = l_Array_repr___redArg(v_localinst_1567_, v_items_1671_);
v___x_1676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
lean_inc(v___y_1673_);
v___x_1677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1673_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = 0;
v___x_1679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*1, v___x_1678_);
v___x_1680_ = l_Repr_addAppParen(v___x_1679_, v_prec_1566_);
return v___x_1680_;
}
}
case 6:
{
lean_object* v_content_1685_; lean_object* v___y_1687_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
lean_dec_ref(v___x_1569_);
lean_dec_ref(v___x_1568_);
lean_dec_ref(v_inst_1564_);
v_content_1685_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_content_1685_);
lean_dec_ref(v_x_1565_);
v___x_1695_ = lean_unsigned_to_nat(1024u);
v___x_1696_ = lean_nat_dec_le(v___x_1695_, v_prec_1566_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1687_ = v___x_1697_;
goto v___jp_1686_;
}
else
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1687_ = v___x_1698_;
goto v___jp_1686_;
}
v___jp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1688_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__21));
v___x_1689_ = l_Array_repr___redArg(v_localinst_1567_, v_content_1685_);
v___x_1690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
lean_inc(v___y_1687_);
v___x_1691_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1687_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = 0;
v___x_1693_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*1, v___x_1692_);
v___x_1694_ = l_Repr_addAppParen(v___x_1693_, v_prec_1566_);
return v___x_1694_;
}
}
default: 
{
lean_object* v_container_1699_; lean_object* v_content_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v___x_1569_);
lean_dec_ref(v___x_1568_);
v_container_1699_ = lean_ctor_get(v_x_1565_, 0);
v_content_1700_ = lean_ctor_get(v_x_1565_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_x_1565_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1702_ = v_x_1565_;
v_isShared_1703_ = v_isSharedCheck_1724_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_content_1700_);
lean_inc(v_container_1699_);
lean_dec(v_x_1565_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1724_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___y_1705_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = lean_unsigned_to_nat(1024u);
v___x_1721_ = lean_nat_dec_le(v___x_1720_, v_prec_1566_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1705_ = v___x_1722_;
goto v___jp_1704_;
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1705_ = v___x_1723_;
goto v___jp_1704_;
}
v___jp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1706_ = lean_box(1);
v___x_1707_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__24));
v___x_1708_ = lean_unsigned_to_nat(1024u);
v___x_1709_ = lean_apply_2(v_inst_1564_, v_container_1699_, v___x_1708_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set_tag(v___x_1702_, 5);
lean_ctor_set(v___x_1702_, 1, v___x_1709_);
lean_ctor_set(v___x_1702_, 0, v___x_1707_);
v___x_1711_ = v___x_1702_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
lean_ctor_set(v___x_1712_, 1, v___x_1706_);
v___x_1713_ = l_Array_repr___redArg(v_localinst_1567_, v_content_1700_);
v___x_1714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1712_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
lean_inc(v___y_1705_);
v___x_1715_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___y_1705_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = 0;
v___x_1717_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*1, v___x_1716_);
v___x_1718_ = l_Repr_addAppParen(v___x_1717_, v_prec_1566_);
return v___x_1718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr(lean_object* v_i_1725_, lean_object* v_b_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_x_1729_, lean_object* v_prec_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1727_, v_inst_1728_, v_x_1729_, v_prec_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___boxed(lean_object* v_i_1732_, lean_object* v_b_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_x_1736_, lean_object* v_prec_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Doc_instReprBlock_repr(v_i_1732_, v_b_1733_, v_inst_1734_, v_inst_1735_, v_x_1736_, v_prec_1737_);
lean_dec(v_prec_1737_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock___redArg(lean_object* v_inst_1739_, lean_object* v_inst_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1741_, 0, lean_box(0));
lean_closure_set(v___x_1741_, 1, lean_box(0));
lean_closure_set(v___x_1741_, 2, v_inst_1739_);
lean_closure_set(v___x_1741_, 3, v_inst_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock(lean_object* v_i_1742_, lean_object* v_b_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1746_, 0, lean_box(0));
lean_closure_set(v___x_1746_, 1, lean_box(0));
lean_closure_set(v___x_1746_, 2, v_inst_1744_);
lean_closure_set(v___x_1746_, 3, v_inst_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default(lean_object* v_i_1751_, lean_object* v_b_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlock_default___closed__1));
return v___x_1753_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedBlock___closed__0(void){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Doc_instInhabitedBlock_default(lean_box(0), lean_box(0));
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock(lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock___closed__0, &l_Lean_Doc_instInhabitedBlock___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock___closed__0);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty(lean_object* v_i_1762_, lean_object* v_b_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = ((lean_object*)(l_Lean_Doc_Block_empty___closed__1));
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg(lean_object* v_x_1765_){
_start:
{
lean_inc_ref(v_x_1765_);
return v_x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg___boxed(lean_object* v_x_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_Doc_Block_cast___redArg(v_x_1766_);
lean_dec_ref(v_x_1766_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast(lean_object* v_i_1768_, lean_object* v_i_x27_1769_, lean_object* v_b_1770_, lean_object* v_b_x27_1771_, lean_object* v_inlines__eq_1772_, lean_object* v_blocks__eq_1773_, lean_object* v_x_1774_){
_start:
{
lean_inc_ref(v_x_1774_);
return v_x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___boxed(lean_object* v_i_1775_, lean_object* v_i_x27_1776_, lean_object* v_b_1777_, lean_object* v_b_x27_1778_, lean_object* v_inlines__eq_1779_, lean_object* v_blocks__eq_1780_, lean_object* v_x_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Doc_Block_cast(v_i_1775_, v_i_x27_1776_, v_b_1777_, v_b_x27_1778_, v_inlines__eq_1779_, v_blocks__eq_1780_, v_x_1781_);
lean_dec_ref(v_x_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___redArg___boxed(lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_x_1786_, lean_object* v_x_1787_){
_start:
{
uint8_t v_res_1788_; lean_object* v_r_1789_; 
v_res_1788_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1783_, v_inst_1784_, v_inst_1785_, v_x_1786_, v_x_1787_);
v_r_1789_ = lean_box(v_res_1788_);
return v_r_1789_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq___redArg(lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_){
_start:
{
lean_object* v_title_1795_; lean_object* v_titleString_1796_; lean_object* v_metadata_1797_; lean_object* v_content_1798_; lean_object* v_subParts_1799_; lean_object* v_title_1800_; lean_object* v_titleString_1801_; lean_object* v_metadata_1802_; lean_object* v_content_1803_; lean_object* v_subParts_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_title_1795_ = lean_ctor_get(v_x_1793_, 0);
lean_inc_ref(v_title_1795_);
v_titleString_1796_ = lean_ctor_get(v_x_1793_, 1);
lean_inc_ref(v_titleString_1796_);
v_metadata_1797_ = lean_ctor_get(v_x_1793_, 2);
lean_inc(v_metadata_1797_);
v_content_1798_ = lean_ctor_get(v_x_1793_, 3);
lean_inc_ref(v_content_1798_);
v_subParts_1799_ = lean_ctor_get(v_x_1793_, 4);
lean_inc_ref(v_subParts_1799_);
lean_dec_ref(v_x_1793_);
v_title_1800_ = lean_ctor_get(v_x_1794_, 0);
lean_inc_ref(v_title_1800_);
v_titleString_1801_ = lean_ctor_get(v_x_1794_, 1);
lean_inc_ref(v_titleString_1801_);
v_metadata_1802_ = lean_ctor_get(v_x_1794_, 2);
lean_inc(v_metadata_1802_);
v_content_1803_ = lean_ctor_get(v_x_1794_, 3);
lean_inc_ref(v_content_1803_);
v_subParts_1804_ = lean_ctor_get(v_x_1794_, 4);
lean_inc_ref(v_subParts_1804_);
lean_dec_ref(v_x_1794_);
v___x_1805_ = lean_array_get_size(v_title_1795_);
v___x_1806_ = lean_array_get_size(v_title_1800_);
v___x_1807_ = lean_nat_dec_eq(v___x_1805_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_content_1803_);
lean_dec(v_metadata_1802_);
lean_dec_ref(v_titleString_1801_);
lean_dec_ref(v_title_1800_);
lean_dec_ref(v_subParts_1799_);
lean_dec_ref(v_content_1798_);
lean_dec(v_metadata_1797_);
lean_dec_ref(v_titleString_1796_);
lean_dec_ref(v_title_1795_);
lean_dec_ref(v_inst_1792_);
lean_dec_ref(v_inst_1791_);
lean_dec_ref(v_inst_1790_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
lean_inc_ref(v_inst_1792_);
lean_inc_ref(v_inst_1791_);
lean_inc_ref_n(v_inst_1790_, 2);
v___x_1808_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___redArg___boxed), 5, 3);
lean_closure_set(v___x_1808_, 0, v_inst_1790_);
lean_closure_set(v___x_1808_, 1, v_inst_1791_);
lean_closure_set(v___x_1808_, 2, v_inst_1792_);
v___x_1809_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1809_, 0, lean_box(0));
lean_closure_set(v___x_1809_, 1, v_inst_1790_);
v___x_1810_ = l_Array_isEqvAux___redArg(v_title_1795_, v_title_1800_, v___x_1809_, v___x_1805_);
lean_dec_ref(v_title_1800_);
lean_dec_ref(v_title_1795_);
if (v___x_1810_ == 0)
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_content_1803_);
lean_dec(v_metadata_1802_);
lean_dec_ref(v_titleString_1801_);
lean_dec_ref(v_subParts_1799_);
lean_dec_ref(v_content_1798_);
lean_dec(v_metadata_1797_);
lean_dec_ref(v_titleString_1796_);
lean_dec_ref(v_inst_1792_);
lean_dec_ref(v_inst_1791_);
lean_dec_ref(v_inst_1790_);
return v___x_1810_;
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_string_dec_eq(v_titleString_1796_, v_titleString_1801_);
lean_dec_ref(v_titleString_1801_);
lean_dec_ref(v_titleString_1796_);
if (v___x_1811_ == 0)
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_content_1803_);
lean_dec(v_metadata_1802_);
lean_dec_ref(v_subParts_1799_);
lean_dec_ref(v_content_1798_);
lean_dec(v_metadata_1797_);
lean_dec_ref(v_inst_1792_);
lean_dec_ref(v_inst_1791_);
lean_dec_ref(v_inst_1790_);
return v___x_1811_;
}
else
{
uint8_t v___x_1812_; 
v___x_1812_ = l_Option_instBEq_beq___redArg(v_inst_1792_, v_metadata_1797_, v_metadata_1802_);
if (v___x_1812_ == 0)
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_content_1803_);
lean_dec_ref(v_subParts_1799_);
lean_dec_ref(v_content_1798_);
lean_dec_ref(v_inst_1791_);
lean_dec_ref(v_inst_1790_);
return v___x_1812_;
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1813_ = lean_array_get_size(v_content_1798_);
v___x_1814_ = lean_array_get_size(v_content_1803_);
v___x_1815_ = lean_nat_dec_eq(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_content_1803_);
lean_dec_ref(v_subParts_1799_);
lean_dec_ref(v_content_1798_);
lean_dec_ref(v_inst_1791_);
lean_dec_ref(v_inst_1790_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1816_, 0, lean_box(0));
lean_closure_set(v___x_1816_, 1, lean_box(0));
lean_closure_set(v___x_1816_, 2, v_inst_1790_);
lean_closure_set(v___x_1816_, 3, v_inst_1791_);
v___x_1817_ = l_Array_isEqvAux___redArg(v_content_1798_, v_content_1803_, v___x_1816_, v___x_1813_);
lean_dec_ref(v_content_1803_);
lean_dec_ref(v_content_1798_);
if (v___x_1817_ == 0)
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_subParts_1799_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = lean_array_get_size(v_subParts_1799_);
v___x_1819_ = lean_array_get_size(v_subParts_1804_);
v___x_1820_ = lean_nat_dec_eq(v___x_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_subParts_1799_);
return v___x_1820_;
}
else
{
uint8_t v___x_1821_; 
v___x_1821_ = l_Array_isEqvAux___redArg(v_subParts_1799_, v_subParts_1804_, v___x_1808_, v___x_1818_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_subParts_1799_);
return v___x_1821_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq(lean_object* v_i_1822_, lean_object* v_b_1823_, lean_object* v_p_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_inst_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_){
_start:
{
uint8_t v___x_1830_; 
v___x_1830_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1825_, v_inst_1826_, v_inst_1827_, v_x_1828_, v_x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___boxed(lean_object* v_i_1831_, lean_object* v_b_1832_, lean_object* v_p_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_x_1837_, lean_object* v_x_1838_){
_start:
{
uint8_t v_res_1839_; lean_object* v_r_1840_; 
v_res_1839_ = l_Lean_Doc_instBEqPart_beq(v_i_1831_, v_b_1832_, v_p_1833_, v_inst_1834_, v_inst_1835_, v_inst_1836_, v_x_1837_, v_x_1838_);
v_r_1840_ = lean_box(v_res_1839_);
return v_r_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart___redArg(lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1844_, 0, lean_box(0));
lean_closure_set(v___x_1844_, 1, lean_box(0));
lean_closure_set(v___x_1844_, 2, lean_box(0));
lean_closure_set(v___x_1844_, 3, v_inst_1841_);
lean_closure_set(v___x_1844_, 4, v_inst_1842_);
lean_closure_set(v___x_1844_, 5, v_inst_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart(lean_object* v_i_1845_, lean_object* v_b_1846_, lean_object* v_p_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1851_, 0, lean_box(0));
lean_closure_set(v___x_1851_, 1, lean_box(0));
lean_closure_set(v___x_1851_, 2, lean_box(0));
lean_closure_set(v___x_1851_, 3, v_inst_1848_);
lean_closure_set(v___x_1851_, 4, v_inst_1849_);
lean_closure_set(v___x_1851_, 5, v_inst_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___redArg___boxed(lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
uint8_t v_res_1857_; lean_object* v_r_1858_; 
v_res_1857_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1852_, v_inst_1853_, v_inst_1854_, v_x_1855_, v_x_1856_);
v_r_1858_ = lean_box(v_res_1857_);
return v_r_1858_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord___redArg(lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
lean_object* v_title_1864_; lean_object* v_titleString_1865_; lean_object* v_metadata_1866_; lean_object* v_content_1867_; lean_object* v_subParts_1868_; lean_object* v_title_1869_; lean_object* v_titleString_1870_; lean_object* v_metadata_1871_; lean_object* v_content_1872_; lean_object* v_subParts_1873_; lean_object* v___x_1874_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v_title_1864_ = lean_ctor_get(v_x_1862_, 0);
lean_inc_ref(v_title_1864_);
v_titleString_1865_ = lean_ctor_get(v_x_1862_, 1);
lean_inc_ref(v_titleString_1865_);
v_metadata_1866_ = lean_ctor_get(v_x_1862_, 2);
lean_inc(v_metadata_1866_);
v_content_1867_ = lean_ctor_get(v_x_1862_, 3);
lean_inc_ref(v_content_1867_);
v_subParts_1868_ = lean_ctor_get(v_x_1862_, 4);
lean_inc_ref(v_subParts_1868_);
lean_dec_ref(v_x_1862_);
v_title_1869_ = lean_ctor_get(v_x_1863_, 0);
lean_inc_ref(v_title_1869_);
v_titleString_1870_ = lean_ctor_get(v_x_1863_, 1);
lean_inc_ref(v_titleString_1870_);
v_metadata_1871_ = lean_ctor_get(v_x_1863_, 2);
lean_inc(v_metadata_1871_);
v_content_1872_ = lean_ctor_get(v_x_1863_, 3);
lean_inc_ref(v_content_1872_);
v_subParts_1873_ = lean_ctor_get(v_x_1863_, 4);
lean_inc_ref(v_subParts_1873_);
lean_dec_ref(v_x_1863_);
lean_inc_ref(v_inst_1861_);
lean_inc_ref(v_inst_1860_);
lean_inc_ref_n(v_inst_1859_, 2);
v___x_1874_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___redArg___boxed), 5, 3);
lean_closure_set(v___x_1874_, 0, v_inst_1859_);
lean_closure_set(v___x_1874_, 1, v_inst_1860_);
lean_closure_set(v___x_1874_, 2, v_inst_1861_);
v___x_1879_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1879_, 0, lean_box(0));
lean_closure_set(v___x_1879_, 1, v_inst_1859_);
v___x_1880_ = l_Array_compareLex___redArg(v___x_1879_, v_title_1864_, v_title_1869_);
lean_dec_ref(v_title_1869_);
lean_dec_ref(v_title_1864_);
if (v___x_1880_ == 1)
{
uint8_t v___x_1881_; 
v___x_1881_ = lean_string_dec_lt(v_titleString_1865_, v_titleString_1870_);
if (v___x_1881_ == 0)
{
uint8_t v___x_1882_; 
v___x_1882_ = lean_string_dec_eq(v_titleString_1865_, v_titleString_1870_);
lean_dec_ref(v_titleString_1870_);
lean_dec_ref(v_titleString_1865_);
if (v___x_1882_ == 0)
{
uint8_t v___x_1883_; 
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec(v_metadata_1871_);
lean_dec_ref(v_subParts_1868_);
lean_dec_ref(v_content_1867_);
lean_dec(v_metadata_1866_);
lean_dec_ref(v_inst_1861_);
lean_dec_ref(v_inst_1860_);
lean_dec_ref(v_inst_1859_);
v___x_1883_ = 2;
return v___x_1883_;
}
else
{
if (lean_obj_tag(v_metadata_1866_) == 0)
{
lean_dec_ref(v_inst_1861_);
if (lean_obj_tag(v_metadata_1871_) == 0)
{
goto v___jp_1875_;
}
else
{
uint8_t v___x_1884_; 
lean_dec_ref(v_metadata_1871_);
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec_ref(v_subParts_1868_);
lean_dec_ref(v_content_1867_);
lean_dec_ref(v_inst_1860_);
lean_dec_ref(v_inst_1859_);
v___x_1884_ = 0;
return v___x_1884_;
}
}
else
{
if (lean_obj_tag(v_metadata_1871_) == 0)
{
uint8_t v___x_1885_; 
lean_dec_ref(v_metadata_1866_);
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec_ref(v_subParts_1868_);
lean_dec_ref(v_content_1867_);
lean_dec_ref(v_inst_1861_);
lean_dec_ref(v_inst_1860_);
lean_dec_ref(v_inst_1859_);
v___x_1885_ = 2;
return v___x_1885_;
}
else
{
lean_object* v_val_1886_; lean_object* v_val_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v_val_1886_ = lean_ctor_get(v_metadata_1866_, 0);
lean_inc(v_val_1886_);
lean_dec_ref(v_metadata_1866_);
v_val_1887_ = lean_ctor_get(v_metadata_1871_, 0);
lean_inc(v_val_1887_);
lean_dec_ref(v_metadata_1871_);
v___x_1888_ = lean_apply_2(v_inst_1861_, v_val_1886_, v_val_1887_);
v___x_1889_ = lean_unbox(v___x_1888_);
if (v___x_1889_ == 1)
{
goto v___jp_1875_;
}
else
{
uint8_t v___x_1890_; 
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec_ref(v_subParts_1868_);
lean_dec_ref(v_content_1867_);
lean_dec_ref(v_inst_1860_);
lean_dec_ref(v_inst_1859_);
v___x_1890_ = lean_unbox(v___x_1888_);
return v___x_1890_;
}
}
}
}
}
else
{
uint8_t v___x_1891_; 
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec(v_metadata_1871_);
lean_dec_ref(v_titleString_1870_);
lean_dec_ref(v_subParts_1868_);
lean_dec_ref(v_content_1867_);
lean_dec(v_metadata_1866_);
lean_dec_ref(v_titleString_1865_);
lean_dec_ref(v_inst_1861_);
lean_dec_ref(v_inst_1860_);
lean_dec_ref(v_inst_1859_);
v___x_1891_ = 0;
return v___x_1891_;
}
}
else
{
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec(v_metadata_1871_);
lean_dec_ref(v_titleString_1870_);
lean_dec_ref(v_subParts_1868_);
lean_dec_ref(v_content_1867_);
lean_dec(v_metadata_1866_);
lean_dec_ref(v_titleString_1865_);
lean_dec_ref(v_inst_1861_);
lean_dec_ref(v_inst_1860_);
lean_dec_ref(v_inst_1859_);
return v___x_1880_;
}
v___jp_1875_:
{
lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1876_, 0, lean_box(0));
lean_closure_set(v___x_1876_, 1, lean_box(0));
lean_closure_set(v___x_1876_, 2, v_inst_1859_);
lean_closure_set(v___x_1876_, 3, v_inst_1860_);
v___x_1877_ = l_Array_compareLex___redArg(v___x_1876_, v_content_1867_, v_content_1872_);
lean_dec_ref(v_content_1872_);
lean_dec_ref(v_content_1867_);
if (v___x_1877_ == 1)
{
uint8_t v___x_1878_; 
v___x_1878_ = l_Array_compareLex___redArg(v___x_1874_, v_subParts_1868_, v_subParts_1873_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_subParts_1868_);
if (v___x_1878_ == 1)
{
return v___x_1878_;
}
else
{
return v___x_1878_;
}
}
else
{
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_subParts_1868_);
return v___x_1877_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord(lean_object* v_i_1892_, lean_object* v_b_1893_, lean_object* v_p_1894_, lean_object* v_inst_1895_, lean_object* v_inst_1896_, lean_object* v_inst_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
uint8_t v___x_1900_; 
v___x_1900_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1895_, v_inst_1896_, v_inst_1897_, v_x_1898_, v_x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___boxed(lean_object* v_i_1901_, lean_object* v_b_1902_, lean_object* v_p_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
uint8_t v_res_1909_; lean_object* v_r_1910_; 
v_res_1909_ = l_Lean_Doc_instOrdPart_ord(v_i_1901_, v_b_1902_, v_p_1903_, v_inst_1904_, v_inst_1905_, v_inst_1906_, v_x_1907_, v_x_1908_);
v_r_1910_ = lean_box(v_res_1909_);
return v_r_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart___redArg(lean_object* v_inst_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1914_, 0, lean_box(0));
lean_closure_set(v___x_1914_, 1, lean_box(0));
lean_closure_set(v___x_1914_, 2, lean_box(0));
lean_closure_set(v___x_1914_, 3, v_inst_1911_);
lean_closure_set(v___x_1914_, 4, v_inst_1912_);
lean_closure_set(v___x_1914_, 5, v_inst_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart(lean_object* v_i_1915_, lean_object* v_b_1916_, lean_object* v_p_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_inst_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1921_, 0, lean_box(0));
lean_closure_set(v___x_1921_, 1, lean_box(0));
lean_closure_set(v___x_1921_, 2, lean_box(0));
lean_closure_set(v___x_1921_, 3, v_inst_1918_);
lean_closure_set(v___x_1921_, 4, v_inst_1919_);
lean_closure_set(v___x_1921_, 5, v_inst_1920_);
return v___x_1921_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_unsigned_to_nat(9u);
v___x_1932_ = lean_nat_to_int(v___x_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_unsigned_to_nat(15u);
v___x_1937_ = lean_nat_to_int(v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_unsigned_to_nat(11u);
v___x_1945_ = lean_nat_to_int(v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg___boxed(lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_x_1952_, lean_object* v_prec_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_1949_, v_inst_1950_, v_inst_1951_, v_x_1952_, v_prec_1953_);
lean_dec(v_prec_1953_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg(lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_x_1958_, lean_object* v_prec_1959_){
_start:
{
lean_object* v_title_1960_; lean_object* v_titleString_1961_; lean_object* v_metadata_1962_; lean_object* v_content_1963_; lean_object* v_subParts_1964_; lean_object* v_localinst_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_title_1960_ = lean_ctor_get(v_x_1958_, 0);
lean_inc_ref(v_title_1960_);
v_titleString_1961_ = lean_ctor_get(v_x_1958_, 1);
lean_inc_ref(v_titleString_1961_);
v_metadata_1962_ = lean_ctor_get(v_x_1958_, 2);
lean_inc(v_metadata_1962_);
v_content_1963_ = lean_ctor_get(v_x_1958_, 3);
lean_inc_ref(v_content_1963_);
v_subParts_1964_ = lean_ctor_get(v_x_1958_, 4);
lean_inc_ref(v_subParts_1964_);
lean_dec_ref(v_x_1958_);
lean_inc_ref(v_inst_1957_);
lean_inc_ref(v_inst_1956_);
lean_inc_ref_n(v_inst_1955_, 2);
v_localinst_1965_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___redArg___boxed), 5, 3);
lean_closure_set(v_localinst_1965_, 0, v_inst_1955_);
lean_closure_set(v_localinst_1965_, 1, v_inst_1956_);
lean_closure_set(v_localinst_1965_, 2, v_inst_1957_);
v___x_1966_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1967_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__3));
v___x_1968_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4);
v___x_1969_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1969_, 0, lean_box(0));
lean_closure_set(v___x_1969_, 1, v_inst_1955_);
v___x_1970_ = l_Array_repr___redArg(v___x_1969_, v_title_1960_);
v___x_1971_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1968_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = 0;
v___x_1973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*1, v___x_1972_);
v___x_1974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1967_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = lean_box(1);
v___x_1978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__6));
v___x_1980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1978_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v___x_1966_);
v___x_1982_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7);
v___x_1983_ = l_String_quote(v_titleString_1961_);
v___x_1984_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1982_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
lean_ctor_set_uint8(v___x_1986_, sizeof(void*)*1, v___x_1972_);
v___x_1987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1981_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
lean_ctor_set(v___x_1988_, 1, v___x_1975_);
v___x_1989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v___x_1977_);
v___x_1990_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__9));
v___x_1991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v___x_1966_);
v___x_1993_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = l_Option_repr___redArg(v_inst_1957_, v_metadata_1962_, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1993_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*1, v___x_1972_);
v___x_1998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1992_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
lean_ctor_set(v___x_1999_, 1, v___x_1975_);
v___x_2000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v___x_1977_);
v___x_2001_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__11));
v___x_2002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_1966_);
v___x_2004_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12);
v___x_2005_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_2005_, 0, lean_box(0));
lean_closure_set(v___x_2005_, 1, lean_box(0));
lean_closure_set(v___x_2005_, 2, v_inst_1955_);
lean_closure_set(v___x_2005_, 3, v_inst_1956_);
v___x_2006_ = l_Array_repr___redArg(v___x_2005_, v_content_1963_);
v___x_2007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2004_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*1, v___x_1972_);
v___x_2009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2003_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v___x_1975_);
v___x_2011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___x_1977_);
v___x_2012_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__14));
v___x_2013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___x_1966_);
v___x_2015_ = l_Array_repr___redArg(v_localinst_1965_, v_subParts_1964_);
v___x_2016_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_1993_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*1, v___x_1972_);
v___x_2018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2014_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v___x_2019_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_2020_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_2021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set(v___x_2021_, 1, v___x_2018_);
v___x_2022_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_2023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2019_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*1, v___x_1972_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr(lean_object* v_i_2026_, lean_object* v_b_2027_, lean_object* v_p_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_inst_2031_, lean_object* v_x_2032_, lean_object* v_prec_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_2029_, v_inst_2030_, v_inst_2031_, v_x_2032_, v_prec_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___boxed(lean_object* v_i_2035_, lean_object* v_b_2036_, lean_object* v_p_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_x_2041_, lean_object* v_prec_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Doc_instReprPart_repr(v_i_2035_, v_b_2036_, v_p_2037_, v_inst_2038_, v_inst_2039_, v_inst_2040_, v_x_2041_, v_prec_2042_);
lean_dec(v_prec_2042_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart___redArg(lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2047_, 0, lean_box(0));
lean_closure_set(v___x_2047_, 1, lean_box(0));
lean_closure_set(v___x_2047_, 2, lean_box(0));
lean_closure_set(v___x_2047_, 3, v_inst_2044_);
lean_closure_set(v___x_2047_, 4, v_inst_2045_);
lean_closure_set(v___x_2047_, 5, v_inst_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart(lean_object* v_i_2048_, lean_object* v_b_2049_, lean_object* v_p_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2054_, 0, lean_box(0));
lean_closure_set(v___x_2054_, 1, lean_box(0));
lean_closure_set(v___x_2054_, 2, lean_box(0));
lean_closure_set(v___x_2054_, 3, v_inst_2051_);
lean_closure_set(v___x_2054_, 4, v_inst_2052_);
lean_closure_set(v___x_2054_, 5, v_inst_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default(lean_object* v_i_2059_, lean_object* v_b_2060_, lean_object* v_p_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = ((lean_object*)(l_Lean_Doc_instInhabitedPart_default___closed__0));
return v___x_2062_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedPart___closed__0(void){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_Doc_instInhabitedPart_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart(lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart___closed__0, &l_Lean_Doc_instInhabitedPart___closed__0_once, _init_l_Lean_Doc_instInhabitedPart___closed__0);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg(lean_object* v_x_2068_){
_start:
{
lean_inc_ref(v_x_2068_);
return v_x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg___boxed(lean_object* v_x_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_Doc_Part_cast___redArg(v_x_2069_);
lean_dec_ref(v_x_2069_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast(lean_object* v_i_2071_, lean_object* v_i_x27_2072_, lean_object* v_b_2073_, lean_object* v_b_x27_2074_, lean_object* v_p_2075_, lean_object* v_p_x27_2076_, lean_object* v_inlines__eq_2077_, lean_object* v_blocks__eq_2078_, lean_object* v_metadata__eq_2079_, lean_object* v_x_2080_){
_start:
{
lean_inc_ref(v_x_2080_);
return v_x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___boxed(lean_object* v_i_2081_, lean_object* v_i_x27_2082_, lean_object* v_b_2083_, lean_object* v_b_x27_2084_, lean_object* v_p_2085_, lean_object* v_p_x27_2086_, lean_object* v_inlines__eq_2087_, lean_object* v_blocks__eq_2088_, lean_object* v_metadata__eq_2089_, lean_object* v_x_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Doc_Part_cast(v_i_2081_, v_i_x27_2082_, v_b_2083_, v_b_x27_2084_, v_p_2085_, v_p_x27_2086_, v_inlines__eq_2087_, v_blocks__eq_2088_, v_metadata__eq_2089_, v_x_2090_);
lean_dec_ref(v_x_2090_);
return v_res_2091_;
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
