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
uint8_t l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_Option_repr___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_378_; lean_object* v_content_380_; lean_object* v_content_x27_381_; 
lean_inc_ref(v_inst_370_);
v___x_378_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___redArg___boxed), 3, 1);
lean_closure_set(v___x_378_, 0, v_inst_370_);
switch(lean_obj_tag(v_x_371_))
{
case 1:
{
lean_object* v_content_384_; lean_object* v_content_385_; 
lean_dec_ref(v_inst_370_);
v_content_384_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_384_);
lean_dec_ref_known(v_x_371_, 1);
v_content_385_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_385_);
lean_dec_ref(v_x_372_);
v_content_380_ = v_content_384_;
v_content_x27_381_ = v_content_385_;
goto v___jp_379_;
}
case 2:
{
lean_object* v_content_386_; lean_object* v_content_387_; 
lean_dec_ref(v_inst_370_);
v_content_386_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_386_);
lean_dec_ref_known(v_x_371_, 1);
v_content_387_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_387_);
lean_dec_ref(v_x_372_);
v_content_380_ = v_content_386_;
v_content_x27_381_ = v_content_387_;
goto v___jp_379_;
}
case 4:
{
uint8_t v_mode_388_; lean_object* v_string_389_; uint8_t v_mode_390_; lean_object* v_string_391_; uint8_t v___x_392_; 
lean_dec_ref(v___x_378_);
lean_dec_ref(v_inst_370_);
v_mode_388_ = lean_ctor_get_uint8(v_x_371_, sizeof(void*)*1);
v_string_389_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_string_389_);
lean_dec_ref_known(v_x_371_, 1);
v_mode_390_ = lean_ctor_get_uint8(v_x_372_, sizeof(void*)*1);
v_string_391_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_string_391_);
lean_dec_ref(v_x_372_);
v___x_392_ = l_Lean_Doc_instOrdMathMode_ord(v_mode_388_, v_mode_390_);
if (v___x_392_ == 1)
{
uint8_t v___x_393_; 
v___x_393_ = lean_string_compare(v_string_389_, v_string_391_);
lean_dec_ref(v_string_391_);
lean_dec_ref(v_string_389_);
return v___x_393_;
}
else
{
lean_dec_ref(v_string_391_);
lean_dec_ref(v_string_389_);
return v___x_392_;
}
}
case 6:
{
lean_object* v_content_394_; lean_object* v_url_395_; lean_object* v_content_396_; lean_object* v_url_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
lean_dec_ref(v_inst_370_);
v_content_394_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_394_);
v_url_395_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_url_395_);
lean_dec_ref_known(v_x_371_, 2);
v_content_396_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_396_);
v_url_397_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_url_397_);
lean_dec_ref(v_x_372_);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_378_, v_content_394_, v_content_396_, v___x_398_);
lean_dec_ref(v_content_396_);
lean_dec_ref(v_content_394_);
if (v___x_399_ == 1)
{
uint8_t v___x_400_; 
v___x_400_ = lean_string_compare(v_url_395_, v_url_397_);
lean_dec_ref(v_url_397_);
lean_dec_ref(v_url_395_);
return v___x_400_;
}
else
{
lean_dec_ref(v_url_397_);
lean_dec_ref(v_url_395_);
return v___x_399_;
}
}
case 7:
{
lean_object* v_name_401_; lean_object* v_content_402_; lean_object* v_name_403_; lean_object* v_content_404_; uint8_t v___x_405_; 
lean_dec_ref(v_inst_370_);
v_name_401_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_name_401_);
v_content_402_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_content_402_);
lean_dec_ref_known(v_x_371_, 2);
v_name_403_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_name_403_);
v_content_404_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_content_404_);
lean_dec_ref(v_x_372_);
v___x_405_ = lean_string_compare(v_name_401_, v_name_403_);
lean_dec_ref(v_name_403_);
lean_dec_ref(v_name_401_);
if (v___x_405_ == 1)
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_378_, v_content_402_, v_content_404_, v___x_406_);
lean_dec_ref(v_content_404_);
lean_dec_ref(v_content_402_);
return v___x_407_;
}
else
{
lean_dec_ref(v_content_404_);
lean_dec_ref(v_content_402_);
lean_dec_ref(v___x_378_);
return v___x_405_;
}
}
case 8:
{
lean_object* v_alt_408_; lean_object* v_url_409_; lean_object* v_alt_410_; lean_object* v_url_411_; uint8_t v___x_412_; 
lean_dec_ref(v___x_378_);
lean_dec_ref(v_inst_370_);
v_alt_408_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_alt_408_);
v_url_409_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_url_409_);
lean_dec_ref_known(v_x_371_, 2);
v_alt_410_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_alt_410_);
v_url_411_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_url_411_);
lean_dec_ref(v_x_372_);
v___x_412_ = lean_string_compare(v_alt_408_, v_alt_410_);
lean_dec_ref(v_alt_410_);
lean_dec_ref(v_alt_408_);
if (v___x_412_ == 1)
{
uint8_t v___x_413_; 
v___x_413_ = lean_string_compare(v_url_409_, v_url_411_);
lean_dec_ref(v_url_411_);
lean_dec_ref(v_url_409_);
return v___x_413_;
}
else
{
lean_dec_ref(v_url_411_);
lean_dec_ref(v_url_409_);
return v___x_412_;
}
}
case 9:
{
lean_object* v_content_414_; lean_object* v_content_415_; 
lean_dec_ref(v_inst_370_);
v_content_414_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_content_414_);
lean_dec_ref_known(v_x_371_, 1);
v_content_415_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_content_415_);
lean_dec_ref(v_x_372_);
v_content_380_ = v_content_414_;
v_content_x27_381_ = v_content_415_;
goto v___jp_379_;
}
case 10:
{
lean_object* v_container_416_; lean_object* v_content_417_; lean_object* v_container_418_; lean_object* v_content_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_container_416_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_container_416_);
v_content_417_ = lean_ctor_get(v_x_371_, 1);
lean_inc_ref(v_content_417_);
lean_dec_ref_known(v_x_371_, 2);
v_container_418_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_container_418_);
v_content_419_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_content_419_);
lean_dec_ref(v_x_372_);
v___x_420_ = lean_apply_2(v_inst_370_, v_container_416_, v_container_418_);
v___x_421_ = lean_unbox(v___x_420_);
if (v___x_421_ == 1)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_378_, v_content_417_, v_content_419_, v___x_422_);
lean_dec_ref(v_content_419_);
lean_dec_ref(v_content_417_);
return v___x_423_;
}
else
{
uint8_t v___x_424_; 
lean_dec_ref(v_content_419_);
lean_dec_ref(v_content_417_);
lean_dec_ref(v___x_378_);
v___x_424_ = lean_unbox(v___x_420_);
return v___x_424_;
}
}
default: 
{
lean_object* v_string_425_; lean_object* v_string_426_; uint8_t v___x_427_; 
lean_dec_ref(v___x_378_);
lean_dec_ref(v_inst_370_);
v_string_425_ = lean_ctor_get(v_x_371_, 0);
lean_inc_ref(v_string_425_);
lean_dec_ref(v_x_371_);
v_string_426_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_string_426_);
lean_dec_ref(v_x_372_);
v___x_427_ = lean_string_compare(v_string_425_, v_string_426_);
lean_dec_ref(v_string_426_);
lean_dec_ref(v_string_425_);
return v___x_427_;
}
}
v___jp_379_:
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_378_, v_content_380_, v_content_x27_381_, v___x_382_);
lean_dec_ref(v_content_x27_381_);
lean_dec_ref(v_content_380_);
return v___x_383_;
}
}
}
else
{
uint8_t v___x_428_; 
lean_dec(v___x_374_);
lean_dec(v___x_373_);
lean_dec_ref(v_x_372_);
lean_dec_ref(v_x_371_);
lean_dec_ref(v_inst_370_);
v___x_428_ = 0;
return v___x_428_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdInline_ord(lean_object* v_i_429_, lean_object* v_inst_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = l_Lean_Doc_instOrdInline_ord___redArg(v_inst_430_, v_x_431_, v_x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline_ord___boxed(lean_object* v_i_434_, lean_object* v_inst_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Lean_Doc_instOrdInline_ord(v_i_434_, v_inst_435_, v_x_436_, v_x_437_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline___redArg(lean_object* v_inst_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_441_, 0, lean_box(0));
lean_closure_set(v___x_441_, 1, v_inst_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdInline(lean_object* v_i_442_, lean_object* v_inst_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_444_, 0, lean_box(0));
lean_closure_set(v___x_444_, 1, v_inst_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg___boxed(lean_object* v_inst_511_, lean_object* v_x_512_, lean_object* v_prec_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_511_, v_x_512_, v_prec_513_);
lean_dec(v_prec_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___redArg(lean_object* v_inst_515_, lean_object* v_x_516_, lean_object* v_prec_517_){
_start:
{
lean_object* v_localinst_518_; 
lean_inc_ref(v_inst_515_);
v_localinst_518_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_518_, 0, v_inst_515_);
switch(lean_obj_tag(v_x_516_))
{
case 0:
{
lean_object* v_string_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v_localinst_518_);
lean_dec_ref(v_inst_515_);
v_string_519_ = lean_ctor_get(v_x_516_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_539_ == 0)
{
v___x_521_ = v_x_516_;
v_isShared_522_ = v_isSharedCheck_539_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_string_519_);
lean_dec(v_x_516_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_539_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___y_524_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(1024u);
v___x_536_ = lean_nat_dec_le(v___x_535_, v_prec_517_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_524_ = v___x_537_;
goto v___jp_523_;
}
else
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_524_ = v___x_538_;
goto v___jp_523_;
}
v___jp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_525_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__2));
v___x_526_ = l_String_quote(v_string_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 3);
lean_ctor_set(v___x_521_, 0, v___x_526_);
v___x_528_ = v___x_521_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_534_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_525_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
lean_inc(v___y_524_);
v___x_530_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_530_, 0, v___y_524_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = 0;
v___x_532_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*1, v___x_531_);
v___x_533_ = l_Repr_addAppParen(v___x_532_, v_prec_517_);
return v___x_533_;
}
}
}
}
case 1:
{
lean_object* v_content_540_; lean_object* v___y_542_; lean_object* v___x_550_; uint8_t v___x_551_; 
lean_dec_ref(v_inst_515_);
v_content_540_ = lean_ctor_get(v_x_516_, 0);
lean_inc_ref(v_content_540_);
lean_dec_ref_known(v_x_516_, 1);
v___x_550_ = lean_unsigned_to_nat(1024u);
v___x_551_ = lean_nat_dec_le(v___x_550_, v_prec_517_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_542_ = v___x_552_;
goto v___jp_541_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_542_ = v___x_553_;
goto v___jp_541_;
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_543_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__5));
v___x_544_ = l_Array_repr___redArg(v_localinst_518_, v_content_540_);
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
lean_inc(v___y_542_);
v___x_546_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_546_, 0, v___y_542_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = 0;
v___x_548_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*1, v___x_547_);
v___x_549_ = l_Repr_addAppParen(v___x_548_, v_prec_517_);
return v___x_549_;
}
}
case 2:
{
lean_object* v_content_554_; lean_object* v___y_556_; lean_object* v___x_564_; uint8_t v___x_565_; 
lean_dec_ref(v_inst_515_);
v_content_554_ = lean_ctor_get(v_x_516_, 0);
lean_inc_ref(v_content_554_);
lean_dec_ref_known(v_x_516_, 1);
v___x_564_ = lean_unsigned_to_nat(1024u);
v___x_565_ = lean_nat_dec_le(v___x_564_, v_prec_517_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
v___x_566_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_556_ = v___x_566_;
goto v___jp_555_;
}
else
{
lean_object* v___x_567_; 
v___x_567_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_556_ = v___x_567_;
goto v___jp_555_;
}
v___jp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_557_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__8));
v___x_558_ = l_Array_repr___redArg(v_localinst_518_, v_content_554_);
v___x_559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
lean_inc(v___y_556_);
v___x_560_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_560_, 0, v___y_556_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = 0;
v___x_562_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*1, v___x_561_);
v___x_563_ = l_Repr_addAppParen(v___x_562_, v_prec_517_);
return v___x_563_;
}
}
case 3:
{
lean_object* v_string_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v_localinst_518_);
lean_dec_ref(v_inst_515_);
v_string_568_ = lean_ctor_get(v_x_516_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_588_ == 0)
{
v___x_570_ = v_x_516_;
v_isShared_571_ = v_isSharedCheck_588_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_string_568_);
lean_dec(v_x_516_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_588_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___y_573_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(1024u);
v___x_585_ = lean_nat_dec_le(v___x_584_, v_prec_517_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_573_ = v___x_586_;
goto v___jp_572_;
}
else
{
lean_object* v___x_587_; 
v___x_587_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_573_ = v___x_587_;
goto v___jp_572_;
}
v___jp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_574_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__11));
v___x_575_ = l_String_quote(v_string_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_575_);
v___x_577_ = v___x_570_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_583_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_574_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
lean_inc(v___y_573_);
v___x_579_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_579_, 0, v___y_573_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = 0;
v___x_581_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set_uint8(v___x_581_, sizeof(void*)*1, v___x_580_);
v___x_582_ = l_Repr_addAppParen(v___x_581_, v_prec_517_);
return v___x_582_;
}
}
}
}
case 4:
{
uint8_t v_mode_589_; lean_object* v_string_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_localinst_518_);
lean_dec_ref(v_inst_515_);
v_mode_589_ = lean_ctor_get_uint8(v_x_516_, sizeof(void*)*1);
v_string_590_ = lean_ctor_get(v_x_516_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_615_ == 0)
{
v___x_592_ = v_x_516_;
v_isShared_593_ = v_isSharedCheck_615_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_string_590_);
lean_dec(v_x_516_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_615_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___y_595_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1024u);
v___x_612_ = lean_nat_dec_le(v___x_611_, v_prec_517_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_595_ = v___x_613_;
goto v___jp_594_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_595_ = v___x_614_;
goto v___jp_594_;
}
v___jp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_608_; 
v___x_596_ = lean_box(1);
v___x_597_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__14));
v___x_598_ = lean_unsigned_to_nat(1024u);
v___x_599_ = l_Lean_Doc_instReprMathMode_repr(v_mode_589_, v___x_598_);
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_597_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_596_);
v___x_602_ = l_String_quote(v_string_590_);
v___x_603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_601_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
lean_inc(v___y_595_);
v___x_605_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_605_, 0, v___y_595_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = 0;
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 6);
lean_ctor_set(v___x_592_, 0, v___x_605_);
v___x_608_ = v___x_592_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_605_);
v___x_608_ = v_reuseFailAlloc_610_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; 
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*1, v___x_606_);
v___x_609_ = l_Repr_addAppParen(v___x_608_, v_prec_517_);
return v___x_609_;
}
}
}
}
case 5:
{
lean_object* v_string_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_localinst_518_);
lean_dec_ref(v_inst_515_);
v_string_616_ = lean_ctor_get(v_x_516_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_636_ == 0)
{
v___x_618_ = v_x_516_;
v_isShared_619_ = v_isSharedCheck_636_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_string_616_);
lean_dec(v_x_516_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_636_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___y_621_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = lean_unsigned_to_nat(1024u);
v___x_633_ = lean_nat_dec_le(v___x_632_, v_prec_517_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_621_ = v___x_634_;
goto v___jp_620_;
}
else
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_621_ = v___x_635_;
goto v___jp_620_;
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_622_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__17));
v___x_623_ = l_String_quote(v_string_616_);
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 3);
lean_ctor_set(v___x_618_, 0, v___x_623_);
v___x_625_ = v___x_618_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_631_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_622_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
lean_inc(v___y_621_);
v___x_627_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_627_, 0, v___y_621_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = 0;
v___x_629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v___x_628_);
v___x_630_ = l_Repr_addAppParen(v___x_629_, v_prec_517_);
return v___x_630_;
}
}
}
}
case 6:
{
lean_object* v_content_637_; lean_object* v_url_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_inst_515_);
v_content_637_ = lean_ctor_get(v_x_516_, 0);
v_url_638_ = lean_ctor_get(v_x_516_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_662_ == 0)
{
v___x_640_ = v_x_516_;
v_isShared_641_ = v_isSharedCheck_662_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_url_638_);
lean_inc(v_content_637_);
lean_dec(v_x_516_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_662_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___y_643_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(1024u);
v___x_659_ = lean_nat_dec_le(v___x_658_, v_prec_517_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_643_ = v___x_660_;
goto v___jp_642_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_643_ = v___x_661_;
goto v___jp_642_;
}
v___jp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_644_ = lean_box(1);
v___x_645_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__20));
v___x_646_ = l_Array_repr___redArg(v_localinst_518_, v_content_637_);
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 5);
lean_ctor_set(v___x_640_, 1, v___x_646_);
lean_ctor_set(v___x_640_, 0, v___x_645_);
v___x_648_ = v___x_640_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_646_);
v___x_648_ = v_reuseFailAlloc_657_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_644_);
v___x_650_ = l_String_quote(v_url_638_);
v___x_651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_649_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
lean_inc(v___y_643_);
v___x_653_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_653_, 0, v___y_643_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = 0;
v___x_655_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*1, v___x_654_);
v___x_656_ = l_Repr_addAppParen(v___x_655_, v_prec_517_);
return v___x_656_;
}
}
}
}
case 7:
{
lean_object* v_name_663_; lean_object* v_content_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_inst_515_);
v_name_663_ = lean_ctor_get(v_x_516_, 0);
v_content_664_ = lean_ctor_get(v_x_516_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_688_ == 0)
{
v___x_666_ = v_x_516_;
v_isShared_667_ = v_isSharedCheck_688_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_content_664_);
lean_inc(v_name_663_);
lean_dec(v_x_516_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_688_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___y_669_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_unsigned_to_nat(1024u);
v___x_685_ = lean_nat_dec_le(v___x_684_, v_prec_517_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_669_ = v___x_686_;
goto v___jp_668_;
}
else
{
lean_object* v___x_687_; 
v___x_687_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_669_ = v___x_687_;
goto v___jp_668_;
}
v___jp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_670_ = lean_box(1);
v___x_671_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__23));
v___x_672_ = l_String_quote(v_name_663_);
v___x_673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 5);
lean_ctor_set(v___x_666_, 1, v___x_673_);
lean_ctor_set(v___x_666_, 0, v___x_671_);
v___x_675_ = v___x_666_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_683_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___x_670_);
v___x_677_ = l_Array_repr___redArg(v_localinst_518_, v_content_664_);
v___x_678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
lean_inc(v___y_669_);
v___x_679_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_679_, 0, v___y_669_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = 0;
v___x_681_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*1, v___x_680_);
v___x_682_ = l_Repr_addAppParen(v___x_681_, v_prec_517_);
return v___x_682_;
}
}
}
}
case 8:
{
lean_object* v_alt_689_; lean_object* v_url_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v_localinst_518_);
lean_dec_ref(v_inst_515_);
v_alt_689_ = lean_ctor_get(v_x_516_, 0);
v_url_690_ = lean_ctor_get(v_x_516_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_715_ == 0)
{
v___x_692_ = v_x_516_;
v_isShared_693_ = v_isSharedCheck_715_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_url_690_);
lean_inc(v_alt_689_);
lean_dec(v_x_516_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_715_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___y_695_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = lean_unsigned_to_nat(1024u);
v___x_712_ = lean_nat_dec_le(v___x_711_, v_prec_517_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_695_ = v___x_713_;
goto v___jp_694_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_695_ = v___x_714_;
goto v___jp_694_;
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_696_ = lean_box(1);
v___x_697_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__26));
v___x_698_ = l_String_quote(v_alt_689_);
v___x_699_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 5);
lean_ctor_set(v___x_692_, 1, v___x_699_);
lean_ctor_set(v___x_692_, 0, v___x_697_);
v___x_701_ = v___x_692_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_699_);
v___x_701_ = v_reuseFailAlloc_710_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_696_);
v___x_703_ = l_String_quote(v_url_690_);
v___x_704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
v___x_705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_702_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
lean_inc(v___y_695_);
v___x_706_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_706_, 0, v___y_695_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = 0;
v___x_708_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*1, v___x_707_);
v___x_709_ = l_Repr_addAppParen(v___x_708_, v_prec_517_);
return v___x_709_;
}
}
}
}
case 9:
{
lean_object* v_content_716_; lean_object* v___y_718_; lean_object* v___x_726_; uint8_t v___x_727_; 
lean_dec_ref(v_inst_515_);
v_content_716_ = lean_ctor_get(v_x_516_, 0);
lean_inc_ref(v_content_716_);
lean_dec_ref_known(v_x_516_, 1);
v___x_726_ = lean_unsigned_to_nat(1024u);
v___x_727_ = lean_nat_dec_le(v___x_726_, v_prec_517_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_718_ = v___x_728_;
goto v___jp_717_;
}
else
{
lean_object* v___x_729_; 
v___x_729_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_718_ = v___x_729_;
goto v___jp_717_;
}
v___jp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_719_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__29));
v___x_720_ = l_Array_repr___redArg(v_localinst_518_, v_content_716_);
v___x_721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
lean_inc(v___y_718_);
v___x_722_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_722_, 0, v___y_718_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = 0;
v___x_724_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*1, v___x_723_);
v___x_725_ = l_Repr_addAppParen(v___x_724_, v_prec_517_);
return v___x_725_;
}
}
default: 
{
lean_object* v_container_730_; lean_object* v_content_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_755_; 
v_container_730_ = lean_ctor_get(v_x_516_, 0);
v_content_731_ = lean_ctor_get(v_x_516_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_755_ == 0)
{
v___x_733_ = v_x_516_;
v_isShared_734_ = v_isSharedCheck_755_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_content_731_);
lean_inc(v_container_730_);
lean_dec(v_x_516_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_755_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___y_736_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_unsigned_to_nat(1024u);
v___x_752_ = lean_nat_dec_le(v___x_751_, v_prec_517_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
v___x_753_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_736_ = v___x_753_;
goto v___jp_735_;
}
else
{
lean_object* v___x_754_; 
v___x_754_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_736_ = v___x_754_;
goto v___jp_735_;
}
v___jp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_737_ = lean_box(1);
v___x_738_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___redArg___closed__32));
v___x_739_ = lean_unsigned_to_nat(1024u);
v___x_740_ = lean_apply_2(v_inst_515_, v_container_730_, v___x_739_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 5);
lean_ctor_set(v___x_733_, 1, v___x_740_);
lean_ctor_set(v___x_733_, 0, v___x_738_);
v___x_742_ = v___x_733_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_750_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_737_);
v___x_744_ = l_Array_repr___redArg(v_localinst_518_, v_content_731_);
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_inc(v___y_736_);
v___x_746_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_746_, 0, v___y_736_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = 0;
v___x_748_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*1, v___x_747_);
v___x_749_ = l_Repr_addAppParen(v___x_748_, v_prec_517_);
return v___x_749_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr(lean_object* v_i_756_, lean_object* v_inst_757_, lean_object* v_x_758_, lean_object* v_prec_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Doc_instReprInline_repr___redArg(v_inst_757_, v_x_758_, v_prec_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___boxed(lean_object* v_i_761_, lean_object* v_inst_762_, lean_object* v_x_763_, lean_object* v_prec_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Doc_instReprInline_repr(v_i_761_, v_inst_762_, v_x_763_, v_prec_764_);
lean_dec(v_prec_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline___redArg(lean_object* v_inst_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_767_, 0, lean_box(0));
lean_closure_set(v___x_767_, 1, v_inst_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline(lean_object* v_i_768_, lean_object* v_inst_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_770_, 0, lean_box(0));
lean_closure_set(v___x_770_, 1, v_inst_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg(){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = ((lean_object*)(l_Lean_Doc_instInhabitedInline_default___redArg___closed__1));
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default___redArg___boxed(lean_object* v___dummy_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Doc_instInhabitedInline_default___redArg();
return v_res_777_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedInline_default___closed__0(void){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Doc_instInhabitedInline_default___redArg();
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline_default(lean_object* v_i_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg(){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline___redArg___boxed(lean_object* v___dummy_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Doc_instInhabitedInline___redArg();
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedInline(lean_object* v_a_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = lean_obj_once(&l_Lean_Doc_instInhabitedInline_default___closed__0, &l_Lean_Doc_instInhabitedInline_default___closed__0_once, _init_l_Lean_Doc_instInhabitedInline_default___closed__0);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg(lean_object* v_x_787_){
_start:
{
lean_inc_ref(v_x_787_);
return v_x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___redArg___boxed(lean_object* v_x_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Doc_Inline_cast___redArg(v_x_788_);
lean_dec_ref(v_x_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast(lean_object* v_i_790_, lean_object* v_i_x27_791_, lean_object* v_inlines__eq_792_, lean_object* v_x_793_){
_start:
{
lean_inc_ref(v_x_793_);
return v_x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_cast___boxed(lean_object* v_i_794_, lean_object* v_i_x27_795_, lean_object* v_inlines__eq_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Doc_Inline_cast(v_i_794_, v_i_x27_795_, v_inlines__eq_796_, v_x_797_);
lean_dec_ref(v_x_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___lam__0(lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
if (lean_obj_tag(v_x_799_) == 9)
{
lean_object* v_content_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_content_801_ = lean_ctor_get(v_x_799_, 0);
v___x_802_ = lean_array_get_size(v_content_801_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_nat_dec_eq(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
if (lean_obj_tag(v_x_800_) == 9)
{
lean_object* v_content_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_815_; 
v_content_805_ = lean_ctor_get(v_x_800_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_800_);
if (v_isSharedCheck_815_ == 0)
{
v___x_807_ = v_x_800_;
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_content_805_);
lean_dec(v_x_800_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_array_get_size(v_content_805_);
v___x_810_ = lean_nat_dec_eq(v___x_809_, v___x_803_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_813_; 
lean_inc_ref(v_content_801_);
lean_dec_ref_known(v_x_799_, 1);
v___x_811_ = l_Array_append___redArg(v_content_801_, v_content_805_);
lean_dec_ref(v_content_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_811_);
v___x_813_ = v___x_807_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_del_object(v___x_807_);
lean_dec_ref(v_content_805_);
return v_x_799_;
}
}
}
else
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_823_; 
lean_inc_ref(v_content_801_);
v_isSharedCheck_823_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_x_799_, 0);
lean_dec(v_unused_824_);
v___x_817_ = v_x_799_;
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_x_799_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = lean_array_push(v_content_801_, v_x_800_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_819_);
v___x_821_ = v___x_817_;
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
}
}
else
{
lean_dec_ref_known(v_x_799_, 1);
return v_x_800_;
}
}
else
{
if (lean_obj_tag(v_x_800_) == 9)
{
lean_object* v_content_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_839_; 
v_content_825_ = lean_ctor_get(v_x_800_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v_x_800_);
if (v_isSharedCheck_839_ == 0)
{
v___x_827_ = v_x_800_;
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_content_825_);
lean_dec(v_x_800_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_829_ = lean_array_get_size(v_content_825_);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_nat_dec_eq(v___x_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = lean_mk_empty_array_with_capacity(v___x_832_);
v___x_834_ = lean_array_push(v___x_833_, v_x_799_);
v___x_835_ = l_Array_append___redArg(v___x_834_, v_content_825_);
lean_dec_ref(v_content_825_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_835_);
v___x_837_ = v___x_827_;
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
else
{
lean_del_object(v___x_827_);
lean_dec_ref(v_content_825_);
return v_x_799_;
}
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_840_ = lean_unsigned_to_nat(2u);
v___x_841_ = lean_mk_empty_array_with_capacity(v___x_840_);
v___x_842_ = lean_array_push(v___x_841_, v_x_799_);
v___x_843_ = lean_array_push(v___x_842_, v_x_800_);
v___x_844_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg(){
_start:
{
lean_object* v___f_847_; 
v___f_847_ = ((lean_object*)(l_Lean_Doc_instAppendInline___redArg___closed__0));
return v___f_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline___redArg___boxed(lean_object* v___dummy_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Doc_instAppendInline___redArg();
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instAppendInline(lean_object* v_i_850_){
_start:
{
lean_object* v___f_851_; 
v___f_851_ = ((lean_object*)(l_Lean_Doc_instAppendInline___redArg___closed__0));
return v___f_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg(){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = ((lean_object*)(l_Lean_Doc_Inline_empty___redArg___closed__1));
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty___redArg___boxed(lean_object* v___dummy_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Doc_Inline_empty___redArg();
return v_res_859_;
}
}
static lean_object* _init_l_Lean_Doc_Inline_empty___closed__0(void){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Doc_Inline_empty___redArg();
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_empty(lean_object* v_i_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = lean_obj_once(&l_Lean_Doc_Inline_empty___closed__0, &l_Lean_Doc_Inline_empty___closed__0_once, _init_l_Lean_Doc_Inline_empty___closed__0);
return v___x_862_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_unsigned_to_nat(12u);
v___x_877_ = lean_nat_to_int(v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__0));
v___x_880_ = lean_string_length(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__9);
v___x_882_ = lean_nat_to_int(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___redArg(lean_object* v_inst_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_889_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__6));
v___x_890_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_891_ = l_Array_repr___redArg(v_inst_887_, v_x_888_);
v___x_892_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = 0;
v___x_894_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set_uint8(v___x_894_, sizeof(void*)*1, v___x_893_);
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_889_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_897_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_895_);
v___x_899_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_896_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*1, v___x_893_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr(lean_object* v_00_u03b1_903_, lean_object* v_inst_904_, lean_object* v_x_905_, lean_object* v_prec_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Doc_instReprListItem_repr___redArg(v_inst_904_, v_x_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___boxed(lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_x_910_, lean_object* v_prec_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Doc_instReprListItem_repr(v_00_u03b1_908_, v_inst_909_, v_x_910_, v_prec_911_);
lean_dec(v_prec_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem___redArg(lean_object* v_inst_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_914_, 0, lean_box(0));
lean_closure_set(v___x_914_, 1, v_inst_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem(lean_object* v_00_u03b1_915_, lean_object* v_inst_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_917_, 0, lean_box(0));
lean_closure_set(v___x_917_, 1, v_inst_916_);
return v___x_917_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq___redArg(lean_object* v_inst_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_array_get_size(v_x_919_);
v___x_922_ = lean_array_get_size(v_x_920_);
v___x_923_ = lean_nat_dec_eq(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_dec_ref(v_inst_918_);
return v___x_923_;
}
else
{
uint8_t v___x_924_; 
v___x_924_ = l_Array_isEqvAux___redArg(v_x_919_, v_x_920_, v_inst_918_, v___x_921_);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___redArg___boxed(lean_object* v_inst_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_925_, v_x_926_, v_x_927_);
lean_dec_ref(v_x_927_);
lean_dec_ref(v_x_926_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqListItem_beq(lean_object* v_00_u03b1_930_, lean_object* v_inst_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = l_Lean_Doc_instBEqListItem_beq___redArg(v_inst_931_, v_x_932_, v_x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem_beq___boxed(lean_object* v_00_u03b1_935_, lean_object* v_inst_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
uint8_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Lean_Doc_instBEqListItem_beq(v_00_u03b1_935_, v_inst_936_, v_x_937_, v_x_938_);
lean_dec_ref(v_x_938_);
lean_dec_ref(v_x_937_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem___redArg(lean_object* v_inst_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_942_, 0, lean_box(0));
lean_closure_set(v___x_942_, 1, v_inst_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqListItem(lean_object* v_00_u03b1_943_, lean_object* v_inst_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_945_, 0, lean_box(0));
lean_closure_set(v___x_945_, 1, v_inst_944_);
return v___x_945_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord___redArg(lean_object* v_inst_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_inst_946_, v_x_947_, v_x_948_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___redArg___boxed(lean_object* v_inst_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
uint8_t v_res_954_; lean_object* v_r_955_; 
v_res_954_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_951_, v_x_952_, v_x_953_);
lean_dec_ref(v_x_953_);
lean_dec_ref(v_x_952_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdListItem_ord(lean_object* v_00_u03b1_956_, lean_object* v_inst_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
uint8_t v___x_960_; 
v___x_960_ = l_Lean_Doc_instOrdListItem_ord___redArg(v_inst_957_, v_x_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem_ord___boxed(lean_object* v_00_u03b1_961_, lean_object* v_inst_962_, lean_object* v_x_963_, lean_object* v_x_964_){
_start:
{
uint8_t v_res_965_; lean_object* v_r_966_; 
v_res_965_ = l_Lean_Doc_instOrdListItem_ord(v_00_u03b1_961_, v_inst_962_, v_x_963_, v_x_964_);
lean_dec_ref(v_x_964_);
lean_dec_ref(v_x_963_);
v_r_966_ = lean_box(v_res_965_);
return v_r_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem___redArg(lean_object* v_inst_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_968_, 0, lean_box(0));
lean_closure_set(v___x_968_, 1, v_inst_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdListItem(lean_object* v_00_u03b1_969_, lean_object* v_inst_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_971_, 0, lean_box(0));
lean_closure_set(v___x_971_, 1, v_inst_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg(){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l_Lean_Doc_instInhabitedListItem_default___redArg___closed__0));
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default___redArg___boxed(lean_object* v___dummy_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Doc_instInhabitedListItem_default___redArg();
return v_res_977_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedListItem_default___closed__0(void){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Doc_instInhabitedListItem_default___redArg();
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem_default(lean_object* v_00_u03b1_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem___redArg(){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem___redArg___boxed(lean_object* v___dummy_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Doc_instInhabitedListItem___redArg();
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedListItem(lean_object* v_a_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = lean_obj_once(&l_Lean_Doc_instInhabitedListItem_default___closed__0, &l_Lean_Doc_instInhabitedListItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedListItem_default___closed__0);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_unsigned_to_nat(8u);
v___x_997_ = lean_nat_to_int(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___redArg(lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v_term_1007_; lean_object* v_desc_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1040_; 
v_term_1007_ = lean_ctor_get(v_x_1006_, 0);
v_desc_1008_ = lean_ctor_get(v_x_1006_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_x_1006_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1010_ = v_x_1006_;
v_isShared_1011_ = v_isSharedCheck_1040_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_desc_1008_);
lean_inc(v_term_1007_);
lean_dec(v_x_1006_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1040_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1012_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1013_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__3));
v___x_1014_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___redArg___closed__4);
v___x_1015_ = l_Array_repr___redArg(v_inst_1004_, v_term_1007_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set_tag(v___x_1010_, 4);
lean_ctor_set(v___x_1010_, 1, v___x_1015_);
lean_ctor_set(v___x_1010_, 0, v___x_1014_);
v___x_1017_ = v___x_1010_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1018_ = 0;
v___x_1019_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set_uint8(v___x_1019_, sizeof(void*)*1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1013_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_box(1);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__8));
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1012_);
v___x_1028_ = l_Array_repr___redArg(v_inst_1005_, v_desc_1008_);
v___x_1029_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1014_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*1, v___x_1018_);
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1027_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_1033_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_1034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_1031_);
v___x_1035_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1032_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*1, v___x_1018_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr(lean_object* v_00_u03b1_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_x_1045_, lean_object* v_prec_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_Doc_instReprDescItem_repr___redArg(v_inst_1043_, v_inst_1044_, v_x_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_x_1052_, lean_object* v_prec_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Doc_instReprDescItem_repr(v_00_u03b1_1048_, v_00_u03b2_1049_, v_inst_1050_, v_inst_1051_, v_x_1052_, v_prec_1053_);
lean_dec(v_prec_1053_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem___redArg(lean_object* v_inst_1055_, lean_object* v_inst_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1057_, 0, lean_box(0));
lean_closure_set(v___x_1057_, 1, lean_box(0));
lean_closure_set(v___x_1057_, 2, v_inst_1055_);
lean_closure_set(v___x_1057_, 3, v_inst_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem(lean_object* v_00_u03b1_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_inst_1060_, lean_object* v_inst_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1062_, 0, lean_box(0));
lean_closure_set(v___x_1062_, 1, lean_box(0));
lean_closure_set(v___x_1062_, 2, v_inst_1060_);
lean_closure_set(v___x_1062_, 3, v_inst_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq___redArg(lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_){
_start:
{
lean_object* v_term_1067_; lean_object* v_desc_1068_; lean_object* v_term_1069_; lean_object* v_desc_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v_term_1067_ = lean_ctor_get(v_x_1065_, 0);
v_desc_1068_ = lean_ctor_get(v_x_1065_, 1);
v_term_1069_ = lean_ctor_get(v_x_1066_, 0);
v_desc_1070_ = lean_ctor_get(v_x_1066_, 1);
v___x_1071_ = lean_array_get_size(v_term_1067_);
v___x_1072_ = lean_array_get_size(v_term_1069_);
v___x_1073_ = lean_nat_dec_eq(v___x_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec_ref(v_inst_1064_);
lean_dec_ref(v_inst_1063_);
return v___x_1073_;
}
else
{
uint8_t v___x_1074_; 
v___x_1074_ = l_Array_isEqvAux___redArg(v_term_1067_, v_term_1069_, v_inst_1063_, v___x_1071_);
if (v___x_1074_ == 0)
{
lean_dec_ref(v_inst_1064_);
return v___x_1074_;
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = lean_array_get_size(v_desc_1068_);
v___x_1076_ = lean_array_get_size(v_desc_1070_);
v___x_1077_ = lean_nat_dec_eq(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec_ref(v_inst_1064_);
return v___x_1077_;
}
else
{
uint8_t v___x_1078_; 
v___x_1078_ = l_Array_isEqvAux___redArg(v_desc_1068_, v_desc_1070_, v_inst_1064_, v___x_1075_);
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___redArg___boxed(lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
uint8_t v_res_1083_; lean_object* v_r_1084_; 
v_res_1083_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1079_, v_inst_1080_, v_x_1081_, v_x_1082_);
lean_dec_ref(v_x_1082_);
lean_dec_ref(v_x_1081_);
v_r_1084_ = lean_box(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDescItem_beq(lean_object* v_00_u03b1_1085_, lean_object* v_00_u03b2_1086_, lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
uint8_t v___x_1091_; 
v___x_1091_ = l_Lean_Doc_instBEqDescItem_beq___redArg(v_inst_1087_, v_inst_1088_, v_x_1089_, v_x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem_beq___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_00_u03b2_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
uint8_t v_res_1098_; lean_object* v_r_1099_; 
v_res_1098_ = l_Lean_Doc_instBEqDescItem_beq(v_00_u03b1_1092_, v_00_u03b2_1093_, v_inst_1094_, v_inst_1095_, v_x_1096_, v_x_1097_);
lean_dec_ref(v_x_1097_);
lean_dec_ref(v_x_1096_);
v_r_1099_ = lean_box(v_res_1098_);
return v_r_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem___redArg(lean_object* v_inst_1100_, lean_object* v_inst_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1102_, 0, lean_box(0));
lean_closure_set(v___x_1102_, 1, lean_box(0));
lean_closure_set(v___x_1102_, 2, v_inst_1100_);
lean_closure_set(v___x_1102_, 3, v_inst_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDescItem(lean_object* v_00_u03b1_1103_, lean_object* v_00_u03b2_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1107_, 0, lean_box(0));
lean_closure_set(v___x_1107_, 1, lean_box(0));
lean_closure_set(v___x_1107_, 2, v_inst_1105_);
lean_closure_set(v___x_1107_, 3, v_inst_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord___redArg(lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v_term_1112_; lean_object* v_desc_1113_; lean_object* v_term_1114_; lean_object* v_desc_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_term_1112_ = lean_ctor_get(v_x_1110_, 0);
v_desc_1113_ = lean_ctor_get(v_x_1110_, 1);
v_term_1114_ = lean_ctor_get(v_x_1111_, 0);
v_desc_1115_ = lean_ctor_get(v_x_1111_, 1);
v___x_1116_ = lean_unsigned_to_nat(0u);
v___x_1117_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_inst_1108_, v_term_1112_, v_term_1114_, v___x_1116_);
if (v___x_1117_ == 1)
{
uint8_t v___x_1118_; 
v___x_1118_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_inst_1109_, v_desc_1113_, v_desc_1115_, v___x_1116_);
return v___x_1118_;
}
else
{
lean_dec_ref(v_inst_1109_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___redArg___boxed(lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1119_, v_inst_1120_, v_x_1121_, v_x_1122_);
lean_dec_ref(v_x_1122_);
lean_dec_ref(v_x_1121_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdDescItem_ord(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_Doc_instOrdDescItem_ord___redArg(v_inst_1127_, v_inst_1128_, v_x_1129_, v_x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem_ord___boxed(lean_object* v_00_u03b1_1132_, lean_object* v_00_u03b2_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Lean_Doc_instOrdDescItem_ord(v_00_u03b1_1132_, v_00_u03b2_1133_, v_inst_1134_, v_inst_1135_, v_x_1136_, v_x_1137_);
lean_dec_ref(v_x_1137_);
lean_dec_ref(v_x_1136_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem___redArg(lean_object* v_inst_1140_, lean_object* v_inst_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1142_, 0, lean_box(0));
lean_closure_set(v___x_1142_, 1, lean_box(0));
lean_closure_set(v___x_1142_, 2, v_inst_1140_);
lean_closure_set(v___x_1142_, 3, v_inst_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdDescItem(lean_object* v_00_u03b1_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1147_, 0, lean_box(0));
lean_closure_set(v___x_1147_, 1, lean_box(0));
lean_closure_set(v___x_1147_, 2, v_inst_1145_);
lean_closure_set(v___x_1147_, 3, v_inst_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg(){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = ((lean_object*)(l_Lean_Doc_instInhabitedDescItem_default___redArg___closed__0));
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default___redArg___boxed(lean_object* v___dummy_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
return v_res_1153_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0(void){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Doc_instInhabitedDescItem_default___redArg();
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem_default(lean_object* v_00_u03b1_1155_, lean_object* v_00_u03b2_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg(){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem___redArg___boxed(lean_object* v___dummy_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Doc_instInhabitedDescItem___redArg();
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedDescItem(lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_obj_once(&l_Lean_Doc_instInhabitedDescItem_default___closed__0, &l_Lean_Doc_instInhabitedDescItem_default___closed__0_once, _init_l_Lean_Doc_instInhabitedDescItem_default___closed__0);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg(lean_object* v_x_1165_){
_start:
{
switch(lean_obj_tag(v_x_1165_))
{
case 0:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
return v___x_1166_;
}
case 1:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_unsigned_to_nat(1u);
return v___x_1167_;
}
case 2:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_unsigned_to_nat(2u);
return v___x_1168_;
}
case 3:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_unsigned_to_nat(3u);
return v___x_1169_;
}
case 4:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_unsigned_to_nat(4u);
return v___x_1170_;
}
case 5:
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_unsigned_to_nat(5u);
return v___x_1171_;
}
case 6:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_unsigned_to_nat(6u);
return v___x_1172_;
}
default: 
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_unsigned_to_nat(7u);
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___redArg___boxed(lean_object* v_x_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1174_);
lean_dec_ref(v_x_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx(lean_object* v_i_1176_, lean_object* v_b_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Doc_Block_ctorIdx___redArg(v_x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorIdx___boxed(lean_object* v_i_1180_, lean_object* v_b_1181_, lean_object* v_x_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Doc_Block_ctorIdx(v_i_1180_, v_b_1181_, v_x_1182_);
lean_dec_ref(v_x_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___redArg(lean_object* v_t_1184_, lean_object* v_k_1185_){
_start:
{
switch(lean_obj_tag(v_t_1184_))
{
case 3:
{
lean_object* v_start_1186_; lean_object* v_items_1187_; lean_object* v___x_1188_; 
v_start_1186_ = lean_ctor_get(v_t_1184_, 0);
lean_inc(v_start_1186_);
v_items_1187_ = lean_ctor_get(v_t_1184_, 1);
lean_inc_ref(v_items_1187_);
lean_dec_ref_known(v_t_1184_, 2);
v___x_1188_ = lean_apply_2(v_k_1185_, v_start_1186_, v_items_1187_);
return v___x_1188_;
}
case 7:
{
lean_object* v_container_1189_; lean_object* v_content_1190_; lean_object* v___x_1191_; 
v_container_1189_ = lean_ctor_get(v_t_1184_, 0);
lean_inc(v_container_1189_);
v_content_1190_ = lean_ctor_get(v_t_1184_, 1);
lean_inc_ref(v_content_1190_);
lean_dec_ref_known(v_t_1184_, 2);
v___x_1191_ = lean_apply_2(v_k_1185_, v_container_1189_, v_content_1190_);
return v___x_1191_;
}
default: 
{
lean_object* v_contents_1192_; lean_object* v___x_1193_; 
v_contents_1192_ = lean_ctor_get(v_t_1184_, 0);
lean_inc_ref(v_contents_1192_);
lean_dec_ref(v_t_1184_);
v___x_1193_ = lean_apply_1(v_k_1185_, v_contents_1192_);
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim(lean_object* v_i_1194_, lean_object* v_b_1195_, lean_object* v_motive__1_1196_, lean_object* v_ctorIdx_1197_, lean_object* v_t_1198_, lean_object* v_h_1199_, lean_object* v_k_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1198_, v_k_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ctorElim___boxed(lean_object* v_i_1202_, lean_object* v_b_1203_, lean_object* v_motive__1_1204_, lean_object* v_ctorIdx_1205_, lean_object* v_t_1206_, lean_object* v_h_1207_, lean_object* v_k_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Doc_Block_ctorElim(v_i_1202_, v_b_1203_, v_motive__1_1204_, v_ctorIdx_1205_, v_t_1206_, v_h_1207_, v_k_1208_);
lean_dec(v_ctorIdx_1205_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim___redArg(lean_object* v_t_1210_, lean_object* v_para_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1210_, v_para_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_para_elim(lean_object* v_i_1213_, lean_object* v_b_1214_, lean_object* v_motive__1_1215_, lean_object* v_t_1216_, lean_object* v_h_1217_, lean_object* v_para_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1216_, v_para_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim___redArg(lean_object* v_t_1220_, lean_object* v_code_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1220_, v_code_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_code_elim(lean_object* v_i_1223_, lean_object* v_b_1224_, lean_object* v_motive__1_1225_, lean_object* v_t_1226_, lean_object* v_h_1227_, lean_object* v_code_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1226_, v_code_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim___redArg(lean_object* v_t_1230_, lean_object* v_ul_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1230_, v_ul_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ul_elim(lean_object* v_i_1233_, lean_object* v_b_1234_, lean_object* v_motive__1_1235_, lean_object* v_t_1236_, lean_object* v_h_1237_, lean_object* v_ul_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1236_, v_ul_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim___redArg(lean_object* v_t_1240_, lean_object* v_ol_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1240_, v_ol_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_ol_elim(lean_object* v_i_1243_, lean_object* v_b_1244_, lean_object* v_motive__1_1245_, lean_object* v_t_1246_, lean_object* v_h_1247_, lean_object* v_ol_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1246_, v_ol_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim___redArg(lean_object* v_t_1250_, lean_object* v_dl_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1250_, v_dl_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_dl_elim(lean_object* v_i_1253_, lean_object* v_b_1254_, lean_object* v_motive__1_1255_, lean_object* v_t_1256_, lean_object* v_h_1257_, lean_object* v_dl_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1256_, v_dl_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim___redArg(lean_object* v_t_1260_, lean_object* v_blockquote_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1260_, v_blockquote_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_blockquote_elim(lean_object* v_i_1263_, lean_object* v_b_1264_, lean_object* v_motive__1_1265_, lean_object* v_t_1266_, lean_object* v_h_1267_, lean_object* v_blockquote_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1266_, v_blockquote_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim___redArg(lean_object* v_t_1270_, lean_object* v_concat_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1270_, v_concat_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_concat_elim(lean_object* v_i_1273_, lean_object* v_b_1274_, lean_object* v_motive__1_1275_, lean_object* v_t_1276_, lean_object* v_h_1277_, lean_object* v_concat_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1276_, v_concat_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim___redArg(lean_object* v_t_1280_, lean_object* v_other_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1280_, v_other_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_other_elim(lean_object* v_i_1283_, lean_object* v_b_1284_, lean_object* v_motive__1_1285_, lean_object* v_t_1286_, lean_object* v_h_1287_, lean_object* v_other_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_Doc_Block_ctorElim___redArg(v_t_1286_, v_other_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___redArg___boxed(lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_res_1294_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1290_, v_inst_1291_, v_x_1292_, v_x_1293_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq___redArg(lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v_localinst_1300_; lean_object* v_a_1302_; lean_object* v_b_1303_; 
lean_inc_ref(v_inst_1297_);
lean_inc_ref(v_inst_1296_);
v_localinst_1300_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1300_, 0, v_inst_1296_);
lean_closure_set(v_localinst_1300_, 1, v_inst_1297_);
switch(lean_obj_tag(v_x_1298_))
{
case 0:
{
lean_dec_ref(v_localinst_1300_);
lean_dec_ref(v_inst_1297_);
if (lean_obj_tag(v_x_1299_) == 0)
{
lean_object* v_contents_1308_; lean_object* v_contents_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_contents_1308_ = lean_ctor_get(v_x_1298_, 0);
lean_inc_ref(v_contents_1308_);
lean_dec_ref_known(v_x_1298_, 1);
v_contents_1309_ = lean_ctor_get(v_x_1299_, 0);
lean_inc_ref(v_contents_1309_);
lean_dec_ref_known(v_x_1299_, 1);
v___x_1310_ = lean_array_get_size(v_contents_1308_);
v___x_1311_ = lean_array_get_size(v_contents_1309_);
v___x_1312_ = lean_nat_dec_eq(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_dec_ref(v_contents_1309_);
lean_dec_ref(v_contents_1308_);
lean_dec_ref(v_inst_1296_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1313_, 0, lean_box(0));
lean_closure_set(v___x_1313_, 1, v_inst_1296_);
v___x_1314_ = l_Array_isEqvAux___redArg(v_contents_1308_, v_contents_1309_, v___x_1313_, v___x_1310_);
lean_dec_ref(v_contents_1309_);
lean_dec_ref(v_contents_1308_);
return v___x_1314_;
}
}
else
{
uint8_t v___x_1315_; 
lean_dec_ref_known(v_x_1298_, 1);
lean_dec_ref(v_x_1299_);
lean_dec_ref(v_inst_1296_);
v___x_1315_ = 0;
return v___x_1315_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1300_);
lean_dec_ref(v_inst_1297_);
lean_dec_ref(v_inst_1296_);
if (lean_obj_tag(v_x_1299_) == 1)
{
lean_object* v_content_1316_; lean_object* v_content_1317_; uint8_t v___x_1318_; 
v_content_1316_ = lean_ctor_get(v_x_1298_, 0);
lean_inc_ref(v_content_1316_);
lean_dec_ref_known(v_x_1298_, 1);
v_content_1317_ = lean_ctor_get(v_x_1299_, 0);
lean_inc_ref(v_content_1317_);
lean_dec_ref_known(v_x_1299_, 1);
v___x_1318_ = lean_string_dec_eq(v_content_1316_, v_content_1317_);
lean_dec_ref(v_content_1317_);
lean_dec_ref(v_content_1316_);
return v___x_1318_;
}
else
{
uint8_t v___x_1319_; 
lean_dec_ref_known(v_x_1298_, 1);
lean_dec_ref(v_x_1299_);
v___x_1319_ = 0;
return v___x_1319_;
}
}
case 2:
{
lean_dec_ref(v_inst_1297_);
lean_dec_ref(v_inst_1296_);
if (lean_obj_tag(v_x_1299_) == 2)
{
lean_object* v_items_1320_; lean_object* v_items_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_items_1320_ = lean_ctor_get(v_x_1298_, 0);
lean_inc_ref(v_items_1320_);
lean_dec_ref_known(v_x_1298_, 1);
v_items_1321_ = lean_ctor_get(v_x_1299_, 0);
lean_inc_ref(v_items_1321_);
lean_dec_ref_known(v_x_1299_, 1);
v___x_1322_ = lean_array_get_size(v_items_1320_);
v___x_1323_ = lean_array_get_size(v_items_1321_);
v___x_1324_ = lean_nat_dec_eq(v___x_1322_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_dec_ref(v_items_1321_);
lean_dec_ref(v_items_1320_);
lean_dec_ref(v_localinst_1300_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1325_, 0, lean_box(0));
lean_closure_set(v___x_1325_, 1, v_localinst_1300_);
v___x_1326_ = l_Array_isEqvAux___redArg(v_items_1320_, v_items_1321_, v___x_1325_, v___x_1322_);
lean_dec_ref(v_items_1321_);
lean_dec_ref(v_items_1320_);
return v___x_1326_;
}
}
else
{
uint8_t v___x_1327_; 
lean_dec_ref_known(v_x_1298_, 1);
lean_dec_ref(v_localinst_1300_);
lean_dec_ref(v_x_1299_);
v___x_1327_ = 0;
return v___x_1327_;
}
}
case 3:
{
lean_dec_ref(v_inst_1297_);
lean_dec_ref(v_inst_1296_);
if (lean_obj_tag(v_x_1299_) == 3)
{
lean_object* v_start_1328_; lean_object* v_items_1329_; lean_object* v_start_1330_; lean_object* v_items_1331_; uint8_t v___x_1332_; 
v_start_1328_ = lean_ctor_get(v_x_1298_, 0);
lean_inc(v_start_1328_);
v_items_1329_ = lean_ctor_get(v_x_1298_, 1);
lean_inc_ref(v_items_1329_);
lean_dec_ref_known(v_x_1298_, 2);
v_start_1330_ = lean_ctor_get(v_x_1299_, 0);
lean_inc(v_start_1330_);
v_items_1331_ = lean_ctor_get(v_x_1299_, 1);
lean_inc_ref(v_items_1331_);
lean_dec_ref_known(v_x_1299_, 2);
v___x_1332_ = lean_int_dec_eq(v_start_1328_, v_start_1330_);
lean_dec(v_start_1330_);
lean_dec(v_start_1328_);
if (v___x_1332_ == 0)
{
lean_dec_ref(v_items_1331_);
lean_dec_ref(v_items_1329_);
lean_dec_ref(v_localinst_1300_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = lean_array_get_size(v_items_1329_);
v___x_1334_ = lean_array_get_size(v_items_1331_);
v___x_1335_ = lean_nat_dec_eq(v___x_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec_ref(v_items_1331_);
lean_dec_ref(v_items_1329_);
lean_dec_ref(v_localinst_1300_);
return v___x_1335_;
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqListItem_beq___boxed), 4, 2);
lean_closure_set(v___x_1336_, 0, lean_box(0));
lean_closure_set(v___x_1336_, 1, v_localinst_1300_);
v___x_1337_ = l_Array_isEqvAux___redArg(v_items_1329_, v_items_1331_, v___x_1336_, v___x_1333_);
lean_dec_ref(v_items_1331_);
lean_dec_ref(v_items_1329_);
return v___x_1337_;
}
}
}
else
{
uint8_t v___x_1338_; 
lean_dec_ref_known(v_x_1298_, 2);
lean_dec_ref(v_localinst_1300_);
lean_dec_ref(v_x_1299_);
v___x_1338_ = 0;
return v___x_1338_;
}
}
case 4:
{
lean_dec_ref(v_inst_1297_);
if (lean_obj_tag(v_x_1299_) == 4)
{
lean_object* v_items_1339_; lean_object* v_items_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_items_1339_ = lean_ctor_get(v_x_1298_, 0);
lean_inc_ref(v_items_1339_);
lean_dec_ref_known(v_x_1298_, 1);
v_items_1340_ = lean_ctor_get(v_x_1299_, 0);
lean_inc_ref(v_items_1340_);
lean_dec_ref_known(v_x_1299_, 1);
v___x_1341_ = lean_array_get_size(v_items_1339_);
v___x_1342_ = lean_array_get_size(v_items_1340_);
v___x_1343_ = lean_nat_dec_eq(v___x_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_dec_ref(v_items_1340_);
lean_dec_ref(v_items_1339_);
lean_dec_ref(v_localinst_1300_);
lean_dec_ref(v_inst_1296_);
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1344_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1344_, 0, lean_box(0));
lean_closure_set(v___x_1344_, 1, v_inst_1296_);
v___x_1345_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqDescItem_beq___boxed), 6, 4);
lean_closure_set(v___x_1345_, 0, lean_box(0));
lean_closure_set(v___x_1345_, 1, lean_box(0));
lean_closure_set(v___x_1345_, 2, v___x_1344_);
lean_closure_set(v___x_1345_, 3, v_localinst_1300_);
v___x_1346_ = l_Array_isEqvAux___redArg(v_items_1339_, v_items_1340_, v___x_1345_, v___x_1341_);
lean_dec_ref(v_items_1340_);
lean_dec_ref(v_items_1339_);
return v___x_1346_;
}
}
else
{
uint8_t v___x_1347_; 
lean_dec_ref_known(v_x_1298_, 1);
lean_dec_ref(v_localinst_1300_);
lean_dec_ref(v_x_1299_);
lean_dec_ref(v_inst_1296_);
v___x_1347_ = 0;
return v___x_1347_;
}
}
case 5:
{
lean_dec_ref(v_inst_1297_);
lean_dec_ref(v_inst_1296_);
if (lean_obj_tag(v_x_1299_) == 5)
{
lean_object* v_items_1348_; lean_object* v_items_1349_; 
v_items_1348_ = lean_ctor_get(v_x_1298_, 0);
lean_inc_ref(v_items_1348_);
lean_dec_ref_known(v_x_1298_, 1);
v_items_1349_ = lean_ctor_get(v_x_1299_, 0);
lean_inc_ref(v_items_1349_);
lean_dec_ref_known(v_x_1299_, 1);
v_a_1302_ = v_items_1348_;
v_b_1303_ = v_items_1349_;
goto v___jp_1301_;
}
else
{
uint8_t v___x_1350_; 
lean_dec_ref_known(v_x_1298_, 1);
lean_dec_ref(v_localinst_1300_);
lean_dec_ref(v_x_1299_);
v___x_1350_ = 0;
return v___x_1350_;
}
}
case 6:
{
lean_dec_ref(v_inst_1297_);
lean_dec_ref(v_inst_1296_);
if (lean_obj_tag(v_x_1299_) == 6)
{
lean_object* v_content_1351_; lean_object* v_content_1352_; 
v_content_1351_ = lean_ctor_get(v_x_1298_, 0);
lean_inc_ref(v_content_1351_);
lean_dec_ref_known(v_x_1298_, 1);
v_content_1352_ = lean_ctor_get(v_x_1299_, 0);
lean_inc_ref(v_content_1352_);
lean_dec_ref_known(v_x_1299_, 1);
v_a_1302_ = v_content_1351_;
v_b_1303_ = v_content_1352_;
goto v___jp_1301_;
}
else
{
uint8_t v___x_1353_; 
lean_dec_ref_known(v_x_1298_, 1);
lean_dec_ref(v_localinst_1300_);
lean_dec_ref(v_x_1299_);
v___x_1353_ = 0;
return v___x_1353_;
}
}
default: 
{
lean_dec_ref(v_inst_1296_);
if (lean_obj_tag(v_x_1299_) == 7)
{
lean_object* v_container_1354_; lean_object* v_content_1355_; lean_object* v_container_1356_; lean_object* v_content_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v_container_1354_ = lean_ctor_get(v_x_1298_, 0);
lean_inc(v_container_1354_);
v_content_1355_ = lean_ctor_get(v_x_1298_, 1);
lean_inc_ref(v_content_1355_);
lean_dec_ref_known(v_x_1298_, 2);
v_container_1356_ = lean_ctor_get(v_x_1299_, 0);
lean_inc(v_container_1356_);
v_content_1357_ = lean_ctor_get(v_x_1299_, 1);
lean_inc_ref(v_content_1357_);
lean_dec_ref_known(v_x_1299_, 2);
v___x_1358_ = lean_apply_2(v_inst_1297_, v_container_1354_, v_container_1356_);
v___x_1359_ = lean_unbox(v___x_1358_);
if (v___x_1359_ == 0)
{
uint8_t v___x_1360_; 
lean_dec_ref(v_content_1357_);
lean_dec_ref(v_content_1355_);
lean_dec_ref(v_localinst_1300_);
v___x_1360_ = lean_unbox(v___x_1358_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = lean_array_get_size(v_content_1355_);
v___x_1362_ = lean_array_get_size(v_content_1357_);
v___x_1363_ = lean_nat_dec_eq(v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_dec_ref(v_content_1357_);
lean_dec_ref(v_content_1355_);
lean_dec_ref(v_localinst_1300_);
return v___x_1363_;
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = l_Array_isEqvAux___redArg(v_content_1355_, v_content_1357_, v_localinst_1300_, v___x_1361_);
lean_dec_ref(v_content_1357_);
lean_dec_ref(v_content_1355_);
return v___x_1364_;
}
}
}
else
{
uint8_t v___x_1365_; 
lean_dec_ref_known(v_x_1298_, 2);
lean_dec_ref(v_localinst_1300_);
lean_dec_ref(v_x_1299_);
lean_dec_ref(v_inst_1297_);
v___x_1365_ = 0;
return v___x_1365_;
}
}
}
v___jp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1304_ = lean_array_get_size(v_a_1302_);
v___x_1305_ = lean_array_get_size(v_b_1303_);
v___x_1306_ = lean_nat_dec_eq(v___x_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v_b_1303_);
lean_dec_ref(v_a_1302_);
lean_dec_ref(v_localinst_1300_);
return v___x_1306_;
}
else
{
uint8_t v___x_1307_; 
v___x_1307_ = l_Array_isEqvAux___redArg(v_a_1302_, v_b_1303_, v_localinst_1300_, v___x_1304_);
lean_dec_ref(v_b_1303_);
lean_dec_ref(v_a_1302_);
return v___x_1307_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqBlock_beq(lean_object* v_i_1366_, lean_object* v_b_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
uint8_t v___x_1372_; 
v___x_1372_ = l_Lean_Doc_instBEqBlock_beq___redArg(v_inst_1368_, v_inst_1369_, v_x_1370_, v_x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock_beq___boxed(lean_object* v_i_1373_, lean_object* v_b_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_x_1377_, lean_object* v_x_1378_){
_start:
{
uint8_t v_res_1379_; lean_object* v_r_1380_; 
v_res_1379_ = l_Lean_Doc_instBEqBlock_beq(v_i_1373_, v_b_1374_, v_inst_1375_, v_inst_1376_, v_x_1377_, v_x_1378_);
v_r_1380_ = lean_box(v_res_1379_);
return v_r_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock___redArg(lean_object* v_inst_1381_, lean_object* v_inst_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1383_, 0, lean_box(0));
lean_closure_set(v___x_1383_, 1, lean_box(0));
lean_closure_set(v___x_1383_, 2, v_inst_1381_);
lean_closure_set(v___x_1383_, 3, v_inst_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqBlock(lean_object* v_i_1384_, lean_object* v_b_1385_, lean_object* v_inst_1386_, lean_object* v_inst_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1388_, 0, lean_box(0));
lean_closure_set(v___x_1388_, 1, lean_box(0));
lean_closure_set(v___x_1388_, 2, v_inst_1386_);
lean_closure_set(v___x_1388_, 3, v_inst_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___redArg___boxed(lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_x_1391_, lean_object* v_x_1392_){
_start:
{
uint8_t v_res_1393_; lean_object* v_r_1394_; 
v_res_1393_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1389_, v_inst_1390_, v_x_1391_, v_x_1392_);
v_r_1394_ = lean_box(v_res_1393_);
return v_r_1394_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord___redArg(lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_){
_start:
{
lean_object* v_localinst_1399_; lean_object* v_a_1401_; lean_object* v_b_1402_; 
lean_inc_ref(v_inst_1396_);
lean_inc_ref(v_inst_1395_);
v_localinst_1399_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1399_, 0, v_inst_1395_);
lean_closure_set(v_localinst_1399_, 1, v_inst_1396_);
switch(lean_obj_tag(v_x_1397_))
{
case 0:
{
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_inst_1396_);
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v_contents_1405_; lean_object* v_contents_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v_contents_1405_ = lean_ctor_get(v_x_1397_, 0);
lean_inc_ref(v_contents_1405_);
lean_dec_ref_known(v_x_1397_, 1);
v_contents_1406_ = lean_ctor_get(v_x_1398_, 0);
lean_inc_ref(v_contents_1406_);
lean_dec_ref_known(v_x_1398_, 1);
v___x_1407_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1407_, 0, lean_box(0));
lean_closure_set(v___x_1407_, 1, v_inst_1395_);
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1407_, v_contents_1405_, v_contents_1406_, v___x_1408_);
lean_dec_ref(v_contents_1406_);
lean_dec_ref(v_contents_1405_);
return v___x_1409_;
}
else
{
uint8_t v___x_1410_; 
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_x_1398_);
lean_dec_ref(v_inst_1395_);
v___x_1410_ = 0;
return v___x_1410_;
}
}
case 1:
{
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v_inst_1395_);
switch(lean_obj_tag(v_x_1398_))
{
case 0:
{
uint8_t v___x_1411_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
v___x_1411_ = 2;
return v___x_1411_;
}
case 1:
{
lean_object* v_content_1412_; lean_object* v_content_1413_; uint8_t v___x_1414_; 
v_content_1412_ = lean_ctor_get(v_x_1397_, 0);
lean_inc_ref(v_content_1412_);
lean_dec_ref_known(v_x_1397_, 1);
v_content_1413_ = lean_ctor_get(v_x_1398_, 0);
lean_inc_ref(v_content_1413_);
lean_dec_ref_known(v_x_1398_, 1);
v___x_1414_ = lean_string_compare(v_content_1412_, v_content_1413_);
lean_dec_ref(v_content_1413_);
lean_dec_ref(v_content_1412_);
return v___x_1414_;
}
default: 
{
uint8_t v___x_1415_; 
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_x_1398_);
v___x_1415_ = 0;
return v___x_1415_;
}
}
}
case 2:
{
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v_inst_1395_);
switch(lean_obj_tag(v_x_1398_))
{
case 0:
{
uint8_t v___x_1416_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1416_ = 2;
return v___x_1416_;
}
case 1:
{
uint8_t v___x_1417_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1417_ = 2;
return v___x_1417_;
}
case 2:
{
lean_object* v_items_1418_; lean_object* v_items_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_items_1418_ = lean_ctor_get(v_x_1397_, 0);
lean_inc_ref(v_items_1418_);
lean_dec_ref_known(v_x_1397_, 1);
v_items_1419_ = lean_ctor_get(v_x_1398_, 0);
lean_inc_ref(v_items_1419_);
lean_dec_ref_known(v_x_1398_, 1);
v___x_1420_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1420_, 0, lean_box(0));
lean_closure_set(v___x_1420_, 1, v_localinst_1399_);
v___x_1421_ = lean_unsigned_to_nat(0u);
v___x_1422_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1420_, v_items_1418_, v_items_1419_, v___x_1421_);
lean_dec_ref(v_items_1419_);
lean_dec_ref(v_items_1418_);
return v___x_1422_;
}
default: 
{
uint8_t v___x_1423_; 
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_x_1398_);
v___x_1423_ = 0;
return v___x_1423_;
}
}
}
case 3:
{
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v_inst_1395_);
switch(lean_obj_tag(v_x_1398_))
{
case 0:
{
uint8_t v___x_1424_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 2);
lean_dec_ref(v_localinst_1399_);
v___x_1424_ = 2;
return v___x_1424_;
}
case 1:
{
uint8_t v___x_1425_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 2);
lean_dec_ref(v_localinst_1399_);
v___x_1425_ = 2;
return v___x_1425_;
}
case 2:
{
uint8_t v___x_1426_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 2);
lean_dec_ref(v_localinst_1399_);
v___x_1426_ = 2;
return v___x_1426_;
}
case 3:
{
lean_object* v_start_1427_; lean_object* v_items_1428_; lean_object* v_start_1429_; lean_object* v_items_1430_; uint8_t v___x_1431_; 
v_start_1427_ = lean_ctor_get(v_x_1397_, 0);
lean_inc(v_start_1427_);
v_items_1428_ = lean_ctor_get(v_x_1397_, 1);
lean_inc_ref(v_items_1428_);
lean_dec_ref_known(v_x_1397_, 2);
v_start_1429_ = lean_ctor_get(v_x_1398_, 0);
lean_inc(v_start_1429_);
v_items_1430_ = lean_ctor_get(v_x_1398_, 1);
lean_inc_ref(v_items_1430_);
lean_dec_ref_known(v_x_1398_, 2);
v___x_1431_ = lean_int_dec_lt(v_start_1427_, v_start_1429_);
if (v___x_1431_ == 0)
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_int_dec_eq(v_start_1427_, v_start_1429_);
lean_dec(v_start_1429_);
lean_dec(v_start_1427_);
if (v___x_1432_ == 0)
{
uint8_t v___x_1433_; 
lean_dec_ref(v_items_1430_);
lean_dec_ref(v_items_1428_);
lean_dec_ref(v_localinst_1399_);
v___x_1433_ = 2;
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdListItem_ord___boxed), 4, 2);
lean_closure_set(v___x_1434_, 0, lean_box(0));
lean_closure_set(v___x_1434_, 1, v_localinst_1399_);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1434_, v_items_1428_, v_items_1430_, v___x_1435_);
lean_dec_ref(v_items_1430_);
lean_dec_ref(v_items_1428_);
return v___x_1436_;
}
}
else
{
uint8_t v___x_1437_; 
lean_dec_ref(v_items_1430_);
lean_dec(v_start_1429_);
lean_dec_ref(v_items_1428_);
lean_dec(v_start_1427_);
lean_dec_ref(v_localinst_1399_);
v___x_1437_ = 0;
return v___x_1437_;
}
}
default: 
{
uint8_t v___x_1438_; 
lean_dec_ref_known(v_x_1397_, 2);
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_x_1398_);
v___x_1438_ = 0;
return v___x_1438_;
}
}
}
case 4:
{
lean_dec_ref(v_inst_1396_);
switch(lean_obj_tag(v_x_1398_))
{
case 0:
{
uint8_t v___x_1439_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_inst_1395_);
v___x_1439_ = 2;
return v___x_1439_;
}
case 1:
{
uint8_t v___x_1440_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_inst_1395_);
v___x_1440_ = 2;
return v___x_1440_;
}
case 2:
{
uint8_t v___x_1441_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_inst_1395_);
v___x_1441_ = 2;
return v___x_1441_;
}
case 3:
{
uint8_t v___x_1442_; 
lean_dec_ref_known(v_x_1398_, 2);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_inst_1395_);
v___x_1442_ = 2;
return v___x_1442_;
}
case 4:
{
lean_object* v_items_1443_; lean_object* v_items_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_items_1443_ = lean_ctor_get(v_x_1397_, 0);
lean_inc_ref(v_items_1443_);
lean_dec_ref_known(v_x_1397_, 1);
v_items_1444_ = lean_ctor_get(v_x_1398_, 0);
lean_inc_ref(v_items_1444_);
lean_dec_ref_known(v_x_1398_, 1);
v___x_1445_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1445_, 0, lean_box(0));
lean_closure_set(v___x_1445_, 1, v_inst_1395_);
v___x_1446_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdDescItem_ord___boxed), 6, 4);
lean_closure_set(v___x_1446_, 0, lean_box(0));
lean_closure_set(v___x_1446_, 1, lean_box(0));
lean_closure_set(v___x_1446_, 2, v___x_1445_);
lean_closure_set(v___x_1446_, 3, v_localinst_1399_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1446_, v_items_1443_, v_items_1444_, v___x_1447_);
lean_dec_ref(v_items_1444_);
lean_dec_ref(v_items_1443_);
return v___x_1448_;
}
default: 
{
uint8_t v___x_1449_; 
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_x_1398_);
lean_dec_ref(v_inst_1395_);
v___x_1449_ = 0;
return v___x_1449_;
}
}
}
case 5:
{
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v_inst_1395_);
switch(lean_obj_tag(v_x_1398_))
{
case 0:
{
uint8_t v___x_1450_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1450_ = 2;
return v___x_1450_;
}
case 1:
{
uint8_t v___x_1451_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1451_ = 2;
return v___x_1451_;
}
case 2:
{
uint8_t v___x_1452_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1452_ = 2;
return v___x_1452_;
}
case 3:
{
uint8_t v___x_1453_; 
lean_dec_ref_known(v_x_1398_, 2);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1453_ = 2;
return v___x_1453_;
}
case 4:
{
uint8_t v___x_1454_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1454_ = 2;
return v___x_1454_;
}
case 5:
{
lean_object* v_items_1455_; lean_object* v_items_1456_; 
v_items_1455_ = lean_ctor_get(v_x_1397_, 0);
lean_inc_ref(v_items_1455_);
lean_dec_ref_known(v_x_1397_, 1);
v_items_1456_ = lean_ctor_get(v_x_1398_, 0);
lean_inc_ref(v_items_1456_);
lean_dec_ref_known(v_x_1398_, 1);
v_a_1401_ = v_items_1455_;
v_b_1402_ = v_items_1456_;
goto v___jp_1400_;
}
default: 
{
uint8_t v___x_1457_; 
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_x_1398_);
v___x_1457_ = 0;
return v___x_1457_;
}
}
}
case 6:
{
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v_inst_1395_);
switch(lean_obj_tag(v_x_1398_))
{
case 0:
{
uint8_t v___x_1458_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1458_ = 2;
return v___x_1458_;
}
case 1:
{
uint8_t v___x_1459_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1459_ = 2;
return v___x_1459_;
}
case 2:
{
uint8_t v___x_1460_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1460_ = 2;
return v___x_1460_;
}
case 3:
{
uint8_t v___x_1461_; 
lean_dec_ref_known(v_x_1398_, 2);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1461_ = 2;
return v___x_1461_;
}
case 4:
{
uint8_t v___x_1462_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1462_ = 2;
return v___x_1462_;
}
case 5:
{
uint8_t v___x_1463_; 
lean_dec_ref_known(v_x_1398_, 1);
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
v___x_1463_ = 2;
return v___x_1463_;
}
case 6:
{
lean_object* v_content_1464_; lean_object* v_content_1465_; 
v_content_1464_ = lean_ctor_get(v_x_1397_, 0);
lean_inc_ref(v_content_1464_);
lean_dec_ref_known(v_x_1397_, 1);
v_content_1465_ = lean_ctor_get(v_x_1398_, 0);
lean_inc_ref(v_content_1465_);
lean_dec_ref_known(v_x_1398_, 1);
v_a_1401_ = v_content_1464_;
v_b_1402_ = v_content_1465_;
goto v___jp_1400_;
}
default: 
{
uint8_t v___x_1466_; 
lean_dec_ref_known(v_x_1397_, 1);
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_x_1398_);
v___x_1466_ = 0;
return v___x_1466_;
}
}
}
default: 
{
lean_dec_ref(v_inst_1395_);
if (lean_obj_tag(v_x_1398_) == 7)
{
lean_object* v_container_1467_; lean_object* v_content_1468_; lean_object* v_container_1469_; lean_object* v_content_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v_container_1467_ = lean_ctor_get(v_x_1397_, 0);
lean_inc(v_container_1467_);
v_content_1468_ = lean_ctor_get(v_x_1397_, 1);
lean_inc_ref(v_content_1468_);
lean_dec_ref_known(v_x_1397_, 2);
v_container_1469_ = lean_ctor_get(v_x_1398_, 0);
lean_inc(v_container_1469_);
v_content_1470_ = lean_ctor_get(v_x_1398_, 1);
lean_inc_ref(v_content_1470_);
lean_dec_ref_known(v_x_1398_, 2);
v___x_1471_ = lean_apply_2(v_inst_1396_, v_container_1467_, v_container_1469_);
v___x_1472_ = lean_unbox(v___x_1471_);
if (v___x_1472_ == 1)
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_localinst_1399_, v_content_1468_, v_content_1470_, v___x_1473_);
lean_dec_ref(v_content_1470_);
lean_dec_ref(v_content_1468_);
return v___x_1474_;
}
else
{
uint8_t v___x_1475_; 
lean_dec_ref(v_content_1470_);
lean_dec_ref(v_content_1468_);
lean_dec_ref(v_localinst_1399_);
v___x_1475_ = lean_unbox(v___x_1471_);
return v___x_1475_;
}
}
else
{
uint8_t v___x_1476_; 
lean_dec_ref_known(v_x_1397_, 2);
lean_dec_ref(v_localinst_1399_);
lean_dec_ref(v_x_1398_);
lean_dec_ref(v_inst_1396_);
v___x_1476_ = 2;
return v___x_1476_;
}
}
}
v___jp_1400_:
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_localinst_1399_, v_a_1401_, v_b_1402_, v___x_1403_);
lean_dec_ref(v_b_1402_);
lean_dec_ref(v_a_1401_);
return v___x_1404_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdBlock_ord(lean_object* v_i_1477_, lean_object* v_b_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_){
_start:
{
uint8_t v___x_1483_; 
v___x_1483_ = l_Lean_Doc_instOrdBlock_ord___redArg(v_inst_1479_, v_inst_1480_, v_x_1481_, v_x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock_ord___boxed(lean_object* v_i_1484_, lean_object* v_b_1485_, lean_object* v_inst_1486_, lean_object* v_inst_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_){
_start:
{
uint8_t v_res_1490_; lean_object* v_r_1491_; 
v_res_1490_ = l_Lean_Doc_instOrdBlock_ord(v_i_1484_, v_b_1485_, v_inst_1486_, v_inst_1487_, v_x_1488_, v_x_1489_);
v_r_1491_ = lean_box(v_res_1490_);
return v_r_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock___redArg(lean_object* v_inst_1492_, lean_object* v_inst_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1494_, 0, lean_box(0));
lean_closure_set(v___x_1494_, 1, lean_box(0));
lean_closure_set(v___x_1494_, 2, v_inst_1492_);
lean_closure_set(v___x_1494_, 3, v_inst_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdBlock(lean_object* v_i_1495_, lean_object* v_b_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1499_, 0, lean_box(0));
lean_closure_set(v___x_1499_, 1, lean_box(0));
lean_closure_set(v___x_1499_, 2, v_inst_1497_);
lean_closure_set(v___x_1499_, 3, v_inst_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = lean_nat_to_int(v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg___boxed(lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_x_1552_, lean_object* v_prec_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1550_, v_inst_1551_, v_x_1552_, v_prec_1553_);
lean_dec(v_prec_1553_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___redArg(lean_object* v_inst_1555_, lean_object* v_inst_1556_, lean_object* v_x_1557_, lean_object* v_prec_1558_){
_start:
{
lean_object* v_localinst_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_inc_ref(v_inst_1556_);
lean_inc_ref(v_inst_1555_);
v_localinst_1559_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___redArg___boxed), 4, 2);
lean_closure_set(v_localinst_1559_, 0, v_inst_1555_);
lean_closure_set(v_localinst_1559_, 1, v_inst_1556_);
v___x_1560_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1560_, 0, lean_box(0));
lean_closure_set(v___x_1560_, 1, v_inst_1555_);
lean_inc_ref(v_localinst_1559_);
v___x_1561_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprListItem_repr___boxed), 4, 2);
lean_closure_set(v___x_1561_, 0, lean_box(0));
lean_closure_set(v___x_1561_, 1, v_localinst_1559_);
switch(lean_obj_tag(v_x_1557_))
{
case 0:
{
lean_object* v_contents_1562_; lean_object* v___y_1564_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
lean_dec_ref(v___x_1561_);
lean_dec_ref(v_localinst_1559_);
lean_dec_ref(v_inst_1556_);
v_contents_1562_ = lean_ctor_get(v_x_1557_, 0);
lean_inc_ref(v_contents_1562_);
lean_dec_ref_known(v_x_1557_, 1);
v___x_1572_ = lean_unsigned_to_nat(1024u);
v___x_1573_ = lean_nat_dec_le(v___x_1572_, v_prec_1558_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1564_ = v___x_1574_;
goto v___jp_1563_;
}
else
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1564_ = v___x_1575_;
goto v___jp_1563_;
}
v___jp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1565_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__2));
v___x_1566_ = l_Array_repr___redArg(v___x_1560_, v_contents_1562_);
v___x_1567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
lean_inc(v___y_1564_);
v___x_1568_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___y_1564_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = 0;
v___x_1570_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*1, v___x_1569_);
v___x_1571_ = l_Repr_addAppParen(v___x_1570_, v_prec_1558_);
return v___x_1571_;
}
}
case 1:
{
lean_object* v_content_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v___x_1561_);
lean_dec_ref(v___x_1560_);
lean_dec_ref(v_localinst_1559_);
lean_dec_ref(v_inst_1556_);
v_content_1576_ = lean_ctor_get(v_x_1557_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1578_ = v_x_1557_;
v_isShared_1579_ = v_isSharedCheck_1596_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_content_1576_);
lean_dec(v_x_1557_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1596_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___y_1581_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1592_ = lean_unsigned_to_nat(1024u);
v___x_1593_ = lean_nat_dec_le(v___x_1592_, v_prec_1558_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1581_ = v___x_1594_;
goto v___jp_1580_;
}
else
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1581_ = v___x_1595_;
goto v___jp_1580_;
}
v___jp_1580_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1582_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__5));
v___x_1583_ = l_String_quote(v_content_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 3);
lean_ctor_set(v___x_1578_, 0, v___x_1583_);
v___x_1585_ = v___x_1578_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1582_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
lean_inc(v___y_1581_);
v___x_1587_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___y_1581_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = 0;
v___x_1589_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*1, v___x_1588_);
v___x_1590_ = l_Repr_addAppParen(v___x_1589_, v_prec_1558_);
return v___x_1590_;
}
}
}
}
case 2:
{
lean_object* v_items_1597_; lean_object* v___y_1599_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
lean_dec_ref(v___x_1560_);
lean_dec_ref(v_localinst_1559_);
lean_dec_ref(v_inst_1556_);
v_items_1597_ = lean_ctor_get(v_x_1557_, 0);
lean_inc_ref(v_items_1597_);
lean_dec_ref_known(v_x_1557_, 1);
v___x_1607_ = lean_unsigned_to_nat(1024u);
v___x_1608_ = lean_nat_dec_le(v___x_1607_, v_prec_1558_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1599_ = v___x_1609_;
goto v___jp_1598_;
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1599_ = v___x_1610_;
goto v___jp_1598_;
}
v___jp_1598_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1600_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__8));
v___x_1601_ = l_Array_repr___redArg(v___x_1561_, v_items_1597_);
v___x_1602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1600_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
lean_inc(v___y_1599_);
v___x_1603_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___y_1599_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = 0;
v___x_1605_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1605_, 0, v___x_1603_);
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*1, v___x_1604_);
v___x_1606_ = l_Repr_addAppParen(v___x_1605_, v_prec_1558_);
return v___x_1606_;
}
}
case 3:
{
lean_object* v_start_1611_; lean_object* v_items_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___x_1560_);
lean_dec_ref(v_localinst_1559_);
lean_dec_ref(v_inst_1556_);
v_start_1611_ = lean_ctor_get(v_x_1557_, 0);
v_items_1612_ = lean_ctor_get(v_x_1557_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1614_ = v_x_1557_;
v_isShared_1615_ = v_isSharedCheck_1647_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_items_1612_);
lean_inc(v_start_1611_);
lean_dec(v_x_1557_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1647_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1632_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = lean_unsigned_to_nat(1024u);
v___x_1644_ = lean_nat_dec_le(v___x_1643_, v_prec_1558_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1632_ = v___x_1645_;
goto v___jp_1631_;
}
else
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1632_ = v___x_1646_;
goto v___jp_1631_;
}
v___jp_1616_:
{
lean_object* v___x_1622_; 
lean_inc(v___y_1618_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set_tag(v___x_1614_, 5);
lean_ctor_set(v___x_1614_, 1, v___y_1620_);
lean_ctor_set(v___x_1614_, 0, v___y_1618_);
v___x_1622_ = v___x_1614_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___y_1618_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v___y_1620_);
v___x_1622_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_inc(v___y_1619_);
v___x_1623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v___y_1619_);
v___x_1624_ = l_Array_repr___redArg(v___x_1561_, v_items_1612_);
v___x_1625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
lean_inc(v___y_1617_);
v___x_1626_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___y_1617_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = 0;
v___x_1628_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set_uint8(v___x_1628_, sizeof(void*)*1, v___x_1627_);
v___x_1629_ = l_Repr_addAppParen(v___x_1628_, v_prec_1558_);
return v___x_1629_;
}
}
v___jp_1631_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1633_ = lean_box(1);
v___x_1634_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__11));
v___x_1635_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___redArg___closed__12, &l_Lean_Doc_instReprBlock_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___redArg___closed__12);
v___x_1636_ = lean_int_dec_lt(v_start_1611_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = l_Int_repr(v_start_1611_);
lean_dec(v_start_1611_);
v___x_1638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
v___y_1617_ = v___y_1632_;
v___y_1618_ = v___x_1634_;
v___y_1619_ = v___x_1633_;
v___y_1620_ = v___x_1638_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1639_ = lean_unsigned_to_nat(1024u);
v___x_1640_ = l_Int_repr(v_start_1611_);
lean_dec(v_start_1611_);
v___x_1641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
v___x_1642_ = l_Repr_addAppParen(v___x_1641_, v___x_1639_);
v___y_1617_ = v___y_1632_;
v___y_1618_ = v___x_1634_;
v___y_1619_ = v___x_1633_;
v___y_1620_ = v___x_1642_;
goto v___jp_1616_;
}
}
}
}
case 4:
{
lean_object* v_items_1648_; lean_object* v___x_1649_; lean_object* v___y_1651_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
lean_dec_ref(v___x_1561_);
lean_dec_ref(v_inst_1556_);
v_items_1648_ = lean_ctor_get(v_x_1557_, 0);
lean_inc_ref(v_items_1648_);
lean_dec_ref_known(v_x_1557_, 1);
v___x_1649_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprDescItem_repr___boxed), 6, 4);
lean_closure_set(v___x_1649_, 0, lean_box(0));
lean_closure_set(v___x_1649_, 1, lean_box(0));
lean_closure_set(v___x_1649_, 2, v___x_1560_);
lean_closure_set(v___x_1649_, 3, v_localinst_1559_);
v___x_1659_ = lean_unsigned_to_nat(1024u);
v___x_1660_ = lean_nat_dec_le(v___x_1659_, v_prec_1558_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1651_ = v___x_1661_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1651_ = v___x_1662_;
goto v___jp_1650_;
}
v___jp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1652_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__15));
v___x_1653_ = l_Array_repr___redArg(v___x_1649_, v_items_1648_);
v___x_1654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
lean_inc(v___y_1651_);
v___x_1655_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___y_1651_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = 0;
v___x_1657_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set_uint8(v___x_1657_, sizeof(void*)*1, v___x_1656_);
v___x_1658_ = l_Repr_addAppParen(v___x_1657_, v_prec_1558_);
return v___x_1658_;
}
}
case 5:
{
lean_object* v_items_1663_; lean_object* v___y_1665_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
lean_dec_ref(v___x_1561_);
lean_dec_ref(v___x_1560_);
lean_dec_ref(v_inst_1556_);
v_items_1663_ = lean_ctor_get(v_x_1557_, 0);
lean_inc_ref(v_items_1663_);
lean_dec_ref_known(v_x_1557_, 1);
v___x_1673_ = lean_unsigned_to_nat(1024u);
v___x_1674_ = lean_nat_dec_le(v___x_1673_, v_prec_1558_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1665_ = v___x_1675_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1665_ = v___x_1676_;
goto v___jp_1664_;
}
v___jp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1666_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__18));
v___x_1667_ = l_Array_repr___redArg(v_localinst_1559_, v_items_1663_);
v___x_1668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
lean_inc(v___y_1665_);
v___x_1669_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___y_1665_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = 0;
v___x_1671_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*1, v___x_1670_);
v___x_1672_ = l_Repr_addAppParen(v___x_1671_, v_prec_1558_);
return v___x_1672_;
}
}
case 6:
{
lean_object* v_content_1677_; lean_object* v___y_1679_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
lean_dec_ref(v___x_1561_);
lean_dec_ref(v___x_1560_);
lean_dec_ref(v_inst_1556_);
v_content_1677_ = lean_ctor_get(v_x_1557_, 0);
lean_inc_ref(v_content_1677_);
lean_dec_ref_known(v_x_1557_, 1);
v___x_1687_ = lean_unsigned_to_nat(1024u);
v___x_1688_ = lean_nat_dec_le(v___x_1687_, v_prec_1558_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1679_ = v___x_1689_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1679_ = v___x_1690_;
goto v___jp_1678_;
}
v___jp_1678_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1680_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__21));
v___x_1681_ = l_Array_repr___redArg(v_localinst_1559_, v_content_1677_);
v___x_1682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
lean_inc(v___y_1679_);
v___x_1683_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___y_1679_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = 0;
v___x_1685_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set_uint8(v___x_1685_, sizeof(void*)*1, v___x_1684_);
v___x_1686_ = l_Repr_addAppParen(v___x_1685_, v_prec_1558_);
return v___x_1686_;
}
}
default: 
{
lean_object* v_container_1691_; lean_object* v_content_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1716_; 
lean_dec_ref(v___x_1561_);
lean_dec_ref(v___x_1560_);
v_container_1691_ = lean_ctor_get(v_x_1557_, 0);
v_content_1692_ = lean_ctor_get(v_x_1557_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1694_ = v_x_1557_;
v_isShared_1695_ = v_isSharedCheck_1716_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_content_1692_);
lean_inc(v_container_1691_);
lean_dec(v_x_1557_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1716_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___y_1697_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = lean_unsigned_to_nat(1024u);
v___x_1713_ = lean_nat_dec_le(v___x_1712_, v_prec_1558_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__4, &l_Lean_Doc_instReprMathMode_repr___closed__4_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__4);
v___y_1697_ = v___x_1714_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_obj_once(&l_Lean_Doc_instReprMathMode_repr___closed__5, &l_Lean_Doc_instReprMathMode_repr___closed__5_once, _init_l_Lean_Doc_instReprMathMode_repr___closed__5);
v___y_1697_ = v___x_1715_;
goto v___jp_1696_;
}
v___jp_1696_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1698_ = lean_box(1);
v___x_1699_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___redArg___closed__24));
v___x_1700_ = lean_unsigned_to_nat(1024u);
v___x_1701_ = lean_apply_2(v_inst_1556_, v_container_1691_, v___x_1700_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set_tag(v___x_1694_, 5);
lean_ctor_set(v___x_1694_, 1, v___x_1701_);
lean_ctor_set(v___x_1694_, 0, v___x_1699_);
v___x_1703_ = v___x_1694_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v___x_1698_);
v___x_1705_ = l_Array_repr___redArg(v_localinst_1559_, v_content_1692_);
v___x_1706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
lean_inc(v___y_1697_);
v___x_1707_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___y_1697_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = 0;
v___x_1709_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*1, v___x_1708_);
v___x_1710_ = l_Repr_addAppParen(v___x_1709_, v_prec_1558_);
return v___x_1710_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr(lean_object* v_i_1717_, lean_object* v_b_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_x_1721_, lean_object* v_prec_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Doc_instReprBlock_repr___redArg(v_inst_1719_, v_inst_1720_, v_x_1721_, v_prec_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___boxed(lean_object* v_i_1724_, lean_object* v_b_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_x_1728_, lean_object* v_prec_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Doc_instReprBlock_repr(v_i_1724_, v_b_1725_, v_inst_1726_, v_inst_1727_, v_x_1728_, v_prec_1729_);
lean_dec(v_prec_1729_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock___redArg(lean_object* v_inst_1731_, lean_object* v_inst_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1733_, 0, lean_box(0));
lean_closure_set(v___x_1733_, 1, lean_box(0));
lean_closure_set(v___x_1733_, 2, v_inst_1731_);
lean_closure_set(v___x_1733_, 3, v_inst_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock(lean_object* v_i_1734_, lean_object* v_b_1735_, lean_object* v_inst_1736_, lean_object* v_inst_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_1738_, 0, lean_box(0));
lean_closure_set(v___x_1738_, 1, lean_box(0));
lean_closure_set(v___x_1738_, 2, v_inst_1736_);
lean_closure_set(v___x_1738_, 3, v_inst_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg(){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlock_default___redArg___closed__1));
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default___redArg___boxed(lean_object* v___dummy_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
return v_res_1746_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedBlock_default___closed__0(void){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Doc_instInhabitedBlock_default___redArg();
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock_default(lean_object* v_i_1748_, lean_object* v_b_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg(){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock___redArg___boxed(lean_object* v___dummy_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_Doc_instInhabitedBlock___redArg();
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedBlock(lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_obj_once(&l_Lean_Doc_instInhabitedBlock_default___closed__0, &l_Lean_Doc_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Doc_instInhabitedBlock_default___closed__0);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg(){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = ((lean_object*)(l_Lean_Doc_Block_empty___redArg___closed__1));
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty___redArg___boxed(lean_object* v___dummy_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Doc_Block_empty___redArg();
return v_res_1765_;
}
}
static lean_object* _init_l_Lean_Doc_Block_empty___closed__0(void){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Doc_Block_empty___redArg();
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_empty(lean_object* v_i_1767_, lean_object* v_b_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_obj_once(&l_Lean_Doc_Block_empty___closed__0, &l_Lean_Doc_Block_empty___closed__0_once, _init_l_Lean_Doc_Block_empty___closed__0);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg(lean_object* v_x_1770_){
_start:
{
lean_inc_ref(v_x_1770_);
return v_x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___redArg___boxed(lean_object* v_x_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Doc_Block_cast___redArg(v_x_1771_);
lean_dec_ref(v_x_1771_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast(lean_object* v_i_1773_, lean_object* v_i_x27_1774_, lean_object* v_b_1775_, lean_object* v_b_x27_1776_, lean_object* v_inlines__eq_1777_, lean_object* v_blocks__eq_1778_, lean_object* v_x_1779_){
_start:
{
lean_inc_ref(v_x_1779_);
return v_x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_cast___boxed(lean_object* v_i_1780_, lean_object* v_i_x27_1781_, lean_object* v_b_1782_, lean_object* v_b_x27_1783_, lean_object* v_inlines__eq_1784_, lean_object* v_blocks__eq_1785_, lean_object* v_x_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Doc_Block_cast(v_i_1780_, v_i_x27_1781_, v_b_1782_, v_b_x27_1783_, v_inlines__eq_1784_, v_blocks__eq_1785_, v_x_1786_);
lean_dec_ref(v_x_1786_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___redArg___boxed(lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_){
_start:
{
uint8_t v_res_1793_; lean_object* v_r_1794_; 
v_res_1793_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1788_, v_inst_1789_, v_inst_1790_, v_x_1791_, v_x_1792_);
v_r_1794_ = lean_box(v_res_1793_);
return v_r_1794_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq___redArg(lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_x_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v_title_1800_; lean_object* v_titleString_1801_; lean_object* v_metadata_1802_; lean_object* v_content_1803_; lean_object* v_subParts_1804_; lean_object* v_title_1805_; lean_object* v_titleString_1806_; lean_object* v_metadata_1807_; lean_object* v_content_1808_; lean_object* v_subParts_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_title_1800_ = lean_ctor_get(v_x_1798_, 0);
lean_inc_ref(v_title_1800_);
v_titleString_1801_ = lean_ctor_get(v_x_1798_, 1);
lean_inc_ref(v_titleString_1801_);
v_metadata_1802_ = lean_ctor_get(v_x_1798_, 2);
lean_inc(v_metadata_1802_);
v_content_1803_ = lean_ctor_get(v_x_1798_, 3);
lean_inc_ref(v_content_1803_);
v_subParts_1804_ = lean_ctor_get(v_x_1798_, 4);
lean_inc_ref(v_subParts_1804_);
lean_dec_ref(v_x_1798_);
v_title_1805_ = lean_ctor_get(v_x_1799_, 0);
lean_inc_ref(v_title_1805_);
v_titleString_1806_ = lean_ctor_get(v_x_1799_, 1);
lean_inc_ref(v_titleString_1806_);
v_metadata_1807_ = lean_ctor_get(v_x_1799_, 2);
lean_inc(v_metadata_1807_);
v_content_1808_ = lean_ctor_get(v_x_1799_, 3);
lean_inc_ref(v_content_1808_);
v_subParts_1809_ = lean_ctor_get(v_x_1799_, 4);
lean_inc_ref(v_subParts_1809_);
lean_dec_ref(v_x_1799_);
v___x_1810_ = lean_array_get_size(v_title_1800_);
v___x_1811_ = lean_array_get_size(v_title_1805_);
v___x_1812_ = lean_nat_dec_eq(v___x_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_dec_ref(v_subParts_1809_);
lean_dec_ref(v_content_1808_);
lean_dec(v_metadata_1807_);
lean_dec_ref(v_titleString_1806_);
lean_dec_ref(v_title_1805_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_content_1803_);
lean_dec(v_metadata_1802_);
lean_dec_ref(v_titleString_1801_);
lean_dec_ref(v_title_1800_);
lean_dec_ref(v_inst_1797_);
lean_dec_ref(v_inst_1796_);
lean_dec_ref(v_inst_1795_);
return v___x_1812_;
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
lean_inc_ref(v_inst_1797_);
lean_inc_ref(v_inst_1796_);
lean_inc_ref_n(v_inst_1795_, 2);
v___x_1813_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___redArg___boxed), 5, 3);
lean_closure_set(v___x_1813_, 0, v_inst_1795_);
lean_closure_set(v___x_1813_, 1, v_inst_1796_);
lean_closure_set(v___x_1813_, 2, v_inst_1797_);
v___x_1814_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqInline_beq___boxed), 4, 2);
lean_closure_set(v___x_1814_, 0, lean_box(0));
lean_closure_set(v___x_1814_, 1, v_inst_1795_);
v___x_1815_ = l_Array_isEqvAux___redArg(v_title_1800_, v_title_1805_, v___x_1814_, v___x_1810_);
lean_dec_ref(v_title_1805_);
lean_dec_ref(v_title_1800_);
if (v___x_1815_ == 0)
{
lean_dec_ref(v___x_1813_);
lean_dec_ref(v_subParts_1809_);
lean_dec_ref(v_content_1808_);
lean_dec(v_metadata_1807_);
lean_dec_ref(v_titleString_1806_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_content_1803_);
lean_dec(v_metadata_1802_);
lean_dec_ref(v_titleString_1801_);
lean_dec_ref(v_inst_1797_);
lean_dec_ref(v_inst_1796_);
lean_dec_ref(v_inst_1795_);
return v___x_1815_;
}
else
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_string_dec_eq(v_titleString_1801_, v_titleString_1806_);
lean_dec_ref(v_titleString_1806_);
lean_dec_ref(v_titleString_1801_);
if (v___x_1816_ == 0)
{
lean_dec_ref(v___x_1813_);
lean_dec_ref(v_subParts_1809_);
lean_dec_ref(v_content_1808_);
lean_dec(v_metadata_1807_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_content_1803_);
lean_dec(v_metadata_1802_);
lean_dec_ref(v_inst_1797_);
lean_dec_ref(v_inst_1796_);
lean_dec_ref(v_inst_1795_);
return v___x_1816_;
}
else
{
uint8_t v___x_1817_; 
v___x_1817_ = l_instBEqOption_beq___redArg(v_inst_1797_, v_metadata_1802_, v_metadata_1807_);
if (v___x_1817_ == 0)
{
lean_dec_ref(v___x_1813_);
lean_dec_ref(v_subParts_1809_);
lean_dec_ref(v_content_1808_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_content_1803_);
lean_dec_ref(v_inst_1796_);
lean_dec_ref(v_inst_1795_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = lean_array_get_size(v_content_1803_);
v___x_1819_ = lean_array_get_size(v_content_1808_);
v___x_1820_ = lean_nat_dec_eq(v___x_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_dec_ref(v___x_1813_);
lean_dec_ref(v_subParts_1809_);
lean_dec_ref(v_content_1808_);
lean_dec_ref(v_subParts_1804_);
lean_dec_ref(v_content_1803_);
lean_dec_ref(v_inst_1796_);
lean_dec_ref(v_inst_1795_);
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqBlock_beq___boxed), 6, 4);
lean_closure_set(v___x_1821_, 0, lean_box(0));
lean_closure_set(v___x_1821_, 1, lean_box(0));
lean_closure_set(v___x_1821_, 2, v_inst_1795_);
lean_closure_set(v___x_1821_, 3, v_inst_1796_);
v___x_1822_ = l_Array_isEqvAux___redArg(v_content_1803_, v_content_1808_, v___x_1821_, v___x_1818_);
lean_dec_ref(v_content_1808_);
lean_dec_ref(v_content_1803_);
if (v___x_1822_ == 0)
{
lean_dec_ref(v___x_1813_);
lean_dec_ref(v_subParts_1809_);
lean_dec_ref(v_subParts_1804_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = lean_array_get_size(v_subParts_1804_);
v___x_1824_ = lean_array_get_size(v_subParts_1809_);
v___x_1825_ = lean_nat_dec_eq(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_dec_ref(v___x_1813_);
lean_dec_ref(v_subParts_1809_);
lean_dec_ref(v_subParts_1804_);
return v___x_1825_;
}
else
{
uint8_t v___x_1826_; 
v___x_1826_ = l_Array_isEqvAux___redArg(v_subParts_1804_, v_subParts_1809_, v___x_1813_, v___x_1823_);
lean_dec_ref(v_subParts_1809_);
lean_dec_ref(v_subParts_1804_);
return v___x_1826_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPart_beq(lean_object* v_i_1827_, lean_object* v_b_1828_, lean_object* v_p_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_){
_start:
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Doc_instBEqPart_beq___redArg(v_inst_1830_, v_inst_1831_, v_inst_1832_, v_x_1833_, v_x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart_beq___boxed(lean_object* v_i_1836_, lean_object* v_b_1837_, lean_object* v_p_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_){
_start:
{
uint8_t v_res_1844_; lean_object* v_r_1845_; 
v_res_1844_ = l_Lean_Doc_instBEqPart_beq(v_i_1836_, v_b_1837_, v_p_1838_, v_inst_1839_, v_inst_1840_, v_inst_1841_, v_x_1842_, v_x_1843_);
v_r_1845_ = lean_box(v_res_1844_);
return v_r_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart___redArg(lean_object* v_inst_1846_, lean_object* v_inst_1847_, lean_object* v_inst_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1849_, 0, lean_box(0));
lean_closure_set(v___x_1849_, 1, lean_box(0));
lean_closure_set(v___x_1849_, 2, lean_box(0));
lean_closure_set(v___x_1849_, 3, v_inst_1846_);
lean_closure_set(v___x_1849_, 4, v_inst_1847_);
lean_closure_set(v___x_1849_, 5, v_inst_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPart(lean_object* v_i_1850_, lean_object* v_b_1851_, lean_object* v_p_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_alloc_closure((void*)(l_Lean_Doc_instBEqPart_beq___boxed), 8, 6);
lean_closure_set(v___x_1856_, 0, lean_box(0));
lean_closure_set(v___x_1856_, 1, lean_box(0));
lean_closure_set(v___x_1856_, 2, lean_box(0));
lean_closure_set(v___x_1856_, 3, v_inst_1853_);
lean_closure_set(v___x_1856_, 4, v_inst_1854_);
lean_closure_set(v___x_1856_, 5, v_inst_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___redArg___boxed(lean_object* v_inst_1857_, lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_){
_start:
{
uint8_t v_res_1862_; lean_object* v_r_1863_; 
v_res_1862_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1857_, v_inst_1858_, v_inst_1859_, v_x_1860_, v_x_1861_);
v_r_1863_ = lean_box(v_res_1862_);
return v_r_1863_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord___redArg(lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v_title_1869_; lean_object* v_titleString_1870_; lean_object* v_metadata_1871_; lean_object* v_content_1872_; lean_object* v_subParts_1873_; lean_object* v_title_1874_; lean_object* v_titleString_1875_; lean_object* v_metadata_1876_; lean_object* v_content_1877_; lean_object* v_subParts_1878_; lean_object* v___x_1879_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_title_1869_ = lean_ctor_get(v_x_1867_, 0);
lean_inc_ref(v_title_1869_);
v_titleString_1870_ = lean_ctor_get(v_x_1867_, 1);
lean_inc_ref(v_titleString_1870_);
v_metadata_1871_ = lean_ctor_get(v_x_1867_, 2);
lean_inc(v_metadata_1871_);
v_content_1872_ = lean_ctor_get(v_x_1867_, 3);
lean_inc_ref(v_content_1872_);
v_subParts_1873_ = lean_ctor_get(v_x_1867_, 4);
lean_inc_ref(v_subParts_1873_);
lean_dec_ref(v_x_1867_);
v_title_1874_ = lean_ctor_get(v_x_1868_, 0);
lean_inc_ref(v_title_1874_);
v_titleString_1875_ = lean_ctor_get(v_x_1868_, 1);
lean_inc_ref(v_titleString_1875_);
v_metadata_1876_ = lean_ctor_get(v_x_1868_, 2);
lean_inc(v_metadata_1876_);
v_content_1877_ = lean_ctor_get(v_x_1868_, 3);
lean_inc_ref(v_content_1877_);
v_subParts_1878_ = lean_ctor_get(v_x_1868_, 4);
lean_inc_ref(v_subParts_1878_);
lean_dec_ref(v_x_1868_);
lean_inc_ref(v_inst_1866_);
lean_inc_ref(v_inst_1865_);
lean_inc_ref_n(v_inst_1864_, 2);
v___x_1879_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___redArg___boxed), 5, 3);
lean_closure_set(v___x_1879_, 0, v_inst_1864_);
lean_closure_set(v___x_1879_, 1, v_inst_1865_);
lean_closure_set(v___x_1879_, 2, v_inst_1866_);
v___x_1885_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdInline_ord___boxed), 4, 2);
lean_closure_set(v___x_1885_, 0, lean_box(0));
lean_closure_set(v___x_1885_, 1, v_inst_1864_);
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1885_, v_title_1869_, v_title_1874_, v___x_1886_);
lean_dec_ref(v_title_1874_);
lean_dec_ref(v_title_1869_);
if (v___x_1887_ == 1)
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_string_compare(v_titleString_1870_, v_titleString_1875_);
lean_dec_ref(v_titleString_1875_);
lean_dec_ref(v_titleString_1870_);
if (v___x_1888_ == 1)
{
if (lean_obj_tag(v_metadata_1871_) == 0)
{
lean_dec_ref(v_inst_1866_);
if (lean_obj_tag(v_metadata_1876_) == 0)
{
goto v___jp_1880_;
}
else
{
uint8_t v___x_1889_; 
lean_dec_ref_known(v_metadata_1876_, 1);
lean_dec_ref(v___x_1879_);
lean_dec_ref(v_subParts_1878_);
lean_dec_ref(v_content_1877_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec_ref(v_inst_1865_);
lean_dec_ref(v_inst_1864_);
v___x_1889_ = 0;
return v___x_1889_;
}
}
else
{
if (lean_obj_tag(v_metadata_1876_) == 0)
{
uint8_t v___x_1890_; 
lean_dec_ref_known(v_metadata_1871_, 1);
lean_dec_ref(v___x_1879_);
lean_dec_ref(v_subParts_1878_);
lean_dec_ref(v_content_1877_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec_ref(v_inst_1866_);
lean_dec_ref(v_inst_1865_);
lean_dec_ref(v_inst_1864_);
v___x_1890_ = 2;
return v___x_1890_;
}
else
{
lean_object* v_val_1891_; lean_object* v_val_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_val_1891_ = lean_ctor_get(v_metadata_1871_, 0);
lean_inc(v_val_1891_);
lean_dec_ref_known(v_metadata_1871_, 1);
v_val_1892_ = lean_ctor_get(v_metadata_1876_, 0);
lean_inc(v_val_1892_);
lean_dec_ref_known(v_metadata_1876_, 1);
v___x_1893_ = lean_apply_2(v_inst_1866_, v_val_1891_, v_val_1892_);
v___x_1894_ = lean_unbox(v___x_1893_);
if (v___x_1894_ == 1)
{
goto v___jp_1880_;
}
else
{
uint8_t v___x_1895_; 
lean_dec_ref(v___x_1879_);
lean_dec_ref(v_subParts_1878_);
lean_dec_ref(v_content_1877_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec_ref(v_inst_1865_);
lean_dec_ref(v_inst_1864_);
v___x_1895_ = lean_unbox(v___x_1893_);
return v___x_1895_;
}
}
}
}
else
{
lean_dec_ref(v___x_1879_);
lean_dec_ref(v_subParts_1878_);
lean_dec_ref(v_content_1877_);
lean_dec(v_metadata_1876_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec(v_metadata_1871_);
lean_dec_ref(v_inst_1866_);
lean_dec_ref(v_inst_1865_);
lean_dec_ref(v_inst_1864_);
return v___x_1888_;
}
}
else
{
lean_dec_ref(v___x_1879_);
lean_dec_ref(v_subParts_1878_);
lean_dec_ref(v_content_1877_);
lean_dec(v_metadata_1876_);
lean_dec_ref(v_titleString_1875_);
lean_dec_ref(v_subParts_1873_);
lean_dec_ref(v_content_1872_);
lean_dec(v_metadata_1871_);
lean_dec_ref(v_titleString_1870_);
lean_dec_ref(v_inst_1866_);
lean_dec_ref(v_inst_1865_);
lean_dec_ref(v_inst_1864_);
return v___x_1887_;
}
v___jp_1880_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1881_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdBlock_ord___boxed), 6, 4);
lean_closure_set(v___x_1881_, 0, lean_box(0));
lean_closure_set(v___x_1881_, 1, lean_box(0));
lean_closure_set(v___x_1881_, 2, v_inst_1864_);
lean_closure_set(v___x_1881_, 3, v_inst_1865_);
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1881_, v_content_1872_, v_content_1877_, v___x_1882_);
lean_dec_ref(v_content_1877_);
lean_dec_ref(v_content_1872_);
if (v___x_1883_ == 1)
{
uint8_t v___x_1884_; 
v___x_1884_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v___x_1879_, v_subParts_1873_, v_subParts_1878_, v___x_1882_);
lean_dec_ref(v_subParts_1878_);
lean_dec_ref(v_subParts_1873_);
return v___x_1884_;
}
else
{
lean_dec_ref(v___x_1879_);
lean_dec_ref(v_subParts_1878_);
lean_dec_ref(v_subParts_1873_);
return v___x_1883_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instOrdPart_ord(lean_object* v_i_1896_, lean_object* v_b_1897_, lean_object* v_p_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_inst_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_){
_start:
{
uint8_t v___x_1904_; 
v___x_1904_ = l_Lean_Doc_instOrdPart_ord___redArg(v_inst_1899_, v_inst_1900_, v_inst_1901_, v_x_1902_, v_x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart_ord___boxed(lean_object* v_i_1905_, lean_object* v_b_1906_, lean_object* v_p_1907_, lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_){
_start:
{
uint8_t v_res_1913_; lean_object* v_r_1914_; 
v_res_1913_ = l_Lean_Doc_instOrdPart_ord(v_i_1905_, v_b_1906_, v_p_1907_, v_inst_1908_, v_inst_1909_, v_inst_1910_, v_x_1911_, v_x_1912_);
v_r_1914_ = lean_box(v_res_1913_);
return v_r_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart___redArg(lean_object* v_inst_1915_, lean_object* v_inst_1916_, lean_object* v_inst_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1918_, 0, lean_box(0));
lean_closure_set(v___x_1918_, 1, lean_box(0));
lean_closure_set(v___x_1918_, 2, lean_box(0));
lean_closure_set(v___x_1918_, 3, v_inst_1915_);
lean_closure_set(v___x_1918_, 4, v_inst_1916_);
lean_closure_set(v___x_1918_, 5, v_inst_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instOrdPart(lean_object* v_i_1919_, lean_object* v_b_1920_, lean_object* v_p_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_alloc_closure((void*)(l_Lean_Doc_instOrdPart_ord___boxed), 8, 6);
lean_closure_set(v___x_1925_, 0, lean_box(0));
lean_closure_set(v___x_1925_, 1, lean_box(0));
lean_closure_set(v___x_1925_, 2, lean_box(0));
lean_closure_set(v___x_1925_, 3, v_inst_1922_);
lean_closure_set(v___x_1925_, 4, v_inst_1923_);
lean_closure_set(v___x_1925_, 5, v_inst_1924_);
return v___x_1925_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_unsigned_to_nat(9u);
v___x_1936_ = lean_nat_to_int(v___x_1935_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_unsigned_to_nat(15u);
v___x_1941_ = lean_nat_to_int(v___x_1940_);
return v___x_1941_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_unsigned_to_nat(11u);
v___x_1949_ = lean_nat_to_int(v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg___boxed(lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_x_1956_, lean_object* v_prec_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_1953_, v_inst_1954_, v_inst_1955_, v_x_1956_, v_prec_1957_);
lean_dec(v_prec_1957_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___redArg(lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_x_1962_, lean_object* v_prec_1963_){
_start:
{
lean_object* v_title_1964_; lean_object* v_titleString_1965_; lean_object* v_metadata_1966_; lean_object* v_content_1967_; lean_object* v_subParts_1968_; lean_object* v_localinst_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_title_1964_ = lean_ctor_get(v_x_1962_, 0);
lean_inc_ref(v_title_1964_);
v_titleString_1965_ = lean_ctor_get(v_x_1962_, 1);
lean_inc_ref(v_titleString_1965_);
v_metadata_1966_ = lean_ctor_get(v_x_1962_, 2);
lean_inc(v_metadata_1966_);
v_content_1967_ = lean_ctor_get(v_x_1962_, 3);
lean_inc_ref(v_content_1967_);
v_subParts_1968_ = lean_ctor_get(v_x_1962_, 4);
lean_inc_ref(v_subParts_1968_);
lean_dec_ref(v_x_1962_);
lean_inc_ref(v_inst_1961_);
lean_inc_ref(v_inst_1960_);
lean_inc_ref_n(v_inst_1959_, 2);
v_localinst_1969_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___redArg___boxed), 5, 3);
lean_closure_set(v_localinst_1969_, 0, v_inst_1959_);
lean_closure_set(v_localinst_1969_, 1, v_inst_1960_);
lean_closure_set(v_localinst_1969_, 2, v_inst_1961_);
v___x_1970_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__5));
v___x_1971_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__3));
v___x_1972_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__4);
v___x_1973_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprInline_repr___boxed), 4, 2);
lean_closure_set(v___x_1973_, 0, lean_box(0));
lean_closure_set(v___x_1973_, 1, v_inst_1959_);
v___x_1974_ = l_Array_repr___redArg(v___x_1973_, v_title_1964_);
v___x_1975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = 0;
v___x_1977_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*1, v___x_1976_);
v___x_1978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1971_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___redArg___closed__6));
v___x_1980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1978_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = lean_box(1);
v___x_1982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__6));
v___x_1984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
lean_ctor_set(v___x_1985_, 1, v___x_1970_);
v___x_1986_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__7);
v___x_1987_ = l_String_quote(v_titleString_1965_);
v___x_1988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1986_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*1, v___x_1976_);
v___x_1991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1985_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v___x_1979_);
v___x_1993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
lean_ctor_set(v___x_1993_, 1, v___x_1981_);
v___x_1994_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__9));
v___x_1995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
lean_ctor_set(v___x_1996_, 1, v___x_1970_);
v___x_1997_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__7);
v___x_1998_ = lean_unsigned_to_nat(0u);
v___x_1999_ = l_Option_repr___redArg(v_inst_1961_, v_metadata_1966_, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1997_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set_uint8(v___x_2001_, sizeof(void*)*1, v___x_1976_);
v___x_2002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_1996_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_1979_);
v___x_2004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v___x_1981_);
v___x_2005_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__11));
v___x_2006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2004_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v___x_1970_);
v___x_2008_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___redArg___closed__12);
v___x_2009_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprBlock_repr___boxed), 6, 4);
lean_closure_set(v___x_2009_, 0, lean_box(0));
lean_closure_set(v___x_2009_, 1, lean_box(0));
lean_closure_set(v___x_2009_, 2, v_inst_1959_);
lean_closure_set(v___x_2009_, 3, v_inst_1960_);
v___x_2010_ = l_Array_repr___redArg(v___x_2009_, v_content_1967_);
v___x_2011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2008_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*1, v___x_1976_);
v___x_2013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2007_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___x_1979_);
v___x_2015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v___x_1981_);
v___x_2016_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___redArg___closed__14));
v___x_2017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
lean_ctor_set(v___x_2018_, 1, v___x_1970_);
v___x_2019_ = l_Array_repr___redArg(v_localinst_1969_, v_subParts_1968_);
v___x_2020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_1997_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*1, v___x_1976_);
v___x_2022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2018_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___redArg___closed__10);
v___x_2024_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__11));
v___x_2025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
lean_ctor_set(v___x_2025_, 1, v___x_2022_);
v___x_2026_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___redArg___closed__12));
v___x_2027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2023_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*1, v___x_1976_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr(lean_object* v_i_2030_, lean_object* v_b_2031_, lean_object* v_p_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_x_2036_, lean_object* v_prec_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_Doc_instReprPart_repr___redArg(v_inst_2033_, v_inst_2034_, v_inst_2035_, v_x_2036_, v_prec_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___boxed(lean_object* v_i_2039_, lean_object* v_b_2040_, lean_object* v_p_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_inst_2044_, lean_object* v_x_2045_, lean_object* v_prec_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Doc_instReprPart_repr(v_i_2039_, v_b_2040_, v_p_2041_, v_inst_2042_, v_inst_2043_, v_inst_2044_, v_x_2045_, v_prec_2046_);
lean_dec(v_prec_2046_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart___redArg(lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_inst_2050_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2051_, 0, lean_box(0));
lean_closure_set(v___x_2051_, 1, lean_box(0));
lean_closure_set(v___x_2051_, 2, lean_box(0));
lean_closure_set(v___x_2051_, 3, v_inst_2048_);
lean_closure_set(v___x_2051_, 4, v_inst_2049_);
lean_closure_set(v___x_2051_, 5, v_inst_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart(lean_object* v_i_2052_, lean_object* v_b_2053_, lean_object* v_p_2054_, lean_object* v_inst_2055_, lean_object* v_inst_2056_, lean_object* v_inst_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_closure((void*)(l_Lean_Doc_instReprPart_repr___boxed), 8, 6);
lean_closure_set(v___x_2058_, 0, lean_box(0));
lean_closure_set(v___x_2058_, 1, lean_box(0));
lean_closure_set(v___x_2058_, 2, lean_box(0));
lean_closure_set(v___x_2058_, 3, v_inst_2055_);
lean_closure_set(v___x_2058_, 4, v_inst_2056_);
lean_closure_set(v___x_2058_, 5, v_inst_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg(){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = ((lean_object*)(l_Lean_Doc_instInhabitedPart_default___redArg___closed__0));
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default___redArg___boxed(lean_object* v___dummy_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Doc_instInhabitedPart_default___redArg();
return v_res_2066_;
}
}
static lean_object* _init_l_Lean_Doc_instInhabitedPart_default___closed__0(void){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_Doc_instInhabitedPart_default___redArg();
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart_default(lean_object* v_i_2068_, lean_object* v_b_2069_, lean_object* v_p_2070_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg(){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart___redArg___boxed(lean_object* v___dummy_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_Doc_instInhabitedPart___redArg();
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instInhabitedPart(lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_obj_once(&l_Lean_Doc_instInhabitedPart_default___closed__0, &l_Lean_Doc_instInhabitedPart_default___closed__0_once, _init_l_Lean_Doc_instInhabitedPart_default___closed__0);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg(lean_object* v_x_2080_){
_start:
{
lean_inc_ref(v_x_2080_);
return v_x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___redArg___boxed(lean_object* v_x_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_Doc_Part_cast___redArg(v_x_2081_);
lean_dec_ref(v_x_2081_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast(lean_object* v_i_2083_, lean_object* v_i_x27_2084_, lean_object* v_b_2085_, lean_object* v_b_x27_2086_, lean_object* v_p_2087_, lean_object* v_p_x27_2088_, lean_object* v_inlines__eq_2089_, lean_object* v_blocks__eq_2090_, lean_object* v_metadata__eq_2091_, lean_object* v_x_2092_){
_start:
{
lean_inc_ref(v_x_2092_);
return v_x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Part_cast___boxed(lean_object* v_i_2093_, lean_object* v_i_x27_2094_, lean_object* v_b_2095_, lean_object* v_b_x27_2096_, lean_object* v_p_2097_, lean_object* v_p_x27_2098_, lean_object* v_inlines__eq_2099_, lean_object* v_blocks__eq_2100_, lean_object* v_metadata__eq_2101_, lean_object* v_x_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Doc_Part_cast(v_i_2093_, v_i_x27_2094_, v_b_2095_, v_b_x27_2096_, v_p_2097_, v_p_x27_2098_, v_inlines__eq_2099_, v_blocks__eq_2100_, v_metadata__eq_2101_, v_x_2102_);
lean_dec_ref(v_x_2102_);
return v_res_2103_;
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
