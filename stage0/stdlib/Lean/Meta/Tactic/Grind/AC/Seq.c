// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Seq
// Imports: public import Init.Grind.AC public import Init.Data.Ord import Init.Data.Nat.Linear
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Grind_AC_instReprSeq_repr(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Grind_AC_instBEqSeq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Grind_AC_Seq_concat(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_length___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_isVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_isVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_reverse_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_reverse(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_compare___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_AC_instOrdSeq__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_AC_Seq_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_AC_instOrdSeq__lean___closed__0 = (const lean_object*)&l_Lean_Grind_AC_instOrdSeq__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_AC_instOrdSeq__lean = (const lean_object*)&l_Lean_Grind_AC_instOrdSeq__lean___closed__0_value;
static const lean_closure_object l_Lean_Grind_AC_instAppendSeq__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_AC_Seq_concat, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_AC_instAppendSeq__lean___closed__0 = (const lean_object*)&l_Lean_Grind_AC_instAppendSeq__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_AC_instAppendSeq__lean = (const lean_object*)&l_Lean_Grind_AC_instAppendSeq__lean___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_false_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_false_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_exact_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_exact_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_prefix_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_prefix_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "_private.Lean.Meta.Tactic.Grind.AC.Seq.0.Lean.Grind.AC.StartsWithResult.exact"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "_private.Lean.Meta.Tactic.Grind.AC.Seq.0.Lean.Grind.AC.StartsWithResult.false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Meta.Tactic.Grind.AC.Seq.0.Lean.Grind.AC.StartsWithResult.prefix"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instInhabitedStartsWithResult_default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "AC"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__9_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(98, 173, 184, 202, 154, 63, 120, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Seq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__11_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12_value),LEAN_SCALAR_PTR_LITERAL(45, 188, 153, 213, 149, 49, 211, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(24, 92, 86, 9, 127, 105, 104, 37)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__14_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(145, 232, 57, 169, 123, 58, 63, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__15_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(239, 177, 234, 249, 69, 97, 159, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__16_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(128, 56, 53, 42, 83, 128, 66, 77)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_::_"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__17_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__18_value),LEAN_SCALAR_PTR_LITERAL(107, 33, 242, 48, 203, 193, 254, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__20_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "::"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__24_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__25_value),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__21_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__23_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__26_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19_value),((lean_object*)(((size_t)(65) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__27_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__28_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a__ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Seq.cons"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12_value),LEAN_SCALAR_PTR_LITERAL(96, 79, 17, 128, 200, 87, 234, 137)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(123, 186, 150, 149, 195, 159, 124, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 225, 101, 238, 32, 166, 171, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__12_value),LEAN_SCALAR_PTR_LITERAL(92, 203, 204, 43, 133, 252, 105, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(111, 191, 131, 18, 100, 220, 77, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__8_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__9_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__11_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instOfNatSeq__lean(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a;
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_false_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_false_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_exact_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_exact_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_prefix_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_prefix_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_suffix_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_suffix_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_middle_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_middle_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_subseq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_false_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_false_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_exact_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_exact_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_strict_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_strict_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_subset(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_isSorted(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_isSorted___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_noAdjacentDuplicates(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_noAdjacentDuplicates___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_sharesVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sharesVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_toSeq_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superposeAC_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superpose_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superpose_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_firstVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_firstVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_startsWithVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_startsWithVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_lastVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_lastVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_endsWithVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_endsWithVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_length(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(1u);
return v___x_2_;
}
else
{
lean_object* v_s_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v_s_3_ = lean_ctor_get(v_x_1_, 1);
v___x_4_ = l_Lean_Grind_AC_Seq_length(v_s_3_);
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_add(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_length___boxed(lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Grind_AC_Seq_length(v_x_7_);
lean_dec_ref(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_isVar(lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
uint8_t v___x_10_; 
v___x_10_ = 1;
return v___x_10_;
}
else
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_isVar___boxed(lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Grind_AC_Seq_isVar(v_x_12_);
lean_dec_ref(v_x_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_reverse_go(lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
if (lean_obj_tag(v_a_15_) == 0)
{
lean_object* v_x_17_; lean_object* v___x_18_; 
v_x_17_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_x_17_);
lean_dec_ref(v_a_15_);
v___x_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_18_, 0, v_x_17_);
lean_ctor_set(v___x_18_, 1, v_a_16_);
return v___x_18_;
}
else
{
lean_object* v_x_19_; lean_object* v_s_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_28_; 
v_x_19_ = lean_ctor_get(v_a_15_, 0);
v_s_20_ = lean_ctor_get(v_a_15_, 1);
v_isSharedCheck_28_ = !lean_is_exclusive(v_a_15_);
if (v_isSharedCheck_28_ == 0)
{
v___x_22_ = v_a_15_;
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_s_20_);
lean_inc(v_x_19_);
lean_dec(v_a_15_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v_a_16_);
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_x_19_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_a_16_);
v___x_25_ = v_reuseFailAlloc_27_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
v_a_15_ = v_s_20_;
v_a_16_ = v___x_25_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_reverse(lean_object* v_s_29_){
_start:
{
if (lean_obj_tag(v_s_29_) == 0)
{
return v_s_29_;
}
else
{
lean_object* v_x_30_; lean_object* v_s_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_x_30_ = lean_ctor_get(v_s_29_, 0);
lean_inc(v_x_30_);
v_s_31_ = lean_ctor_get(v_s_29_, 1);
lean_inc_ref(v_s_31_);
lean_dec_ref(v_s_29_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v_x_30_);
v___x_33_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_reverse_go(v_s_31_, v___x_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(lean_object* v_s_u2081_34_, lean_object* v_s_u2082_35_){
_start:
{
if (lean_obj_tag(v_s_u2081_34_) == 0)
{
if (lean_obj_tag(v_s_u2082_35_) == 0)
{
lean_object* v_x_36_; lean_object* v_x_37_; uint8_t v___x_38_; 
v_x_36_ = lean_ctor_get(v_s_u2081_34_, 0);
v_x_37_ = lean_ctor_get(v_s_u2082_35_, 0);
v___x_38_ = lean_nat_dec_lt(v_x_36_, v_x_37_);
if (v___x_38_ == 0)
{
uint8_t v___x_39_; 
v___x_39_ = lean_nat_dec_eq(v_x_36_, v_x_37_);
if (v___x_39_ == 0)
{
uint8_t v___x_40_; 
v___x_40_ = 2;
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = 1;
return v___x_41_;
}
}
else
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
}
else
{
uint8_t v___x_43_; 
v___x_43_ = 0;
return v___x_43_;
}
}
else
{
if (lean_obj_tag(v_s_u2082_35_) == 0)
{
uint8_t v___x_44_; 
v___x_44_ = 2;
return v___x_44_;
}
else
{
lean_object* v_x_45_; lean_object* v_s_46_; lean_object* v_x_47_; lean_object* v_s_48_; uint8_t v___x_49_; 
v_x_45_ = lean_ctor_get(v_s_u2081_34_, 0);
v_s_46_ = lean_ctor_get(v_s_u2081_34_, 1);
v_x_47_ = lean_ctor_get(v_s_u2082_35_, 0);
v_s_48_ = lean_ctor_get(v_s_u2082_35_, 1);
v___x_49_ = lean_nat_dec_lt(v_x_45_, v_x_47_);
if (v___x_49_ == 0)
{
uint8_t v___x_50_; 
v___x_50_ = lean_nat_dec_eq(v_x_45_, v_x_47_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 2;
return v___x_51_;
}
else
{
v_s_u2081_34_ = v_s_46_;
v_s_u2082_35_ = v_s_48_;
goto _start;
}
}
else
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex___boxed(lean_object* v_s_u2081_54_, lean_object* v_s_u2082_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(v_s_u2081_54_, v_s_u2082_55_);
lean_dec_ref(v_s_u2082_55_);
lean_dec_ref(v_s_u2081_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_compare(lean_object* v_s_u2081_58_, lean_object* v_s_u2082_59_){
_start:
{
lean_object* v_len_u2081_60_; lean_object* v_len_u2082_61_; uint8_t v___x_62_; 
v_len_u2081_60_ = l_Lean_Grind_AC_Seq_length(v_s_u2081_58_);
v_len_u2082_61_ = l_Lean_Grind_AC_Seq_length(v_s_u2082_59_);
v___x_62_ = lean_nat_dec_lt(v_len_u2081_60_, v_len_u2082_61_);
if (v___x_62_ == 0)
{
uint8_t v___x_63_; 
v___x_63_ = lean_nat_dec_lt(v_len_u2082_61_, v_len_u2081_60_);
lean_dec(v_len_u2081_60_);
lean_dec(v_len_u2082_61_);
if (v___x_63_ == 0)
{
uint8_t v___x_64_; 
v___x_64_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(v_s_u2081_58_, v_s_u2082_59_);
return v___x_64_;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = 2;
return v___x_65_;
}
}
else
{
uint8_t v___x_66_; 
lean_dec(v_len_u2082_61_);
lean_dec(v_len_u2081_60_);
v___x_66_ = 0;
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_compare___boxed(lean_object* v_s_u2081_67_, lean_object* v_s_u2082_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Lean_Grind_AC_Seq_compare(v_s_u2081_67_, v_s_u2082_68_);
lean_dec_ref(v_s_u2082_68_);
lean_dec_ref(v_s_u2081_67_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx(lean_object* v_x_75_){
_start:
{
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
lean_object* v___x_76_; 
v___x_76_ = lean_unsigned_to_nat(0u);
return v___x_76_;
}
case 1:
{
lean_object* v___x_77_; 
v___x_77_ = lean_unsigned_to_nat(1u);
return v___x_77_;
}
default: 
{
lean_object* v___x_78_; 
v___x_78_ = lean_unsigned_to_nat(2u);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___boxed(lean_object* v_x_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx(v_x_79_);
lean_dec(v_x_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(lean_object* v_t_81_, lean_object* v_k_82_){
_start:
{
if (lean_obj_tag(v_t_81_) == 2)
{
lean_object* v_s_83_; lean_object* v___x_84_; 
v_s_83_ = lean_ctor_get(v_t_81_, 0);
lean_inc_ref(v_s_83_);
lean_dec_ref(v_t_81_);
v___x_84_ = lean_apply_1(v_k_82_, v_s_83_);
return v___x_84_;
}
else
{
lean_dec(v_t_81_);
return v_k_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim(lean_object* v_motive_85_, lean_object* v_ctorIdx_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_k_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_87_, v_k_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___boxed(lean_object* v_motive_91_, lean_object* v_ctorIdx_92_, lean_object* v_t_93_, lean_object* v_h_94_, lean_object* v_k_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim(v_motive_91_, v_ctorIdx_92_, v_t_93_, v_h_94_, v_k_95_);
lean_dec(v_ctorIdx_92_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_false_elim___redArg(lean_object* v_t_97_, lean_object* v_false_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_97_, v_false_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_false_elim(lean_object* v_motive_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_false_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_101_, v_false_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_exact_elim___redArg(lean_object* v_t_105_, lean_object* v_exact_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_105_, v_exact_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_exact_elim(lean_object* v_motive_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_exact_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_109_, v_exact_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_prefix_elim___redArg(lean_object* v_t_113_, lean_object* v_prefix_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_113_, v_prefix_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_prefix_elim(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_prefix_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_117_, v_prefix_119_);
return v___x_120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(2u);
v___x_128_ = lean_nat_to_int(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_to_int(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr(lean_object* v_x_137_, lean_object* v_prec_138_){
_start:
{
lean_object* v___y_140_; lean_object* v___y_147_; 
switch(lean_obj_tag(v_x_137_))
{
case 0:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1024u);
v___x_154_ = lean_nat_dec_le(v___x_153_, v_prec_138_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
v___y_147_ = v___x_155_;
goto v___jp_146_;
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
v___y_147_ = v___x_156_;
goto v___jp_146_;
}
}
case 1:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(1024u);
v___x_158_ = lean_nat_dec_le(v___x_157_, v_prec_138_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
v___y_140_ = v___x_159_;
goto v___jp_139_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
v___y_140_ = v___x_160_;
goto v___jp_139_;
}
}
default: 
{
lean_object* v_s_161_; lean_object* v___y_163_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_s_161_ = lean_ctor_get(v_x_137_, 0);
lean_inc_ref(v_s_161_);
lean_dec_ref(v_x_137_);
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_173_ = lean_nat_dec_le(v___x_172_, v_prec_138_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
v___y_163_ = v___x_174_;
goto v___jp_162_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
v___y_163_ = v___x_175_;
goto v___jp_162_;
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__8));
v___x_165_ = lean_unsigned_to_nat(1024u);
v___x_166_ = l_Lean_Grind_AC_instReprSeq_repr(v_s_161_, v___x_165_);
v___x_167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_164_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
lean_inc(v___y_163_);
v___x_168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_168_, 0, v___y_163_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = 0;
v___x_170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*1, v___x_169_);
v___x_171_ = l_Repr_addAppParen(v___x_170_, v_prec_138_);
return v___x_171_;
}
}
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__1));
lean_inc(v___y_140_);
v___x_142_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_142_, 0, v___y_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = 0;
v___x_144_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*1, v___x_143_);
v___x_145_ = l_Repr_addAppParen(v___x_144_, v_prec_138_);
return v___x_145_;
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__3));
lean_inc(v___y_147_);
v___x_149_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_149_, 0, v___y_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = 0;
v___x_151_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*1, v___x_150_);
v___x_152_ = l_Repr_addAppParen(v___x_151_, v_prec_138_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___boxed(lean_object* v_x_176_, lean_object* v_prec_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr(v_x_176_, v_prec_177_);
lean_dec(v_prec_177_);
return v_res_178_;
}
}
static lean_object* _init_l_Lean_Grind_AC_instInhabitedStartsWithResult_default(void){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_box(0);
return v___x_181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_box(0);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(lean_object* v_s_u2081_183_, lean_object* v_s_u2082_184_){
_start:
{
if (lean_obj_tag(v_s_u2082_184_) == 0)
{
if (lean_obj_tag(v_s_u2081_183_) == 0)
{
lean_object* v_x_185_; lean_object* v_x_186_; uint8_t v___x_187_; 
v_x_185_ = lean_ctor_get(v_s_u2082_184_, 0);
lean_inc(v_x_185_);
lean_dec_ref(v_s_u2082_184_);
v_x_186_ = lean_ctor_get(v_s_u2081_183_, 0);
v___x_187_ = lean_nat_dec_eq(v_x_185_, v_x_186_);
lean_dec(v_x_185_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
return v___x_188_;
}
else
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(1);
return v___x_189_;
}
}
else
{
lean_object* v_x_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_201_; 
v_x_190_ = lean_ctor_get(v_s_u2082_184_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_s_u2082_184_);
if (v_isSharedCheck_201_ == 0)
{
v___x_192_ = v_s_u2082_184_;
v_isShared_193_ = v_isSharedCheck_201_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_x_190_);
lean_dec(v_s_u2082_184_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_201_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_x_194_; lean_object* v_s_195_; uint8_t v___x_196_; 
v_x_194_ = lean_ctor_get(v_s_u2081_183_, 0);
v_s_195_ = lean_ctor_get(v_s_u2081_183_, 1);
v___x_196_ = lean_nat_dec_eq(v_x_190_, v_x_194_);
lean_dec(v_x_190_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_del_object(v___x_192_);
v___x_197_ = lean_box(0);
return v___x_197_;
}
else
{
lean_object* v___x_199_; 
lean_inc_ref(v_s_195_);
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 2);
lean_ctor_set(v___x_192_, 0, v_s_195_);
v___x_199_ = v___x_192_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_s_195_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2081_183_) == 0)
{
lean_object* v___x_202_; 
lean_dec_ref(v_s_u2082_184_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
lean_object* v_x_203_; lean_object* v_s_204_; lean_object* v_x_205_; lean_object* v_s_206_; uint8_t v___x_207_; 
v_x_203_ = lean_ctor_get(v_s_u2082_184_, 0);
lean_inc(v_x_203_);
v_s_204_ = lean_ctor_get(v_s_u2082_184_, 1);
lean_inc_ref(v_s_204_);
lean_dec_ref(v_s_u2082_184_);
v_x_205_ = lean_ctor_get(v_s_u2081_183_, 0);
v_s_206_ = lean_ctor_get(v_s_u2081_183_, 1);
v___x_207_ = lean_nat_dec_eq(v_x_203_, v_x_205_);
lean_dec(v_x_203_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_dec_ref(v_s_204_);
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
v_s_u2081_183_ = v_s_206_;
v_s_u2082_184_ = v_s_204_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith___boxed(lean_object* v_s_u2081_210_, lean_object* v_s_u2082_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2081_210_, v_s_u2082_211_);
lean_dec_ref(v_s_u2081_210_);
return v_res_212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__4));
v___x_289_ = l_String_toRawSubstring_x27(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1(lean_object* v_x_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19));
lean_inc(v_x_314_);
v___x_319_ = l_Lean_Syntax_isOfKind(v_x_314_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec(v_x_314_);
v___x_320_ = lean_box(1);
v___x_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_a_316_);
return v___x_321_;
}
else
{
lean_object* v_quotContext_322_; lean_object* v_currMacroScope_323_; lean_object* v_ref_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_quotContext_322_ = lean_ctor_get(v_a_315_, 1);
v_currMacroScope_323_ = lean_ctor_get(v_a_315_, 2);
v_ref_324_ = lean_ctor_get(v_a_315_, 5);
v___x_325_ = l_Lean_Syntax_getArg(v_x_314_, v___x_317_);
v___x_326_ = lean_unsigned_to_nat(2u);
v___x_327_ = l_Lean_Syntax_getArg(v_x_314_, v___x_326_);
lean_dec(v_x_314_);
v___x_328_ = 0;
v___x_329_ = l_Lean_SourceInfo_fromRef(v_ref_324_, v___x_328_);
v___x_330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3));
v___x_331_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5);
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7));
lean_inc(v_currMacroScope_323_);
lean_inc(v_quotContext_322_);
v___x_333_ = l_Lean_addMacroScope(v_quotContext_322_, v___x_332_, v_currMacroScope_323_);
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12));
lean_inc_n(v___x_329_, 2);
v___x_335_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_335_, 0, v___x_329_);
lean_ctor_set(v___x_335_, 1, v___x_331_);
lean_ctor_set(v___x_335_, 2, v___x_333_);
lean_ctor_set(v___x_335_, 3, v___x_334_);
v___x_336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14));
v___x_337_ = l_Lean_Syntax_node2(v___x_329_, v___x_336_, v___x_325_, v___x_327_);
v___x_338_ = l_Lean_Syntax_node2(v___x_329_, v___x_330_, v___x_335_, v___x_337_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_a_316_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___boxed(lean_object* v_x_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1(v_x_340_, v_a_341_, v_a_342_);
lean_dec_ref(v_a_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(lean_object* v_x_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3));
lean_inc(v_x_347_);
v___x_351_ = l_Lean_Syntax_isOfKind(v_x_347_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_x_347_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_a_349_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l_Lean_Syntax_getArg(v_x_347_, v___x_354_);
v___x_356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1));
lean_inc(v___x_355_);
v___x_357_ = l_Lean_Syntax_isOfKind(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v___x_355_);
lean_dec(v_x_347_);
v___x_358_ = lean_box(0);
v___x_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v_a_349_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = l_Lean_Syntax_getArg(v_x_347_, v___x_360_);
lean_dec(v_x_347_);
v___x_362_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_361_);
v___x_363_ = l_Lean_Syntax_matchesNull(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v___x_361_);
lean_dec(v___x_355_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v_a_349_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_ref_368_; uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_366_ = l_Lean_Syntax_getArg(v___x_361_, v___x_354_);
v___x_367_ = l_Lean_Syntax_getArg(v___x_361_, v___x_360_);
lean_dec(v___x_361_);
v_ref_368_ = l_Lean_replaceRef(v___x_355_, v_a_348_);
lean_dec(v___x_355_);
v___x_369_ = 0;
v___x_370_ = l_Lean_SourceInfo_fromRef(v_ref_368_, v___x_369_);
lean_dec(v_ref_368_);
v___x_371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19));
v___x_372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22));
lean_inc(v___x_370_);
v___x_373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_370_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = l_Lean_Syntax_node3(v___x_370_, v___x_371_, v___x_366_, v___x_373_, v___x_367_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v_a_349_);
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___boxed(lean_object* v_x_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(v_x_376_, v_a_377_, v_a_378_);
lean_dec(v_a_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instOfNatSeq__lean(lean_object* v_n_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v_n_380_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a(void){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(1u);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx(lean_object* v_x_383_){
_start:
{
switch(lean_obj_tag(v_x_383_))
{
case 0:
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(0u);
return v___x_384_;
}
case 1:
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(1u);
return v___x_385_;
}
case 2:
{
lean_object* v___x_386_; 
v___x_386_ = lean_unsigned_to_nat(2u);
return v___x_386_;
}
case 3:
{
lean_object* v___x_387_; 
v___x_387_ = lean_unsigned_to_nat(3u);
return v___x_387_;
}
default: 
{
lean_object* v___x_388_; 
v___x_388_ = lean_unsigned_to_nat(4u);
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx___boxed(lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Grind_AC_SubseqResult_ctorIdx(v_x_389_);
lean_dec(v_x_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(lean_object* v_t_391_, lean_object* v_k_392_){
_start:
{
switch(lean_obj_tag(v_t_391_))
{
case 2:
{
lean_object* v_s_393_; lean_object* v___x_394_; 
v_s_393_ = lean_ctor_get(v_t_391_, 0);
lean_inc_ref(v_s_393_);
lean_dec_ref(v_t_391_);
v___x_394_ = lean_apply_1(v_k_392_, v_s_393_);
return v___x_394_;
}
case 3:
{
lean_object* v_s_395_; lean_object* v___x_396_; 
v_s_395_ = lean_ctor_get(v_t_391_, 0);
lean_inc_ref(v_s_395_);
lean_dec_ref(v_t_391_);
v___x_396_ = lean_apply_1(v_k_392_, v_s_395_);
return v___x_396_;
}
case 4:
{
lean_object* v_p_397_; lean_object* v_s_398_; lean_object* v___x_399_; 
v_p_397_ = lean_ctor_get(v_t_391_, 0);
lean_inc_ref(v_p_397_);
v_s_398_ = lean_ctor_get(v_t_391_, 1);
lean_inc_ref(v_s_398_);
lean_dec_ref(v_t_391_);
v___x_399_ = lean_apply_2(v_k_392_, v_p_397_, v_s_398_);
return v___x_399_;
}
default: 
{
lean_dec(v_t_391_);
return v_k_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim(lean_object* v_motive_400_, lean_object* v_ctorIdx_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_k_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_402_, v_k_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim___boxed(lean_object* v_motive_406_, lean_object* v_ctorIdx_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_k_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Grind_AC_SubseqResult_ctorElim(v_motive_406_, v_ctorIdx_407_, v_t_408_, v_h_409_, v_k_410_);
lean_dec(v_ctorIdx_407_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_false_elim___redArg(lean_object* v_t_412_, lean_object* v_false_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_412_, v_false_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_false_elim(lean_object* v_motive_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_false_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_416_, v_false_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_exact_elim___redArg(lean_object* v_t_420_, lean_object* v_exact_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_420_, v_exact_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_exact_elim(lean_object* v_motive_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_exact_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_424_, v_exact_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_prefix_elim___redArg(lean_object* v_t_428_, lean_object* v_prefix_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_428_, v_prefix_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_prefix_elim(lean_object* v_motive_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_prefix_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_432_, v_prefix_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_suffix_elim___redArg(lean_object* v_t_436_, lean_object* v_suffix_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_436_, v_suffix_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_suffix_elim(lean_object* v_motive_439_, lean_object* v_t_440_, lean_object* v_h_441_, lean_object* v_suffix_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_440_, v_suffix_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_middle_elim___redArg(lean_object* v_t_444_, lean_object* v_middle_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_444_, v_middle_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_middle_elim(lean_object* v_motive_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_middle_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_448_, v_middle_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(lean_object* v_s_u2081_452_, lean_object* v_s_u2082_453_, lean_object* v_acc_454_){
_start:
{
if (lean_obj_tag(v_s_u2082_453_) == 0)
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_u2081_452_, v_s_u2082_453_);
lean_dec_ref(v_s_u2082_453_);
lean_dec_ref(v_s_u2081_452_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_dec_ref(v_acc_454_);
v___x_456_ = lean_box(0);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = l_Lean_Grind_AC_Seq_reverse(v_acc_454_);
v___x_458_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
else
{
lean_object* v_x_459_; lean_object* v_s_460_; lean_object* v___x_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_474_; 
v_x_459_ = lean_ctor_get(v_s_u2082_453_, 0);
lean_inc(v_x_459_);
v_s_460_ = lean_ctor_get(v_s_u2082_453_, 1);
lean_inc_ref(v_s_460_);
lean_inc_ref(v_s_u2081_452_);
v___x_461_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_453_, v_s_u2081_452_);
v_isSharedCheck_474_ = !lean_is_exclusive(v_s_u2082_453_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; lean_object* v_unused_476_; 
v_unused_475_ = lean_ctor_get(v_s_u2082_453_, 1);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_s_u2082_453_, 0);
lean_dec(v_unused_476_);
v___x_463_ = v_s_u2082_453_;
v_isShared_464_ = v_isSharedCheck_474_;
goto v_resetjp_462_;
}
else
{
lean_dec(v_s_u2082_453_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_474_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
switch(lean_obj_tag(v___x_461_))
{
case 0:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v_acc_454_);
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_x_459_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_acc_454_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
v_s_u2082_453_ = v_s_460_;
v_acc_454_ = v___x_466_;
goto _start;
}
}
case 1:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_del_object(v___x_463_);
lean_dec_ref(v_s_460_);
lean_dec(v_x_459_);
lean_dec_ref(v_s_u2081_452_);
v___x_469_ = l_Lean_Grind_AC_Seq_reverse(v_acc_454_);
v___x_470_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
default: 
{
lean_object* v_s_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_del_object(v___x_463_);
lean_dec_ref(v_s_460_);
lean_dec(v_x_459_);
lean_dec_ref(v_s_u2081_452_);
v_s_471_ = lean_ctor_get(v___x_461_, 0);
lean_inc_ref(v_s_471_);
lean_dec_ref(v___x_461_);
v___x_472_ = l_Lean_Grind_AC_Seq_reverse(v_acc_454_);
v___x_473_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v_s_471_);
return v___x_473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_subseq(lean_object* v_s_u2081_477_, lean_object* v_s_u2082_478_){
_start:
{
if (lean_obj_tag(v_s_u2082_478_) == 0)
{
uint8_t v___x_479_; 
v___x_479_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_u2081_477_, v_s_u2082_478_);
lean_dec_ref(v_s_u2082_478_);
lean_dec_ref(v_s_u2081_477_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_box(0);
return v___x_480_;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_box(1);
return v___x_481_;
}
}
else
{
lean_object* v_x_482_; lean_object* v_s_483_; lean_object* v___x_484_; 
v_x_482_ = lean_ctor_get(v_s_u2082_478_, 0);
lean_inc(v_x_482_);
v_s_483_ = lean_ctor_get(v_s_u2082_478_, 1);
lean_inc_ref(v_s_483_);
lean_inc_ref(v_s_u2081_477_);
v___x_484_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_478_, v_s_u2081_477_);
lean_dec_ref(v_s_u2082_478_);
switch(lean_obj_tag(v___x_484_))
{
case 0:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v_x_482_);
v___x_486_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(v_s_u2081_477_, v_s_483_, v___x_485_);
return v___x_486_;
}
case 1:
{
lean_object* v___x_487_; 
lean_dec_ref(v_s_483_);
lean_dec(v_x_482_);
lean_dec_ref(v_s_u2081_477_);
v___x_487_ = lean_box(1);
return v___x_487_;
}
default: 
{
lean_object* v_s_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_s_483_);
lean_dec(v_x_482_);
lean_dec_ref(v_s_u2081_477_);
v_s_488_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_484_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_s_488_);
lean_dec(v___x_484_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_s_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx(lean_object* v_x_496_){
_start:
{
switch(lean_obj_tag(v_x_496_))
{
case 0:
{
lean_object* v___x_497_; 
v___x_497_ = lean_unsigned_to_nat(0u);
return v___x_497_;
}
case 1:
{
lean_object* v___x_498_; 
v___x_498_ = lean_unsigned_to_nat(1u);
return v___x_498_;
}
default: 
{
lean_object* v___x_499_; 
v___x_499_ = lean_unsigned_to_nat(2u);
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx___boxed(lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Grind_AC_SubsetResult_ctorIdx(v_x_500_);
lean_dec(v_x_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(lean_object* v_t_502_, lean_object* v_k_503_){
_start:
{
if (lean_obj_tag(v_t_502_) == 2)
{
lean_object* v_s_504_; lean_object* v___x_505_; 
v_s_504_ = lean_ctor_get(v_t_502_, 0);
lean_inc_ref(v_s_504_);
lean_dec_ref(v_t_502_);
v___x_505_ = lean_apply_1(v_k_503_, v_s_504_);
return v___x_505_;
}
else
{
lean_dec(v_t_502_);
return v_k_503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim(lean_object* v_motive_506_, lean_object* v_ctorIdx_507_, lean_object* v_t_508_, lean_object* v_h_509_, lean_object* v_k_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_508_, v_k_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim___boxed(lean_object* v_motive_512_, lean_object* v_ctorIdx_513_, lean_object* v_t_514_, lean_object* v_h_515_, lean_object* v_k_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Grind_AC_SubsetResult_ctorElim(v_motive_512_, v_ctorIdx_513_, v_t_514_, v_h_515_, v_k_516_);
lean_dec(v_ctorIdx_513_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_false_elim___redArg(lean_object* v_t_518_, lean_object* v_false_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_518_, v_false_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_false_elim(lean_object* v_motive_521_, lean_object* v_t_522_, lean_object* v_h_523_, lean_object* v_false_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_522_, v_false_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_exact_elim___redArg(lean_object* v_t_526_, lean_object* v_exact_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_526_, v_exact_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_exact_elim(lean_object* v_motive_529_, lean_object* v_t_530_, lean_object* v_h_531_, lean_object* v_exact_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_530_, v_exact_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_strict_elim___redArg(lean_object* v_t_534_, lean_object* v_strict_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_534_, v_strict_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_strict_elim(lean_object* v_motive_537_, lean_object* v_t_538_, lean_object* v_h_539_, lean_object* v_strict_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_538_, v_strict_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(lean_object* v_s_u2081_542_, lean_object* v_s_u2082_543_, lean_object* v_acc_544_){
_start:
{
if (lean_obj_tag(v_s_u2081_542_) == 0)
{
if (lean_obj_tag(v_s_u2082_543_) == 0)
{
lean_object* v_x_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_556_; 
v_x_545_ = lean_ctor_get(v_s_u2081_542_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_s_u2081_542_);
if (v_isSharedCheck_556_ == 0)
{
v___x_547_ = v_s_u2081_542_;
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_x_545_);
lean_dec(v_s_u2081_542_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_x_549_; uint8_t v___x_550_; 
v_x_549_ = lean_ctor_get(v_s_u2082_543_, 0);
lean_inc(v_x_549_);
lean_dec_ref(v_s_u2082_543_);
v___x_550_ = lean_nat_dec_eq(v_x_545_, v_x_549_);
lean_dec(v_x_549_);
lean_dec(v_x_545_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_del_object(v___x_547_);
lean_dec_ref(v_acc_544_);
v___x_551_ = lean_box(0);
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = l_Lean_Grind_AC_Seq_reverse(v_acc_544_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 2);
lean_ctor_set(v___x_547_, 0, v___x_552_);
v___x_554_ = v___x_547_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_x_557_; lean_object* v_x_558_; lean_object* v_s_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_580_; 
v_x_557_ = lean_ctor_get(v_s_u2081_542_, 0);
v_x_558_ = lean_ctor_get(v_s_u2082_543_, 0);
v_s_559_ = lean_ctor_get(v_s_u2082_543_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_s_u2082_543_);
if (v_isSharedCheck_580_ == 0)
{
v___x_561_ = v_s_u2082_543_;
v_isShared_562_ = v_isSharedCheck_580_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_s_559_);
lean_inc(v_x_558_);
lean_dec(v_s_u2082_543_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_580_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
uint8_t v___x_563_; 
v___x_563_ = lean_nat_dec_eq(v_x_557_, v_x_558_);
if (v___x_563_ == 0)
{
uint8_t v___x_564_; 
v___x_564_ = lean_nat_dec_lt(v_x_557_, v_x_558_);
if (v___x_564_ == 0)
{
lean_object* v___x_566_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v_acc_544_);
v___x_566_ = v___x_561_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_x_558_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_acc_544_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v_s_u2082_543_ = v_s_559_;
v_acc_544_ = v___x_566_;
goto _start;
}
}
else
{
lean_object* v___x_569_; 
lean_del_object(v___x_561_);
lean_dec_ref(v_s_559_);
lean_dec(v_x_558_);
lean_dec_ref(v_s_u2081_542_);
lean_dec_ref(v_acc_544_);
v___x_569_ = lean_box(0);
return v___x_569_;
}
}
else
{
lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_578_; 
lean_del_object(v___x_561_);
lean_dec(v_x_558_);
v_isSharedCheck_578_ = !lean_is_exclusive(v_s_u2081_542_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v_s_u2081_542_, 0);
lean_dec(v_unused_579_);
v___x_571_ = v_s_u2081_542_;
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
else
{
lean_dec(v_s_u2081_542_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = l_Lean_Grind_AC_Seq_reverse(v_acc_544_);
v___x_574_ = l_Lean_Grind_AC_Seq_concat(v___x_573_, v_s_559_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 2);
lean_ctor_set(v___x_571_, 0, v___x_574_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_543_) == 0)
{
lean_object* v___x_581_; 
lean_dec_ref(v_s_u2082_543_);
lean_dec_ref(v_s_u2081_542_);
lean_dec_ref(v_acc_544_);
v___x_581_ = lean_box(0);
return v___x_581_;
}
else
{
lean_object* v_x_582_; lean_object* v_s_583_; lean_object* v_x_584_; lean_object* v_s_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_597_; 
v_x_582_ = lean_ctor_get(v_s_u2081_542_, 0);
v_s_583_ = lean_ctor_get(v_s_u2081_542_, 1);
v_x_584_ = lean_ctor_get(v_s_u2082_543_, 0);
v_s_585_ = lean_ctor_get(v_s_u2082_543_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_s_u2082_543_);
if (v_isSharedCheck_597_ == 0)
{
v___x_587_ = v_s_u2082_543_;
v_isShared_588_ = v_isSharedCheck_597_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_s_585_);
lean_inc(v_x_584_);
lean_dec(v_s_u2082_543_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_597_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
uint8_t v___x_589_; 
v___x_589_ = lean_nat_dec_eq(v_x_582_, v_x_584_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; 
v___x_590_ = lean_nat_dec_lt(v_x_582_, v_x_584_);
if (v___x_590_ == 0)
{
lean_object* v___x_592_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_acc_544_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_x_584_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_acc_544_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
v_s_u2082_543_ = v_s_585_;
v_acc_544_ = v___x_592_;
goto _start;
}
}
else
{
lean_object* v___x_595_; 
lean_del_object(v___x_587_);
lean_dec_ref(v_s_585_);
lean_dec(v_x_584_);
lean_dec_ref(v_s_u2081_542_);
lean_dec_ref(v_acc_544_);
v___x_595_ = lean_box(0);
return v___x_595_;
}
}
else
{
lean_inc_ref(v_s_583_);
lean_del_object(v___x_587_);
lean_dec(v_x_584_);
lean_dec_ref(v_s_u2081_542_);
v_s_u2081_542_ = v_s_583_;
v_s_u2082_543_ = v_s_585_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_subset(lean_object* v_s_u2081_598_, lean_object* v_s_u2082_599_){
_start:
{
if (lean_obj_tag(v_s_u2081_598_) == 0)
{
if (lean_obj_tag(v_s_u2082_599_) == 0)
{
lean_object* v_x_600_; lean_object* v_x_601_; uint8_t v___x_602_; 
v_x_600_ = lean_ctor_get(v_s_u2081_598_, 0);
lean_inc(v_x_600_);
lean_dec_ref(v_s_u2081_598_);
v_x_601_ = lean_ctor_get(v_s_u2082_599_, 0);
lean_inc(v_x_601_);
lean_dec_ref(v_s_u2082_599_);
v___x_602_ = lean_nat_dec_eq(v_x_600_, v_x_601_);
lean_dec(v_x_601_);
lean_dec(v_x_600_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
v___x_603_ = lean_box(0);
return v___x_603_;
}
else
{
lean_object* v___x_604_; 
v___x_604_ = lean_box(1);
return v___x_604_;
}
}
else
{
lean_object* v_x_605_; lean_object* v_x_606_; lean_object* v_s_607_; uint8_t v___x_608_; 
v_x_605_ = lean_ctor_get(v_s_u2081_598_, 0);
v_x_606_ = lean_ctor_get(v_s_u2082_599_, 0);
lean_inc(v_x_606_);
v_s_607_ = lean_ctor_get(v_s_u2082_599_, 1);
lean_inc_ref(v_s_607_);
lean_dec_ref(v_s_u2082_599_);
v___x_608_ = lean_nat_dec_eq(v_x_605_, v_x_606_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = lean_nat_dec_lt(v_x_605_, v_x_606_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v_x_606_);
v___x_611_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(v_s_u2081_598_, v_s_607_, v___x_610_);
return v___x_611_;
}
else
{
lean_object* v___x_612_; 
lean_dec_ref(v_s_607_);
lean_dec(v_x_606_);
lean_dec_ref(v_s_u2081_598_);
v___x_612_ = lean_box(0);
return v___x_612_;
}
}
else
{
lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_x_606_);
v_isSharedCheck_619_ = !lean_is_exclusive(v_s_u2081_598_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v_s_u2081_598_, 0);
lean_dec(v_unused_620_);
v___x_614_ = v_s_u2081_598_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_dec(v_s_u2081_598_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set_tag(v___x_614_, 2);
lean_ctor_set(v___x_614_, 0, v_s_607_);
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_s_607_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_599_) == 0)
{
lean_object* v___x_621_; 
lean_dec_ref(v_s_u2082_599_);
lean_dec_ref(v_s_u2081_598_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
else
{
lean_object* v_x_622_; lean_object* v_s_623_; lean_object* v_x_624_; lean_object* v_s_625_; uint8_t v___x_626_; 
v_x_622_ = lean_ctor_get(v_s_u2081_598_, 0);
v_s_623_ = lean_ctor_get(v_s_u2081_598_, 1);
v_x_624_ = lean_ctor_get(v_s_u2082_599_, 0);
lean_inc(v_x_624_);
v_s_625_ = lean_ctor_get(v_s_u2082_599_, 1);
lean_inc_ref(v_s_625_);
lean_dec_ref(v_s_u2082_599_);
v___x_626_ = lean_nat_dec_eq(v_x_622_, v_x_624_);
if (v___x_626_ == 0)
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_lt(v_x_622_, v_x_624_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_x_624_);
v___x_629_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(v_s_u2081_598_, v_s_625_, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; 
lean_dec_ref(v_s_625_);
lean_dec(v_x_624_);
lean_dec_ref(v_s_u2081_598_);
v___x_630_ = lean_box(0);
return v___x_630_;
}
}
else
{
lean_inc_ref(v_s_623_);
lean_dec(v_x_624_);
lean_dec_ref(v_s_u2081_598_);
v_s_u2081_598_ = v_s_623_;
v_s_u2082_599_ = v_s_625_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(lean_object* v_x_632_, lean_object* v_s_633_){
_start:
{
if (lean_obj_tag(v_s_633_) == 0)
{
lean_object* v_x_634_; uint8_t v___x_635_; 
v_x_634_ = lean_ctor_get(v_s_633_, 0);
v___x_635_ = lean_nat_dec_le(v_x_632_, v_x_634_);
return v___x_635_;
}
else
{
lean_object* v_x_636_; lean_object* v_s_637_; uint8_t v___x_638_; 
v_x_636_ = lean_ctor_get(v_s_633_, 0);
v_s_637_ = lean_ctor_get(v_s_633_, 1);
v___x_638_ = lean_nat_dec_le(v_x_632_, v_x_636_);
if (v___x_638_ == 0)
{
return v___x_638_;
}
else
{
v_x_632_ = v_x_636_;
v_s_633_ = v_s_637_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go___boxed(lean_object* v_x_640_, lean_object* v_s_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(v_x_640_, v_s_641_);
lean_dec_ref(v_s_641_);
lean_dec(v_x_640_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_isSorted(lean_object* v_s_644_){
_start:
{
if (lean_obj_tag(v_s_644_) == 0)
{
uint8_t v___x_645_; 
v___x_645_ = 1;
return v___x_645_;
}
else
{
lean_object* v_x_646_; lean_object* v_s_647_; uint8_t v___x_648_; 
v_x_646_ = lean_ctor_get(v_s_644_, 0);
v_s_647_ = lean_ctor_get(v_s_644_, 1);
v___x_648_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(v_x_646_, v_s_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_isSorted___boxed(lean_object* v_s_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Lean_Grind_AC_Seq_isSorted(v_s_649_);
lean_dec_ref(v_s_649_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_contains(lean_object* v_s_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_s_652_) == 0)
{
lean_object* v_x_654_; uint8_t v___x_655_; 
v_x_654_ = lean_ctor_get(v_s_652_, 0);
v___x_655_ = lean_nat_dec_eq(v_x_653_, v_x_654_);
return v___x_655_;
}
else
{
lean_object* v_x_656_; lean_object* v_s_657_; uint8_t v___x_658_; 
v_x_656_ = lean_ctor_get(v_s_652_, 0);
v_s_657_ = lean_ctor_get(v_s_652_, 1);
v___x_658_ = lean_nat_dec_eq(v_x_653_, v_x_656_);
if (v___x_658_ == 0)
{
v_s_652_ = v_s_657_;
goto _start;
}
else
{
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_contains___boxed(lean_object* v_s_660_, lean_object* v_x_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_Lean_Grind_AC_Seq_contains(v_s_660_, v_x_661_);
lean_dec(v_x_661_);
lean_dec_ref(v_s_660_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(lean_object* v_x_664_, lean_object* v_s_665_){
_start:
{
if (lean_obj_tag(v_s_665_) == 0)
{
lean_object* v_x_666_; uint8_t v___x_667_; 
v_x_666_ = lean_ctor_get(v_s_665_, 0);
v___x_667_ = lean_nat_dec_eq(v_x_664_, v_x_666_);
if (v___x_667_ == 0)
{
uint8_t v___x_668_; 
v___x_668_ = 1;
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = 0;
return v___x_669_;
}
}
else
{
lean_object* v_x_670_; lean_object* v_s_671_; uint8_t v___x_672_; 
v_x_670_ = lean_ctor_get(v_s_665_, 0);
v_s_671_ = lean_ctor_get(v_s_665_, 1);
v___x_672_ = lean_nat_dec_eq(v_x_664_, v_x_670_);
if (v___x_672_ == 0)
{
v_x_664_ = v_x_670_;
v_s_665_ = v_s_671_;
goto _start;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = 0;
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go___boxed(lean_object* v_x_675_, lean_object* v_s_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(v_x_675_, v_s_676_);
lean_dec_ref(v_s_676_);
lean_dec(v_x_675_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_noAdjacentDuplicates(lean_object* v_s_679_){
_start:
{
if (lean_obj_tag(v_s_679_) == 0)
{
uint8_t v___x_680_; 
v___x_680_ = 1;
return v___x_680_;
}
else
{
lean_object* v_x_681_; lean_object* v_s_682_; uint8_t v___x_683_; 
v_x_681_ = lean_ctor_get(v_s_679_, 0);
v_s_682_ = lean_ctor_get(v_s_679_, 1);
v___x_683_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(v_x_681_, v_s_682_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_noAdjacentDuplicates___boxed(lean_object* v_s_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Lean_Grind_AC_Seq_noAdjacentDuplicates(v_s_684_);
lean_dec_ref(v_s_684_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_sharesVar(lean_object* v_s_u2081_687_, lean_object* v_s_u2082_688_){
_start:
{
if (lean_obj_tag(v_s_u2081_687_) == 0)
{
if (lean_obj_tag(v_s_u2082_688_) == 0)
{
lean_object* v_x_689_; lean_object* v_x_690_; uint8_t v___x_691_; 
v_x_689_ = lean_ctor_get(v_s_u2081_687_, 0);
v_x_690_ = lean_ctor_get(v_s_u2082_688_, 0);
v___x_691_ = lean_nat_dec_eq(v_x_689_, v_x_690_);
return v___x_691_;
}
else
{
lean_object* v_x_692_; lean_object* v_x_693_; lean_object* v_s_694_; uint8_t v___x_695_; 
v_x_692_ = lean_ctor_get(v_s_u2081_687_, 0);
v_x_693_ = lean_ctor_get(v_s_u2082_688_, 0);
v_s_694_ = lean_ctor_get(v_s_u2082_688_, 1);
v___x_695_ = lean_nat_dec_eq(v_x_692_, v_x_693_);
if (v___x_695_ == 0)
{
v_s_u2082_688_ = v_s_694_;
goto _start;
}
else
{
return v___x_695_;
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_688_) == 0)
{
lean_object* v_x_697_; lean_object* v_s_698_; lean_object* v_x_699_; uint8_t v___x_700_; 
v_x_697_ = lean_ctor_get(v_s_u2081_687_, 0);
v_s_698_ = lean_ctor_get(v_s_u2081_687_, 1);
v_x_699_ = lean_ctor_get(v_s_u2082_688_, 0);
v___x_700_ = lean_nat_dec_eq(v_x_697_, v_x_699_);
if (v___x_700_ == 0)
{
v_s_u2081_687_ = v_s_698_;
goto _start;
}
else
{
return v___x_700_;
}
}
else
{
lean_object* v_x_702_; lean_object* v_s_703_; lean_object* v_x_704_; lean_object* v_s_705_; uint8_t v___x_706_; 
v_x_702_ = lean_ctor_get(v_s_u2081_687_, 0);
v_s_703_ = lean_ctor_get(v_s_u2081_687_, 1);
v_x_704_ = lean_ctor_get(v_s_u2082_688_, 0);
v_s_705_ = lean_ctor_get(v_s_u2082_688_, 1);
v___x_706_ = lean_nat_dec_eq(v_x_702_, v_x_704_);
if (v___x_706_ == 0)
{
uint8_t v___x_707_; 
v___x_707_ = lean_nat_dec_lt(v_x_702_, v_x_704_);
if (v___x_707_ == 0)
{
v_s_u2082_688_ = v_s_705_;
goto _start;
}
else
{
v_s_u2081_687_ = v_s_703_;
goto _start;
}
}
else
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sharesVar___boxed(lean_object* v_s_u2081_710_, lean_object* v_s_u2082_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = l_Lean_Grind_AC_Seq_sharesVar(v_s_u2081_710_, v_s_u2082_711_);
lean_dec_ref(v_s_u2082_711_);
lean_dec_ref(v_s_u2081_710_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter___redArg(lean_object* v_s_u2082_714_, lean_object* v_s_u2081_715_, lean_object* v_h__1_716_, lean_object* v_h__2_717_, lean_object* v_h__3_718_, lean_object* v_h__4_719_){
_start:
{
if (lean_obj_tag(v_s_u2082_714_) == 0)
{
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
if (lean_obj_tag(v_s_u2081_715_) == 0)
{
lean_object* v_x_720_; lean_object* v_x_721_; lean_object* v___x_722_; 
lean_dec(v_h__2_717_);
v_x_720_ = lean_ctor_get(v_s_u2082_714_, 0);
lean_inc(v_x_720_);
lean_dec_ref(v_s_u2082_714_);
v_x_721_ = lean_ctor_get(v_s_u2081_715_, 0);
lean_inc(v_x_721_);
lean_dec_ref(v_s_u2081_715_);
v___x_722_ = lean_apply_2(v_h__1_716_, v_x_720_, v_x_721_);
return v___x_722_;
}
else
{
lean_object* v_x_723_; lean_object* v_x_724_; lean_object* v_s_725_; lean_object* v___x_726_; 
lean_dec(v_h__1_716_);
v_x_723_ = lean_ctor_get(v_s_u2082_714_, 0);
lean_inc(v_x_723_);
lean_dec_ref(v_s_u2082_714_);
v_x_724_ = lean_ctor_get(v_s_u2081_715_, 0);
lean_inc(v_x_724_);
v_s_725_ = lean_ctor_get(v_s_u2081_715_, 1);
lean_inc_ref(v_s_725_);
lean_dec_ref(v_s_u2081_715_);
v___x_726_ = lean_apply_3(v_h__2_717_, v_x_723_, v_x_724_, v_s_725_);
return v___x_726_;
}
}
else
{
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
if (lean_obj_tag(v_s_u2081_715_) == 0)
{
lean_object* v_x_727_; lean_object* v_s_728_; lean_object* v_x_729_; lean_object* v___x_730_; 
lean_dec(v_h__4_719_);
v_x_727_ = lean_ctor_get(v_s_u2082_714_, 0);
lean_inc(v_x_727_);
v_s_728_ = lean_ctor_get(v_s_u2082_714_, 1);
lean_inc_ref(v_s_728_);
lean_dec_ref(v_s_u2082_714_);
v_x_729_ = lean_ctor_get(v_s_u2081_715_, 0);
lean_inc(v_x_729_);
lean_dec_ref(v_s_u2081_715_);
v___x_730_ = lean_apply_3(v_h__3_718_, v_x_727_, v_s_728_, v_x_729_);
return v___x_730_;
}
else
{
lean_object* v_x_731_; lean_object* v_s_732_; lean_object* v_x_733_; lean_object* v_s_734_; lean_object* v___x_735_; 
lean_dec(v_h__3_718_);
v_x_731_ = lean_ctor_get(v_s_u2082_714_, 0);
lean_inc(v_x_731_);
v_s_732_ = lean_ctor_get(v_s_u2082_714_, 1);
lean_inc_ref(v_s_732_);
lean_dec_ref(v_s_u2082_714_);
v_x_733_ = lean_ctor_get(v_s_u2081_715_, 0);
lean_inc(v_x_733_);
v_s_734_ = lean_ctor_get(v_s_u2081_715_, 1);
lean_inc_ref(v_s_734_);
lean_dec_ref(v_s_u2081_715_);
v___x_735_ = lean_apply_4(v_h__4_719_, v_x_731_, v_s_732_, v_x_733_, v_s_734_);
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter(lean_object* v_motive_736_, lean_object* v_s_u2082_737_, lean_object* v_s_u2081_738_, lean_object* v_h__1_739_, lean_object* v_h__2_740_, lean_object* v_h__3_741_, lean_object* v_h__4_742_){
_start:
{
if (lean_obj_tag(v_s_u2082_737_) == 0)
{
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
if (lean_obj_tag(v_s_u2081_738_) == 0)
{
lean_object* v_x_743_; lean_object* v_x_744_; lean_object* v___x_745_; 
lean_dec(v_h__2_740_);
v_x_743_ = lean_ctor_get(v_s_u2082_737_, 0);
lean_inc(v_x_743_);
lean_dec_ref(v_s_u2082_737_);
v_x_744_ = lean_ctor_get(v_s_u2081_738_, 0);
lean_inc(v_x_744_);
lean_dec_ref(v_s_u2081_738_);
v___x_745_ = lean_apply_2(v_h__1_739_, v_x_743_, v_x_744_);
return v___x_745_;
}
else
{
lean_object* v_x_746_; lean_object* v_x_747_; lean_object* v_s_748_; lean_object* v___x_749_; 
lean_dec(v_h__1_739_);
v_x_746_ = lean_ctor_get(v_s_u2082_737_, 0);
lean_inc(v_x_746_);
lean_dec_ref(v_s_u2082_737_);
v_x_747_ = lean_ctor_get(v_s_u2081_738_, 0);
lean_inc(v_x_747_);
v_s_748_ = lean_ctor_get(v_s_u2081_738_, 1);
lean_inc_ref(v_s_748_);
lean_dec_ref(v_s_u2081_738_);
v___x_749_ = lean_apply_3(v_h__2_740_, v_x_746_, v_x_747_, v_s_748_);
return v___x_749_;
}
}
else
{
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
if (lean_obj_tag(v_s_u2081_738_) == 0)
{
lean_object* v_x_750_; lean_object* v_s_751_; lean_object* v_x_752_; lean_object* v___x_753_; 
lean_dec(v_h__4_742_);
v_x_750_ = lean_ctor_get(v_s_u2082_737_, 0);
lean_inc(v_x_750_);
v_s_751_ = lean_ctor_get(v_s_u2082_737_, 1);
lean_inc_ref(v_s_751_);
lean_dec_ref(v_s_u2082_737_);
v_x_752_ = lean_ctor_get(v_s_u2081_738_, 0);
lean_inc(v_x_752_);
lean_dec_ref(v_s_u2081_738_);
v___x_753_ = lean_apply_3(v_h__3_741_, v_x_750_, v_s_751_, v_x_752_);
return v___x_753_;
}
else
{
lean_object* v_x_754_; lean_object* v_s_755_; lean_object* v_x_756_; lean_object* v_s_757_; lean_object* v___x_758_; 
lean_dec(v_h__3_741_);
v_x_754_ = lean_ctor_get(v_s_u2082_737_, 0);
lean_inc(v_x_754_);
v_s_755_ = lean_ctor_get(v_s_u2082_737_, 1);
lean_inc_ref(v_s_755_);
lean_dec_ref(v_s_u2082_737_);
v_x_756_ = lean_ctor_get(v_s_u2081_738_, 0);
lean_inc(v_x_756_);
v_s_757_ = lean_ctor_get(v_s_u2081_738_, 1);
lean_inc_ref(v_s_757_);
lean_dec_ref(v_s_u2081_738_);
v___x_758_ = lean_apply_4(v_h__4_742_, v_x_754_, v_s_755_, v_x_756_, v_s_757_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(lean_object* v_xs_759_, lean_object* v_acc_760_){
_start:
{
if (lean_obj_tag(v_xs_759_) == 0)
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Grind_AC_Seq_reverse(v_acc_760_);
return v___x_761_;
}
else
{
lean_object* v_head_762_; lean_object* v_tail_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_771_; 
v_head_762_ = lean_ctor_get(v_xs_759_, 0);
v_tail_763_ = lean_ctor_get(v_xs_759_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_xs_759_);
if (v_isSharedCheck_771_ == 0)
{
v___x_765_ = v_xs_759_;
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_tail_763_);
lean_inc(v_head_762_);
lean_dec(v_xs_759_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_acc_760_);
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_head_762_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_acc_760_);
v___x_768_ = v_reuseFailAlloc_770_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
v_xs_759_ = v_tail_763_;
v_acc_760_ = v___x_768_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_toSeq_x3f(lean_object* v_xs_772_){
_start:
{
if (lean_obj_tag(v_xs_772_) == 0)
{
lean_object* v___x_773_; 
v___x_773_ = lean_box(0);
return v___x_773_;
}
else
{
lean_object* v_head_774_; lean_object* v_tail_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_head_774_ = lean_ctor_get(v_xs_772_, 0);
lean_inc(v_head_774_);
v_tail_775_ = lean_ctor_get(v_xs_772_, 1);
lean_inc(v_tail_775_);
lean_dec_ref(v_xs_772_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_head_774_);
v___x_777_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(v_tail_775_, v___x_776_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(lean_object* v_s_x3f_779_, lean_object* v_x_780_){
_start:
{
if (lean_obj_tag(v_s_x3f_779_) == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v_x_780_);
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
else
{
lean_object* v_val_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_791_; 
v_val_783_ = lean_ctor_get(v_s_x3f_779_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_s_x3f_779_);
if (v_isSharedCheck_791_ == 0)
{
v___x_785_ = v_s_x3f_779_;
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_val_783_);
lean_dec(v_s_x3f_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_787_, 0, v_x_780_);
lean_ctor_set(v___x_787_, 1, v_val_783_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_787_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(lean_object* v_s_x3f_792_){
_start:
{
if (lean_obj_tag(v_s_x3f_792_) == 0)
{
return v_s_x3f_792_;
}
else
{
lean_object* v_val_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_val_793_ = lean_ctor_get(v_s_x3f_792_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_s_x3f_792_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v_s_x3f_792_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_val_793_);
lean_dec(v_s_x3f_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = l_Lean_Grind_AC_Seq_reverse(v_val_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(lean_object* v_s_x3f_802_, lean_object* v_s_x27_803_){
_start:
{
if (lean_obj_tag(v_s_x3f_802_) == 0)
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v_s_x27_803_);
return v___x_804_;
}
else
{
lean_object* v_val_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_val_805_ = lean_ctor_get(v_s_x3f_802_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_s_x3f_802_);
if (v_isSharedCheck_813_ == 0)
{
v___x_807_ = v_s_x3f_802_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_val_805_);
lean_dec(v_s_x3f_802_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = l_Lean_Grind_AC_Seq_concat(v_val_805_, v_s_x27_803_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(lean_object* v_r_u2081_814_, lean_object* v_c_815_, lean_object* v_r_u2082_816_){
_start:
{
if (lean_obj_tag(v_r_u2081_814_) == 1)
{
if (lean_obj_tag(v_c_815_) == 1)
{
if (lean_obj_tag(v_r_u2082_816_) == 1)
{
lean_object* v_val_817_; lean_object* v_val_818_; lean_object* v_val_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_828_; 
v_val_817_ = lean_ctor_get(v_r_u2081_814_, 0);
v_val_818_ = lean_ctor_get(v_c_815_, 0);
v_val_819_ = lean_ctor_get(v_r_u2082_816_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v_r_u2082_816_);
if (v_isSharedCheck_828_ == 0)
{
v___x_821_ = v_r_u2082_816_;
v_isShared_822_ = v_isSharedCheck_828_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_val_819_);
lean_dec(v_r_u2082_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_828_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
lean_inc(v_val_818_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_val_818_);
lean_ctor_set(v___x_823_, 1, v_val_819_);
lean_inc(v_val_817_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_val_817_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_824_);
v___x_826_ = v___x_821_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v___x_829_; 
lean_dec(v_r_u2082_816_);
v___x_829_ = lean_box(0);
return v___x_829_;
}
}
else
{
lean_object* v___x_830_; 
lean_dec(v_r_u2082_816_);
v___x_830_ = lean_box(0);
return v___x_830_;
}
}
else
{
lean_object* v___x_831_; 
lean_dec(v_r_u2082_816_);
v___x_831_ = lean_box(0);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult___boxed(lean_object* v_r_u2081_832_, lean_object* v_c_833_, lean_object* v_r_u2082_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v_r_u2081_832_, v_c_833_, v_r_u2082_834_);
lean_dec(v_c_833_);
lean_dec(v_r_u2081_832_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(lean_object* v_s_u2081_836_, lean_object* v_s_u2082_837_, lean_object* v_r_u2081_838_, lean_object* v_c_839_, lean_object* v_r_u2082_840_){
_start:
{
if (lean_obj_tag(v_s_u2081_836_) == 0)
{
if (lean_obj_tag(v_s_u2082_837_) == 0)
{
lean_object* v_x_841_; lean_object* v_x_842_; uint8_t v___x_843_; 
v_x_841_ = lean_ctor_get(v_s_u2081_836_, 0);
lean_inc(v_x_841_);
lean_dec_ref(v_s_u2081_836_);
v_x_842_ = lean_ctor_get(v_s_u2082_837_, 0);
lean_inc(v_x_842_);
lean_dec_ref(v_s_u2082_837_);
v___x_843_ = lean_nat_dec_eq(v_x_841_, v_x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_844_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_838_, v_x_841_);
v___x_845_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_844_);
v___x_846_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_839_);
v___x_847_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_840_, v_x_842_);
v___x_848_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_847_);
v___x_849_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_845_, v___x_846_, v___x_848_);
lean_dec(v___x_846_);
lean_dec(v___x_845_);
return v___x_849_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v_x_842_);
v___x_850_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_838_);
v___x_851_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_839_, v_x_841_);
v___x_852_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_851_);
v___x_853_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_840_);
v___x_854_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_850_, v___x_852_, v___x_853_);
lean_dec(v___x_852_);
lean_dec(v___x_850_);
return v___x_854_;
}
}
else
{
lean_object* v_x_855_; lean_object* v_x_856_; lean_object* v_s_857_; uint8_t v___x_858_; 
v_x_855_ = lean_ctor_get(v_s_u2081_836_, 0);
v_x_856_ = lean_ctor_get(v_s_u2082_837_, 0);
v_s_857_ = lean_ctor_get(v_s_u2082_837_, 1);
v___x_858_ = lean_nat_dec_eq(v_x_855_, v_x_856_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; 
v___x_859_ = lean_nat_dec_lt(v_x_855_, v_x_856_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
lean_inc_ref(v_s_857_);
lean_inc(v_x_856_);
lean_dec_ref(v_s_u2082_837_);
v___x_860_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_840_, v_x_856_);
v_s_u2082_837_ = v_s_857_;
v_r_u2082_840_ = v___x_860_;
goto _start;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_inc(v_x_855_);
lean_dec_ref(v_s_u2081_836_);
v___x_862_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_838_, v_x_855_);
v___x_863_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_862_);
v___x_864_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_839_);
v___x_865_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_840_);
v___x_866_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_865_, v_s_u2082_837_);
v___x_867_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_863_, v___x_864_, v___x_866_);
lean_dec(v___x_864_);
lean_dec(v___x_863_);
return v___x_867_;
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_inc_ref(v_s_857_);
lean_inc(v_x_855_);
lean_dec_ref(v_s_u2082_837_);
lean_dec_ref(v_s_u2081_836_);
v___x_868_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_838_);
v___x_869_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_839_, v_x_855_);
v___x_870_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_869_);
v___x_871_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_840_);
v___x_872_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_871_, v_s_857_);
v___x_873_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_868_, v___x_870_, v___x_872_);
lean_dec(v___x_870_);
lean_dec(v___x_868_);
return v___x_873_;
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_837_) == 0)
{
lean_object* v_x_874_; lean_object* v_s_875_; lean_object* v_x_876_; uint8_t v___x_877_; 
v_x_874_ = lean_ctor_get(v_s_u2081_836_, 0);
v_s_875_ = lean_ctor_get(v_s_u2081_836_, 1);
v_x_876_ = lean_ctor_get(v_s_u2082_837_, 0);
v___x_877_ = lean_nat_dec_eq(v_x_874_, v_x_876_);
if (v___x_877_ == 0)
{
uint8_t v___x_878_; 
v___x_878_ = lean_nat_dec_lt(v_x_874_, v_x_876_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
lean_inc(v_x_876_);
lean_dec_ref(v_s_u2082_837_);
v___x_879_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_838_);
v___x_880_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_879_, v_s_u2081_836_);
v___x_881_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_839_);
v___x_882_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_840_, v_x_876_);
v___x_883_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_882_);
v___x_884_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_880_, v___x_881_, v___x_883_);
lean_dec(v___x_881_);
lean_dec(v___x_880_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; 
lean_inc_ref(v_s_875_);
lean_inc(v_x_874_);
lean_dec_ref(v_s_u2081_836_);
v___x_885_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_838_, v_x_874_);
v_s_u2081_836_ = v_s_875_;
v_r_u2081_838_ = v___x_885_;
goto _start;
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_inc_ref(v_s_875_);
lean_inc(v_x_874_);
lean_dec_ref(v_s_u2082_837_);
lean_dec_ref(v_s_u2081_836_);
v___x_887_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_838_);
v___x_888_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_887_, v_s_875_);
v___x_889_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_839_, v_x_874_);
v___x_890_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_889_);
v___x_891_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_840_);
v___x_892_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_888_, v___x_890_, v___x_891_);
lean_dec(v___x_890_);
lean_dec(v___x_888_);
return v___x_892_;
}
}
else
{
lean_object* v_x_893_; lean_object* v_s_894_; lean_object* v_x_895_; lean_object* v_s_896_; uint8_t v___x_897_; 
v_x_893_ = lean_ctor_get(v_s_u2081_836_, 0);
v_s_894_ = lean_ctor_get(v_s_u2081_836_, 1);
v_x_895_ = lean_ctor_get(v_s_u2082_837_, 0);
v_s_896_ = lean_ctor_get(v_s_u2082_837_, 1);
v___x_897_ = lean_nat_dec_eq(v_x_893_, v_x_895_);
if (v___x_897_ == 0)
{
uint8_t v___x_898_; 
v___x_898_ = lean_nat_dec_lt(v_x_893_, v_x_895_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_inc_ref(v_s_896_);
lean_inc(v_x_895_);
lean_dec_ref(v_s_u2082_837_);
v___x_899_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_840_, v_x_895_);
v_s_u2082_837_ = v_s_896_;
v_r_u2082_840_ = v___x_899_;
goto _start;
}
else
{
lean_object* v___x_901_; 
lean_inc_ref(v_s_894_);
lean_inc(v_x_893_);
lean_dec_ref(v_s_u2081_836_);
v___x_901_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_838_, v_x_893_);
v_s_u2081_836_ = v_s_894_;
v_r_u2081_838_ = v___x_901_;
goto _start;
}
}
else
{
lean_object* v___x_903_; 
lean_inc_ref(v_s_896_);
lean_inc_ref(v_s_894_);
lean_inc(v_x_893_);
lean_dec_ref(v_s_u2082_837_);
lean_dec_ref(v_s_u2081_836_);
v___x_903_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_839_, v_x_893_);
v_s_u2081_836_ = v_s_894_;
v_s_u2082_837_ = v_s_896_;
v_c_839_ = v___x_903_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superposeAC_x3f(lean_object* v_s_u2081_905_, lean_object* v_s_u2082_906_){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_box(0);
v___x_908_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(v_s_u2081_905_, v_s_u2082_906_, v___x_907_, v___x_907_, v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(lean_object* v_s_u2081_909_, lean_object* v_s_u2082_910_, lean_object* v_p_911_){
_start:
{
lean_object* v___x_912_; 
lean_inc_ref(v_s_u2081_909_);
v___x_912_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_910_, v_s_u2081_909_);
switch(lean_obj_tag(v___x_912_))
{
case 0:
{
if (lean_obj_tag(v_s_u2081_909_) == 0)
{
lean_object* v___x_913_; 
lean_dec_ref(v_s_u2081_909_);
lean_dec_ref(v_p_911_);
v___x_913_ = lean_box(0);
return v___x_913_;
}
else
{
lean_object* v_x_914_; lean_object* v_s_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
v_x_914_ = lean_ctor_get(v_s_u2081_909_, 0);
v_s_915_ = lean_ctor_get(v_s_u2081_909_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v_s_u2081_909_);
if (v_isSharedCheck_923_ == 0)
{
v___x_917_ = v_s_u2081_909_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_s_915_);
lean_inc(v_x_914_);
lean_dec(v_s_u2081_909_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v_p_911_);
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_x_914_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_p_911_);
v___x_920_ = v_reuseFailAlloc_922_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
v_s_u2081_909_ = v_s_915_;
v_p_911_ = v___x_920_;
goto _start;
}
}
}
}
case 1:
{
lean_object* v___x_924_; 
lean_dec_ref(v_p_911_);
lean_dec_ref(v_s_u2081_909_);
v___x_924_ = lean_box(0);
return v___x_924_;
}
default: 
{
lean_object* v_s_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_935_; 
v_s_925_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_935_ == 0)
{
v___x_927_ = v___x_912_;
v_isShared_928_ = v_isSharedCheck_935_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_s_925_);
lean_dec(v___x_912_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_935_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_929_ = l_Lean_Grind_AC_Seq_reverse(v_p_911_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_s_u2081_909_);
lean_ctor_set(v___x_930_, 1, v_s_925_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
if (v_isShared_928_ == 0)
{
lean_ctor_set_tag(v___x_927_, 1);
lean_ctor_set(v___x_927_, 0, v___x_931_);
v___x_933_ = v___x_927_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go___boxed(lean_object* v_s_u2081_936_, lean_object* v_s_u2082_937_, lean_object* v_p_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(v_s_u2081_936_, v_s_u2082_937_, v_p_938_);
lean_dec_ref(v_s_u2082_937_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superpose_x3f(lean_object* v_s_u2081_940_, lean_object* v_s_u2082_941_){
_start:
{
if (lean_obj_tag(v_s_u2081_940_) == 0)
{
lean_object* v___x_942_; 
lean_dec_ref(v_s_u2081_940_);
v___x_942_ = lean_box(0);
return v___x_942_;
}
else
{
lean_object* v_x_943_; lean_object* v_s_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_x_943_ = lean_ctor_get(v_s_u2081_940_, 0);
lean_inc(v_x_943_);
v_s_944_ = lean_ctor_get(v_s_u2081_940_, 1);
lean_inc_ref(v_s_944_);
lean_dec_ref(v_s_u2081_940_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v_x_943_);
v___x_946_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(v_s_944_, v_s_u2082_941_, v___x_945_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superpose_x3f___boxed(lean_object* v_s_u2081_947_, lean_object* v_s_u2082_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Grind_AC_Seq_superpose_x3f(v_s_u2081_947_, v_s_u2082_948_);
lean_dec_ref(v_s_u2082_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_firstVar(lean_object* v_s_950_){
_start:
{
lean_object* v_x_951_; 
v_x_951_ = lean_ctor_get(v_s_950_, 0);
lean_inc(v_x_951_);
return v_x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_firstVar___boxed(lean_object* v_s_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Grind_AC_Seq_firstVar(v_s_952_);
lean_dec_ref(v_s_952_);
return v_res_953_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_startsWithVar(lean_object* v_s_954_, lean_object* v_x_955_){
_start:
{
lean_object* v_x_956_; uint8_t v___x_957_; 
v_x_956_ = lean_ctor_get(v_s_954_, 0);
v___x_957_ = lean_nat_dec_eq(v_x_955_, v_x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_startsWithVar___boxed(lean_object* v_s_958_, lean_object* v_x_959_){
_start:
{
uint8_t v_res_960_; lean_object* v_r_961_; 
v_res_960_ = l_Lean_Grind_AC_Seq_startsWithVar(v_s_958_, v_x_959_);
lean_dec(v_x_959_);
lean_dec_ref(v_s_958_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_lastVar(lean_object* v_s_962_){
_start:
{
if (lean_obj_tag(v_s_962_) == 0)
{
lean_object* v_x_963_; 
v_x_963_ = lean_ctor_get(v_s_962_, 0);
lean_inc(v_x_963_);
return v_x_963_;
}
else
{
lean_object* v_s_964_; 
v_s_964_ = lean_ctor_get(v_s_962_, 1);
v_s_962_ = v_s_964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_lastVar___boxed(lean_object* v_s_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Grind_AC_Seq_lastVar(v_s_966_);
lean_dec_ref(v_s_966_);
return v_res_967_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_endsWithVar(lean_object* v_s_968_, lean_object* v_x_969_){
_start:
{
if (lean_obj_tag(v_s_968_) == 0)
{
lean_object* v_x_970_; uint8_t v___x_971_; 
v_x_970_ = lean_ctor_get(v_s_968_, 0);
v___x_971_ = lean_nat_dec_eq(v_x_969_, v_x_970_);
return v___x_971_;
}
else
{
lean_object* v_s_972_; 
v_s_972_ = lean_ctor_get(v_s_968_, 1);
v_s_968_ = v_s_972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_endsWithVar___boxed(lean_object* v_s_974_, lean_object* v_x_975_){
_start:
{
uint8_t v_res_976_; lean_object* v_r_977_; 
v_res_976_ = l_Lean_Grind_AC_Seq_endsWithVar(v_s_974_, v_x_975_);
lean_dec(v_x_975_);
lean_dec_ref(v_s_974_);
v_r_977_ = lean_box(v_res_976_);
return v_r_977_;
}
}
lean_object* runtime_initialize_Init_Grind_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_AC_instInhabitedStartsWithResult_default = _init_l_Lean_Grind_AC_instInhabitedStartsWithResult_default();
lean_mark_persistent(l_Lean_Grind_AC_instInhabitedStartsWithResult_default);
l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult = _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult);
l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a = _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_AC(uint8_t builtin);
lean_object* initialize_Init_Data_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
}
#ifdef __cplusplus
}
#endif
